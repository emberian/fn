;; fn: bounded incremental BLAKE3 over immutable page words. PRF-1087.
;; Library component; not yet called by the checkpoint host.
(in-package "ACL2")
(include-book "pagestore-words-blake3")

(defstobj pgs-digest-state
  (pgs-dc-mode :initially :done)
  (pgs-dc-sel :type (integer 0 *) :initially 0)
  (pgs-dc-base :type (integer 0 *) :initially 0)
  (pgs-dc-total :type (integer 0 *) :initially 0)
  (pgs-dc-start :type (integer 0 *) :initially 0)
  (pgs-dc-end :type (integer 0 *) :initially 0)
  (pgs-dc-pos :type (integer 0 *) :initially 0)
  (pgs-dc-counter :type (integer 0 *) :initially 0)
  (pgs-dc-power :type (integer 0 *) :initially 1)
  (pgs-dc-depth :type (integer 0 *) :initially 0)
  (pgs-dc-cv :initially nil)
  (pgs-dc-output :initially nil)
  (pgs-dc-capture :initially nil)
  (pgs-dc-lease :initially nil)
  (pgs-dc-answer :type (integer 0 *) :initially 0)
  (pgs-dc-frames :type (array t (64)) :initially nil)
  :inline t)

(defun pgs-dc-begin (sel base nb capture lease pgs-digest-state)
  (declare (xargs :stobjs pgs-digest-state
                  :guard (and (natp sel) (natp base) (natp nb))))
  (let* ((pgs-digest-state (update-pgs-dc-mode :node pgs-digest-state))
         (pgs-digest-state (update-pgs-dc-sel sel pgs-digest-state))
         (pgs-digest-state (update-pgs-dc-base base pgs-digest-state))
         (pgs-digest-state (update-pgs-dc-total (* 8 nb) pgs-digest-state))
         (pgs-digest-state (update-pgs-dc-start 0 pgs-digest-state))
         (pgs-digest-state (update-pgs-dc-end (* 8 nb) pgs-digest-state))
         (pgs-digest-state (update-pgs-dc-pos 0 pgs-digest-state))
         (pgs-digest-state (update-pgs-dc-counter 0 pgs-digest-state))
         (pgs-digest-state (update-pgs-dc-power 1 pgs-digest-state))
         (pgs-digest-state (update-pgs-dc-depth 0 pgs-digest-state))
         (pgs-digest-state (update-pgs-dc-cv *fn-b3-iv* pgs-digest-state))
         (pgs-digest-state (update-pgs-dc-output nil pgs-digest-state))
         (pgs-digest-state (update-pgs-dc-capture capture pgs-digest-state))
         (pgs-digest-state (update-pgs-dc-lease lease pgs-digest-state)))
    (update-pgs-dc-answer 0 pgs-digest-state)))

(defun pgs-dc-block (k sel base pgs-mem)
  ;; K is at most eight; each source u64 becomes low then high u32.
  (declare (xargs :stobjs pgs-mem :measure (nfix k)
                  :guard (and (natp k) (<= k 8) (natp base)
                              (<= (+ base k) (pgs-x-len sel pgs-mem)))))
  (if (zp k) nil
    (let ((word (pgs-x-word sel base pgs-mem)))
      (cons (pgs-lo32 word)
            (cons (pgs-hi32 word)
                  (pgs-dc-block (1- k) sel (1+ base) pgs-mem))))))

(defun pgs-dc-pad-words (k words)
  (declare (xargs :guard (natp k) :measure (nfix k)))
  (if (zp k) nil
    (cons (fn-b3-nthx 0 words)
          (pgs-dc-pad-words (1- k) (if (consp words) (cdr words) nil)))))

(defun pgs-dc-pad-block (words)
  (declare (xargs :guard t))
  (pgs-dc-pad-words 16 words))

(defun pgs-dc-result (pgs-digest-state)
  (declare (xargs :stobjs pgs-digest-state))
  (pgs-dc-answer pgs-digest-state))

(defun pgs-dc-step (block pgs-digest-state)
  (declare (xargs :stobjs pgs-digest-state
                  :guard (and (<= (pgs-dc-start pgs-digest-state) (pgs-dc-pos pgs-digest-state))
                              (<= (pgs-dc-pos pgs-digest-state) (pgs-dc-end pgs-digest-state))
                              (<= (pgs-dc-end pgs-digest-state) (pgs-dc-total pgs-digest-state)))
                  :verify-guards nil))
  (let ((mode (pgs-dc-mode pgs-digest-state))
        (start (pgs-dc-start pgs-digest-state))
        (end (pgs-dc-end pgs-digest-state))
        (pos (pgs-dc-pos pgs-digest-state))
        (depth (pgs-dc-depth pgs-digest-state)))
    (case mode
      (:done (mv :done pgs-digest-state))
      (:node
       (if (< 128 (- end start))
           (let* ((pgs-digest-state (update-pgs-dc-power 1 pgs-digest-state))
                  (pgs-digest-state (update-pgs-dc-mode :split pgs-digest-state)))
             (mv :continue pgs-digest-state))
         (let* ((pgs-digest-state (update-pgs-dc-pos start pgs-digest-state))
                (pgs-digest-state (update-pgs-dc-cv *fn-b3-iv* pgs-digest-state))
                (pgs-digest-state (update-pgs-dc-mode :chunk pgs-digest-state)))
           (mv :continue pgs-digest-state))))
      (:split
       (let ((power (pgs-dc-power pgs-digest-state)))
         (cond
          ((and (posp power) (< (* 256 power) (- end start)))
           (let ((pgs-digest-state (update-pgs-dc-power (* 2 power) pgs-digest-state)))
             (mv :continue pgs-digest-state)))
          ((and (posp power) (< depth 64) (< (* 128 power) (- end start)))
           (let* ((right (+ start (* 128 power)))
                  (frame (list :left right end
                               (+ (pgs-dc-counter pgs-digest-state) power) nil))
                  (pgs-digest-state (update-pgs-dc-framesi depth frame pgs-digest-state))
                  (pgs-digest-state (update-pgs-dc-depth (+ 1 depth) pgs-digest-state))
                  (pgs-digest-state (update-pgs-dc-end right pgs-digest-state))
                  (pgs-digest-state (update-pgs-dc-mode :node pgs-digest-state)))
             (mv :continue pgs-digest-state)))
          (t (mv :invalid pgs-digest-state)))))
      (:chunk
       (let* ((count (min 8 (- end pos)))
              (words (pgs-dc-pad-block (if (zp count) nil block)))
              (lastp (<= (- end pos) 8))
              (flags (logior (if (= pos start) *fn-b3-chunk-start* 0)
                            (if lastp *fn-b3-chunk-end* 0)))
              (out (fn-b3-output (pgs-dc-cv pgs-digest-state) words
                                (pgs-dc-counter pgs-digest-state) (* 8 count) flags)))
         (if lastp
             (let* ((pgs-digest-state (update-pgs-dc-output out pgs-digest-state))
                    (pgs-digest-state (update-pgs-dc-mode :return pgs-digest-state)))
               (mv :continue pgs-digest-state))
           (let* ((pgs-digest-state (update-pgs-dc-cv (fn-b3-output-cv out) pgs-digest-state))
                  (pgs-digest-state (update-pgs-dc-pos (+ 8 pos) pgs-digest-state)))
             (mv :continue pgs-digest-state)))))
      (:return
       (cond
        ((zp depth) (let ((pgs-digest-state (update-pgs-dc-mode :root pgs-digest-state)))
                      (mv :continue pgs-digest-state)))
        ((<= depth 64)
         (let* ((index (- depth 1))
                (frame (pgs-dc-framesi index pgs-digest-state))
                (cv (fn-b3-output-cv (pgs-dc-output pgs-digest-state))))
           (if (eq (fn-b3-nthx 0 frame) :left)
               (let* ((frame2 (list :right (fn-b3-nthx 1 frame) (fn-b3-nthx 2 frame) (fn-b3-nthx 3 frame) cv))
                      (pgs-digest-state (update-pgs-dc-framesi index frame2 pgs-digest-state))
                      (pgs-digest-state (update-pgs-dc-start (nfix (fn-b3-nthx 1 frame)) pgs-digest-state))
                      (pgs-digest-state (update-pgs-dc-pos (nfix (fn-b3-nthx 1 frame)) pgs-digest-state))
                      (pgs-digest-state (update-pgs-dc-end (nfix (fn-b3-nthx 2 frame)) pgs-digest-state))
                      (pgs-digest-state (update-pgs-dc-counter (nfix (fn-b3-nthx 3 frame)) pgs-digest-state))
                      (pgs-digest-state (update-pgs-dc-mode :node pgs-digest-state)))
                 (mv :continue pgs-digest-state))
             (let* ((out (fn-b3-output *fn-b3-iv*
                             (append (fn-b3-cv8 (fn-b3-nthx 4 frame)) cv)
                             0 64 *fn-b3-parent*))
                    (pgs-digest-state (update-pgs-dc-output out pgs-digest-state))
                    (pgs-digest-state (update-pgs-dc-depth index pgs-digest-state)))
               (mv :continue pgs-digest-state)))))
        (t (mv :invalid pgs-digest-state))))
      (:root
       (let* ((answer (pgs-octets-be-nat
                       (fn-b3-output-root (pgs-dc-output pgs-digest-state))))
              (pgs-digest-state (update-pgs-dc-answer answer pgs-digest-state))
              (pgs-digest-state (update-pgs-dc-mode :done pgs-digest-state)))
         (mv :done pgs-digest-state)))
      (otherwise (mv :invalid pgs-digest-state)))))

(verify-guards pgs-dc-step)

(defun pgs-dc-needs-block (pgs-digest-state)
  (declare (xargs :stobjs pgs-digest-state))
  (and (eq (pgs-dc-mode pgs-digest-state) :chunk)
       (< (pgs-dc-pos pgs-digest-state) (pgs-dc-end pgs-digest-state))))

(defun pgs-dc-next-word-offset (pgs-digest-state)
  (declare (xargs :stobjs pgs-digest-state))
  (pgs-dc-pos pgs-digest-state))

(defun pgs-dc-read-demand (pgs-digest-state)
  (declare (xargs :stobjs pgs-digest-state))
  (if (pgs-dc-needs-block pgs-digest-state)
      (min 8 (nfix (- (pgs-dc-end pgs-digest-state) (pgs-dc-pos pgs-digest-state))))
    0))

(defthm pgs-dc-read-demand-is-bounded
  (and (natp (pgs-dc-read-demand pgs-digest-state))
       (<= (pgs-dc-read-demand pgs-digest-state) 8))
  :hints (("Goal" :in-theory (enable pgs-dc-read-demand)))
  :rule-classes ((:type-prescription
                  :corollary (natp (pgs-dc-read-demand pgs-digest-state)))
                 (:linear
                  :corollary (<= (pgs-dc-read-demand pgs-digest-state) 8))))

(defun pgs-dc-tick (pgs-mem pgs-digest-state)
  ;; Optional immutable captured-array client. Streaming clients call STEP.
  (declare (xargs :stobjs (pgs-mem pgs-digest-state)
                  :guard (and (<= (+ (pgs-dc-base pgs-digest-state)
                                     (pgs-dc-total pgs-digest-state))
                                  (pgs-x-len (pgs-dc-sel pgs-digest-state) pgs-mem))
                              (<= (pgs-dc-start pgs-digest-state) (pgs-dc-pos pgs-digest-state))
                              (<= (pgs-dc-pos pgs-digest-state) (pgs-dc-end pgs-digest-state))
                              (<= (pgs-dc-end pgs-digest-state) (pgs-dc-total pgs-digest-state)))))
  (let ((block (if (pgs-dc-needs-block pgs-digest-state)
                   (pgs-dc-block (pgs-dc-read-demand pgs-digest-state)
                                  (pgs-dc-sel pgs-digest-state)
                                  (+ (pgs-dc-base pgs-digest-state) (pgs-dc-pos pgs-digest-state))
                                  pgs-mem)
                 nil)))
    (pgs-dc-step block pgs-digest-state)))

(defthm pgs-dc-block-length
  (implies (natp k)
           (equal (len (pgs-dc-block k sel base pgs-mem)) (* 2 k)))
  :hints (("Goal" :in-theory (enable pgs-dc-block))))

(defthm pgs-dc-step-preserves-capture-and-lease
  (let ((next (mv-nth 1 (pgs-dc-step block pgs-digest-state))))
    (and (equal (pgs-dc-capture next) (pgs-dc-capture pgs-digest-state))
         (equal (pgs-dc-lease next) (pgs-dc-lease pgs-digest-state))))
  :hints (("Goal" :in-theory (enable pgs-dc-step pgs-dc-capture pgs-dc-lease))))

(defthm pgs-dc-pad-words-length
  (equal (len (pgs-dc-pad-words k words)) (nfix k))
  :hints (("Goal" :in-theory (enable pgs-dc-pad-words))))

(defthm pgs-dc-pad-words-is-identity
  (implies (and (natp k) (true-listp words) (equal (len words) k))
           (equal (pgs-dc-pad-words k words) words))
  :hints (("Goal" :induct (pgs-dc-pad-words k words)
                  :in-theory (enable pgs-dc-pad-words fn-b3-nthx))))

(defthm pgs-dc-pad-block-length
  (equal (len (pgs-dc-pad-block words)) 16)
  :hints (("Goal" :in-theory (enable pgs-dc-pad-block))))

(defthm pgs-dc-pad-block-is-identity
  (implies (and (true-listp words) (equal (len words) 16))
           (equal (pgs-dc-pad-block words) words))
  :hints (("Goal" :in-theory (enable pgs-dc-pad-block))))

;; Open the boundary in a proof hint; consumers do not inherit its machine.
(in-theory (disable pgs-dc-begin pgs-dc-block pgs-dc-pad-words pgs-dc-pad-block
                    pgs-dc-result pgs-dc-step pgs-dc-needs-block
                    pgs-dc-next-word-offset pgs-dc-read-demand pgs-dc-tick))
