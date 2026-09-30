;; fn: bounded incremental BLAKE3 over immutable page words. PRF-1087.
;; Library component; not yet called by the checkpoint host.
(in-package "ACL2")
(include-book "pagestore-words-blake3")

(defstobj pgs-digest
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

(defun pgs-dc-begin (sel base nb capture lease pgs-digest)
  (declare (xargs :stobjs pgs-digest
                  :guard (and (natp sel) (natp base) (natp nb))))
  (let* ((pgs-digest (update-pgs-dc-mode :node pgs-digest))
         (pgs-digest (update-pgs-dc-sel sel pgs-digest))
         (pgs-digest (update-pgs-dc-base base pgs-digest))
         (pgs-digest (update-pgs-dc-total (* 8 nb) pgs-digest))
         (pgs-digest (update-pgs-dc-start 0 pgs-digest))
         (pgs-digest (update-pgs-dc-end (* 8 nb) pgs-digest))
         (pgs-digest (update-pgs-dc-pos 0 pgs-digest))
         (pgs-digest (update-pgs-dc-counter 0 pgs-digest))
         (pgs-digest (update-pgs-dc-power 1 pgs-digest))
         (pgs-digest (update-pgs-dc-depth 0 pgs-digest))
         (pgs-digest (update-pgs-dc-cv *fn-b3-iv* pgs-digest))
         (pgs-digest (update-pgs-dc-output nil pgs-digest))
         (pgs-digest (update-pgs-dc-capture capture pgs-digest))
         (pgs-digest (update-pgs-dc-lease lease pgs-digest)))
    (update-pgs-dc-answer 0 pgs-digest)))

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

(defun pgs-dc-result (pgs-digest)
  (declare (xargs :stobjs pgs-digest))
  (pgs-dc-answer pgs-digest))

(defun pgs-dc-step (block pgs-digest)
  (declare (xargs :stobjs pgs-digest
                  :guard (and (<= (pgs-dc-start pgs-digest) (pgs-dc-pos pgs-digest))
                              (<= (pgs-dc-pos pgs-digest) (pgs-dc-end pgs-digest))
                              (<= (pgs-dc-end pgs-digest) (pgs-dc-total pgs-digest)))
                  :verify-guards nil))
  (let ((mode (pgs-dc-mode pgs-digest))
        (start (pgs-dc-start pgs-digest))
        (end (pgs-dc-end pgs-digest))
        (pos (pgs-dc-pos pgs-digest))
        (depth (pgs-dc-depth pgs-digest)))
    (case mode
      (:done (mv :done pgs-digest))
      (:node
       (if (< 128 (- end start))
           (let* ((pgs-digest (update-pgs-dc-power 1 pgs-digest))
                  (pgs-digest (update-pgs-dc-mode :split pgs-digest)))
             (mv :continue pgs-digest))
         (let* ((pgs-digest (update-pgs-dc-pos start pgs-digest))
                (pgs-digest (update-pgs-dc-cv *fn-b3-iv* pgs-digest))
                (pgs-digest (update-pgs-dc-mode :chunk pgs-digest)))
           (mv :continue pgs-digest))))
      (:split
       (let ((power (pgs-dc-power pgs-digest)))
         (cond
          ((and (posp power) (< (* 256 power) (- end start)))
           (let ((pgs-digest (update-pgs-dc-power (* 2 power) pgs-digest)))
             (mv :continue pgs-digest)))
          ((and (posp power) (< depth 64) (< (* 128 power) (- end start)))
           (let* ((right (+ start (* 128 power)))
                  (frame (list :left right end
                               (+ (pgs-dc-counter pgs-digest) power) nil))
                  (pgs-digest (update-pgs-dc-framesi depth frame pgs-digest))
                  (pgs-digest (update-pgs-dc-depth (+ 1 depth) pgs-digest))
                  (pgs-digest (update-pgs-dc-end right pgs-digest))
                  (pgs-digest (update-pgs-dc-mode :node pgs-digest)))
             (mv :continue pgs-digest)))
          (t (mv :invalid pgs-digest)))))
      (:chunk
       (let* ((count (min 8 (- end pos)))
              (words (pgs-dc-pad-block (if (zp count) nil block)))
              (lastp (<= (- end pos) 8))
              (flags (logior (if (= pos start) *fn-b3-chunk-start* 0)
                            (if lastp *fn-b3-chunk-end* 0)))
              (out (fn-b3-output (pgs-dc-cv pgs-digest) words
                                (pgs-dc-counter pgs-digest) (* 8 count) flags)))
         (if lastp
             (let* ((pgs-digest (update-pgs-dc-output out pgs-digest))
                    (pgs-digest (update-pgs-dc-mode :return pgs-digest)))
               (mv :continue pgs-digest))
           (let* ((pgs-digest (update-pgs-dc-cv (fn-b3-output-cv out) pgs-digest))
                  (pgs-digest (update-pgs-dc-pos (+ 8 pos) pgs-digest)))
             (mv :continue pgs-digest)))))
      (:return
       (cond
        ((zp depth) (let ((pgs-digest (update-pgs-dc-mode :root pgs-digest)))
                      (mv :continue pgs-digest)))
        ((<= depth 64)
         (let* ((index (- depth 1))
                (frame (pgs-dc-framesi index pgs-digest))
                (cv (fn-b3-output-cv (pgs-dc-output pgs-digest))))
           (if (eq (fn-b3-nthx 0 frame) :left)
               (let* ((frame2 (list :right (fn-b3-nthx 1 frame) (fn-b3-nthx 2 frame) (fn-b3-nthx 3 frame) cv))
                      (pgs-digest (update-pgs-dc-framesi index frame2 pgs-digest))
                      (pgs-digest (update-pgs-dc-start (nfix (fn-b3-nthx 1 frame)) pgs-digest))
                      (pgs-digest (update-pgs-dc-pos (nfix (fn-b3-nthx 1 frame)) pgs-digest))
                      (pgs-digest (update-pgs-dc-end (nfix (fn-b3-nthx 2 frame)) pgs-digest))
                      (pgs-digest (update-pgs-dc-counter (nfix (fn-b3-nthx 3 frame)) pgs-digest))
                      (pgs-digest (update-pgs-dc-mode :node pgs-digest)))
                 (mv :continue pgs-digest))
             (let* ((out (fn-b3-output *fn-b3-iv*
                             (append (fn-b3-cv8 (fn-b3-nthx 4 frame)) cv)
                             0 64 *fn-b3-parent*))
                    (pgs-digest (update-pgs-dc-output out pgs-digest))
                    (pgs-digest (update-pgs-dc-depth index pgs-digest)))
               (mv :continue pgs-digest)))))
        (t (mv :invalid pgs-digest))))
      (:root
       (let* ((answer (pgs-octets-be-nat
                       (fn-b3-output-root (pgs-dc-output pgs-digest))))
              (pgs-digest (update-pgs-dc-answer answer pgs-digest))
              (pgs-digest (update-pgs-dc-mode :done pgs-digest)))
         (mv :done pgs-digest)))
      (otherwise (mv :invalid pgs-digest)))))

(verify-guards pgs-dc-step)

(defun pgs-dc-needs-block (pgs-digest)
  (declare (xargs :stobjs pgs-digest))
  (and (eq (pgs-dc-mode pgs-digest) :chunk)
       (< (pgs-dc-pos pgs-digest) (pgs-dc-end pgs-digest))))

(defun pgs-dc-next-word-offset (pgs-digest)
  (declare (xargs :stobjs pgs-digest))
  (pgs-dc-pos pgs-digest))

(defun pgs-dc-read-demand (pgs-digest)
  (declare (xargs :stobjs pgs-digest))
  (if (pgs-dc-needs-block pgs-digest)
      (min 8 (nfix (- (pgs-dc-end pgs-digest) (pgs-dc-pos pgs-digest))))
    0))

(defthm pgs-dc-read-demand-is-bounded
  (and (natp (pgs-dc-read-demand pgs-digest))
       (<= (pgs-dc-read-demand pgs-digest) 8))
  :hints (("Goal" :in-theory (enable pgs-dc-read-demand)))
  :rule-classes ((:type-prescription
                  :corollary (natp (pgs-dc-read-demand pgs-digest)))
                 (:linear
                  :corollary (<= (pgs-dc-read-demand pgs-digest) 8))))

(defun pgs-dc-tick (pgs-mem pgs-digest)
  ;; Optional immutable captured-array client. Streaming clients call STEP.
  (declare (xargs :stobjs (pgs-mem pgs-digest)
                  :guard (and (<= (+ (pgs-dc-base pgs-digest)
                                     (pgs-dc-total pgs-digest))
                                  (pgs-x-len (pgs-dc-sel pgs-digest) pgs-mem))
                              (<= (pgs-dc-start pgs-digest) (pgs-dc-pos pgs-digest))
                              (<= (pgs-dc-pos pgs-digest) (pgs-dc-end pgs-digest))
                              (<= (pgs-dc-end pgs-digest) (pgs-dc-total pgs-digest)))))
  (let ((block (if (pgs-dc-needs-block pgs-digest)
                   (pgs-dc-block (pgs-dc-read-demand pgs-digest)
                                  (pgs-dc-sel pgs-digest)
                                  (+ (pgs-dc-base pgs-digest) (pgs-dc-pos pgs-digest))
                                  pgs-mem)
                 nil)))
    (pgs-dc-step block pgs-digest)))

(defthm pgs-dc-block-length
  (implies (natp k)
           (equal (len (pgs-dc-block k sel base pgs-mem)) (* 2 k)))
  :hints (("Goal" :in-theory (enable pgs-dc-block))))

(defthm pgs-dc-step-preserves-capture-and-lease
  (let ((next (mv-nth 1 (pgs-dc-step block pgs-digest))))
    (and (equal (pgs-dc-capture next) (pgs-dc-capture pgs-digest))
         (equal (pgs-dc-lease next) (pgs-dc-lease pgs-digest))))
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
