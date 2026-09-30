;; Exact-byte extension of the page digest continuation. PRF-1087.
;; BYTE-TOTAL is the immutable captured controller scalar, passed unchanged.
(in-package "ACL2")
(include-book "pagestore-digest-cursor")

(defun pgs-dcb-word-count (byte-total)
  (declare (xargs :guard (natp byte-total)))
  (ceiling byte-total 8))

(defun pgs-dcb-begin (sel base byte-total capture lease pgs-digest-state)
  (declare (xargs :stobjs pgs-digest-state
                  :guard (and (natp sel) (natp base) (natp byte-total))))
  (let* ((pgs-digest-state (pgs-dc-begin sel base (ceiling byte-total 64) capture lease pgs-digest-state))
         (pgs-digest-state (update-pgs-dc-total (pgs-dcb-word-count byte-total) pgs-digest-state)))
    (update-pgs-dc-end (pgs-dcb-word-count byte-total) pgs-digest-state)))

(defun pgs-dcb-next-byte-offset (pgs-digest-state)
  (declare (xargs :stobjs pgs-digest-state))
  (* 8 (pgs-dc-pos pgs-digest-state)))

(defun pgs-dcb-read-demand (byte-total pgs-digest-state)
  (declare (xargs :stobjs pgs-digest-state :guard (natp byte-total)))
  (if (pgs-dc-needs-block pgs-digest-state)
      (min 64 (nfix (- (min byte-total (* 8 (pgs-dc-end pgs-digest-state)))
                       (* 8 (pgs-dc-pos pgs-digest-state)))))
    0))

(defun pgs-dcb-step (byte-total block pgs-digest-state)
  (declare (xargs :stobjs pgs-digest-state
                  :guard (and (natp byte-total)
                              (equal (pgs-dc-total pgs-digest-state) (pgs-dcb-word-count byte-total))
                              (<= (pgs-dc-start pgs-digest-state) (pgs-dc-pos pgs-digest-state))
                              (<= (pgs-dc-pos pgs-digest-state) (pgs-dc-end pgs-digest-state))
                              (<= (pgs-dc-end pgs-digest-state) (pgs-dc-total pgs-digest-state))
                              (<= (* 8 (pgs-dc-pos pgs-digest-state)) byte-total))
                  :verify-guards nil))
  (if (and (eq (pgs-dc-mode pgs-digest-state) :chunk)
           (equal (pgs-dc-end pgs-digest-state) (pgs-dc-total pgs-digest-state))
           (<= (- (pgs-dc-end pgs-digest-state) (pgs-dc-pos pgs-digest-state)) 8))
      (let* ((count (nfix (- byte-total (* 8 (pgs-dc-pos pgs-digest-state)))))
             (out (fn-b3-output (pgs-dc-cv pgs-digest-state)
                               (pgs-dc-pad-block (if (zp count) nil block))
                               (pgs-dc-counter pgs-digest-state) count
                               (logior (if (equal (pgs-dc-pos pgs-digest-state) (pgs-dc-start pgs-digest-state))
                                           *fn-b3-chunk-start* 0)
                                       *fn-b3-chunk-end*)))
             (pgs-digest-state (update-pgs-dc-output out pgs-digest-state))
             (pgs-digest-state (update-pgs-dc-mode :return pgs-digest-state)))
        (mv :continue pgs-digest-state))
    (pgs-dc-step block pgs-digest-state)))

(verify-guards pgs-dcb-step)

(defun pgs-dcb-result-octets (pgs-digest-state)
  ;; One bounded ROOT compression and 32 octets. Caller funds the demand.
  (declare (xargs :stobjs pgs-digest-state :guard (eq (pgs-dc-mode pgs-digest-state) :done)))
  (fn-b3-output-root (pgs-dc-output pgs-digest-state)))

(defthm pgs-dcb-read-demand-is-bounded
  (and (natp (pgs-dcb-read-demand byte-total pgs-digest-state))
       (<= (pgs-dcb-read-demand byte-total pgs-digest-state) 64))
  :hints (("Goal" :in-theory (enable pgs-dcb-read-demand)))
  :rule-classes ((:type-prescription :corollary (natp (pgs-dcb-read-demand byte-total pgs-digest-state)))
                 (:linear :corollary (<= (pgs-dcb-read-demand byte-total pgs-digest-state) 64))))

(defthm pgs-dcb-step-preserves-capture-and-lease
  (let ((next (mv-nth 1 (pgs-dcb-step byte-total block pgs-digest-state))))
    (and (equal (pgs-dc-capture next) (pgs-dc-capture pgs-digest-state))
         (equal (pgs-dc-lease next) (pgs-dc-lease pgs-digest-state))))
  :hints (("Goal" :use pgs-dc-step-preserves-capture-and-lease
                  :in-theory (e/d (pgs-dcb-step pgs-dc-capture pgs-dc-lease)
                                   (nth update-nth pgs-dc-step-preserves-capture-and-lease)))))

(defthm pgs-dcb-result-octets-length
  (equal (len (pgs-dcb-result-octets pgs-digest-state)) 32)
  :hints (("Goal" :in-theory (enable pgs-dcb-result-octets))))

(in-theory (disable pgs-dcb-word-count pgs-dcb-begin pgs-dcb-next-byte-offset
                    pgs-dcb-read-demand pgs-dcb-step pgs-dcb-result-octets))
