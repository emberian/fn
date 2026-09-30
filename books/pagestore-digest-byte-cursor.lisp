;; Exact-byte extension of the page digest continuation. PRF-1087.
;; BYTE-TOTAL is the immutable captured controller scalar, passed unchanged.
(in-package "ACL2")
(include-book "pagestore-digest-cursor")

(defun pgs-dcb-word-count (byte-total)
  (declare (xargs :guard (natp byte-total)))
  (ceiling byte-total 8))

(defun pgs-dcb-begin (sel base byte-total capture lease pgs-digest)
  (declare (xargs :stobjs pgs-digest
                  :guard (and (natp sel) (natp base) (natp byte-total))))
  (let* ((pgs-digest (pgs-dc-begin sel base (ceiling byte-total 64) capture lease pgs-digest))
         (pgs-digest (update-pgs-dc-total (pgs-dcb-word-count byte-total) pgs-digest)))
    (update-pgs-dc-end (pgs-dcb-word-count byte-total) pgs-digest)))

(defun pgs-dcb-next-byte-offset (pgs-digest)
  (declare (xargs :stobjs pgs-digest))
  (* 8 (pgs-dc-pos pgs-digest)))

(defun pgs-dcb-read-demand (byte-total pgs-digest)
  (declare (xargs :stobjs pgs-digest :guard (natp byte-total)))
  (if (pgs-dc-needs-block pgs-digest)
      (min 64 (nfix (- (min byte-total (* 8 (pgs-dc-end pgs-digest)))
                       (* 8 (pgs-dc-pos pgs-digest)))))
    0))

(defun pgs-dcb-step (byte-total block pgs-digest)
  (declare (xargs :stobjs pgs-digest
                  :guard (and (natp byte-total)
                              (equal (pgs-dc-total pgs-digest) (pgs-dcb-word-count byte-total))
                              (<= (pgs-dc-start pgs-digest) (pgs-dc-pos pgs-digest))
                              (<= (pgs-dc-pos pgs-digest) (pgs-dc-end pgs-digest))
                              (<= (pgs-dc-end pgs-digest) (pgs-dc-total pgs-digest))
                              (<= (* 8 (pgs-dc-pos pgs-digest)) byte-total))
                  :verify-guards nil))
  (if (and (eq (pgs-dc-mode pgs-digest) :chunk)
           (equal (pgs-dc-end pgs-digest) (pgs-dc-total pgs-digest))
           (<= (- (pgs-dc-end pgs-digest) (pgs-dc-pos pgs-digest)) 8))
      (let* ((count (nfix (- byte-total (* 8 (pgs-dc-pos pgs-digest)))))
             (out (fn-b3-output (pgs-dc-cv pgs-digest)
                               (pgs-dc-pad-block (if (zp count) nil block))
                               (pgs-dc-counter pgs-digest) count
                               (logior (if (equal (pgs-dc-pos pgs-digest) (pgs-dc-start pgs-digest))
                                           *fn-b3-chunk-start* 0)
                                       *fn-b3-chunk-end*)))
             (pgs-digest (update-pgs-dc-output out pgs-digest))
             (pgs-digest (update-pgs-dc-mode :return pgs-digest)))
        (mv :continue pgs-digest))
    (pgs-dc-step block pgs-digest)))

(verify-guards pgs-dcb-step)

(defun pgs-dcb-result-octets (pgs-digest)
  ;; One bounded ROOT compression and 32 octets. Caller funds the demand.
  (declare (xargs :stobjs pgs-digest :guard (eq (pgs-dc-mode pgs-digest) :done)))
  (fn-b3-output-root (pgs-dc-output pgs-digest)))

(defthm pgs-dcb-read-demand-is-bounded
  (and (natp (pgs-dcb-read-demand byte-total pgs-digest))
       (<= (pgs-dcb-read-demand byte-total pgs-digest) 64))
  :hints (("Goal" :in-theory (enable pgs-dcb-read-demand)))
  :rule-classes ((:type-prescription :corollary (natp (pgs-dcb-read-demand byte-total pgs-digest)))
                 (:linear :corollary (<= (pgs-dcb-read-demand byte-total pgs-digest) 64))))

(defthm pgs-dcb-step-preserves-capture-and-lease
  (let ((next (mv-nth 1 (pgs-dcb-step byte-total block pgs-digest))))
    (and (equal (pgs-dc-capture next) (pgs-dc-capture pgs-digest))
         (equal (pgs-dc-lease next) (pgs-dc-lease pgs-digest))))
  :hints (("Goal" :use pgs-dc-step-preserves-capture-and-lease
                  :in-theory (e/d (pgs-dcb-step pgs-dc-capture pgs-dc-lease)
                                   (nth update-nth pgs-dc-step-preserves-capture-and-lease)))))

(defthm pgs-dcb-result-octets-length
  (equal (len (pgs-dcb-result-octets pgs-digest)) 32)
  :hints (("Goal" :in-theory (enable pgs-dcb-result-octets))))

(in-theory (disable pgs-dcb-word-count pgs-dcb-begin pgs-dcb-next-byte-offset
                    pgs-dcb-read-demand pgs-dcb-step pgs-dcb-result-octets))
