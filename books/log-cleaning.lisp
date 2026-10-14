; LC root/pin/tail decisions. Slot observations carry the decoded live set;
; unknown raw slots conservatively reference every segment. The observation
; bridge to the root codec is owed before a native caller uses this decision.
(in-package "ACL2")
(include-book "log-locator-resolves")
(include-book "pagestore")
(include-book "log-checkpoint-total-accessors")

(defun fn-lc-slot-references (slot seg)
  (declare (xargs :guard t :verify-guards nil))
  (if (and (true-listp slot) (equal (len slot) 3)
           (equal (car slot) :lc-slot-observation)
           (true-listp (nth 2 slot)))
      (if (member-equal seg (nth 2 slot)) t nil)
    (if (null slot) nil t)))

(defun fn-lc-tail-references (tail seg)
  (declare (xargs :guard (unsigned-byte-p 64 seg) :verify-guards nil))
  (if (natp tail) (<= tail (nfix seg)) t))

(defun fn-lc-unlink-allowedp (seg disk r fn-lc-pins tail)
  (declare (xargs :guard (and (unsigned-byte-p 64 seg)
                              (fn-lc-pins-p fn-lc-pins)) :verify-guards nil))
  (and (not (fn-lc-slot-references (mbe :logic (car (pgs-root-slots r disk)) :exec (fn-lc-head (pgs-root-slots r disk))) seg))
       (not (fn-lc-slot-references (mbe :logic (cdr (pgs-root-slots r disk)) :exec (fn-lc-rest (pgs-root-slots r disk))) seg))
       (not (fn-lc-pin-references fn-lc-pins seg))
       (not (fn-lc-tail-references tail seg))))
