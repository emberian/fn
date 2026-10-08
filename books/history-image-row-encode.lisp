; Shared row encoding for final placement and the live append planner.
(in-package "ACL2")
(include-book "history-pages")

(defun fn-hp-x-row (ev)
  (declare (xargs :guard t))
  (if (not (fn-sccb-treep ev))
      (mv (list :refused :event) 0 nil)
    (let* ((enc (fn-scc-encode ev)) (tl (len enc)))
      (if (not (unsigned-byte-p 64 tl))
          (mv (list :refused :event) 0 nil)
        (mv nil tl (fn-hp-pad8 enc))))))

(defthm fn-hp-x-row-true-listp
 (true-listp (mv-nth 2 (fn-hp-x-row ev)))
 :rule-classes :type-prescription
 :hints (("Goal" :in-theory (enable fn-hp-pad8))))
