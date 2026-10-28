; TRACE is a differential of the concrete turn against reference.lisp.
(in-package "ACL2")
(include-book "../books/reference")

; Both cores persist across turns; import only the common adapter boundary.
(defun fn2-check-trace-turn (profile cursor queues fn2-core fn2-ref-core)
  (declare (xargs :stobjs (fn2-core fn2-ref-core) :verify-guards nil))
  (b* ((fn2-ref-core (fn2-ref-import-boundary fn2-core fn2-ref-core))
       (lists (fn2-ref-lists (fn2-profile-p profile) cursor queues))
       (before (fn2-ref-difference fn2-core fn2-ref-core lists))
       ((mv rs ro rv ra lists fn2-ref-core) (fn2-ref-turn lists fn2-ref-core))
       ((mv status obs visits actions fn2-core) (fn2-turn fn2-core))
       (difference (or before (fn2-ref-difference fn2-core fn2-ref-core lists)
                       (and (not (equal (list status obs visits actions) (list rs ro rv ra)))
                            (list :turn-result (list status obs visits actions) (list rs ro rv ra)))))
       (verdict (if difference (list :fail :trace difference) :pass)))
    (progn$ (if difference (cw "TRACE DIFFERENCE ~x0~%" difference) nil)
            (mv verdict status obs visits actions (nth 1 lists) (nth 2 lists) fn2-core fn2-ref-core))))
(in-theory (disable fn2-check-trace-turn))
