; Runnable admission controls; source grant has not executed these assertions.
(in-package "ACL2")
(include-book "../books/event-archive-producer")
(include-book "../books/machines-c-bind")
(assert-event (and (fn2-run-layout-internal-p 20) (not (fn2-run-layout-internal-p 14))
                  (= (fn2-run-layout-fields 20 0) 8)
                  (not (fn2-run-layout-physical-ref-p 20))))
(make-event
 (value `(assert-event
          (not (member-eq 'fn2-event-archive-member
                (strip-cars (fn2-succ-schema-specs ',(fn2-decl-rows :schema (w state)))))))))
(defun fn2-eau-internal-admission ()
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-succ-txns
  (mv-let (answer fn2-succ-txns)
   (with-local-stobj fn2-succ-slots
    (mv-let (answer fn2-succ-txns fn2-succ-slots)
     (b* ((fn2-succ-txns (fn2-succ-txns-init 1 fn2-succ-txns))
          (fn2-succ-slots (fn2-succ-slots-init *fn2-succ-slots* fn2-succ-slots))
          ((mv refused fn2-succ-txns fn2-succ-slots) (fn2-succ-put 0 0 20 :insert fn2-succ-txns fn2-succ-slots))
          (untouched (and (equal (fn2-succ-txns-phase 0 fn2-succ-txns) *fn2-succ-phase-idle*)
                          (equal (fn2-succ-slots-phase 0 fn2-succ-slots) *fn2-succ-slot-phase-empty*)))
          ((mv public fn2-succ-txns fn2-succ-slots) (fn2-succ-put 0 0 14 :insert fn2-succ-txns fn2-succ-slots)))
      (mv (and (eq refused :schema) untouched (eq public :ok)
               (= (fn2-succ-slots-sid 0 fn2-succ-slots) 14)) fn2-succ-txns fn2-succ-slots))
     (mv answer fn2-succ-txns))) answer)))
(assert-event (fn2-eau-internal-admission))
