; WFP fixes the length of every operation column to ROWS. The three rings
; have independent capacities, so their actual lengths are also observed.
(in-package "ACL2")
(include-book "vocab")

(defun fn2-ops-resident-shape (fn2-ops)
  (declare (xargs :stobjs fn2-ops :guard t))
  (list (fn2-ops-rows fn2-ops) (fn2-ops-out-slot-length fn2-ops)
        (fn2-ops-out-gen-length fn2-ops) (fn2-ops-posted-fifo-length fn2-ops)))

(local
 (defthm fn2-ops-shape-submit-prefix
   (equal (fn2-ops-resident-shape (fn2-outbox-submit-prefix n fn2-ops))
          (fn2-ops-resident-shape fn2-ops))
   :hints (("Goal" :induct (fn2-outbox-submit-prefix n fn2-ops)
            :in-theory (e/d (fn2-outbox-submit-prefix fn2-ops-set-phase
                             update-fn2-ops-phase$ai update-fn2-ops-out-head update-fn2-ops-queued
                             fn2-ops-out-slot-length fn2-ops-out-gen-length fn2-ops-posted-fifo-length
                             fn2-ops-rows)
                            (update-nth fn2-op-slotp fn2-op-ack-phase fn2-ring-next))))))

(defthm fn2-outbox-ack-resident-shape
  (equal (fn2-ops-resident-shape (mv-nth 1 (fn2-outbox-ack n fn2-ops)))
         (fn2-ops-resident-shape fn2-ops))
  :hints (("Goal" :in-theory (e/d (fn2-outbox-ack)
                                 (fn2-ops-resident-shape fn2-outbox-submit-prefix fn2-outbox-prefixp)))))

(defthm fn2-post-clock-resident-shape
  (equal (fn2-ops-resident-shape (fn2-post-clock mono real flags fn2-ops))
         (fn2-ops-resident-shape fn2-ops))
  :hints ((fn2-columns-guard-hint
           '(fn2-ops) '(update-nth binary-logand binary-logior fn2-saturating-inc60)
           (append '(fn2-post-clock fn2-ops-resident-shape fn2-ops-rows fn2-ops-out-slot-length
                     fn2-ops-out-gen-length fn2-ops-posted-fifo-length)
                   (fn2-columns-table-scalar-runes '(fn2-ops) t world)) world)))

(local (include-book "ops-issued-observation"))
(defthm fn2-post-result-resident-shape
  (implies (fn2-opsp fn2-ops)
           (equal (fn2-ops-resident-shape
                   (fn2-post-result cell slot gen evkind outcome reason count aux0 aux1 fn2-ops))
                  (fn2-ops-resident-shape fn2-ops)))
  :hints ((let ((schema (fn2-decl-row '(:columns fn2-ops) world)))
            (fn2-columns-guard-hint
             '(fn2-ops) '(update-nth fn2-ring-next fn2-post-eligiblep fn2-post-payloadp)
             (append '(fn2-post-result fn2-count-stray fn2-ops-resident-shape
                       fn2-ops-rows fn2-ops-out-slot-length fn2-ops-out-gen-length
                       fn2-ops-posted-fifo-length fn2-ops-post-tail)
                     (fn2-issued-payload-column-writers (fn2-decl-get :columns schema))
                     (fn2-issued-extra-writers (fn2-decl-get :extra-fields schema)))
             world))))
