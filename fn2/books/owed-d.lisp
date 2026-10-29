; Keystone T10 (RELEASE-PLAN section 4.1): the core's resident state is
; bounded by the profile, over the open core-child registry. A generator,
; expanded once here over the served assembly, emits from the registry and
; each child's fn2-columns row (never a hand-written list): a per-child
; resident measure from the ACTUAL lengths of the child's column arrays and
; array extra fields times their declared element widths, plus its fixed
; scalar fields; the core's measure is their sum. A child field the
; generator cannot measure (a hash table, a nested stobj, an untyped array)
; is refused at expansion by name unless its declaration's :why states the
; bound. What T10 does not cover: the adapter, the SBCL runtime and the
; simulator's own state (W13's guardrail, not this theorem).
(in-package "ACL2")
(include-book "resident")
(include-book "executor")
(fn2-book-layer :d)

(make-event (value (fn2-declare '(:operation-set fn2-resident) nil nil nil)))

(fn2-resident-measure-events)

; Coverage, checked where the measure is generated: it names exactly the
; registry's children, in registry order.
(assert-event (equal *fn2-resident-children* (strip-cars *fn2-core-children*)))

; The measure of a core initialized from PROFILE (logical view).
(defun-nx fn2-core-resident-at-init (profile core)
  (fn2-core-resident-measure (fn2-core-init profile core)))

(defthm-owed fn2-core-state-bounded (profile core1 core2 core n cell slot gen evkind outcome reason count aux0 aux1 mono real flags)
  (and (implies (fn2-core-profilep profile)
                (equal (fn2-core-resident-at-init profile core1)
                       (fn2-core-resident-at-init profile core2)))
       (implies (and (fn2-corep core) (fn2-core-wfp core))
                (equal (fn2-core-resident-measure (mv-nth 4 (fn2-turn core)))
                       (fn2-core-resident-measure core)))
       ; The adapter-boundary entries change only the operations child.
       (implies (and (fn2-corep core) (fn2-core-wfp core))
                (and (equal (fn2-core-resident-measure
                             (update-fn2-core-ops (mv-nth 1 (fn2-outbox-ack n (fn2-core-ops core))) core))
                            (fn2-core-resident-measure core))
                     (equal (fn2-core-resident-measure
                             (update-fn2-core-ops (fn2-post-result cell slot gen evkind outcome reason count aux0 aux1
                                                                   (fn2-core-ops core)) core))
                            (fn2-core-resident-measure core))
                     (equal (fn2-core-resident-measure
                             (update-fn2-core-ops (fn2-post-clock mono real flags (fn2-core-ops core)) core))
                            (fn2-core-resident-measure core)))))
  :schema :bound :from (:operation-set fn2-resident)
  :teeth (fn2-core-test-state-bounded fn2-core-test-state-bounded-negative)
  :doc "T10: a core's resident bytes (every registered child's arrays and scalars at declared widths) are fixed by its profile at init and unchanged by every turn; no array grows or shrinks after init.")
