; Second half of the commit kind's B-S2 section: checkpoint allocation and
; installation coordinators, txn source reference, block read, and verbatim copy.
(in-package "ACL2")
(include-book "assembly-callbacks-bt0")

(defun fn2-inst-begin-put-a (c ordinal token okind oslot ogen fn2-retirement-control)
  (declare (xargs :stobjs fn2-retirement-control
                  :guard (and (fn2-retirement-control-wfp fn2-retirement-control)
                              (< 0 (fn2-retirement-control-rows fn2-retirement-control))
                              (unsigned-byte-p 32 c) (unsigned-byte-p 60 ordinal)
                              (unsigned-byte-p 60 token) (unsigned-byte-p 8 okind)
                              (unsigned-byte-p 32 oslot) (unsigned-byte-p 60 ogen))
                  :guard-hints (("Goal" :in-theory (disable unsigned-byte-p fn2-retirement-control-wfp fn2-retirement-control-rows)))))
  (fn2-retirement-control-put 0
    (state *fn2-retirement-state-scanning*)
    (allocation-member 0) (installation-member 1) (candidate c)
    (expected 0) (final-ticket 0) (journal-ticket ordinal)
    (token token) (owner-kind okind) (owner-slot oslot) (owner-gen ogen)))

(defthm fn2-inst-begin-put-a-type
  (implies (and (fn2-retirement-controlp fn2-retirement-control)
                (< 0 (fn2-retirement-control-rows fn2-retirement-control))
                (unsigned-byte-p 32 c) (unsigned-byte-p 60 ordinal)
                (unsigned-byte-p 60 token) (unsigned-byte-p 8 okind)
                (unsigned-byte-p 32 oslot) (unsigned-byte-p 60 ogen))
           (fn2-retirement-controlp (fn2-inst-begin-put-a c ordinal token okind oslot ogen fn2-retirement-control)))
  :hints (("Goal" :in-theory (disable unsigned-byte-p fn2-retirement-controlp fn2-retirement-control-rows))))

(defthm fn2-inst-begin-put-a-wfp
  (implies (and (fn2-retirement-controlp fn2-retirement-control)
                (fn2-retirement-control-wfp fn2-retirement-control)
                (< 0 (fn2-retirement-control-rows fn2-retirement-control))
                (unsigned-byte-p 32 c) (unsigned-byte-p 60 ordinal)
                (unsigned-byte-p 60 token) (unsigned-byte-p 8 okind)
                (unsigned-byte-p 32 oslot) (unsigned-byte-p 60 ogen))
           (fn2-retirement-control-wfp (fn2-inst-begin-put-a c ordinal token okind oslot ogen fn2-retirement-control)))
  :hints (("Goal" :in-theory (disable unsigned-byte-p fn2-retirement-controlp fn2-retirement-control-wfp fn2-retirement-control-rows))))

(defthm fn2-inst-begin-put-a-rows
  (equal (fn2-retirement-control-rows (fn2-inst-begin-put-a c ordinal token okind oslot ogen fn2-retirement-control))
         (fn2-retirement-control-rows fn2-retirement-control))
  :hints (("Goal" :in-theory (disable fn2-retirement-control-rows))))

(in-theory (disable fn2-inst-begin-put-a))

(defun fn2-inst-begin-put-b (slot gen fn2-retirement-control)
  (declare (xargs :stobjs fn2-retirement-control
                  :guard (and (fn2-retirement-control-wfp fn2-retirement-control)
                              (< 0 (fn2-retirement-control-rows fn2-retirement-control))
                              (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen))
                  :guard-hints (("Goal" :in-theory (disable unsigned-byte-p fn2-retirement-control-wfp fn2-retirement-control-rows)))))
  (fn2-retirement-control-put 0
    (slot slot) (gen gen) (scan 0) (count 0) (bytes 0)
    (installed 0) (install-offset 0) (batch 0) (event 0)))

(defthm fn2-inst-begin-put-b-type
  (implies (and (fn2-retirement-controlp fn2-retirement-control)
                (< 0 (fn2-retirement-control-rows fn2-retirement-control))
                (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen))
           (fn2-retirement-controlp (fn2-inst-begin-put-b slot gen fn2-retirement-control)))
  :hints (("Goal" :in-theory (disable unsigned-byte-p fn2-retirement-controlp fn2-retirement-control-rows))))

(defthm fn2-inst-begin-put-b-wfp
  (implies (and (fn2-retirement-controlp fn2-retirement-control)
                (fn2-retirement-control-wfp fn2-retirement-control)
                (< 0 (fn2-retirement-control-rows fn2-retirement-control))
                (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen))
           (fn2-retirement-control-wfp (fn2-inst-begin-put-b slot gen fn2-retirement-control)))
  :hints (("Goal" :in-theory (disable unsigned-byte-p fn2-retirement-controlp fn2-retirement-control-wfp fn2-retirement-control-rows))))

(in-theory (disable fn2-inst-begin-put-b))

(make-event
 (let* ((body (fn2-commit-event-forms-1t))
        (pos-a (position-equal '(fn2-checkpoint-allocation-coordinator-events) body))
        (pos-i (position-equal '(fn2-checkpoint-installation-coordinator-events) body))
        (inst-progn (cadr (getpropc 'fn2-checkpoint-installation-coordinator-events 'macro-body nil (w state))))
        (inst-begin-fixed
         '(defun fn2-checkpoint-installation-begin (c token okind oslot ogen fn2-core)
            (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
            (b* (((unless (and (unsigned-byte-p 32 c) (posp token) (unsigned-byte-p 60 token)
                               (posp okind) (unsigned-byte-p 8 okind) (unsigned-byte-p 32 oslot) (unsigned-byte-p 60 ogen)
                               (not (fn2-core-stopped-p fn2-core)))) (mv :admission fn2-core))
                 ((mv ready ordinal)
                  (stobj-let ((fn2-checkpoints (fn2-core-checkpoints fn2-core))
                              (fn2-checkpoint-refs (fn2-core-checkpoint-refs fn2-core))
                              (fn2-checkpoint-construction (fn2-core-checkpoint-construction fn2-core))
                              (fn2-extents (fn2-core-extents fn2-core))
                              (fn2-retirement-control (fn2-core-retirement-control fn2-core))) (ready ordinal)
                   (mv (and (< 0 (fn2-retirement-control-rows fn2-retirement-control))
                            (= (fn2-retirement-control-state 0 fn2-retirement-control) *fn2-retirement-state-idle*)
                            (= (fn2-alloc-freeze-phase fn2-extents) 2) (= (fn2-alloc-freeze-token fn2-extents) token)
                            (= (fn2-alloc-freeze-owner-kind fn2-extents) okind)
                            (= (fn2-alloc-freeze-owner-slot fn2-extents) oslot) (= (fn2-alloc-freeze-owner-gen fn2-extents) ogen)
                            (fn2-checkpoint-builder-claimp c token okind oslot ogen fn2-checkpoints)
                            (= (fn2-checkpoints-state c fn2-checkpoints) *fn2-checkpoint-state-checked*)
                            (<= (* 6 (+ 1 c)) (fn2-checkpoint-refs-rows fn2-checkpoint-refs))
                            (fn2-checkpoint-production-roots-p 0 c token fn2-checkpoint-refs))
                       (fn2-construction-next-ticket fn2-checkpoint-construction)) (mv ready ordinal)))
                 ((unless ready) (mv :pending fn2-core))
                 ((mv code future-c future-token slot gen fn2-core)
                  (fn2-checkpoint-staging-claim c okind oslot ogen (fn2-checkpoint-installation-member-capacity) fn2-core))
                 ((unless (eq code :ok)) (mv code fn2-core))
                 ((unless (and (equal c future-c) (equal token future-token))) (mv :owner fn2-core)))
             (stobj-let ((fn2-retirement-control (fn2-core-retirement-control fn2-core))) (fn2-retirement-control)
              (if (and (< 0 (fn2-retirement-control-rows fn2-retirement-control))
                       (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen)
                       (unsigned-byte-p 60 ordinal))
                  (let ((fn2-retirement-control (fn2-inst-begin-put-a c ordinal token okind oslot ogen fn2-retirement-control)))
                    (fn2-inst-begin-put-b slot gen fn2-retirement-control))
                fn2-retirement-control)
              (mv :ok fn2-core)))))
        (inst-fixed (list* 'progn inst-begin-fixed (cddr inst-progn)))
        (wrapped
         `(encapsulate ()
            (local
             (in-theory (enable
                         (:forward-chaining fn2-checkpoint-construction-wfp-of-fn2-core-checkpoint-construction)
                         (:forward-chaining fn2-checkpoint-bytes-wfp-of-fn2-core-checkpoint-bytes))))
            (local
             (defthm fn2-checkpoint-builder-claimp-bounds-fc
               (implies (fn2-checkpoint-builder-claimp c token okind oslot ogen fn2-checkpoints)
                        (and (natp c)
                             (< c (fn2-checkpoints-rows fn2-checkpoints))
                             (posp token)))
               :rule-classes :forward-chaining
               :hints (("Goal" :in-theory (enable fn2-checkpoint-builder-claimp)))))
            (make-event
             (value `(local (in-theory (disable nth
                       fn2-core-wfp
                       fn2-checkpoint-builder-claimp
                       fn2-checkpoint-production-roots-p
                       fn2-alloc-handle-code
                       fn2-checkpoint-future-bind
                       fn2-checkpoint-future-lease
                       fn2-checkpoint-future-staging-return
                       fn2-pool-reset
                       fn2-pool-cap
                       ,@(fn2-columns-getter-runes
                           '(fn2-extents fn2-checkpoint-construction fn2-retirement-control
                             fn2-checkpoint-future fn2-checkpoint-future-windows
                             fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes
                             fn2-fields fn2-pool)
                           (w state)))))))
            (local
             (defthm fn2-checkpoint-staging-claim-candidate-u32
               (and (natp (mv-nth 1 (fn2-checkpoint-staging-claim expected-c okind oslot ogen need fn2-core)))
                    (< (mv-nth 1 (fn2-checkpoint-staging-claim expected-c okind oslot ogen need fn2-core)) 4294967296)
                    (unsigned-byte-p 32 (mv-nth 1 (fn2-checkpoint-staging-claim expected-c okind oslot ogen need fn2-core))))
               :rule-classes (:rewrite
                              (:type-prescription :typed-term (mv-nth 1 (fn2-checkpoint-staging-claim expected-c okind oslot ogen need fn2-core)))
                              (:linear :trigger-terms ((mv-nth 1 (fn2-checkpoint-staging-claim expected-c okind oslot ogen need fn2-core)))))
               :hints (("Goal" :in-theory (e/d (fn2-checkpoint-staging-claim)
                                               (fn2-checkpoint-future-bind fn2-checkpoint-future-lease
                                                fn2-pool-reset fn2-checkpoint-future-candidate
                                                fn2-checkpoint-future-rows fn2-checkpoint-future-windows-rows
                                                fn2-checkpoint-future-windows-borrowed fn2-alloc-freeze-token))))))
            (local
             (defthm fn2-checkpoint-staging-current-candidate-u32
               (and (natp (mv-nth 1 (fn2-checkpoint-staging-current okind oslot ogen need fn2-core)))
                    (< (mv-nth 1 (fn2-checkpoint-staging-current okind oslot ogen need fn2-core)) 4294967296)
                    (unsigned-byte-p 32 (mv-nth 1 (fn2-checkpoint-staging-current okind oslot ogen need fn2-core))))
               :rule-classes (:rewrite
                              (:type-prescription :typed-term (mv-nth 1 (fn2-checkpoint-staging-current okind oslot ogen need fn2-core)))
                              (:linear :trigger-terms ((mv-nth 1 (fn2-checkpoint-staging-current okind oslot ogen need fn2-core)))))
               :hints (("Goal" :in-theory (e/d (fn2-checkpoint-staging-current)
                                               (fn2-checkpoint-staging-claim
                                                fn2-checkpoint-future-rows fn2-checkpoint-future-candidate))))))
            (fn2-checkpoint-allocation-coordinator-events)
            ,inst-fixed)))
   (if (and pos-a pos-i (= (+ 1 pos-a) pos-i))
       (value (list* 'progn
                     (fn2-commit-local-theory)
                     (fn2-commit-local-forward)
                     (fn2-commit-local-idp)
                     wrapped
                     (nthcdr (+ 1 pos-i) body)))
     (er soft 'assembly-callbacks-bt "Could not locate adjacent allocation/installation coordinator events in fn2-commit-event-forms-1t."))))
