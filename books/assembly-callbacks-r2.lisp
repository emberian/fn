; The commit kind's second section, second half: install, publish,
; settlement, drop and the drain's operations, then the kind's arms
; (commit-arms.lisp, generated here) and its run (split from
; assembly-callbacks-r under the one-minute rule).
(in-package "ACL2")

(include-book "commit-arms")
(make-event
 (let* ((body (fn2-commit-event-forms-2b))
        (pos (position-equal '(fn2-checkpoint-retirement-install-events) body))
        (adapter (fn2-checkpoint-retirement-adapter))
        (prefix (cdr (assoc-equal 'fn2-retirement-adapter-install-prefix adapter)))
        (full-install (fn2-retirement-adapt
                       '(progn
                          (defun fn2-commit-lifecycle-step (id member off fn2-core)
                            (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
                            (b* (((unless (and (fn2-commit-idp id fn2-core)
                                               (fn2-commit-lifecycle-cursorp (fn2-machine-member-count id fn2-core) member off)
                                               (= (fn2-machine-phase id fn2-core) *fn2-commit-state-publish*)
                                               (= (fn2-machine-cb-deps-ok id fn2-core) 1)
                                               (= (fn2-machine-cb-log-ok id fn2-core) 1)
                                               (= (fn2-machine-cb-fence-ok id fn2-core) 1)
                                               (= (fn2-machine-cb-failed id fn2-core) 0)))
                                  (mv :invalid 0 0 fn2-core))
                                 (batch (fn2-machine-batch-no id fn2-core))
                                 (event (+ (fn2-machine-first-key id fn2-core) member))
                                 (installed (stobj-let ((fn2-commit-root (fn2-core-commit-root fn2-core))) (installed)
                                              (and (< 0 (fn2-commit-root-rows fn2-commit-root))
                                                   (= (fn2-commit-root-installed 0 fn2-commit-root) batch)) installed))
                                 ((unless installed) (mv :invalid 0 0 fn2-core))
                                 ((when (= member (fn2-machine-member-count id fn2-core))) (mv :done member 0 fn2-core))
                                 ((mv found kind slot gen len okind oslot ogen)
                                  (fn2-commit-member-ws (+ (* *fn2-commit-members-per-batch* (fn2-commit-row id fn2-core)) member) fn2-core))
                                 ((unless found) (mv :invalid 0 0 fn2-core))
                                 ((when (not (= kind *fn2-commit-member-kind-txn*))) (mv :more (+ 1 member) 0 fn2-core))
                                 ((when (= off len)) (mv :more (+ 1 member) 0 fn2-core))
                                 ((unless (< off len)) (mv :invalid 0 0 fn2-core))
                                 (base (* 128 (fn2-commit-row id fn2-core)))
                                 ((mv framed rkind bytes next fn2-core)
                                  (fn2-commit-txn-frame base slot gen off len okind oslot ogen fn2-core))
                                 ((unless (and (eq framed :ok) (< off next) (<= (+ next bytes) len)))
                                  (mv :invalid 0 0 fn2-core))
                                 ((unless (or (not (member-equal rkind (list *record-kind-allocation* *record-kind-checkpoint-installation*)))
                                              fn2-retirement-adapter-record-match)) (mv :invalid 0 0 fn2-core))
                                 ((mv code fn2-core)
                                  (if (= rkind *record-kind-checkpoint-installation*)
                                      fn2-retirement-adapter-installation
                                   (if (= rkind *record-kind-allocation*)
                                      fn2-retirement-adapter-allocation
                                   (if (not (= rkind *record-kind-retirement*)) (mv :ok fn2-core)
                                   (stobj-let ((fn2-fields (fn2-core-fields fn2-core))
                                               (fn2-pool (fn2-core-pool fn2-core))
                                               (fn2-extents (fn2-core-extents fn2-core))
                                               (fn2-retirement-control (fn2-core-retirement-control fn2-core)))
                                    (code fn2-fields fn2-extents)
                                    (if (not (and (natp base) (<= (+ base *fn2-format-retirement-num-fields*) (fn2-fields-rows fn2-fields))
                                                  (unsigned-byte-p 32 next) (unsigned-byte-p 32 (+ next bytes))
                                                  (unsigned-byte-p 8 okind) (unsigned-byte-p 32 oslot) (unsigned-byte-p 60 ogen)))
                                        (mv :invalid fn2-fields fn2-extents)
                                     (mv-let (decoded end fn2-fields)
                                      (fn2-format-retirement-decode base slot gen next (+ next bytes) okind oslot ogen fn2-fields fn2-pool)
                                      (if (not (and (eq decoded :ok) (= end (+ next bytes))
                                                    (< 0 (fn2-retirement-control-rows fn2-retirement-control))
                                                    (= (fn2-retirement-control-state 0 fn2-retirement-control) *fn2-retirement-state-waiting*)
                                                    (= (fn2-retirement-control-allocation-member 0 fn2-retirement-control) 0)
                                                    (= (fn2-retirement-control-installation-member 0 fn2-retirement-control) 0)
                                                    (= (fn2-retirement-control-event 0 fn2-retirement-control) event)
                                                    (= (fn2-retirement-control-slot 0 fn2-retirement-control) slot)
                                                    (= (fn2-retirement-control-gen 0 fn2-retirement-control) gen)
                                                    (= (fn2-retirement-control-batch 0 fn2-retirement-control) batch)
                                                    (= (fn2-retirement-control-owner-kind 0 fn2-retirement-control) okind)
                                                    (= (fn2-retirement-control-owner-slot 0 fn2-retirement-control) oslot)
                                                    (= (fn2-retirement-control-owner-gen 0 fn2-retirement-control) ogen)
                                                    (= (fn2-retirement-control-extent 0 fn2-retirement-control)
                                                       (fn2-fields-value (+ base *fn2-format-retirement-field-extent*) fn2-fields))
                                                    (= (fn2-retirement-control-epoch 0 fn2-retirement-control)
                                                       (fn2-fields-value (+ base *fn2-format-retirement-field-writer-epoch*) fn2-fields))
                                                    (= (fn2-retirement-control-allocation 0 fn2-retirement-control)
                                                       (fn2-fields-value (+ base *fn2-format-retirement-field-allocation*) fn2-fields))
                                                    (fn2-alloc-retirement-intentp
                                                     (fn2-retirement-control-extent 0 fn2-retirement-control)
                                                     (fn2-retirement-control-epoch 0 fn2-retirement-control)
                                                     (fn2-retirement-control-allocation 0 fn2-retirement-control) fn2-extents)
                                                    (= batch (fn2-alloc-retirement-intent-batch fn2-extents))))
                                          (mv :invalid fn2-fields fn2-extents)
                                       (mv-let (code fn2-extents) (fn2-retirement-install batch base fn2-fields fn2-extents)
                                        (mv code fn2-fields fn2-extents)))))
                                    (mv code fn2-core)))))))
                             (mv (if (eq code :ok) :more :invalid) member (+ next bytes) fn2-core)))
                          (fn2-core-preserves fn2-commit-lifecycle-step (id member off fn2-core) :position 3 :rows nil)
                          (defthm fn2-commit-lifecycle-step-naturals
                            (and (natp (mv-nth 1 (fn2-commit-lifecycle-step id member off fn2-core)))
                                 (natp (mv-nth 2 (fn2-commit-lifecycle-step id member off fn2-core))))
                            :hints (("Goal" :in-theory (enable fn2-commit-lifecycle-step)))))
                       adapter))
        (replacement
         `(progn
            (encapsulate ()
              (local
               (in-theory (enable
                           (:forward-chaining fn2-checkpoint-construction-wfp-of-fn2-core-checkpoint-construction)
                           (:forward-chaining fn2-checkpoint-bytes-wfp-of-fn2-core-checkpoint-bytes)
                           (:forward-chaining fn2-ops-wfp-of-fn2-core-ops))))
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
                         remove-weak-inequalities-one
                         remove-weak-inequalities-two
                         fn2-core-wfp
                         fn2-checkpoint-builder-claimp
                         fn2-checkpoint-allocation-install
                         fn2-checkpoint-install
                         fn2-format-allocation-decode
                         fn2-format-checkpoint-installation-decode
                         ,@(fn2-columns-getter-runes
                             '(fn2-extents fn2-checkpoint-construction fn2-retirement-control
                               fn2-checkpoint-future fn2-checkpoint-future-windows
                               fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes
                               fn2-fields fn2-pool fn2-alloc-edges fn2-ops)
                             (w state)))))))
              ,prefix)
            (local
             (defthm fn2-commit-member-ws-types
               (implies (and (fn2-corep fn2-core)
                             (fn2-core-wfp fn2-core))
                        (and (natp (mv-nth 1 (fn2-commit-member-ws r fn2-core)))
                             (acl2-numberp (mv-nth 1 (fn2-commit-member-ws r fn2-core)))
                             (natp (mv-nth 2 (fn2-commit-member-ws r fn2-core)))
                             (unsigned-byte-p 32 (mv-nth 2 (fn2-commit-member-ws r fn2-core)))
                             (natp (mv-nth 3 (fn2-commit-member-ws r fn2-core)))
                             (unsigned-byte-p 60 (mv-nth 3 (fn2-commit-member-ws r fn2-core)))
                             (natp (mv-nth 4 (fn2-commit-member-ws r fn2-core)))
                             (acl2-numberp (mv-nth 4 (fn2-commit-member-ws r fn2-core)))
                             (unsigned-byte-p 32 (mv-nth 4 (fn2-commit-member-ws r fn2-core)))
                             (natp (mv-nth 5 (fn2-commit-member-ws r fn2-core)))
                             (unsigned-byte-p 8 (mv-nth 5 (fn2-commit-member-ws r fn2-core)))
                             (natp (mv-nth 6 (fn2-commit-member-ws r fn2-core)))
                             (unsigned-byte-p 32 (mv-nth 6 (fn2-commit-member-ws r fn2-core)))
                             (natp (mv-nth 7 (fn2-commit-member-ws r fn2-core)))
                             (unsigned-byte-p 60 (mv-nth 7 (fn2-commit-member-ws r fn2-core)))))
               :hints (("Goal" :in-theory (e/d (fn2-commit-member-ws)
                                               (nth fn2-core-wfp
                                                    ,@(fn2-columns-getter-runes
                                                        '(fn2-commit-member)
                                                        (w state))))))))
            (local
             (defthm fn2-format-retirement-scan-next-natp
               (implies (natp next)
                        (natp (mv-nth 1 (fn2-format-retirement-scan
                                         fuel base phase pos v hi size ref payload next
                                         slot gen end okind oslot ogen fn2-fields fn2-pool))))
               :hints (("Goal"
                        :induct (fn2-format-retirement-scan
                                 fuel base phase pos v hi size ref payload next
                                 slot gen end okind oslot ogen fn2-fields fn2-pool)
                        :in-theory (e/d (fn2-format-retirement-scan)
                                        (nth fn2-pool-read fn2-layout-store
                                             fn2-format-retirement-byte
                                             fn2-format-retirement-empty-p
                                             fn2-format-retirement-field-index
                                             fn2-format-retirement-next-phase
                                             ,@(fn2-columns-getter-runes '(fn2-fields) (w state))))))))
            (local
             (defthm fn2-format-retirement-decode-step-next-natp
               (implies (and (natp off)
                             (fn2-fieldsp fn2-fields)
                             (fn2-fields-wfp fn2-fields)
                             (natp base)
                             (< base (fn2-fields-rows fn2-fields)))
                        (natp (mv-nth 1 (fn2-format-retirement-decode-step
                                         base slot gen off end okind oslot ogen budget
                                         fn2-fields fn2-pool))))
               :hints (("Goal"
                        :in-theory (e/d (fn2-format-retirement-decode-step)
                                        (nth fn2-layout-range-code fn2-format-retirement-scan
                                             ,@(fn2-columns-getter-runes '(fn2-fields) (w state))))))))
            (local
             (defthm fn2-format-retirement-decode-next-natp
               (implies (and (natp off)
                             (fn2-fieldsp fn2-fields)
                             (fn2-fields-wfp fn2-fields)
                             (natp base)
                             (< base (fn2-fields-rows fn2-fields)))
                        (and (natp (mv-nth 1 (fn2-format-retirement-decode
                                              base slot gen off end okind oslot ogen
                                              fn2-fields fn2-pool)))
                             (acl2-numberp (mv-nth 1 (fn2-format-retirement-decode
                                                      base slot gen off end okind oslot ogen
                                                      fn2-fields fn2-pool)))))
               :hints (("Goal"
                        :in-theory (e/d (fn2-format-retirement-decode)
                                        (fn2-format-retirement-start
                                         fn2-format-retirement-decode-step))))))
            (local
             (defthm fn2-r2-core-child-shapes-rewrite
               (and (implies (fn2-corep c) (fn2-fieldsp (fn2-core-fields c)))
                    (implies (fn2-core-wfp c) (fn2-fields-wfp (fn2-core-fields c)))
                    (implies (fn2-corep c) (fn2-poolp (fn2-core-pool c)))
                    (implies (fn2-core-wfp c) (fn2-pool-wfp (fn2-core-pool c)))
                    (implies (fn2-corep c) (fn2-extentsp (fn2-core-extents c)))
                    (implies (fn2-core-wfp c) (fn2-extents-wfp (fn2-core-extents c)))
                    (implies (fn2-corep c) (fn2-retirement-controlp (fn2-core-retirement-control c)))
                    (implies (fn2-core-wfp c) (fn2-retirement-control-wfp (fn2-core-retirement-control c))))
               :hints (("Goal" :in-theory (disable fn2-core-wfp)))))
            (encapsulate ()
              (make-event
               (value `(local (in-theory (disable nth
                         remove-weak-inequalities-one
                         remove-weak-inequalities-two
                         fn2-retirement-controlp
                         fn2-retirement-control-wfp
                         fn2-retirement-control-rows
                         fn2-format-retirement-decode
                         fn2-retirement-install
                         fn2-checkpoint-staging-match-p
                         fn2-checkpoint-installation-install-member
                         fn2-checkpoint-allocation-install-member
                         ,@(fn2-columns-getter-runes
                             '(fn2-retirement-control fn2-fields fn2-extents)
                             (w state)))))))
              ,full-install))))
   (if pos
       (value (append (take pos body) (cons replacement (nthcdr (+ 1 pos) body))))
     (er soft 'assembly-callbacks-r2 "Could not locate (fn2-checkpoint-retirement-install-events) in fn2-commit-event-forms-2b."))))
