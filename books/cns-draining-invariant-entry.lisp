; Actual entry and admission preservation are separate from direct-arm
; semantics under the original maintained accounting hypotheses.
(in-package "ACL2")
(include-book "cns-accounting-entry")
(include-book "cns-draining-effects")

(defthm fn2-cns-core-init-reservation-entry
  (fn2-cns-draining-reservedp (fn2-core-init profile core))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn2-core-init-partition-reservation-entry
                                   (ord *fn2-cns-admission-ordinal*)))
           :in-theory (disable fn2-core-init fn2-cns-draining-reservedp
                               fn2-machines-partition-reservedp))))

; Preserve the exact public take operation's live guard and scalar ABI.
; Registry child facts compose through the actual core face; no synthetic
; take or initializer substitutes for the served operation.
(defun fn2-cns-take-reservation-events (world)
  (declare (xargs :verify-guards nil))
  (let* ((child 'fn2-machine-take-fn2-cns-children)
         (face 'fn2-machine-take-fn2-cns)
         (child-call (cons child (getpropc child 'formals nil world)))
         (face-call (cons face (getpropc face 'formals nil world))))
    (if (or (not (getpropc child 'unnormalized-body nil world))
            (not (getpropc face 'unnormalized-body nil world))
            (not (equal (cdr child-call)
                        '(waiter ctl ctl-gen request fpos flen fkind tx-slot tx-gen
                          ordinal kind fn2-cns fn2-machines fn2-pool fn2-control)))
            (not (equal (cdr face-call)
                        '(waiter ctl ctl-gen request fpos flen fkind tx-slot tx-gen fn2-core)))
            (not (equal (getpropc child 'stobjs-out nil world)
                        '(nil nil nil fn2-cns fn2-machines fn2-pool fn2-control)))
            (not (equal (getpropc face 'stobjs-out nil world) '(nil nil nil fn2-core))))
        '((make-event (er soft 'fn2-cns-take-reservation-events
            "Actual CNS take child/core bodies or full result ABI are unavailable.")))
      `((defthm fn2-cns-take-children-reservation-preserved
          (implies
           (and ,@(fn2-lower-predicates
                    (remove-eq nil (getpropc child 'stobjs-in nil world)) "P")
                ,(getpropc child 'guard t world)
                (fn2-machines-partition-reservedp ordinal fn2-machines))
           (fn2-machines-partition-reservedp ordinal (mv-nth 4 ,child-call)))
          :rule-classes nil
          :hints (("Goal" :in-theory
                   (e/d (,child fn2-machines-free-head-of)
                        (fn2-machines-partition-reservedp fn2-machines-partition-install
                         fn2-machines-park-taken fn2-pool-reserve fn2-core-release-children
                         fn2-machines-free-headi fn2-cns-next-free
                         fn2-cnsp fn2-cns-wfp fn2-machinesp fn2-machines-wfp
                         fn2-poolp fn2-pool-wfp fn2-controlp fn2-control-wfp)))))
        (defthm fn2-cns-take-core-reservation-preserved
          (implies (and (fn2-corep fn2-core) ,(getpropc face 'guard t world)
                        (fn2-cns-draining-reservedp fn2-core))
                   (fn2-cns-draining-reservedp (mv-nth 3 ,face-call)))
          :rule-classes nil
          :hints (("Goal"
                   :use ((:instance fn2-cns-take-children-reservation-preserved
                            (fn2-cns (fn2-cns-table fn2-core))
                            (fn2-machines (fn2-core-machines fn2-core))
                            (fn2-pool (fn2-core-pool fn2-core))
                            (fn2-control (fn2-core-control fn2-core))
                            (ordinal *fn2-cns-admission-ordinal*) (kind *fn2-cns-kind*)))
                   :in-theory
                   (e/d (,face)
                        (,child fn2-cns-draining-reservedp fn2-machines-partition-reservedp
                         fn2-cns-table fn2-core-machines fn2-core-pool fn2-core-control
                         fn2-corep fn2-core-wfp)))))))))
(make-event (value (cons 'progn (fn2-cns-take-reservation-events (w state)))))
