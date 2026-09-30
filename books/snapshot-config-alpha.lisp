; PRF-1115: complete configured replay alpha and configuration suffix.
(in-package "ACL2")
(include-book "snapshot-node-alpha")
(include-book "config-physical-replay")
(local (in-theory (disable (tau-system))))
(defun fn-osa-cnode-alpha (cn fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (list (fn-osa-node-alpha (fn-cnode-node cn) fn-arena)
        (fn-cnode-config cn)))
(in-theory (disable fn-osa-cnode-alpha))
(local
 (defthm fn-osa-cnode-state-has-node-state-by-definition
   (implies (fn-cnode-statep cn) (fn-node-statep (fn-cnode-node cn)))
   :hints (("Goal" :in-theory (enable fn-cnode-statep)))))
(local
 (defthm fn-osa-config-node-advance-keeps-full-alpha
   (implies (and (fn-node-statep a) (fn-node-statep b)
                 (equal (fn-osa-node-alpha a source)
                        (fn-osa-node-alpha b target)))
            (equal (fn-osa-node-alpha (fn-replay-advance-txid a txid) source)
                   (fn-osa-node-alpha (fn-replay-advance-txid b txid) target)))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-osa-node-alpha fn-osa-acceptance-alpha
                             fn-osa-pending-alpha fn-replay-advance-txid)
                            (fn-node-statep fn-statep fn-node-make-state
                             fn-make-state fn-handle-bytes fn-articles-wire-of))))))
(defthm fn-osa-cnode-alpha-keeps-config-check-by-definition
   (implies (equal (fn-osa-cnode-alpha a source) (fn-osa-cnode-alpha b target))
            (equal (fn-cnode-record-acceptablep a record ceiling)
                   (fn-cnode-record-acceptablep b record ceiling)))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn-osa-cnode-alpha fn-osa-node-alpha
                                      fn-cnode-record-acceptablep)
                                     (fn-cfg-record-acceptablep fn-osa-acceptance-alpha)))))
(defthm fn-osa-config-transition-keeps-complete-alpha
   (implies (and (fn-cnode-statep a) (fn-cnode-statep b)
                 (equal (fn-osa-cnode-alpha a source) (fn-osa-cnode-alpha b target)))
            (equal (fn-osa-cnode-alpha (fn-cnode-apply-config a record ceiling) source)
                   (fn-osa-cnode-alpha (fn-cnode-apply-config b record ceiling) target)))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :use (fn-osa-cnode-alpha-keeps-config-check-by-definition)
            :in-theory (e/d (fn-osa-cnode-alpha fn-osa-node-alpha
                             fn-osa-acceptance-alpha fn-osa-pending-alpha
                             fn-cnode-apply-config)
                            (fn-cnode-statep fn-cnode-record-acceptablep
                             fn-node-statep fn-statep fn-node-make-state
                             fn-make-state fn-retain-make-state
                             fn-articles-wire-of fn-cfg-apply-record
                             fn-cnode-extend-nexts fn-cnode-domain-of)))))
(defthm fn-osa-cnode-advance-keeps-complete-alpha
   (implies (and (fn-cnode-statep a) (fn-cnode-statep b)
                 (equal (fn-osa-cnode-alpha a source) (fn-osa-cnode-alpha b target)))
            (equal (fn-osa-cnode-alpha (fn-cnode-make
                    (fn-replay-advance-txid (fn-cnode-node a) txid) (fn-cnode-config a)) source)
                   (fn-osa-cnode-alpha (fn-cnode-make
                    (fn-replay-advance-txid (fn-cnode-node b) txid) (fn-cnode-config b)) target)))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn-osa-config-node-advance-keeps-full-alpha
                         (a (fn-cnode-node a)) (b (fn-cnode-node b))))
            :in-theory (e/d (fn-osa-cnode-alpha)
                            (fn-osa-node-alpha fn-replay-advance-txid fn-cnode-statep)))))

(defun fn-osa-cpr-result-alpha (result fn-arena)
 (declare (xargs :stobjs fn-arena :guard t))
 (list (fn-replay-result-kind result)
       (fn-osa-cnode-alpha (fn-replay-result-node result) fn-arena)
       (fn-replay-result-sequence result) (fn-replay-result-reason result)))
(in-theory (disable fn-osa-cpr-result-alpha))
(defthm fn-osa-cnode-alpha-keeps-advance-control-by-definition
  (implies (and (fn-cnode-statep a) (fn-cnode-statep b)
                (equal (fn-osa-cnode-alpha a source) (fn-osa-cnode-alpha b target)))
           (equal (fn-replay-advance-okp (fn-cnode-node a) txid)
                  (fn-replay-advance-okp (fn-cnode-node b) txid)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-osa-cnode-alpha fn-osa-node-alpha
                                   fn-osa-acceptance-alpha fn-osa-pending-alpha fn-replay-advance-okp)
                                  (fn-articles-wire-of fn-node-statep fn-cnode-statep fn-handle-bytes)))))
(local
 (defun fn-osa-config-only-induct (a b configs cs es)
  (if (consp configs)
   (let* ((record (car configs)) (txid (fn-cfg-record-txid record))
          (at-a (fn-cnode-make (fn-replay-advance-txid (fn-cnode-node a) txid)
                               (fn-cnode-config a)))
          (at-b (fn-cnode-make (fn-replay-advance-txid (fn-cnode-node b) txid)
                               (fn-cnode-config b))))
    (fn-osa-config-only-induct
     (fn-cnode-apply-config at-a record (fn-cnode-line-ceiling))
     (fn-cnode-apply-config at-b record (fn-cnode-line-ceiling))
     (cdr configs) (1+ (nfix cs)) es))
   (list a b cs es))))
(defthm fn-osa-configuration-suffix-keeps-full-result-alpha
 (implies (and (fn-cnode-statep a) (fn-cnode-statep b)
               (equal (fn-osa-cnode-alpha a source) (fn-osa-cnode-alpha b target)))
          (equal (fn-osa-cpr-result-alpha (fn-cpr-loop a configs nil cs es) source)
                 (fn-osa-cpr-result-alpha (fn-cpr-loop b configs nil cs es) target)))
 :rule-classes nil
 :hints (("Goal" :induct (fn-osa-config-only-induct a b configs cs es)
          :in-theory (union-theories (theory 'minimal-theory)
           '((:induction fn-osa-config-only-induct) fn-cpr-loop fn-cpr-config-firstp fn-osa-cpr-result-alpha
             fn-replay-result-kind fn-replay-result-node fn-replay-result-sequence
             fn-replay-result-reason fn-replay-ok fn-replay-fault
             car-cons cdr-cons cons-equal)))
         ("Subgoal *1/1"
          :use ((:instance fn-osa-cnode-alpha-keeps-advance-control-by-definition
                    (txid (fn-cfg-record-txid (car configs))))
                (:instance fn-osa-cnode-advance-keeps-complete-alpha
                    (txid (fn-cfg-record-txid (car configs))))
                (:instance fn-cnode-advanced-node-is-configured (cn a)
                    (txid (fn-cfg-record-txid (car configs))))
                (:instance fn-cnode-advanced-node-is-configured (cn b)
                    (txid (fn-cfg-record-txid (car configs))))
                (:instance fn-osa-cnode-alpha-keeps-config-check-by-definition
                 (a (fn-cnode-make (fn-replay-advance-txid (fn-cnode-node a)
                                    (fn-cfg-record-txid (car configs))) (fn-cnode-config a)))
                 (b (fn-cnode-make (fn-replay-advance-txid (fn-cnode-node b)
                                    (fn-cfg-record-txid (car configs))) (fn-cnode-config b)))
                 (record (car configs)) (ceiling (fn-cnode-line-ceiling)))
                (:instance fn-osa-config-transition-keeps-complete-alpha
                 (a (fn-cnode-make (fn-replay-advance-txid (fn-cnode-node a)
                                    (fn-cfg-record-txid (car configs))) (fn-cnode-config a)))
                 (b (fn-cnode-make (fn-replay-advance-txid (fn-cnode-node b)
                                    (fn-cfg-record-txid (car configs))) (fn-cnode-config b)))
                 (record (car configs)) (ceiling (fn-cnode-line-ceiling)))
                (:instance fn-cnode-apply-config-preserves-state
                  (cn (fn-cnode-make (fn-replay-advance-txid (fn-cnode-node a)
                                    (fn-cfg-record-txid (car configs))) (fn-cnode-config a)))
                  (record (car configs)) (ceiling (fn-cnode-line-ceiling)))
                (:instance fn-cnode-apply-config-preserves-state
                  (cn (fn-cnode-make (fn-replay-advance-txid (fn-cnode-node b)
                                    (fn-cfg-record-txid (car configs))) (fn-cnode-config b)))
                  (record (car configs)) (ceiling (fn-cnode-line-ceiling)))))))
