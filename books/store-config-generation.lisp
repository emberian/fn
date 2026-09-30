; PKT-183: configuration namespace contiguity through the actual replay.
(in-package "ACL2")
(include-book "store-capacity-config")

(local
 (defun fn-cvcg-induct (cn ceiling records expected)
   (declare (xargs :measure (acl2-count records)
                   :guard (and (fn-cnode-statep cn) (acl2-numberp expected))
                   :verify-guards nil))
   (if (consp records)
       (fn-cvcg-induct (fn-cnode-apply-config cn (car records) ceiling)
                       ceiling (cdr records) (+ 1 expected))
     (list cn expected))))

(local
 (verify-guards fn-cvcg-induct
   :hints (("Goal" :in-theory
            (enable fn-cnode-apply-config-preserves-state)))))

(local
 (defthm fn-cvcg-state-generation-is-natural
   (implies (fn-cnode-statep cn)
            (natp (fn-cfg-generation (fn-cnode-config cn))))
   :hints (("Goal" :use fn-cnode-statep-forward-cfgp
            :in-theory (enable fn-cfgp fn-cfg-generation)))))

(local
 (defthm fn-cvcg-successful-config-loop-counts-records
   (implies
    (equal (fn-replay-result-kind
            (fn-cnode-replay-loop cn ceiling (fn-cnode-config-jrecs records)
                                  expected)) :ok)
    (equal (fn-cfg-generation
            (fn-cnode-config
             (fn-replay-result-node
              (fn-cnode-replay-loop cn ceiling (fn-cnode-config-jrecs records)
                                    expected))))
           (+ (fn-cfg-generation (fn-cnode-config cn)) (len records))))
   :hints (("Goal"
            :induct (fn-cvcg-induct cn ceiling records expected)
            :expand ((fn-cnode-replay-loop cn ceiling
                      (fn-cnode-config-jrecs records) expected))
            :in-theory
            (e/d (fn-cnode-config-jrecs fn-cnode-replay-loop
                  fn-cnode-apply-config-bumps-the-generation
                  fn-replay-ok fn-replay-fault
                  fn-replay-result-kind fn-replay-result-node
                  fn-jrec-make fn-jrec-kind fn-jrec-body fn-jrec-sequence
                  fn-cfg-ag-car fn-cfg-ag-cdr)
                 (fn-cnode-statep fn-cnode-record-acceptablep
                  fn-cnode-apply-config fn-cnode-apply-record
                  fn-cfg-generation fn-cnode-config)))
           ("Subgoal *1/2" :use fn-cvcg-state-generation-is-natural))))

; Native publication obtains CURRENT from this replay; successful replay's
; generation is the cardinality of its exact configuration record prefix.
(defthm fn-cvcg-config-replay-generation-counts-records
  (implies (equal (fn-replay-result-kind (fn-cnode-config-replay records)) :ok)
           (equal (fn-cfg-generation
                   (fn-cnode-config
                    (fn-replay-result-node (fn-cnode-config-replay records))))
                  (len records)))
  :hints (("Goal"
           :use ((:instance fn-cvcg-successful-config-loop-counts-records
                            (cn (fn-cnode-initial (fn-cfg-initial)))
                            (ceiling (fn-cnode-line-ceiling)) (expected 0)))
           :in-theory
           (e/d (fn-cnode-config-replay fn-cnode-replay fn-cnode-initial
                 fn-cfg-initial fn-cfg-generation)
                (fn-cnode-statep fn-cnode-config-jrecs fn-cnode-replay-loop
                 fn-cnode-line-ceiling)))))

(local
 (defthm fn-cvcg-native-publication-generation-is-next-count
   (implies
    (equal (fn-native-admin-publication-status
            (fn-native-admin-publication-authorize
             records frontier config-records record lock-owned observed-names
             max-generations)) :accepted)
    (equal (fn-native-admin-publication-generation
            (fn-native-admin-publication-authorize
             records frontier config-records record lock-owned observed-names
             max-generations))
           (+ 1 (len config-records))))
   :hints (("Goal"
            :use ((:instance fn-cvcg-config-replay-generation-counts-records
                             (records config-records)))
            :in-theory
            (e/d (fn-native-admin-publication-authorize
                  fn-native-admin-publication-result
                  fn-native-admin-publication-status
                  fn-native-admin-publication-generation)
                 (fn-cnode-config-replay fn-native-admin-candidate-openp
                  fn-native-admin-config-name fn-cfg-recordp))))))

; The actual profile-aware writer's authorized next record fits the
; configuration listing bound because its generation IS the next count.
; Counts here are exact records, not caller-supplied generation estimates.
(defthm fn-cvcg-accepted-publication-count-fits-profile
  (let ((answer (fn-cvec-native-admin-authorize
                 records frontier config-records record lock-owned
                 observed-names profile)))
    (implies
     (equal (fn-native-admin-publication-status answer) :accepted)
     (and (equal (fn-native-admin-publication-generation answer)
                 (+ 1 (len config-records)))
          (<= (+ 1 (len config-records))
              (nfix (fn-bs-profile-max-config-generations profile))))))
  :hints (("Goal"
           :use ((:instance fn-cvcg-native-publication-generation-is-next-count
                            (max-generations (fn-cvec-config-generations profile record)))
                 (:instance fn-native-admin-publication-within-the-operator-bound
                            (max-generations (fn-cvec-config-generations profile record))))
           :in-theory
           (union-theories
            (theory 'minimal-theory)
            '(fn-cvec-native-admin-authorize fn-cvec-config-generations
              fn-native-admin-publication-status fn-native-admin-publication-result
              fn-ag-car car-cons cdr-cons nfix natp)))))
