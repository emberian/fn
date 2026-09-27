;; Teeth for books/config-carried-open.lisp's readback (PKT-601 (2),
;; fn-cfgc-readback-verified-is-the-reopen).  The authorization and the
;; carried candidate are tests/acl2/config-carried-open-tests.lisp (split so
;; each certifies under ten seconds); the history here is 5 records, not 50,
;; for the same reason.
;; The fixtures are books/config-carried-candidate's test book's (restated:
;; a test book is not included by another).
(in-package "ACL2")
(include-book "../../books/config-carried-open")
(include-book "../../books/codec-attach")
(include-book "std/testing/must-fail" :dir :system)

(defconst *fn-cfgct-events*
  (list (fn-store-retention-event-make :undertake 0 0 0
                                        "admin-history" "subject" "evidence" 10)
        (fn-store-retention-event-make :release 1 1 1
                                        "admin-history" "subject" "evidence" 0)))

(defun fn-cfgct-configs (i n)
  (declare (xargs :measure (nfix (- (nfix n) (nfix i)))))
  (if (and (natp i) (natp n) (< i n))
      (cons (fn-cfg-record-make i 2 (+ 1 i)
                                (list (fn-cfg-set-capacity (+ 1048576 i)))
                                *fn-cfg-default-stamp*)
            (fn-cfgct-configs (+ 1 i) n))
    nil))

(defconst *fn-cfgct-history*
  (cons *fn-cfg-default-record* (fn-cfgct-configs 1 5)))

(defconst *fn-cfgct-record*
  (fn-cfg-record-make 5 2 6 (list (fn-cfg-set-capacity 2097152))
                      *fn-cfg-default-stamp*))

(defconst *fn-cfgct-open* (fn-cpr-replay *fn-cfgct-history* *fn-cfgct-events*))

(defconst *fn-cfgct-configuration* (fn-cnode-config-replay *fn-cfgct-history*))

(defconst *fn-cfgct-opened* (fn-cpo-open-observed *fn-cfgct-history* 2 *fn-cfgct-events*))

(defconst *fn-cfgct-skip*
  (fn-cfg-record-make 5 2 8 (list (fn-cfg-set-capacity 2097152))
                      *fn-cfg-default-stamp*))

; -----------------------------------------------------------------------------
; PKT-601 (2): the published record read back
; (fn-cfgc-readback-verified-is-the-reopen).

(defconst *fn-cfgct-authorized* (fn-cfg-encode *fn-cfgct-record*))
(defconst *fn-cfgct-auth*
  (fn-native-admin-publication-authorize *fn-cfgct-events* 2 *fn-cfgct-history*
                                         *fn-cfgct-record* t nil 1000))
(defconst *fn-cfgct-reopened*
  (append *fn-cfgct-history*
          (list (fn-record-parse-value (fn-cfg-decode-exact *fn-cfgct-authorized*)))))
; The antecedents, non-degenerate: the authorization accepted generation 6,
; the octets decode to the record, the readback is those octets.
(assert-event (equal (fn-native-admin-publication-status *fn-cfgct-auth*) :accepted))
(assert-event (equal (fn-native-admin-publication-generation *fn-cfgct-auth*) 6))
(assert-event (equal *fn-cfgct-record*
                     (fn-record-parse-value (fn-cfg-decode-exact *fn-cfgct-authorized*))))
(assert-event (equal (fn-cfgc-readback-verdict *fn-cfgct-authorized* *fn-cfgct-authorized*
                                               6 2)
                     :verified))
; The conclusion: the reopen of the 6-record history succeeds at generation 6.
(assert-event (fn-sn-open-okp (fn-cpo-open-observed *fn-cfgct-reopened* 2 *fn-cfgct-events*)))
(assert-event (equal (fn-replay-result-kind (fn-cpr-replay *fn-cfgct-reopened*
                                                           *fn-cfgct-events*))
                     :ok))
(assert-event
 (equal (fn-cfg-generation
         (fn-cnode-config
          (fn-replay-result-node (fn-cpr-replay *fn-cfgct-reopened* *fn-cfgct-events*))))
        6))
; The other verdicts are reachable: other octets, another generation, a
; frontier past the record.
(defconst *fn-cfgct-skip-octets* (fn-cfg-encode *fn-cfgct-skip*))
(assert-event (equal (fn-cfgc-readback-verdict *fn-cfgct-skip-octets* *fn-cfgct-authorized*
                                               6 2)
                     :mismatch))
(assert-event (equal (fn-cfgc-readback-verdict *fn-cfgct-authorized* *fn-cfgct-authorized*
                                               7 2)
                     :generation-mismatch))
(assert-event (equal (fn-cfgc-readback-verdict *fn-cfgct-authorized* *fn-cfgct-authorized*
                                               6 3)
                     :before-frontier))

; The reopen over the skipping record fails: the witness for each removal.
(defconst *fn-cfgct-skip-reopened* (append *fn-cfgct-history* (list *fn-cfgct-skip*)))
(assert-event (equal *fn-cfgct-skip*
                     (fn-record-parse-value (fn-cfg-decode-exact *fn-cfgct-skip-octets*))))
(assert-event (not (fn-sn-open-okp (fn-cpo-open-observed *fn-cfgct-skip-reopened* 2
                                                         *fn-cfgct-events*))))

; (R1) the authorization accepted.  The skipping record, authorized as its own
; octets and read back as them at its generation 8: the authorization
; refuses it, the verdict is :verified, and the reopen fails.
(assert-event
 (and (not (equal (fn-native-admin-publication-status
                   (fn-native-admin-publication-authorize
                    *fn-cfgct-events* 2 *fn-cfgct-history* *fn-cfgct-skip* t nil 1000))
                  :accepted))
      (equal (fn-cfgc-readback-verdict *fn-cfgct-skip-octets* *fn-cfgct-skip-octets* 8 2)
             :verified)))
(must-fail
 (defthm fn-cfgct-readback-without-the-authorization
  (implies (and (equal record (fn-record-parse-value (fn-cfg-decode-exact authorized))) (equal (fn-cfgc-readback-verdict readback authorized generation
                                                 frontier)
                       :verified))
           (let ((reopened (append config-records
                                   (list (fn-record-parse-value
                                          (fn-cfg-decode-exact readback))))))
             (and (fn-sn-open-okp (fn-cpo-open-observed reopened frontier records))
                  (equal (fn-replay-result-kind (fn-cpr-replay reopened records)) :ok)
                  (equal (fn-cfg-generation
                          (fn-cnode-config
                           (fn-replay-result-node (fn-cpr-replay reopened records))))
                         generation))))
  :hints (("Goal"
            :do-not-induct t
            :use ((:instance fn-cfgc-open-okp-is-observed
                             (configs (append config-records (list record)))
                             (events records))
                  (:instance fn-cfgc-observed-is-below
                             (events records)
                             (bound (fn-cfg-record-txid record)))
                  (:instance fn-cfgc-cpr-replay-of-one-more
                             (configs (true-list-fix config-records)) (events records))
                  (:instance fn-cfgc-cpr-loop-one-config-generation
                             (cn (fn-replay-result-node
                                  (fn-cpr-replay (true-list-fix config-records) records)))
                             (r record) (cs (len (true-list-fix config-records)))
                             (es (len records))))
            :in-theory (e/d (fn-native-admin-publication-authorize
                             fn-native-admin-candidate-openp
                             fn-native-admin-candidate-open-result
                             fn-cfgc-readback-verdict fn-cfgc-cpr-extend)
                            (fn-cpo-open-observed fn-cpr-replay fn-cpr-loop
                             fn-cnode-config-replay fn-sn-observed-historyp
                             fn-cfgc-events-below fn-native-admin-config-name
                             fn-cfg-recordp fn-cfg-decode-exact
                             fn-cfgc-open-okp-is-observed fn-cfgc-observed-is-below
                             fn-cfgc-cpr-replay-of-one-more
                             fn-cfgc-cpr-loop-one-config-generation
                             fn-sn-open-okp fn-cnode-statep))))))

; (R2) the authorized octets are the accepted record's.  The authorization
; accepted the record at generation 6; the octets published are the skipping
; record's, read back as themselves at 8: the reopen fails.
(assert-event
 (and (equal (fn-native-admin-publication-status *fn-cfgct-auth*) :accepted)
      (not (equal *fn-cfgct-record*
                  (fn-record-parse-value (fn-cfg-decode-exact *fn-cfgct-skip-octets*))))
      (equal (fn-cfgc-readback-verdict *fn-cfgct-skip-octets* *fn-cfgct-skip-octets* 8 2)
             :verified)))
(must-fail
 (defthm fn-cfgct-readback-without-the-authorized-octets
  (implies (and (equal (fn-native-admin-publication-status
                        (fn-native-admin-publication-authorize
                         records frontier config-records record lock-owned
                         observed-names max-generations))
                       :accepted) (equal (fn-cfgc-readback-verdict readback authorized generation
                                                 frontier)
                       :verified))
           (let ((reopened (append config-records
                                   (list (fn-record-parse-value
                                          (fn-cfg-decode-exact readback))))))
             (and (fn-sn-open-okp (fn-cpo-open-observed reopened frontier records))
                  (equal (fn-replay-result-kind (fn-cpr-replay reopened records)) :ok)
                  (equal (fn-cfg-generation
                          (fn-cnode-config
                           (fn-replay-result-node (fn-cpr-replay reopened records))))
                         generation))))
  :hints (("Goal"
            :do-not-induct t
            :use ((:instance fn-cfgc-open-okp-is-observed
                             (configs (append config-records (list record)))
                             (events records))
                  (:instance fn-cfgc-observed-is-below
                             (events records)
                             (bound (fn-cfg-record-txid record)))
                  (:instance fn-cfgc-cpr-replay-of-one-more
                             (configs (true-list-fix config-records)) (events records))
                  (:instance fn-cfgc-cpr-loop-one-config-generation
                             (cn (fn-replay-result-node
                                  (fn-cpr-replay (true-list-fix config-records) records)))
                             (r record) (cs (len (true-list-fix config-records)))
                             (es (len records))))
            :in-theory (e/d (fn-native-admin-publication-authorize
                             fn-native-admin-candidate-openp
                             fn-native-admin-candidate-open-result
                             fn-cfgc-readback-verdict fn-cfgc-cpr-extend)
                            (fn-cpo-open-observed fn-cpr-replay fn-cpr-loop
                             fn-cnode-config-replay fn-sn-observed-historyp
                             fn-cfgc-events-below fn-native-admin-config-name
                             fn-cfg-recordp fn-cfg-decode-exact
                             fn-cfgc-open-okp-is-observed fn-cfgc-observed-is-below
                             fn-cfgc-cpr-replay-of-one-more
                             fn-cfgc-cpr-loop-one-config-generation
                             fn-sn-open-okp fn-cnode-statep))))))

; (R3) the verdict.  The authorization and its octets are the record's; the
; file read back holds the skipping record: the verdict is :mismatch and the
; reopen of what the directory holds fails.
(assert-event
 (and (equal (fn-native-admin-publication-status *fn-cfgct-auth*) :accepted)
      (equal *fn-cfgct-record*
             (fn-record-parse-value (fn-cfg-decode-exact *fn-cfgct-authorized*)))
      (not (equal (fn-cfgc-readback-verdict *fn-cfgct-skip-octets* *fn-cfgct-authorized*
                                            6 2)
                  :verified))))
(must-fail
 (defthm fn-cfgct-readback-without-the-verdict
  (implies (and (equal (fn-native-admin-publication-status
                        (fn-native-admin-publication-authorize
                         records frontier config-records record lock-owned
                         observed-names max-generations))
                       :accepted) (equal record (fn-record-parse-value (fn-cfg-decode-exact authorized))))
           (let ((reopened (append config-records
                                   (list (fn-record-parse-value
                                          (fn-cfg-decode-exact readback))))))
             (and (fn-sn-open-okp (fn-cpo-open-observed reopened frontier records))
                  (equal (fn-replay-result-kind (fn-cpr-replay reopened records)) :ok)
                  (equal (fn-cfg-generation
                          (fn-cnode-config
                           (fn-replay-result-node (fn-cpr-replay reopened records))))
                         generation))))
  :hints (("Goal"
            :do-not-induct t
            :use ((:instance fn-cfgc-open-okp-is-observed
                             (configs (append config-records (list record)))
                             (events records))
                  (:instance fn-cfgc-observed-is-below
                             (events records)
                             (bound (fn-cfg-record-txid record)))
                  (:instance fn-cfgc-cpr-replay-of-one-more
                             (configs (true-list-fix config-records)) (events records))
                  (:instance fn-cfgc-cpr-loop-one-config-generation
                             (cn (fn-replay-result-node
                                  (fn-cpr-replay (true-list-fix config-records) records)))
                             (r record) (cs (len (true-list-fix config-records)))
                             (es (len records))))
            :in-theory (e/d (fn-native-admin-publication-authorize
                             fn-native-admin-candidate-openp
                             fn-native-admin-candidate-open-result
                             fn-cfgc-readback-verdict fn-cfgc-cpr-extend)
                            (fn-cpo-open-observed fn-cpr-replay fn-cpr-loop
                             fn-cnode-config-replay fn-sn-observed-historyp
                             fn-cfgc-events-below fn-native-admin-config-name
                             fn-cfg-recordp fn-cfg-decode-exact
                             fn-cfgc-open-okp-is-observed fn-cfgc-observed-is-below
                             fn-cfgc-cpr-replay-of-one-more
                             fn-cfgc-cpr-loop-one-config-generation
                             fn-sn-open-okp fn-cnode-statep))))))
