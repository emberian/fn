; fn: the offline configuration request decides its candidate open from the
; open's own result, authorizes from the open's carried fold, and verifies by
; reading its published record back (PKT-510 (1), PKT-601 (1) and (2);
; lanes config-consumer-catalog and config-consumer-catalog-2).
;
; books/config-carried-candidate.lisp states the folds' one-step extensions
; and the candidate from the carried folds; this book adds what needs the
; open's success condition (books/store-open-bridge.lisp
; fn-cpo-open-observed-succeeds-exactly): the candidate open decided from the
; open's result, the authorization the host calls
; (host/store-node-host.lisp fn-store-cfg-native-admin-authorize-carried for
; host/native/admin.lisp fnn-admin-execute), and the readback verdict
; (host/native/admin.lisp fnn-admin-verify-under-lock).  Two books so that
; each certifies under ten seconds (D26).

(in-package "ACL2")
(include-book "config-carried-candidate")
(include-book "store-open-bridge")

; -----------------------------------------------------------------------------
; The candidate open, extended from the open's own success (PKT-601 (1)).
;
; The candidate open fn-cpo-open-observed of CONFIGS ++ (R) differs from the
; open's fn-cpo-open-observed of CONFIGS only in its configuration: the
; history shape, the identity, consumer and topic replays and the event index
; are functions of the Store history and the frontier alone, which the
; request does not change.  Its success is exactly the configured replay's
; (store-open-bridge fn-cpo-open-observed-succeeds-exactly), so given the
; open's success the candidate's is the extended fold's kind and the four
; scalar conditions under which a replayed node accepts the frontier; the
; node's whole-state recognizer is implied by the fold's success
; (fn-cpr-replay-ok-is-configured).  No record is revisited.

; fn-replay-advance-okp without its whole-state recognizer: the four scalar
; tests on the node the fold produced.
(defun fn-cfgc-advance-okp (node frontier)
  (declare (xargs :guard t))
  (let ((acceptance (fn-node-acceptance node)))
    (and (natp frontier)
         (null (fn-node-stage node))
         (null (fn-state-pending acceptance))
         (equal (fn-state-fenced acceptance) nil)
         (natp (fn-state-next-txid acceptance))
         (<= (fn-state-next-txid acceptance) frontier))))

(defthm fn-cfgc-advance-okp-is-replay-advance-okp
  (implies (fn-node-statep node)
           (equal (fn-cfgc-advance-okp node frontier)
                  (fn-replay-advance-okp node frontier)))
  :hints (("Goal" :in-theory (enable fn-replay-advance-okp fn-node-statep fn-statep))))

; The open's result kind is its success (the whole-state recognizer ran
; inside the open, before it answered :ok).
(defthm fn-cfgc-cpo-open-kind-ok-is-okp
  (equal (equal (fn-sn-open-kind (fn-cpo-open-observed configs frontier events)) :ok)
         (fn-sn-open-okp (fn-cpo-open-observed configs frontier events)))
  :hints (("Goal" :in-theory (e/d (fn-cpo-open-observed fn-sn-open-okp fn-sn-open-ok
                                   fn-sn-open-error fn-sn-open-kind fn-sn-open-state
                                   fn-sn-open-shapep)
                                  (fn-sn-statep fn-cpr-replay fn-cnode-statep
                                   fn-replay-advance-okp fn-sn-observed-historyp
                                   fn-sn-with-event-index fn-sn-with-topic
                                   fn-sn-with-consumer fn-cpo-install
                                   fn-sn-update-replayed fn-sn-observed-seed
                                   fn-stx-index-of-store fn-replay-advance-txid
                                   fn-replay-identity fn-cpe-projection-replay
                                   fn-th-prefix-project fn-cei-build)))))

; Over the same Store history and frontier, a second configuration history
; opens exactly when its configured replay does.
(defthm fn-cfgc-cpo-open-of-other-configs
  (implies (fn-sn-open-okp (fn-cpo-open-observed configs frontier events))
           (iff (fn-sn-open-okp (fn-cpo-open-observed configs2 frontier events))
                (fn-sob-configured-openp configs2 frontier events)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-cpo-open-observed-succeeds-exactly)
                        (:instance fn-cpo-open-observed-succeeds-exactly
                                   (configs configs2)))
           :in-theory nil)))

(defthm fn-cfgc-cpo-open-ok-is-recovering
  (implies (fn-sn-open-okp (fn-cpo-open-observed configs frontier events))
           (equal (fn-sf-phase (fn-sn-files (fn-sn-open-state
                                             (fn-cpo-open-observed configs frontier events))))
                  :recovering))
  :hints (("Goal" :use (fn-sob-cpo-open-ok-facts)
           :in-theory (e/d (fn-bs-recovered-kernel)
                           (fn-cpo-open-observed fn-sn-open-okp)))))

; The configured open's condition is the fold's kind and the four scalar tests.
(defthm fn-cfgc-configured-openp-by-kind
  (implies (consp configs2)
           (equal (fn-sob-configured-openp configs2 frontier events)
                  (let ((replayed (fn-cpr-replay configs2 events)))
                    (and (equal (fn-replay-result-kind replayed) :ok)
                         (fn-cfgc-advance-okp
                          (fn-cnode-node (fn-replay-result-node replayed))
                          frontier)))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-cpr-replay-ok-is-configured
                                   (configs configs2)))
           :in-theory (e/d (fn-sob-configured-openp fn-cnode-statep)
                           (fn-cpr-replay fn-cpr-replay-ok-is-configured
                            fn-cfgc-advance-okp fn-replay-advance-okp)))))

; OPENED is the open's result, carried (host/store-node-host.lisp
; fn-store-sn-open-extended keeps it beside E and REPLAYED).  When it
; succeeded and the record is filed after every event, the candidate is decided
; from the extended fold alone; otherwise the replaying candidate.
(defun fn-cfgc-candidate-open-carried
    (records frontier config-records record configuration replayed opened)
  (declare (xargs :guard t :verify-guards nil))
  (let ((configuration1 (fn-cfgc-config-extend configuration record)))
    (if (not (equal (fn-replay-result-kind configuration1) :ok))
        (list :refused :configuration)
      (if (and (<= (nfix frontier) (nfix (fn-cfg-record-txid record)))
               (equal (fn-sn-open-kind opened) :ok))
          (let ((replayed1 (fn-cfgc-cpr-extend replayed config-records records record)))
            (if (and (equal (fn-replay-result-kind replayed1) :ok)
                     (fn-cfgc-advance-okp
                      (fn-cnode-node (fn-replay-result-node replayed1)) frontier))
                (list :accepted (fn-replay-result-node replayed1))
              (list :refused :history)))
        (fn-cfgc-candidate-open-result records frontier config-records record
                                       configuration replayed)))))

(verify-guards fn-cfgc-candidate-open-carried)

; KEYSTONE (PKT-601 (1): the candidate open is not recomputed).  From the
; open's carried result, the candidate is the candidate the authorization
; replayed for.
(defthm fn-cfgc-candidate-open-carried-is-the-replayed-candidate
  (implies (and (true-listp config-records)
                (equal configuration (fn-cnode-config-replay config-records))
                (equal replayed (fn-cpr-replay config-records records))
                (equal opened (fn-cpo-open-observed config-records frontier records)))
           (equal (fn-cfgc-candidate-open-carried
                   records frontier config-records record configuration replayed
                   opened)
                  (fn-native-admin-candidate-open-result
                   records frontier
                   (fn-native-admin-append-record config-records record))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance fn-cfgc-candidate-open-result-is-the-replayed-candidate)
                 (:instance fn-cfgc-config-replay-of-one-more
                            (configs config-records))
                 (:instance fn-cfgc-cpo-open-kind-ok-is-okp
                            (configs config-records) (events records))
                 (:instance fn-cfgc-cpo-open-of-other-configs
                            (configs config-records) (events records)
                            (configs2 (append config-records (list record))))
                 (:instance fn-cfgc-configured-openp-by-kind
                            (configs2 (append config-records (list record)))
                            (events records))
                 (:instance fn-cfgc-cpo-open-ok-is-recovering
                            (configs (append config-records (list record)))
                            (events records))
                 (:instance fn-sob-cpo-open-ok-facts
                            (configs config-records) (events records))
                 (:instance fn-cfgc-observed-is-below
                            (events records)
                            (bound (fn-cfg-record-txid record)))
                 (:instance fn-cfgc-cpr-replay-of-one-more
                            (configs config-records) (events records)))
           :in-theory (e/d (fn-native-admin-candidate-open-result)
                           (fn-cpo-open-observed fn-cpr-replay fn-cfgc-cpr-extend
                            fn-cfgc-config-extend fn-cnode-config-replay
                            fn-sn-observed-historyp fn-cfgc-events-below
                            fn-cfgc-candidate-open-result
                            fn-cfgc-candidate-open-result-is-the-replayed-candidate
                            fn-native-admin-append-record fn-sob-configured-openp
                            fn-cfgc-config-replay-of-one-more
                            fn-cfgc-cpr-replay-of-one-more
                            fn-cfgc-cpo-open-kind-ok-is-okp
                            fn-cfgc-cpo-open-ok-is-recovering
                            fn-cfgc-observed-is-below
                            fn-cfgc-advance-okp
                            fn-sn-open-okp fn-sn-open-kind)))))

; -----------------------------------------------------------------------------
; The authorization the offline request calls.

; fn-native-admin-publication-authorize with the configuration-only fold run
; once (over CONFIG-RECORDS; the candidate's is one step from it), the
; candidate's physical fold one step from REPLAYED, the open's, and the
; candidate open decided from OPENED, the open's result (PKT-601 (1)).
(defun fn-cfgc-publication-authorize
    (records frontier config-records record lock-owned observed-names
             max-generations replayed opened)
  (declare (xargs :guard t))
  (if (not lock-owned)
      (fn-native-admin-publication-result :refused :lock nil nil nil)
    (let ((configuration (fn-cnode-config-replay config-records)))
      (if (not (equal (fn-replay-result-kind configuration) :ok))
          (fn-native-admin-publication-result :refused :configuration nil nil nil)
        (let* ((current (fn-cnode-config (fn-replay-result-node configuration)))
               (generation (+ 1 (nfix (fn-cfg-generation current))))
               (name (fn-native-admin-config-name generation))
               (candidate (equal (car (fn-cfgc-candidate-open-carried
                                       records frontier config-records record
                                       configuration replayed opened))
                                 :accepted)))
          (cond ((not (fn-cfg-recordp record))
                 (fn-native-admin-publication-result :refused :record nil nil nil))
                ((or (not (equal (fn-cfg-record-sequence record)
                                 (fn-cfg-generation current)))
                     (not (equal (fn-cfg-record-generation record) generation)))
                 (fn-native-admin-publication-result :refused :generation nil nil nil))
                ((< (nfix max-generations) generation)
                 (fn-native-admin-publication-result
                  :refused :max-config-generations nil nil nil))
                ((null name)
                 (fn-native-admin-publication-result :refused :generation-name nil nil nil))
                ((fn-native-admin-name-memberp name observed-names)
                 (fn-native-admin-publication-result :refused :occupied nil nil nil))
                ((not candidate)
                 (fn-native-admin-publication-result :refused :candidate nil nil nil))
                (t (fn-native-admin-publication-result
                    :accepted nil generation name (fn-jpub-initial t)))))))))

; KEYSTONE.  With the open's fold carried, the authorization is the one it
; replaces, on every arm (so every keystone of
; fn-native-admin-publication-authorize carries: the lock, the generation, the
; occupied name, the candidate).
(defthm fn-cfgc-publication-authorize-is-the-replayed-authorization
  (implies (and (true-listp config-records)
                (equal replayed (fn-cpr-replay config-records records))
                (equal opened (fn-cpo-open-observed config-records frontier records)))
           (equal (fn-cfgc-publication-authorize
                   records frontier config-records record lock-owned
                   observed-names max-generations replayed opened)
                  (fn-native-admin-publication-authorize
                   records frontier config-records record lock-owned
                   observed-names max-generations)))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance fn-cfgc-candidate-open-carried-is-the-replayed-candidate
                            (configuration (fn-cnode-config-replay config-records))))
           :in-theory (e/d (fn-native-admin-publication-authorize
                            fn-native-admin-candidate-openp)
                           (fn-cfgc-candidate-open-carried
                            fn-native-admin-candidate-open-result
                            fn-cfgc-candidate-open-carried-is-the-replayed-candidate
                            fn-cpo-open-observed
                            fn-cnode-config-replay fn-cpr-replay
                            fn-native-admin-config-name fn-cfg-recordp
                            fn-native-admin-append-record)))))

; The host-called subject: fn-cvec-native-admin-authorize (the profile's
; group-name bound, then the publication under the profile's generations)
; over the carried fold.
(defun fn-cfgc-cvec-native-admin-authorize
    (records frontier config-records record lock-owned observed-names profile
             replayed opened)
  (declare (xargs :guard t))
  (if (not (fn-cvec-group-names-within
            (fn-cfg-record-change record)
            (fn-bs-profile-max-group-name-octets profile)))
      (fn-native-admin-publication-result :refused :max-group-name-octets
                                          nil nil nil)
    (fn-cfgc-publication-authorize
     records frontier config-records record lock-owned observed-names
     (fn-cvec-config-generations profile record) replayed opened)))

; KEYSTONE (PKT-510 (1): one replay per offline request).  The authorization
; host/store-node-host.lisp fn-store-cfg-native-admin-authorize-carried calls
; (for host/native/admin.lisp fnn-admin-execute) equals the one
; fn-store-cfg-native-admin-authorize calls, whenever REPLAYED is the open's
; fold of the same histories and OPENED is the open's result:
; fn-store-sn-open-extended keeps both in the global fn-store-sco-open, and
; fn-sco-store-open-of-extended-capture (books/owner-checkpoint-open.lisp) is
; the theorem that they are (fn-cpr-replay configs events) and
; (fn-cpo-open-observed configs frontier events) of the open's configuration
; records, frontier and the extended capture's records, on the full and the
; checkpoint open alike.
(defthm fn-cfgc-cvec-native-admin-authorize-is-the-replayed-authorization
  (implies (and (true-listp config-records)
                (equal replayed (fn-cpr-replay config-records records))
                (equal opened (fn-cpo-open-observed config-records frontier records)))
           (equal (fn-cfgc-cvec-native-admin-authorize
                   records frontier config-records record lock-owned
                   observed-names profile replayed opened)
                  (fn-cvec-native-admin-authorize
                   records frontier config-records record lock-owned
                   observed-names profile)))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (fn-cvec-native-admin-authorize)
                           (fn-cfgc-publication-authorize
                            fn-native-admin-publication-authorize
                            fn-cpr-replay fn-cpo-open-observed fn-cvec-group-names-within
                            fn-cvec-config-generations)))))

; -----------------------------------------------------------------------------
; The published record read back under the lock (PKT-601 (2)).
;
; host/native/admin.lisp fnn-admin-verify-under-lock reopened the whole store
; after the publication (fnn-bridge-reset, fnn-recover) to observe that the
; reopened configuration's generation is the one the authorization named.
; The reopen is decided already: the authorization accepted only a candidate
; whose open over CONFIGS ++ (R) succeeds.  What the publication adds is the
; durable file, so the host reads that one file back and ACL2 compares it
; with the authorized octets; the reopen over the history the directory now
; holds is then the candidate, at the named generation.

; The record is filed after every Store event (its txid at or past FRONTIER,
; as the host builds it at the opened node's next txid), so the reopen's fold
; is one configuration step from the open's.
(defun fn-cfgc-readback-verdict (readback authorized generation frontier)
  (declare (xargs :guard t :verify-guards nil))
  (if (not (equal readback authorized))
      :mismatch
    (let ((parsed (fn-cfg-decode-exact readback)))
      (cond ((not (fn-record-parse-okp parsed)) :undecodable)
            ((not (equal (fn-cfg-record-generation (fn-record-parse-value parsed))
                         generation))
             :generation-mismatch)
            ((< (nfix (fn-cfg-record-txid (fn-record-parse-value parsed)))
                (nfix frontier))
             :before-frontier)
            (t :verified)))))

(verify-guards fn-cfgc-readback-verdict)

(local
 (defthm fn-cfgc-cpr-loop-of-nothing
   (equal (fn-replay-result-node (fn-cpr-loop cn nil nil cs es)) cn)
   :hints (("Goal" :expand ((fn-cpr-loop cn nil nil cs es))
            :in-theory (enable fn-cpr-config-firstp)))))

; One configuration step that succeeds leaves the record's generation.
(defthm fn-cfgc-cpr-loop-one-config-generation
  (implies (equal (fn-replay-result-kind (fn-cpr-loop cn (list r) nil cs es)) :ok)
           (equal (fn-cfg-generation
                   (fn-cnode-config
                    (fn-replay-result-node (fn-cpr-loop cn (list r) nil cs es))))
                  (fn-cfg-record-generation r)))
  :hints (("Goal"
           :expand ((fn-cpr-loop cn (list r) nil cs es))
           :use ((:instance fn-cnode-apply-config-bumps-the-generation
                            (cn (fn-cnode-make (fn-replay-advance-txid
                                                (fn-cnode-node cn)
                                                (fn-cfg-record-txid r))
                                               (fn-cnode-config cn)))
                            (record r) (ceiling (fn-cnode-line-ceiling))))
           :in-theory (e/d (fn-cpr-config-firstp fn-cnode-record-acceptablep
                            fn-cfg-record-acceptablep)
                           (fn-cnode-apply-config-bumps-the-generation
                            fn-cnode-statep fn-cnode-apply-config
                            fn-replay-advance-okp fn-replay-advance-txid
                            fn-cfg-admissiblep fn-cfg-recordp fn-cfgp)))))

(defthm fn-cfgc-append-of-true-list-fix
  (equal (append (true-list-fix x) y) (append x y)))

(defthm fn-cfgc-append-record-is-append-always
  (equal (fn-native-admin-append-record configs record)
         (append configs (list record)))
  :hints (("Goal" :in-theory (enable fn-native-admin-append-record))))

; KEYSTONE (PKT-601 (2): the readback replaces the reopen).  When the
; authorization accepted RECORD, decoded from AUTHORIZED, and the octets
; read back from its published file are AUTHORIZED at GENERATION, the open of
; the configuration history the directory now holds (the observed history,
; then the record read back) succeeds and serves GENERATION: what the
; retired reopen observed.
(defthm fn-cfgc-readback-verified-is-the-reopen
  (implies (and (equal (fn-native-admin-publication-status
                        (fn-native-admin-publication-authorize
                         records frontier config-records record lock-owned
                         observed-names max-generations))
                       :accepted)
                (equal record (fn-record-parse-value (fn-cfg-decode-exact authorized)))
                (equal (fn-cfgc-readback-verdict readback authorized generation
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
                            fn-sn-open-okp fn-cnode-statep)))))
