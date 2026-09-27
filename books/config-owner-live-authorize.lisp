; fn: the live owner's administrative authorization from its carried state
; (lane log-recovery-2, 2026-09-27; PKT-837).
;
; This book has the prefix `fn-olau-' (docs/prefixes.md).
;
; What this replaces.  host/owner-host.lisp `fn-owner-cfg-native-admin-
; authorize' (called by host/native/admin.lisp `fnn-admin-authorize-owner'
; from `fnn-owner-live-reconfigure-locked', every live configuration verb)
; asked `fn-cvec-native-admin-authorize' over the owner's carried Store rows
; and frontier.  Its candidate open (`fn-native-admin-candidate-openp')
; replays the configuration and Store histories extended by the record
; (`fn-cpr-replay', `fn-cpo-open-observed': every Store record revisited,
; hot_path_check's fn-cpr-loop finding) on every operator request, while the
; owner holds the mutex.  The owner carries what that replay recomputes: its
; store's node IS the replayed node advanced to the frontier, and its
; configuration IS the replayed configuration (`fn-ocl-relation').  So the
; candidate here is the one configuration step applied to the carried node
; (as `fn-oclc-configure' completes it), the configuration-only fold one step
; from the fold the authorization computes anyway, and the observed
; configuration history compared with the carried one: no Store record is
; read.
(in-package "ACL2")
(include-book "config-owner-carried")
(include-book "config-carried-open")

; The Store history's own reopen conditions, the ones the candidate open asks
; of the records alone (store-open-bridge fn-cpo-open-observed-succeeds-
; exactly, without the configured replay and the observed-history shape):
; the identity, consumer and topic replays and the identity context's field
; types.  `fn-ocl-relation' does not carry them (it carries the configured
; replay, fn-cst-relation); the owner's recovery established them at its open
; (fn-cpo-open-observed succeeded) and every appended record passed its step
; gate.  Proof vocabulary: no host line evaluates it.
(defun fn-olau-events-reopenp (events)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-sn-observed-identity-okp events)
       (fn-sn-observed-consumer-okp events)
       (fn-sn-observed-topic-okp events)
       (fn-sob-identity-typedp events)))

; The candidate from the carried state.  ST is the owner's store, CONFIG its
; configuration, CONFIGS the configuration history the host observed on disk
; and CONFIGURATION that history's configuration-only fold (the
; authorization computes it for the current generation).  O(1) in the Store
; history: the observed history is compared with the carried one (the
; configuration generations, bounded by the profile's
; max-config-generations), and the record is applied to the carried node.
(defun fn-olau-candidatep (st config configs record configuration)
  (declare (xargs :guard t))
  (let* ((files (fn-sn-files st))
         (frontier (fn-sf-frontier files)))
    (and (equal (fn-sf-phase files) :ready)
         (equal configs (fn-sn-config-history st))
         (equal (fn-replay-result-kind (fn-cfgc-config-extend configuration record)) :ok)
         (fn-cfg-recordp record)
         (equal (fn-cfg-record-txid record) frontier)
         (equal (fn-cfg-record-sequence record) (len configs))
         (let ((at (fn-cnode-make (fn-sn-node st) config)))
           (and (fn-cnode-carried-acceptablep at record (fn-cnode-line-ceiling))
                (fn-oclc-advance-okp (fn-cnode-node (fn-oclc-apply at record))
                                     frontier))))))

; `fn-native-admin-publication-authorize' with the candidate from the carried
; state.  Every other arm is that function's, over the same observations.
(defun fn-olau-publication-authorize
    (oc config-records record lock-owned observed-names max-generations)
  (declare (xargs :guard t))
  (if (not lock-owned)
      (fn-native-admin-publication-result :refused :lock nil nil nil)
    (let ((configuration (fn-cnode-config-replay config-records)))
      (if (not (equal (fn-replay-result-kind configuration) :ok))
          (fn-native-admin-publication-result :refused :configuration nil nil nil)
        (let* ((current (fn-cnode-config (fn-replay-result-node configuration)))
               (generation (+ 1 (nfix (fn-cfg-generation current))))
               (name (fn-native-admin-config-name generation))
               (candidate (fn-olau-candidatep (fn-own-store (fn-ocfg-owner oc))
                                              (fn-ocfg-config oc)
                                              config-records record configuration)))
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

; The host-called subject (host/owner-host.lisp fn-owner-cfg-native-admin-
; authorize, for host/native/admin.lisp fnn-admin-authorize-owner): the
; profile's group-name bound, then the publication under the profile's
; configuration generations, as `fn-cvec-native-admin-authorize'.
(defun fn-olau-authorize
    (oc config-records record lock-owned observed-names profile)
  (declare (xargs :guard t))
  (if (not (fn-cvec-group-names-within
            (fn-cfg-record-change record)
            (fn-bs-profile-max-group-name-octets profile)))
      (fn-native-admin-publication-result :refused :max-group-name-octets
                                          nil nil nil)
    (fn-olau-publication-authorize
     oc config-records record lock-owned observed-names
     (fn-cvec-config-generations profile record))))

; -----------------------------------------------------------------------------
; The candidate open of the extended history, over the carried state.

(local
 (defthm fn-olau-open-ok-by-conditions
   (iff (fn-sn-open-okp (fn-cpo-open-observed configs frontier events))
        (and (fn-sob-configured-openp configs frontier events)
             (fn-sn-observed-historyp frontier events)
             (fn-olau-events-reopenp events)))
   :hints (("Goal" :use fn-cpo-open-observed-succeeds-exactly
            :in-theory '(fn-olau-events-reopenp)))))

(local
 (defthm fn-olau-candidate-openp-by-conditions
   (equal (fn-native-admin-candidate-openp events frontier configs2)
          (and (equal (fn-replay-result-kind (fn-cnode-config-replay configs2)) :ok)
               (fn-sob-configured-openp configs2 frontier events)
               (fn-sn-observed-historyp frontier events)
               (fn-olau-events-reopenp events)))
   :rule-classes nil
   :hints (("Goal"
            :do-not-induct t
            :use ((:instance fn-olau-open-ok-by-conditions (configs configs2))
                  (:instance fn-cfgc-cpo-open-ok-is-recovering (configs configs2))
                  (:instance fn-sob-cpo-open-ok-facts (configs configs2)))
            :in-theory (e/d (fn-native-admin-candidate-openp
                             fn-native-admin-candidate-open-result
                             fn-sob-configured-openp)
                            (fn-cpo-open-observed fn-cpr-replay fn-cnode-config-replay
                             fn-cnode-statep fn-replay-advance-okp fn-sn-observed-historyp
                             fn-olau-events-reopenp fn-sn-open-okp
                             fn-olau-open-ok-by-conditions
                             fn-cfgc-cpo-open-ok-is-recovering))))))

; The candidate open of CONFIGS ++ (RECORD), for the carried history CONFIGS
; and a record at the frontier, is the carried candidate: the configured
; replay of the extended history is one step from the carried fold
; (fn-cfgc-cpr-replay-of-one-more), that fold's node advanced to the frontier
; is the store's node (fn-oclc-relation-facts), and the step's acceptance and
; application are the carried ones (fn-cnode-record-acceptablep-is-the-
; carried-check, fn-oclc-apply-is-apply-config).
(defthm fn-olau-candidatep-is-the-replayed-candidate
  (implies (and (fn-cpo-history-relation st)
                (equal (fn-sf-phase (fn-sn-files st)) :ready)
                (equal config (fn-cnode-config (fn-oclc-replayed st)))
                (equal configs (fn-sn-config-history st))
                (true-listp configs)
                (equal configuration (fn-cnode-config-replay configs))
                (equal (fn-cfg-record-txid record) (fn-sf-frontier (fn-sn-files st)))
                (fn-olau-events-reopenp (fn-sf-records (fn-sn-files st))))
           (equal (fn-native-admin-candidate-openp
                   (fn-sf-records (fn-sn-files st)) (fn-sf-frontier (fn-sn-files st))
                   (fn-native-admin-append-record configs record))
                  (fn-olau-candidatep st config configs record configuration)))
  :hints (("Goal"
           :do-not-induct t
           :use (fn-oclc-relation-facts
                 (:instance fn-olau-candidate-openp-by-conditions
                            (events (fn-sf-records (fn-sn-files st)))
                            (frontier (fn-sf-frontier (fn-sn-files st)))
                            (configs2 (append (fn-sn-config-history st) (list record))))
                 (:instance fn-cfgc-config-replay-of-one-more
                            (configs (fn-sn-config-history st)))
                 (:instance fn-cfgc-cpr-replay-of-one-more
                            (configs (fn-sn-config-history st))
                            (events (fn-sf-records (fn-sn-files st))))
                 (:instance fn-cfgc-observed-is-below
                            (frontier (fn-sf-frontier (fn-sn-files st)))
                            (events (fn-sf-records (fn-sn-files st)))
                            (bound (fn-cfg-record-txid record)))
                 (:instance fn-cnode-apply-config-preserves-state
                            (cn (fn-cnode-make (fn-sn-node st)
                                               (fn-cnode-config (fn-oclc-replayed st))))
                            (ceiling (fn-cnode-line-ceiling)))
                 (:instance fn-cnode-record-acceptablep-is-the-carried-check
                            (cn (fn-cnode-make (fn-sn-node st)
                                               (fn-cnode-config (fn-oclc-replayed st))))
                            (ceiling (fn-cnode-line-ceiling))))
           :in-theory (e/d (fn-olau-candidatep fn-sob-configured-openp fn-cfgc-cpr-extend
                            fn-oclc-replayed)
                           (fn-cpo-history-relation fn-native-admin-candidate-openp
                            fn-cnode-config-replay fn-cfgc-config-extend
                            fn-cfgc-config-replay-of-one-more fn-cfgc-cpr-replay-of-one-more
                            fn-cpr-replay fn-cpr-loop fn-cnode-statep fn-sn-statep
                            fn-cnode-apply-config fn-cnode-record-acceptablep
                            fn-cnode-carried-acceptablep fn-cfg-recordp
                            fn-replay-advance-okp fn-replay-advance-txid
                            fn-oclc-advance fn-oclc-advance-okp fn-oclc-apply
                            fn-sn-observed-historyp fn-cfgc-observed-is-below
                            fn-cnode-line-ceiling fn-cnode-apply-config-preserves-state
                            fn-olau-events-reopenp fn-node-statep)))))

; The authorization is the publication authorization with its candidate
; replaced, arm for arm.
(local
 (defthm fn-olau-publication-authorize-by-candidate
   (let* ((st (fn-own-store (fn-ocfg-owner oc)))
          (files (fn-sn-files st)))
     (implies (equal (fn-olau-candidatep st (fn-ocfg-config oc) configs record
                                         (fn-cnode-config-replay configs))
                     (fn-native-admin-candidate-openp
                      (fn-sf-records files) (fn-sf-frontier files)
                      (fn-native-admin-append-record configs record)))
              (equal (fn-olau-publication-authorize oc configs record lock-owned
                                                    observed-names max-generations)
                     (fn-native-admin-publication-authorize
                      (fn-sf-records files) (fn-sf-frontier files)
                      configs record lock-owned observed-names max-generations))))
   :hints (("Goal"
            :do-not-induct t
            :in-theory (union-theories
                        '(fn-olau-publication-authorize fn-native-admin-publication-authorize)
                        (theory 'minimal-theory))))))

(local
 (defthm fn-olau-ocl-relation-facts
   (implies (fn-ocl-relation oc)
            (let ((st (fn-own-store (fn-ocfg-owner oc))))
              (and (fn-cst-relation st)
                   (true-listp (fn-sn-config-history st))
                   (equal (fn-ocfg-config oc) (fn-cnode-config (fn-oclc-replayed st))))))
   :rule-classes nil
   :hints (("Goal" :in-theory '(fn-ocl-relation fn-ocl-config-historyp fn-oclc-replayed)))))

; KEYSTONE (PKT-837: no replay on the live administrative path).  Under the
; owner's invariant `fn-ocl-relation' (the conjunct of control-quanta-2's
; `fn-lgoc-invariantp' it needs), at the ready phase, when the configuration
; history the host observed on disk is the one the owner carries, the record
; is filed at the owner's frontier, and the Store history's own reopen
; conditions hold, the authorization the host calls (host/owner-host.lisp
; fn-owner-cfg-native-admin-authorize, from host/native/admin.lisp
; fnn-admin-authorize-owner) EQUALS `fn-cvec-native-admin-authorize' over the
; carried rows and frontier -- the replaying decision it replaced -- on every
; arm, so every keystone of that function (the lock, the generation bound,
; the release's reserved generation, the group-name bound, the occupied name,
; the candidate reopen) carries to the live path.
;   Scope of the hypotheses.  The ready phase and the frontier txid hold of
; every record the host gets here: the host asks fn-oclc-live-authorizep
; first (fnn-owner-live-reconfigure-locked), which holds only at :ready of a
; record at the frontier (fn-oclc-configure).  The observed configuration
; history is the carried one unless another writer published into config/
; while the owner held the store lock (the lock refuses one).  The reopen
; conditions of the Store history are established by the owner's open and
; are not carried by fn-ocl-relation; carrying them is PKT-837's remainder.
; Outside them the two differ: the teeth (tests/acl2/config-owner-live-
; authorize-tests.lisp) exhibit each difference the hypotheses exclude.
(defthm fn-olau-authorize-is-the-replayed-authorization
  (let* ((st (fn-own-store (fn-ocfg-owner oc)))
         (files (fn-sn-files st)))
    (implies (and (fn-ocl-relation oc)
                  (equal (fn-sf-phase files) :ready)
                  (equal config-records (fn-sn-config-history st))
                  (equal (fn-cfg-record-txid record) (fn-sf-frontier files))
                  (fn-olau-events-reopenp (fn-sf-records files)))
             (equal (fn-olau-authorize oc config-records record lock-owned
                                       observed-names profile)
                    (fn-cvec-native-admin-authorize
                     (fn-sf-records files) (fn-sf-frontier files)
                     config-records record lock-owned observed-names profile))))
  :rule-classes nil
  :hints (("Goal"
           :do-not-induct t
           :use (fn-olau-ocl-relation-facts
                 (:instance fn-oclc-ready-cst-relation-is-history-relation
                            (st (fn-own-store (fn-ocfg-owner oc))))
                 (:instance fn-olau-candidatep-is-the-replayed-candidate
                            (st (fn-own-store (fn-ocfg-owner oc)))
                            (config (fn-ocfg-config oc))
                            (configs config-records)
                            (configuration (fn-cnode-config-replay config-records)))
                 (:instance fn-olau-publication-authorize-by-candidate
                            (configs config-records)
                            (max-generations (fn-cvec-config-generations profile record))))
           :in-theory '(fn-olau-authorize fn-cvec-native-admin-authorize))))
