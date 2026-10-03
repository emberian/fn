; fn: the live owner's administrative authorization with no configuration
; history read from disk (sweep S033, 2026-10-03).
;
; host/native/admin.lisp fnn-owner-live-reconfigure-locked, under the owner
; mutex, listed the configuration directory and read every record file
; (host/native/io.lisp fnn-config-record-observation), handed them all to
; host/owner-host.lisp fn-owner-cfg-native-admin-authorize as octet lists to
; decode, and fn-olau-authorize compared that observed history with the one
; the owner carries.  Every live reconfiguration (admin vectors, peer
; invite/accept/confirm, XREDEEM) paid O(generations) opens, reads, decodes
; and an equality walk while every other class waited.
;
; Here the history is the carried one (fn-sn-config-history of the owner's
; store), and the host observes ONE name: whether the next generation's
; file, `fn-olau-next-name' (from the carried configuration's generation, no
; fold), already exists.  `fn-olau-authorize-carried' is fn-olau-authorize
; over the carried history with that observation as the observed names.
;
; KEYSTONE fn-olau-authorize-carried-is-the-observed-authorization: under
; the owner's invariant fn-ocl-relation, when OCCUPIED is whether the next
; name is among the names on disk, the carried authorization EQUALS
; fn-olau-authorize over the carried history and those names, on every arm.
; With fn-olau-authorize-is-the-replayed-authorization (whose hypothesis
; that the observed history is the carried one this discharges by
; construction), every keystone of fn-cvec-native-admin-authorize carries
; to it.
;
; Not here (open): the configuration-only fold of the carried history still
; runs in memory on each call (fn-olau-publication-authorize's
; `configuration', O(generations) <= the profile's max-config-generations,
; no I/O); carrying that fold in the owner's state would make the call O(1).
;
; This book uses the prefix `fn-olau-' of books/config-owner-live-authorize.

(in-package "ACL2")
(include-book "config-owner-live-authorize")
(include-book "config-crash-replay")

; The next generation's configuration file name, from the carried
; configuration's generation (O(1)).  The host observes this one name.
(defun fn-olau-next-name (oc)
  (declare (xargs :guard t))
  (fn-native-admin-config-name
   (+ 1 (nfix (fn-cfg-generation (fn-ocfg-config oc))))))

; THE FUNCTION THE HOST CALLS (host/owner-host.lisp
; fn-owner-cfg-native-admin-authorize-carried, from host/native/admin.lisp
; fnn-admin-authorize-owner).
(defun fn-olau-authorize-carried (oc record lock-owned occupied profile)
  (declare (xargs :guard t))
  (fn-olau-authorize oc (fn-sn-config-history (fn-own-store (fn-ocfg-owner oc)))
                     record lock-owned
                     (if occupied (list (fn-olau-next-name oc)) nil)
                     profile))

; -----------------------------------------------------------------------------
; The publication reads the observed names only through the membership of
; the name its own fold computes.

(local
 (defthm fn-olau-publication-authorize-reads-one-membership
   (implies (equal (fn-native-admin-name-memberp
                    (fn-native-admin-config-name
                     (+ 1 (nfix (fn-cfg-generation
                                 (fn-cnode-config
                                  (fn-replay-result-node
                                   (fn-cnode-config-replay configs)))))))
                    names1)
                   (fn-native-admin-name-memberp
                    (fn-native-admin-config-name
                     (+ 1 (nfix (fn-cfg-generation
                                 (fn-cnode-config
                                  (fn-replay-result-node
                                   (fn-cnode-config-replay configs)))))))
                    names2))
            (equal (fn-olau-publication-authorize oc configs record lock-owned
                                                  names1 max-generations)
                   (fn-olau-publication-authorize oc configs record lock-owned
                                                  names2 max-generations)))
   :hints (("Goal" :in-theory (e/d (fn-olau-publication-authorize)
                                   (fn-native-admin-name-memberp
                                    fn-native-admin-config-name
                                    fn-cnode-config-replay fn-olau-candidatep
                                    fn-native-admin-publication-result))))))

(local
 (defthm fn-olau-name-memberp-is-boolean
   (booleanp (fn-native-admin-name-memberp n names))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable fn-native-admin-name-memberp)))))

(local
 (defthm fn-olau-member-of-singleton
   (and (equal (fn-native-admin-name-memberp n (list m)) (equal n m))
        (equal (fn-native-admin-name-memberp n nil) nil))
   :hints (("Goal" :in-theory (enable fn-native-admin-name-memberp)))))

; Under the invariant the fold's configuration is the carried one, so its
; next name is fn-olau-next-name.
(local
 (defthm fn-olau-fold-config-is-carried
   (implies (and (fn-ocl-relation oc)
                 (equal (fn-replay-result-kind
                         (fn-cnode-config-replay
                          (fn-sn-config-history (fn-own-store (fn-ocfg-owner oc)))))
                        :ok))
            (equal (fn-cnode-config
                    (fn-replay-result-node
                     (fn-cnode-config-replay
                      (fn-sn-config-history (fn-own-store (fn-ocfg-owner oc))))))
                   (fn-ocfg-config oc)))
   :hints (("Goal"
            :use ((:instance fn-ocl-cpr-replay-ok-is-config-replay-ok
                             (configs (fn-sn-config-history (fn-own-store (fn-ocfg-owner oc))))
                             (events (fn-sf-records
                                      (fn-sn-files (fn-own-store (fn-ocfg-owner oc)))))))
            :in-theory '(fn-ocl-relation fn-ocl-config-historyp)))))

; A refused fold answers before any name is read: then any two name lists
; give the same answer.
(local
 (defthm fn-olau-publication-authorize-without-a-fold
   (implies (not (equal (fn-replay-result-kind (fn-cnode-config-replay configs)) :ok))
            (equal (fn-olau-publication-authorize oc configs record lock-owned
                                                  names1 max-generations)
                   (fn-olau-publication-authorize oc configs record lock-owned
                                                  names2 max-generations)))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn-olau-publication-authorize)
                                   (fn-cnode-config-replay fn-olau-candidatep))))))

; KEYSTONE.
(defthm fn-olau-authorize-carried-is-the-observed-authorization
  (implies (and (fn-ocl-relation oc)
                (equal occupied
                       (fn-native-admin-name-memberp (fn-olau-next-name oc)
                                                     observed-names)))
           (equal (fn-olau-authorize-carried oc record lock-owned occupied profile)
                  (fn-olau-authorize oc
                                     (fn-sn-config-history
                                      (fn-own-store (fn-ocfg-owner oc)))
                                     record lock-owned observed-names profile)))
  :hints (("Goal"
           :do-not-induct t
           :cases ((equal (fn-replay-result-kind
                           (fn-cnode-config-replay
                            (fn-sn-config-history (fn-own-store (fn-ocfg-owner oc)))))
                          :ok))
           :use ((:instance fn-olau-publication-authorize-without-a-fold
                            (configs (fn-sn-config-history (fn-own-store (fn-ocfg-owner oc))))
                            (names1 (if (fn-native-admin-name-memberp
                                         (fn-olau-next-name oc) observed-names)
                                        (list (fn-olau-next-name oc)) nil))
                            (names2 observed-names)
                            (max-generations (fn-cvec-config-generations profile record)))
                 (:instance fn-olau-publication-authorize-reads-one-membership
                            (configs (fn-sn-config-history (fn-own-store (fn-ocfg-owner oc))))
                            (names1 (if (fn-native-admin-name-memberp
                                         (fn-olau-next-name oc) observed-names)
                                        (list (fn-olau-next-name oc)) nil))
                            (names2 observed-names)
                            (max-generations (fn-cvec-config-generations profile record)))
                 fn-olau-fold-config-is-carried)
           :in-theory '(fn-olau-authorize-carried fn-olau-authorize fn-olau-next-name
                        fn-olau-member-of-singleton fn-olau-name-memberp-is-boolean
                        (:executable-counterpart fn-native-admin-name-memberp)))))
