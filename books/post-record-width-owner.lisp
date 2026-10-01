; PKT-250: PRF-123's record-width composition over the owner's two host calls.
;
; The served POST asks the boundary first (host/owner-host.lisp
; `fn-owner-post-boundary', which answers `fn-pak-post-admission'), then
; prepares (`fn-owner-prepare-buffer', which builds the record with
; `fn-sn-article-record', interns it with `fn-apc-intern-row-at' and calls
; `fn-ppc-pout-prepare-article-cat'; host/native/owner.lisp
; `fnn-owner-attempt' seals only on its :prepared word).  The keystone below
; is stated over exactly those three ACL2 functions: when the boundary
; answered :ok under a carry whose verdict is its profile's, and the prepare
; answered :prepared, the record's encoding is within the profile's R, so the
; publish gate's record check never refuses it.  No join, view or relation
; hypothesis: the duplicate test the catalog decides may be any value.
(in-package "ACL2")
(include-book "record-width-producers")
(include-book "post-prepare-catalog")
(include-book "post-admission-keyed")
(include-book "owner-parse-carried")

; -----------------------------------------------------------------------------
; The shared file stage stages only a candidate, whose coordinates are u32.

(defthm fn-prwo-pcar-stage-record-stages-u32-coordinates
  (implies (and (fn-sf-statep files)
                (not (equal (fn-sf-phase (fn-pcar-stage-record files record))
                            (fn-sf-phase files))))
           (and (fn-record-uint32p (fn-store-event-sequence record))
                (fn-record-uint32p (fn-store-event-txid record))
                (fn-record-uint32p (fn-store-event-generation record))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-sf-record-listp-len-bound
                                   (records (fn-sf-records files)) (sequence 0)
                                   (lower 0) (frontier (fn-sf-frontier files))))
           :in-theory (enable fn-pcar-stage-record-is-stage-record
                              fn-spc-stage-record fn-sf-candidatep
                              fn-sf-statep fn-record-uint32p))))

; The owner's catalog prepare stages only a held row with u32 coordinates.
(defthm fn-prwo-ppc-spc-prepare-stages-u32-coordinates
  (implies (fn-pout-stagedp s (fn-ppc-spc-prepare s row dup carry))
           (and (fn-held-p row)
                (fn-record-uint32p (fn-store-event-sequence row))
                (fn-record-uint32p (fn-store-event-txid row))
                (fn-record-uint32p (fn-store-event-generation row))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-prwo-pcar-stage-record-stages-u32-coordinates
                                   (files (fn-sn-files s)) (record row)))
           :in-theory (e/d (fn-ppc-spc-prepare fn-pout-stagedp fn-sn-statep)
                           (fn-pcar-stage-record fn-sf-statep fn-node-statep
                            fn-ppc-sn-prepare-node fn-rcon-sn-record-bindsp
                            fn-rcon-cpe-projection-step fn-held-p
                            fn-store-event-sequence fn-store-event-txid
                            fn-store-event-generation fn-record-uint32p)))))

; Its Store is the one it was given or the catalog Store prepare.
(defthm fn-prwo-store-of-ppc-psrv-prepare
  (or (equal (fn-sbud-oc-store (fn-ppc-psrv-prepare oc row budget dup carry))
             (fn-sbud-oc-store oc))
      (equal (fn-sbud-oc-store (fn-ppc-psrv-prepare oc row budget dup carry))
             (fn-ppc-spc-prepare (fn-sbud-oc-store oc) row dup carry)))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn-ppc-psrv-prepare fn-ppc-sbud-prepare
                               fn-ppc-opc-owner-prepare fn-sbud-oc-store
                               fn-ocfg-with-owner fn-ocfg-owner-of-fn-ocfg-make
                               fn-own-refresh-keeps-fields
                               fn-own-store-of-fn-own-make))))

; A refusal word is never :prepared.
(defthm fn-prwo-refusal-kind-is-not-prepared
  (not (equal (fn-psrv-refusal-kind oc record budget) :prepared))
  :hints (("Goal" :in-theory (enable fn-psrv-refusal-kind fn-sbud-refusal-kind))))

; The host's prepare answers :prepared only when it staged a u32 row.
(defthm fn-prwo-prepared-row-has-u32-coordinates
  (implies (equal (mv-nth 0 (fn-ppc-pout-prepare-article-cat oc row budget carry
                                                             fn-arena fn-cat))
                  :prepared)
           (and (fn-held-p row)
                (fn-record-uint32p (fn-store-event-sequence row))
                (fn-record-uint32p (fn-store-event-txid row))
                (fn-record-uint32p (fn-store-event-generation row))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-prwo-store-of-ppc-psrv-prepare
                            (dup (fn-pidx-find-article-cat
                                  (fn-record-msgid row)
                                  (fn-state-articles
                                   (fn-node-acceptance
                                    (fn-sn-node (fn-own-store (fn-ocfg-owner oc)))))
                                  (fn-own-view (fn-ocfg-owner oc)) fn-arena fn-cat)))
                 (:instance fn-prwo-ppc-spc-prepare-stages-u32-coordinates
                            (s (fn-sbud-oc-store oc))
                            (dup (fn-pidx-find-article-cat
                                  (fn-record-msgid row)
                                  (fn-state-articles
                                   (fn-node-acceptance
                                    (fn-sn-node (fn-own-store (fn-ocfg-owner oc)))))
                                  (fn-own-view (fn-ocfg-owner oc)) fn-arena fn-cat)))
                 (:instance fn-pout-stagedp-is-a-change
                            (before (fn-sbud-oc-store oc))
                            (after (fn-sbud-oc-store oc))))
           :in-theory (e/d (fn-ppc-pout-prepare-article-cat
                            fn-prwo-refusal-kind-is-not-prepared)
                           (fn-ppc-psrv-prepare fn-ppc-spc-prepare fn-pout-stagedp
                            fn-psrv-refusal-kind fn-sbud-oc-store
                            fn-pidx-find-article-cat fn-held-p
                            fn-store-event-sequence fn-store-event-txid
                            fn-store-event-generation fn-record-uint32p)))))

; The interned row carries the record's coordinates (a held row reads its
; event coordinates through the record accessors).
(defthm fn-prwo-intern-row-at-coordinates
  (implies (fn-held-p (fn-apc-intern-row-at w keyring generation h carry))
           (and (equal (fn-store-event-sequence
                        (fn-apc-intern-row-at w keyring generation h carry))
                       (fn-record-sequence w))
                (equal (fn-store-event-txid
                        (fn-apc-intern-row-at w keyring generation h carry))
                       (fn-record-txid w))
                (equal (fn-store-event-generation
                        (fn-apc-intern-row-at w keyring generation h carry))
                       (fn-record-generation w))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-apc-intern-row-at fn-store-event-sequence
                                   fn-store-event-txid fn-store-event-generation
                                   fn-record-accessors-of-held-make)
                                  (fn-held-p)))))

; A value that is not an admitted profile reads G as 0 (the same fact
; record-width-producers proves locally).
(local
 (defthm fn-prwo-unadmitted-profile-has-no-group-bound
   (implies (not (fn-bs-profile-admittedp values))
            (equal (fn-bs-profile-max-groups-per-article values) 0))
   :hints (("Goal" :use ((:instance fn-bs-profile-of-is-valid-or-nil))
            :in-theory (e/d (fn-bs-profile-admittedp
                             fn-bs-profile-max-groups-per-article
                             fn-bs-profile-field)
                            (fn-bs-profile-of fn-bs-profile-validp))))))

; KEYSTONE (PKT-250; PRF-123's composition at the owner's host calls).
; host/owner-host.lisp `fn-owner-post-boundary' answers
; `fn-pak-post-admission' under the owner's carried profile verdict;
; `fn-owner-prepare-buffer' builds RECORD with `fn-sn-article-record' over
; the same Message-ID, payload and resolved groups, interns it with
; `fn-apc-intern-row-at' and answers the word of
; `fn-ppc-pout-prepare-article-cat'.  When the boundary said :ok and the
; prepare said :prepared, the profile is admitted, the record is narrow
; (u32 coordinates, stamp and charge), and its payload and group count are
; within the profile's A and G.  Each conjunct fails when its hypothesis is
; removed (tests/acl2/post-record-width-owner-tests.lisp).
(defthm fn-prwo-owner-post-record-is-narrow-within-the-profile
  (implies (and (fn-pvc-carryp pcarry)
                (equal (fn-pak-post-admission pcarry profile msgid-octets
                                              (len payload) (len groups)
                                              charge key cat)
                       :ok)
                (equal (mv-nth 0 (fn-ppc-pout-prepare-article-cat
                                  oc
                                  (fn-apc-intern-row-at
                                   (fn-sn-article-record s obs msgid payload groups
                                                         obligation-id subject
                                                         evidence charge)
                                   keyring generation h acarry)
                                  budget carry fn-arena fn-cat))
                       :prepared))
           (and (fn-bs-profile-admittedp profile)
                (not (fn-record-widep
                      (fn-sn-article-record s obs msgid payload groups
                                            obligation-id subject evidence
                                            charge)))
                (<= (len payload) (fn-bs-profile-max-article-octets profile))
                (<= (len groups) (fn-bs-profile-max-groups-per-article profile))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-prwo-prepared-row-has-u32-coordinates
                            (row (fn-apc-intern-row-at
                                  (fn-sn-article-record s obs msgid payload groups
                                                        obligation-id subject
                                                        evidence charge)
                                  keyring generation h acarry)))
                 (:instance fn-prwo-intern-row-at-coordinates
                            (w (fn-sn-article-record s obs msgid payload groups
                                                     obligation-id subject
                                                     evidence charge))
                            (carry acarry))
                 (:instance fn-pak-post-admission-refused-is-the-boundary-by-definition
                            (carry pcarry) (payload-length (len payload))
                            (group-count (len groups)) (fn-cat cat))
                 (:instance fn-pvc-post-boundary-carried-is-sbud-post-boundary
                            (carry pcarry) (msgid msgid-octets)
                            (payload-length (len payload))
                            (group-count (len groups)))
                 (:instance fn-sbud-post-boundary-admits-a-u32-charge
                            (payload-length (len payload))
                            (group-count (len groups)))
                 )
           :in-theory (e/d (fn-sbud-post-boundary fn-sbud-payload-bound
                            fn-sbud-group-bound fn-sn-article-record
                            fn-record-widep fn-record-stamp-of-observation
                            fn-record-uint32p)
                           (fn-ppc-pout-prepare-article-cat fn-apc-intern-row-at
                            fn-pak-post-admission fn-pvc-post-boundary-carried
                            fn-store-event-sequence fn-store-event-txid
                            fn-store-event-generation fn-held-p
                            fn-bs-profile-admittedp fn-af-message-idp
                            fn-bs-profile-max-record-octets
                            fn-bs-profile-max-article-octets
                            fn-bs-profile-max-groups-per-article)))))

; PRF-123's conclusion at the owner's host calls, from the keystone and
; fn-bs-profile-admits-every-article-record: the record encodes within the
; profile's R, so the publish gate's record check never refuses it.
(defthm fn-prwo-owner-post-record-is-within-r
  (implies (and (fn-pvc-carryp pcarry)
                (equal (fn-pak-post-admission pcarry profile msgid-octets
                                              (len payload) (len groups)
                                              charge key cat)
                       :ok)
                (equal (mv-nth 0 (fn-ppc-pout-prepare-article-cat
                                  oc
                                  (fn-apc-intern-row-at
                                   (fn-sn-article-record s obs msgid payload groups
                                                         obligation-id subject
                                                         evidence charge)
                                   keyring generation h acarry)
                                  budget carry fn-arena fn-cat))
                       :prepared))
           (<= (len (fn-record-encode
                     (fn-sn-article-record s obs msgid payload groups
                                           obligation-id subject evidence
                                           charge)))
               (fn-bs-profile-max-record-octets profile)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-prwo-owner-post-record-is-narrow-within-the-profile)
                 (:instance fn-bs-profile-admits-every-article-record
                            (values profile)
                            (record (fn-sn-article-record
                                     s obs msgid payload groups
                                     obligation-id subject evidence charge))))
           :in-theory (e/d (fn-sn-article-record)
                           (fn-ppc-pout-prepare-article-cat fn-apc-intern-row-at
                            fn-pak-post-admission fn-record-widep
                            fn-bs-profile-admittedp
                            fn-bs-profile-max-record-octets
                            fn-bs-profile-max-article-octets
                            fn-bs-profile-max-groups-per-article)))))
