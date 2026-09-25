; fn: the runtime producers stay inside the record widths the profile admits
; (PRF-123; D27, packets P6 and 6 of the Fable mandate §12).
;
; `fn-bs-profile-admits-every-article-record' (byte-store-frame) holds for a
; record that is not `fn-record-widep': every integer field within u32.  This
; book proves that premise of the records the node actually stages, from the
; producers, not from a refusal downstream of them:
;
;   sequence, txid, generation  the durable allocator.  `fn-sf-prepare-record'
;       stages a record only when its sequence is the committed count, its
;       txid is the reserved one (frontier - 1) and its generation is its
;       txid (`fn-sf-candidatep'); the frontier is u32 in every file state
;       (`fn-sf-statep'), and the committed records have strictly increasing
;       txids below it, so the count is at most the frontier.
;   stamp   `fn-record-stamp-of-observation' (records-stamp) yields a stamp
;       below 2^32 or :clock-unusable, and `fn-sn-article-record' refuses the
;       latter before any record exists.
;   charge  the POST boundary (`fn-sbud-post-boundary', store-budget-naming)
;       answers :ok only for a charge within u32.
;
; Subject: `fn-sn-prepare', the prepare the host calls (host/store-node-host
; `fn-store-sn-prepare-article' through `fn-spc-prepare', equal to it by
; `fn-spc-prepare-equals-specification-under-relation'; host/owner-host
; through `fn-pcar-sbud-prepare', equal to `fn-sbud-prepare' by
; `fn-pcar-sbud-prepare-is-sbud-prepare'), applied to the record
; `fn-sn-article-record' builds.
(in-package "ACL2")
(include-book "store-node")
(include-book "store-budget-naming")
(include-book "bp-ingress")

(local
 (defthm fn-rwp-event-coordinates-are-natural
   (implies (fn-store-event-p record)
            (and (natp (fn-store-event-sequence record))
                 (natp (fn-store-event-txid record))
                 (natp (fn-store-event-generation record))))
   :rule-classes ((:forward-chaining) (:rewrite))
   :hints (("Goal" :in-theory (disable fn-store-event-p)))))

; The committed records' txids strictly increase from LOWER and stay below
; FRONTIER, so there are at most FRONTIER - LOWER of them.
(defthm fn-sf-record-listp-len-bound
  (implies (and (fn-sf-record-listp records sequence lower frontier)
                (natp lower) (natp frontier))
           (<= (len records) (nfix (- frontier lower))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-sf-record-listp))))

; Allocator widths: a record the file machine stages has sequence, txid and
; generation within u32.
(defthm fn-sf-prepare-record-stages-u32-coordinates
  (implies (and (fn-sf-statep s)
                (not (equal (fn-sf-prepare-record s record groups capacity) s)))
           (and (fn-record-uint32p (fn-store-event-sequence record))
                (fn-record-uint32p (fn-store-event-txid record))
                (fn-record-uint32p (fn-store-event-generation record))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-sf-record-listp-len-bound
                                   (records (fn-sf-records s)) (sequence 0)
                                   (lower 0) (frontier (fn-sf-frontier s))))
           :in-theory (enable fn-sf-prepare-record fn-sf-candidatep
                              fn-sf-statep fn-record-uint32p))))

;  The composed prepare stages a record only through the file machine's gate.
(local
(defthm fn-rwp-sn-prepare-gate
  (implies (not (equal (fn-sn-prepare s record) s))
           (and (fn-record-p record)
                (fn-sf-statep (fn-sn-files s))
                (not (equal (fn-sf-prepare-record (fn-sn-files s) record
                                                  (fn-sn-groups s)
                                                  (fn-sn-capacity s))
                            (fn-sn-files s)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-sn-prepare fn-sn-statep)
                           (fn-sf-prepare-record fn-sf-statep fn-sn-update
                            fn-cpe-projection-step fn-sn-shapep
                            fn-node-statep fn-sn-verdict-listp
                            fn-sn-keyring-snapshot-listp fn-prin-keyringp
                            fn-sn-prepare-node fn-sn-record-bindsp
                            fn-record-p))))))

; The same at the composed prepare: a record `fn-sn-prepare' stages is a
; record whose sequence, txid and generation are within u32.
(defthm fn-sn-prepare-stages-u32-coordinates
  (implies (not (equal (fn-sn-prepare s record) s))
           (and (fn-record-p record)
                (fn-record-uint32p (fn-record-sequence record))
                (fn-record-uint32p (fn-record-txid record))
                (fn-record-uint32p (fn-record-generation record))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-rwp-sn-prepare-gate)
                        (:instance fn-sf-prepare-record-stages-u32-coordinates
                                   (s (fn-sn-files s))
                                   (groups (fn-sn-groups s))
                                   (capacity (fn-sn-capacity s))))
           :in-theory (e/d (fn-store-event-sequence fn-store-event-txid
                            fn-store-event-generation)
                           (fn-sf-prepare-record fn-sf-statep fn-sn-prepare
                            fn-record-p fn-record-uint32p)))))

; The article producer: its stamp is below 2^32 (`fn-record-stamp-of-observation'
; answers :clock-unusable past it) and its charge is the one it was given.
(defthm fn-sn-article-record-stamp-and-charge
  (implies (fn-record-p (fn-sn-article-record s obs msgid payload groups
                                              obligation-id subject evidence
                                              charge))
           (and (fn-record-uint32p
                 (fn-record-stamp (fn-sn-article-record
                                   s obs msgid payload groups obligation-id
                                   subject evidence charge)))
                (equal (fn-record-charge
                        (fn-sn-article-record s obs msgid payload groups
                                              obligation-id subject evidence
                                              charge))
                       charge)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-sn-article-record
                                     fn-record-stamp-of-observation
                                     fn-record-uint32p))))

; The charge gate: the POST boundary answers :ok only for a charge within u32.
(defthm fn-sbud-post-boundary-admits-a-u32-charge
  (implies (equal (fn-sbud-post-boundary profile msgid-octets payload-length
                                         group-count charge)
                  :ok)
           (fn-record-uint32p charge))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-sbud-post-boundary fn-record-uint32p)
                                  (fn-sbud-payload-bound fn-sbud-group-bound
                                   fn-af-message-idp)))))

; KEYSTONE (PRF-123: the producers satisfy the runtime-width premise).  The
; article record the host builds (`fn-sn-article-record') and the prepare
; stages (`fn-sn-prepare') is not `fn-record-widep' when its charge is within
; u32: the allocator bounds sequence, txid and generation, the observation
; bounds the stamp.
(defthm fn-sn-prepare-stages-a-narrow-article-record
  (implies (and (fn-record-uint32p charge)
                (not (equal (fn-sn-prepare
                             s (fn-sn-article-record s obs msgid payload groups
                                                     obligation-id subject
                                                     evidence charge))
                            s)))
           (not (fn-record-widep
                 (fn-sn-article-record s obs msgid payload groups obligation-id
                                       subject evidence charge))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-sn-prepare-stages-u32-coordinates
                                   (record (fn-sn-article-record
                                            s obs msgid payload groups
                                            obligation-id subject evidence
                                            charge)))
                        (:instance fn-sn-article-record-stamp-and-charge))
           :in-theory (e/d (fn-record-widep)
                           (fn-sn-article-record fn-sn-prepare fn-record-p
                            fn-record-uint32p)))))

; A value that is not an admitted profile reads G as 0, so no group count is
; within it.
(local
 (defthm fn-rwp-unadmitted-profile-has-no-group-bound
   (implies (not (fn-bs-profile-admittedp values))
            (equal (fn-bs-profile-max-groups-per-article values) 0))
   :hints (("Goal" :use ((:instance fn-bs-profile-of-is-valid-or-nil))
            :in-theory (e/d (fn-bs-profile-admittedp
                             fn-bs-profile-max-groups-per-article
                             fn-bs-profile-field)
                            (fn-bs-profile-of fn-bs-profile-validp))))))

; The hypothesis of `fn-bs-profile-admits-every-article-record', discharged
; at the host's sequence: the POST boundary admits the article under the
; persisted PROFILE (host/native/io.lisp `fnn-post-boundary', owner
; `fn-owner-post-boundary'), the producer builds its record and the prepare
; stages it; then its encoding is within the profile's R, so the publish
; gate's record check (`fn-bs-publication-admissiblep') never refuses it.
(defthm fn-post-admitted-article-record-is-within-r
  (implies (and (equal (fn-sbud-post-boundary profile msgid-octets
                                              (len payload) (len groups) charge)
                       :ok)
                (not (equal (fn-sn-prepare
                             s (fn-sn-article-record s obs msgid payload groups
                                                     obligation-id subject
                                                     evidence charge))
                            s)))
           (<= (len (fn-record-encode
                     (fn-sn-article-record s obs msgid payload groups
                                           obligation-id subject evidence
                                           charge)))
               (fn-bs-profile-max-record-octets profile)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-sbud-post-boundary-admits-a-u32-charge
                                   (payload-length (len payload))
                                   (group-count (len groups)))
                        (:instance fn-sn-prepare-stages-a-narrow-article-record)
                        (:instance fn-bs-profile-admits-every-article-record
                                   (values profile)
                                   (record (fn-sn-article-record
                                            s obs msgid payload groups
                                            obligation-id subject evidence
                                            charge))))
           :in-theory (e/d (fn-sbud-post-boundary fn-sbud-payload-bound
                            fn-sbud-group-bound fn-sn-article-record)
                           (fn-sn-prepare fn-record-widep
                            fn-bs-profile-admittedp fn-af-message-idp
                            fn-bs-profile-max-record-octets
                            fn-bs-profile-max-article-octets
                            fn-bs-profile-max-groups-per-article)))))

; The BP ingress producer (`fn-bpi-record-for', books/bp-ingress, host
; host/bp-ingress-host): its charge is the policy's, which `fn-bpi-policy-p'
; bounds by u32, so the record it stages is narrow with no further premise.
(defthm fn-bpi-staged-record-is-narrow
  (implies (and (fn-bpi-policy-p policy)
                (not (equal (fn-sn-prepare
                             store (fn-bpi-record-for store policy context
                                                      msgid-octets group-octets
                                                      adu))
                            store)))
           (not (fn-record-widep
                 (fn-bpi-record-for store policy context msgid-octets
                                    group-octets adu))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-sn-prepare-stages-a-narrow-article-record
                                   (s store)
                                   (obs (fn-bpi-context-observation context))
                                   (msgid (fn-record-octets-string msgid-octets))
                                   (payload adu)
                                   (groups (car (cdr (fn-bpi-map-groups
                                                      group-octets
                                                      (fn-bpi-policy-group-map
                                                       policy)))))
                                   (obligation-id (fn-bpi-policy-archive-id policy))
                                   (subject (fn-bpi-policy-subject policy))
                                   (evidence (fn-bpi-policy-evidence policy))
                                   (charge (fn-bpi-policy-charge policy))))
           :in-theory (e/d (fn-bpi-record-for fn-bpi-policy-p)
                           (fn-sn-article-record fn-sn-prepare fn-record-widep
                            fn-record-uint32p)))))
