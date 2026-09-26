; P8 / PRF-026: a served POST carrying an FN-Authorship carrier is classified
; exactly as protected transit is.
;
; Host path (writer).  host/native/owner.lisp fnn-owner-drain-one (the served
; NNTP POST, line 1173) and fnn-owner-complete-bound-submission (control
; `post' and BP applications, line 1247) call fnn-owner-attempt-served
; (line 884), which calls fnn-owner-attempt-transit, the attempt protected
; NNTP and BP transit already call.  Its decisions are ACL2's:
; fn-pa-carrier-form (absent -> the unsigned fnn-owner-attempt, unchanged;
; present-invalid -> refused), fn-pa-current-plan over the POST's octets and
; this Store's keyring snapshots (host/owner-host.lisp
; fn-owner-peer-carrier-plan, line 1177), the primitive observation, then
; fn-pa-authorized-event (fn-owner-peer-carried-event, line 1190), whose
; kind-4 event fnn-owner-identity-commit prepares and publishes.  Its
; completion is the owner's (:complete) (host/owner-host.lisp fn-owner-finish,
; line 531, via *fnn-finish-callback*).  The poster's word is
; fn-pa-served-post-word (host/owner-host.lisp fn-owner-served-post-word,
; since PKT-473; equal to fn-pa-served-word except for a durable composite
; whose key change the Store refused), and fn-owner-outcome runs
; fn-own-outcome with it.
;
; Premise of the valid arm, not proved here: that the Store's completion
; record after the identity prepare and publication is the event ACL2 built
; (the same premise the P8 finish keystone takes).  The token recorded is
; the decoded verdict event's; that it is :verified in general needs a round
; trip of the fn-stxe codec, which no book proves.  The test book shows it on
; a reachable trace.
(in-package "ACL2")
(include-book "owner-verdict-read")
(include-book "peer-authored-accept")
(include-book "hybrid-lifecycle-store-invariants")

; -----------------------------------------------------------------------------
; The kind-4 event ACL2 constructs names the POST's Message-ID and the
; enrollment generation the plan selected.

(defthm fn-osp-bindsp-verdict-names-the-article-record
  (implies (fn-stxa-bindsp e)
           (and (equal (fn-stxe-msgid (fn-hls-kind4-verdict-event e))
                       (fn-record-msgid
                        (fn-record-result-record
                         (fn-record-decode-exact (fn-stxa-article-record e)))))
                (equal (fn-stxe-keyring-generation (fn-hls-kind4-verdict-event e))
                       (fn-stxa-keyring-generation e))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-stxa-bindsp fn-hls-kind4-verdict-event)
                                  (fn-stxe-decode-exact
                                   fn-stxe-encode)))))

(defthm fn-osp-bindsp-is-an-acceptance
  (implies (fn-stxa-bindsp e) (fn-stxa-p e))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-stxa-bindsp))))

(defthm fn-osp-bindsp-article-record-decodes
  (implies (fn-stxa-bindsp e)
           (fn-record-result-okp
            (fn-record-decode-exact (fn-stxa-article-record e))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-stxa-bindsp))))

(defthm fn-osp-bound-verdict-names-the-encoded-record
  (implies (and (fn-stxa-bindsp e)
                (equal (fn-stxa-article-record e) (fn-record-encode r)))
           (and (fn-record-p r)
                (equal (fn-stxe-msgid (fn-hls-kind4-verdict-event e))
                       (fn-record-msgid r))))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-osp-bindsp-verdict-names-the-article-record
                 fn-osp-bindsp-article-record-decodes
                 (:instance fn-record-accepted-input-bounds (octets nil))
                 (:instance fn-record-round-trip-succeeds (record r)))
           :in-theory (disable fn-hls-kind4-verdict-event fn-stxa-bindsp
                               fn-record-round-trip-succeeds))))

(defthm fn-osp-carried-event-base-shape
  (let ((e (fn-hsig-authorized-carried-submission-event-base
            sequence txid generation keyring-generation enrolled-snapshot
            msgid source received groups obligation-id content-subject
            release-evidence charge principal keys signatures observed-ml-key
            ed25519-observation ml-dsa-65-observation observation
            projection-ok)))
    (implies e
             (and (fn-stxa-bindsp e)
                  (equal (fn-stxa-article-record e)
                         (fn-record-encode
                          (fn-record-make sequence txid generation msgid received
                                          groups obligation-id content-subject
                                          release-evidence charge
                                          (fn-record-stamp-of-observation
                                           observation))))
                  (equal (fn-stxa-keyring-generation e) keyring-generation))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-hsig-authorized-carried-submission-event-base
                                   fn-stxa-make-carried)
                                  (fn-stxa-bindsp fn-stxe-encode fn-record-stamp-of-observation
                                   fn-record-string-octets fn-hsig-authorize
                                   fn-hsig-carried-record-metadatap
                                   fn-hsig-authored-source-fields
                                   fn-hsig-authored-source-id
                                   fn-hsig-keyring-snapshot)))))

(defthm fn-osp-authorized-event-binds-the-post
  (let ((e (fn-pa-authorized-event
            sequence txid generation msgid received groups obligation-id
            content-subject release-evidence charge snapshots
            observed-ml-key ed-observation ml-observation clock-observation))
        (plan (fn-pa-current-plan received snapshots nil nil)))
    (implies e
             (and (equal (car plan) :ok)
                  (fn-stxa-p e)
                  (equal (fn-stxe-msgid (fn-hls-kind4-verdict-event e)) msgid)
                  (equal (fn-stxe-keyring-generation (fn-hls-kind4-verdict-event e))
                         (nth 6 plan)))))
  :hints (("Goal"
           :use (fn-pa-authorized-event-requires-current-plan-by-definition
                 (:instance fn-osp-carried-event-base-shape
                  (keyring-generation (nth 6 (fn-pa-current-plan received snapshots nil nil)))
                  (enrolled-snapshot (fn-stxk-snapshot
                                      (nth 5 (fn-pa-current-plan received snapshots nil nil))))
                  (source (nth 1 (fn-pa-current-plan received snapshots nil nil)))
                  (principal (nth 2 (fn-pa-current-plan received snapshots nil nil)))
                  (keys (nth 3 (fn-pa-current-plan received snapshots nil nil)))
                  (signatures (nth 4 (fn-pa-current-plan received snapshots nil nil)))
                  (ed25519-observation ed-observation)
                  (ml-dsa-65-observation ml-observation)
                  (observation clock-observation)
                  (projection-ok (fn-hc-okp (fn-hc-received-plan received))))
                 (:instance fn-osp-bound-verdict-names-the-encoded-record
                  (e (fn-pa-authorized-event
                      sequence txid generation msgid received groups obligation-id
                      content-subject release-evidence charge snapshots
                      observed-ml-key ed-observation ml-observation clock-observation))
                  (r (fn-record-make sequence txid generation msgid received
                                     groups obligation-id content-subject
                                     release-evidence charge
                                     (fn-record-stamp-of-observation
                                      clock-observation))))
                 (:instance fn-osp-bindsp-verdict-names-the-article-record
                  (e (fn-pa-authorized-event
                      sequence txid generation msgid received groups obligation-id
                      content-subject release-evidence charge snapshots
                      observed-ml-key ed-observation ml-observation clock-observation))))
           :in-theory (e/d (fn-pa-authorized-event)
                           (fn-pa-current-plan fn-hls-kind4-verdict-event
                            fn-stxa-bindsp fn-stxa-p fn-record-make fn-record-stamp-of-observation
                            fn-hc-okp fn-hc-received-plan fn-stxk-snapshot
                            fn-hsig-authorized-carried-submission-event-base)))))

; PRF-177 (a), the carried-source keystone of the two-node exchange (CNS-004).
; The receiving node's host-called transit constructor keeps what the author
; signed: host/native/owner.lisp fnn-owner-attempt-transit's :ok arm calls
; host/owner-host.lisp fn-owner-peer-carried-event, which is
; fn-pa-authorized-event.  Whenever it forms an event, the received octets
; carry a well-formed carrier; the event's authored source is exactly the
; carrier's source; the stored article record holds exactly the received
; octets (so the carrier and both signatures in them); and the two
; signatures the verdict authorized are exactly the carrier's.  The hop-local
; parts of the received article (this node's Path) may differ between nodes;
; the source and the signatures are the carrier's at every hop.
(encapsulate ()
(local
 (defthm osp-base-keeps-source-and-signatures
   (let ((e (fn-hsig-authorized-carried-submission-event-base
             sequence txid generation keyring-generation enrolled-snapshot
             msgid source received groups obligation-id content-subject
             release-evidence charge principal keys signatures observed-ml-key
             ed25519-observation ml-dsa-65-observation observation
             projection-ok)))
     (implies e
              (and (equal (fn-stxa-authored-source e) source)
                   (fn-hsig-authorize-at (fn-hsig-source-version source)
                                         principal keys source signatures
                                         observed-ml-key ed25519-observation
                                         ml-dsa-65-observation))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-hsig-authorized-carried-submission-event-base
                             fn-stxa-make-carried)
                            (fn-stxa-bindsp fn-stxe-encode fn-record-stamp-of-observation
                             fn-record-string-octets fn-hsig-authorize-at
                             fn-hsig-carried-record-metadatap
                             fn-hsig-authored-source-fields
                             fn-hsig-authored-source-id
                             fn-hsig-keyring-snapshot fn-hsig-source-filed-groups
                             fn-stxe-make fn-record-make fn-hsig-evidence-tag
                             fn-hsig-source-version))))))
(local
 (defthm osp-ok-plan-is-the-carrier-form
   (let ((plan (fn-pa-current-plan received snapshots nil nil))
         (form (fn-pa-carrier-form received)))
     (implies (equal (car plan) :ok)
              (and (equal (car form) :ok)
                   (equal (nth 1 plan) (nth 1 form))
                   (equal (nth 2 plan) (nth 2 form))
                   (equal (nth 3 plan) (nth 3 form))
                   (equal (nth 4 plan) (nth 4 form)))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-pa-current-plan)
                            (fn-pa-carrier-form fn-hl-current-for-principal
                             fn-hl-current-enrollment fn-stxk-p
                             fn-stxk-keyring-generation fn-pa-carriesp
                             fn-pa-revoked-tombstonep))))))
(defthm fn-osp-authorized-event-keeps-the-carried-source-and-signatures
  (let ((e (fn-pa-authorized-event
            sequence txid generation msgid received groups obligation-id
            content-subject release-evidence charge snapshots
            observed-ml-key ed-observation ml-observation clock-observation))
        (form (fn-pa-carrier-form received)))
    (implies e
             (and (equal (car form) :ok)
                  (equal (fn-stxa-authored-source e) (nth 1 form))
                  (equal (fn-stxa-article-record e)
                         (fn-record-encode
                          (fn-record-make sequence txid generation msgid received
                                          groups obligation-id content-subject
                                          release-evidence charge
                                          (fn-record-stamp-of-observation
                                           clock-observation))))
                  (fn-hsig-authorize-at (fn-hsig-source-version (nth 1 form))
                                        (nth 2 form) (nth 3 form) (nth 1 form)
                                        (nth 4 form) observed-ml-key
                                        ed-observation ml-observation))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance osp-ok-plan-is-the-carrier-form)
                 (:instance osp-base-keeps-source-and-signatures
                  (keyring-generation (nth 6 (fn-pa-current-plan received snapshots nil nil)))
                  (enrolled-snapshot (fn-stxk-snapshot
                                      (nth 5 (fn-pa-current-plan received snapshots nil nil))))
                  (source (nth 1 (fn-pa-current-plan received snapshots nil nil)))
                  (principal (nth 2 (fn-pa-current-plan received snapshots nil nil)))
                  (keys (nth 3 (fn-pa-current-plan received snapshots nil nil)))
                  (signatures (nth 4 (fn-pa-current-plan received snapshots nil nil)))
                  (ed25519-observation ed-observation)
                  (ml-dsa-65-observation ml-observation)
                  (observation clock-observation)
                  (projection-ok (fn-hc-okp (fn-hc-received-plan received))))
                 (:instance fn-osp-carried-event-base-shape
                  (keyring-generation (nth 6 (fn-pa-current-plan received snapshots nil nil)))
                  (enrolled-snapshot (fn-stxk-snapshot
                                      (nth 5 (fn-pa-current-plan received snapshots nil nil))))
                  (source (nth 1 (fn-pa-current-plan received snapshots nil nil)))
                  (principal (nth 2 (fn-pa-current-plan received snapshots nil nil)))
                  (keys (nth 3 (fn-pa-current-plan received snapshots nil nil)))
                  (signatures (nth 4 (fn-pa-current-plan received snapshots nil nil)))
                  (ed25519-observation ed-observation)
                  (ml-dsa-65-observation ml-observation)
                  (observation clock-observation)
                  (projection-ok (fn-hc-okp (fn-hc-received-plan received)))))
           :in-theory (e/d (fn-pa-authorized-event)
                           (fn-pa-current-plan fn-pa-carrier-form
                            fn-hsig-authorized-carried-submission-event-base
                            fn-hsig-authorize-at fn-record-make
                            fn-stxa-authored-source fn-stxa-article-record
                            fn-record-stamp-of-observation fn-stxk-snapshot
                            fn-hc-okp fn-hc-received-plan fn-hsig-source-version)))))
)

; -----------------------------------------------------------------------------
; The valid arm over the owner's (:complete), which the host's fn-owner-finish
; runs.  Lemmas: the P8 keystones fn-sn-finish-of-a-kind-4-acceptance-records-
; its-verdict (books/hybrid-lifecycle-store-invariants) and
; fn-own-reader-opened-after-completion-pins-the-finished-verdicts
; (books/owner-verdict-read).  The HDR :fn-verified reply of such a reader is
; fn-stx-reader-verdict over its pinned list
; (fn-own-read-hdr-fn-verified-is-the-pinned-verdict, same book).

(defthm fn-osp-complete-store-is-finish
  (implies (fn-sn-completion-enabledp (fn-own-store o))
           (equal (fn-own-store (fn-own-step o '(:complete)))
                  (fn-sn-finish (fn-own-store o))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-own-step fn-own-complete fn-own-refresh)
                           (fn-sn-finish fn-sn-completion-enabledp
                            fn-own-view-make-group-indexed fn-own-conn-make-group-indexed
                            fn-served-open-group-indexed fn-midx-refresh fn-gidx-build)))))

(defthm fn-osp-signed-post-finish-records-its-verdict
  (let* ((e (fn-pa-authorized-event
             sequence txid generation msgid received groups obligation-id
             content-subject release-evidence charge snapshots
             observed-ml-key ed-observation ml-observation clock-observation))
         (plan (fn-pa-current-plan received snapshots nil nil))
         (v (fn-hls-kind4-verdict-event e)))
    (implies (and e
                  (fn-sn-completion-enabledp (fn-own-store o))
                  (equal (fn-sn-completion-record (fn-own-store o)) e))
             (equal (fn-sn-verdict-lookup
                     (fn-own-store (fn-own-step o '(:complete))) msgid)
                    (fn-stx-make-verdict (fn-stxe-token v) (fn-stxe-detail v)
                                         (nth 6 plan)))))
  :hints (("Goal" :do-not-induct t
           :use (fn-osp-authorized-event-binds-the-post
                 (:instance fn-sn-finish-of-a-kind-4-acceptance-records-its-verdict
                  (s (fn-own-store o))))
           :in-theory (e/d (fn-osp-complete-store-is-finish)
                           (fn-pa-authorized-event fn-pa-current-plan
                            fn-hls-kind4-verdict-event fn-sn-finish
                            fn-sn-verdict-lookup fn-stx-make-verdict
                            fn-sn-completion-enabledp fn-own-step
                            fn-osp-authorized-event-binds-the-post
                            fn-sn-finish-of-a-kind-4-acceptance-records-its-verdict)))))

(defthm fn-osp-reader-after-signed-post-reports-its-verdict
  (let* ((e (fn-pa-authorized-event
             sequence txid generation msgid received groups obligation-id
             content-subject release-evidence charge snapshots
             observed-ml-key ed-observation ml-observation clock-observation))
         (plan (fn-pa-current-plan received snapshots nil nil))
         (v (fn-hls-kind4-verdict-event e))
         (o2 (cdr (fn-own-open (fn-own-step o '(:complete)) acfg)))
         (conn (fn-own-find-conn (fn-own-next-id o) (fn-own-conns o2))))
    (implies (and e
                  (fn-sn-completion-enabledp (fn-own-store o))
                  (equal (fn-sn-completion-record (fn-own-store o)) e)
                  (< (len (fn-own-conns o)) (nfix (fn-own-max-conns o))))
             (and conn
                  (equal (fn-stx-reader-verdict msgid (fn-own-conn-verdicts conn))
                         (fn-stx-reader-item
                          (fn-stx-make-verdict (fn-stxe-token v) (fn-stxe-detail v)
                                               (nth 6 plan)))))))
  :hints (("Goal" :do-not-induct t
           :use (fn-osp-signed-post-finish-records-its-verdict
                 fn-own-reader-opened-after-completion-pins-the-finished-verdicts)
           :in-theory (e/d (fn-osp-complete-store-is-finish fn-sn-verdict-lookup
                            fn-sn-verdict-lookup-list fn-stx-reader-verdict)
                           (fn-pa-authorized-event fn-pa-current-plan
                            fn-hls-kind4-verdict-event fn-sn-finish
                            fn-stx-make-verdict fn-stx-reader-item fn-stx-reader-lookup
                            fn-sn-completion-enabledp fn-own-step fn-own-open
                            fn-osp-signed-post-finish-records-its-verdict
                            fn-own-reader-opened-after-completion-pins-the-finished-verdicts)))))

(defthm fn-osp-finished-post-outcome-is-durable
  (implies (and (fn-sn-completion-enabledp (fn-own-store o))
                (fn-own-inflight o)
                (natp (fn-own-sub-mark (fn-own-inflight o)))
                (<= (fn-own-sub-mark (fn-own-inflight o))
                    (len (fn-own-ledger o))))
           (equal (fn-own-outcome-completion (fn-own-step o '(:complete)) :durable)
                  :durable))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-own-step fn-own-complete fn-own-refresh
                            fn-own-outcome-completion fn-own-completion-consumedp)
                           (fn-sn-finish fn-sn-completion-enabledp
                            fn-own-view-make-group-indexed fn-own-conn-make-group-indexed
                            fn-served-open-group-indexed fn-midx-refresh fn-gidx-build)))))

; -----------------------------------------------------------------------------
; The refused arm.  A present carrier the plan refuses is never the unsigned
; arm, and its reason is one the served word relays; the served outcome for
; any relayed reason is that reason's own 441 line, with no Store, ledger,
; feed or connection change.

(defthm fn-osp-plan-refusal-is-a-served-reason
  (implies (equal (car (fn-pa-current-plan received snapshots nil nil)) :refused)
           (and (member-equal (cadr (fn-pa-current-plan received snapshots nil nil))
                              '(:article :carrier :carrier-shape :local-enrollment))
                (not (equal (fn-pa-carrier-form received) :absent))))
  :hints (("Goal" :in-theory (e/d (fn-pa-current-plan fn-pa-carrier-form)
                                  (fn-pa-carrier-kind fn-hc-received-plan
                                   fn-hl-current-for-principal
                                   fn-hl-current-enrollment)))))

(defthm fn-osp-served-refusal-renders-its-reason
  (let* ((word (fn-pa-served-word :refused detail))
         (conn (fn-own-find-conn id (fn-own-conns o)))
         (sub (fn-own-inflight o))
         (r (fn-own-outcome o id word)))
    (implies (and conn sub (equal (fn-own-sub-id sub) id)
                  (not (fn-own-completion-consumedp o))
                  (member-equal detail *fn-pa-served-reasons*))
             (and (equal word detail)
                  (equal (fn-own-outcome-completion o word) :refused)
                  (equal (car r)
                         (fn-post-result-effects
                          (fn-nntp-post-outcome
                           (fn-auth-post-session (fn-own-conn-session conn))
                           detail)))
                  (equal (fn-own-store (cdr r)) (fn-own-store o))
                  (equal (fn-own-ledger (cdr r)) (fn-own-ledger o))
                  (equal (fn-own-feeds (cdr r)) (fn-own-feeds o))
                  (equal (fn-own-conns (cdr r)) (fn-own-conns o)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-own-outcome fn-own-outcome-completion
                            fn-own-outcome-rendering fn-own-refusal-wordp
                            fn-post-store-refusalp fn-served-post-outcome
                            fn-own-post-rendering fn-pa-served-word)
                           (fn-nntp-post-outcome fn-own-completion-consumedp
                            fn-own-feed-durable fn-own-advance
                            )))))

; KEYSTONE (PKT-473, PRF-184).  The served POST whose kind-4 composite is
; durable and whose key change the Store refused.  Host path:
; host/native/owner.lisp fnn-owner-statement-committed sets the detail
; :key-change-refused only after a :durable commit whose executor answered
; :refused; fnn-owner-attempt-served returns fn-owner-served-post-word
; (fn-pa-served-post-word) over that word and detail; fnn-owner-drain-one
; hands it to fn-owner-outcome (fn-own-outcome).  Once the completion is
; consumed the reply is fn-nntp-post-outcome's line naming the refused key
; change, and the owner moves exactly as for :durable (the poster re-pinned,
; the feeds as durable): the composite stands.
(defthm fn-osp-served-post-names-a-refused-key-change
  (let* ((word (fn-pa-served-post-word attempt detail))
         (conn (fn-own-find-conn id (fn-own-conns o)))
         (sub (fn-own-inflight o))
         (r (fn-own-outcome o id word)))
    (implies (and conn sub (equal (fn-own-sub-id sub) id)
                  (fn-own-completion-consumedp o)
                  (equal attempt :durable)
                  (equal detail :key-change-refused))
             (and (equal word :durable-key-change-refused)
                  (equal (fn-own-outcome-completion o word) :durable)
                  (equal (car r)
                         (fn-post-result-effects
                          (fn-nntp-post-outcome
                           (fn-auth-post-session (fn-own-conn-session conn))
                           :durable-key-change-refused)))
                  (equal (cdr r) (cdr (fn-own-outcome o id :durable))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-own-outcome fn-own-outcome-completion
                            fn-own-outcome-rendering fn-own-post-rendering
                            fn-own-durable-wordp fn-served-post-outcome
                            fn-pa-served-post-word)
                           (fn-nntp-post-outcome fn-own-completion-consumedp
                            fn-own-feed-durable fn-own-advance)))))

; KEYSTONE (PKT-473, PRF-184), the converse: the POST reply names a refused
; key change ONLY for a durable attempt whose detail is the executor's
; refusal, and only once the completion is consumed.  No other word the host
; can pass, and no refusal, is answered with it.
(defthm fn-osp-key-change-reply-only-for-a-consumed-refused-key-change
  (let* ((word (fn-pa-served-post-word attempt detail))
         (conn (fn-own-find-conn id (fn-own-conns o)))
         (r (fn-own-outcome o id word)))
    (implies (and (fn-post-sessionp (fn-auth-post-session (fn-own-conn-session conn)))
                  (not (equal attempt :durable-key-change-refused))
                  (equal (car r)
                         (fn-post-result-effects
                          (fn-nntp-post-outcome
                           (fn-auth-post-session (fn-own-conn-session conn))
                           :durable-key-change-refused))))
             (and (equal attempt :durable)
                  (equal detail :key-change-refused)
                  (fn-own-completion-consumedp o))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-post-outcome-names-a-refused-key-change-only-for-its-completion
                            (ps (fn-auth-post-session (fn-own-conn-session
                                                       (fn-own-find-conn id (fn-own-conns o)))))
                            (completion (fn-own-post-rendering
                                         o (fn-pa-served-post-word attempt detail))))
                 (:instance fn-pa-served-post-word-names-a-refused-key-change-only-when-durable
                            (word attempt)))
           :in-theory (e/d (fn-own-outcome fn-own-outcome-completion
                            fn-own-outcome-rendering fn-own-post-rendering
                            fn-own-durable-wordp fn-served-post-outcome)
                           (fn-nntp-post-outcome fn-own-completion-consumedp
                            fn-pa-served-post-word fn-post-sessionp
                            fn-own-feed-durable fn-own-advance)))))

(defthm fn-osp-served-reasons-are-store-refusals
  (implies (member-equal detail *fn-pa-served-reasons*)
           (fn-post-store-refusalp detail))
  :hints (("Goal" :in-theory (enable fn-post-store-refusalp))))

; KEYSTONE (transit refusal on the wire).  The IHAVE arm of the same relay.
; Host path: host/native/owner.lisp fnn-owner-transit-complete feeds
; fn-owner-transit-outcome (host/owner-host.lisp, which runs
; fn-own-transit-outcome) the word fn-owner-served-carried-word gives, that
; is fn-pa-served-word over the attempt's word and the ingress detail, as
; fnn-owner-attempt-served does for POST.  For a relayed reason the 437 the
; peer reads names it, with the text POST's 441 line carries for the same
; word (fn-post-store-refusal-text); no Store, ledger or feed changes.
(defthm fn-osp-transit-refusal-renders-its-reason
  (let* ((word (fn-pa-served-word :refused detail))
         (conn (fn-own-find-conn id (fn-own-conns o)))
         (sub (fn-own-inflight o))
         (r (fn-own-transit-outcome o id :want reason word)))
    (implies (and conn sub (equal (fn-own-sub-id sub) id)
                  (fn-own-transit-subp sub)
                  (equal (fn-peer-submission-kind (fn-own-sub-decision sub))
                         :ihave)
                  (not (fn-own-completion-consumedp o))
                  (member-equal detail *fn-pa-served-reasons*))
             (and (equal word detail)
                  (equal (car r)
                         (fn-peer-single
                          (fn-auth-session-base (fn-own-conn-session conn))
                          (string-append "437 transfer rejected; "
                                         (fn-post-store-refusal-text detail))))
                  (equal (fn-own-store (cdr r)) (fn-own-store o))
                  (equal (fn-own-ledger (cdr r)) (fn-own-ledger o))
                  (equal (fn-own-feeds (cdr r)) (fn-own-feeds o)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-own-transit-outcome fn-own-outcome-completion
                            fn-own-outcome-rendering fn-own-refusal-wordp
                            fn-post-store-refusalp fn-served-transit-outcome
                            fn-peer-transit-outcome
                            fn-peer-transit-outcome-effects
                            fn-peer-transit-code fn-peer-transit-refusal-line
                            fn-pa-served-word)
                           (fn-own-completion-consumedp fn-own-feed-durable
                            fn-own-advance fn-peer-single
                            fn-post-store-refusal-text)))))

; -----------------------------------------------------------------------------
; D23, the carried arm (planning/decisions.md, 2026-09-24).  Host path:
; host/native/owner.lisp fnn-owner-attempt-transit, NNTP transit only
; (fnn-owner-drain-one passes the delivering boundary), asks
; fn-owner-peer-carrier-plan (host/owner-host.lisp) for fn-pa-current-plan
; with the boundary's carried-source list; on (:carried ...) it builds
; fn-pa-carried-event (fn-owner-peer-carried-relay-event) and publishes it
; through fnn-owner-identity-commit, whose Store prepare admits a kind-4
; event only when fn-replay-identity-step answers :ok.

; What R stores, and so what R's feed offers onward, is the received octets
; (the relayed octets fn-peer-relayed-octets made of what arrived, whose
; non-Path, non-Xref bytes are what arrived:
; fn-peer-relayed-octets-change-only-path-and-xref,
; books/peer-inbound-invariants), and the authored source is the carrier's.
(defthm fn-osp-carried-event-keeps-the-relayed-octets
  (let ((e (fn-pa-carried-event
            sequence txid generation msgid received groups obligation-id
            content-subject release-evidence charge snapshots carried
            clock-observation)))
    (implies e
             (and (equal (fn-stxa-article-record e)
                         (fn-record-encode
                          (fn-record-make sequence txid generation msgid received
                                          groups obligation-id content-subject
                                          release-evidence charge
                                          (fn-record-stamp-of-observation
                                           clock-observation))))
                  (equal (fn-stxa-authored-source e)
                         (nth 1 (fn-pa-carrier-form received))))))
  :hints (("Goal"
           :use ((:instance fn-pa-carried-arm-needs-the-list-and-no-local-snapshot
                            (transitp t))
                 (:instance fn-pa-carried-event-requires-the-carried-arm))
           :in-theory (e/d (fn-pa-carried-event fn-stxa-make-carried)
                           (fn-pa-current-plan fn-pa-carrier-form
                            fn-pa-carried-arm-needs-the-list-and-no-local-snapshot
                            fn-pa-carried-event-requires-the-carried-arm
                            fn-hsig-article-event-carried-bindsp
                            fn-stxa-bindsp fn-stxe-encode 
                            fn-record-stamp-of-observation fn-record-make
                            fn-record-string-octets
                            fn-hsig-carried-record-metadatap
                            fn-hsig-authored-source-fields
                            fn-hsig-authored-source-id)))))

(defthm fn-osp-carried-event-stores-the-relayed-octets
  (let ((e (fn-pa-carried-event
            sequence txid generation msgid received groups obligation-id
            content-subject release-evidence charge snapshots carried
            clock-observation)))
    (implies e
             (equal (fn-record-payload
                     (fn-record-result-record
                      (fn-record-decode-exact (fn-stxa-article-record e))))
                    received)))
  :hints (("Goal"
           :use (fn-osp-carried-event-keeps-the-relayed-octets
                 (:instance fn-pa-carried-event-is-a-carried-record)
                 (:instance fn-osp-bound-verdict-names-the-encoded-record
                  (e (fn-pa-carried-event
                      sequence txid generation msgid received groups obligation-id
                      content-subject release-evidence charge snapshots carried
                      clock-observation))
                  (r (fn-record-make sequence txid generation msgid received
                                     groups obligation-id content-subject
                                     release-evidence charge
                                     (fn-record-stamp-of-observation
                                      clock-observation))))
                 (:instance fn-record-round-trip-succeeds
                  (record (fn-record-make sequence txid generation msgid received
                                          groups obligation-id content-subject
                                          release-evidence charge
                                          (fn-record-stamp-of-observation
                                           clock-observation)))))
           :in-theory (disable fn-pa-carried-event fn-stxa-bindsp
                               fn-osp-carried-event-keeps-the-relayed-octets
                               fn-pa-carried-event-is-a-carried-record
                               fn-record-round-trip-succeeds
                               fn-hls-kind4-verdict-event

                               fn-record-stamp-of-observation))))

; Replay's dispatch: a carried composite is recorded by the carried branch,
; never by the enrolled one and never faulted for a missing snapshot.
(defthm fn-osp-replay-records-a-carried-composite
  (implies (and (fn-hsig-article-event-carried-bindsp e)
                (equal (fn-stxk-context-kind ctx) :ok)
                (equal (fn-store-event-sequence e) (fn-stxk-context-next ctx)))
           (equal (fn-replay-identity-step ctx e)
                  (fn-replay-apply-carried-verdict
                   ctx (fn-stmt-value
                        (fn-stxe-decode-exact (fn-stxa-verdict-event e))))))
  :hints (("Goal"
           :use ((:instance fn-hls-kind4-disjoint-from-other-store-events
                            (event e)))
           :in-theory (e/d (fn-replay-identity-step)
                           (fn-replay-apply-carried-verdict
                            fn-hls-kind4-disjoint-from-other-store-events
                            fn-hsig-article-event-carried-bindsp
                            fn-stxk-p fn-stxe-p fn-stxa-p fn-stxa-bindsp
                            fn-hsig-article-event-snapshot-bindsp
                            fn-stxe-decode-exact fn-stxk-apply-snapshot
                            fn-stxk-apply-verdict fn-store-event-sequence
                            fn-replay-identity-advance)))))

;; PRF-098: the revoked composite at replay.  Replay's dispatch records a
;; revoked composite by its own branch (never the enrolled one, never the
;; carried one), and admits it exactly when the generation its verdict names
;; is, in the replayed snapshots, a tombstone of exactly the verdict's
;; principal and the stored carrier's keys were enrolled for that principal.
(defthm fn-osp-replay-records-a-revoked-composite
  (implies (and (fn-hsig-article-event-revoked-bindsp e)
                (equal (fn-stxk-context-kind ctx) :ok)
                (equal (fn-store-event-sequence e) (fn-stxk-context-next ctx)))
           (equal (fn-replay-identity-step ctx e)
                  (fn-replay-apply-revoked-verdict
                   ctx (fn-stmt-value
                        (fn-stxe-decode-exact (fn-stxa-verdict-event e)))
                   (fn-hsig-article-event-carrier-keys e))))
  :hints (("Goal"
           :use ((:instance fn-hls-kind4-disjoint-from-other-store-events
                            (event e))
                 (:instance fn-hsig-article-event-revoked-bindsp-facts
                            (event e))
                 (:instance fn-hsig-article-event-revoked-is-not-carried
                            (event e)))
           :in-theory (e/d (fn-replay-identity-step)
                           (fn-replay-apply-carried-verdict
                            fn-replay-apply-revoked-verdict
                            fn-hls-kind4-disjoint-from-other-store-events
                            fn-hsig-article-event-carried-bindsp
                            fn-hsig-article-event-revoked-bindsp
                            fn-hsig-article-event-revoked-bindsp-facts
                            fn-hsig-article-event-revoked-is-not-carried
                            fn-hsig-article-event-carrier fn-hsig-article-event-carrier-keys
                            fn-stxk-p fn-stxe-p fn-stxa-p fn-stxa-bindsp
                            fn-hsig-article-event-snapshot-bindsp
                            fn-stxe-decode-exact fn-stxk-apply-snapshot
                            fn-stxk-apply-verdict fn-store-event-sequence
                            fn-replay-identity-advance)))))

; KEYSTONE (replay admits :revoked exactly at a tombstone).  Given the
; composite's verdict is at the replay cursor, the step is :ok exactly when
; fn-hsig-revoked-tombstone-bindsp holds over the replayed snapshots; it then
; records exactly that verdict and leaves the keyring snapshots unchanged.
(defthm fn-osp-replay-admits-a-revoked-composite-exactly-at-its-tombstone
  (let* ((v (fn-stmt-value (fn-stxe-decode-exact (fn-stxa-verdict-event e))))
         (keys (fn-hsig-article-event-carrier-keys e))
         (next (fn-replay-identity-step ctx e)))
    (implies (and (fn-hsig-article-event-revoked-bindsp e)
                  (fn-stxe-p v)
                  (equal (fn-stxk-context-kind ctx) :ok)
                  (equal (fn-store-event-sequence e) (fn-stxk-context-next ctx))
                  (equal (fn-stxe-sequence v) (fn-stxk-context-next ctx)))
             (and (iff (equal (fn-stxk-context-kind next) :ok)
                       (fn-hsig-revoked-tombstone-bindsp
                        v keys (fn-stxk-context-snapshots ctx)))
                  (implies (equal (fn-stxk-context-kind next) :ok)
                           (and (equal (fn-stxk-context-verdicts next)
                                       (cons v (fn-stxk-context-verdicts ctx)))
                                (equal (fn-stxk-context-snapshots next)
                                       (fn-stxk-context-snapshots ctx)))))))
  :hints (("Goal"
           :use ((:instance fn-osp-replay-records-a-revoked-composite)
                 (:instance fn-hsig-article-event-revoked-bindsp-facts
                            (event e)))
           :in-theory (e/d (fn-replay-apply-revoked-verdict fn-stxk-fault
                            fn-stxk-context)
                           (fn-replay-identity-step
                            fn-osp-replay-records-a-revoked-composite
                            fn-hsig-article-event-revoked-bindsp
                            fn-hsig-article-event-revoked-bindsp-facts
                            fn-hsig-revoked-tombstone-bindsp
                            fn-hsig-article-event-carrier fn-hsig-article-event-carrier-keys
                            fn-stxe-p fn-stxe-decode-exact)))))

; A carried or revoked composite never changes a keyring: the replay step
; that records it leaves the snapshot list as it was.
(defthm fn-osp-carried-composite-keeps-the-keyring
  (implies (and (fn-hsig-article-event-carried-bindsp e)
                (equal (fn-stxk-context-kind ctx) :ok)
                (equal (fn-store-event-sequence e) (fn-stxk-context-next ctx)))
           (equal (fn-stxk-context-snapshots (fn-replay-identity-step ctx e))
                  (fn-stxk-context-snapshots ctx)))
  :hints (("Goal"
           :use ((:instance fn-osp-replay-records-a-carried-composite))
           :in-theory (e/d (fn-replay-apply-carried-verdict fn-stxk-fault
                            fn-stxk-context)
                           (fn-replay-identity-step
                            fn-osp-replay-records-a-carried-composite
                            fn-hsig-article-event-carried-bindsp
                            fn-stxe-p fn-stxe-decode-exact)))))

(defthm fn-osp-revoked-composite-keeps-the-keyring
  (implies (and (fn-hsig-article-event-revoked-bindsp e)
                (equal (fn-stxk-context-kind ctx) :ok)
                (equal (fn-store-event-sequence e) (fn-stxk-context-next ctx)))
           (equal (fn-stxk-context-snapshots (fn-replay-identity-step ctx e))
                  (fn-stxk-context-snapshots ctx)))
  :hints (("Goal"
           :use ((:instance fn-osp-replay-records-a-revoked-composite))
           :in-theory (e/d (fn-replay-apply-revoked-verdict fn-stxk-fault
                            fn-stxk-context)
                           (fn-replay-identity-step
                            fn-osp-replay-records-a-revoked-composite
                            fn-hsig-article-event-revoked-bindsp
                            fn-hsig-revoked-tombstone-bindsp
                            fn-hsig-article-event-carrier fn-hsig-article-event-carrier-keys
                            fn-stxe-p fn-stxe-decode-exact)))))

; The recorded pair is (token detail generation) of that verdict
; (fn-replay-verdict-pairs), and the HDR :fn-verified item the reader renders
; for it (fn-own-read-hdr-fn-verified-is-the-pinned-verdict, books/
; owner-verdict-read) begins `carried', never `verified'.
(defthm fn-osp-carried-record-reads-carried
  (equal (fn-stx-reader-verdict
          msgid (cons (cons msgid (fn-stx-make-verdict :carried detail generation))
                      verdicts))
         (append *fn-stx-token-carried* (cons 32 (fn-stx-hex-octets detail))))
  :hints (("Goal" :in-theory (enable fn-stx-reader-verdict fn-stx-reader-item
                                     fn-stx-verified-item))))
