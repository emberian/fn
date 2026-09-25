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
; fn-pa-served-word (fn-owner-served-carried-word, line 1186), and
; fn-owner-outcome (line 1095) runs fn-own-outcome with it.
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
        (plan (fn-pa-current-plan received snapshots nil)))
    (implies e
             (and (equal (car plan) :ok)
                  (fn-stxa-p e)
                  (equal (fn-stxe-msgid (fn-hls-kind4-verdict-event e)) msgid)
                  (equal (fn-stxe-keyring-generation (fn-hls-kind4-verdict-event e))
                         (nth 6 plan)))))
  :hints (("Goal"
           :use (fn-pa-authorized-event-requires-current-plan-by-definition
                 (:instance fn-osp-carried-event-base-shape
                  (keyring-generation (nth 6 (fn-pa-current-plan received snapshots nil)))
                  (enrolled-snapshot (fn-stxk-snapshot
                                      (nth 5 (fn-pa-current-plan received snapshots nil))))
                  (source (nth 1 (fn-pa-current-plan received snapshots nil)))
                  (principal (nth 2 (fn-pa-current-plan received snapshots nil)))
                  (keys (nth 3 (fn-pa-current-plan received snapshots nil)))
                  (signatures (nth 4 (fn-pa-current-plan received snapshots nil)))
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
         (plan (fn-pa-current-plan received snapshots nil))
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
         (plan (fn-pa-current-plan received snapshots nil))
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
  (implies (equal (car (fn-pa-current-plan received snapshots nil)) :refused)
           (and (member-equal (cadr (fn-pa-current-plan received snapshots nil))
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
                            fn-pa-served-word)
                           (fn-nntp-post-outcome fn-own-completion-consumedp
                            fn-own-feed-durable fn-own-advance
                            )))))

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
           :use ((:instance fn-pa-carried-arm-needs-the-list-and-no-local-snapshot)
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
