; Teeth for books/owner-signed-post (P8 / PRF-026, the signed served POST).
;
; The witness is the host's own sequence over the owner: a connection POSTs
; an FN-Authorship carrier through fn-own-read, the writer takes it, ACL2
; plans over the staged (injected) octets and this Store's enrollment,
; fn-pa-authorized-event builds the kind-4 event, the Store prepares and
; publishes it, (:complete) finishes, fn-own-outcome answers 240, and a reader
; opened afterwards is answered HDR :fn-verified from its pin.  The
; primitive observations are :verified here; the signatures are fixtures.
(in-package "ACL2")
(include-book "../../books/owner-signed-post")
(include-book "peer-authored-accept-tests")
(include-book "store-identity-traces-tests")
(include-book "std/testing/must-fail" :dir :system)

(defconst *ospt-groups* '("fn.test"))
(defconst *ospt-msgid* "<topic-binding@example.invalid>")
(defconst *ospt-agent*
  '(102 110 46 101 120 97 109 112 108 101 46 105 110 118 97 108 105 100))
(defconst *ospt-config*
  (fn-inj-make-config t *ospt-agent* (list (fn-nntp-string-octets "fn.test"))
                      32768))
(defconst *ospt-obs* (fn-clock-observation 2000000 1600000010000 500 t))
(defconst *ospt-post-command* (append (fn-nntp-string-octets "POST") '(13 10)))

; The Store after this node enrolled the author (keyring generation 1).
(make-event `(defconst *ospt-enrollment*
               ',(fn-hsig-keyring-event 0 0 0 1 *tha-principal* *tha-keys*)))
(make-event `(defconst *ospt-enrolled*
               ',(fn-sit-commit-identity (fn-sn-initial *ospt-groups* 32)
                                         *ospt-enrollment*)))
(assert-event (equal (fn-sn-keyring-snapshots *ospt-enrolled*)
                     (list *ospt-enrollment*)))

; Reader A (connection 0) before the post; the poster is connection 1.
(make-event
 `(defconst *ospt-open*
    ',(let* ((o (fn-own-run (fn-own-start *ospt-enrolled* 4)
                            (list (list :configure *ospt-config*)
                                  (list :observe *ospt-obs*))))
             (o (cdr (fn-own-open o nil))))
        (cdr (fn-own-open o nil)))))
(defconst *ospt-poster* 1)
(defun ospt-submit (o octets)
  (let* ((offered (cdr (fn-own-read o *ospt-poster* *ospt-post-command*))))
    (cdr (fn-own-read offered *ospt-poster* (append octets '(46 13 10))))))
(make-event
 `(defconst *ospt-taken*
    ',(fn-own-step (ospt-submit *ospt-open* *tha-received*) '(:take))))
(assert-event (equal (fn-own-sub-id (fn-own-inflight *ospt-taken*)) *ospt-poster*))

; The octets the host attempts are the staged injected ones; the carrier
; survives injection and the plan selects this Store's enrollment.
(defconst *ospt-staged* (fn-inj-decision-octets
                         (fn-own-sub-decision (fn-own-inflight *ospt-taken*))))
(assert-event (not (equal *ospt-staged* *tha-received*)))
(defconst *ospt-snapshots* (fn-sn-keyring-snapshots (fn-own-store *ospt-taken*)))
(assert-event
 (equal (fn-pa-current-plan *ospt-staged* *ospt-snapshots* nil)
        (list :ok *tha-root-source* *tha-principal* *tha-keys*
              *tha-signatures* *ospt-enrollment* 1)))

(defun ospt-event (received snapshots)
  (let ((coordinates
         (let ((s (fn-own-store *ospt-taken*)))
           (list (fn-sn-identity-next s)
                 (fn-state-next-txid (fn-node-acceptance (fn-sn-node s)))))))
    (fn-pa-authorized-event
     (first coordinates) (second coordinates) (second coordinates)
     *ospt-msgid* received *ospt-groups*
     (fn-record-octets-string
      (fn-id-text (fn-id-obligation-of (fn-record-string-octets *ospt-msgid*)
                                       (fn-id-subject-of-payload received))))
     (fn-record-octets-string (fn-id-text (fn-id-subject-of-payload received)))
     "served-post-evidence" (fn-charge-for-payload (len received))
     snapshots *tha-ml-key* :verified :verified *ospt-obs*)))
(make-event `(defconst *ospt-event* ',(ospt-event *ospt-staged* *ospt-snapshots*)))
(assert-event (fn-stxa-p *ospt-event*))
(defun ospt-store-events (event)
  (list '(:store (:io :start-frontier nil))
        '(:store (:io :frontier-file :ok))
        '(:store (:io :frontier-replace :ok))
        '(:store (:io :frontier-directory :ok))
        (list :store (list :prepare-identity event))
        '(:store (:io :record-file :ok))
        '(:store (:io :record-link :ok))
        '(:store (:io :record-directory :ok))))
(make-event
 `(defconst *ospt-completing*
    ',(fn-own-run *ospt-taken* (ospt-store-events *ospt-event*))))
(make-event
 `(defconst *ospt-finished* ',(fn-own-step *ospt-completing* '(:complete))))

; ---------------------------------------------------------------------------
; fn-osp-signed-post-finish-records-its-verdict: reachable witness.
(defun ospt-finish-conclusion (o received snapshots)
  (let* ((e (ospt-event received snapshots))
         (v (fn-hls-kind4-verdict-event e)))
    (equal (fn-sn-verdict-lookup (fn-own-store (fn-own-step o '(:complete)))
                                 *ospt-msgid*)
           (fn-stx-make-verdict (fn-stxe-token v) (fn-stxe-detail v)
                                (nth 6 (fn-pa-current-plan received snapshots nil))))))
(assert-event (fn-sn-completion-enabledp (fn-own-store *ospt-completing*)))
(assert-event (equal (fn-sn-completion-record (fn-own-store *ospt-completing*))
                     *ospt-event*))
(assert-event (null (fn-sn-verdict-lookup (fn-own-store *ospt-completing*)
                                          *ospt-msgid*)))
(assert-event (ospt-finish-conclusion *ospt-completing* *ospt-staged*
                                      *ospt-snapshots*))
; The recorded token on this trace is :verified, bound to the principal.
(assert-event (equal (fn-stxe-token (fn-hls-kind4-verdict-event *ospt-event*))
                     :verified))
(assert-event (equal (fn-stxe-detail (fn-hls-kind4-verdict-event *ospt-event*))
                     *tha-principal*))

; Without the event (no enrollment selected: the plan refuses and
; fn-pa-authorized-event is nil).  The completion record is then not that
; nil event either; an enabled completion always has a record, so this
; hypothesis cannot fail alone.
(assert-event (null (ospt-event *ospt-staged* nil)))
(must-fail (assert-event (ospt-finish-conclusion *ospt-completing*
                                                 *ospt-staged* nil)))
; Without completion-record = event: another authorized event (the same
; carrier under a generation-2 enrollment) is not the record completing.
(make-event `(defconst *ospt-g2*
               ',(list (fn-hsig-keyring-event 0 0 0 2 *tha-principal* *tha-keys*))))
(assert-event (ospt-event *ospt-staged* *ospt-g2*))
(assert-event (not (equal (ospt-event *ospt-staged* *ospt-g2*) *ospt-event*)))
(must-fail (assert-event (ospt-finish-conclusion *ospt-completing*
                                                 *ospt-staged* *ospt-g2*)))
; Without fn-sn-completion-enabledp: the same completion record with the
; identity sequence one ahead; the gate is closed and nothing is recorded.
(defun ospt-with-store (o s)
  (fn-own-make s (fn-own-view o) (fn-own-conns o) (fn-own-next-id o)
               (fn-own-max-conns o) (fn-own-pending o) (fn-own-ledger o)
               (fn-own-clock o) (fn-own-facts o) (fn-own-config o)
               (fn-own-queue o) (fn-own-inflight o) (fn-own-feeds o)))
(make-event
 `(defconst *ospt-off*
    ',(ospt-with-store *ospt-completing*
                       (fn-sn-advance-identity-next
                        (fn-own-store *ospt-completing*)))))
(assert-event (not (fn-sn-completion-enabledp (fn-own-store *ospt-off*))))
(assert-event (equal (fn-sn-completion-record (fn-own-store *ospt-off*))
                     *ospt-event*))
(must-fail (assert-event (ospt-finish-conclusion *ospt-off* *ospt-staged*
                                                 *ospt-snapshots*)))

; ---------------------------------------------------------------------------
; The served outcome: 240 after the finish (fn-osp-finished-post-outcome-is-
; durable), and a reader opened afterwards answers HDR :fn-verified with the
; recorded verdict (fn-osp-reader-after-signed-post-reports-its-verdict,
; then fn-own-read, the host-called fold).
(assert-event (equal (fn-own-outcome-completion *ospt-finished* :durable)
                     :durable))
(defconst *ospt-240* (fn-own-outcome *ospt-finished* *ospt-poster* :durable))
(assert-event (equal (fn-served-reply-octets (car *ospt-240*))
                     (append (fn-nntp-string-octets "240 article received OK")
                             '(13 10))))
(defun ospt-reader-verdict (o)
  (let* ((o2 (cdr (fn-own-open (fn-own-step o '(:complete)) nil)))
         (conn (fn-own-find-conn (fn-own-next-id o) (fn-own-conns o2))))
    (and conn
         (fn-stx-reader-verdict *ospt-msgid* (fn-own-conn-verdicts conn)))))
(assert-event
 (equal (ospt-reader-verdict *ospt-completing*)
        (fn-stx-reader-item
         (fn-stx-make-verdict :verified *tha-principal* 1))))
(make-event
 `(defconst *ospt-reader-b* ',(cdr (fn-own-open (cdr *ospt-240*) nil))))
(defconst *ospt-hdr*
  (append (fn-nntp-string-octets
           "HDR :fn-verified <topic-binding@example.invalid>") '(13 10)))
(defconst *ospt-read-b*
  (fn-own-read *ospt-reader-b* (fn-own-next-id (cdr *ospt-240*)) *ospt-hdr*))
(assert-event
 (equal (fn-served-reply-octets (car *ospt-read-b*))
        (append (fn-nntp-string-octets "225 headers follow")
                '(13 10 48 32)
                (fn-nntp-string-octets "verified ")
                (fn-stx-hex-octets *tha-principal*)
                (fn-nntp-string-octets " keyring 1")
                '(13 10 46 13 10))))
; Reader A, open before the post, keeps its pin and has no verdict.
(assert-event
 (not (equal (ospt-reader-verdict *ospt-completing*)
             (fn-stx-reader-verdict
              *ospt-msgid*
              (fn-own-conn-verdicts
               (fn-own-find-conn 0 (fn-own-conns *ospt-finished*)))))))
; Without the connection bound: at max-conns the reader is not opened.
(make-event
 `(defconst *ospt-full*
    ',(fn-own-make (fn-own-store *ospt-completing*) (fn-own-view *ospt-completing*)
                   (fn-own-conns *ospt-completing*) (fn-own-next-id *ospt-completing*)
                   (len (fn-own-conns *ospt-completing*))
                   (fn-own-pending *ospt-completing*) (fn-own-ledger *ospt-completing*)
                   (fn-own-clock *ospt-completing*) (fn-own-facts *ospt-completing*)
                   (fn-own-config *ospt-completing*) (fn-own-queue *ospt-completing*)
                   (fn-own-inflight *ospt-completing*) (fn-own-feeds *ospt-completing*))))
(must-fail (assert-event (ospt-reader-verdict *ospt-full*)))
; The other three hypotheses of the reader theorem are the finish theorem's:
; with the gate closed the reader's pin has no verdict for the Message-ID.
(must-fail
 (assert-event (equal (ospt-reader-verdict *ospt-off*)
                      (fn-stx-reader-item
                       (fn-stx-make-verdict :verified *tha-principal* 1)))))

; ---------------------------------------------------------------------------
; The refused arm.  fn-osp-plan-refusal-is-a-served-reason and
; fn-osp-served-refusal-renders-its-reason, on a POST in flight.
(assert-event (equal (fn-pa-current-plan *ospt-staged* nil nil)
                     '(:refused :local-enrollment)))
(defconst *ospt-malformed*
  (append (tha-line "FN-Authorship: !!!") *tha-root-source*))
(assert-event (equal (fn-pa-current-plan *ospt-malformed* *ospt-snapshots* nil)
                     '(:refused :carrier)))
(assert-event (not (equal (fn-pa-carrier-form *ospt-malformed*) :absent)))
; Without the refused plan, the plan's second element is not a reason.
(must-fail
 (assert-event
  (member-equal (cadr (fn-pa-current-plan *ospt-staged* *ospt-snapshots* nil))
                '(:article :carrier :carrier-shape :local-enrollment))))
; An absent carrier is the unsigned arm with its word unchanged.
(assert-event (equal (fn-pa-current-plan *tha-root-source* *ospt-snapshots* nil)
                     :absent))
(assert-event (equal (fn-pa-served-word :durable nil) :durable))
(assert-event (equal (fn-pa-served-word :refused nil) :refused))

(defun ospt-refusal-conclusion (o id detail)
  (let* ((word (fn-pa-served-word :refused detail))
         (conn (fn-own-find-conn id (fn-own-conns o)))
         (r (fn-own-outcome o id word)))
    (and (equal word detail)
         (equal (car r)
                (fn-post-result-effects
                 (fn-nntp-post-outcome
                  (fn-auth-post-session (fn-own-conn-session conn)) detail)))
         (equal (fn-own-ledger (cdr r)) (fn-own-ledger o)))))
(assert-event (ospt-refusal-conclusion *ospt-taken* *ospt-poster*
                                       :local-enrollment))
(assert-event
 (equal (fn-served-reply-octets
         (car (fn-own-outcome *ospt-taken* *ospt-poster*
                              (fn-pa-served-word :refused :local-enrollment))))
        (append (fn-nntp-string-octets
                 "441 posting failed; the signer has no current enrollment here (local-enrollment)")
                '(13 10))))
(assert-event
 (equal (fn-served-reply-octets
         (car (fn-own-outcome *ospt-taken* *ospt-poster*
                              (fn-pa-served-word :refused :signature))))
        (append (fn-nntp-string-octets
                 "441 posting failed; the author signature does not verify")
                '(13 10))))
; Without the reason in the relayed set: a Store word is not relayed.
(must-fail (assert-event (ospt-refusal-conclusion *ospt-taken* *ospt-poster*
                                                  :duplicate)))
; Without a completion unconsumed: after the kind-4 finish the word is
; :uncertain, never a refusal line.
(must-fail (assert-event (ospt-refusal-conclusion *ospt-finished* *ospt-poster*
                                                  :signature)))
; Without the in-flight submission being this connection's: reader A.
(must-fail (assert-event (ospt-refusal-conclusion *ospt-taken* 0 :signature)))
; Without an in-flight submission: the queued POST before the take.
(must-fail (assert-event (ospt-refusal-conclusion
                          (ospt-submit *ospt-open* *tha-received*)
                          *ospt-poster* :signature)))
; Without the connection: the in-flight submission's connection is gone.
(must-fail
 (assert-event
  (ospt-refusal-conclusion
   (fn-own-make (fn-own-store *ospt-taken*) (fn-own-view *ospt-taken*)
                (fn-own-remove-conn *ospt-poster* (fn-own-conns *ospt-taken*))
                (fn-own-next-id *ospt-taken*) (fn-own-max-conns *ospt-taken*)
                (fn-own-pending *ospt-taken*) (fn-own-ledger *ospt-taken*)
                (fn-own-clock *ospt-taken*) (fn-own-facts *ospt-taken*)
                (fn-own-config *ospt-taken*) (fn-own-queue *ospt-taken*)
                (fn-own-inflight *ospt-taken*) (fn-own-feeds *ospt-taken*))
   *ospt-poster* :signature)))

; ---------------------------------------------------------------------------
; D23, the carried arm on a Store with no enrollment of the author.  The
; owner, Store prepare, (:complete) and a reader opened afterwards are the
; host-called functions; the delivering boundary's list is *pat-carries*.
(make-event
 `(defconst *ospt-bare-open*
    ',(let* ((o (fn-own-run (fn-own-start (fn-sn-initial *ospt-groups* 32) 4)
                            (list (list :configure *ospt-config*)
                                  (list :observe *ospt-obs*))))
             (o (cdr (fn-own-open o nil))))
        (cdr (fn-own-open o nil)))))
(make-event
 `(defconst *ospt-bare-taken*
    ',(fn-own-step (ospt-submit *ospt-bare-open* *tha-received*) '(:take))))
(defconst *ospt-bare-staged*
  (fn-inj-decision-octets
   (fn-own-sub-decision (fn-own-inflight *ospt-bare-taken*))))
(assert-event (null (fn-sn-keyring-snapshots (fn-own-store *ospt-bare-taken*))))
(assert-event (equal (fn-pa-current-plan *ospt-bare-staged* nil nil)
                     '(:refused :local-enrollment)))
(assert-event (equal (car (fn-pa-current-plan *ospt-bare-staged* nil
                                              *pat-carries*))
                     :carried))
(defun ospt-carried-event (received carried)
  (let ((s (fn-own-store *ospt-bare-taken*)))
    (fn-pa-carried-event
     (fn-sn-identity-next s)
     (fn-state-next-txid (fn-node-acceptance (fn-sn-node s)))
     (fn-state-next-txid (fn-node-acceptance (fn-sn-node s)))
     *ospt-msgid* received *ospt-groups*
     (fn-record-octets-string
      (fn-id-text (fn-id-obligation-of (fn-record-string-octets *ospt-msgid*)
                                       (fn-id-subject-of-payload received))))
     (fn-record-octets-string (fn-id-text (fn-id-subject-of-payload received)))
     "transit-evidence" (fn-charge-for-payload (len received))
     (fn-sn-keyring-snapshots s) carried *ospt-obs*)))
(make-event `(defconst *ospt-carried*
               ',(ospt-carried-event *ospt-bare-staged* *pat-carries*)))
(assert-event (fn-hsig-article-event-carried-bindsp *ospt-carried*))
(assert-event (null (ospt-carried-event *ospt-bare-staged* nil)))
; Replay's step records it (fn-osp-replay-records-a-carried-composite).
(defconst *ospt-bare-ctx* (fn-sn-identity-context (fn-own-store *ospt-bare-taken*)))
(assert-event (equal (fn-stxk-context-kind *ospt-bare-ctx*) :ok))
(assert-event
 (equal (fn-replay-identity-step *ospt-bare-ctx* *ospt-carried*)
        (fn-replay-apply-carried-verdict
         *ospt-bare-ctx* (fn-hls-kind4-verdict-event *ospt-carried*))))
(assert-event (equal (fn-stxk-context-kind
                      (fn-replay-identity-step *ospt-bare-ctx* *ospt-carried*))
                     :ok))
; Tooth (the sequence): the same event one identity sequence late faults.
(must-fail
 (assert-event
  (equal (fn-stxk-context-kind
          (fn-replay-identity-step
           (fn-stxk-context :ok (1+ (fn-stxk-context-next *ospt-bare-ctx*))
                            nil nil
                            (fn-stxk-context-current-generation *ospt-bare-ctx*)
                            nil)
           *ospt-carried*))
         :ok)))
; Tooth (the carried binding): the forged :verified composite at generation
; 0 is refused by replay for want of a snapshot.
(assert-event (not (fn-hsig-article-event-carried-bindsp *pat-forged-verified*)))

; The Store publishes it; a reader opened after (:complete) answers
; HDR :fn-verified `carried <principal>' (fn-osp-carried-record-reads-carried).
(make-event
 `(defconst *ospt-carried-completing*
    ',(fn-own-run *ospt-bare-taken* (ospt-store-events *ospt-carried*))))
(assert-event (fn-sn-completion-enabledp (fn-own-store *ospt-carried-completing*)))
(assert-event (equal (fn-sn-completion-record
                      (fn-own-store *ospt-carried-completing*))
                     *ospt-carried*))
(assert-event
 (equal (ospt-reader-verdict *ospt-carried-completing*)
        (append (fn-nntp-string-octets "carried ")
                (fn-stx-hex-octets *tha-principal*))))
(must-fail
 (assert-event
  (equal (ospt-reader-verdict *ospt-carried-completing*)
         (fn-stx-reader-item
          (fn-stx-make-verdict :verified *tha-principal* 0)))))

; ---------------------------------------------------------------------------
; fn-osp-transit-refusal-renders-its-reason, on a transit in flight.  The
; owner is *ospt-taken* with its in-flight submission replaced by an IHAVE
; transit on the same connection, id, version and mark, exactly as
; tests/acl2/owner-tests.lisp own-fed-transit-on-connection builds one.
(defun ospt-with-transit (o kind)
  (let ((sub (fn-own-inflight o)))
    (fn-own-make (fn-own-store o) (fn-own-view o) (fn-own-conns o)
                 (fn-own-next-id o) (fn-own-max-conns o) (fn-own-pending o)
                 (fn-own-ledger o) (fn-own-clock o) (fn-own-facts o)
                 (fn-own-config o) (fn-own-queue o)
                 (fn-own-sub-make (fn-own-sub-id sub) (fn-own-sub-version sub)
                                  (fn-own-sub-mark sub)
                                  (fn-peer-make-submission
                                   "p" kind (fn-nntp-string-octets *ospt-msgid*)
                                   *tha-received*))
                 (fn-own-feeds o))))
(defconst *ospt-transit* (ospt-with-transit *ospt-taken* :ihave))
(assert-event (fn-own-transit-subp (fn-own-inflight *ospt-transit*)))
(assert-event (not (fn-own-completion-consumedp *ospt-transit*)))
(defun ospt-transit-conclusion (o id kind detail)
  (let* ((word (fn-pa-served-word :refused detail))
         (conn (fn-own-find-conn id (fn-own-conns o)))
         (r (fn-own-transit-outcome o id kind nil word)))
    (and (equal word detail)
         (equal (car r)
                (fn-peer-single
                 (fn-auth-session-base (fn-own-conn-session conn))
                 (string-append "437 transfer rejected; "
                                (fn-post-store-refusal-text detail))))
         (equal (fn-own-store (cdr r)) (fn-own-store o))
         (equal (fn-own-ledger (cdr r)) (fn-own-ledger o))
         (equal (fn-own-feeds (cdr r)) (fn-own-feeds o)))))
(assert-event (ospt-transit-conclusion *ospt-transit* *ospt-poster* :want
                                       :control-not-filed))
(assert-event (ospt-transit-conclusion *ospt-transit* *ospt-poster* :want
                                       :local-enrollment))
; On the wire: the reason POST's 441 names, after 437.
(assert-event
 (equal (fn-served-reply-octets
         (car (fn-own-transit-outcome
               *ospt-transit* *ospt-poster* :want nil
               (fn-pa-served-word :refused :control-not-filed))))
        (append (fn-nntp-string-octets
                 "437 transfer rejected; control message not filed: its control group is not configured here (control-not-filed)")
                '(13 10))))
(assert-event
 (equal (fn-post-store-refusal-line :control-not-filed)
        "441 posting failed; control message not filed: its control group is not configured here (control-not-filed)"))
; The word with no detail keeps its own line.
(assert-event
 (equal (fn-served-reply-octets
         (car (fn-own-transit-outcome *ospt-transit* *ospt-poster* :want nil
                                      (fn-pa-served-word :refused nil))))
        (append (fn-nntp-string-octets
                 "437 transfer rejected; refused by acceptance")
                '(13 10))))
; Without the reason in the relayed set: the word stays :refused.
(must-fail (assert-event (ospt-transit-conclusion *ospt-transit* *ospt-poster*
                                                  :want :duplicate)))
; Without the in-flight submission being this connection's: reader A.
(must-fail (assert-event (ospt-transit-conclusion *ospt-transit* 0 :want
                                                  :control-not-filed)))
; Without a transit submission: the POST in flight is fn-own-outcome's.
(must-fail (assert-event (ospt-transit-conclusion *ospt-taken* *ospt-poster*
                                                  :want :control-not-filed)))
; Without IHAVE: TAKETHIS answers 439 with the Message-ID (RFC 4644 2.5).
(must-fail (assert-event (ospt-transit-conclusion
                          (ospt-with-transit *ospt-taken* :takethis)
                          *ospt-poster* :want :control-not-filed)))
; Without the :want decision: no attempt ran and the decision is rendered.
(must-fail (assert-event (ospt-transit-conclusion *ospt-transit* *ospt-poster*
                                                  :refuse :control-not-filed)))
; Without a completion unconsumed: after the finish the word is :uncertain.
(must-fail (assert-event (ospt-transit-conclusion
                          (ospt-with-transit *ospt-finished* :ihave)
                          *ospt-poster* :want :control-not-filed)))
; Without the connection: the in-flight submission's connection is gone.
(must-fail
 (assert-event
  (ospt-transit-conclusion
   (fn-own-make (fn-own-store *ospt-transit*) (fn-own-view *ospt-transit*)
                (fn-own-remove-conn *ospt-poster* (fn-own-conns *ospt-transit*))
                (fn-own-next-id *ospt-transit*) (fn-own-max-conns *ospt-transit*)
                (fn-own-pending *ospt-transit*) (fn-own-ledger *ospt-transit*)
                (fn-own-clock *ospt-transit*) (fn-own-facts *ospt-transit*)
                (fn-own-config *ospt-transit*) (fn-own-queue *ospt-transit*)
                (fn-own-inflight *ospt-transit*) (fn-own-feeds *ospt-transit*))
   *ospt-poster* :want :control-not-filed)))
