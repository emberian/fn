; fn: owner keystones over the functions host/owner-host.lisp calls (v0 P2,
; P3, P5).
;
; books/owner-invariants states most owner theorems over fn-own-step and
; fn-own-run.  The host reaches the owner through narrower entries:
; fn-owner-outcome calls fn-own-outcome directly (owner-host.lisp:1034),
; fn-owner-chunk calls fn-ocfg-read-tls-prefix (:1240), fn-owner-open calls
; fn-ocfg-open (:1218), fn-owner-fault calls fn-ocfg-fault (:1273), and the
; writer path runs (:take), (:store ...) and (:complete) through
; fn-owner-step, which is fn-ocfg-step (:209).  Each theorem here is stated
; over one of those entries.  This is a separate book so the owner-invariants
; book stays under its proof-cost bound.
;
; Keystones:
;   fn-own-240-follows-consumed-completion       (P2; subject fn-own-finish,
;                                                  which host/owner-host.lisp
;                                                  fn-owner-finish-submission
;                                                  calls; see below)
;   fn-own-pinned-view-survives-other-post       (P3, the plan's T6)
;   fn-ocfg-open-at-the-bound-refuses            (P5, the session bound)
;   fn-ocfg-fault-is-own-fault                   (P5, the wrapper's equation)
;   fn-ocfg-fault-keeps-every-other-connection   (P5, K-FAULT-2 over the wrapper)
; Teeth: tests/acl2/owner-served-invariants-tests.lisp.

(in-package "ACL2")
(include-book "owner-tls-prefix")
(include-book "owner-prepare-correspondence")
; SEC-006: the served arm of the stored octets carries the login's
; RFC 8315 Cancel-Lock (books/cancel-lock.lisp fn-cl-served-payload).
(include-book "cancel-lock")
(include-book "injection-info-params")
(include-book "store-intern")

;; Rules withdrawn at their source that this book's proofs use
;; (lane rule-hygiene, tools/rule_cost.py).
(local (in-theory (enable (:definition fn-ipp-accountp)
                          (:definition fn-ns-entryp)
                          (:definition fn-ns-ring-entriesp)
                          (:definition fn-ns-ringp)
                          (:rewrite fn-ipp-injected-octets-without-parameters))))

; -----------------------------------------------------------------------------
; P2.  The 240 names this submission's record.
;
; fn-own-outcome renders 240 when the host's word is :durable and the ledger
; grew after the take (fn-own-outcome-completion).  Nothing in the owner ties
; the record the store completed to the submission in flight: the host reads
; the submission's Message-ID and octets out of fn-owner-take's globals and
; hands them back to fn-owner-prepare, and fn-owner-finish decides :durable by
; comparing phases and ledger lengths (owner-host.lisp:495-507).  So a 240 for
; one submission over a completion of a different record is a reachable owner
; state; tests/acl2/owner-tests.lisp's *own-240* is one (its submission is the
; injected "Hello, news." article, its completed record is <three@example>),
; asserted in the teeth book.
;
; fn-own-finish is the (:complete) event with its word computed here: the
; completion is consumed exactly as fn-own-complete consumes it, and the word
; is :durable only when that consumption happened and the completed record
; carries the in-flight submission's Message-ID and the octets the owner
; handed the Store for it (fn-own-sub-stored-octets under the live
; configuration CFG).  Any other case is :fault, which fn-own-outcome renders
; as the uncertain 441 (436 for transit).  host/owner-host.lisp
; fn-owner-finish-submission reports this word, with CFG the configured
; owner's fn-ocfg-config.

; The octets the owner hands the Store for submission SUB under the live
; configuration CFG.  host/owner-host.lisp fn-owner-take stages exactly this
; value as fn-owner-submit-octets.  A local or control submission's are its
; injected form.  A transit submission's are fn-peer-relayed-octets of the
; peer's octets: this node's Path identity prepended and Xref removed (RFC
; 5537 3.6/3.7, books/path-update.lisp).  They differ from the received
; octets (fn-own-sub-octets) whenever a Path identity is configured, so a
; completion compared with the received octets names a different article
; (transit-436, 2026-09-24).
; SEC-006 (PRF-210): a local submission's are its injected octets with the
; RFC 8315 lines the node generates for the submission's account under the
; key ring RING (the owner's fn-own-node-secret) IN FRONT: `Cancel-Lock:
; sha256:lock(E, ACCOUNT, MSGID)' under the current epoch E and, on a
; cancel or Supersedes, `Cancel-Key:' with one key per retained epoch
; (books/cancel-lock.lisp fn-cl-served-payload).  Without an account
; (control, BP, an unauthenticated POST) or a ring they are the injected
; octets.  The lines are outside the D25 source (books/cancel-lock-lines.lisp
; fn-cll-skip; fn-own-stored-octets-keep-the-injected-octets below).
(defun fn-own-sub-stored-octets (cfg sub secret)
  (declare (xargs :guard t))
  (let ((d (fn-own-sub-decision sub)))
    (if (fn-peer-submissionp d)
        (fn-peer-relayed-octets cfg (fn-peer-submission-peer d)
                                (fn-peer-submission-octets d))
      (fn-cl-served-payload secret (fn-own-sub-account sub)
                            (fn-inj-decision-msgid d)
                            (fn-ipp-injected-octets d secret (fn-own-sub-login sub)
                                                    cfg)))))

;; The two arms, named by definition (they are not keystones).  A local or
;; control submission's staged octets are the generated lines, if any, and
;; its own injected octets.  A transit submission's are fn-peer-relayed-octets of
;; the received octets, whose Path is the received Path with this node's
;; identity and diagnostic prepended when a Path identity is set
;; (books/peer-inbound-invariants.lisp
;; fn-peer-relayed-octets-keep-the-received-path-tail).
(defthm fn-own-sub-stored-octets-of-a-local-submission-by-definition
  (implies (not (fn-peer-submissionp (fn-own-sub-decision sub)))
           (equal (fn-own-sub-stored-octets cfg sub secret)
                  (fn-cl-served-payload secret (fn-own-sub-account sub)
                                        (fn-own-sub-msgid sub)
                                        (fn-ipp-injected-octets
                                         (fn-own-sub-decision sub) secret
                                         (fn-own-sub-login sub) cfg))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-own-sub-stored-octets fn-own-sub-octets
                                   fn-own-sub-msgid)
                                  (fn-ipp-injected-octets fn-cl-served-payload)))))

(defthm fn-own-sub-stored-octets-without-an-account-by-definition
  (implies (and (not (fn-peer-submissionp (fn-own-sub-decision sub)))
                (not (fn-cl-accountp (fn-own-sub-account sub)))
                (not (fn-ipp-accountp secret (fn-own-sub-login sub)))
                (not (fn-ipp-complaints cfg)))
           (equal (fn-own-sub-stored-octets cfg sub secret)
                  (fn-own-sub-octets sub)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-own-sub-stored-octets fn-own-sub-octets
                                   fn-ipp-accountp)
                                  (fn-ipp-injected-octets fn-ipp-complaints))
           :use ((:instance fn-ipp-injected-octets-without-parameters
                            (d (fn-own-sub-decision sub))
                            (login (fn-own-sub-login sub)))))))

(defthm fn-own-sub-stored-octets-of-a-transit-submission-by-definition
  (implies (fn-peer-submissionp (fn-own-sub-decision sub))
           (equal (fn-own-sub-stored-octets cfg sub secret)
                  (fn-peer-relayed-octets
                   cfg (fn-peer-submission-peer (fn-own-sub-decision sub))
                   (fn-own-sub-octets sub))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-own-sub-stored-octets fn-own-sub-octets))))

; KEYSTONE (SEC-006, PRF-210; subject fn-own-sub-stored-octets, which
; host/owner-host.lisp fn-owner-take stages for the Store and
; fn-owner-finish-submission's gate compares with the durable record).  For
; a served submission by account A, with a key ring installed, no
; Cancel-Lock written by the poster and no signature carrier, the stored
; octets are exactly one Cancel-Lock line, A's lock for the submission's
; Message-ID under the current key epoch, then (for a cancel) the Cancel-Key
; line, then the injected octets unchanged; by
; fn-cl-account-key-opens-exactly-its-lock, A's key opens that lock and
; another account's key opens it only through a collision.
(defthm fn-own-stored-octets-carry-the-account-lock
  (let* ((d (fn-own-sub-decision sub))
         (account (fn-own-sub-account sub))
         (x (fn-ipp-injected-octets d secret (fn-own-sub-login sub) cfg))
         (fields (fn-ctl-received-fields x)))
    (implies (and (not (fn-peer-submissionp d))
                  (fn-cl-lock-wanted-p secret account fields))
             (equal (fn-own-sub-stored-octets cfg sub secret)
                    (append (fn-cll-line *fn-cll-lock-head*
                                         (fn-cl-lock (fn-ns-current secret) account
                                                     (fn-inj-decision-msgid d)))
                            (if (consp (fn-cl-key-values secret account fields))
                                (fn-cll-key-line (fn-cl-key-values secret account fields))
                              nil)
                            x))))
  :hints (("Goal" :in-theory (e/d (fn-own-sub-stored-octets)
                                  (fn-cl-served-payload fn-cl-lock fn-cl-key-values
                                   fn-ipp-injected-octets
                                   fn-ctl-received-fields fn-cll-line fn-cll-key-line
                                   fn-cl-lock-wanted-p))
           :use ((:instance fn-cl-served-payload-writes-one-account-lock
                            (ring secret)
                            (account (fn-own-sub-account sub))
                            (msgid (fn-inj-decision-msgid (fn-own-sub-decision sub)))
                            (payload (fn-ipp-injected-octets
                                      (fn-own-sub-decision sub) secret
                                      (fn-own-sub-login sub) cfg)))))))

; KEYSTONE (D25 restored, gpt-6's wave-5 review section 3; subject
; fn-own-sub-stored-octets).  Whatever the key ring and the account, the
; D25 projection (books/cancel-lock-lines.lisp fn-cll-skip, which
; books/poster-bytes.lisp reads both compared payloads through) of the
; octets a served submission stores is its injected octets: the generated
; metadata never enters the source identity, so a same-source retry by
; another account or after a key rotation compares exactly as the injected
; articles do (books/cancel-lock-d25.lisp states the verdicts).
(defthm fn-own-stored-octets-keep-the-injected-octets
  (let* ((d (fn-own-sub-decision sub))
         (x (fn-ipp-injected-octets d secret (fn-own-sub-login sub) cfg)))
    (implies (and (not (fn-peer-submissionp d))
                  (not (equal (car x) 67)))
             (equal (fn-cll-skip (fn-own-sub-stored-octets cfg sub secret)) x)))
  :hints (("Goal" :in-theory (e/d (fn-own-sub-stored-octets)
                                  (fn-cl-served-payload fn-ipp-injected-octets))
           :use ((:instance fn-cl-served-payload-projects-to-the-injected-octets
                            (ring secret)
                            (account (fn-own-sub-account sub))
                            (msgid (fn-inj-decision-msgid (fn-own-sub-decision sub)))
                            (payload (fn-ipp-injected-octets
                                      (fn-own-sub-decision sub) secret
                                      (fn-own-sub-login sub) cfg)))))))

; The store retains ROWS (records-flip, books/store-intern.lisp): the
; completion record is a held row whose payload position is a handle into
; the entry's arena, so the submission is named through ALPHA of the row
; (fn-row-wire-of: the wire record the row stands for, its payload the bytes
; under the handle).  Comparing the handle itself with the staged octets is
; false on every completion, and every served POST finish was :fault (436
; uncertain) until this read went through the arena.
(defun fn-own-completion-names-submission-p (o cfg fn-arena)
  (declare (xargs :stobjs fn-arena :guard (fn-sn-statep (fn-own-store o))))
  (let* ((sub (fn-own-inflight o))
         (record (fn-sn-completion-record (fn-own-store o)))
         (w (fn-row-wire-of record fn-arena)))
    (and sub
         (fn-held-p record)
         (equal (fn-record-msgid w)
                (fn-record-octets-string (fn-own-sub-msgid sub)))
         (equal (fn-record-payload w) (fn-own-sub-stored-octets cfg sub (fn-own-node-secret o)))
         t)))

(defun fn-own-finish (o cfg fn-arena)
  (declare (xargs :stobjs fn-arena :guard (fn-sn-statep (fn-own-store o))))
  (cons (if (and (fn-sn-completion-enabledp (fn-own-store o))
                 (fn-own-completion-names-submission-p o cfg fn-arena))
            :durable
          :fault)
        (fn-own-complete o)))

(local
 (defthm fn-own-car-last-of-append-singleton
   (equal (car (last (append l (list x)))) x)))

; Completion touches no connection, no clock and no in-flight slot.  Used
; for P2 below and for P3 through the writer events.
(defthm fn-own-complete-keeps-every-connection
  (and (equal (fn-own-conns (fn-own-complete o)) (fn-own-conns o))
       (equal (fn-own-clock (fn-own-complete o)) (fn-own-clock o))
       (equal (fn-own-inflight (fn-own-complete o)) (fn-own-inflight o)))
  :hints (("Goal" :in-theory (enable fn-own-complete fn-own-refresh-keeps-fields))))

; KEYSTONE (P2, T5's name).  If the reply fn-own-outcome renders for
; connection `id' after the served finish is the 240 line, then:
; fn-sn-finish consumed the store's completion (it was enabled, and the new
; store is fn-sn-finish of the old); exactly one acknowledgement, the
; completion pair, was appended to the store's success list and to the
; ledger; the in-flight submission is connection `id''s; the completed record
; is a held article row, and ALPHA of it through the arena (fn-row-wire-of)
; carries that submission's Message-ID and, as its payload, the octets the
; owner staged for it under CFG (fn-own-sub-stored-octets); and the pair
; names a record in the durable history.
(defthm fn-own-240-follows-consumed-completion
  (let* ((o2 (cdr (fn-own-finish o cfg fn-arena)))
         (word (car (fn-own-finish o cfg fn-arena)))
         (pair (fn-sf-completion (fn-sn-files (fn-own-store o))))
         (record (fn-sn-completion-record (fn-own-store o)))
         (w (fn-row-wire-of record fn-arena))
         (sub (fn-own-inflight o)))
    (implies (and (fn-own-relation o)
                  (equal (car (fn-own-outcome o2 id word))
                         (let ((conn (fn-own-find-conn id (fn-own-conns o2))))
                           (fn-served-result-effects
                            (fn-served-post-outcome
                             (fn-served-make-conn (fn-own-conn-wire conn)
                                                  (fn-own-conn-session conn)
                                                  (fn-own-conn-archive conn)
                                                  (fn-own-conn-config conn)
                                                  (fn-own-conn-observation conn)
                                                  (fn-own-clock o2))
                             :durable)))))
             (and (equal word :durable)
                  sub
                  (equal (fn-own-sub-id sub) id)
                  (fn-sn-completion-enabledp (fn-own-store o))
                  (equal (fn-own-store o2) (fn-sn-finish (fn-own-store o)))
                  (equal (fn-sf-successes (fn-sn-files (fn-own-store o2)))
                         (append (fn-sf-successes (fn-sn-files (fn-own-store o)))
                                 (list pair)))
                  (equal (fn-own-ledger o2) (append (fn-own-ledger o) (list pair)))
                  (equal (fn-own-inflight o2) sub)
                  (fn-held-p record)
                  (equal (fn-record-msgid w)
                         (fn-record-octets-string (fn-own-sub-msgid sub)))
                  (equal (fn-record-payload w)
                         (fn-own-sub-stored-octets cfg sub (fn-own-node-secret o)))
                  (fn-sf-record-has-pairp
                   pair (fn-sf-records (fn-sn-files (fn-own-store o2)))))))
  :rule-classes nil
  :hints (("Goal"
           :cases ((and (fn-sn-completion-enabledp (fn-own-store o))
                        (fn-own-completion-names-submission-p o cfg fn-arena)))
           :use ((:instance fn-own-durable-reply-names-a-durable-record
                            (o (cdr (fn-own-finish o cfg fn-arena)))
                            (word (car (fn-own-finish o cfg fn-arena))))
                 (:instance fn-own-complete-preserves-relation)
                 fn-own-complete-keeps-every-connection
                 (:instance fn-own-complete-ledger-is-exact-pair)
                 (:instance fn-sn-finish-acknowledges-exact-pair
                            (s (fn-own-store o))))
           :in-theory (e/d (fn-own-finish fn-own-completion-names-submission-p)
                           (fn-own-sub-stored-octets fn-row-wire-of
                            fn-own-complete fn-own-relation fn-own-outcome
                            fn-served-post-outcome fn-sn-finish
                            fn-sn-completion-enabledp fn-sn-completion-record
                            fn-own-complete-preserves-relation
                            fn-own-complete-ledger-is-exact-pair
                            fn-sn-finish-acknowledges-exact-pair)))))

; -----------------------------------------------------------------------------
; P3 (T6).  A reader pinned before another connection's POST keeps its view.
;
; The host's POST path is the writer events through fn-owner-step
; (fn-ocfg-step): (:take), (:begin id), (:store e) and (:complete); the
; prepare call fn-opc-prepare equals the (:store (:prepare record)) event
; under the relation (fn-opc-prepare-equals-owner-event-under-relation).  The
; outcome is fn-own-outcome on the core, installed by fn-owner-replace-core,
; which is fn-ocfg-with-owner.  A read is fn-ocfg-read-tls-prefix.
(defun fn-ocfg-writer-eventp (event)
  (declare (xargs :guard t))
  (and (consp event)
       (member-equal (car event) '(:take :begin :store :complete))
       t))

(defun fn-ocfg-writer-eventsp (events)
  (declare (xargs :guard t))
  (if (consp events)
      (and (fn-ocfg-writer-eventp (car events))
           (fn-ocfg-writer-eventsp (cdr events)))
    t))

(defthm fn-own-writer-step-keeps-every-connection
  (implies (fn-ocfg-writer-eventp event)
           (and (equal (fn-own-conns (fn-own-step o event fn-arena)) (fn-own-conns o))
                (equal (fn-own-clock (fn-own-step o event fn-arena)) (fn-own-clock o))))
  :hints (("Goal" :in-theory (enable fn-own-step fn-own-take-submission fn-own-begin
                                     fn-own-store-step fn-own-refresh-keeps-fields))))

(defthm fn-ocfg-writer-step-keeps-every-connection
  (implies (fn-ocfg-writer-eventp event)
           (and (equal (fn-own-conns (fn-ocfg-owner (fn-ocfg-step oc event fn-arena)))
                       (fn-own-conns (fn-ocfg-owner oc)))
                (equal (fn-own-clock (fn-ocfg-owner (fn-ocfg-step oc event fn-arena)))
                       (fn-own-clock (fn-ocfg-owner oc)))))
  :hints (("Goal" :in-theory (e/d (fn-ocfg-step fn-ocfg-pass fn-ocfg-complete
                                   fn-ocfg-with-owner)
                                  (fn-own-step fn-own-complete fn-ocfg-open fn-ocfg-read
                                   fn-ocfg-read-step fn-ocfg-fault fn-ocfg-close
                                   fn-ocfg-advance fn-ocfg-open-peer fn-ocfg-reconfigure))
           :use ((:instance fn-own-writer-step-keeps-every-connection
                            (o (fn-ocfg-owner oc)))))))

(defthm fn-ocfg-writer-run-keeps-every-connection
  (implies (fn-ocfg-writer-eventsp events)
           (and (equal (fn-own-conns (fn-ocfg-owner (fn-ocfg-run oc events fn-arena)))
                       (fn-own-conns (fn-ocfg-owner oc)))
                (equal (fn-own-clock (fn-ocfg-owner (fn-ocfg-run oc events fn-arena)))
                       (fn-own-clock (fn-ocfg-owner oc)))))
  :hints (("Goal" :induct (fn-ocfg-run oc events fn-arena)
           :in-theory (e/d (fn-ocfg-run) (fn-ocfg-step fn-ocfg-writer-eventp)))))

(defthm fn-own-outcome-keeps-the-clock
  (equal (fn-own-clock (cdr (fn-own-outcome o id word))) (fn-own-clock o))
  :hints (("Goal" :in-theory (enable fn-own-outcome fn-own-advance fn-own-advance-result
                                     fn-own-set-conns))))

; A reader connection's served chunk reads its own connection record, the
; owner's clock and the owner's committed view (NNT-042, specs/nntp.md: a
; successful GROUP or LISTGROUP in the chunk acquires that view; books/served
; fn-served-repin), nothing else.  A peer connection also reads the live node
; (fn-own-conn-live-session): its offers answer from the store as it is now,
; deliberately, so it is outside this statement.
(defthm fn-own-reader-tls-read-depends-only-on-its-connection-clock-and-view
  (implies (and (equal (fn-own-find-conn id (fn-own-conns o2))
                       (fn-own-find-conn id (fn-own-conns o)))
                (equal (fn-own-clock o2) (fn-own-clock o))
                (equal (fn-own-view o2) (fn-own-view o))
                (not (fn-peer-session-cfg
                      (fn-auth-session-base
                       (fn-own-conn-session (fn-own-find-conn id (fn-own-conns o)))))))
           (and (equal (fn-own-tls-result-effects (fn-own-read-tls-prefix o2 id octets fn-arena))
                       (fn-own-tls-result-effects (fn-own-read-tls-prefix o id octets fn-arena)))
                (equal (fn-own-tls-result-consumed (fn-own-read-tls-prefix o2 id octets fn-arena))
                       (fn-own-tls-result-consumed (fn-own-read-tls-prefix o id octets fn-arena)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-own-read-tls-prefix fn-own-finish-read
                                   fn-own-conn-live-session fn-own-tls-served-conn
                                   fn-own-served-conn
                                   fn-own-tls-make-result fn-own-tls-result-effects
                                   fn-own-tls-result-consumed)
                                  (fn-served-step-counted-fast fn-own-conn-boundedp
                                   fn-own-conn-make-group-indexed fn-own-set-conns
                                   fn-own-enqueue fn-own-view-live)))))

; One framed event that is not a selection (fn-served-advance-eventp: a GROUP
; or LISTGROUP line) is answered from the connection's own pin: the committed
; view is not read (books/served.lisp fn-served-dispatch-without-advance-is-
; core), so two owners with the same connection record and clock answer it
; identically whatever their views.  fn-ocfg-read-step is the host's per-event
; read (host/owner-host.lisp fn-owner-read-step).
(defthm fn-ocfg-read-step-without-selection-depends-only-on-its-connection-and-clock
  (implies (and (equal (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc2)))
                       (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc))))
                (equal (fn-own-clock (fn-ocfg-owner oc2))
                       (fn-own-clock (fn-ocfg-owner oc)))
                (not (fn-served-advance-eventp event)))
           (equal (car (fn-ocfg-read-step oc2 id event fn-arena))
                  (car (fn-ocfg-read-step oc id event fn-arena))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (fn-ocfg-read-step fn-own-read-step-full fn-own-served-conn
                            fn-served-dispatch-core)
                           (fn-served-dispatch fn-own-conn-boundedp
                            fn-own-conn-make-group-indexed fn-own-set-conns
                            fn-own-enqueue fn-own-remove-conn fn-own-replace-conn
                            fn-served-advance-eventp fn-own-view-live
                            fn-ocfg-with-read-owner
                            fn-auth-step-pinned fn-post-offeredp
                            fn-wire-begin-article-with-line-limit
                            fn-wire-article-line-limit))
           :use ((:instance fn-served-dispatch-without-advance-is-core
                            (conn (fn-own-served-conn
                                   (fn-ocfg-owner oc2)
                                   (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc2)))
                                   (fn-own-conn-session
                                    (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc2)))))))
                 (:instance fn-served-dispatch-without-advance-is-core
                            (conn (fn-own-served-conn
                                   (fn-ocfg-owner oc)
                                   (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc)))
                                   (fn-own-conn-session
                                    (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc)))))))))))

; KEYSTONE (P3, the plan's T6; restated under NNT-042 on 2026-09-27).  Over
; the host's own calls: any sequence of writer events through fn-ocfg-step,
; then the outcome for connection `sub-id' installed on the core, leaves every
; other connection's record -- its pinned version and frontier, its session,
; its wire -- exactly what it was, and the clock: another connection's post
; never moves a reader's pin.  Only the reader's own successful GROUP or
; LISTGROUP (the served re-pin, NNT-042), the poster's own 240
; (fn-own-durable-outcome-repins-the-poster) or the control channel's advance
; moves it.  Before NNT-042 this theorem also said the reader's served chunk
; answered as before; a chunk whose GROUP or LISTGROUP succeeds now answers
; from the fresh view BY SPECIFICATION, and the read half holds per framed
; event for every other command (the corollary below); its chunk form (a
; chunk framing no selection answers as before) is stated in the record and
; not yet proved.
(defthm fn-own-pinned-view-survives-other-post
  (implies (and (fn-ocfg-writer-eventsp events)
                (not (equal id sub-id)))
           (let* ((oc1 (fn-ocfg-run oc events fn-arena))
                  (oc2 (fn-ocfg-with-owner
                        oc1 (cdr (fn-own-outcome (fn-ocfg-owner oc1) sub-id word)))))
             (and (equal (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc2)))
                         (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc))))
                  (equal (fn-own-clock (fn-ocfg-owner oc2))
                         (fn-own-clock (fn-ocfg-owner oc))))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-own-outcome-touches-only-its-connection
                            (o (fn-ocfg-owner (fn-ocfg-run oc events fn-arena)))
                            (id sub-id) (other id)))
           :in-theory (e/d (fn-ocfg-with-owner)
                           (fn-own-outcome fn-ocfg-run
                            fn-own-outcome-touches-only-its-connection)))))

; The read half of P3 under NNT-042: after another connection's post, every
; framed event of a reader that is not a selection is answered exactly as
; before (fn-ocfg-read-step, the host's per-event read).
(defthm fn-own-other-post-keeps-a-non-selecting-read-step
  (implies (and (fn-ocfg-writer-eventsp events)
                (not (equal id sub-id))
                (not (fn-served-advance-eventp event)))
           (let* ((oc1 (fn-ocfg-run oc events fn-arena))
                  (oc2 (fn-ocfg-with-owner
                        oc1 (cdr (fn-own-outcome (fn-ocfg-owner oc1) sub-id word)))))
             (equal (car (fn-ocfg-read-step oc2 id event fn-arena))
                    (car (fn-ocfg-read-step oc id event fn-arena)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-own-pinned-view-survives-other-post)
                 (:instance fn-ocfg-read-step-without-selection-depends-only-on-its-connection-and-clock
                            (oc2 (fn-ocfg-with-owner
                                  (fn-ocfg-run oc events fn-arena)
                                  (cdr (fn-own-outcome (fn-ocfg-owner (fn-ocfg-run oc events fn-arena))
                                                       sub-id word))))))
           :in-theory (disable fn-ocfg-read-step fn-ocfg-with-owner fn-ocfg-run
                               fn-own-outcome fn-served-advance-eventp))))

; -----------------------------------------------------------------------------
; P5.  The fault wrapper and the session bound, over the host's calls.

; fn-owner-fault (owner-host.lisp:1273) calls fn-ocfg-fault; this is its
; equation to owner-fault's fn-own-fault, so K-FAULT-1..6 hold of the owner
; the host installs.
(defthm fn-ocfg-fault-is-own-fault
  (and (equal (car (fn-ocfg-fault oc id))
              (car (fn-own-fault (fn-ocfg-owner oc) id)))
       (equal (fn-ocfg-owner (cdr (fn-ocfg-fault oc id)))
              (cdr (fn-own-fault (fn-ocfg-owner oc) id)))
       (equal (fn-ocfg-config (cdr (fn-ocfg-fault oc id)))
              (fn-ocfg-config oc))
       (equal (fn-ocfg-staged (cdr (fn-ocfg-fault oc id)))
              (fn-ocfg-staged oc)))
  :hints (("Goal" :in-theory (e/d (fn-ocfg-fault) (fn-own-fault)))))

; K-FAULT-2 over the wrapper: every other connection, and its configuration
; pin, is what it was.
(defthm fn-ocfg-fault-keeps-every-other-connection
  (implies (not (equal other id))
           (and (equal (fn-own-find-conn
                        other (fn-own-conns (fn-ocfg-owner (cdr (fn-ocfg-fault oc id)))))
                       (fn-own-find-conn other (fn-own-conns (fn-ocfg-owner oc))))
                (equal (fn-ocfg-pin-find other (fn-ocfg-pins (cdr (fn-ocfg-fault oc id))))
                       (fn-ocfg-pin-find other (fn-ocfg-pins oc)))))
  :hints (("Goal" :in-theory (e/d (fn-ocfg-fault fn-ocfg-pin-remove fn-ocfg-pin-find)
                                  (fn-own-fault)))))

(defthm fn-own-open-at-the-bound-refuses
  (implies (<= (nfix (fn-own-max-conns o)) (len (fn-own-conns o)))
           (equal (fn-own-open o acfg) (cons nil o)))
  :hints (("Goal" :in-theory (enable fn-own-open))))

(local
 (defthm fn-ocfg-make-of-its-fields
   (implies (fn-ocfg-shapep x)
            (equal (fn-ocfg-make (fn-ocfg-owner x) (fn-ocfg-config x)
                                 (fn-ocfg-pins x) (fn-ocfg-staged x))
                   x))
   :hints (("Goal" :in-theory (enable fn-ocfg-shapep fn-ocfg-make fn-ocfg-owner
                                      fn-ocfg-config fn-ocfg-pins fn-ocfg-staged)
            :expand ((len x) (len (cdr x)) (len (cddr x)) (len (cdddr x))
                     (len (cddddr x)))))))

; KEYSTONE (P5, the bound).  fn-owner-open (owner-host.lisp:1218) calls
; fn-ocfg-open.  At max-conns open connections it answers no effects and
; returns the configured owner unchanged: no connection, no pin, no
; identifier consumed.  The host then closes the socket without a reply.
(defthm fn-ocfg-open-at-the-bound-refuses
  (implies (and (fn-ocfg-statep oc)
                (<= (nfix (fn-own-max-conns (fn-ocfg-owner oc)))
                    (len (fn-own-conns (fn-ocfg-owner oc)))))
           (equal (fn-ocfg-open oc acfg) (cons nil oc)))
  :hints (("Goal" :in-theory (e/d (fn-ocfg-open fn-ocfg-statep)
                                  (fn-own-relation fn-own-open fn-ocfg-make-of-its-fields))
                  :use ((:instance fn-own-relation-has-no-connection-at-next-id
                                   (o (fn-ocfg-owner oc)))
                        (:instance fn-own-open-at-the-bound-refuses
                                   (o (fn-ocfg-owner oc)))
                        (:instance fn-ocfg-make-of-its-fields (x oc))))))

; -----------------------------------------------------------------------------
; The operator's retry (books/owner.lisp fn-own-operator-decision; flip-L8-2).
; The decision reads the octets the store holds for the Message-ID, STORED,
; which the pure step cannot read after the records flip (the acceptance
; article holds a handle).  This entry computes them: the bytes under the
; held handle, read through the arena the host holds (fn-handle-bytes,
; books/store-intern.lisp), or :absent when the node holds no article with
; the Message-ID.  The host passes its value to fn-own-operator-submit-result
; and as the (:operator-submit MSGID GROUPS OCTETS STORED) event's last
; element (host/owner-host.lisp fn-owner-operator-submit; flip-L8-2's request
; to flip-L6).
(defun fn-own-operator-stored-octets (o msgid fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (let ((article (fn-find-article (fn-record-octets-string msgid)
                                  (fn-state-articles
                                   (fn-node-acceptance (fn-sn-node (fn-own-store o)))))))
    (if article
        (fn-handle-bytes (fn-article-payload article) fn-arena)
      :absent)))

; KEYSTONE (the retry at the entry).  When the node holds MSGID's article
; and ALPHA of it (the bytes under its handle through the arena) is the
; injection the operator's octets got under an earlier clock reading FIRST,
; the decision at the owner's current clock, given what this entry reads,
; is that stored injection itself -- not a fresh injection with a new
; Injection-Date, which the store would refuse as a conflict.  The host
; calls fn-own-operator-submit-result / the (:operator-submit ...) event over
; fn-own-operator-stored-octets (flip-L6's wiring).
(defthm fn-own-operator-retry-at-the-entry-is-the-stored-injection
  (let* ((cfg (fn-own-config o))
         (first-d (fn-inj-decide octets cfg first))
         (article (fn-find-article (fn-record-octets-string msgid)
                                   (fn-state-articles
                                    (fn-node-acceptance (fn-sn-node (fn-own-store o)))))))
    (implies (and (fn-inj-injectedp first-d)
                  (equal (fn-inj-decision-msgid first-d) msgid)
                  article
                  (equal (fn-handle-bytes (fn-article-payload article) fn-arena)
                         (fn-inj-decision-octets first-d))
                  (fn-clock-observationp (fn-own-clock o))
                  (fn-clock-has-wall (fn-own-clock o)))
             (equal (fn-own-operator-decision-of
                     o msgid groups octets (fn-own-operator-stored-octets o msgid fn-arena))
                    (fn-inj-make-decision :injected nil msgid groups
                                          (fn-inj-decision-octets first-d)))))
  :hints (("Goal" :in-theory (e/d (fn-own-operator-decision-of fn-own-operator-stored-octets)
                                  (fn-own-operator-decision fn-inj-decide fn-handle-bytes
                                   fn-find-article))
           :use ((:instance fn-own-operator-retry-resubmits-the-stored-injection
                            (cfg (fn-own-config o)) (later (fn-own-clock o))
                            (stored (fn-handle-bytes
                                     (fn-article-payload
                                      (fn-find-article (fn-record-octets-string msgid)
                                                       (fn-state-articles
                                                        (fn-node-acceptance
                                                         (fn-sn-node (fn-own-store o))))))
                                     fn-arena)))))))

(in-theory (disable fn-own-finish fn-own-completion-names-submission-p
                    fn-own-sub-stored-octets fn-own-operator-stored-octets
                    fn-ocfg-writer-eventp))
