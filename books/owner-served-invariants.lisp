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
(defun fn-own-sub-stored-octets (cfg sub)
  (declare (xargs :guard t))
  (let ((d (fn-own-sub-decision sub)))
    (if (fn-peer-submissionp d)
        (fn-peer-relayed-octets cfg (fn-peer-submission-peer d)
                                (fn-peer-submission-octets d))
      (fn-inj-decision-octets d))))

;; The two arms, named by definition (they are not keystones).  A local or
;; control submission's staged octets are its own: nothing is prepended, so
;; for served POST the keystone below compares with the submission's octets
;; exactly as before.  A transit submission's are fn-peer-relayed-octets of
;; the received octets, whose Path is the received Path with this node's
;; identity and diagnostic prepended when a Path identity is set
;; (books/peer-inbound-invariants.lisp
;; fn-peer-relayed-octets-keep-the-received-path-tail).
(defthm fn-own-sub-stored-octets-of-a-local-submission-by-definition
  (implies (not (fn-peer-submissionp (fn-own-sub-decision sub)))
           (equal (fn-own-sub-stored-octets cfg sub)
                  (fn-own-sub-octets sub)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-own-sub-stored-octets fn-own-sub-octets))))

(defthm fn-own-sub-stored-octets-of-a-transit-submission-by-definition
  (implies (fn-peer-submissionp (fn-own-sub-decision sub))
           (equal (fn-own-sub-stored-octets cfg sub)
                  (fn-peer-relayed-octets
                   cfg (fn-peer-submission-peer (fn-own-sub-decision sub))
                   (fn-own-sub-octets sub))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-own-sub-stored-octets fn-own-sub-octets))))

(defun fn-own-completion-names-submission-p (o cfg)
  (declare (xargs :guard (fn-sn-statep (fn-own-store o))))
  (let ((sub (fn-own-inflight o))
        (record (fn-sn-completion-record (fn-own-store o))))
    (and sub
         (fn-record-p record)
         (equal (fn-record-msgid record)
                (fn-record-octets-string (fn-own-sub-msgid sub)))
         (equal (fn-record-payload record) (fn-own-sub-stored-octets cfg sub))
         t)))

(defun fn-own-finish (o cfg)
  (declare (xargs :guard (fn-sn-statep (fn-own-store o))))
  (cons (if (and (fn-sn-completion-enabledp (fn-own-store o))
                 (fn-own-completion-names-submission-p o cfg))
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
; is an article record whose Message-ID is that submission's and whose
; payload is the octets the owner staged for it under CFG
; (fn-own-sub-stored-octets); and the pair names a record in the durable
; history.
(defthm fn-own-240-follows-consumed-completion
  (let* ((o2 (cdr (fn-own-finish o cfg)))
         (word (car (fn-own-finish o cfg)))
         (pair (fn-sf-completion (fn-sn-files (fn-own-store o))))
         (record (fn-sn-completion-record (fn-own-store o)))
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
                  (fn-record-p record)
                  (equal (fn-record-msgid record)
                         (fn-record-octets-string (fn-own-sub-msgid sub)))
                  (equal (fn-record-payload record)
                         (fn-own-sub-stored-octets cfg sub))
                  (fn-sf-record-has-pairp
                   pair (fn-sf-records (fn-sn-files (fn-own-store o2)))))))
  :rule-classes nil
  :hints (("Goal"
           :cases ((and (fn-sn-completion-enabledp (fn-own-store o))
                        (fn-own-completion-names-submission-p o cfg)))
           :use ((:instance fn-own-durable-reply-names-a-durable-record
                            (o (cdr (fn-own-finish o cfg)))
                            (word (car (fn-own-finish o cfg))))
                 (:instance fn-own-complete-preserves-relation)
                 fn-own-complete-keeps-every-connection
                 (:instance fn-own-complete-ledger-is-exact-pair)
                 (:instance fn-sn-finish-acknowledges-exact-pair
                            (s (fn-own-store o))))
           :in-theory (e/d (fn-own-finish fn-own-completion-names-submission-p)
                           (fn-own-sub-stored-octets
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
           (and (equal (fn-own-conns (fn-own-step o event)) (fn-own-conns o))
                (equal (fn-own-clock (fn-own-step o event)) (fn-own-clock o))))
  :hints (("Goal" :in-theory (enable fn-own-step fn-own-take-submission fn-own-begin
                                     fn-own-store-step fn-own-refresh-keeps-fields))))

(defthm fn-ocfg-writer-step-keeps-every-connection
  (implies (fn-ocfg-writer-eventp event)
           (and (equal (fn-own-conns (fn-ocfg-owner (fn-ocfg-step oc event)))
                       (fn-own-conns (fn-ocfg-owner oc)))
                (equal (fn-own-clock (fn-ocfg-owner (fn-ocfg-step oc event)))
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
           (and (equal (fn-own-conns (fn-ocfg-owner (fn-ocfg-run oc events)))
                       (fn-own-conns (fn-ocfg-owner oc)))
                (equal (fn-own-clock (fn-ocfg-owner (fn-ocfg-run oc events)))
                       (fn-own-clock (fn-ocfg-owner oc)))))
  :hints (("Goal" :induct (fn-ocfg-run oc events)
           :in-theory (e/d (fn-ocfg-run) (fn-ocfg-step fn-ocfg-writer-eventp)))))

(defthm fn-own-outcome-keeps-the-clock
  (equal (fn-own-clock (cdr (fn-own-outcome o id word))) (fn-own-clock o))
  :hints (("Goal" :in-theory (enable fn-own-outcome fn-own-advance fn-own-advance-result
                                     fn-own-set-conns))))

; A reader connection's served chunk reads its own connection record and the
; owner's clock, nothing else.  A peer connection also reads the live node
; (fn-own-conn-live-session): its offers answer from the store as it is now,
; deliberately, so it is outside this statement.
(defthm fn-own-reader-tls-read-depends-only-on-its-connection-and-clock
  (implies (and (equal (fn-own-find-conn id (fn-own-conns o2))
                       (fn-own-find-conn id (fn-own-conns o)))
                (equal (fn-own-clock o2) (fn-own-clock o))
                (not (fn-peer-session-cfg
                      (fn-auth-session-base
                       (fn-own-conn-session (fn-own-find-conn id (fn-own-conns o)))))))
           (and (equal (fn-own-tls-result-effects (fn-own-read-tls-prefix o2 id octets))
                       (fn-own-tls-result-effects (fn-own-read-tls-prefix o id octets)))
                (equal (fn-own-tls-result-consumed (fn-own-read-tls-prefix o2 id octets))
                       (fn-own-tls-result-consumed (fn-own-read-tls-prefix o id octets)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-own-read-tls-prefix fn-own-finish-read
                                   fn-own-conn-live-session fn-own-tls-served-conn
                                   fn-own-tls-make-result fn-own-tls-result-effects
                                   fn-own-tls-result-consumed)
                                  (fn-served-step-counted-fast fn-own-conn-boundedp
                                   fn-own-conn-make-group-indexed fn-own-set-conns
                                   fn-own-enqueue)))))

; KEYSTONE (P3, the plan's T6).  Over the host's own calls: any sequence of
; writer events through fn-ocfg-step, then the outcome for connection
; `sub-id' installed on the core, leaves every other reader connection's
; served chunk (fn-ocfg-read-tls-prefix, owner-host.lisp:1240) answering
; exactly as it answered before: the same effects and the same consumed
; prefix, for any octets.  With `word' :durable the poster's own connection
; is re-pinned (fn-own-durable-outcome-repins-the-poster); no other is.
(defthm fn-own-pinned-view-survives-other-post
  (implies (and (fn-ocfg-writer-eventsp events)
                (not (equal id sub-id))
                (not (fn-peer-session-cfg
                      (fn-auth-session-base
                       (fn-own-conn-session
                        (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc))))))))
           (let* ((oc1 (fn-ocfg-run oc events))
                  (oc2 (fn-ocfg-with-owner
                        oc1 (cdr (fn-own-outcome (fn-ocfg-owner oc1) sub-id word)))))
             (and (equal (fn-own-tls-result-effects (fn-ocfg-read-tls-prefix oc2 id octets))
                         (fn-own-tls-result-effects (fn-ocfg-read-tls-prefix oc id octets)))
                  (equal (fn-own-tls-result-consumed (fn-ocfg-read-tls-prefix oc2 id octets))
                         (fn-own-tls-result-consumed (fn-ocfg-read-tls-prefix oc id octets))))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-own-reader-tls-read-depends-only-on-its-connection-and-clock
                            (o (fn-ocfg-owner oc))
                            (o2 (cdr (fn-own-outcome (fn-ocfg-owner (fn-ocfg-run oc events))
                                                     sub-id word))))
                 (:instance fn-own-outcome-touches-only-its-connection
                            (o (fn-ocfg-owner (fn-ocfg-run oc events)))
                            (id sub-id) (other id)))
           :in-theory (e/d (fn-ocfg-read-tls-prefix fn-ocfg-with-owner
                            fn-own-tls-make-result fn-own-tls-result-effects
                            fn-own-tls-result-consumed)
                           (fn-own-read-tls-prefix fn-own-outcome fn-ocfg-run
                            fn-own-outcome-touches-only-its-connection)))))

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

(in-theory (disable fn-own-finish fn-own-completion-names-submission-p
                    fn-own-sub-stored-octets
                    fn-ocfg-writer-eventp))
