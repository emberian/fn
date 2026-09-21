; What the reopened image answers about one work, and where a work recovered
; from a cut parts from one this session enqueued.
;
; host/workflow-host.lisp:9 (fn-workflow-install-replay) installs the image
; fn-bp-replay-journal computes and records the work ids it holds;
; host/workflow-host.lisp:65 (fn-workflow-work-status) calls fn-bp-work-status
; on that image's works; host/workflow-host.lisp:71
; (fn-workflow-work-origin) calls fn-bp-work-origin on the same works with the
; recorded id list.  Every theorem here is about one of those three functions,
; so the host computes nothing about a work that ACL2 has not decided.
;
; The four-node lab read `absent` for every work id in a replayed history and
; stopped there.  The cause was fn-workflow-work-status projecting only the
; attempt status, and the fix (fn-bp-work-status, bp-workflow-records.lisp)
; landed with no theorem: this book supplies them.
(in-package "ACL2")
(include-book "bp-workflow-records-invariants")

; bp-workflow-records-invariants exports its lemmas but closes none of the
; workflow vocabulary -- its own disables are local -- so an includer inherits
; every recognizer and every accessor ENABLED.  Reasoning about fn-bp-statep
; with fn-bp-statep open is the fan this project has measured four times, so
; close the vocabulary here first and open exactly what each proof needs.
(local (in-theory (disable
 fn-bp-nth
 fn-bp-config-schema fn-bp-config-local-eid fn-bp-config-peer-eid
 fn-bp-config-policy-id fn-bp-config-authority fn-bp-config-lifetime
 fn-bp-config-incarnation fn-bp-config-auth-context fn-bp-make-config
 fn-bp-configp
 fn-bp-attempt-id fn-bp-attempt-generation fn-bp-attempt-status
 fn-bp-attempt-lifetime fn-bp-transport-statusp fn-bp-retryable-statusp
 fn-bp-make-attempt fn-bp-attemptp
 fn-bp-receipt-id fn-bp-receipt-work-id fn-bp-receipt-subject
 fn-bp-receipt-issuer fn-bp-receipt-peer-eid fn-bp-receipt-policy-id
 fn-bp-receipt-incarnation fn-bp-receipt-auth-context fn-bp-receipt-terms-id
 fn-bp-make-receipt fn-bp-receiptp fn-bp-receipt-listp
 fn-bp-work-id fn-bp-work-msgid fn-bp-work-subject fn-bp-work-archive-id
 fn-bp-work-obligation-id fn-bp-work-peer-eid fn-bp-work-policy-id
 fn-bp-work-incarnation fn-bp-work-auth-context fn-bp-work-terms-id
 fn-bp-work-next-generation fn-bp-work-attempt fn-bp-work-receipt
 fn-bp-make-work fn-bp-workp fn-bp-work-listp fn-bp-find-work
 fn-bp-find-work-by-msgid fn-bp-replace-work fn-bp-work-outstandingp
 fn-bp-work-retryablep fn-bp-authorized-receiptp fn-bp-work-with-attempt
 fn-bp-work-with-receipt fn-bp-work-with-status
 fn-bp-pending-kind fn-bp-pending-txid fn-bp-pending-generation
 fn-bp-pending-work fn-bp-pending-receipt fn-bp-make-pending fn-bp-pendingp
 fn-bp-make-tx-key fn-bp-tx-keyp fn-bp-tx-key-listp
 fn-bp-state-node fn-bp-state-config fn-bp-state-works fn-bp-state-receipts
 fn-bp-state-pending fn-bp-state-fenced fn-bp-state-used-txs
 fn-bp-make-state fn-bp-statep fn-bp-initial-state fn-bp-pending-matchesp
 fn-bp-work-boundp fn-bp-works-boundp
 fn-bp-prepare-enqueue fn-bp-prepare-attempt fn-bp-prepare-receipt
 fn-bp-apply-pending fn-bp-effect-for-pending fn-bp-make-result
 fn-bp-result-state fn-bp-result-effects fn-bp-complete
 fn-bp-recovery-pending fn-bp-recover fn-bp-transport-transition-okp
 fn-bp-live-statusp fn-bp-status-rank fn-bp-observe-transport
 fn-bp-request-retry fn-bp-restart-work fn-bp-restart-works fn-bp-restart
 fn-bp-event-kind fn-bp-enqueue-prepare-event fn-bp-attempt-prepare-event
 fn-bp-receipt-prepare-event fn-bp-storage-complete-event
 fn-bp-storage-recover-event fn-bp-transport-event fn-bp-no-contact-event
 fn-bp-retry-request-event fn-bp-restart-event fn-bp-eventp
 fn-bp-step fn-bp-trace fn-bp-binding-statep fn-bp-pending-boundp
 fn-bp-journal-textp fn-bp-u64p fn-bp-journal-nth fn-bp-config-recordp
 fn-bp-config-from-record fn-bp-journal-recordp fn-bp-record-event
 fn-bp-record-contextp fn-bp-apply-journal-record fn-bp-replay-records
 fn-bp-replay-journal fn-bp-record-live-event fn-bp-record-fence-events
 fn-bp-record-events fn-bp-journal-events fn-bp-journal-denotation
 fn-bp-work-status fn-bp-work-status-after-restart fn-bp-work-ids
 fn-bp-work-origin)))
(set-prover-step-limit 3000000)

; -----------------------------------------------------------------------------
; One work's answer, and what the restart transition does to it

; fn-bp-work-status reads exactly the work fn-bp-find-work returns, so every
; proof below is about one work and the id lookup is carried by this rewrite.
(local
(defun fn-bp-rs-status (work)
  (declare (xargs :guard t))
  (cond ((not (consp work)) :absent)
        ((not (fn-bp-work-outstandingp work)) :receipted)
        ((consp (fn-bp-work-attempt work)) (fn-bp-attempt-status
                                            (fn-bp-work-attempt work)))
        (t :outstanding))))

(local
(defthm fn-bp-rs-work-status-is-rs-status
  (equal (fn-bp-work-status id works)
         (fn-bp-rs-status (fn-bp-find-work id works)))
  :hints (("Goal" :in-theory (enable fn-bp-work-status)))))

(local
(defthm fn-bp-rs-work-id-of-with-status
  (equal (fn-bp-work-id (fn-bp-work-with-status w st)) (fn-bp-work-id w))
  :hints (("Goal" :in-theory (enable fn-bp-work-with-status
                                     fn-bp-work-with-attempt fn-bp-make-work
                                     fn-bp-work-id)))))

(local
(defthm fn-bp-rs-work-id-of-restart-work
  (equal (fn-bp-work-id (fn-bp-restart-work w)) (fn-bp-work-id w))
  :hints (("Goal" :in-theory (enable fn-bp-restart-work)))))

; The lookup commutes with the restart map, including the not-found case:
; fn-bp-restart-work of NIL is NIL, because NIL carries no attempt.
(local
(defthm fn-bp-rs-find-work-of-restart-works
  (equal (fn-bp-find-work id (fn-bp-restart-works works))
         (fn-bp-restart-work (fn-bp-find-work id works)))
  :hints (("Goal" :induct (fn-bp-find-work id works)
           :in-theory (enable fn-bp-find-work fn-bp-restart-works))
          ("Subgoal *1/3" :in-theory (enable fn-bp-find-work
                                             fn-bp-restart-works
                                             fn-bp-restart-work
                                             fn-bp-work-attempt fn-bp-nth)))))

(local
(defthm fn-bp-rs-work-receipt-of-with-status
  (equal (fn-bp-work-receipt (fn-bp-work-with-status w st))
         (fn-bp-work-receipt w))
  :hints (("Goal" :in-theory (enable fn-bp-work-with-status
                                     fn-bp-work-with-attempt fn-bp-make-work
                                     fn-bp-work-receipt)))))

(local
(defthm fn-bp-rs-work-attempt-of-with-status
  (equal (fn-bp-work-attempt (fn-bp-work-with-status w st))
         (fn-bp-make-attempt (fn-bp-attempt-id (fn-bp-work-attempt w))
                             (fn-bp-attempt-generation (fn-bp-work-attempt w))
                             st
                             (fn-bp-attempt-lifetime (fn-bp-work-attempt w))))
  :hints (("Goal" :in-theory (enable fn-bp-work-with-status
                                     fn-bp-work-with-attempt fn-bp-make-work
                                     fn-bp-work-attempt)))))

(local
(defthm fn-bp-rs-attempt-status-of-make-attempt
  (equal (fn-bp-attempt-status (fn-bp-make-attempt a b st c)) st)
  :hints (("Goal" :in-theory (enable fn-bp-make-attempt
                                     fn-bp-attempt-status)))))

(local
(defthm fn-bp-rs-make-attempt-is-consp
  (consp (fn-bp-make-attempt a b c d))
  :hints (("Goal" :in-theory (enable fn-bp-make-attempt)))))

(local
(defthm fn-bp-rs-work-with-status-is-consp
  (consp (fn-bp-work-with-status w st))
  :hints (("Goal" :in-theory (enable fn-bp-work-with-status
                                     fn-bp-work-with-attempt
                                     fn-bp-make-work)))))

; An attempt of a well-formed work carries a transport status, which is what
; separates the three non-attempt answers from every attempt answer.
(local
(defthm fn-bp-rs-attemptp-status-is-transport
  (implies (fn-bp-attemptp a) (fn-bp-transport-statusp (fn-bp-attempt-status a)))
  :hints (("Goal" :in-theory (enable fn-bp-attemptp)))))

(local
(defthm fn-bp-rs-workp-attempt-status-is-transport
  (implies (and (fn-bp-workp config w) (consp (fn-bp-work-attempt w)))
           (fn-bp-transport-statusp (fn-bp-attempt-status (fn-bp-work-attempt w))))
  :hints (("Goal" :in-theory (enable fn-bp-workp)))))

(local
(defthm fn-bp-rs-workp-of-find-work
  (implies (and (fn-bp-work-listp config works)
                (consp (fn-bp-find-work id works)))
           (fn-bp-workp config (fn-bp-find-work id works)))
  :hints (("Goal" :induct (fn-bp-find-work id works)
           :in-theory (enable fn-bp-find-work fn-bp-work-listp)))))

; An atom carries no attempt, so a work with one is a cons.
(local
(defthm fn-bp-rs-work-attempt-of-atom
  (implies (not (consp w)) (equal (fn-bp-work-attempt w) nil))
  :hints (("Goal" :in-theory (enable fn-bp-work-attempt)))))

; The one-work fact.  The hypothesis is only that an attempt, if there is one,
; carries a transport status: without it a work could carry the literal
; :outstanding as its attempt status and the two sides would part.
(local
(defthm fn-bp-rs-status-of-restart-work
  (implies (or (not (consp (fn-bp-work-attempt w)))
               (fn-bp-transport-statusp (fn-bp-attempt-status
                                         (fn-bp-work-attempt w))))
           (equal (fn-bp-rs-status (fn-bp-restart-work w))
                  (fn-bp-work-status-after-restart (fn-bp-rs-status w))))
  :hints (("Goal" :in-theory (enable fn-bp-restart-work
                                     fn-bp-work-status-after-restart
                                     fn-bp-work-outstandingp
                                     fn-bp-transport-statusp
                                     fn-bp-retryable-statusp)))))

(local
(defthm fn-bp-rs-state-works-of-restart
  (implies (fn-bp-statep s)
           (equal (fn-bp-state-works (fn-bp-restart s))
                  (fn-bp-restart-works (fn-bp-state-works s))))
  :hints (("Goal" :in-theory (enable fn-bp-restart fn-bp-make-state
                                     fn-bp-state-works fn-bp-nth)))))

(local
(defthm fn-bp-rs-statep-work-listp
  (implies (fn-bp-statep s)
           (fn-bp-work-listp (fn-bp-state-config s) (fn-bp-state-works s)))
  :hints (("Goal" :in-theory (enable fn-bp-statep)))))

; KEYSTONE.  The restart transition a reopen runs changes the boundary answer
; in exactly one way: an attempt that was in flight is marked
; :restart-observed.  :absent, :outstanding and :receipted are fixed points,
; so a reopen can neither lose a work, nor invent one, nor reopen a receipted
; one.  fn-bp-work-status-after-restart is the whole difference.
(defthm fn-bp-work-status-of-restart
  (implies (fn-bp-statep s)
           (equal (fn-bp-work-status id (fn-bp-state-works (fn-bp-restart s)))
                  (fn-bp-work-status-after-restart
                   (fn-bp-work-status id (fn-bp-state-works s)))))
  :hints (("Goal"
           :use ((:instance fn-bp-rs-status-of-restart-work
                            (w (fn-bp-find-work id (fn-bp-state-works s))))
                 (:instance fn-bp-rs-workp-of-find-work
                            (config (fn-bp-state-config s))
                            (works (fn-bp-state-works s)))
                 (:instance fn-bp-rs-workp-attempt-status-is-transport
                            (config (fn-bp-state-config s))
                            (w (fn-bp-find-work id (fn-bp-state-works s)))))
           :in-theory (disable fn-bp-rs-status-of-restart-work
                               fn-bp-rs-workp-of-find-work
                               fn-bp-rs-workp-attempt-status-is-transport))))

; -----------------------------------------------------------------------------
; The replayed image against the machine that never died

; fn-bp-journal-events ends in the restart fn-bp-replay-records appends.  Its
; prefix is what the pre-crash machine ran: the durable records' own events,
; each recovery outcome still preceded by the :indeterminate fence the crash
; implied.
(defun fn-bp-durable-events (records)
  (declare (xargs :guard t :verify-guards nil))
  (if (atom records)
      nil
    (append (fn-bp-record-events (car records))
            (fn-bp-durable-events (cdr records)))))
(local (in-theory (disable fn-bp-durable-events)))

(local
(defthm fn-bp-rs-append-assoc
  (equal (append (append x y) z) (append x (append y z)))))

(defthm fn-bp-journal-events-is-durable-events-then-restart
  (equal (fn-bp-journal-events records)
         (append (fn-bp-durable-events records) (list (fn-bp-restart-event))))
  :hints (("Goal" :induct (fn-bp-durable-events records)
           :in-theory (enable fn-bp-journal-events fn-bp-durable-events))))

(local
(defthm fn-bp-rs-trace-preserves-statep
  (implies (fn-bp-statep s) (fn-bp-statep (fn-bp-trace s events)))
  :hints (("Goal" :induct (fn-bp-trace s events)
           :in-theory (enable fn-bp-trace)))))

(local
(defthm fn-bp-rs-step-of-restart-event
  (equal (fn-bp-result-state (fn-bp-step s (fn-bp-restart-event)))
         (fn-bp-restart s))
  :hints (("Goal" :in-theory (enable fn-bp-step fn-bp-restart-event
                                     fn-bp-event-kind fn-bp-make-result
                                     fn-bp-result-state fn-bp-nth)))))

; ACL2 evaluates (fn-bp-restart-event) wherever it appears as a ground term,
; so the fact is needed on the evaluated constant as well -- the same trap
; fn-bp-restart-constant-step-emits-nothing records in the book below.
(local
(defthm fn-bp-rs-step-of-restart-constant
  (equal (fn-bp-result-state (fn-bp-step s '(:restart))) (fn-bp-restart s))
  :hints (("Goal" :in-theory (enable fn-bp-step fn-bp-event-kind
                                     fn-bp-make-result fn-bp-result-state
                                     fn-bp-nth)))))

(local
(defthm fn-bp-rs-trace-of-one-restart
  (equal (fn-bp-trace s (list (fn-bp-restart-event))) (fn-bp-restart s))
  :hints (("Goal" :in-theory (enable fn-bp-trace)))))

(local
(defthm fn-bp-rs-trace-of-one-restart-constant
  (equal (fn-bp-trace s '((:restart))) (fn-bp-restart s))
  :hints (("Goal" :in-theory (enable fn-bp-trace)))))

(local
(defthm fn-bp-rs-replay-journal-ok-implies-initial-statep
  (implies (car (fn-bp-replay-journal node records))
           (fn-bp-statep (fn-bp-initial-state
                          node (fn-bp-config-from-record (car records)))))
  :hints (("Goal" :in-theory (enable fn-bp-replay-journal)))))

; KEYSTONE.  A work id in the replayed history reads what the machine that
; never died would have answered for it, marked by the restart and by nothing
; else.  With the previous keystone: a work that machine held reads
; :outstanding or its attempt's restart mark and never :absent, and a work it
; never held reads :absent and never anything else.
(defthm fn-bp-replay-work-status-is-the-pre-crash-status-restarted
  (implies (car (fn-bp-replay-journal node records))
           (equal (fn-bp-work-status
                   id (fn-bp-state-works
                       (fn-bp-journal-nth 1 (fn-bp-replay-journal node records))))
                  (fn-bp-work-status-after-restart
                   (fn-bp-work-status
                    id (fn-bp-state-works
                        (fn-bp-trace
                         (fn-bp-initial-state
                          node (fn-bp-config-from-record (car records)))
                         (fn-bp-durable-events (cdr records))))))))
  :hints (("Goal"
           :use ((:instance fn-bp-work-status-of-restart
                            (s (fn-bp-trace
                                (fn-bp-initial-state
                                 node (fn-bp-config-from-record (car records)))
                                (fn-bp-durable-events (cdr records))))))
           :in-theory (e/d (fn-bp-journal-denotation)
                           (fn-bp-work-status-of-restart)))))

; -----------------------------------------------------------------------------
; Provenance: recovered from a cut, or enqueued after the reopen

(local
(defthm fn-bp-rs-find-work-carries-its-id
  (implies (consp (fn-bp-find-work id works))
           (equal (fn-bp-work-id (fn-bp-find-work id works)) id))
  :hints (("Goal" :induct (fn-bp-find-work id works)
           :in-theory (enable fn-bp-find-work)))))

(local
(defthm fn-bp-rs-member-of-work-ids
  (implies (consp (fn-bp-find-work id works))
           (member-equal id (fn-bp-work-ids works)))
  :hints (("Goal" :induct (fn-bp-find-work id works)
           :in-theory (enable fn-bp-find-work fn-bp-work-ids)))))

; KEYSTONE.  At open, the list the install records is exactly the image's
; works, so every work the reopen recovered reads :recovered and every other
; id reads :absent.  :recovered is therefore never an answer about a work the
; image does not hold.
(defthm fn-bp-work-origin-at-open-is-recovered-or-absent
  (equal (fn-bp-work-origin id (fn-bp-work-ids works) works)
         (if (consp (fn-bp-find-work id works)) :recovered :absent))
  :hints (("Goal" :in-theory (enable fn-bp-work-origin))))

; KEYSTONE.  A work this session enqueues after the reopen reads :enqueued,
; not :recovered -- so the two situations the status word cannot separate are
; separated here.  The subject is fn-bp-complete of an :enqueue pending, which
; is the transition host/workflow-host.lisp:46 (fn-workflow-apply-record)
; performs for the :outcome record of an enqueue.
(defthm fn-bp-durable-enqueue-after-open-reads-enqueued
  (implies (and (fn-bp-pending-matchesp s txid generation)
                (not (fn-bp-state-fenced s))
                (equal (fn-bp-pending-kind (fn-bp-state-pending s)) :enqueue)
                (not (member-equal
                      (fn-bp-work-id (fn-bp-pending-work (fn-bp-state-pending s)))
                      recovered)))
           (equal (fn-bp-work-origin
                   (fn-bp-work-id (fn-bp-pending-work (fn-bp-state-pending s)))
                   recovered
                   (fn-bp-state-works
                    (fn-bp-result-state
                     (fn-bp-complete s txid generation :durable))))
                  :enqueued))
  :hints (("Goal"
           :use ((:instance fn-bp-durable-enqueue-holds-the-work))
           :in-theory (e/d (fn-bp-work-origin)
                           (fn-bp-durable-enqueue-holds-the-work)))))

; Nothing here leaves a rewrite over the workflow vocabulary enabled: the two
; read-model definitions and fn-bp-durable-events stay closed, and the four
; keystones are the book's whole export.
(in-theory (disable fn-bp-work-status-after-restart fn-bp-work-ids
                    fn-bp-work-origin fn-bp-durable-events))
