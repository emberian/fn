; fn: the open accepts every state a clean stop leaves (lane
; closure-theorems-2, 2026-09-29; PRF-945).  Prefix `fn-clo-'
; (docs/prefixes.md).
;
; Two halves already on dev meet here.  The configured trace model's clean
; stop, `fn-cst-recoverablep' (books/config-store-traces), is what the
; store steps carry (books/config-store-steps: `fn-cstp-relation-*'); its
; replay under the physical fold is :ok (`fn-cstp-recoverable-facts').  The
; open's frontier fold (books/open-frontier, PRF-937) admits every :ok replay
; at the frontier the host computes from the same records
; (`fn-ofr-replay-ok-frontier-admits').  The finalize the host reaches through
; `fn-sco-store-open' (books/store-checkpoint-open; its :logic body is
; `fn-sco-finalize') refuses the history in three ways, :history, :replay and
; :frontier.  Here: at the computed frontier the :frontier arm cannot fire for
; any :ok replay, and on a clean stop the :replay arm cannot fire either; what
; remains is the carried contexts' :identity refusal and the open itself.
;
; A checkpoint C of the history (CONFIGS, EVENTS) is any C whose records are
; EVENTS and whose drained fold is the history's replay; `fn-sco-capture' is
; one (`fn-sco-replay-of-capture'), and the host's extended captures reduce to
; it (`fn-sco-extend-of-capture').
;
; Not proved here (the owed rows, planning/evidence/closure-theorems-2026-09-29.md
; section C): the host's events fold `fn-store-log-next-txid-of-events'
; (host/store-host.lisp, program mode) is `fn-ofr-events-next' -- the config
; half is host-called (PRF-937); until the events half is equated, "the
; frontier the host passes" is `fn-ofr-frontier' by transcription, not by
; theorem.  The :history arm's premise, `fn-sn-observed-historyp' at the
; computed frontier, is derived below from the same premise at the recorded
; frontier (what the trace relation carries): the events fold is above every
; event's txid, so only the uint32 bound on the computed frontier remains.
(in-package "ACL2")
(include-book "config-store-steps")
(include-book "open-frontier")
(include-book "store-checkpoint-open")

;; The tau system is off in this book (lane tau-pass, tools/tau_cost.py).
(local (in-theory (disable (tau-system))))

; The inner construction of the opened state, never unfolded here.
(local (deftheory fn-clo-finalize-inner
         '(fn-sco-records fn-sco-cpr fn-sco-cpr-finish fn-sco-identity
           fn-sco-consumer fn-sco-topic fn-sn-observed-historyp
           fn-replay-result-kind fn-replay-result-node fn-cnode-node
           fn-cnode-statep fn-replay-advance-okp fn-replay-advance-txid
           fn-cnode-config fn-sf-make fn-sn-observed-seed fn-cnode-domain-of
           fn-cfg-capacity fn-cfg-value fn-sn-with-event-index fn-sn-with-topic
           fn-sn-with-consumer fn-cpo-install fn-sn-update-replayed
           fn-stx-index-of-store fn-stx-store fn-cnode-make fn-cp-nth
           fn-stxk-context-kind fn-th-at fn-sn-statep fn-cpr-replay
           fn-ofr-frontier fn-cst-recoverablep)))

; -----------------------------------------------------------------------------
; An :ok replay is a configured node the computed frontier admits.

(defthm fn-clo-ok-replay-admits-the-computed-frontier
  (implies (and (equal (fn-replay-result-kind (fn-cpr-replay configs events)) :ok)
                (natp floor))
           (and (fn-cnode-statep (fn-replay-result-node (fn-cpr-replay configs events)))
                (fn-replay-advance-okp
                 (fn-cnode-node (fn-replay-result-node (fn-cpr-replay configs events)))
                 (fn-ofr-frontier configs events floor))))
  :rule-classes nil
  :hints (("Goal" :use (fn-ofr-replay-ok-frontier-admits fn-cpr-replay-ok-is-configured)
           :in-theory (disable fn-ofr-replay-ok-frontier-admits fn-cpr-replay-ok-is-configured
                               fn-cpr-replay fn-ofr-frontier fn-cnode-statep
                               fn-replay-advance-okp))))

; -----------------------------------------------------------------------------
; At the computed frontier the :frontier arm cannot fire, for any checkpoint
; of any history.  (The open's :frontier answer is reachable only when the
; frontier the host passes is not the fold of its own records.)

(defthm fn-clo-finalize-never-answers-frontier-at-the-computed-frontier
  (implies (and (natp floor)
                (equal (fn-sco-records c) events)
                (equal (fn-sco-cpr-finish (fn-sco-cpr c) configs)
                       (fn-cpr-replay configs events)))
           (not (equal (fn-sco-finalize c configs (fn-ofr-frontier configs events floor))
                       (fn-sn-open-error :frontier))))
  :hints (("Goal" :use fn-clo-ok-replay-admits-the-computed-frontier
           :in-theory (e/d (fn-sco-finalize fn-sn-open-error fn-sn-open-ok)
                           (fn-clo-finalize-inner)))))

; -----------------------------------------------------------------------------
; A clean stop replays :ok (the configured model's fact, cited).

(defthm fn-clo-clean-stop-replays-ok-unfolds
  (implies (fn-cst-recoverablep configs events frontier)
           (equal (fn-replay-result-kind (fn-cpr-replay configs events)) :ok))
  :hints (("Goal" :use fn-cstp-recoverable-facts
           :in-theory (disable fn-cst-recoverablep fn-cpr-replay
                               fn-cstp-fold fn-cstp-idlep fn-cnode-statep
                               fn-replay-advance-okp fn-replay-advance-txid
                               fn-cst-replay-node fn-cstp-configs-at-most))))

; -----------------------------------------------------------------------------
; KEYSTONE.  On a clean stop, at the computed frontier, the finalize refuses
; the history in none of its three ways: its answer is the open, or the
; carried contexts' :identity refusal.

(defthm fn-clo-clean-stop-is-accepted-or-identity
  (implies (and (fn-cst-recoverablep configs events frontier)
                (natp floor)
                (consp configs)
                (fn-sn-observed-historyp (fn-ofr-frontier configs events floor) events)
                (equal (fn-sco-records c) events)
                (equal (fn-sco-cpr-finish (fn-sco-cpr c) configs)
                       (fn-cpr-replay configs events)))
           (let ((answer (fn-sco-finalize c configs (fn-ofr-frontier configs events floor))))
             (or (equal (fn-sn-open-kind answer) :ok)
                 (equal answer (fn-sn-open-error :identity)))))
  :rule-classes nil
  :hints (("Goal" :use (fn-clo-ok-replay-admits-the-computed-frontier
                        fn-clo-clean-stop-replays-ok-unfolds)
           :in-theory (e/d (fn-sco-finalize fn-sn-open-error fn-sn-open-ok fn-sn-open-kind)
                           (fn-clo-finalize-inner fn-clo-clean-stop-replays-ok-unfolds)))))

; The same, of the capture of the history: the checkpoint the host's extended
; captures reduce to.

(local (defthm fn-clo-true-list-fix-when-true-listp
         (implies (true-listp x) (equal (true-list-fix x) x))))

(local (defthm fn-clo-records-of-capture
         (implies (true-listp events)
                  (equal (fn-sco-records (fn-sco-capture configs events)) events))
         :hints (("Goal" :in-theory (union-theories
                                     (theory 'minimal-theory)
                                     '(fn-sco-capture fn-sco-make fn-sco-records fn-sco-at
                                       nth car-cons cdr-cons nfix natp fix zp
                                       fn-clo-true-list-fix-when-true-listp
                                       (:executable-counterpart equal)
                                       (:executable-counterpart natp)
                                       (:executable-counterpart zp)
                                       (:executable-counterpart nfix)
                                       (:executable-counterpart binary-+)
                                       (:executable-counterpart unary--)))))))

(defthm fn-clo-capture-of-clean-stop-is-accepted-or-identity
  (implies (and (true-listp events)
                (fn-cst-recoverablep configs events frontier)
                (natp floor)
                (consp configs)
                (fn-sn-observed-historyp (fn-ofr-frontier configs events floor) events))
           (let ((answer (fn-sco-finalize (fn-sco-capture configs events) configs
                                          (fn-ofr-frontier configs events floor))))
             (or (equal (fn-sn-open-kind answer) :ok)
                 (equal answer (fn-sn-open-error :identity)))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-clo-clean-stop-is-accepted-or-identity
                                   (c (fn-sco-capture configs events)))
                        (:instance fn-sco-replay-of-capture (records events))
                        fn-clo-records-of-capture)
           :in-theory (theory 'minimal-theory))))

; And of the host's call: fn-sco-store-open's second value is that finalize.

(defthm fn-clo-store-open-of-clean-stop-is-accepted-or-identity
  (implies (and (true-listp events)
                (fn-cst-recoverablep configs events frontier)
                (natp floor)
                (consp configs)
                (fn-sn-observed-historyp (fn-ofr-frontier configs events floor) events))
           (let ((answer (cadr (fn-sco-store-open (fn-sco-capture configs events) configs
                                                  (fn-ofr-frontier configs events floor)))))
             (or (equal (fn-sn-open-kind answer) :ok)
                 (equal answer (fn-sn-open-error :identity)))))
  :rule-classes nil
  :hints (("Goal" :use fn-clo-capture-of-clean-stop-is-accepted-or-identity
           :in-theory (e/d (fn-sco-store-open)
                           (fn-clo-finalize-inner fn-sco-finalize fn-sn-open-kind
                            fn-sn-open-error fn-sco-capture)))))

; -----------------------------------------------------------------------------
; The :history arm at the computed frontier.  An observed history below the
; recorded frontier is observed below the computed one: the frontier enters
; `fn-sf-record-listp' only as the bound `(< txid frontier)', and the events
; fold is above every event's txid.

(defthm fn-clo-record-listp-later
  (implies (and (fn-sf-record-listp records sequence lower f) (<= f g))
           (fn-sf-record-listp records sequence lower g))
  :hints (("Goal" :induct (fn-sf-record-listp records sequence lower f)
           :in-theory (e/d (fn-sf-record-listp)
                           (fn-store-event-p fn-store-event-sequence fn-store-event-txid
                            fn-store-event-generation)))))
(defthm fn-clo-record-listp-true-listp
  (implies (fn-sf-record-listp records sequence lower f) (true-listp records))
  :rule-classes nil
  :hints (("Goal" :induct (fn-sf-record-listp records sequence lower f)
           :in-theory (e/d (fn-sf-record-listp)
                           (fn-store-event-p fn-store-event-sequence fn-store-event-txid
                            fn-store-event-generation)))))
(local (defun fn-clo-ind (records sequence lower acc)
         (declare (xargs :measure (len records)))
         (if (consp records)
             (fn-clo-ind (cdr records) (1+ sequence) (1+ (fn-store-event-txid (car records)))
                         (let ((txid (fn-store-event-txid (car records))))
                           (if (natp txid) (max (nfix acc) (+ 1 txid)) (nfix acc))))
           (list sequence lower acc))))
(defthm fn-clo-record-listp-below-events-next
  (implies (fn-sf-record-listp records sequence lower f)
           (fn-sf-record-listp records sequence lower (fn-ofr-events-next records acc)))
  :hints (("Goal" :induct (fn-clo-ind records sequence lower acc)
           :in-theory (e/d (fn-sf-record-listp fn-ofr-events-next)
                           (fn-store-event-p fn-store-event-sequence fn-store-event-txid
                            fn-store-event-generation fn-ofr-events-next-of-cons)))))
(defthm fn-clo-observed-at-the-computed-frontier
  (implies (and (fn-sn-observed-historyp f events)
                (fn-record-uint32p (fn-ofr-frontier configs events floor)))
           (fn-sn-observed-historyp (fn-ofr-frontier configs events floor) events))
  :hints (("Goal" :use ((:instance fn-clo-record-listp-below-events-next
                                   (records events) (sequence 0) (lower 0) (acc floor))
                        (:instance fn-clo-record-listp-later
                                   (records events) (sequence 0) (lower 0)
                                   (f (fn-ofr-events-next events floor))
                                   (g (fn-ofr-frontier configs events floor))))
           :in-theory (e/d (fn-sn-observed-historyp fn-ofr-frontier)
                           (fn-sf-record-listp fn-ofr-events-next fn-ofr-configs-next
                            fn-clo-record-listp-below-events-next fn-clo-record-listp-later
                            fn-record-uint32p)))))

; -----------------------------------------------------------------------------
; The keystone with the recorded frontier's premises only, and of the state
; the trace relation describes (books/config-store-traces `fn-cst-relation':
; what the store steps carry): its history opens, or is refused :identity.

(defthm fn-clo-observed-history-true-listp
  (implies (fn-sn-observed-historyp f events) (true-listp events))
  :rule-classes nil
  :hints (("Goal" :use (:instance fn-clo-record-listp-true-listp
                                  (records events) (sequence 0) (lower 0))
           :in-theory (e/d (fn-sn-observed-historyp) (fn-sf-record-listp fn-record-uint32p)))))
(defthm fn-clo-capture-of-clean-stop-opens-or-identity
  (implies (and (fn-cst-recoverablep configs events frontier)
                (fn-sn-observed-historyp frontier events)
                (natp floor)
                (consp configs)
                (fn-record-uint32p (fn-ofr-frontier configs events floor)))
           (let ((answer (cadr (fn-sco-store-open (fn-sco-capture configs events) configs
                                                  (fn-ofr-frontier configs events floor)))))
             (or (equal (fn-sn-open-kind answer) :ok)
                 (equal answer (fn-sn-open-error :identity)))))
  :rule-classes nil
  :hints (("Goal" :use (fn-clo-store-open-of-clean-stop-is-accepted-or-identity
                        (:instance fn-clo-observed-at-the-computed-frontier (f frontier))
                        (:instance fn-clo-observed-history-true-listp (f frontier)))
           :in-theory (disable fn-clo-finalize-inner fn-sco-store-open fn-sco-capture
                               fn-sn-open-kind fn-sn-open-error fn-sf-record-listp
                               fn-record-uint32p fn-clo-observed-at-the-computed-frontier
                               fn-clo-record-listp-later fn-clo-record-listp-below-events-next))))
(defthm fn-clo-relation-state-opens-or-identity
  (implies (and (fn-cst-relation st)
                (natp floor)
                (consp (fn-sn-config-history st))
                (fn-record-uint32p (fn-ofr-frontier (fn-sn-config-history st)
                                                    (fn-sf-records (fn-sn-files st)) floor)))
           (let* ((configs (fn-sn-config-history st))
                  (events (fn-sf-records (fn-sn-files st)))
                  (answer (cadr (fn-sco-store-open (fn-sco-capture configs events) configs
                                                   (fn-ofr-frontier configs events floor)))))
             (or (equal (fn-sn-open-kind answer) :ok)
                 (equal answer (fn-sn-open-error :identity)))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-clo-capture-of-clean-stop-opens-or-identity
                                   (configs (fn-sn-config-history st))
                                   (events (fn-sf-records (fn-sn-files st)))
                                   (frontier (fn-sf-frontier (fn-sn-files st)))))
           :in-theory (union-theories (theory 'minimal-theory) '(fn-cst-relation)))))
