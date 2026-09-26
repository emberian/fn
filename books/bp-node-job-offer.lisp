; The base job offer: a fair contact selection, a named attempt callback, and
; the status-report effect join (mandate 5.7, spec bp-node-machine 7.6/5.7).
(in-package "ACL2")
(include-book "bp-node-contact-driver")
(include-book "bp-node-progress-premises")
(include-book "bp-node-machine-authorization")
(set-verify-guards-eagerness 0)

(defun fn-bpnj-offerable (job peer routing)
  (declare (xargs :guard t))
  (if (not (equal (fn-bpn-nth 0 routing) :table))
      (list :send nil)
    (let ((decision (fn-bprt-send-decision
                     (fn-bpn-job-route job) (fn-bpaj-eid-text peer)
                     (fn-bpn-nth 1 routing))))
      (cond ((not (equal (fn-bpn-nth 0 decision) :send))
             (list :held (fn-bpn-nth 1 decision)))
            ((not (equal (fn-bpn-nth 1 decision) (fn-bpn-job-route job)))
             (list :held :route-changed))
            (t (list :send (fn-bpn-nth 3 decision)))))))
(defun fn-bpnj-candidatep (job peer offered)
  (declare (xargs :guard t))
  (and (equal (fn-bpn-job-status job) :queued)
       (equal (fn-bpn-job-peer job) peer)
       (not (fn-bpn-member (fn-bpn-job-key job) offered))))
(defun fn-bpnj-readyp (job peer routing offered)
  (declare (xargs :guard t))
  (and (fn-bpnj-candidatep job peer offered)
       (equal (fn-cbor-ag-car (fn-bpnj-offerable job peer routing)) :send)))
(defun fn-bpnj-start-job (base peer key)
  (declare (xargs :guard (fn-bpn-machine-statep base) :verify-guards nil))
  (let ((job (fn-bpn-find-job key (fn-bpn-machine-state-jobs base))))
    (if (or (not job)
            (not (equal (fn-bpn-job-status job) :queued))
            (not (equal (fn-bpn-job-peer job) peer))
            (fn-bpn-machine-state-fenced base)
            (fn-bpn-machine-state-pending base)
            (not (fn-bpn-contact-openp peer (fn-bpn-machine-state-contacts base))))
        (fn-bpn-answer base nil)
      (let* ((token (fn-bpn-machine-state-next-token base))
             (jkey (fn-bpn-job-key job))
             (record (list :attempting token (nth 0 jkey) (nth 1 jkey) (nth 2 jkey))))
        (fn-bpn-propose
         base record
         (list (list :cl-send (fn-bpn-job-route job) peer jkey
                     (fn-bpn-job-wire job)))
         (list :bundle-queue-refused (nth 0 jkey) (nth 1 jkey) (nth 2 jkey)
               :attempt-persistence-refused)
         (list :bundle-queue-uncertain (nth 0 jkey) (nth 1 jkey) (nth 2 jkey)
               :attempt-persistence))))))
(defun fn-bpnj-open-base (base peer)
  (declare (xargs :guard (fn-bpn-machine-statep base) :verify-guards nil))
  (fn-bpn-state-with base (fn-bpn-machine-state-jobs base)
                     (fn-bpn-open-contact peer (fn-bpn-machine-state-contacts base))
                     (fn-bpn-machine-state-pending base)
                     (fn-bpn-machine-state-fenced base)
                     (fn-bpn-machine-state-next-token base)))
; Only the base slot changes: the served state's waits, credit, sessions and
; pending image (fields 11 to 15) are kept, as fn-bpnp-step keeps them on a
; lower machine event.
(defun fn-bpnj-with-base (st base)
  (declare (xargs :guard t))
  (if (true-listp st) (update-nth 1 base st) st))

; (:contact-job PEER KEY): open PEER's contact and propose the :attempting
; record of exactly the queued job KEY names, under the same gate that opens
; a base contact (fn-bpnp-receipt-contact-event: nothing issued, no
; uncertain delivery, the base neither fenced nor pending, a queued job for
; PEER).
(defun fn-bpnj-contact-job-step (st peer key)
  (declare (xargs :guard (fn-bpn-machine-statep (fn-bpnf-base st)) :verify-guards nil))
  (if (not (and (true-listp st) (fn-bpnp-receipt-contact-event st peer)))
      (fn-bpnf-answer st nil)
    (let ((ans (fn-bpnj-start-job (fn-bpnj-open-base (fn-bpnf-base st) peer) peer key)))
      (fn-bpnf-answer (fn-bpnj-with-base st (fn-bpn-answer-state ans))
                      (fn-bpn-answer-effects ans)))))

(defun fn-bpnj-attempt-token (st key)
  (declare (xargs :guard t))
  (let ((job (fn-bpn-find-job key (fn-bpn-machine-state-jobs (fn-bpnf-base st)))))
    (if (and job (equal (fn-bpn-job-status job) :attempting))
        (fn-bpn-job-last-token job)
      nil)))

; The first queued job for PEER, in job-list order, that this contact has not
; offered and whose routing decision sends it on its durable route.  Each
; list position is read through fn-bpn-find-job, the lookup the lower
; machine's start uses, so the job selected is the job started.
(defun fn-bpnj-select (rest jobs peer routing offered)
  (declare (xargs :guard t))
  (if (atom rest)
      nil
    (let ((job (fn-bpn-find-job (fn-bpn-job-key (car rest)) jobs)))
      (if (fn-bpnj-readyp job peer routing offered)
          job
        (fn-bpnj-select (cdr rest) jobs peer routing offered)))))

; The first queued, not yet offered job for PEER that routing holds.
(defun fn-bpnj-held (rest jobs peer routing offered)
  (declare (xargs :guard t))
  (if (atom rest)
      nil
    (let ((job (fn-bpn-find-job (fn-bpn-job-key (car rest)) jobs)))
      (if (and (fn-bpnj-candidatep job peer offered)
               (not (fn-bpnj-readyp job peer routing offered)))
          job
        (fn-bpnj-held (cdr rest) jobs peer routing offered)))))

; The one question the host's contact loop asks before each offer
; (host/native/bp-service.lisp fnn-bpc-drive-contact, and
; host/native/bp-node.lisp fnn-bpnode-send-receipts).  Its answers:
;   (:offer (:contact-job PEER KEY) OFFERED EID)  drive the event through
;        fn-bpnj-step; OFFERED gains KEY; EID is the node ID the hop must
;        announce (nil without routing);
;   (:held KEY DECISION)  nothing is ready; the oldest held job's decision;
;   (:close)  nothing more to offer on this contact.
; A held or already offered job never stops the contact while a younger job
; for the peer is ready (fn-bpnj-contact-offers-while-a-ready-job-remains).
(defun fn-bpnj-contact-next (st peer routing offered)
  (declare (xargs :guard t))
  (let* ((jobs (fn-bpn-machine-state-jobs (fn-bpnf-base st)))
         (job (fn-bpnj-select jobs jobs peer routing offered))
         (held (fn-bpnj-held jobs jobs peer routing offered)))
    (cond ((not (fn-bpnp-receipt-contact-event st peer)) (list :close))
          (job (list :offer
                     (list :contact-job peer (fn-bpn-job-key job))
                     (cons (fn-bpn-job-key job) offered)
                     (fn-bpn-nth 1 (fn-bpnj-offerable job peer routing))))
          (held (list :held (fn-bpn-job-key held)
                      (fn-bpn-nth 1 (fn-bpnj-offerable held peer routing))))
          (t (list :close)))))

(defun fn-bpnj-transfer-outcomep (x)
  (declare (xargs :guard t))
  (fn-bpn-member x '(:accepted :refused :failed :uncertain)))
(defun fn-bpnj-result-step (st key token outcome)
  (declare (xargs :guard (and (fn-bpn-machine-statep (fn-bpnf-base st))
                              (fn-bpnp-session-listp (fn-bpnp-sessions st))
                              (true-listp (fn-bpnf-held-list st)))
                  :verify-guards nil))
  (if (and (natp token) (equal (fn-bpnj-attempt-token st key) token))
      (fn-bpnp-step st (list :base (list :forward-result key outcome)))
    (fn-bpnf-answer st (list (list :job-result-stale key token)))))
(defun fn-bpnj-unnamed-result-p (event)
  (declare (xargs :guard t))
  (and (equal (fn-cbor-ag-car event) :base)
       (equal (fn-cbor-ag-car (fn-bpn-nth 1 event)) :forward-result)))
(defun fn-bpnj-host-eventp (event)
  (declare (xargs :guard t))
  (case (fn-cbor-ag-car event)
    (:contact-job
     (and (true-listp event) (equal (len event) 3)
          (fn-bpp-eidp (fn-bpn-nth 1 event))
          (fn-bpn-keyp (fn-bpn-nth 2 event))))
    (:job-result
     (and (true-listp event) (equal (len event) 4)
          (fn-bpn-keyp (fn-bpn-nth 1 event))
          (natp (fn-bpn-nth 2 event))
          (fn-bpnj-transfer-outcomep (fn-bpn-nth 3 event))))
    (otherwise (and (not (fn-bpnj-unnamed-result-p event))
                    (fn-bpnp-host-eventp event)))))
(defun fn-bpnj-step (st event)
  (declare (xargs :guard (and (fn-bpn-machine-statep (fn-bpnf-base st))
                              (fn-bpnp-session-listp (fn-bpnp-sessions st))
                              (true-listp (fn-bpnf-held-list st))
                              (fn-bpnj-host-eventp event))
                  :verify-guards nil))
  (cond
   ((equal (fn-cbor-ag-car event) :contact-job)
    (fn-bpnj-contact-job-step st (fn-bpn-nth 1 event) (fn-bpn-nth 2 event)))
   ((equal (fn-cbor-ag-car event) :job-result)
    (fn-bpnj-result-step st (fn-bpn-nth 1 event) (fn-bpn-nth 2 event)
                         (fn-bpn-nth 3 event)))
   ((fn-bpnj-unnamed-result-p event)
    (fn-bpnf-answer st (list (list :job-result-unnamed
                                   (fn-bpn-nth 1 (fn-bpn-nth 1 event))))))
   (t (fn-bpnp-step st event))))

(in-theory (disable fn-bpnj-offerable fn-bpnj-candidatep fn-bpnj-readyp))

(defthm fn-bpnj-step-delegates-every-other-event
  (implies (and (not (equal (fn-cbor-ag-car event) :contact-job))
                (not (equal (fn-cbor-ag-car event) :job-result))
                (not (fn-bpnj-unnamed-result-p event)))
           (equal (fn-bpnj-step st event) (fn-bpnp-step st event)))
  :hints (("Goal" :in-theory (union-theories '(fn-bpnj-step) (theory 'minimal-theory))))
  :rule-classes nil)
(defthm fn-bpnj-host-event-delegated-is-a-served-event
  (implies (and (fn-bpnj-host-eventp event)
                (not (equal (fn-cbor-ag-car event) :contact-job))
                (not (equal (fn-cbor-ag-car event) :job-result)))
           (and (not (fn-bpnj-unnamed-result-p event))
                (fn-bpnp-host-eventp event)))
  :hints (("Goal" :in-theory (union-theories '(fn-bpnj-host-eventp) (theory 'minimal-theory))))
  :rule-classes nil)
(defthm fn-bpnj-result-event-is-a-served-event
  (implies (fn-bpn-keyp key)
           (fn-bpnp-host-eventp (list :base (list :forward-result key outcome))))
  :rule-classes nil)

(defthm fn-bpnj-stale-job-result-settles-nothing
  (implies (not (and (natp token) (equal (fn-bpnj-attempt-token st key) token)))
           (equal (fn-bpnj-step st (list :job-result key token outcome))
                  (fn-bpnf-answer st (list (list :job-result-stale key token)))))
  :hints (("Goal" :in-theory (union-theories '(fn-bpnj-step fn-bpnj-result-step fn-cbor-ag-car fn-bpn-nth-is-nth-on-true-lists)
                                             (theory 'ground-zero))))
  :rule-classes nil)
; An unnamed base transport result is refused before the step by the host's
; event check (fn-bpnj-host-eventp), so the host never reaches the step's
; unnamed arm; that arm only keeps the logical step total.
(defthm fn-bpnj-host-refuses-an-unnamed-transport-result
  (implies (fn-bpnj-unnamed-result-p event)
           (not (fn-bpnj-host-eventp event)))
  :hints (("Goal" :in-theory (enable fn-bpnj-host-eventp fn-bpnj-unnamed-result-p)))
  :rule-classes nil)

(defthm fn-bpnj-found-job-has-its-key
  (implies (fn-bpn-find-job key jobs)
           (equal (fn-bpn-job-key (fn-bpn-find-job key jobs)) key))
  :hints (("Goal" :in-theory (enable fn-bpn-find-job))))
(defthm fn-bpnj-ready-job-is-a-queued-job-for-the-peer
  (implies (fn-bpnj-readyp job peer routing offered)
           (and job
                (equal (fn-bpn-job-status job) :queued)
                (equal (fn-bpn-job-peer job) peer)
                (not (fn-bpn-member (fn-bpn-job-key job) offered))
                (equal (fn-cbor-ag-car (fn-bpnj-offerable job peer routing)) :send)))
  :hints (("Goal" :in-theory (enable fn-bpnj-readyp fn-bpnj-candidatep fn-bpn-job-status)))
  :rule-classes nil)
(defthm fn-bpnj-nothing-is-ready-without-a-job
  (not (fn-bpnj-readyp nil peer routing offered))
  :hints (("Goal" :in-theory (enable fn-bpnj-readyp fn-bpnj-candidatep fn-bpn-job-status))))
(defthm fn-bpnj-select-is-ready
  (implies (fn-bpnj-select rest jobs peer routing offered)
           (fn-bpnj-readyp (fn-bpnj-select rest jobs peer routing offered)
                           peer routing offered))
  :hints (("Goal" :induct (fn-bpnj-select rest jobs peer routing offered)
           :in-theory (union-theories '(fn-bpnj-select) (theory 'minimal-theory)))))
(defthm fn-bpnj-select-is-found
  (implies (fn-bpnj-select rest jobs peer routing offered)
           (equal (fn-bpn-find-job
                   (fn-bpn-job-key (fn-bpnj-select rest jobs peer routing offered)) jobs)
                  (fn-bpnj-select rest jobs peer routing offered)))
  :hints (("Goal" :induct (fn-bpnj-select rest jobs peer routing offered)
           :in-theory (union-theories '(fn-bpnj-select fn-bpnj-found-job-has-its-key)
                                      (theory 'minimal-theory)))))
(defthm fn-bpnj-ready-job-is-selected
  (implies (and (member-equal j rest)
                (fn-bpnj-readyp (fn-bpn-find-job (fn-bpn-job-key j) jobs) peer routing offered))
           (fn-bpnj-select rest jobs peer routing offered))
  :hints (("Goal" :induct (member-equal j rest)
           :in-theory (union-theories '(fn-bpnj-select member-equal fn-bpnj-nothing-is-ready-without-a-job)
                                      (theory 'minimal-theory)))
          ("Subgoal *1/2" :use ((:instance fn-bpnj-ready-job-is-a-queued-job-for-the-peer
                                 (job (fn-bpn-find-job (fn-bpn-job-key (car rest)) jobs)))))))

(defthm fn-bpnj-open-contact-is-open
  (fn-bpn-contact-openp peer (fn-bpn-open-contact peer contacts))
  :hints (("Goal" :in-theory (enable fn-bpn-contact-openp fn-bpn-open-contact))))
(defthm fn-bpnj-with-base-fields
  (implies (true-listp st)
           (and (equal (fn-bpnf-base (fn-bpnj-with-base st b)) b)
                (equal (fn-bpnf-answer-state (fn-bpnf-answer s e)) s)
                (equal (fn-bpnf-answer-effects (fn-bpnf-answer s e)) e)))
  :hints (("Goal" :in-theory (enable fn-bpnj-with-base fn-bpnf-base fn-bpnf-answer
                                     fn-bpnf-answer-state fn-bpnf-answer-effects fn-bpn-nth))))
(defthm fn-bpnj-contact-offer-starts-the-ready-job
  (let* ((d (fn-bpnj-contact-next st peer routing offered))
         (base (fn-bpnf-base st))
         (jobs (fn-bpn-machine-state-jobs base))
         (job (fn-bpnj-select jobs jobs peer routing offered))
         (key (fn-bpn-job-key job))
         (token (fn-bpn-machine-state-next-token base))
         (ans (fn-bpnj-step st (fn-bpn-nth 1 d)))
         (pending (fn-bpn-machine-state-pending
                   (fn-bpnf-base (fn-bpnf-answer-state ans)))))
    (implies (and (true-listp st)
                  (fn-bpn-machine-statep base)
                  (equal (car d) :offer)
                  (< token *fn-bpn-machine-max-records*))
             (and (equal (fn-bpn-nth 1 d) (list :contact-job peer key))
                  (fn-bpnj-readyp job peer routing offered)
                  (equal (fn-bpnf-answer-effects ans)
                         (list (list :persist token
                                     (list :attempting token (nth 0 key)
                                           (nth 1 key) (nth 2 key)))))
                  (equal (fn-bpn-pending-success-effects pending)
                         (list (list :cl-send (fn-bpn-job-route job) peer key
                                     (fn-bpn-job-wire job)))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnj-select-is-ready
                  (rest (fn-bpn-machine-state-jobs (fn-bpnf-base st)))
                  (jobs (fn-bpn-machine-state-jobs (fn-bpnf-base st))))
                 (:instance fn-bpnj-select-is-found
                  (rest (fn-bpn-machine-state-jobs (fn-bpnf-base st)))
                  (jobs (fn-bpn-machine-state-jobs (fn-bpnf-base st))))
                 (:instance fn-bpnj-ready-job-is-a-queued-job-for-the-peer
                  (job (fn-bpnj-select (fn-bpn-machine-state-jobs (fn-bpnf-base st))
                                       (fn-bpn-machine-state-jobs (fn-bpnf-base st))
                                       peer routing offered)))
                 (:instance fn-bpnp-receipt-contact-event-needs-a-queued-job))
           :in-theory (union-theories
                       '(fn-bpnj-contact-next fn-bpnj-step fn-bpnj-contact-job-step
                         fn-bpnj-start-job fn-bpnj-open-base fn-bpn-propose
                         fn-bpnj-open-contact-is-open fn-bpnj-with-base-fields
                         fn-bpn-state-with-accessors fn-bpn-answer-constructor-accessors
                         fn-bpn-pending-constructor-accessors
                         car-cons cdr-cons fn-cbor-ag-car fn-bpn-nth
                         nth (:e zp) (:e binary-+) (:e equal) (:e not) (:e car) (:e nth)
                         (:e natp) natp zp)
                       (theory 'minimal-theory))))
  :rule-classes nil)

(defthm fn-bpnj-start-job-preserves-lifecycle-invariant
  (implies
   (fn-bpn-lifecycle-invariantp st)
   (fn-bpn-lifecycle-invariantp
    (fn-bpn-answer-state (fn-bpnj-start-job st peer key))))
  :hints
  (("Goal"
    :use
    ((:instance fn-bpn-lifecycle-invariant-implies-machine-invariant)
     (:instance fn-bpn-machine-invariant-components)
     (:instance fn-bpn-machine-statep-components)
     (:instance fn-bpn-find-job-is-a-job (jobs (fn-bpn-machine-state-jobs st)))
     (:instance fn-bpnj-found-job-has-its-key (jobs (fn-bpn-machine-state-jobs st)))
     (:instance fn-bpn-attempt-proposal-is-authorized
                (job (fn-bpn-find-job key (fn-bpn-machine-state-jobs st)))))
    :in-theory
    (union-theories
     '(fn-bpnj-start-job fn-bpn-propose-preserves-lifecycle-invariant
       fn-bpn-attempting-record-is-typed fn-bpn-answer-constructor-accessors
       fn-bpn-record-applicablep fn-bpn-proposal-effectsp
       fn-bpn-record-key fn-bpn-record-token fn-bpn-nth
       fn-bpn-job-key-accessors
       fn-bpn-effect-listp-of-singleton fn-bpn-effectp fn-bpn-member
       fn-cbor-ag-car car-cons cdr-cons true-listp len nth zp natp)
     (theory 'minimal-theory)))))
(defthm fn-bpnj-start-job-preserves-machine-invariant
  (implies
   (fn-bpn-machine-invariantp st)
   (fn-bpn-machine-invariantp
    (fn-bpn-answer-state (fn-bpnj-start-job st peer key))))
  :hints
  (("Goal"
    :use ((:instance fn-bpn-machine-invariant-components)
          (:instance fn-bpn-machine-statep-components)
          (:instance fn-bpn-find-job-is-a-job (jobs (fn-bpn-machine-state-jobs st))))
    :in-theory
    (union-theories
     '(fn-bpnj-start-job fn-bpn-propose-preserves-machine-invariant
       fn-bpn-attempting-record-is-typed fn-bpn-answer-constructor-accessors
       fn-bpn-job-key-accessors
       fn-bpn-effect-listp-of-singleton fn-bpn-effectp fn-bpn-member
       car-cons cdr-cons true-listp)
     (theory 'minimal-theory)))))

(defthm fn-bpnj-with-base-keeps-the-other-fields
  (implies (true-listp st)
           (and (equal (fn-bpnf-held-list (fn-bpnj-with-base st b)) (fn-bpnf-held-list st))
                (equal (fn-bpnp-sessions (fn-bpnj-with-base st b)) (fn-bpnp-sessions st))
                (equal (fn-bpnf-issued (fn-bpnj-with-base st b)) (fn-bpnf-issued st))
                (equal (fn-bpnf-waits (fn-bpnj-with-base st b)) (fn-bpnf-waits st))
                (true-listp (fn-bpnj-with-base st b))))
  :hints (("Goal" :in-theory (enable fn-bpnj-with-base fn-bpnf-held-list fn-bpnp-sessions
                                     fn-bpnf-issued fn-bpnf-waits fn-bpn-nth))))
(defthm fn-bpnj-open-base-preserves-invariants
  (implies (and (fn-bpn-machine-invariantp base)
                (fn-bpp-eidp peer)
                (not (fn-bpn-machine-state-pending base)))
           (and (fn-bpn-machine-invariantp (fn-bpnj-open-base base peer))
                (implies (fn-bpn-lifecycle-invariantp base)
                         (fn-bpn-lifecycle-invariantp (fn-bpnj-open-base base peer)))))
  :hints (("Goal"
           :use ((:instance fn-bpn-open-contact-preserves-contact-listp
                  (contacts (fn-bpn-machine-state-contacts base)))
                 (:instance fn-bpn-machine-invariant-components (st base))
                 (:instance fn-bpn-machine-statep-components (st base))
                 (:instance fn-bpn-contact-state-with-preserves-machine-invariant
                  (st base) (contacts (fn-bpn-open-contact peer (fn-bpn-machine-state-contacts base))))
                 (:instance fn-bpn-contact-state-with-preserves-lifecycle-invariant
                  (st base) (contacts (fn-bpn-open-contact peer (fn-bpn-machine-state-contacts base)))))
           :in-theory (union-theories '(fn-bpnj-open-base fn-bpn-open-contact-preserves-contact-listp)
                                      (theory 'minimal-theory)))))
(defthm fn-bpnj-contact-job-step-preserves-the-base-invariants
  (let ((next (fn-bpnf-base (fn-bpnf-answer-state (fn-bpnj-contact-job-step st peer key)))))
    (and (implies (fn-bpn-machine-invariantp (fn-bpnf-base st))
                  (fn-bpn-machine-invariantp next))
         (implies (fn-bpn-lifecycle-invariantp (fn-bpnf-base st))
                  (fn-bpn-lifecycle-invariantp next))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnp-receipt-contact-event-needs-a-queued-job)
                 (:instance fn-bpn-lifecycle-invariant-implies-machine-invariant (st (fn-bpnf-base st)))
                 (:instance fn-bpnj-open-base-preserves-invariants (base (fn-bpnf-base st)))
                 (:instance fn-bpnj-start-job-preserves-machine-invariant
                  (st (fn-bpnj-open-base (fn-bpnf-base st) peer)))
                 (:instance fn-bpnj-start-job-preserves-lifecycle-invariant
                  (st (fn-bpnj-open-base (fn-bpnf-base st) peer))))
           :in-theory (union-theories '(fn-bpnj-contact-job-step fn-bpnj-with-base-fields)
                                      (theory 'minimal-theory))))
  :rule-classes nil)

(defthm fn-bpnj-contact-job-step-keeps-the-served-fields
  (implies (true-listp st)
           (let ((next (fn-bpnf-answer-state (fn-bpnj-contact-job-step st peer key))))
             (and (equal (fn-bpnp-sessions next) (fn-bpnp-sessions st))
                  (equal (fn-bpnf-held-list next) (fn-bpnf-held-list st))
                  (equal (fn-bpnf-issued next) (fn-bpnf-issued st)))))
  :hints (("Goal" :in-theory (union-theories '(fn-bpnj-contact-job-step fn-bpnj-with-base-fields
                                               fn-bpnj-with-base-keeps-the-other-fields)
                                             (theory 'minimal-theory))))
  :rule-classes nil)
(defthm fn-bpnj-step-preserves-guard-premises
  (implies (and (fn-bpnp-step-guard-premisesp st)
                (true-listp st)
                (fn-bpnj-host-eventp event))
           (fn-bpnp-step-guard-premisesp
            (fn-bpnf-answer-state (fn-bpnj-step st event))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnj-contact-job-step-keeps-the-served-fields
                  (peer (fn-bpn-nth 1 event)) (key (fn-bpn-nth 2 event)))
                 (:instance fn-bpnj-contact-job-step-preserves-the-base-invariants
                  (peer (fn-bpn-nth 1 event)) (key (fn-bpn-nth 2 event)))
                 (:instance fn-bpnj-result-event-is-a-served-event
                  (key (fn-bpn-nth 1 event)) (outcome (fn-bpn-nth 3 event)))
                 (:instance fn-bpnp-step-preserves-guard-premises
                  (event (list :base (list :forward-result (fn-bpn-nth 1 event)
                                           (fn-bpn-nth 3 event)))))
                 (:instance fn-bpnp-step-preserves-guard-premises)
                 (:instance fn-bpnj-host-event-delegated-is-a-served-event))
           :in-theory (union-theories '(fn-bpnj-step fn-bpnj-result-step fn-bpnp-step-guard-premisesp
                                        fn-bpnj-host-eventp fn-bpnj-with-base-fields)
                                      (theory 'minimal-theory)))))
(defthm fn-bpnj-new-arms-preserve-the-lifecycle-invariant
  (implies (and (fn-bpn-lifecycle-invariantp (fn-bpnf-base st))
                (true-listp st)
                (or (equal (fn-cbor-ag-car event) :contact-job)
                    (equal (fn-cbor-ag-car event) :job-result)))
           (fn-bpn-lifecycle-invariantp
            (fn-bpnf-base (fn-bpnf-answer-state (fn-bpnj-step st event)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnj-contact-job-step-preserves-the-base-invariants
                  (peer (fn-bpn-nth 1 event)) (key (fn-bpn-nth 2 event)))
                 (:instance fn-bpnp-step-base-event-preserves-lifecycle-invariant-by-bridge
                  (e (list :forward-result (fn-bpn-nth 1 event) (fn-bpn-nth 3 event)))))
           :in-theory (union-theories '(fn-bpnj-step fn-bpnj-result-step fn-bpnj-with-base-fields
                                        fn-bpn-machine-eventp fn-bpn-eventp fn-bpn-member
                                        true-listp car-cons cdr-cons (:e fn-bpn-member) (:e equal))
                                      (theory 'minimal-theory)))))

(defun fn-bpnj-forwarded-transport-p (effects)
  (declare (xargs :guard t))
  (if (atom effects)
      nil
    (or (and (equal (fn-cbor-ag-car (car effects)) :transport)
             (equal (fn-bpn-nth 4 (car effects)) :forwarded))
        (fn-bpnj-forwarded-transport-p (cdr effects)))))
(defthm fn-bpnj-forwarded-success-is-a-finished-proposal
  (implies (and (fn-bpn-proposal-effectsp st record success refusal uncertain)
                (fn-bpnj-forwarded-transport-p success))
           (and (equal (fn-cbor-ag-car record) :finished)
                (equal (fn-bpn-job-status
                        (fn-bpn-find-job (fn-bpn-record-key record)
                                         (fn-bpn-machine-state-jobs st)))
                       :attempting)))
  :hints (("Goal" :in-theory (enable fn-bpn-proposal-effectsp fn-bpnj-forwarded-transport-p
                                     fn-bpn-nth fn-cbor-ag-car)))
  :rule-classes nil)
(defthm fn-bpnj-authorized-refusal-and-uncertainty-are-not-transport
  (implies (fn-bpn-proposal-effectsp st record success refusal uncertain)
           (and (not (equal (fn-cbor-ag-car refusal) :transport))
                (not (equal (fn-cbor-ag-car uncertain) :transport))))
  :hints (("Goal" :in-theory (enable fn-bpn-proposal-effectsp fn-cbor-ag-car)))
  :rule-classes nil)
(defthm fn-bpnj-base-forwarded-needs-a-durable-finished-record
  (implies
   (and (fn-bpn-lifecycle-invariantp st)
        (fn-bpnj-forwarded-transport-p
         (fn-bpn-answer-effects (fn-bpn-step st event))))
   (let* ((pending (fn-bpn-machine-state-pending st))
          (record (fn-bpn-pending-record pending)))
     (and pending
          (equal (car event) :persist-result)
          (equal (nth 1 event) (fn-bpn-pending-token pending))
          (equal (nth 2 event) :durable)
          (equal (fn-cbor-ag-car record) :finished)
          (equal (fn-bpn-job-status
                  (fn-bpn-find-job (fn-bpn-record-key record)
                                   (fn-bpn-machine-state-jobs st)))
                 :attempting))))
  :hints
  (("Goal"
    :use ((:instance fn-bpn-lifecycle-invariant-authorizes-pending)
          (:instance fn-bpnj-authorized-refusal-and-uncertainty-are-not-transport
                     (record (fn-bpn-pending-record (fn-bpn-machine-state-pending st)))
                     (success (fn-bpn-pending-success-effects (fn-bpn-machine-state-pending st)))
                     (refusal (fn-bpn-pending-refusal-effect (fn-bpn-machine-state-pending st)))
                     (uncertain (fn-bpn-pending-uncertainty-effect (fn-bpn-machine-state-pending st))))
          (:instance fn-bpnj-forwarded-success-is-a-finished-proposal
                     (record (fn-bpn-pending-record (fn-bpn-machine-state-pending st)))
                     (success (fn-bpn-pending-success-effects (fn-bpn-machine-state-pending st)))
                     (refusal (fn-bpn-pending-refusal-effect (fn-bpn-machine-state-pending st)))
                     (uncertain (fn-bpn-pending-uncertainty-effect (fn-bpn-machine-state-pending st)))))
    :in-theory
    (union-theories
     '(fn-bpn-step fn-bpn-dispatch fn-bpn-enqueue-step fn-bpn-contact-step
       fn-bpn-start-one fn-bpn-persist-result-step
       fn-bpn-forward-result-step fn-bpn-clock-step fn-bpn-restart-step
       fn-bpn-propose fn-bpn-apply-record
       fn-bpnj-forwarded-transport-p fn-bpn-answer-constructor-accessors
       fn-bpn-pending-authorizedp fn-bpn-lifecycle-invariantp
       fn-bpn-member fn-cbor-ag-car fn-bpn-nth car-cons cdr-cons true-listp nth zp)
     (theory 'minimal-theory))))
  :rule-classes nil)

(defthm fn-bpnj-named-result-is-the-transport-outcome
  (let* ((base (fn-bpnf-base st))
         (token (fn-bpn-machine-state-next-token base))
         (ans (fn-bpnj-step st (list :job-result key attempt outcome)))
         (pending (fn-bpn-machine-state-pending
                   (fn-bpnf-base (fn-bpnf-answer-state ans))))
         (w (nth 0 key)) (a (nth 1 key)) (g (nth 2 key))
         (reason (if (equal outcome :refused) :refused
                   (if (equal outcome :uncertain) :uncertain :failed))))
    (implies (and (fn-bpn-machine-statep base)
                  (not (fn-bpnf-issued st))
                  (not (fn-bpah-delivery-uncertainp st))
                  (not (fn-bpn-machine-state-fenced base))
                  (not (fn-bpn-machine-state-pending base))
                  (natp attempt)
                  (equal (fn-bpnj-attempt-token st key) attempt)
                  (< token *fn-bpn-machine-max-records*))
             (if (equal outcome :accepted)
                 (and (equal (fn-bpnf-answer-effects ans)
                             (list (list :persist token
                                         (list :finished token w a g :none :finished))))
                      (equal (fn-bpn-pending-success-effects pending)
                             (list (list :transport w a g :forwarded))))
               (and (equal (fn-bpnf-answer-effects ans)
                           (list (list :persist token
                                       (list :requeued token w a g reason :requeued))))
                    (equal (fn-bpn-pending-success-effects pending)
                           (list (list :transport w a g :attempted)
                                 (list :forward-refused w a g reason)))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnp-step-base-event-refines-fn-bpn-step
                  (e (list :forward-result key outcome))))
           :in-theory (union-theories
                       '(fn-bpnj-step fn-bpnj-result-step fn-bpnj-attempt-token
                         fn-bpn-step fn-bpn-dispatch fn-bpn-forward-result-step fn-bpn-propose
                         fn-bpn-state-with-accessors fn-bpn-answer-constructor-accessors
                         fn-bpn-pending-constructor-accessors
                         fn-cbor-ag-car fn-bpn-nth car-cons cdr-cons nth
                         (:e zp) (:e binary-+) (:e equal) (:e not) (:e car) (:e nth)
                         (:e natp) natp zp)
                       (theory 'minimal-theory))))
  :rule-classes nil)

(defthm fn-bpnj-step-forwarded-needs-a-durable-finished-record
  (implies
   (and (fn-bpn-lifecycle-invariantp (fn-bpnf-base st))
        (fn-bpnj-forwarded-transport-p
         (fn-bpnf-answer-effects (fn-bpnj-step st (list :base e)))))
   (let* ((base (fn-bpnf-base st))
          (pending (fn-bpn-machine-state-pending base))
          (record (fn-bpn-pending-record pending)))
     (and (not (fn-bpnf-issued st))
          (not (fn-bpah-delivery-uncertainp st))
          pending
          (equal (car e) :persist-result)
          (equal (nth 1 e) (fn-bpn-pending-token pending))
          (equal (nth 2 e) :durable)
          (equal (fn-cbor-ag-car record) :finished)
          (equal (fn-bpn-job-status
                  (fn-bpn-find-job (fn-bpn-record-key record)
                                   (fn-bpn-machine-state-jobs base)))
                 :attempting))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnp-step-base-event-refines-fn-bpn-step)
                 (:instance fn-bpnj-base-forwarded-needs-a-durable-finished-record
                            (st (fn-bpnf-base st)) (event e)))
           :in-theory (union-theories
                       '(fn-bpnj-step fn-bpnj-unnamed-result-p fn-bpnj-forwarded-transport-p
                         fn-bpnf-answer fn-bpnf-answer-effects fn-bpn-nth fn-cbor-ag-car
                         car-cons cdr-cons nth (:e zp) (:e nth) (:e car) (:e equal) (:e fn-bpnj-forwarded-transport-p) zp)
                       (theory 'minimal-theory))))
  :rule-classes nil)

(defthm fn-bpnj-encoder-refusal-settles-the-pending-record
  (let* ((base (fn-bpnf-base st))
         (pending (fn-bpn-machine-state-pending base))
         (ans (fn-bpnj-step st (list :base (list :persist-result
                                                 (fn-bpn-pending-token pending)
                                                 :refused))))
         (next (fn-bpnf-base (fn-bpnf-answer-state ans))))
    (implies (and (fn-bpn-machine-statep base)
                  pending
                  (not (fn-bpnf-issued st))
                  (not (fn-bpah-delivery-uncertainp st)))
             (and (not (fn-bpn-machine-state-pending next))
                  (not (fn-bpn-machine-state-fenced next))
                  (equal (fn-bpn-machine-state-jobs next)
                         (fn-bpn-machine-state-jobs base))
                  (equal (fn-bpnf-answer-effects ans)
                         (list (fn-bpn-pending-refusal-effect pending))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnp-step-base-event-refines-fn-bpn-step
                  (e (list :persist-result
                           (fn-bpn-pending-token (fn-bpn-machine-state-pending (fn-bpnf-base st)))
                           :refused))))
           :in-theory (union-theories
                       '(fn-bpnj-step fn-bpnj-unnamed-result-p
                         fn-bpn-step fn-bpn-dispatch fn-bpn-persist-result-step
                         fn-bpn-state-with-accessors fn-bpn-answer-constructor-accessors
                         fn-cbor-ag-car fn-bpn-nth car-cons cdr-cons nth
                         (:e zp) (:e nth) (:e car) (:e equal) (:e not) zp)
                       (theory 'minimal-theory))))
  :rule-classes nil)

(defun fn-bpnj-job-keys (jobs)
  (declare (xargs :guard t))
  (if (atom jobs) nil
    (cons (fn-bpn-job-key (car jobs)) (fn-bpnj-job-keys (cdr jobs)))))
(defun fn-bpnj-keys-through (key jobs)
  (declare (xargs :guard t))
  (if (atom jobs) nil
    (cons (fn-bpn-job-key (car jobs))
          (if (equal (fn-bpn-job-key (car jobs)) key) nil
            (fn-bpnj-keys-through key (cdr jobs))))))
(defun fn-bpnj-unoffered (keys offered)
  (declare (xargs :guard t))
  (if (atom keys) nil
    (if (member-equal (car keys) offered)
        (fn-bpnj-unoffered (cdr keys) offered)
      (cons (car keys) (fn-bpnj-unoffered (cdr keys) offered)))))
(defun fn-bpnj-contact-offers (sts peer routing offered)
  (declare (xargs :guard t))
  (if (atom sts) nil
    (let ((d (fn-bpnj-contact-next (car sts) peer routing offered)))
      (if (equal (fn-bpn-nth 0 d) :offer)
          (cons (fn-bpn-nth 0 (fn-bpn-nth 2 d))
                (fn-bpnj-contact-offers (cdr sts) peer routing (fn-bpn-nth 2 d)))
        nil))))
(defun fn-bpnj-stays-ready-p (sts peer routing key prefix)
  (declare (xargs :guard t))
  (if (atom sts) t
    (let ((jobs (fn-bpn-machine-state-jobs (fn-bpnf-base (car sts)))))
      (and (fn-bpnp-receipt-contact-event (car sts) peer)
           (member-equal key (fn-bpnj-job-keys jobs))
           (fn-bpnj-readyp (fn-bpn-find-job key jobs) peer routing nil)
           (equal (fn-bpnj-keys-through key jobs) prefix)
           (fn-bpnj-stays-ready-p (cdr sts) peer routing key prefix)))))
(defthm fn-bpnj-member-is-member-equal
  (iff (fn-bpn-member x xs) (member-equal x xs))
  :hints (("Goal" :in-theory (enable fn-bpn-member))))
(defthm fn-bpnj-ready-without-offers
  (implies (and (fn-bpnj-readyp job peer routing nil)
                (not (member-equal (fn-bpn-job-key job) offered)))
           (fn-bpnj-readyp job peer routing offered))
  :hints (("Goal" :in-theory (enable fn-bpnj-readyp fn-bpnj-candidatep))))
(defthm fn-bpnj-selected-key-is-unoffered
  (implies (fn-bpnj-select rest jobs peer routing offered)
           (not (member-equal (fn-bpn-job-key (fn-bpnj-select rest jobs peer routing offered))
                              offered)))
  :hints (("Goal" :use ((:instance fn-bpnj-select-is-ready)
                        (:instance fn-bpnj-ready-job-is-a-queued-job-for-the-peer
                         (job (fn-bpnj-select rest jobs peer routing offered))))
           :in-theory (union-theories '(fn-bpnj-member-is-member-equal) (theory 'minimal-theory)))))
(defthm fn-bpnj-ready-job-exists
  (implies (fn-bpnj-readyp job peer routing offered) job)
  :hints (("Goal" :use fn-bpnj-ready-job-is-a-queued-job-for-the-peer))
  :rule-classes :forward-chaining)
(defthm fn-bpnj-select-is-within-the-prefix
  (implies (and (member-equal key (fn-bpnj-job-keys rest))
                (fn-bpnj-readyp (fn-bpn-find-job key jobs) peer routing offered))
           (member-equal (fn-bpn-job-key (fn-bpnj-select rest jobs peer routing offered))
                         (fn-bpnj-keys-through key rest)))
  :hints (("Goal" :induct (fn-bpnj-keys-through key rest)
           :in-theory (union-theories '(fn-bpnj-select fn-bpnj-job-keys fn-bpnj-keys-through
                                        member-equal fn-bpnj-found-job-has-its-key
                                        fn-bpnj-nothing-is-ready-without-a-job fn-bpnj-ready-job-exists car-cons cdr-cons)
                                      (theory 'minimal-theory)))))
(defthm fn-bpnj-unoffered-shrinks
  (implies (and (member-equal k keys) (not (member-equal k offered)))
           (< (len (fn-bpnj-unoffered keys (cons k offered)))
              (len (fn-bpnj-unoffered keys offered))))
  :rule-classes :linear)
(defthm fn-bpnj-unoffered-grows-no-larger
  (<= (len (fn-bpnj-unoffered keys (cons k offered)))
      (len (fn-bpnj-unoffered keys offered)))
  :rule-classes :linear)
(defthm fn-bpnj-key-is-in-its-prefix
  (implies (member-equal key (fn-bpnj-job-keys jobs))
           (member-equal key (fn-bpnj-keys-through key jobs))))
(defthm fn-bpnj-unoffered-key-counts
  (implies (and (member-equal key keys) (not (member-equal key offered)))
           (< 0 (len (fn-bpnj-unoffered keys offered))))
  :rule-classes :linear)

(defthm fn-bpnj-contact-next-offer-shape
  (let ((jobs (fn-bpn-machine-state-jobs (fn-bpnf-base st))))
    (implies (and (fn-bpnp-receipt-contact-event st peer)
                  (fn-bpnj-select jobs jobs peer routing offered))
             (equal (fn-bpnj-contact-next st peer routing offered)
                    (list :offer
                          (list :contact-job peer
                                (fn-bpn-job-key (fn-bpnj-select jobs jobs peer routing offered)))
                          (cons (fn-bpn-job-key (fn-bpnj-select jobs jobs peer routing offered))
                                offered)
                          (fn-bpn-nth 1 (fn-bpnj-offerable
                                         (fn-bpnj-select jobs jobs peer routing offered)
                                         peer routing))))))
  :hints (("Goal" :in-theory (union-theories '(fn-bpnj-contact-next) (theory 'minimal-theory)))))
(defthm fn-bpnj-ready-key-is-selected
  (implies (and (member-equal key (fn-bpnj-job-keys rest))
                (fn-bpnj-readyp (fn-bpn-find-job key jobs) peer routing offered))
           (fn-bpnj-select rest jobs peer routing offered))
  :hints (("Goal" :induct (fn-bpnj-job-keys rest)
           :in-theory (union-theories '(fn-bpnj-select fn-bpnj-job-keys member-equal
                                        fn-bpnj-nothing-is-ready-without-a-job car-cons cdr-cons)
                                      (theory 'minimal-theory)))))
(defthm fn-bpnj-ready-key-stays-ready-while-unoffered
  (implies (and (fn-bpnj-readyp (fn-bpn-find-job key jobs) peer routing nil)
                (not (member-equal key offered)))
           (fn-bpnj-readyp (fn-bpn-find-job key jobs) peer routing offered))
  :hints (("Goal" :use ((:instance fn-bpnj-ready-without-offers (job (fn-bpn-find-job key jobs)))
                        (:instance fn-bpnj-found-job-has-its-key)
                        (:instance fn-bpnj-ready-job-exists (job (fn-bpn-find-job key jobs))
                                   (offered nil)))
           :in-theory (theory 'minimal-theory))))
(defthm fn-bpnj-one-ask-offers-within-the-prefix
  (let* ((jobs (fn-bpn-machine-state-jobs (fn-bpnf-base st)))
         (d (fn-bpnj-contact-next st peer routing offered))
         (k (fn-bpn-nth 0 (fn-bpn-nth 2 d))))
    (implies (and (fn-bpnp-receipt-contact-event st peer)
                  (member-equal key (fn-bpnj-job-keys jobs))
                  (fn-bpnj-readyp (fn-bpn-find-job key jobs) peer routing nil)
                  (not (member-equal key offered)))
             (and (equal (fn-bpn-nth 0 d) :offer)
                  (equal (fn-bpn-nth 2 d) (cons k offered))
                  (member-equal k (fn-bpnj-keys-through key jobs))
                  (not (member-equal k offered)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnj-ready-key-stays-ready-while-unoffered
                  (jobs (fn-bpn-machine-state-jobs (fn-bpnf-base st))))
                 (:instance fn-bpnj-ready-key-is-selected
                  (rest (fn-bpn-machine-state-jobs (fn-bpnf-base st)))
                  (jobs (fn-bpn-machine-state-jobs (fn-bpnf-base st))))
                 (:instance fn-bpnj-select-is-within-the-prefix
                  (rest (fn-bpn-machine-state-jobs (fn-bpnf-base st)))
                  (jobs (fn-bpn-machine-state-jobs (fn-bpnf-base st))))
                 (:instance fn-bpnj-selected-key-is-unoffered
                  (rest (fn-bpn-machine-state-jobs (fn-bpnf-base st)))
                  (jobs (fn-bpn-machine-state-jobs (fn-bpnf-base st))))
                 )
           :in-theory (union-theories '(fn-bpnj-contact-next-offer-shape fn-bpn-nth fn-cbor-ag-car fn-cbor-ag-cdr car-cons cdr-cons
                                        (:e zp) zp (:e natp) (:e fn-bpn-nth) (:e equal) (:e car) (:e binary-+))
                                      (theory 'minimal-theory))))
  :rule-classes nil)
(defthm fn-bpnj-one-ask-shrinks-the-unoffered-prefix
  (let* ((jobs (fn-bpn-machine-state-jobs (fn-bpnf-base st)))
         (d (fn-bpnj-contact-next st peer routing offered)))
    (implies (and (fn-bpnp-receipt-contact-event st peer)
                  (member-equal key (fn-bpnj-job-keys jobs))
                  (fn-bpnj-readyp (fn-bpn-find-job key jobs) peer routing nil)
                  (equal (fn-bpnj-keys-through key jobs) prefix)
                  (not (member-equal key offered)))
             (and (equal (fn-bpn-nth 0 d) :offer)
                  (implies (not (equal (fn-bpn-nth 0 (fn-bpn-nth 2 d)) key))
                           (not (member-equal key (fn-bpn-nth 2 d))))
                  (< (len (fn-bpnj-unoffered prefix (fn-bpn-nth 2 d)))
                     (len (fn-bpnj-unoffered prefix offered))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnj-one-ask-offers-within-the-prefix)
                 (:instance fn-bpnj-unoffered-shrinks
                  (keys prefix)
                  (k (fn-bpn-nth 0 (fn-bpn-nth 2 (fn-bpnj-contact-next st peer routing offered))))))
           :in-theory (union-theories '(member-equal car-cons cdr-cons)
                                      (theory 'minimal-theory))))
  :rule-classes nil)
(defthm fn-bpnj-contact-offers-a-ready-job-within-its-prefix
  (implies (and (fn-bpnj-stays-ready-p sts peer routing key prefix)
                (member-equal key prefix)
                (not (member-equal key offered))
                (<= (len (fn-bpnj-unoffered prefix offered)) (len sts)))
           (member-equal key (fn-bpnj-contact-offers sts peer routing offered)))
  :hints (("Goal" :induct (fn-bpnj-contact-offers sts peer routing offered)
           :in-theory (union-theories
                       '(fn-bpnj-contact-offers fn-bpnj-stays-ready-p
                         fn-bpnj-unoffered-key-counts
                         len (:type-prescription len) member-equal car-cons cdr-cons (:e zp) zp
                         (:e equal) (:e len) natp (:e natp) (:e <) (:e binary-+) fix)
                       (theory 'minimal-theory)))
          ("Subgoal *1/3" :use ((:instance fn-bpnj-one-ask-shrinks-the-unoffered-prefix (st (car sts)))))
          ("Subgoal *1/2" :use ((:instance fn-bpnj-one-ask-shrinks-the-unoffered-prefix (st (car sts)))))))

(defthm fn-bpnj-found-key-is-a-job-key
  (implies (fn-bpn-find-job key jobs)
           (member-equal key (fn-bpnj-job-keys jobs)))
  :hints (("Goal" :in-theory (enable fn-bpn-find-job))))

;; KEYSTONE (no starvation on a contact).  Over the selection the host asks
;; before every offer: while the contact is open for offers and any queued
;; job for the peer is ready (not yet offered on this contact, routed on its
;; durable route), the answer is an offer.  A held or already offered job
;; ahead of it in the list never ends the contact.
(defthm fn-bpnj-contact-offers-while-a-ready-job-remains
  (let ((jobs (fn-bpn-machine-state-jobs (fn-bpnf-base st))))
    (implies (and (fn-bpnp-receipt-contact-event st peer)
                  (fn-bpnj-readyp (fn-bpn-find-job key jobs) peer routing offered))
             (equal (car (fn-bpnj-contact-next st peer routing offered)) :offer)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnj-ready-key-is-selected
                  (rest (fn-bpn-machine-state-jobs (fn-bpnf-base st)))
                  (jobs (fn-bpn-machine-state-jobs (fn-bpnf-base st))))
                 (:instance fn-bpnj-found-key-is-a-job-key
                  (jobs (fn-bpn-machine-state-jobs (fn-bpnf-base st))))
                 (:instance fn-bpnj-ready-job-exists
                  (job (fn-bpn-find-job key (fn-bpn-machine-state-jobs (fn-bpnf-base st))))))
           :in-theory (union-theories '(fn-bpnj-contact-next car-cons)
                                      (theory 'minimal-theory))))
  :rule-classes nil)
