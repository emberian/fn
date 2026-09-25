; Owed receipts leave from `bp-node serve' itself (spec bp-node-machine 9.4).
;
; `fnn-bpnode-queue-outbox' (host/native/bp-node.lisp) queues each owed
; receipt as a base FNBS job whose peer is the requester's EID and whose
; route is the node's configured neighbour (CONTACT-HOST:PORT).  This book is
; the one decision the node's own loop asks before sending them: whether to
; open a base contact for that peer now.  The host (fnn-bpnode-send-receipts)
; computes nothing: it drives the event this function returns through the
; same fn-bpnp-step (:base E) path `bp-contact tick' drives.
;
; The offer itself is the lower machine's: on an opened contact,
; fn-bpn-contact-step proposes the :attempting record of exactly the first
; queued job for the peer, with the :cl-send that carries that job's route,
; peer, key and wire as its success effect.  fn-bpnp-step answers exactly
; fn-bpn-step on (:base E) when nothing is issued and no delivery is
; uncertain (fn-bpnp-step-base-event-refines-fn-bpn-step), and this event
; is non-nil only in that case.
(in-package "ACL2")
(include-book "bp-node-progress-bridge")
(include-book "bp-node-machine-invariants")
(set-verify-guards-eagerness 0)

(defun fn-bpnp-receipt-contact-event (st peer)
  (declare (xargs :guard t))
  (let ((base (fn-bpnf-base st)))
    (if (and (fn-bpp-eidp peer)
             (not (fn-bpnf-issued st))
             (not (fn-bpah-delivery-uncertainp st))
             (not (fn-bpn-machine-state-fenced base))
             (not (fn-bpn-machine-state-pending base))
             (fn-bpn-member peer (fn-bpn-ready-peers
                                  (fn-bpn-machine-state-jobs base))))
        (list :contact peer t)
      nil)))

;; ---------------------------------------------------------------------
;; Job-list facts.

(local
 (defthm bprsend-ready-peer-has-a-queued-job
   (iff (fn-bpn-member peer (fn-bpn-ready-peers jobs))
        (fn-bpn-find-queued-for-peer peer jobs))
   :hints (("Goal" :induct (fn-bpn-ready-peers jobs)
            :in-theory (enable fn-bpn-ready-peers fn-bpn-member
                               fn-bpn-find-queued-for-peer)))))

(local
 (defthm bprsend-queued-job-names-the-peer
   (implies (fn-bpn-find-queued-for-peer peer jobs)
            (and (equal (fn-bpn-job-peer (fn-bpn-find-queued-for-peer peer jobs))
                        peer)
                 (equal (fn-bpn-job-status
                         (fn-bpn-find-queued-for-peer peer jobs))
                        :queued)))
   :hints (("Goal" :induct (fn-bpn-find-queued-for-peer peer jobs)
            :in-theory (union-theories '(fn-bpn-find-queued-for-peer)
                                       (theory 'minimal-theory))))))

;; ---------------------------------------------------------------------
;; KEYSTONE (c).  The event opens a contact only for a peer with a queued
;; job, and for every such peer while nothing is issued or fenced.

(defthm fn-bpnp-receipt-contact-event-needs-a-queued-job
  (let* ((base (fn-bpnf-base st))
         (job (fn-bpn-find-queued-for-peer
               peer (fn-bpn-machine-state-jobs base))))
    (iff (fn-bpnp-receipt-contact-event st peer)
         (and (fn-bpp-eidp peer)
              (not (fn-bpnf-issued st))
              (not (fn-bpah-delivery-uncertainp st))
              (not (fn-bpn-machine-state-fenced base))
              (not (fn-bpn-machine-state-pending base))
              job
              (equal (fn-bpn-job-status job) :queued)
              (equal (fn-bpn-job-peer job) peer))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories
                       '(fn-bpnp-receipt-contact-event
                         bprsend-ready-peer-has-a-queued-job
                         bprsend-queued-job-names-the-peer)
                       (theory 'minimal-theory))))
  :rule-classes nil)

;; ---------------------------------------------------------------------
;; KEYSTONE (a).  Over the called fn-bpnp-step: the event's one proposal is
;; the :attempting record of exactly the first queued job for the peer, and
;; its success effect is the :cl-send of that job's route, peer, key and
;; wire.  The token hypothesis is the lower machine's journal bound; at the
;; bound the answer is the refusal effect instead.

(local
 (defthm bprsend-contact-step-proposal
   (let* ((jobs (fn-bpn-machine-state-jobs base))
          (job (fn-bpn-find-queued-for-peer peer jobs))
          (token (fn-bpn-machine-state-next-token base))
          (key (fn-bpn-job-key job))
          (low (fn-bpn-step base (list :contact peer t))))
     (implies (and (fn-bpn-machine-statep base)
                   (fn-bpp-eidp peer)
                   (not (fn-bpn-machine-state-fenced base))
                   (not (fn-bpn-machine-state-pending base))
                   job
                   (< token *fn-bpn-machine-max-records*))
              (and (equal (fn-bpn-answer-effects low)
                          (list (list :persist token
                                      (list :attempting token (nth 0 key)
                                            (nth 1 key) (nth 2 key)))))
                   (equal (fn-bpn-machine-state-pending (fn-bpn-answer-state low))
                          (fn-bpn-make-pending
                           token
                           (list :attempting token (nth 0 key)
                                 (nth 1 key) (nth 2 key))
                           (list (list :cl-send (fn-bpn-job-route job) peer key
                                       (fn-bpn-job-wire job)))
                           (list :bundle-queue-refused (nth 0 key) (nth 1 key)
                                 (nth 2 key) :attempt-persistence-refused)
                           (list :bundle-queue-uncertain (nth 0 key) (nth 1 key)
                                 (nth 2 key) :attempt-persistence))))))
   :hints (("Goal" :do-not-induct t
            :in-theory (union-theories
                        '(fn-bpn-step fn-bpn-dispatch fn-bpn-contact-step
                          fn-bpn-start-one fn-bpn-propose
                          fn-bpn-contact-openp fn-bpn-open-contact
                          fn-bpn-member
                          fn-bpn-state-with-accessors
                          fn-bpn-answer-constructor-accessors
                          bprsend-queued-job-names-the-peer
                          car-cons cdr-cons nth (:e zp) (:e binary-+) (:e eql) not
                          (:e nth) (:e car) (:e equal) (:e not))
                        (theory 'minimal-theory))))))

(defthm fn-bpnp-receipt-contact-offers-the-queued-job
  (let* ((base (fn-bpnf-base st))
         (jobs (fn-bpn-machine-state-jobs base))
         (job (fn-bpn-find-queued-for-peer peer jobs))
         (token (fn-bpn-machine-state-next-token base))
         (key (fn-bpn-job-key job))
         (event (fn-bpnp-receipt-contact-event st peer))
         (ans (fn-bpnp-step st (list :base event)))
         (pending (fn-bpn-machine-state-pending
                   (fn-bpnf-base (fn-bpnf-answer-state ans)))))
    (implies (and (fn-bpn-machine-statep base)
                  event
                  (< token *fn-bpn-machine-max-records*))
             (and (equal event (list :contact peer t))
                  (equal (fn-bpn-job-status job) :queued)
                  (equal (fn-bpn-job-peer job) peer)
                  (equal (fn-bpnf-answer-effects ans)
                         (list (list :persist token
                                     (list :attempting token (nth 0 key)
                                           (nth 1 key) (nth 2 key)))))
                  (equal (fn-bpn-pending-success-effects pending)
                         (list (list :cl-send (fn-bpn-job-route job) peer key
                                     (fn-bpn-job-wire job)))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnp-step-base-event-refines-fn-bpn-step
                            (e (list :contact peer t)))
                 (:instance bprsend-contact-step-proposal
                            (base (fn-bpnf-base st))))
           :in-theory (union-theories
                       '(fn-bpnp-receipt-contact-event
                         bprsend-ready-peer-has-a-queued-job
                         bprsend-queued-job-names-the-peer
                         fn-bpn-pending-constructor-accessors
                         (:e equal) (:e not))
                       (theory 'minimal-theory))))
  :rule-classes nil)

;; ---------------------------------------------------------------------
;; An uncertain receipt transfer is connection-local (spec bp-node-machine
;; 4.3.2).  The lower machine's answer to (:forward-result KEY :uncertain)
;; for an :attempting job is the durable :requeued record with reason
;; :uncertain (fn-bpn-forward-result-step); the job keeps its durable
;; :attempting record until that record is durable, then it is :queued
;; again under the same key, peer, route and wire.  Nothing fences: the
;; base stays unfenced, nothing FNBS-level is issued, no delivery becomes
;; uncertain, and no effect releases, prepares a receipt or reports the
;; transfer :forwarded.  Only an uncertain PUBLICATION of that record (the
;; pending uncertainty effect, :bundle-queue-uncertain) fences, as it does
;; for every record.

(local
 (defthm bprsend-base-event-keeps-the-gates-open
   (let ((next (fn-bpnf-answer-state (fn-bpnp-step st (list :base e)))))
     (implies (and (not (fn-bpnf-issued st))
                   (not (fn-bpah-delivery-uncertainp st)))
              (and (not (fn-bpnf-issued next))
                   (not (fn-bpah-delivery-uncertainp next)))))
   :hints (("Goal" :do-not-induct t
            :in-theory (union-theories
                        '(fn-bpnp-step fn-bpnp-delegate-with-credit
                          fn-bpn-report-author-step fn-bpn-report-step
                          fn-bpnf-fragment-step fn-bpnf-step
                          fn-bpnp-preserve-runtime-answer
                          fn-bpn-report-delete-issuedp fn-bpnf-family-issuedp
                          fn-bpnp-credit-proposal-kind
                          fn-bpnp-domain-recover-eventp fn-bpnp-conflict-held
                          fn-bpnp-with-waits fn-bpnp-with-credit
                          fn-bpnp-with-runtime fn-bpnf-with-base
                          fn-bpnf-state-with-arrival
                          fn-bpnf-issued fn-bpnf-waits fn-bpah-delivery-uncertainp
                          fn-bpnf-answer fn-bpnf-answer-state fn-bpnf-answer-effects
                          fn-bpn-nth fn-cbor-ag-car
                          nth-update-nth true-listp-update-nth fn-bpn-nth-is-nth-on-true-lists nth-0-cons nth-add1 (:e binary-+) (:e nth) len-update-nth (:e len) true-listp
                          car-cons cdr-cons natp zp nfix
                          (:e zp) (:e natp) (:e fn-cbor-ag-car) (:e fn-bpn-nth)
                          (:e equal) (:e not) (:e nfix))
                        (theory 'minimal-theory))))))

(local
 (defthm bprsend-uncertain-transfer-proposal
   (let* ((jobs (fn-bpn-machine-state-jobs base))
          (job (fn-bpn-find-job key jobs))
          (token (fn-bpn-machine-state-next-token base))
          (low (fn-bpn-step base (list :forward-result key :uncertain))))
     (implies (and (fn-bpn-machine-statep base)
                   (not (fn-bpn-machine-state-fenced base))
                   (not (fn-bpn-machine-state-pending base))
                   job
                   (equal (fn-bpn-job-status job) :attempting)
                   (< token *fn-bpn-machine-max-records*))
              (and (equal (fn-bpn-answer-effects low)
                          (list (list :persist token
                                      (list :requeued token (nth 0 key) (nth 1 key)
                                            (nth 2 key) :uncertain :requeued))))
                   (equal (fn-bpn-machine-state-jobs (fn-bpn-answer-state low)) jobs)
                   (equal (fn-bpn-machine-state-contacts (fn-bpn-answer-state low))
                          (fn-bpn-machine-state-contacts base))
                   (not (fn-bpn-machine-state-fenced (fn-bpn-answer-state low)))
                   (equal (fn-bpn-machine-state-next-token (fn-bpn-answer-state low))
                          token)
                   (equal (fn-bpn-machine-state-pending (fn-bpn-answer-state low))
                          (fn-bpn-make-pending
                           token
                           (list :requeued token (nth 0 key) (nth 1 key)
                                 (nth 2 key) :uncertain :requeued)
                           (list (list :transport (nth 0 key) (nth 1 key)
                                       (nth 2 key) :attempted)
                                 (list :forward-refused (nth 0 key) (nth 1 key)
                                       (nth 2 key) :uncertain))
                           (list :bundle-queue-refused (nth 0 key) (nth 1 key)
                                 (nth 2 key) :result-persistence-refused)
                           (list :bundle-queue-uncertain (nth 0 key) (nth 1 key)
                                 (nth 2 key) :result-persistence))))))
   :hints (("Goal" :do-not-induct t
            :in-theory (union-theories
                        '(fn-bpn-step fn-bpn-dispatch fn-bpn-forward-result-step
                          fn-bpn-propose
                          fn-bpn-state-with-accessors
                          fn-bpn-answer-constructor-accessors
                          car-cons cdr-cons nth (:e zp) (:e eql) not
                          (:e nth) (:e car) (:e equal) (:e not))
                        (theory 'minimal-theory))))))

(local
 (defthm bprsend-make-pending-is-a-cons
   (consp (fn-bpn-make-pending token record success refusal uncertain))
   :hints (("Goal" :in-theory (enable fn-bpn-make-pending)))
   :rule-classes :type-prescription))

(local
 (defthm bprsend-state-with-differs-by-token
   (implies (not (equal next-token (fn-bpn-machine-state-next-token other)))
            (not (equal (fn-bpn-state-with st jobs contacts pending fenced
                                           next-token)
                        other)))
   :hints (("Goal" :in-theory (union-theories '(fn-bpn-state-with-accessors)
                                              (theory 'minimal-theory))))))

(local
 (defthm bprsend-find-job-of-replace-same-key
   (implies (and (fn-bpn-find-job key jobs)
                 (equal (fn-bpn-job-key r) key))
            (equal (fn-bpn-find-job key (fn-bpn-replace-job key r jobs)) r))
   :hints (("Goal" :induct (fn-bpn-replace-job key r jobs)
            :in-theory (enable fn-bpn-replace-job fn-bpn-find-job)))))

(local
 (defthm bprsend-job-with-status-fields
   (and (equal (fn-bpn-job-status (fn-bpn-job-with-status job status token)) status)
        (equal (fn-bpn-job-peer (fn-bpn-job-with-status job status token))
               (fn-bpn-job-peer job)))
   :hints (("Goal" :in-theory (enable fn-bpn-job-with-status)))))

(local
 (defthm bprsend-found-key-is-typed
   (implies (and (fn-bpn-job-listp jobs) (fn-bpn-find-job key jobs))
            (fn-bpn-keyp key))
   :hints (("Goal" :use (fn-bpn-key-of-found-job fn-bpn-find-job-is-a-job
                         (:instance fn-bpn-job-key-is-typed
                                    (job (fn-bpn-find-job key jobs))))
            :in-theory (theory 'minimal-theory)))))

(local
 (defthm bprsend-uncertain-then-durable-requeues
   (let* ((jobs (fn-bpn-machine-state-jobs base))
          (job (fn-bpn-find-job key jobs))
          (token (fn-bpn-machine-state-next-token base))
          (b1 (fn-bpn-answer-state
               (fn-bpn-step base (list :forward-result key :uncertain))))
          (low2 (fn-bpn-step b1 (list :persist-result token :durable)))
          (b2 (fn-bpn-answer-state low2)))
     (implies (and (fn-bpn-lifecycle-invariantp base)
                   (not (fn-bpn-machine-state-fenced base))
                   (not (fn-bpn-machine-state-pending base))
                   job
                   (equal (fn-bpn-job-status job) :attempting)
                   (< token *fn-bpn-machine-max-records*))
              (and (equal (fn-bpn-answer-effects low2)
                          (list (list :transport (nth 0 key) (nth 1 key)
                                      (nth 2 key) :attempted)
                                (list :forward-refused (nth 0 key) (nth 1 key)
                                      (nth 2 key) :uncertain)))
                   (equal (fn-bpn-find-job key (fn-bpn-machine-state-jobs b2))
                          (fn-bpn-job-with-status job :queued token))
                   (not (fn-bpn-machine-state-fenced b2))
                   (not (fn-bpn-machine-state-pending b2)))))
   :hints (("Goal" :do-not-induct t
            :expand ((fn-bpn-step (fn-bpn-answer-state (fn-bpn-step base (list :forward-result key :uncertain))) (list :persist-result (fn-bpn-machine-state-next-token base) :durable)))
            :use ((:instance fn-bpn-step-preserves-lifecycle-invariant
                             (st base)
                             (event (list :forward-result key :uncertain)))
                  (:instance fn-bpn-lifecycle-invariant-authorizes-pending
                             (st (fn-bpn-answer-state
                                  (fn-bpn-step base (list :forward-result key :uncertain)))))
                  (:instance fn-bpn-lifecycle-invariant-implies-machine-invariant
                             (st base))
                  (:instance fn-bpn-machine-invariant-components (st base))
                  (:instance fn-bpn-lifecycle-invariant-implies-machine-invariant
                             (st (fn-bpn-answer-state
                                  (fn-bpn-step base (list :forward-result key :uncertain)))))
                  (:instance fn-bpn-machine-invariant-components
                             (st (fn-bpn-answer-state
                                  (fn-bpn-step base (list :forward-result key :uncertain)))))
                  (:instance fn-bpn-machine-statep-components (st base))
                  (:instance bprsend-found-key-is-typed
                             (jobs (fn-bpn-machine-state-jobs base)))
                  (:instance fn-bpn-key-reconstruction))
            :in-theory (union-theories
                        '(bprsend-uncertain-transfer-proposal (:type-prescription bprsend-make-pending-is-a-cons) bprsend-state-with-differs-by-token fn-cbor-ag-car fn-cbor-ag-cdr
                          bprsend-find-job-of-replace-same-key
                          fn-bpn-job-key-of-job-with-status
                          fn-bpn-key-of-found-job
                          fn-bpn-machine-eventp fn-bpn-eventp fn-bpn-member
                          fn-bpn-dispatch fn-bpn-persist-result-step
                          fn-bpn-apply-record fn-bpn-record-token fn-bpn-record-key
                          fn-bpn-nth-is-nth-on-true-lists (:e natp) nth-add1 nth-0-cons
                          fn-bpn-state-with-accessors
                          fn-bpn-pending-constructor-accessors
                          fn-bpn-answer-constructor-accessors
                          car-cons cdr-cons nth true-listp len
                          (:e zp) (:e eql) not (:e binary-+) (:e fix)
                          (:e nth) (:e car) (:e equal) (:e not) (:e len))
                        (theory 'minimal-theory))))))

(local
 (defthm bprsend-queued-job-is-found-for-its-peer
   (implies (and (fn-bpn-find-job key jobs)
                 (equal (fn-bpn-job-status (fn-bpn-find-job key jobs)) :queued))
            (fn-bpn-find-queued-for-peer
             (fn-bpn-job-peer (fn-bpn-find-job key jobs)) jobs))
   :hints (("Goal" :induct (fn-bpn-find-job key jobs)
            :in-theory (enable fn-bpn-find-job fn-bpn-find-queued-for-peer)))))

(local
 (defthm bprsend-job-with-status-is-a-cons
   (consp (fn-bpn-job-with-status job status token))
   :hints (("Goal" :in-theory (enable fn-bpn-job-with-status fn-bpn-make-job)))
   :rule-classes :type-prescription))

;; KEYSTONE (d).  Over the called fn-bpnp-step, on the transfer outcome the
;; host reports (fnn-bps-send-effect, host/native/bp-service.lisp): the one
;; effect is the :requeued record's persistence; the jobs are unchanged
;; (the job is still :attempting, its durable record kept); the base is not
;; fenced, nothing is issued and no delivery is uncertain; the proposal's
;; success effects are the :attempted transport and the retained report;
;; and neither the effects nor the success effects release or prepare a
;; receipt (the form of fn-bpnp-step-emits-no-release-and-no-receipt-prepare).

(defthm fn-bpnp-uncertain-receipt-transfer-keeps-the-job-owed
  (let* ((base (fn-bpnf-base st))
         (jobs (fn-bpn-machine-state-jobs base))
         (job (fn-bpn-find-job key jobs))
         (token (fn-bpn-machine-state-next-token base))
         (record (list :requeued token (nth 0 key) (nth 1 key) (nth 2 key)
                       :uncertain :requeued))
         (ans (fn-bpnp-step st (list :base (list :forward-result key :uncertain))))
         (next (fn-bpnf-answer-state ans))
         (next-base (fn-bpnf-base next))
         (pending (fn-bpn-machine-state-pending next-base)))
    (implies (and (fn-bpn-machine-statep base)
                  (not (fn-bpnf-issued st))
                  (not (fn-bpah-delivery-uncertainp st))
                  (not (fn-bpn-machine-state-fenced base))
                  (not (fn-bpn-machine-state-pending base))
                  job
                  (equal (fn-bpn-job-status job) :attempting)
                  (< token *fn-bpn-machine-max-records*))
             (and (equal (fn-bpnf-answer-effects ans)
                         (list (list :persist token record)))
                  (equal (fn-bpn-machine-state-jobs next-base) jobs)
                  (not (fn-bpn-machine-state-fenced next-base))
                  (not (fn-bpnf-issued next))
                  (not (fn-bpah-delivery-uncertainp next))
                  (equal (fn-bpn-pending-record pending) record)
                  (equal (fn-bpn-pending-success-effects pending)
                         (list (list :transport (nth 0 key) (nth 1 key)
                                     (nth 2 key) :attempted)
                               (list :forward-refused (nth 0 key) (nth 1 key)
                                     (nth 2 key) :uncertain)))
                  (not (fn-bpn-effect-kind-memberp
                        :release (fn-bpnf-answer-effects ans)))
                  (not (fn-bpn-effect-kind-memberp
                        :receipt-prepare (fn-bpnf-answer-effects ans)))
                  (not (fn-bpn-effect-kind-memberp
                        :release (fn-bpn-pending-success-effects pending)))
                  (not (fn-bpn-effect-kind-memberp
                        :receipt-prepare
                        (fn-bpn-pending-success-effects pending))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnp-step-base-event-refines-fn-bpn-step
                            (e (list :forward-result key :uncertain)))
                 (:instance bprsend-base-event-keeps-the-gates-open
                            (e (list :forward-result key :uncertain))))
           :in-theory (union-theories
                       '(fn-bpn-pending-constructor-accessors bprsend-uncertain-transfer-proposal
                         fn-bpn-effect-kind-memberp
                         car-cons cdr-cons (:e equal) (:e not))
                       (theory 'minimal-theory))))
  :rule-classes nil)

;; KEYSTONE (e).  After the durable :requeued record the job is :queued
;; again with its own identity (fn-bpn-job-with-status keeps every field but
;; the status and last token), the effects are exactly the transport
;; observation and the retention report (no :forwarded, no release), and the
;; node's receipt contact event for the job's peer is open again: the next
;; contact offers it (with fn-bpnp-receipt-contact-offers-the-queued-job).

(defthm fn-bpnp-receipt-reoffer-after-uncertain
  (let* ((base (fn-bpnf-base st))
         (jobs (fn-bpn-machine-state-jobs base))
         (job (fn-bpn-find-job key jobs))
         (token (fn-bpn-machine-state-next-token base))
         (peer (fn-bpn-job-peer job))
         (s1 (fn-bpnf-answer-state
              (fn-bpnp-step st (list :base (list :forward-result key :uncertain)))))
         (ans2 (fn-bpnp-step s1 (list :base (list :persist-result token :durable))))
         (s2 (fn-bpnf-answer-state ans2)))
    (implies (and (fn-bpn-lifecycle-invariantp base)
                  (not (fn-bpnf-issued st))
                  (not (fn-bpah-delivery-uncertainp st))
                  (not (fn-bpn-machine-state-fenced base))
                  (not (fn-bpn-machine-state-pending base))
                  job
                  (equal (fn-bpn-job-status job) :attempting)
                  (< token *fn-bpn-machine-max-records*))
             (and (equal (fn-bpnf-answer-effects ans2)
                         (list (list :transport (nth 0 key) (nth 1 key)
                                     (nth 2 key) :attempted)
                               (list :forward-refused (nth 0 key) (nth 1 key)
                                     (nth 2 key) :uncertain)))
                  (equal (fn-bpn-find-job
                          key (fn-bpn-machine-state-jobs (fn-bpnf-base s2)))
                         (fn-bpn-job-with-status job :queued token))
                  (equal (fn-bpnp-receipt-contact-event s2 peer)
                         (list :contact peer t)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnp-step-base-event-refines-fn-bpn-step
                            (e (list :forward-result key :uncertain)))
                 (:instance bprsend-base-event-keeps-the-gates-open
                            (e (list :forward-result key :uncertain)))
                 (:instance fn-bpnp-step-base-event-refines-fn-bpn-step
                            (st (fn-bpnf-answer-state
                                 (fn-bpnp-step st (list :base (list :forward-result key :uncertain)))))
                            (e (list :persist-result
                                     (fn-bpn-machine-state-next-token (fn-bpnf-base st))
                                     :durable)))
                 (:instance bprsend-base-event-keeps-the-gates-open
                            (st (fn-bpnf-answer-state
                                 (fn-bpnp-step st (list :base (list :forward-result key :uncertain)))))
                            (e (list :persist-result
                                     (fn-bpn-machine-state-next-token (fn-bpnf-base st))
                                     :durable)))
                 (:instance fn-bpn-lifecycle-invariant-implies-machine-invariant
                            (st (fn-bpnf-base st)))
                 (:instance fn-bpn-machine-invariant-components
                            (st (fn-bpnf-base st)))
                 (:instance fn-bpn-machine-statep-components
                            (st (fn-bpnf-base st)))
                 (:instance fn-bpn-find-job-is-a-job
                            (jobs (fn-bpn-machine-state-jobs (fn-bpnf-base st))))
                 (:instance bprsend-queued-job-is-found-for-its-peer
                            (jobs (fn-bpn-machine-state-jobs
                                   (fn-bpn-answer-state
                                    (fn-bpn-step
                                     (fn-bpn-answer-state
                                      (fn-bpn-step (fn-bpnf-base st)
                                                   (list :forward-result key :uncertain)))
                                     (list :persist-result
                                           (fn-bpn-machine-state-next-token (fn-bpnf-base st))
                                           :durable))))))
                 (:instance fn-bpn-jobp-components
                            (job (fn-bpn-find-job key (fn-bpn-machine-state-jobs (fn-bpnf-base st))))))
           :in-theory (union-theories
                       '(bprsend-uncertain-then-durable-requeues (:type-prescription bprsend-job-with-status-is-a-cons)
                         bprsend-job-with-status-fields
                         bprsend-ready-peer-has-a-queued-job
                         fn-bpnp-receipt-contact-event
                         (:e equal) (:e not))
                       (theory 'minimal-theory))))
  :rule-classes nil)

;; Once per contact is the host's and the lower machine's, not a theorem
;; here: a durable :attempting record makes the job :attempting (not
;; :queued) until its transfer result, and fnn-bpc-drive-contact stops the
;; contact at the first outcome that is not :accepted.  Open (lane
;; bp-budgets-receipts): the ACL2 statement over fn-bpn-apply-record.

(verify-guards fn-bpn-ready-peers)
(verify-guards fn-bpnp-receipt-contact-event)
