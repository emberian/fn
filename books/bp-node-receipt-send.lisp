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

;; Once per contact is the host's and the lower machine's, not a theorem
;; here: a durable :attempting record makes the job :attempting (not
;; :queued) until its transfer result, and fnn-bpc-drive-contact stops the
;; contact at the first outcome that is not :accepted.  Open (lane
;; bp-budgets-receipts): the ACL2 statement over fn-bpn-apply-record.

(verify-guards fn-bpn-ready-peers)
(verify-guards fn-bpnp-receipt-contact-event)
