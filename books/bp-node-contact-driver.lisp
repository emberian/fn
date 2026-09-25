; The base contact driver: routed queued jobs, offered once per contact
; (spec bp-node-machine 4.6 and 4.3.2; PRF-103).
;
; A base FNBS job (A's request carrier from `bp-obligation request', B's
; receipts and status reports from `bp-node serve'/dispatch and `bp-contact
; tick') is offered on a contact by the lower machine: fn-bpn-contact-step
; proposes the :attempting record of the first queued job for the peer, and
; its success effect is the :cl-send on that job's durable route.  Two
; decisions sat in the host: which hop the job goes to (the CONTACT-HOST:PORT
; it was queued with), and when a contact stops offering (the host loop in
; fnn-bpc-drive-contact stopped at the first transfer that was not
; accepted).  Both are ACL2's here.
;
;   queue time    the host queues a job only on the route
;                 fn-bprt-job-route answers (books/bp-route-jobs.lisp); a
;                 destination the table routes nowhere is not queued, and
;                 its obligation stays owed where it is;
;   contact time  fn-bpnp-contact-next is the one question the host asks
;                 before each offer of a contact.  Its answer is
;                   (:offer EVENT OFFERED EID)  drive EVENT through
;                        fn-bpnp-step; OFFERED is the contact's offered keys
;                        with this job's; EID the node ID the hop's contact
;                        must announce (nil when routing is not in force);
;                   (:held KEY DECISION)  offer nothing; the job keeps its
;                        durable row and the contact closes;
;                   (:close)  nothing more to offer on this contact.
;
; ROUTING is (:table TABLE) with the route table fn-bprt-table builds from
; the configuration, or nil for a verb that has no Store (`bp-service run',
; and `bp-service resume' or `bp-contact tick' without STORE): those keep the
; address they were queued with.
(in-package "ACL2")
(include-book "bp-node-receipt-send")
(include-book "bp-route-jobs")
(set-verify-guards-eagerness 0)

(defun fn-bpnp-contact-job (st peer)
  (declare (xargs :guard t))
  (fn-bpn-find-queued-for-peer
   peer (fn-bpn-machine-state-jobs (fn-bpnf-base st))))

(defun fn-bpnp-contact-next (st peer routing offered)
  (declare (xargs :guard t))
  (let* ((event (fn-bpnp-receipt-contact-event st peer))
         (job (fn-bpnp-contact-job st peer))
         (key (fn-bpn-job-key job)))
    (cond
     ((not event) (list :close))
     ; Once per contact: a job this contact already offered is queued
     ; again only because its transfer was not accepted (the lower
     ; machine's :requeued record) or its :attempting record was not
     ; published; it waits for the next contact.
     ((fn-bpn-member key offered) (list :close))
     ((not (equal (fn-bpn-nth 0 routing) :table))
      (list :offer (list :base event) (cons key offered) nil))
     (t
      (let ((decision (fn-bprt-send-decision
                       (fn-bpn-job-route job) (fn-bpaj-eid-text peer)
                       (fn-bpn-nth 1 routing))))
        (cond
         ((not (equal (fn-bpn-nth 0 decision) :send))
          (list :held key (fn-bpn-nth 1 decision)))
         ; The job's durable route is not the hop the table names now: it
         ; is never offered to another address than its durable record
         ; holds (spec 4.6: a durable re-route record is open).
         ((not (equal (fn-bpn-nth 1 decision) (fn-bpn-job-route job)))
          (list :held key :route-changed))
         (t (list :offer (list :base event) (cons key offered)
                  (fn-bpn-nth 3 decision)))))))))

;; ---------------------------------------------------------------------
;; Facts about the driver's answer.

(local
 (defthm bpcd-offer-shape
   (let ((d (fn-bpnp-contact-next st peer routing offered)))
     (implies (equal (car d) :offer)
              (and (fn-bpnp-receipt-contact-event st peer)
                   (equal (cadr d)
                          (list :base (fn-bpnp-receipt-contact-event st peer)))
                   (equal (caddr d)
                          (cons (fn-bpn-job-key (fn-bpnp-contact-job st peer))
                                offered))
                   (not (fn-bpn-member (fn-bpn-job-key (fn-bpnp-contact-job st peer))
                                       offered)))))
   :hints (("Goal" :do-not-induct t
            :in-theory (union-theories
                        '(fn-bpnp-contact-next fn-bpn-nth fn-cbor-ag-car car-cons cdr-cons
                          (:e equal) (:e car) (:e cdr))
                        (theory 'minimal-theory))))))

(local
 (defthm bpcd-member-is-member-equal
   (iff (fn-bpn-member x xs) (member-equal x xs))
   :hints (("Goal" :in-theory (enable fn-bpn-member)))))

(local
 (defthm bpcd-send-decision-shape
   (let ((d (fn-bprt-send-decision route dest table)))
     (and (consp d) (consp (cdr d))
          (implies (equal (car d) :send)
                   (and (consp (cddr d)) (consp (cdddr d))))))
   :hints (("Goal" :in-theory (enable fn-bprt-send-decision)))))

;; ---------------------------------------------------------------------
;; KEYSTONE (routing).  Over the step the host calls on the driver's event:
;; when routing is in force and the driver offers, the step's one effect
;; persists the :attempting record of the first queued job for the peer,
;; the :cl-send it owes on success carries that job's durable route, and
;; that route is the one fn-bprt-send-decision names over the table: the
;; contact port of the boundary fn-bprt-next-hop chooses for the job's
;; destination among the boundaries that have a contact.  The EID the host
;; must expect from that contact is the decision's.
(defthm fn-bpnp-contact-offer-is-the-routed-hop
  (let* ((d (fn-bpnp-contact-next st peer (list :table table) offered))
         (base (fn-bpnf-base st))
         (job (fn-bpnp-contact-job st peer))
         (key (fn-bpn-job-key job))
         (token (fn-bpn-machine-state-next-token base))
         (dest (fn-bpaj-eid-text peer))
         (decision (fn-bprt-send-decision (fn-bpn-job-route job) dest table))
         (ans (fn-bpnp-step st (cadr d)))
         (pending (fn-bpn-machine-state-pending
                   (fn-bpnf-base (fn-bpnf-answer-state ans)))))
    (implies (and (fn-bpn-machine-statep base)
                  (equal (car d) :offer)
                  (< token *fn-bpn-machine-max-records*))
             (and (equal (fn-bpnf-answer-effects ans)
                         (list (list :persist token
                                     (list :attempting token (nth 0 key)
                                           (nth 1 key) (nth 2 key)))))
                  (equal (fn-bpn-pending-success-effects pending)
                         (list (list :cl-send (fn-bpn-job-route job) peer key
                                     (fn-bpn-job-wire job))))
                  (equal (fn-bpn-job-status job) :queued)
                  (equal (fn-bpn-job-peer job) peer)
                  (equal (car decision) :send)
                  (equal (fn-bpn-job-route job) (cadr decision))
                  (equal (caddr decision)
                         (fn-bprt-next-hop dest table (fn-bprt-contactable table)))
                  (equal (caddr (fn-bpn-job-route job))
                         (fn-bprt-route-port
                          (fn-bprt-hop-route dest table
                                             (fn-bprt-contactable table))))
                  (equal (cadddr d) (cadddr decision)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnp-receipt-contact-offers-the-queued-job)
                 (:instance fn-bprt-send-decision-offers-only-the-routed-hop
                            (route (fn-bpn-job-route (fn-bpnp-contact-job st peer)))
                            (dest (fn-bpaj-eid-text peer))))
           :in-theory (union-theories
                       '(fn-bpnp-contact-next fn-bpnp-contact-job
                         bpcd-send-decision-shape
                         fn-bpn-nth fn-cbor-ag-car car-cons cdr-cons
                         (:e zp) (:e binary-+) (:e unary--) (:e equal) (:e car)
                         (:e cdr) (:e fn-bpn-nth) natp (:e natp))
                       (theory 'minimal-theory))))
  :rule-classes nil)

;; KEYSTONE (no route).  With routing in force and no route matching the
;; peer's destination, the driver never offers: the host drives no event,
;; so the job keeps its durable row and its obligation.  When the peer has
;; an offerable job the answer names it and the decision.
(defthm fn-bpnp-contact-holds-an-unrouted-job
  (implies (atom (fn-bprt-matching (fn-bpaj-eid-text peer) table))
           (and (not (equal (car (fn-bpnp-contact-next
                                  st peer (list :table table) offered))
                            :offer))
                (implies (and (fn-bpnp-receipt-contact-event st peer)
                              (not (member-equal
                                    (fn-bpn-job-key (fn-bpnp-contact-job st peer))
                                    offered)))
                         (equal (fn-bpnp-contact-next
                                 st peer (list :table table) offered)
                                (list :held
                                      (fn-bpn-job-key (fn-bpnp-contact-job st peer))
                                      :no-route)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bprt-send-decision-holds-without-a-route
                            (route (fn-bpn-job-route (fn-bpnp-contact-job st peer)))
                            (dest (fn-bpaj-eid-text peer))))
           :in-theory (union-theories
                       '(fn-bpnp-contact-next bpcd-member-is-member-equal
                         fn-bpn-nth fn-cbor-ag-car car-cons cdr-cons
                         (:e zp) (:e binary-+) (:e unary--) (:e equal) (:e car)
                         (:e cdr) (:e fn-bpn-nth) natp (:e natp))
                       (theory 'minimal-theory)))))

;; ---------------------------------------------------------------------
;; Once per contact.  The host's contact loop (host/native/bp-contact.lisp
;; fnn-bpc-drive-contact) asks fn-bpnp-contact-next at each state it
;; reaches, drives the event it is given, threads the OFFERED it is given,
;; and ends at the first answer that is not an offer.  Whatever the states
;; between two questions are (the host drives the persist, transfer and
;; result effects in between), the keys the contact offers are:

(defun fn-bpnp-contact-offers (sts peer routing offered)
  (declare (xargs :guard t))
  (if (atom sts) nil
    (let ((d (fn-bpnp-contact-next (car sts) peer routing offered)))
      (if (equal (fn-bpn-nth 0 d) :offer)
          (cons (fn-bpn-nth 0 (fn-bpn-nth 2 d))
                (fn-bpnp-contact-offers (cdr sts) peer routing
                                        (fn-bpn-nth 2 d)))
        nil))))

(local
 (defthm bpcd-offer-threads-offered
   (let ((d (fn-bpnp-contact-next st peer routing offered)))
     (implies (equal (fn-bpn-nth 0 d) :offer)
              (and (consp (fn-bpn-nth 2 d))
                   (equal (cdr (fn-bpn-nth 2 d)) offered)
                   (not (member-equal (car (fn-bpn-nth 2 d)) offered)))))
   :hints (("Goal" :do-not-induct t
            :in-theory (union-theories
                        '(fn-bpnp-contact-next bpcd-send-decision-shape
                          bpcd-member-is-member-equal fn-bpn-nth fn-cbor-ag-car
                          car-cons cdr-cons (:e zp) (:e binary-+) (:e equal)
                          (:e car) (:e cdr) natp (:e natp))
                        (theory 'minimal-theory))))))

(local
 (defthm bpcd-offers-avoid-offered
   (implies (member-equal k (fn-bpnp-contact-offers sts peer routing offered))
            (not (member-equal k offered)))
   :hints (("Goal" :induct (fn-bpnp-contact-offers sts peer routing offered)
            :in-theory (union-theories '(fn-bpnp-contact-offers member-equal no-duplicatesp-equal
                                         (:e fn-bpn-nth) (:e equal) (:e zp)
                                         fn-bpn-nth fn-cbor-ag-car natp (:e natp)
                                         car-cons cdr-cons )
                                       (theory 'minimal-theory)))
           ("Subgoal *1/2" :use ((:instance bpcd-offer-threads-offered
                                  (st (car sts))))))))

;; KEYSTONE (once per contact).  Along any sequence of states, the keys one
;; contact offers are pairwise distinct and none was offered before the
;; sequence began: each owed job is offered at most once per contact.
(defthm fn-bpnp-contact-offers-each-job-at-most-once
  (let ((offers (fn-bpnp-contact-offers sts peer routing offered)))
    (and (no-duplicatesp-equal offers)
         (implies (member-equal k offers)
                  (not (member-equal k offered)))))
  :hints (("Goal" :induct (fn-bpnp-contact-offers sts peer routing offered)
           :in-theory (union-theories '(fn-bpnp-contact-offers member-equal no-duplicatesp-equal
                                         (:e fn-bpn-nth) (:e equal) (:e zp)
                                         fn-bpn-nth fn-cbor-ag-car natp (:e natp)
                                         car-cons cdr-cons bpcd-offers-avoid-offered)
                                       (theory 'minimal-theory)))
          ("Subgoal *1/2" :use ((:instance bpcd-offer-threads-offered
                                 (st (car sts)))
                                (:instance bpcd-offers-avoid-offered
                                 (k (car (fn-bpn-nth 2 (fn-bpnp-contact-next
                                                        (car sts) peer routing
                                                        offered))))
                                 (sts (cdr sts))
                                 (offered (fn-bpn-nth 2 (fn-bpnp-contact-next
                                                         (car sts) peer routing
                                                         offered))))))))

;; The first queued job for a peer is :queued and names the peer.
(local
 (defthm bpcd-queued-job-names-the-peer
   (implies (fn-bpn-find-queued-for-peer peer jobs)
            (and (equal (fn-bpn-job-peer (fn-bpn-find-queued-for-peer peer jobs))
                        peer)
                 (equal (fn-bpn-job-status
                         (fn-bpn-find-queued-for-peer peer jobs))
                        :queued)))
   :hints (("Goal" :induct (fn-bpn-find-queued-for-peer peer jobs)
            :in-theory (union-theories '(fn-bpn-find-queued-for-peer)
                                       (theory 'minimal-theory))))))

;; KEYSTONE (every owed job is offered unless a transfer was not accepted).
;; The driver closes a contact whose base is open for offers only when the
;; peer has no queued job, or the first queued job is one this contact
;; already offered.  A job the contact offered is :queued again only through
;; the lower machine's :requeued record (a transfer that was :refused,
;; :failed or :uncertain) or an :attempting record that was not published;
;; an accepted transfer makes it :forwarded, which no record returns to
;; :queued (fn-bpn-apply-record-keeps-forwarded below).  With routing in
;; force, the other answer that ends a contact, :held, names the routing
;; decision.
(defthm fn-bpnp-contact-closes-only-when-nothing-owed-remains
  (let ((d (fn-bpnp-contact-next st peer routing offered))
        (base (fn-bpnf-base st)))
    (implies (and (not (equal (car d) :offer))
                  (not (equal (car d) :held))
                  (fn-bpp-eidp peer)
                  (not (fn-bpnf-issued st))
                  (not (fn-bpah-delivery-uncertainp st))
                  (not (fn-bpn-machine-state-fenced base))
                  (not (fn-bpn-machine-state-pending base))
                  (fn-bpnp-contact-job st peer))
             (member-equal (fn-bpn-job-key (fn-bpnp-contact-job st peer))
                           offered)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnp-receipt-contact-event-needs-a-queued-job))
           :in-theory (union-theories
                       '(fn-bpnp-contact-next fn-bpnp-contact-job
                         bpcd-member-is-member-equal bpcd-queued-job-names-the-peer
                         fn-bpn-nth fn-cbor-ag-car car-cons cdr-cons
                         (:e zp) (:e binary-+) (:e unary--) (:e equal) (:e car)
                         (:e cdr) (:e fn-bpn-nth) natp (:e natp))
                       (theory 'minimal-theory))))
  :rule-classes nil)

;; No lifecycle record returns a :forwarded job to :queued: applying any
;; record (the one function that changes a job's status, called by the
;; lower machine's :persist-result arm and by its restart replay) leaves a
;; :forwarded job :forwarded.
(local
 (defthm bpcd-find-job-of-replace-other
   (implies (and (not (equal k key))
                 (not (equal k (fn-bpn-job-key new))))
            (equal (fn-bpn-find-job k (fn-bpn-replace-job key new jobs))
                   (fn-bpn-find-job k jobs)))
   :hints (("Goal" :induct (fn-bpn-replace-job key new jobs)
            :in-theory (union-theories '(fn-bpn-replace-job fn-bpn-find-job
                                         car-cons cdr-cons)
                                       (theory 'minimal-theory))))))

(local
 (defthm bpcd-find-job-of-append
   (implies (fn-bpn-find-job k jobs)
            (equal (fn-bpn-find-job k (fn-bpn-append jobs more))
                   (fn-bpn-find-job k jobs)))
   :hints (("Goal" :induct (fn-bpn-find-job k jobs)
            :expand ((fn-bpn-append jobs more)
                     (:free (x y) (fn-bpn-find-job k (cons x y))))
            :in-theory (union-theories '(fn-bpn-append fn-bpn-find-job
                                         car-cons cdr-cons)
                                       (theory 'minimal-theory))))))

(local
 (defthm bpcd-job-key-of-with-status
   (equal (fn-bpn-job-key (fn-bpn-job-with-status job status token))
          (fn-bpn-job-key job))
   :hints (("Goal" :in-theory (enable fn-bpn-job-key fn-bpn-job-with-status)))))

(local
 (defthm bpcd-found-job-has-its-key
   (implies (fn-bpn-find-job key jobs)
            (equal (fn-bpn-job-key (fn-bpn-find-job key jobs)) key))
   :hints (("Goal" :induct (fn-bpn-find-job key jobs)
            :in-theory (union-theories '(fn-bpn-find-job)
                                       (theory 'minimal-theory))))))

(local
 (defthm bpcd-replace-keeps-forwarded
   (implies (and (equal (fn-bpn-job-status (fn-bpn-find-job k jobs)) :forwarded)
                 (fn-bpn-find-job key jobs)
                 (not (equal (fn-bpn-job-status (fn-bpn-find-job key jobs))
                             :forwarded)))
            (equal (fn-bpn-find-job
                    k (fn-bpn-replace-job
                       key (fn-bpn-job-with-status (fn-bpn-find-job key jobs)
                                                   status token)
                       jobs))
                   (fn-bpn-find-job k jobs)))
   :hints (("Goal" :do-not-induct t :cases ((equal k key))
            :use ((:instance bpcd-find-job-of-replace-other
                             (new (fn-bpn-job-with-status
                                   (fn-bpn-find-job key jobs) status token))))
            :in-theory (union-theories '(bpcd-job-key-of-with-status
                                         bpcd-found-job-has-its-key)
                                       (theory 'minimal-theory))))))

(local
 (defthm bpcd-append-keeps-forwarded
   (implies (equal (fn-bpn-job-status (fn-bpn-find-job k jobs)) :forwarded)
            (equal (fn-bpn-find-job k (fn-bpn-append jobs more))
                   (fn-bpn-find-job k jobs)))
   :hints (("Goal" :use ((:instance bpcd-find-job-of-append))
            :in-theory (union-theories '((:e fn-bpn-job-status))
                                       (theory 'minimal-theory))))))

(defthm fn-bpn-apply-record-keeps-forwarded
  (implies (equal (fn-bpn-job-status
                   (fn-bpn-find-job k (fn-bpn-machine-state-jobs st)))
                  :forwarded)
           (equal (fn-bpn-job-status
                   (fn-bpn-find-job
                    k (fn-bpn-machine-state-jobs (fn-bpn-apply-record st record))))
                  :forwarded))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories
                       '(fn-bpn-apply-record fn-bpn-record-applicablep
                         fn-bpn-state-with fn-bpn-machine-constructor-accessors
                         bpcd-replace-keeps-forwarded bpcd-append-keeps-forwarded
                         (:e equal) (:e fn-bpn-member) fn-bpn-member
                         car-cons cdr-cons)
                       (theory 'minimal-theory)))))
