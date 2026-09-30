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
;   contact time  the host asks fn-bpnjc-contact-next (books/bp-node-job-cursor.lisp),
;                 equal to fn-bpnj-contact-next (books/bp-node-job-offer.lisp,
;                 the fair selection, whose keystones carry PRF-103's routed
;                 hop and once-per-contact claims).  The first-queued-job
;                 driver fn-bpnp-contact-next that stood here had no caller
;                 and was deleted (assurance-hygiene-6).
;
; ROUTING is (:table TABLE) with the route table fn-bprt-table builds from
; the configuration, or nil for a verb that has no Store (`bp-service run',
; and `bp-service resume' or `bp-contact tick' without STORE): those keep the
; address they were queued with.
(in-package "ACL2")
(include-book "bp-node-receipt-send")
(include-book "bp-route-jobs")
(set-verify-guards-eagerness 0)

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
