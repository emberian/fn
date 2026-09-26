; The fragment family's rows and the node's job table agree (PRF-121, item 3).
;
; The job table is the held list itself: slots 10 to 13 of a held row are its
; dispatch record, next hop, job state and kind-8 attempt.  A fragment row is
; a carrier: the progress selector never dispatches it (fn-bpnp-live-pendingp
; and fn-bpnp-oldest-uncertain-local both require a non-fragment), so its one
; job is reassembly.  The relation says so: every active fragment row carries
; exactly the reassembly job ((:dispatch-pending), no dispatch record, no next
; hop, no attempt).  Under it, the kind-18 family replacement, which removes
; its source rows from the held list, discards carriers only: every consumed
; row had no unfinished forwarding or delivery job, and the whole row it
; installs carries the family's job on as (:dispatch-pending).
;
; Host path: host/native/bp-service.lisp fnn-bps-fragment-progress asks
; fn-bpnf-family-next for a ready anchor, then fnn-bps-foundation-step calls
; fn-bpnp-step with (:family A observation) and, after the kind-18
; publication, with (:persist-result EPOCH OP RESULT).  The theorems below
; are over fn-bpnp-step on exactly those two events.
(in-package "ACL2")
(include-book "bp-node-progress")
(set-verify-guards-eagerness 0)

(defun fn-bpnf-reassembly-job-onlyp (h)
  (declare (xargs :guard t))
  (and (null (fn-bpn-nth 10 h))
       (null (fn-bpn-nth 11 h))
       (equal (fn-bpn-nth 12 h) '(:dispatch-pending))
       (null (fn-bpn-nth 13 h))))

(defun fn-bpnf-rows-job-onlyp (rows)
  (declare (xargs :guard t))
  (if (consp rows)
      (and (fn-bpnf-reassembly-job-onlyp (car rows))
           (fn-bpnf-rows-job-onlyp (cdr rows)))
    t))

(defun fn-bpnf-family-jobs-agreep (held)
  (declare (xargs :guard t))
  (if (consp held)
      (and (or (not (fn-bpnf-active-fragmentp (car held)))
               (fn-bpnf-reassembly-job-onlyp (car held)))
           (fn-bpnf-family-jobs-agreep (cdr held)))
    t))

(local
 (defthm bpnfj-agreep-of-retain
   (implies (fn-bpnf-family-jobs-agreep held)
            (fn-bpnf-family-jobs-agreep
             (fn-bpnf-family-retain-other-rows held consumed)))
   :hints (("Goal" :induct (fn-bpnf-family-retain-other-rows held consumed)
            :in-theory (disable fn-bpnf-active-fragmentp
                                fn-bpnf-reassembly-job-onlyp)))))

(local
 (defthm bpnfj-active-set-rows-job-only
  (implies (fn-bpnf-family-jobs-agreep held)
           (fn-bpnf-rows-job-onlyp (fn-bpnf-active-set-rows held anchor)))
  :hints (("Goal" :induct (fn-bpnf-active-set-rows held anchor)
           :in-theory (union-theories
                       '(fn-bpnf-active-set-rows fn-bpnf-family-jobs-agreep
                         fn-bpnf-rows-job-onlyp
                         fn-bpnf-same-family-members-are-active car-cons cdr-cons)
                       (theory 'minimal-theory))))))

(local
 (defthm bpnfj-active-set-job-only
  (implies (fn-bpnf-family-jobs-agreep (fn-bpnf-held-list st))
           (fn-bpnf-rows-job-onlyp (fn-bpnf-active-set st anchor)))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-bpnf-active-set bpnfj-active-set-rows-job-only fn-bpnf-rows-job-onlyp (:e fn-bpnf-rows-job-onlyp))
                              (theory 'minimal-theory))))))

(local
 (defthm bpnfj-new-row-job-only
   (fn-bpnf-reassembly-job-onlyp
    (fn-bpnf-held p id a i s l b w an nil nil '(:dispatch-pending) nil d tk))
   :hints (("Goal" :in-theory (enable fn-bpnf-held fn-bpn-nth)))))

;; KEYSTONE.  Kind-18 replacement conserves the job table: it consumes only
;; rows whose one job was reassembly, the whole row carries the job on, and
;; the relation holds of the new held list.
(defthm fn-bpnf-family-apply-conserves-jobs
  (implies (and (fn-bpnf-family-jobs-agreep (fn-bpnf-held-list st))
                (equal (car (fn-bpnf-family-apply st record arrival)) :ready))
           (and (fn-bpnf-rows-job-onlyp
                 (cadddr (fn-bpnf-family-apply st record arrival)))
                (fn-bpnf-reassembly-job-onlyp
                 (caddr (fn-bpnf-family-apply st record arrival)))
                (fn-bpnf-family-jobs-agreep
                 (cadr (fn-bpnf-family-apply st record arrival)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories
                       '(fn-bpnf-family-apply
                         bpnfj-active-set-job-only bpnfj-agreep-of-retain
                         bpnfj-new-row-job-only fn-bpnf-family-jobs-agreep
                         car-cons cdr-cons (:e equal))
                       (theory 'minimal-theory)))))

(local
 (defthm bpnfj-held-of-state-with-arrival
  (and (equal (fn-bpnf-held-list
               (fn-bpnf-state-with-arrival b h o ho c i w e n a)) h)
       (equal (fn-bpnf-held-list (fn-bpnf-with-issued st x))
              (fn-bpnf-held-list st))
       (equal (fn-bpnf-answer-state (fn-bpnf-answer x ef)) x))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-bpnf-state-with-arrival fn-bpnf-with-issued
                                fn-bpnf-held-list fn-bpnf-answer fn-bpnf-answer-state
                                fn-bpn-nth fn-cbor-ag-car car-cons cdr-cons
                                (:e natp) (:e zp) (:e binary-+) natp zp)
                              (theory 'minimal-theory))))))

(local
 (defthm bpnfj-apply-shape
  (and (true-listp (fn-bpnf-family-apply st record arrival))
       (consp (fn-bpnf-family-apply st record arrival)))
  :hints (("Goal" :in-theory (union-theories '(fn-bpnf-family-apply)
                               (theory 'minimal-theory))))
  :rule-classes nil))

(local
 (defthm bpnfj-apply-at-ready-is-apply
  (implies (equal (fn-cbor-ag-car (fn-bpnf-family-apply-at st record arrival))
                  :ready)
           (equal (fn-bpnf-family-apply-at st record arrival)
                  (fn-bpnf-family-apply st record arrival)))
  :hints (("Goal" :in-theory (union-theories '(fn-bpnf-family-apply-at
                                               (:e fn-cbor-ag-car) (:e equal))
                               (theory 'minimal-theory))))
  :rule-classes nil))

(local
 (defthm bpnfj-nth-1 (equal (nth 1 x) (cadr x)) :hints (("Goal" :expand ((nth 1 x) (nth 0 (cdr x)))))))

(local
 (defthm bpnfj-apply-at-ready
  (implies (and (fn-bpnf-family-jobs-agreep (fn-bpnf-held-list st))
                (equal (fn-cbor-ag-car (fn-bpnf-family-apply-at st record arrival))
                       :ready))
           (fn-bpnf-family-jobs-agreep
            (fn-bpn-nth 1 (fn-bpnf-family-apply-at st record arrival))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bpnf-family-apply-conserves-jobs) (:instance bpnfj-apply-shape)
                 (:instance bpnfj-apply-at-ready-is-apply))
           :in-theory (union-theories '(fn-cbor-ag-car fn-bpn-nth-is-nth-on-true-lists bpnfj-nth-1 bpnfj-nth-1
                                        nth zp natp (:e natp) (:e zp) (:e fix)
                                        (:e binary-+) (:e unary--) (:e equal) (:e not))
                                      (theory 'minimal-theory))))))

(local
 (defthm bpnfj-persist-step
  (implies (fn-bpnf-family-jobs-agreep (fn-bpnf-held-list st))
           (fn-bpnf-family-jobs-agreep
            (fn-bpnf-held-list
             (fn-bpnf-answer-state (fn-bpnf-family-persist-step st epoch op result)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn-bpnf-family-persist-step
                                        bpnfj-held-of-state-with-arrival
                                        bpnfj-apply-at-ready (:e fn-cbor-ag-car) (:e equal) (:e fn-bpn-nth))
                                      (theory 'minimal-theory))))))

(local
 (defthm bpnfj-propose-step
  (equal (fn-bpnf-held-list
          (fn-bpnf-answer-state (fn-bpnf-family-propose-step st a obs)))
         (fn-bpnf-held-list st))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn-bpnf-family-propose-step
                                        bpnfj-held-of-state-with-arrival)
                                      (theory 'minimal-theory))))))

(local
 (defthm bpnfj-held-of-slot-writers
  (and (equal (fn-bpnf-held-list (fn-bpnp-with-waits st w)) (fn-bpnf-held-list st))
       (equal (fn-bpnf-held-list (fn-bpnp-with-credit st u d)) (fn-bpnf-held-list st))
       (equal (fn-bpnf-held-list (fn-bpnp-with-runtime st s p)) (fn-bpnf-held-list st)))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-bpnp-with-waits fn-bpnp-with-credit
                                fn-bpnp-with-runtime fn-bpnf-held-list
                                fn-bpn-nth-is-nth-on-true-lists
                                nth-update-nth true-listp-update-nth
                                (:e equal) (:e natp) (:e <) (:e nfix))
                              (theory 'minimal-theory))))))

(local
 (defun bpnfj-our-eventp (st event)
  (declare (xargs :guard t))
  (or (equal (fn-cbor-ag-car event) :family)
      (and (equal (fn-cbor-ag-car event) :persist-result)
           (fn-bpnf-family-issuedp st)))))

(local
 (defthm bpnfj-answer-effects
  (equal (fn-bpnf-answer-effects (fn-bpnf-answer x e)) e)
  :hints (("Goal" :in-theory (enable fn-bpnf-answer fn-bpnf-answer-effects fn-bpn-nth)))))

(local
 (defthm bpnfj-propose-effects
  (not (equal (fn-bpn-nth 0 (fn-bpn-nth 0 (fn-bpnf-answer-effects
                                          (fn-bpnf-family-propose-step st a obs))))
              :persist-delivery))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn-bpnf-family-propose-step bpnfj-answer-effects
                                        fn-bpn-nth fn-cbor-ag-car car-cons cdr-cons
                                        (:e fn-bpn-nth) (:e equal) (:e natp) (:e zp)
                                        (:e binary-+) natp zp)
                                      (theory 'minimal-theory))))))

(local
 (defthm bpnfj-persist-effects
  (not (equal (fn-bpn-nth 0 (fn-bpn-nth 0 (fn-bpnf-answer-effects
                                          (fn-bpnf-family-persist-step st e o r))))
              :persist-delivery))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn-bpnf-family-persist-step bpnfj-answer-effects
                                        fn-bpn-nth fn-cbor-ag-car car-cons cdr-cons
                                        (:e fn-bpn-nth) (:e equal) (:e natp) (:e zp)
                                        (:e binary-+) natp zp)
                                      (theory 'minimal-theory))))))

(local
 (defthm bpnfj-fragment-step
  (implies (and (fn-bpnf-family-jobs-agreep (fn-bpnf-held-list st))
                (bpnfj-our-eventp st event))
           (and (fn-bpnf-family-jobs-agreep
                 (fn-bpnf-held-list (fn-bpnf-answer-state (fn-bpnf-fragment-step st event))))
                (not (equal (fn-bpn-nth 0 (fn-bpn-nth 0 (fn-bpnf-answer-effects
                                                        (fn-bpnf-fragment-step st event))))
                            :persist-delivery))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories
                       '(fn-bpnf-fragment-step bpnfj-our-eventp
                         bpnfj-persist-step bpnfj-propose-step
                         bpnfj-propose-effects bpnfj-persist-effects
                         bpnfj-held-of-state-with-arrival bpnfj-answer-effects
                         (:e fn-bpn-nth) (:e fn-cbor-ag-car) (:e equal))
                       (theory 'minimal-theory))))))

(local
 (defthm bpnfj-report-author-step
  (implies (and (fn-bpnf-family-jobs-agreep (fn-bpnf-held-list st))
                (bpnfj-our-eventp st event))
           (and (fn-bpnf-family-jobs-agreep
                 (fn-bpnf-held-list (fn-bpnf-answer-state (fn-bpn-report-author-step st event))))
                (not (equal (fn-bpn-nth 0 (fn-bpn-nth 0 (fn-bpnf-answer-effects
                                                        (fn-bpn-report-author-step st event))))
                            :persist-delivery))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance bpnfj-fragment-step))
           :in-theory (union-theories
                       '(fn-bpn-report-author-step fn-bpn-report-step
                         fn-bpn-report-delete-issuedp fn-bpnf-family-issuedp
                         bpnfj-our-eventp
                         bpnfj-held-of-state-with-arrival bpnfj-answer-effects
                         (:e fn-bpn-nth) (:e fn-cbor-ag-car) (:e equal))
                       (theory 'minimal-theory))))))

(local
 (defthm bpnfj-delegate
  (implies (and (fn-bpnf-family-jobs-agreep (fn-bpnf-held-list st))
                (bpnfj-our-eventp st event))
           (fn-bpnf-family-jobs-agreep
            (fn-bpnf-held-list (fn-bpnf-answer-state (fn-bpnp-delegate-with-credit st event)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance bpnfj-report-author-step))
           :in-theory (union-theories
                       '(fn-bpnp-delegate-with-credit fn-bpnp-credit-refusal
                         fn-bpnp-credit-proposal-kind
                         bpnfj-our-eventp
                         bpnfj-held-of-state-with-arrival bpnfj-held-of-slot-writers
                         (:e fn-bpn-nth) (:e fn-cbor-ag-car) (:e equal))
                       (theory 'minimal-theory))))))

;; The served step on the two events of the fragment-progress path keeps the
;; relation: a (:family A OBS) proposal leaves the held list as it is, and a
;; (:persist-result EPOCH OP RESULT) while a kind-18 operation is issued
;; either leaves it or installs kind-18's own replacement (the keystone),
;; through every wrapper of fn-bpnp-step (credit admission and refusal,
;; publication fault, runtime slots).
(defthm fn-bpnp-step-family-events-keep-jobs-agreeing
  (implies (and (fn-bpnf-family-jobs-agreep (fn-bpnf-held-list st))
                (or (equal (fn-cbor-ag-car event) :family)
                    (and (equal (fn-cbor-ag-car event) :persist-result)
                         (fn-bpnf-family-issuedp st))))
           (fn-bpnf-family-jobs-agreep
            (fn-bpnf-held-list (fn-bpnf-answer-state (fn-bpnp-step st event)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance bpnfj-delegate))
           :in-theory (union-theories
                       '(fn-bpnp-step fn-bpnp-preserve-runtime-answer
                         fn-bpnp-domain-recover-eventp fn-bpnp-conflict-held
                         fn-bpnf-family-issuedp bpnfj-our-eventp
                         bpnfj-held-of-state-with-arrival bpnfj-held-of-slot-writers
                         (:e fn-bpn-nth) (:e fn-cbor-ag-car) (:e equal))
                       (theory 'minimal-theory)))))

;; Established at a cold start: the initial held list is empty.
(defthm fn-bpnf-family-jobs-agree-when-empty
  (fn-bpnf-family-jobs-agreep nil))
