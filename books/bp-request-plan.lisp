; The generic native request plan: from a durable FNWF attempt to the exact
; request ADU for that work.  `bp-obligation request' (host/native/
; bp-obligation.lisp) calls fn-bprq-plan through host/workflow-host.lisp's
; fn-workflow-request-plan, publishes the plan's two records, takes the one
; :submit effect, and hands the plan's ADU to its FNBS carrier.  No ION record,
; route or helper is read here: ION is one transport adapter of this attempt.
(in-package "ACL2")
(include-book "bp-workflow-constructors")
(include-book "bp-outbound")

; The :attempt record the current image admits for WORK-ID, or nil.  Fields
; are ACL2's: the work's next generation and the configured local/peer EID,
; policy and lifetime.  The ION sender publishes this same record.
(defun fn-bprq-attempt-record (s txid tx-generation work-id attempt-id)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((work (fn-bp-find-work work-id (fn-bp-state-works s)))
         (config (fn-bp-state-config s))
         (record (list :attempt txid tx-generation work-id attempt-id
                       (fn-bp-work-next-generation work)
                       (fn-bp-config-local-eid config)
                       (fn-bp-config-peer-eid config)
                       (fn-bp-config-policy-id config)
                       (fn-bp-config-lifetime config))))
    (if (and (fn-bp-journal-recordp record)
             (car (fn-bprl-apply-journal-record s record)))
        record nil)))

; The transaction id is chosen above every id the recovered image has used,
; as fn-bprl-receipt-auto-record does; the operator supplies none.
(defun fn-bprq-next-txid (s)
  (declare (xargs :guard t :verify-guards nil))
  (1+ (fn-bprl-max-used-txid (fn-bp-state-used-txs s) 0)))

; The effects fn-workflow-take-submit accepts: exactly one :submit for
; exactly this (work, attempt, generation).
(defun fn-bprq-submit-effectsp (effects work-id attempt-id generation)
  (declare (xargs :guard t))
  (and (consp effects)
       (null (cdr effects))
       (equal (fn-bp-journal-nth 0 (car effects)) :submit)
       (equal (fn-bp-journal-nth 1 (car effects)) work-id)
       (equal (fn-bp-journal-nth 2 (car effects)) attempt-id)
       (equal (fn-bp-journal-nth 3 (car effects)) generation)))

(defun fn-bprq-plan-attempt (plan) (declare (xargs :guard t)) (fn-bp-journal-nth 1 plan))
(defun fn-bprq-plan-outcome (plan) (declare (xargs :guard t)) (fn-bp-journal-nth 2 plan))
(defun fn-bprq-plan-key (plan) (declare (xargs :guard t)) (fn-bp-journal-nth 3 plan))
(defun fn-bprq-plan-adu (plan) (declare (xargs :guard t)) (fn-bp-journal-nth 4 plan))
(defun fn-bprq-plan-destination (plan) (declare (xargs :guard t)) (fn-bp-journal-nth 5 plan))
(defun fn-bprq-plan-retry (plan) (declare (xargs :guard t)) (fn-bp-journal-nth 6 plan))

; A work whose last attempt a reopen marked :restart-observed is retryable
; only in the live image: disk replay applies the restart after the last
; record, so a new :attempt straight after the old one is refused on the next
; open.  The journaled :retry-request for the old attempt (fn-bp-request-retry,
; the explicit local policy decision to retry) is admitted both live and in
; replay, and makes the old attempt :unknown, which is retryable.  The
; operator asking again for the same work is that decision.
(defun fn-bprq-retry-record (s work-id)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((work (fn-bp-find-work work-id (fn-bp-state-works s)))
         (old (fn-bp-work-attempt work))
         (record (list :retry-request work-id (fn-bp-attempt-id old)
                       (fn-bp-attempt-generation old)
                       (fn-bp-config-policy-id (fn-bp-state-config s)))))
    (if (and (consp old)
             (equal (fn-bp-attempt-status old) :restart-observed)
             (fn-bp-journal-recordp record)
             (car (fn-bprl-apply-journal-record s record)))
        record
      nil)))

(defun fn-bprq-pre-state (s retry)
  (declare (xargs :guard t :verify-guards nil))
  (if retry (fn-bp-journal-nth 1 (fn-bprl-apply-journal-record s retry)) s))

; The workflow image after the plan's records (its retry request, if any,
; its attempt and the attempt's durable outcome), which is the image the host
; holds once every publication returns :durable.
(defun fn-bprq-published-state (s retry attempt outcome)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bp-journal-nth
   1 (fn-bprl-apply-journal-record
      (fn-bp-journal-nth
       1 (fn-bprl-apply-journal-record (fn-bprq-pre-state s retry) attempt))
      outcome)))

; Plan: (:request ATTEMPT OUTCOME (WORK ATTEMPT-ID GENERATION) ADU DESTINATION
; RETRY) or nil, RETRY being the :retry-request published first, or nil.  DESTINATION is the work's peer EID, the bundle destination the
; FNBS carrier addresses; the request inside names the same EID.
; nil is a refusal: no admissible attempt, no single :submit, or no request
; (fn-bpo-request-adu refuses a work that is not outstanding, not bound to a
; committed article, or whose image is pending or fenced).
(defun fn-bprq-plan (s work-id attempt-id)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((retry (fn-bprq-retry-record s work-id))
         (s1 (fn-bprq-pre-state s retry))
         (txid (fn-bprq-next-txid s1))
         (attempt (fn-bprq-attempt-record s1 txid 0 work-id attempt-id)))
    (if (not attempt)
        nil
      (let* ((outcome (list :outcome txid 0 :ordinary :durable))
             (a1 (fn-bprl-apply-journal-record s1 attempt))
             (a2 (fn-bprl-apply-journal-record
                  (fn-bp-journal-nth 1 a1) outcome))
             (generation (fn-bp-journal-nth 5 attempt))
             (result (fn-bpo-request-adu (fn-bp-journal-nth 1 a2)
                                         work-id attempt-id generation)))
        (if (and (car a2)
                 (fn-bprq-submit-effectsp (fn-bp-journal-nth 2 a2)
                                          work-id attempt-id generation)
                 (fn-bpo-result-okp result))
            (list :request attempt outcome
                  (list work-id attempt-id generation)
                  (fn-bpo-result-value result)
                  (fn-bp-work-peer-eid
                   (fn-bp-find-work work-id
                                    (fn-bp-state-works
                                     (fn-bp-journal-nth 1 a2))))
                  retry)
          nil)))))

(defthm fn-bprq-find-work-names-its-key
  (implies (fn-bp-find-work work-id works)
           (equal (fn-bp-work-id (fn-bp-find-work work-id works)) work-id))
  :hints (("Goal" :in-theory (e/d (fn-bp-find-work) (fn-bp-work-id)))))

; The request exists only for a work the image holds.
(defthm fn-bprq-request-message-finds-its-work
  (implies (consp (fn-bpo-request-message s work-id attempt-id generation))
           (fn-bp-find-work work-id (fn-bp-state-works s)))
  :hints (("Goal" :in-theory (enable fn-bpo-request-message
                                     fn-bp-work-outstandingp))))

(defthm fn-bprq-request-message-names-its-work
  (implies (consp (fn-bpo-request-message s work-id attempt-id generation))
           (equal (fn-bpa-request-work-id
                   (fn-bpo-request-message s work-id attempt-id generation))
                  work-id))
  :hints (("Goal"
           :use ((:instance fn-bpo-request-success-preserves-context-and-article
                            (attempt-generation generation))
                 (:instance fn-bprq-find-work-names-its-key
                            (works (fn-bp-state-works s)))
                 fn-bprq-request-message-finds-its-work)
           :in-theory (disable fn-bpo-request-success-preserves-context-and-article
                               fn-bprq-find-work-names-its-key
                               fn-bprq-request-message-finds-its-work
                               fn-bpo-request-message fn-bpo-request-adu
                               fn-bp-find-work fn-bp-work-id
                               fn-bpa-request-work-id))))

;; The request ADU over any image, stated over that image's work WORK-ID.
(defthm fn-bprq-request-adu-is-the-works-request
  (implies
   (fn-bpo-result-okp (fn-bpo-request-adu s work-id attempt-id generation))
   (let* ((work (fn-bp-find-work work-id (fn-bp-state-works s)))
          (article
           (fn-find-article
            (fn-bp-work-msgid work)
            (fn-state-articles (fn-node-acceptance (fn-bp-state-node s)))))
          (request
           (fn-bpa-make-request
            (fn-bp-work-id work) (fn-bp-work-subject work)
            (fn-bp-config-local-eid (fn-bp-state-config s))
            (fn-bp-work-peer-eid work) (fn-bp-work-policy-id work)
            (fn-bp-work-incarnation work) (fn-bp-work-auth-context work)
            (fn-bp-work-terms-id work) (fn-article-payload article))))
     (and (equal (fn-bpa-decode-exact
                  (fn-bpo-result-value
                   (fn-bpo-request-adu s work-id attempt-id generation)))
                 (list :ok request))
          (fn-bpa-requestp request)
          (equal (fn-bpa-request-work-id request) work-id))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-bpo-request-success-decodes-exactly
                            (attempt-generation generation))
                 (:instance fn-bpo-request-message-is-exact-construction
                            (attempt-generation generation))
                 (:instance fn-bpo-request-message-is-request
                            (attempt-generation generation))
                 fn-bprq-request-message-names-its-work)
           :in-theory (disable fn-bpo-request-adu fn-bpo-request-message
                               fn-bpo-result-value
                               fn-bpa-decode-exact fn-bpa-encode
                               fn-bpa-make-request fn-bpa-requestp
                               fn-bpa-request-work-id
                               fn-bpo-request-success-decodes-exactly
                               fn-bpo-request-message-is-exact-construction
                               fn-bpo-request-message-is-request
                               fn-bprq-request-message-names-its-work
                               fn-bp-find-work fn-bp-state-works
                               fn-bp-state-node fn-bp-state-config
                               fn-bp-work-id fn-bp-work-subject
                               fn-bp-work-peer-eid fn-bp-work-policy-id
                               fn-bp-work-incarnation fn-bp-work-auth-context
                               fn-bp-work-terms-id fn-bp-config-local-eid
                               fn-article-payload
                               fn-bp-work-msgid fn-state-articles
                               fn-node-acceptance fn-find-article))))

(defthm fn-bprq-plan-unfolds
  (implies (fn-bprq-plan s work-id attempt-id)
           (let* ((retry (fn-bprq-retry-record s work-id))
                  (s1 (fn-bprq-pre-state s retry))
                  (txid (fn-bprq-next-txid s1))
                  (attempt (fn-bprq-attempt-record s1 txid 0 work-id attempt-id))
                  (outcome (list :outcome txid 0 :ordinary :durable))
                  (generation (fn-bp-journal-nth 5 attempt))
                  (s2 (fn-bprq-published-state s retry attempt outcome))
                  (plan (fn-bprq-plan s work-id attempt-id)))
             (and attempt
                  (equal (fn-bprq-plan-retry plan) retry)
                  (equal (fn-bprq-plan-attempt plan) attempt)
                  (equal (fn-bprq-plan-outcome plan) outcome)
                  (equal (fn-bprq-plan-key plan)
                         (list work-id attempt-id generation))
                  (fn-bpo-result-okp
                   (fn-bpo-request-adu s2 work-id attempt-id generation))
                  (equal (fn-bprq-plan-adu plan)
                         (fn-bpo-result-value
                          (fn-bpo-request-adu s2 work-id attempt-id
                                              generation)))
                  (equal (fn-bprq-plan-destination plan)
                         (fn-bp-work-peer-eid
                          (fn-bp-find-work work-id (fn-bp-state-works s2)))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-bprq-plan fn-bprq-plan-attempt
                                   fn-bprq-plan-outcome fn-bprq-plan-key
                                   fn-bprq-plan-adu fn-bprq-plan-destination
                                   fn-bprq-plan-retry fn-bprq-published-state)
                                  (fn-bp-find-work fn-bp-work-peer-eid
                                   fn-bprq-retry-record fn-bprq-pre-state
                                   fn-bp-state-works fn-bprq-attempt-record fn-bprq-next-txid
                                   fn-bprl-apply-journal-record
                                   fn-bpo-request-adu fn-bpo-result-okp
                                   fn-bpo-result-value
                                   fn-bprq-submit-effectsp)))))

(defthm fn-bprq-attempt-record-names-its-attempt
  (implies (fn-bprq-attempt-record s txid tx-generation work-id attempt-id)
           (let ((r (fn-bprq-attempt-record s txid tx-generation work-id
                                            attempt-id)))
             (and (equal (fn-bp-journal-nth 0 r) :attempt)
                  (equal (fn-bp-journal-nth 3 r) work-id)
                  (equal (fn-bp-journal-nth 4 r) attempt-id))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-bprl-apply-journal-record
                                      fn-bp-journal-recordp))))

; Keystone.  A plan the host may execute is the workflow's own request for
; exactly WORK-ID: its attempt names WORK-ID and ATTEMPT-ID, its FNBS key is
; that attempt's (work, attempt, generation), its ADU decodes exactly to
; fn-bpa-make-request over the work WORK-ID holds in the image the host has
; after publishing the plan's two records, whose work id field is WORK-ID,
; and the carrier's destination is that work's peer EID, the request's own.
(defthm fn-bprq-plan-is-the-works-request
  (implies
   (fn-bprq-plan s work-id attempt-id)
   (let* ((plan (fn-bprq-plan s work-id attempt-id))
          (attempt (fn-bprq-plan-attempt plan))
          (generation (fn-bp-journal-nth 5 attempt))
          (s2 (fn-bprq-published-state s (fn-bprq-plan-retry plan) attempt
                                       (fn-bprq-plan-outcome plan)))
          (work (fn-bp-find-work work-id (fn-bp-state-works s2)))
          (article
           (fn-find-article
            (fn-bp-work-msgid work)
            (fn-state-articles (fn-node-acceptance (fn-bp-state-node s2)))))
          (request
           (fn-bpa-make-request
            (fn-bp-work-id work) (fn-bp-work-subject work)
            (fn-bp-config-local-eid (fn-bp-state-config s2))
            (fn-bp-work-peer-eid work) (fn-bp-work-policy-id work)
            (fn-bp-work-incarnation work) (fn-bp-work-auth-context work)
            (fn-bp-work-terms-id work) (fn-article-payload article))))
     (and (equal (fn-bp-journal-nth 0 attempt) :attempt)
          (equal (fn-bp-journal-nth 3 attempt) work-id)
          (equal (fn-bp-journal-nth 4 attempt) attempt-id)
          (equal (fn-bprq-plan-key plan) (list work-id attempt-id generation))
          (equal (fn-bpa-decode-exact (fn-bprq-plan-adu plan))
                 (list :ok request))
          (fn-bpa-requestp request)
          (equal (fn-bpa-request-work-id request) work-id)
          (equal (fn-bprq-plan-destination plan) (fn-bp-work-peer-eid work)))))
  :hints (("Goal"
           :use ((:instance fn-bprq-plan-unfolds)
                 (:instance fn-bprq-attempt-record-names-its-attempt
                            (s (fn-bprq-pre-state s (fn-bprq-retry-record s work-id)))
                            (txid (fn-bprq-next-txid
                                   (fn-bprq-pre-state
                                    s (fn-bprq-retry-record s work-id))))
                            (tx-generation 0))
                 (:instance fn-bprq-request-adu-is-the-works-request
                            (s (fn-bprq-published-state
                                s (fn-bprq-retry-record s work-id)
                                (fn-bprq-attempt-record
                                 (fn-bprq-pre-state s (fn-bprq-retry-record s work-id))
                                 (fn-bprq-next-txid
                                  (fn-bprq-pre-state
                                   s (fn-bprq-retry-record s work-id)))
                                 0 work-id attempt-id)
                                (list :outcome
                                      (fn-bprq-next-txid
                                       (fn-bprq-pre-state
                                        s (fn-bprq-retry-record s work-id)))
                                      0 :ordinary :durable)))
                            (generation
                             (fn-bp-journal-nth
                              5 (fn-bprq-attempt-record
                                 (fn-bprq-pre-state s (fn-bprq-retry-record s work-id))
                                 (fn-bprq-next-txid
                                  (fn-bprq-pre-state
                                   s (fn-bprq-retry-record s work-id)))
                                 0 work-id attempt-id)))))
           :in-theory (theory 'minimal-theory))))
