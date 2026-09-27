; Teeth for books/bp-request-plan.lisp, over the committed-article workflow
; image of bp-outbound-tests (one work, enqueued and durable, no attempt).
(in-package "ACL2")
(include-book "bp-outbound-tests")
(include-book "../../books/bp-request-plan")
(include-book "../../books/bp-ion-workflow")
(include-book "std/testing/must-fail" :dir :system)
; The workflow entries read the payload arena (the records flip): each call
; runs over an arena holding *bpo-payloads* (tests/acl2/arena-lift.lisp).
(bpr-lift fn-bprq-plan 3)
(bpr-lift fn-bpiw-apply 3)
(bpr-lift fn-bpiw-replay-journal 2)

(defconst *bprq-s* (fn-bp-journal-nth 1 *bpo-enqueued*))
(defconst *bprq-plan* (in-arena-fn-bprq-plan *bpo-payloads* *bprq-s* "work:out" "attempt:out"))

; Reachable, non-degenerate witness.  The transaction id is chosen above the
; enqueue's 10; the attempt is the exact record the outbound tests publish by
; hand, and the ADU is the request those tests decode field by field.
(assert-event (equal (car *bprq-plan*) :request))
(assert-event (equal (fn-bprq-next-txid *bprq-s*) 11))
(assert-event (equal (fn-bprq-plan-attempt *bprq-plan*) *bpo-attempt-record*))
(assert-event (equal (fn-bprq-plan-outcome *bprq-plan*)
                     '(:outcome 11 0 :ordinary :durable)))
(assert-event (equal (fn-bprq-plan-key *bprq-plan*)
                     '("work:out" "attempt:out" 0)))
(assert-event (equal (fn-bprq-plan-adu *bprq-plan*) *bpo-request-octets*))
(assert-event (equal (fn-bprq-plan-destination *bprq-plan*) "dtn://destination/"))
(assert-event
 (equal (fn-bpa-request-work-id
         (fn-bpa-result-message
          (fn-bpa-decode-exact (fn-bprq-plan-adu *bprq-plan*))))
        "work:out"))
(assert-event
 (equal (fn-bpa-request-article
         (fn-bpa-result-message
          (fn-bpa-decode-exact (fn-bprq-plan-adu *bprq-plan*))))
        *bpo-article*))
; The keystone's article conjuncts (PKT-RT-1): the article in the plan's ADU
; is the arena's payload under the node article's handle, a sealed handle
; (handle 0 of the one-payload arena), never the handle.
(defun bprq-ks-article (s w a fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (let* ((plan (fn-bprq-plan s w a fn-arena))
         (s2 (fn-bprq-published-state s (fn-bprq-plan-retry plan)
                                      (fn-bprq-plan-attempt plan)
                                      (fn-bprq-plan-outcome plan)))
         (work (fn-bp-find-work w (fn-bp-state-works s2)))
         (article (fn-find-article
                   (fn-bp-work-msgid work)
                   (fn-state-articles (fn-node-acceptance (fn-bp-state-node s2)))))
         (h (fn-article-payload article)))
    (and plan
         (natp h) (< h (fn-arena-count fn-arena))
         (equal (fn-bpa-request-article
                 (fn-bpa-result-message
                  (fn-bpa-decode-exact (fn-bprq-plan-adu plan))))
                (fn-arena-payload h fn-arena)))))
(bpr-lift bprq-ks-article 3)
(assert-event (in-arena-bprq-ks-article *bpo-payloads* *bprq-s* "work:out" "attempt:out"))
; Without a sealed handle (an empty arena) the hypothesis fails -- no plan --
; and so do the article conjuncts.
(assert-event (null (in-arena-fn-bprq-plan nil *bprq-s* "work:out" "attempt:out")))
(assert-event (not (in-arena-bprq-ks-article nil *bprq-s* "work:out" "attempt:out")))
; The image the plan names is the one the host reaches by publishing the two
; records through fn-bpiw-apply (host/workflow-host.lisp fn-workflow-apply-record).
(defconst *bprq-live-1*
  (in-arena-fn-bpiw-apply *bpo-payloads* *bprq-s* (fn-bpiw-initial) (fn-bprq-plan-attempt *bprq-plan*)))
(defconst *bprq-live-2*
  (in-arena-fn-bpiw-apply *bpo-payloads* (nth 1 *bprq-live-1*) (nth 3 *bprq-live-1*)
                 (fn-bprq-plan-outcome *bprq-plan*)))
(assert-event (and (car *bprq-live-1*) (car *bprq-live-2*)))
(assert-event (null (fn-bprq-plan-retry *bprq-plan*)))
(assert-event (equal (nth 1 *bprq-live-2*)
                     (fn-bprq-published-state
                      *bprq-s* nil (fn-bprq-plan-attempt *bprq-plan*)
                      (fn-bprq-plan-outcome *bprq-plan*))))
(assert-event (equal (nth 1 *bprq-live-2*) *bpo-state*))
(assert-event (fn-bprq-submit-effectsp (nth 2 *bprq-live-2*)
                                       "work:out" "attempt:out" 0))

; The keystone has one hypothesis, that a plan exists.  Without it the
; conclusion fails: an absent work has no plan and nothing that decodes.
(defconst *bprq-none* (in-arena-fn-bprq-plan *bpo-payloads* *bprq-s* "work:missing" "attempt:out"))
(assert-event (null *bprq-none*))
(assert-event (not (equal (car (fn-bpa-decode-exact
                                (fn-bprq-plan-adu *bprq-none*)))
                          :ok)))
; The conclusion instantiated at that witness is false (a concrete
; counterexample, so the unhypothesised statement is not a theorem).
(must-fail
 (assert-event
  (equal (car (fn-bpa-decode-exact (fn-bprq-plan-adu *bprq-none*))) :ok)))
(must-fail
 (assert-event
  (equal (fn-bp-journal-nth 3 (fn-bprq-plan-attempt *bprq-none*))
         "work:missing")))

; Refusals.  A work whose attempt is in flight (the durable image of the hand
; trace) has no second plan; nor does a pending or a fenced image; nor an
; image whose work is bound to no committed article, where an attempt alone
; would still be admissible but no request can be formed.
(assert-event (null (in-arena-fn-bprq-plan *bpo-payloads* *bpo-state* "work:out" "attempt:two")))
(assert-event (null (in-arena-fn-bprq-plan *bpo-payloads* (nth 1 *bpo-attempt-prepared*)
                                  "work:out" "attempt:two")))
(assert-event (null (in-arena-fn-bprq-plan *bpo-payloads* (fn-bp-restart (nth 1 *bpo-attempt-prepared*))
                                  "work:out" "attempt:two")))
(defconst *bprq-unbound*
  (fn-bp-make-state
   (fn-node-initial-state *bpo-groups* 32)
   (fn-bp-state-config *bprq-s*)
   (fn-bp-state-works *bprq-s*) nil nil nil
   (fn-bp-state-used-txs *bprq-s*)))
(assert-event (fn-bprq-attempt-record *bprq-unbound* 11 0 "work:out" "attempt:out"))
(assert-event (null (in-arena-fn-bprq-plan *bpo-payloads* *bprq-unbound* "work:out" "attempt:out")))

; After a restart the in-flight attempt is :restart-observed.  The next plan
; journals a :retry-request for the old attempt first, then a new attempt at
; the next generation, and the whole history (the reopen's restart is not a
; record) replays: fn-bpiw-replay-journal, the function the host's open calls
; (host/workflow-host.lisp fn-workflow-install-replay), accepts it.
(defconst *bprq-restarted* (fn-bp-restart *bpo-state*))
(defconst *bprq-plan-2* (in-arena-fn-bprq-plan *bpo-payloads* *bprq-restarted* "work:out" "attempt:two"))
(assert-event (equal (car *bprq-plan-2*) :request))
(assert-event (equal (fn-bprq-plan-retry *bprq-plan-2*)
                     '(:retry-request "work:out" "attempt:out" 0 "policy:out")))
(assert-event (equal (fn-bprq-plan-key *bprq-plan-2*)
                     '("work:out" "attempt:two" 1)))
(assert-event (equal (fn-bprq-plan-adu *bprq-plan-2*) *bpo-request-octets*))
(defconst *bprq-history*
  (list *bpo-config-record* *bpo-enqueue-record* '(:outcome 10 0 :ordinary :durable)
        *bpo-attempt-record* '(:outcome 11 0 :ordinary :durable)))
(assert-event (car (in-arena-fn-bpiw-replay-journal *bpo-payloads* *bpo-node* *bprq-history*)))
(assert-event
 (car (in-arena-fn-bpiw-replay-journal *bpo-payloads*
       *bpo-node*
       (append *bprq-history*
               (list (fn-bprq-plan-retry *bprq-plan-2*)
                     (fn-bprq-plan-attempt *bprq-plan-2*)
                     (fn-bprq-plan-outcome *bprq-plan-2*))))))
; Without the retry request the live image still admits the new attempt, and
; the history refuses it: the defect the retry record closes.
(assert-event
 (fn-bprq-attempt-record *bprq-restarted* 12 0 "work:out" "attempt:two"))
(assert-event
 (not (car (in-arena-fn-bpiw-replay-journal *bpo-payloads*
            *bpo-node*
            (append *bprq-history*
                    (list (fn-bprq-plan-attempt *bprq-plan-2*)
                          (fn-bprq-plan-outcome *bprq-plan-2*)))))))

; ION is an adapter of the same attempt: its constructor is this one.
(defthm fn-bpiw-attempt-record-is-the-generic-attempt
  (equal (fn-bpiw-attempt-record bp txid tx-generation work-id attempt-id)
         (fn-bprq-attempt-record bp txid tx-generation work-id attempt-id))
  :hints (("Goal" :in-theory (union-theories
                              '(fn-bpiw-attempt-record fn-bprq-attempt-record)
                              (theory 'minimal-theory)))))
