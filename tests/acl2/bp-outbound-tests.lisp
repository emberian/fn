; Sender composition traces over an actual committed node article and durable
; workflow work/attempt.
(in-package "ACL2")
(include-book "../../books/bp-outbound")
(include-book "arena-lift")

(defconst *bpo-groups* '("fn.test"))
(defconst *bpo-msgid* "<out@example.invalid>")
(defconst *bpo-article* '(72 101 108 108 111 13 10))
; by specification: the flip -- the node's acceptance machine carries the
; payload as an arena handle (natp), never octets (books/acceptance.lisp
; fn-article-payload natp; fn-accept-prepare refuses a non-natp payload).  The
; article's octets *bpo-article* are the arena's extent 0, so the node holds
; handle 0; the request ADU below must still carry the octets.
(defconst *bpo-article-handle* 0)
; The arena the sender reads: *bpo-article* sealed at handle 0.
(defconst *bpo-payloads* (list *bpo-article*))
(bpr-lift fn-bpo-request-adu 4)
(bpr-lift fn-bpo-request-message 4)
(defconst *bpo-node-prepared*
  (fn-node-prepare
   (fn-node-initial-state *bpo-groups* 32)
   4 *bpo-msgid* *bpo-article-handle* *bpo-groups*
   "archive:out" "subject:out" "release:out" 1 841000000))
(defconst *bpo-node*
  (fn-node-complete *bpo-node-prepared* 0 4 :durable))
(defconst *bpo-config-record*
  '(:config "dtn://source/" "dtn://destination/" "policy:out"
    "dtn://receipt-authority/" 3600 "source-incarnation:7" "auth:out"))
(defconst *bpo-enqueue-record*
  '(:enqueue 10 0 "work:out" "<out@example.invalid>"
    "subject:out" "archive:out" "forward:out"
    "dtn://destination/" "policy:out" "terms:out"))
(defconst *bpo-attempt-record*
  '(:attempt 11 0 "work:out" "attempt:out" 0
    "dtn://source/" "dtn://destination/" "policy:out" 3600))
(defconst *bpo-state-0*
  (fn-bp-initial-state
   *bpo-node* (fn-bp-config-from-record *bpo-config-record*)))
(defconst *bpo-enqueue-prepared*
  (fn-bp-apply-journal-record *bpo-state-0* *bpo-enqueue-record*))
(defconst *bpo-enqueued*
  (fn-bp-apply-journal-record
   (fn-bp-journal-nth 1 *bpo-enqueue-prepared*)
   '(:outcome 10 0 :ordinary :durable)))
(defconst *bpo-attempt-prepared*
  (fn-bp-apply-journal-record
   (fn-bp-journal-nth 1 *bpo-enqueued*) *bpo-attempt-record*))
(defconst *bpo-attempt-durable*
  (fn-bp-apply-journal-record
   (fn-bp-journal-nth 1 *bpo-attempt-prepared*)
   '(:outcome 11 0 :ordinary :durable)))
(defconst *bpo-state* (fn-bp-journal-nth 1 *bpo-attempt-durable*))

(assert-event (car *bpo-enqueue-prepared*))
(assert-event (car *bpo-enqueued*))
(assert-event (car *bpo-attempt-prepared*))
(assert-event (car *bpo-attempt-durable*))
(assert-event (fn-bp-statep *bpo-state*))
(assert-event
 (fn-bpo-result-okp
  (in-arena-fn-bpo-request-adu *bpo-payloads* *bpo-state* "work:out" "attempt:out" 0)))
(defconst *bpo-request-octets*
  (fn-bpo-result-value
   (in-arena-fn-bpo-request-adu *bpo-payloads* *bpo-state* "work:out" "attempt:out" 0)))
(defconst *bpo-request-message*
  (fn-bpa-result-message (fn-bpa-decode-exact *bpo-request-octets*)))

; Every workflow/config field and the committed article body crosses exactly.
(assert-event (fn-bpa-requestp *bpo-request-message*))
(assert-event (equal (fn-bpa-request-work-id *bpo-request-message*) "work:out"))
(assert-event (equal (fn-bpa-request-subject *bpo-request-message*) "subject:out"))
(assert-event (equal (fn-bpa-request-source-eid *bpo-request-message*)
                     "dtn://source/"))
(assert-event (equal (fn-bpa-request-destination-eid *bpo-request-message*)
                     "dtn://destination/"))
(assert-event (equal (fn-bpa-request-policy-id *bpo-request-message*)
                     "policy:out"))
(assert-event (equal (fn-bpa-request-incarnation *bpo-request-message*)
                     "source-incarnation:7"))
(assert-event (equal (fn-bpa-request-auth-context *bpo-request-message*)
                     "auth:out"))
(assert-event (equal (fn-bpa-request-terms-id *bpo-request-message*)
                     "terms:out"))
(assert-event (equal (fn-bpa-request-article *bpo-request-message*)
                     *bpo-article*))
;
; ---------------------------------------------------------------------------
; Teeth for the KEYSTONE fn-bpo-request-success-preserves-context-and-article
; (PKT-RT-1): the hypothesis and the literal conclusion, each over an arena.
(defun bpo-ks-hyp (s w a g fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (fn-bpo-result-okp (fn-bpo-request-adu s w a g fn-arena)))
(defun bpo-ks-concl (s w a g fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (let* ((request (fn-bpo-request-message s w a g fn-arena))
         (work (fn-bp-find-work w (fn-bp-state-works s)))
         (article (fn-find-article
                   (fn-bp-work-msgid work)
                   (fn-state-articles
                    (fn-node-acceptance (fn-bp-state-node s))))))
    (and (equal (fn-bpa-request-work-id request) (fn-bp-work-id work))
         (equal (fn-bpa-request-subject request) (fn-bp-work-subject work))
         (equal (fn-bpa-request-source-eid request)
                (fn-bp-config-local-eid (fn-bp-state-config s)))
         (equal (fn-bpa-request-destination-eid request)
                (fn-bp-work-peer-eid work))
         (equal (fn-bpa-request-policy-id request) (fn-bp-work-policy-id work))
         (equal (fn-bpa-request-incarnation request)
                (fn-bp-work-incarnation work))
         (equal (fn-bpa-request-auth-context request)
                (fn-bp-work-auth-context work))
         (equal (fn-bpa-request-terms-id request) (fn-bp-work-terms-id work))
         (natp (fn-article-payload article))
         (< (fn-article-payload article) (fn-arena-count fn-arena))
         (equal (fn-bpa-request-article request)
                (fn-arena-payload (fn-article-payload article) fn-arena)))))
(bpr-lift bpo-ks-hyp 4)
(bpr-lift bpo-ks-concl 4)
; Positive, reachable: the committed article's handle 0 is sealed with its
; octets; the hypothesis and the whole conclusion hold, and the article that
; crosses is the octets, not the handle.
(assert-event
 (in-arena-bpo-ks-hyp *bpo-payloads* *bpo-state* "work:out" "attempt:out" 0))
(assert-event
 (in-arena-bpo-ks-concl *bpo-payloads* *bpo-state* "work:out" "attempt:out" 0))
(assert-event
 (equal (fn-article-payload
         (fn-find-article *bpo-msgid*
                          (fn-state-articles (fn-node-acceptance *bpo-node*))))
        *bpo-article-handle*))
(assert-event (not (equal (fn-bpa-request-article *bpo-request-message*)
                          *bpo-article-handle*)))
; Hypothesis removal (the one hypothesis, a formed ADU): the same image over
; an arena that has not sealed the article's handle.  The hypothesis fails
; (the sender refuses) and so does the conclusion (the handle is not below
; the arena's count).
(assert-event
 (not (in-arena-bpo-ks-hyp nil *bpo-state* "work:out" "attempt:out" 0)))
(assert-event
 (not (in-arena-bpo-ks-concl nil *bpo-state* "work:out" "attempt:out" 0)))
; Mutation witness (the arena, not the node, decides the octets): an arena
; holding other octets under handle 0 yields an ADU carrying those octets.
(defconst *bpo-other-article* '(66 121 101 13 10))
(assert-event
 (equal (fn-bpa-request-article
         (fn-bpa-result-message
          (fn-bpa-decode-exact
           (fn-bpo-result-value
            (in-arena-fn-bpo-request-adu (list *bpo-other-article*)
                                         *bpo-state* "work:out" "attempt:out"
                                         0)))))
        *bpo-other-article*))
(assert-event
 (in-arena-bpo-ks-concl (list *bpo-other-article*)
                        *bpo-state* "work:out" "attempt:out" 0))
; The PKT-RT-1 regression: the request built from the handle itself is not a
; request (fn-bpa-requestp refuses it), which is why every send failed.
(assert-event
 (not (fn-bpa-requestp
       (fn-bpa-make-request "work:out" "subject:out" "dtn://source/"
                            "dtn://destination/" "policy:out"
                            "source-incarnation:7" "auth:out" "terms:out"
                            *bpo-article-handle*))))

; Stale attempt identity and missing work are refused.
(assert-event
 (not (fn-bpo-result-okp
       (in-arena-fn-bpo-request-adu *bpo-payloads* *bpo-state* "work:out" "attempt:old" 0))))
(assert-event
 (not (fn-bpo-result-okp
       (in-arena-fn-bpo-request-adu *bpo-payloads* *bpo-state* "work:missing" "attempt:out" 0))))

; A hand-constructed state can satisfy fn-bp-statep while omitting the
; stronger workflow-to-node binding relation; outbound composition rechecks it.
(defconst *bpo-unbound-state*
  (fn-bp-make-state
   (fn-node-initial-state *bpo-groups* 32)
   (fn-bp-state-config *bpo-state*)
   (fn-bp-state-works *bpo-state*) nil nil nil
   (fn-bp-state-used-txs *bpo-state*)))
(assert-event (fn-bp-statep *bpo-unbound-state*))
(assert-event
 (not (fn-bpo-result-okp
       (in-arena-fn-bpo-request-adu *bpo-payloads*         *bpo-unbound-state* "work:out" "attempt:out" 0))))

; The workflow admits strings larger than the portable 256-octet metadata
; profile.  Such a work remains a logical workflow state but cannot form an ADU.
(defun fn-bpo-test-repeat-char (n)
  (if (zp n) nil (cons #\x (fn-bpo-test-repeat-char (1- n)))))
(defconst *bpo-long-work-id*
  (coerce (fn-bpo-test-repeat-char 257) 'string))
(defconst *bpo-long-work*
  (fn-bp-make-work
   *bpo-long-work-id* *bpo-msgid* "subject:out" "archive:out" "forward:out"
   "dtn://destination/" "policy:out" "source-incarnation:7" "auth:out"
   "terms:out" 1 (fn-bp-make-attempt "attempt:out" 0 :intent 3600) nil))
(defconst *bpo-long-state*
  (fn-bp-make-state
   *bpo-node* (fn-bp-state-config *bpo-state*)
   (list *bpo-long-work*) nil nil nil nil))
(assert-event (fn-bp-statep *bpo-long-state*))
(assert-event
 (not (fn-bpo-result-okp
       (in-arena-fn-bpo-request-adu *bpo-payloads*         *bpo-long-state* *bpo-long-work-id* "attempt:out" 0))))

; A matching returned receipt produces the actual local journal intent.  The
; caller's transaction pair appears in that record, never in the receipt ADU.
(defconst *bpo-receipt-message*
  (fn-bpa-make-receipt
   "receipt:out" "work:out" "subject:out"
   "dtn://receipt-authority/" "dtn://destination/" "policy:out"
   "source-incarnation:7" "auth:out" "terms:out"))
(defconst *bpo-receipt-octets* (fn-bpa-encode *bpo-receipt-message*))
(defconst *bpo-receipt-result*
  (fn-bpo-receipt-intent-record
   *bpo-state* 12 0 *bpo-receipt-octets* t))
(assert-event (fn-bpo-result-okp *bpo-receipt-result*))
(assert-event
 (equal (fn-bpo-result-value *bpo-receipt-result*)
        '(:receipt-intent 12 0 "receipt:out" "work:out" "subject:out"
          "dtn://receipt-authority/" "dtn://destination/" "policy:out"
          "source-incarnation:7" "auth:out" "terms:out")))
(assert-event
 (car (fn-bp-apply-journal-record
       *bpo-state* (fn-bpo-result-value *bpo-receipt-result*))))

; Wire context cannot authorize itself, and every bound mismatch fails closed.
(assert-event
 (not (fn-bpo-result-okp
       (fn-bpo-receipt-intent-record
        *bpo-state* 12 0 *bpo-receipt-octets* nil))))
(assert-event
 (not (fn-bpo-result-okp
       (fn-bpo-receipt-intent-record
        *bpo-state* 12 0
        (fn-bpa-encode
         (fn-bpa-make-receipt
          "receipt:out" "work:out" "subject:out"
          "dtn://wrong-authority/" "dtn://destination/" "policy:out"
          "source-incarnation:7" "auth:out" "terms:out"))
        t))))
(assert-event
 (not (fn-bpo-result-okp
       (fn-bpo-receipt-intent-record
        *bpo-state* 12 0
        (fn-bpa-encode
         (fn-bpa-make-receipt
          "receipt:out" "work:out" "subject:out"
          "dtn://receipt-authority/" "dtn://destination/" "wrong-policy"
          "source-incarnation:7" "auth:out" "terms:out"))
        t))))
(assert-event
 (not (fn-bpo-result-okp
       (fn-bpo-receipt-intent-record
        *bpo-state* 12 0 '(0 1 2) t))))
