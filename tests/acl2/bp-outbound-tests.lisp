; Sender composition traces over an actual committed node article and durable
; workflow work/attempt.
(in-package "ACL2")
(include-book "../../books/bp-outbound")

(defconst *bpo-groups* '("fn.test"))
(defconst *bpo-msgid* "<out@example.invalid>")
(defconst *bpo-article* '(72 101 108 108 111 13 10))
(defconst *bpo-node-prepared*
  (fn-node-prepare
   (fn-node-initial-state *bpo-groups* 32)
   4 *bpo-msgid* 0 *bpo-groups*
   "archive:out" "subject:out" "release:out" 1 841000000))
(defconst *bpo-node*
  (fn-node-complete *bpo-node-prepared* 0 4 :durable))
;; Since the acceptance flip (c5808cd72) the committed article holds a HANDLE
;; at its payload position (0 here, as the Store's intern assigns it); the
;; payload arena holds the article's bytes at that handle.  The request reads
;; them through the arena (fn-bpo-article-octets).
(defconst *bpo-payloads* (list *bpo-article*))
(include-book "arena-lift")
(bpr-lift fn-bpo-request-adu 4)
(bpr-lift fn-bpo-request-message 4)
(bpr-lift fn-bpo-article-octets 1)
(assert-event (equal (fn-article-payload
                      (fn-find-article *bpo-msgid* (fn-state-articles (fn-node-acceptance *bpo-node*))))
                     0))
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
       (in-arena-fn-bpo-request-adu *bpo-payloads* *bpo-unbound-state* "work:out" "attempt:out" 0))))

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
       (in-arena-fn-bpo-request-adu *bpo-payloads* *bpo-long-state* *bpo-long-work-id* "attempt:out" 0))))

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

; -----------------------------------------------------------------------------
; The flipped request (lane audit-fixes, sub-lane bpo).  Before this, the
; request carried the article's payload position -- the handle 0 -- and every
; request was refused (fn-bpa-requestp's article gate): the positive witness
; above is the fix's reachable witness (the committed article's bytes cross
; exactly).  fn-bpo-request-success-preserves-context-and-article's article
; conjunct, literally: the request's article is fn-bpo-article-octets of the
; work's article over the same arena.
(assert-event
 (equal (fn-bpa-request-article *bpo-request-message*)
        (in-arena-fn-bpo-article-octets
         *bpo-payloads*
         (fn-find-article *bpo-msgid* (fn-state-articles (fn-node-acceptance *bpo-node*))))))
; The arena is what is read: over an arena whose handle 0 holds other bytes,
; the request carries those bytes.
(defconst *bpo-other-bytes* '(66 121 101 13 10))
(assert-event
 (equal (fn-bpa-request-article
         (fn-bpa-result-message
          (fn-bpa-decode-exact
           (fn-bpo-result-value
            (in-arena-fn-bpo-request-adu (list *bpo-other-bytes*) *bpo-state*
                                         "work:out" "attempt:out" 0)))))
        *bpo-other-bytes*))
; A handle outside the arena denotes no bytes and the request is refused (an
; arena that never interned the article; the host's arena always has).  It
; is not answered with an empty article.
(assert-event
 (equal (in-arena-fn-bpo-request-adu nil *bpo-state* "work:out" "attempt:out" 0)
        '(:error :request-refused)))
