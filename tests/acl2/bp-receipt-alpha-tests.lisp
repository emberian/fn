; Teeth for books/bp-receipt-alpha.lisp (records-flip, flip-L4):
; fn-bpr-store-record-acceptedp-is-acceptance-over-alpha, the receiver's
; Store gate over the arena is the pre-flip gate over ALPHA of the Store.
; The Store is bp-signed-binding-tests': a hybrid-signed article retained as
; a composite ROW whose article is the held row at handle 0 of an arena that
; holds the stored projection.
(in-package "ACL2")
(include-book "../../books/bp-receipt-alpha")
(include-book "bp-signed-binding-tests")
(include-book "arena-lift")
(include-book "std/testing/must-fail" :dir :system)

; The keystone's right-hand side: the pre-flip gate over ALPHA.
(defun bpra-over-alpha (store record fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (and (fn-sn-statep store) (fn-record-p record)
       (equal (fn-sf-phase (fn-sn-files store)) :ready)
       (member-equal
        record
        (fn-bpr-article-records
         (fn-rows-wire-of (fn-sf-records (fn-sn-files store)) fn-arena)))
       (let* ((node (fn-sn-node store))
              (article (fn-find-article
                        (fn-record-msgid record)
                        (fn-articles-wire-of
                         (fn-state-articles (fn-node-acceptance node)) fn-arena)))
              (binding (fn-node-find-binding
                        (fn-record-msgid record) (fn-node-bindings node))))
         (and (fn-node-statep node) (consp article) (consp binding)
              (equal (fn-article-payload article) (fn-record-payload record))
              (equal (fn-article-groups article) (fn-record-groups record))
              (equal (fn-node-binding-subject binding)
                     (fn-record-content-subject record))
              (equal (fn-node-binding-id binding)
                     (fn-record-obligation-id record))))
       t))
(bpr-lift bpra-over-alpha 2)
(bpr-lift fn-rows-composites-okp 1)

; Reachable positive witness: the hypothesis holds of the committed Store's
; history, and both sides hold of the wire record the dispatcher binds.
(assert-event (in-arena-fn-rows-composites-okp *bsb-payloads*
                                               (fn-sf-records (fn-sn-files *bsb-store*))))
(assert-event (in-arena-fn-bpr-store-record-acceptedp *bsb-payloads* *bsb-store* *bsb-record*))
(assert-event (in-arena-bpra-over-alpha *bsb-payloads* *bsb-store* *bsb-record*))
; ... and neither holds of the row itself (no wire record).
(assert-event (not (in-arena-fn-bpr-store-record-acceptedp *bsb-payloads* *bsb-store* *bsb-row*)))
(assert-event (not (in-arena-bpra-over-alpha *bsb-payloads* *bsb-store* *bsb-row*)))

; Hypothesis removal (fn-rows-composites-okp), a CORRUPTED-STATE witness no
; Store transition builds: the composite row's held row replaced by one that
; differs from the composite's article record only in its charge (a field
; the node does not compare).  The Store recognizer still holds; the
; hypothesis fails; the arena gate accepts the forged row's wire form while
; ALPHA's article is the composite's own record, so the equivalence fails.
(defconst *bpra-forged-held*
  (fn-held-make (fn-record-sequence *bsb-row*) (fn-record-txid *bsb-row*)
                (fn-record-generation *bsb-row*) (fn-record-msgid *bsb-row*)
                (fn-record-payload *bsb-row*) (fn-record-groups *bsb-row*)
                (fn-record-obligation-id *bsb-row*)
                (fn-record-content-subject *bsb-row*)
                (fn-record-release-evidence *bsb-row*)
                (+ 1 (fn-record-charge *bsb-row*)) (fn-record-stamp *bsb-row*)
                (fn-held-facts *bsb-row*) (fn-held-context *bsb-row*)
                (fn-held-numbers *bsb-row*) (fn-held-withdrawn *bsb-row*)))
(assert-event (fn-held-p *bpra-forged-held*))
(defconst *bpra-forged-records*
  (list *bsb-enrollment* (fn-hstxa-make *bsb-composite* *bpra-forged-held*)))
(defconst *bpra-forged-store*
  (fn-sn-update *bsb-store*
                (update-nth 4 *bpra-forged-records* (fn-sn-files *bsb-store*))
                (fn-sn-node *bsb-store*)))
(defconst *bpra-forged-record* (in-arena-fn-row-wire-of *bsb-payloads* *bpra-forged-held*))
(assert-event (equal (fn-sf-records (fn-sn-files *bpra-forged-store*)) *bpra-forged-records*))
(assert-event (fn-sn-statep *bpra-forged-store*))
(assert-event (not (in-arena-fn-rows-composites-okp *bsb-payloads* *bpra-forged-records*)))
(assert-event (in-arena-fn-bpr-store-record-acceptedp *bsb-payloads* *bpra-forged-store*
                                                      *bpra-forged-record*))
(assert-event (not (in-arena-bpra-over-alpha *bsb-payloads* *bpra-forged-store*
                                             *bpra-forged-record*)))
(must-fail
 (assert-event (iff (in-arena-fn-bpr-store-record-acceptedp *bsb-payloads* *bpra-forged-store*
                                                            *bpra-forged-record*)
                    (in-arena-bpra-over-alpha *bsb-payloads* *bpra-forged-store*
                                              *bpra-forged-record*))))
