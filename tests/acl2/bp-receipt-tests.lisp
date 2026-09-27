(in-package "ACL2")
(include-book "../../books/bp-receipt")
(include-book "../../books/codec-attach")
(include-book "arena-lift")
; codecs withdrew the record and cbor proof vocabularies at export (2026-09-19);
; this book reasons under them, so open them here, locally.
(local (in-theory (enable fn-record-record-vocabulary fn-record-codec-vocabulary fn-record-guard-vocabulary
                          fn-record-invariants-vocabulary fn-cbor-record-vocabulary
                          fn-cbor-codec-vocabulary fn-cbor-invariants-vocabulary)))

(defconst *bpr-groups* '("fn.letters"))
(defconst *bpr-map*
  (list (list '(102 110 46 108 101 116 116 101 114 115) "fn.letters")))
(defconst *bpr-policy*
  (fn-bpi-make-policy "dtn://fn.lab/inbox" "dtn://fn.lab/inbox" *bpr-map*
                      "archive:receiver-1" "subject:receiver-1"
                      "unsigned-ingress-v0" 1 "receiver-policy" "terms-1"
                      "dtn://fn.lab/issuer"))
(defconst *bpr-context*
  (fn-bpi-make-context "dtn://fn.lab/inbox" "dtn://sender.lab"
                       "local-bid-1" 300 (fn-clock-observation 1 841000000000 0 t)))
(defconst *bpr-adu*
  '(77 101 115 115 97 103 101 45 73 68 58 32 60 114 101 99 101 105 112 116 45 49 64 101 120 97 109 112 108 101 62 13 10
    78 101 119 115 103 114 111 117 112 115 58 32 102 110 46 108 101 116 116 101 114 115 13 10 13 10
    66 111 100 121 13 10))
(defun bpr-reserve (s)
  (fn-sn-io (fn-sn-io (fn-sn-io (fn-sn-io s :start-frontier nil)
                                :frontier-file :ok)
                      :frontier-replace :ok)
            :frontier-directory :ok))
(defconst *bpr-prepared*
  (fn-bpi-ingress-prepare (bpr-reserve (fn-sn-initial *bpr-groups* 20))
                          *bpr-policy* *bpr-context* *bpr-adu* 0))
;; The Store retains the held ROW (its payload the handle 0); the receiver
;; is handed the WIRE record (the journal persists it), and reads the row's
;; bytes through an arena holding the ADU at handle 0 (records-flip).
(defconst *bpr-row* (fn-bpi-result-record *bpr-prepared*))
(defconst *bpr-record* (fn-bpi-result-wire *bpr-prepared*))
(defconst *bpr-store* (fn-bpi-finish-prepared (fn-bpi-result-store *bpr-prepared*)))
(assert-event (fn-bpi-durably-acceptedp *bpr-store* *bpr-row*))
(assert-event (fn-held-p *bpr-row*))
(assert-event (fn-record-p *bpr-record*))
(assert-event (equal (fn-record-payload *bpr-record*) *bpr-adu*))

(defconst *bpr-payloads* (list *bpr-adu*))
(bpr-lift fn-bpi-node-wire-committedp 2)
(bpr-lift fn-bpr-accept-request 5)
(bpr-lift fn-bpr-rows-stand-for 2)
(bpr-lift fn-bpr-store-record-acceptedp 2)


(defconst *bpr-request*
  (fn-bpa-make-request "work-1" "subject:receiver-1" "dtn://sender.lab"
                       "dtn://fn.lab/inbox" "receiver-policy" "sender-inc-7"
                       "wire-auth-context" "terms-1" *bpr-adu*))
(assert-event (fn-bpa-requestp *bpr-request*))
(assert-event (equal (fn-bpa-decode-exact (fn-bpa-encode *bpr-request*))
                     (list :ok *bpr-request*)))
(defconst *bpr-config*
  (fn-bpr-make-config "dtn://fn.lab/inbox" "receiver-policy"
                      "dtn://fn.lab/issuer"))
(defconst *bpr-initial* (fn-bpr-initial-state *bpr-config*))
(defconst *bpr-accepted*
  (in-arena-fn-bpr-accept-request *bpr-payloads* *bpr-initial* *bpr-store* *bpr-record* *bpr-request* t))
(assert-event (equal (car *bpr-accepted*) :accepted))
(defconst *bpr-context-state* (car (cdr *bpr-accepted*)))
(assert-event (fn-bpr-statep *bpr-context-state*))
; A wire authorization-context alone never substitutes the explicit lab
; A-POLICY input, even after the article is durably accepted.
(assert-event (equal (in-arena-fn-bpr-accept-request *bpr-payloads* *bpr-initial* *bpr-store* *bpr-record* *bpr-request* nil)
                     (list :refused *bpr-initial*)))
(assert-event (equal (fn-bpr-prepare-receipt *bpr-context-state* "work-1"
                                             "receipt-1" nil)
                     *bpr-context-state*))
(defconst *bpr-receipt-pending*
  (fn-bpr-prepare-receipt *bpr-context-state* "work-1" "receipt-1" t))
(assert-event (consp (fn-bpr-state-pending *bpr-receipt-pending*)))
(assert-event (equal (fn-bpr-receipt-adu *bpr-receipt-pending* *bpr-request*) nil))
(defconst *bpr-committed*
  (fn-bpr-commit-receipt *bpr-receipt-pending* "work-1" "receipt-1" :committed))
(defconst *bpr-receipt-adu* (fn-bpr-receipt-adu *bpr-committed* *bpr-request*))
(defconst *bpr-receipt-decode* (fn-bpa-decode-exact *bpr-receipt-adu*))
(assert-event (fn-bpa-result-okp *bpr-receipt-decode*))
(defconst *bpr-receipt* (fn-bpa-result-message *bpr-receipt-decode*))
(assert-event (equal (fn-bpa-receipt-work-id *bpr-receipt*) "work-1"))
(assert-event (equal (fn-bpa-receipt-subject *bpr-receipt*) "subject:receiver-1"))
(assert-event (equal (fn-bpa-receipt-issuer *bpr-receipt*) "dtn://fn.lab/issuer"))
(assert-event (equal (fn-bpa-receipt-peer-eid *bpr-receipt*) "dtn://fn.lab/inbox"))
(assert-event (equal (fn-bpa-receipt-incarnation *bpr-receipt*) "sender-inc-7"))
(assert-event (equal (fn-bpa-receipt-auth-context *bpr-receipt*) "wire-auth-context"))
; A restart/new BPA transport reference reuses the exact committed request
; context and regenerates the same receipt ADU without changing Store state.
(assert-event (equal (fn-bpr-receipt-adu *bpr-committed* *bpr-request*)
                     *bpr-receipt-adu*))
(assert-event (fn-bpi-durably-acceptedp *bpr-store* *bpr-row*))
(defconst *bpr-conflicting-request*
  (fn-bpa-make-request "work-1" "subject:receiver-1" "dtn://sender.lab"
                       "dtn://fn.lab/inbox" "receiver-policy" "sender-inc-evil"
                       "wire-auth-context" "terms-1" *bpr-adu*))
(assert-event (equal (car (in-arena-fn-bpr-accept-request *bpr-payloads* *bpr-context-state* *bpr-store* *bpr-record* *bpr-conflicting-request* t))
                     :conflict))
(assert-event (equal (fn-bpr-commit-receipt *bpr-receipt-pending*
                                             "work-stale" "receipt-stale" :committed)
                     *bpr-receipt-pending*))
(assert-event (equal (car (in-arena-fn-bpr-accept-request *bpr-payloads* *bpr-receipt-pending* *bpr-store* *bpr-record* *bpr-request* t))
                     :refused))

; A recovered article/binding alone is not enough while recovery barriers are
; incomplete.  Once the observed file machine is ready, the exact durable
; record list and rebuilt node support replay of the receiver request context.
(defun bpr-ready-after-barriers (s n)
  (if (zp n) s
    (bpr-ready-after-barriers (fn-sn-io s :recovery-barrier :ok) (1- n))))
(defconst *bpr-recovering-store*
  (fn-sn-recover (fn-sn-crash *bpr-store* :old :present)))
(assert-event (equal (fn-sf-phase (fn-sn-files *bpr-recovering-store*))
                     :recovering))
(assert-event (not (in-arena-fn-bpr-store-record-acceptedp *bpr-payloads* *bpr-recovering-store* *bpr-record*)))
(defconst *bpr-recovered-ready-store*
  (bpr-ready-after-barriers *bpr-recovering-store* 5))
(assert-event (equal (fn-sf-phase (fn-sn-files *bpr-recovered-ready-store*))
                     :ready))
(assert-event (in-arena-fn-bpr-store-record-acceptedp *bpr-payloads* *bpr-recovered-ready-store* *bpr-record*))
(assert-event (equal
 (car (in-arena-fn-bpr-accept-request *bpr-payloads* *bpr-initial* *bpr-recovered-ready-store* *bpr-record* *bpr-request* t))
 :accepted))

; The receiver reads the retained row's bytes through the arena
; (fn-bpr-store-record-acceptedp over fn-bpr-rows-stand-for and
; fn-bpi-node-wire-committedp): the same Store and wire record are accepted
; over the arena that holds the ADU at the row's handle, and refused over an
; arena that holds other bytes there, or none.
(defconst *bpr-other-adu* (append *bpr-adu* (list 13 10)))
(assert-event (in-arena-fn-bpr-store-record-acceptedp *bpr-payloads* *bpr-store* *bpr-record*))
(assert-event (in-arena-fn-bpr-rows-stand-for *bpr-payloads* *bpr-record* (fn-bpr-article-records (fn-sf-records (fn-sn-files *bpr-store*)))))
(assert-event (in-arena-fn-bpi-node-wire-committedp *bpr-payloads* (fn-sn-node *bpr-store*) *bpr-record*))
(assert-event (not (in-arena-fn-bpr-store-record-acceptedp (list *bpr-other-adu*)
                                                            *bpr-store* *bpr-record*)))
(assert-event (not (in-arena-fn-bpr-store-record-acceptedp nil *bpr-store* *bpr-record*)))
(assert-event (equal (in-arena-fn-bpr-accept-request (list *bpr-other-adu*)
                                                     *bpr-initial* *bpr-store* *bpr-record*
                                                     *bpr-request* t)
                     (list :refused *bpr-initial*)))
; The row itself is no wire record: handed the row, the receiver refuses.
(assert-event (not (in-arena-fn-bpr-store-record-acceptedp *bpr-payloads* *bpr-store* *bpr-row*)))
