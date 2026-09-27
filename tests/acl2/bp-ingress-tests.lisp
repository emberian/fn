(in-package "ACL2")
(include-book "../../books/bp-ingress")
(include-book "../../books/codec-attach")
; codecs withdrew the record and cbor proof vocabularies at export (2026-09-19);
; this book reasons under them, so open them here, locally.
(local (in-theory (enable fn-record-record-vocabulary fn-record-codec-vocabulary fn-record-guard-vocabulary
                          fn-cbor-record-vocabulary fn-cbor-codec-vocabulary)))

(defconst *bpi-groups* '("fn.letters" "fn.test"))
(defconst *bpi-map*
  (list (list '(102 110 46 108 101 116 116 101 114 115) "fn.letters")
        (list '(102 110 46 116 101 115 116) "fn.test")))
(defconst *bpi-policy*
  (fn-bpi-make-policy "dtn://fn.example/inbox" "dtn://fn.example/inbox"
                      *bpi-map* "archive:bp-1" "legacy-article:bp-1"
                      "unsigned-ingress-v0" 3 "bp-policy-v0" "bp-terms-v0"
                      "dtn://fn.example"))
(defconst *bpi-context*
  (fn-bpi-make-context "dtn://fn.example/inbox" "dtn://peer.example"
                       "bpa-local-42" 3600 (fn-clock-observation 1 841000000000 0 t)))
(defconst *bpi-adu*
  '(77 101 115 115 97 103 101 45 73 68 58 32 60 98 112 45 49 64 101 120 97 109 112 108 101 62 13 10
    78 101 119 115 103 114 111 117 112 115 58 32 102 110 46 108 101 116 116 101 114 115 13 10 13 10
    66 111 100 121 13 10))
(defun bpi-reserve (s)
  (fn-sn-io (fn-sn-io (fn-sn-io (fn-sn-io s :start-frontier nil)
                                :frontier-file :ok)
                      :frontier-replace :ok)
            :frontier-directory :ok))
(defconst *bpi-reserved* (bpi-reserve (fn-sn-initial *bpi-groups* 20)))
(defconst *bpi-prepared*
  (fn-bpi-ingress-prepare *bpi-reserved* *bpi-policy* *bpi-context* *bpi-adu* 0))
(assert-event (equal (fn-bpi-result-kind *bpi-prepared*) :prepared))
(defconst *bpi-record* (fn-bpi-result-record *bpi-prepared*))
; The store stages a ROW (records-flip): its payload is the handle, 0 here;
; the wire record the ADU composed to carries the ADU itself.
(assert-event (fn-held-p *bpi-record*))
(assert-event (equal (fn-record-payload *bpi-record*) 0))
(defconst *bpi-wire* (fn-bpi-result-wire *bpi-prepared*))
(assert-event (fn-record-p *bpi-wire*))
(assert-event (equal (fn-record-payload *bpi-wire*) *bpi-adu*))
; THE ENTRY over a local arena (fn-bpi-ingress-prepare-interned-row-is-the-
; received-adu): (result count row-wire row-bytes).
(defun bpi-entry-in (store policy context adu fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (mv-let (r fn-arena)
    (fn-bpi-ingress-prepare-interned store policy context adu fn-arena)
    (mv (list r (fn-arena-count fn-arena)
              (fn-row-wire-of (fn-bpi-result-record r) fn-arena)
              (fn-row-bytes (fn-bpi-result-record r) fn-arena))
        fn-arena)))
(defun bpi-entry (store policy context adu)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (x fn-arena) (bpi-entry-in store policy context adu fn-arena) x)))
(defconst *bpi-entry* (bpi-entry *bpi-reserved* *bpi-policy* *bpi-context* *bpi-adu*))
(assert-event (equal (nth 0 *bpi-entry*) *bpi-prepared*))
(assert-event (equal (nth 1 *bpi-entry*) 1))
(assert-event (equal (nth 2 *bpi-entry*) *bpi-wire*))
(assert-event (equal (nth 3 *bpi-entry*) *bpi-adu*))
; Tooth for the :prepared hypothesis: a rejected ADU seals nothing.
(defconst *bpi-entry-rejected* (bpi-entry *bpi-reserved* *bpi-policy* *bpi-context* '(1 2 3)))
(assert-event (equal (fn-bpi-result-kind (nth 0 *bpi-entry-rejected*)) :rejected))
(assert-event (equal (nth 1 *bpi-entry-rejected*) 0))
; The durable query over an arena holding the ADU at handle 0.
(defun bpi-durable-in (store policy context adu fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (let ((fn-arena (fn-arena-seal-list adu fn-arena)))
    (mv (fn-bpi-adu-durably-acceptedp store policy context adu fn-arena) fn-arena)))
(defun bpi-durable (store policy context adu)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (x fn-arena) (bpi-durable-in store policy context adu fn-arena) x)))
(assert-event (equal (fn-record-stamp *bpi-record*) 841000000))
(defconst *bpi-no-clock-context*
  (fn-bpi-make-context "dtn://fn.example/inbox" "dtn://peer.example"
                       "bpa-local-42" 3600 (fn-clock-observation 1 0 0 nil)))
(defconst *bpi-no-clock*
  (fn-bpi-ingress-prepare *bpi-reserved* *bpi-policy*
                          *bpi-no-clock-context* *bpi-adu* 0))
(assert-event (equal (fn-bpi-result-kind *bpi-no-clock*) :rejected))
(assert-event (equal (fn-bpi-result-store *bpi-no-clock*) :clock-unusable))
(assert-event (null (fn-bpi-result-record *bpi-no-clock*)))
(assert-event (equal (fn-record-string-octets (fn-record-msgid *bpi-record*))
                     '(60 98 112 45 49 64 101 120 97 109 112 108 101 62)))
(defconst *bpi-done* (fn-bpi-finish-prepared (fn-bpi-result-store *bpi-prepared*)))
(assert-event (fn-bpi-durably-acceptedp *bpi-done* *bpi-record*))
(assert-event (bpi-durable *bpi-done* *bpi-policy*
                                             *bpi-context* *bpi-adu*))
; Its tooth: over an arena whose handle 0 holds other bytes it is false.
(assert-event (not (bpi-durable *bpi-done* *bpi-policy* *bpi-context* '(1 2 3))))
(assert-event (equal (fn-bpi-receipt-eligibility *bpi-done* *bpi-record*
                                                   *bpi-policy* *bpi-context*)
                     (list :eligible "<bp-1@example>" "legacy-article:bp-1"
                           "archive:bp-1" "bp-policy-v0" "bp-terms-v0"
                           "dtn://fn.example" "dtn://peer.example")))
; A replay after durable completion is refused by the actual Store duplicate
; gate; no second record and no transport identity are invented.
(defconst *bpi-duplicate*
  (fn-bpi-ingress-prepare (bpi-reserve *bpi-done*) *bpi-policy*
                          *bpi-context* *bpi-adu* 0))
(assert-event (equal (fn-bpi-result-kind *bpi-duplicate*) :rejected))
(assert-event (equal (fn-bpi-result-store *bpi-duplicate*) :store-refused))
(assert-event (equal (fn-bpi-result-record *bpi-duplicate*) nil))
; Restart/replay reconstructs the accepted article and its prior local durable
; success.  This only re-establishes unsigned eligibility; it does not create a
; receipt-intent decision, authorization, or signature.
(defconst *bpi-restarted*
  (fn-sn-recover (fn-sn-crash *bpi-done* :old :present)))
(assert-event (fn-bpi-node-record-committedp (fn-sn-node *bpi-restarted*)
                                             *bpi-record*))
(assert-event (bpi-durable *bpi-restarted* *bpi-policy*
                                             *bpi-context* *bpi-adu*))
(assert-event (equal (fn-bpi-receipt-eligibility *bpi-restarted* *bpi-record*
                                                  *bpi-policy* *bpi-context*)
                     (fn-bpi-receipt-eligibility *bpi-done* *bpi-record*
                                                 *bpi-policy* *bpi-context*)))
(defconst *bpi-wrong-subject-policy*
  (fn-bpi-make-policy "dtn://fn.example/inbox" "dtn://fn.example/inbox"
                      *bpi-map* "archive:wrong" "legacy-article:wrong"
                      "unsigned-ingress-v0" 3 "bp-policy-v0" "bp-terms-v0"
                      "dtn://fn.example"))
(assert-event (equal (fn-bpi-receipt-eligibility *bpi-done* *bpi-record*
                                                   *bpi-wrong-subject-policy*
                                                   *bpi-context*)
                     nil))
(assert-event (equal (fn-bpi-receipt-eligibility *bpi-done* *bpi-record*
                                                   *bpi-policy*
                                                   (fn-bpi-make-context
                                                    "dtn://wrong/inbox"
                                                    "dtn://peer.example"
                                                    "bpa-local-42" 3600 (fn-clock-observation 1 841000000000 0 t)))
                     nil))
; Parser/semantic and policy failures happen before Store preparation.
(assert-event (equal (fn-bpi-result-kind
                      (fn-bpi-ingress-prepare *bpi-reserved* *bpi-policy*
                                              *bpi-context* '(1 2 3) 0))
                     :rejected))
(assert-event (equal (fn-bpi-result-kind
                      (fn-bpi-ingress-prepare *bpi-reserved* *bpi-policy*
                       (fn-bpi-make-context "dtn://wrong/inbox" "dtn://peer.example"
                                            "bpa-local-42" 3600 (fn-clock-observation 1 841000000000 0 t))
                       *bpi-adu* 0))
                     :rejected))
; Critical-field and group-policy rejections use the actual ACL2 article and
; article-fields grammar; the host never duplicates this parsing.
(defconst *bpi-no-groups-adu*
  '(77 101 115 115 97 103 101 45 73 68 58 32 60 98 112 45 50 64 101 120 97 109 112 108 101 62 13 10
    13 10 66 111 100 121 13 10))
(assert-event (equal (fn-bpi-ingress-prepare *bpi-reserved* *bpi-policy*
                                             *bpi-context* *bpi-no-groups-adu* 0)
                     '(:rejected :newsgroups-missing)))
(defconst *bpi-no-message-id-adu*
  '(78 101 119 115 103 114 111 117 112 115 58 32 102 110 46 108 101 116 116 101 114 115 13 10
    13 10 66 111 100 121 13 10))
(assert-event (equal (fn-bpi-ingress-prepare *bpi-reserved* *bpi-policy*
                                             *bpi-context* *bpi-no-message-id-adu* 0)
                     '(:rejected :message-id-missing)))
(defconst *bpi-duplicate-message-id-adu*
  '(77 101 115 115 97 103 101 45 73 68 58 32 60 98 112 45 51 64 101 120 97 109 112 108 101 62 13 10
    77 101 115 115 97 103 101 45 73 68 58 32 60 98 112 45 52 64 101 120 97 109 112 108 101 62 13 10
    78 101 119 115 103 114 111 117 112 115 58 32 102 110 46 108 101 116 116 101 114 115 13 10 13 10
    66 111 100 121 13 10))
(assert-event (equal (fn-bpi-ingress-prepare *bpi-reserved* *bpi-policy*
                                             *bpi-context*
                                             *bpi-duplicate-message-id-adu* 0)
                     '(:rejected :message-id-duplicate)))
(defconst *bpi-duplicate-newsgroups-adu*
  '(77 101 115 115 97 103 101 45 73 68 58 32 60 98 112 45 54 64 101 120 97 109 112 108 101 62 13 10
    78 101 119 115 103 114 111 117 112 115 58 32 102 110 46 108 101 116 116 101 114 115 13 10
    78 101 119 115 103 114 111 117 112 115 58 32 102 110 46 116 101 115 116 13 10 13 10
    66 111 100 121 13 10))
(assert-event (equal (fn-bpi-ingress-prepare *bpi-reserved* *bpi-policy*
                                             *bpi-context*
                                             *bpi-duplicate-newsgroups-adu* 0)
                     '(:rejected :newsgroups-duplicate)))
(defconst *bpi-unknown-group-adu*
  '(77 101 115 115 97 103 101 45 73 68 58 32 60 98 112 45 53 64 101 120 97 109 112 108 101 62 13 10
    78 101 119 115 103 114 111 117 112 115 58 32 102 110 46 103 104 111 115 116 13 10 13 10
    66 111 100 121 13 10))
(assert-event (equal (fn-bpi-ingress-prepare *bpi-reserved* *bpi-policy*
                                             *bpi-context* *bpi-unknown-group-adu* 0)
                     '(:rejected :unknown-group)))
