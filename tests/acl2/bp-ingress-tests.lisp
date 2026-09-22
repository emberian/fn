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
                       "bpa-local-42" 3600))
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
  (fn-bpi-ingress-prepare *bpi-reserved* *bpi-policy* *bpi-context* *bpi-adu*))
(assert-event (equal (fn-bpi-result-kind *bpi-prepared*) :prepared))
(defconst *bpi-record* (fn-bpi-result-record *bpi-prepared*))
(assert-event (equal (fn-record-payload *bpi-record*) *bpi-adu*))
(assert-event (equal (fn-record-string-octets (fn-record-msgid *bpi-record*))
                     '(60 98 112 45 49 64 101 120 97 109 112 108 101 62)))
(defconst *bpi-done* (fn-bpi-finish-prepared (fn-bpi-result-store *bpi-prepared*)))
(assert-event (fn-bpi-durably-acceptedp *bpi-done* *bpi-record*))
(assert-event (fn-bpi-adu-durably-acceptedp *bpi-done* *bpi-policy*
                                             *bpi-context* *bpi-adu*))
(assert-event (equal (fn-bpi-receipt-eligibility *bpi-done* *bpi-record*
                                                   *bpi-policy* *bpi-context*)
                     (list :eligible "<bp-1@example>" "legacy-article:bp-1"
                           "archive:bp-1" "bp-policy-v0" "bp-terms-v0"
                           "dtn://fn.example" "dtn://peer.example")))
; A replay after durable completion is refused by the actual Store duplicate
; gate; no second record and no transport identity are invented.
(defconst *bpi-duplicate*
  (fn-bpi-ingress-prepare (bpi-reserve *bpi-done*) *bpi-policy*
                          *bpi-context* *bpi-adu*))
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
(assert-event (fn-bpi-adu-durably-acceptedp *bpi-restarted* *bpi-policy*
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
                                                    "bpa-local-42" 3600))
                     nil))
; Parser/semantic and policy failures happen before Store preparation.
(assert-event (equal (fn-bpi-result-kind
                      (fn-bpi-ingress-prepare *bpi-reserved* *bpi-policy*
                                              *bpi-context* '(1 2 3)))
                     :rejected))
(assert-event (equal (fn-bpi-result-kind
                      (fn-bpi-ingress-prepare *bpi-reserved* *bpi-policy*
                       (fn-bpi-make-context "dtn://wrong/inbox" "dtn://peer.example"
                                            "bpa-local-42" 3600)
                       *bpi-adu*))
                     :rejected))
; Critical-field and group-policy rejections use the actual ACL2 article and
; article-fields grammar; the host never duplicates this parsing.
(defconst *bpi-no-groups-adu*
  '(77 101 115 115 97 103 101 45 73 68 58 32 60 98 112 45 50 64 101 120 97 109 112 108 101 62 13 10
    13 10 66 111 100 121 13 10))
(assert-event (equal (fn-bpi-ingress-prepare *bpi-reserved* *bpi-policy*
                                             *bpi-context* *bpi-no-groups-adu*)
                     '(:rejected :newsgroups-missing)))
(defconst *bpi-no-message-id-adu*
  '(78 101 119 115 103 114 111 117 112 115 58 32 102 110 46 108 101 116 116 101 114 115 13 10
    13 10 66 111 100 121 13 10))
(assert-event (equal (fn-bpi-ingress-prepare *bpi-reserved* *bpi-policy*
                                             *bpi-context* *bpi-no-message-id-adu*)
                     '(:rejected :message-id-missing)))
(defconst *bpi-duplicate-message-id-adu*
  '(77 101 115 115 97 103 101 45 73 68 58 32 60 98 112 45 51 64 101 120 97 109 112 108 101 62 13 10
    77 101 115 115 97 103 101 45 73 68 58 32 60 98 112 45 52 64 101 120 97 109 112 108 101 62 13 10
    78 101 119 115 103 114 111 117 112 115 58 32 102 110 46 108 101 116 116 101 114 115 13 10 13 10
    66 111 100 121 13 10))
(assert-event (equal (fn-bpi-ingress-prepare *bpi-reserved* *bpi-policy*
                                             *bpi-context*
                                             *bpi-duplicate-message-id-adu*)
                     '(:rejected :message-id-duplicate)))
(defconst *bpi-duplicate-newsgroups-adu*
  '(77 101 115 115 97 103 101 45 73 68 58 32 60 98 112 45 54 64 101 120 97 109 112 108 101 62 13 10
    78 101 119 115 103 114 111 117 112 115 58 32 102 110 46 108 101 116 116 101 114 115 13 10
    78 101 119 115 103 114 111 117 112 115 58 32 102 110 46 116 101 115 116 13 10 13 10
    66 111 100 121 13 10))
(assert-event (equal (fn-bpi-ingress-prepare *bpi-reserved* *bpi-policy*
                                             *bpi-context*
                                             *bpi-duplicate-newsgroups-adu*)
                     '(:rejected :newsgroups-duplicate)))
(defconst *bpi-unknown-group-adu*
  '(77 101 115 115 97 103 101 45 73 68 58 32 60 98 112 45 53 64 101 120 97 109 112 108 101 62 13 10
    78 101 119 115 103 114 111 117 112 115 58 32 102 110 46 103 104 111 115 116 13 10 13 10
    66 111 100 121 13 10))
(assert-event (equal (fn-bpi-ingress-prepare *bpi-reserved* *bpi-policy*
                                             *bpi-context* *bpi-unknown-group-adu*)
                     '(:rejected :unknown-group)))
