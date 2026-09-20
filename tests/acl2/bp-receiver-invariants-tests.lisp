(in-package "ACL2")
(include-book "../../books/bp-receiver-trace-invariants")
(include-book "bp-receipt-records-tests")
; codecs withdrew the record and cbor proof vocabularies at export (2026-09-19);
; this book reasons under them, so open them here, locally.
(local (in-theory (enable fn-record-record-vocabulary fn-record-codec-vocabulary fn-record-guard-vocabulary
                          fn-record-invariants-vocabulary fn-cbor-record-vocabulary
                          fn-cbor-codec-vocabulary fn-cbor-invariants-vocabulary)))

(defconst *bprv-journal*
 (list *bprr-config-record* *bprr-request-record* *bprr-intent-record* *bprr-decision-record*))
(defconst *bprv-replayed* (cadr (fn-bprr-replay *bpr-recovered-ready-store* *bprv-journal*)))
(assert-event (fn-bprv-invariantp *bpr-recovered-ready-store* *bprv-replayed* *bprv-journal*))
(assert-event (fn-bprv-relationalp *bpr-recovered-ready-store* *bprv-replayed*))
(assert-event (fn-bprv-entries-decidedp (fn-bpr-state-receipts *bprv-replayed*) *bprv-journal*))
(assert-event (equal (fn-bpr-receipt-adu *bprv-replayed* *bpr-request*) *bpr-receipt-adu*))

; Typed receiver state alone does not establish stored-context or receipt binding.
(defconst *bprv-orphan-decision*
 (fn-bpr-make-state *bpr-config* nil (fn-bpr-state-receipts *bprv-replayed*) nil))
(assert-event (fn-bpr-statep *bprv-orphan-decision*))
(assert-event (not (fn-bprv-relationalp *bpr-store* *bprv-orphan-decision*)))
(defconst *bprv-forged-receipt*
 (fn-bpa-make-receipt "receipt-1" "work-1" "wrong-subject"
  "dtn://fn.lab/issuer" "dtn://fn.lab/inbox" "receiver-policy"
  "sender-inc-7" "wire-auth-context" "terms-1"))
(defconst *bprv-mismatched-decision*
 (fn-bpr-make-state *bpr-config* (fn-bpr-state-contexts *bprv-replayed*)
   (list (fn-bpr-make-receipt-entry *bprr-context* *bprv-forged-receipt*)) nil))
(assert-event (fn-bpr-statep *bprv-mismatched-decision*))
(assert-event (not (fn-bprv-relationalp *bpr-store* *bprv-mismatched-decision*)))
(assert-event (not (fn-bprv-relationalp *bpr-recovering-store* *bprv-replayed*)))

; Pending/absent outcomes cannot generate receipt bytes.
(defconst *bprv-intent-only*
 (list *bprr-config-record* *bprr-request-record* *bprr-intent-record*))
(assert-event (fn-bprv-no-committed-decisionsp *bprv-intent-only*))
(assert-event (equal (fn-bpr-receipt-adu
 (cadr (fn-bprr-replay *bpr-store* *bprv-intent-only*)) *bpr-request*) nil))
(assert-event (equal (fn-bpr-receipt-adu (cadr *bprr-absent*) *bpr-request*) nil))

; Replay stops on a duplicate/malformed journal record and retains the committed prefix.
(defconst *bprv-duplicate-extension*
 (fn-bprr-replay-rest *bprv-replayed* *bpr-recovered-ready-store*
                     (list *bprr-request-record*)))
(assert-event (not (car *bprv-duplicate-extension*)))
(assert-event (equal (cadr *bprv-duplicate-extension*) *bprv-replayed*))
(assert-event (equal (fn-bpr-receipt-adu (cadr *bprv-duplicate-extension*) *bpr-request*)
                     *bpr-receipt-adu*))
(assert-event (equal (cadr (fn-bprr-replay-rest *bprv-replayed* *bpr-recovered-ready-store*
                                             '((:broken) (:receipt-decision))))
                     *bprv-replayed*))
; Unready Store replay cannot reconstruct an accepted context or emit a receipt.
(assert-event (not (car (fn-bprr-replay *bpr-recovering-store* *bprv-journal*))))
(assert-event (equal (fn-bpr-receipt-adu
 (cadr (fn-bprr-replay *bpr-recovering-store* *bprv-journal*)) *bpr-request*) nil))
