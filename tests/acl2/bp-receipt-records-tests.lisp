(in-package "ACL2")
(include-book "../../books/bp-receipt-records")
(include-book "bp-receipt-tests")
(defconst *bprr-config-record* '(:config "dtn://fn.lab/inbox" "receiver-policy" "dtn://fn.lab/issuer"))
(defconst *bprr-request-record* (list :request-context "local-bid-1"
 (fn-bpa-encode *bpr-request*) (fn-record-encode *bpr-record*) t))
(defconst *bprr-context-answer* (fn-bprr-replay *bpr-store*
 (list *bprr-config-record* *bprr-request-record*)))
(assert-event (car *bprr-context-answer*))
(defconst *bprr-context* (car (fn-bpr-state-contexts (fn-bprr-nth 1 *bprr-context-answer*))))
(defconst *bprr-receipt* (fn-bpr-receipt-for *bprr-context* *bpr-config* "receipt-1"))
(defconst *bprr-intent-record* (list :receipt-intent "work-1" "receipt-1"
 (fn-bpa-encode *bprr-receipt*) t))
(defconst *bprr-decision-record* '(:receipt-decision "work-1" "receipt-1" :committed))
(defconst *bprr-full* (fn-bprr-replay *bpr-store*
 (list *bprr-config-record* *bprr-request-record* *bprr-intent-record* *bprr-decision-record*)))
(assert-event (car *bprr-full*))
(assert-event (equal (fn-bpr-receipt-adu (fn-bprr-nth 1 *bprr-full*) *bpr-request*)
                     (fn-bpa-encode *bprr-receipt*)))
(assert-event (not (car (fn-bprr-replay *bpr-store*
 (list *bprr-config-record* *bprr-request-record* *bprr-request-record*)))))
(assert-event (not (car (fn-bprr-replay *bpr-store*
 (list *bprr-config-record* *bprr-request-record*
       (update-nth 3 '(1 2 3) *bprr-intent-record*))))))
(assert-event (not (car (fn-bprr-replay *bpr-store*
 (list *bprr-config-record* *bprr-request-record* *bprr-intent-record*
       '(:receipt-decision "work-1" "receipt-old" :committed))))))
(defconst *bprr-absent* (fn-bprr-replay *bpr-store*
 (list *bprr-config-record* *bprr-request-record* *bprr-intent-record*
       '(:receipt-decision "work-1" "receipt-1" :absent))))
(assert-event (car *bprr-absent*))
(assert-event (equal (fn-bpr-receipt-adu (fn-bprr-nth 1 *bprr-absent*) *bpr-request*) nil))
