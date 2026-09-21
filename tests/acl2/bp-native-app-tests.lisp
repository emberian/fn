(in-package "ACL2")
(include-book "../../books/bp-native-app")
(include-book "bp-receipt-records-tests")

(defconst *bpaj-request*
  (fn-bpa-make-request
   "work-native" (fn-record-content-subject *bpr-record*)
   "dtn://sender.lab" "dtn://fn.lab/inbox" "receiver-policy"
   "sender-inc-native" "wire-auth-context" "terms-1" *bpr-adu*))
(defconst *bpaj-request-octets* (fn-bpa-encode *bpaj-request*))
(defconst *bpaj-config* *bprr-config-record*)
(defconst *bpaj-intent*
  (list :request-intent "bundle-original" *bpaj-request-octets* 7
        (fn-record-txid *bpr-record*) :duplicate))
(defconst *bpaj-context*
  (list :request-context-v2 "bundle-original" *bpaj-request-octets*
        (fn-record-encode *bpr-record*) 7 (fn-record-txid *bpr-record*)
        (fn-record-generation *bpr-record*) t :duplicate))

(assert-event (fn-bpaj-intentp *bpaj-intent*))
(assert-event (fn-bpaj-context-v2p *bpaj-context*))

; Intent alone is not acceptance and produces no receipt.
(defconst *bpaj-intent-replay*
  (fn-bpaj-replay *bpr-store* (list *bpaj-config* *bpaj-intent*)))
(assert-event (car *bpaj-intent-replay*))
(assert-event
 (equal (fn-bpaj-request-status (fn-bpaj-nth 1 *bpaj-intent-replay*)
                                 *bpaj-request-octets*)
        :intent))
(assert-event
 (equal (fn-bpaj-dispatch (fn-bpaj-nth 1 *bpaj-intent-replay*)
                           *bpr-store* *bpaj-request-octets* 7)
        (list :bind *bpr-record*)))

(defconst *bpaj-context-replay*
  (fn-bpaj-replay *bpr-store*
                   (list *bpaj-config* *bpaj-intent* *bpaj-context*)))
(assert-event (car *bpaj-context-replay*))
(assert-event
 (equal (fn-bpaj-request-status (fn-bpaj-nth 1 *bpaj-context-replay*)
                                 *bpaj-request-octets*)
        :context))
(assert-event
 (equal (fn-bpaj-request-result (fn-bpaj-nth 1 *bpaj-context-replay*)
                                 *bpaj-request-octets*)
        :duplicate))

; Strict context has teeth: no intent, wrong generation, wrong transaction,
; wrong result, or a second candidate all prevent the binding.
(assert-event
 (not (car (fn-bpaj-replay *bpr-store*
                            (list *bpaj-config* *bpaj-context*)))))
(assert-event
 (not (car (fn-bpaj-replay
            *bpr-store*
            (list *bpaj-config* *bpaj-intent*
                  (update-nth 4 8 *bpaj-context*))))))
(assert-event
 (not (car (fn-bpaj-replay
            *bpr-store*
            (list *bpaj-config* *bpaj-intent*
                  (update-nth 5 (+ 1 (fn-record-txid *bpr-record*))
                              *bpaj-context*))))))
(assert-event
 (not (car (fn-bpaj-replay
            *bpr-store*
            (list *bpaj-config* *bpaj-intent*
                  (update-nth 8 :accepted *bpaj-context*))))))

; Reachable examples for the dispatcher projections: a matching current intent
; over an absent Store submits, while a stale generation or committed context
; does not.
(defconst *bpaj-fresh-store* (fn-sn-initial *bpr-groups* 20))
(defconst *bpaj-accept-intent*
  (list :request-intent "bundle-new" *bpaj-request-octets* 9 0 :accepted))
(defconst *bpaj-accept-replay*
  (fn-bpaj-replay *bpaj-fresh-store*
                   (list *bpaj-config* *bpaj-accept-intent*)))
(assert-event (car *bpaj-accept-replay*))
(assert-event
 (equal (fn-bpaj-dispatch (fn-bpaj-nth 1 *bpaj-accept-replay*)
                           *bpaj-fresh-store* *bpaj-request-octets* 9)
        (list :submit)))
(assert-event
 (not (equal (fn-bpaj-dispatch (fn-bpaj-nth 1 *bpaj-accept-replay*)
                                *bpaj-fresh-store* *bpaj-request-octets* 10)
             (list :submit))))
(assert-event
 (not (equal (fn-bpaj-dispatch (fn-bpaj-nth 1 *bpaj-context-replay*)
                                *bpr-store* *bpaj-request-octets* 7)
             (list :submit))))

; Legacy journals remain replayable only before the append-only intent
; vocabulary appears; a legacy context after strict mode is rejected.
(assert-event
 (car (fn-bpaj-replay *bpr-store*
                       (list *bpaj-config* *bprr-request-record*))))
(assert-event
 (not (car (fn-bpaj-replay
            *bpr-store*
            (list *bpaj-config* *bpaj-intent* *bprr-request-record*)))))
