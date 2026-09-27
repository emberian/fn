(in-package "ACL2")
(include-book "../../books/bp-native-app")
(include-book "../../books/codec-attach")
(include-book "bp-receipt-records-tests")

(defconst *bpaj-request*
  (fn-bpa-make-request
   "work-native" (fn-record-content-subject *bpr-record*)
   "dtn://sender.lab" "dtn://fn.lab/inbox" "receiver-policy"
   "sender-inc-native" "wire-auth-context" "terms-1" *bpr-adu*))
(defconst *bpaj-request-octets* (fn-bpa-encode *bpaj-request*))
(defconst *bpaj-config* *bprr-config-record*)
; PKT-646: the records carry the request's reference, never its bytes.
; Every intent is a transit intent (D34): a test intent pins the Store
; record's payload as its projection (its length and digest) under two
; Path identities; the builder over a live plan is bp-transit-join-tests'.
(defun bpaj-test-intent (inbound octets generation txid result stored)
  (let ((ref (fn-bpaj-request-ref (fn-bpaj-request octets))))
    (list :request-transit-intent inbound (car ref) generation txid result
          "peer-b" "fn.lab" "peer.lab" (cadr ref) (caddr ref)
          (len stored) (fn-frame-digest stored))))
(make-event `(defconst *bpaj-intent* ',(bpaj-test-intent "bundle-original" *bpaj-request-octets* 7
                         (fn-record-txid *bpr-record*) :duplicate
                         (fn-record-payload *bpr-record*))))
(make-event `(defconst *bpaj-context* ',(fn-bpaj-transit-context-record "bundle-original" *bpaj-request-octets*
                             (fn-record-encode-impl *bpr-record*) 7
                             (fn-record-txid *bpr-record*)
                             (fn-record-generation *bpr-record*) :duplicate)))

(assert-event (fn-bpaj-transit-intentp *bpaj-intent*))
(assert-event (fn-bpaj-transit-contextp *bpaj-context*))
; Neither holds the request's or the Store record's bytes.
(assert-event
 (and (not (member-equal *bpaj-request-octets* *bpaj-intent*))
      (not (member-equal (fn-record-payload *bpr-record*) *bpaj-intent*))
      (not (member-equal *bpaj-request-octets* *bpaj-context*))
      (not (member-equal (fn-record-encode-impl *bpr-record*) *bpaj-context*))))

; Intent alone is not acceptance and produces no receipt.
(bpr-lift fn-bpaj-dispatch 4)
(bpr-lift fn-bpaj-replay 2)

(make-event `(defconst *bpaj-intent-replay* ',(in-arena-fn-bpaj-replay *bpr-payloads* *bpr-store* (list *bpaj-config* *bpaj-intent*))))
(assert-event (car *bpaj-intent-replay*))
(assert-event
 (equal (fn-bpaj-request-status (fn-bpaj-nth 1 *bpaj-intent-replay*)
                                 *bpaj-request-octets*)
        :intent))
(assert-event
 (equal (in-arena-fn-bpaj-dispatch *bpr-payloads* (fn-bpaj-nth 1 *bpaj-intent-replay*) *bpr-store* *bpaj-request-octets* 7)
        (list :bind *bpr-record*)))

(make-event `(defconst *bpaj-context-replay* ',(in-arena-fn-bpaj-replay *bpr-payloads* *bpr-store* (list *bpaj-config* *bpaj-intent* *bpaj-context*))))
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
 (not (car (in-arena-fn-bpaj-replay *bpr-payloads* *bpr-store* (list *bpaj-config* *bpaj-context*)))))
(assert-event
 (not (car (in-arena-fn-bpaj-replay *bpr-payloads* *bpr-store* (list *bpaj-config* *bpaj-intent*
                  (update-nth 4 8 *bpaj-context*))))))
(assert-event
 (not (car (in-arena-fn-bpaj-replay *bpr-payloads* *bpr-store* (list *bpaj-config* *bpaj-intent*
                  (update-nth 5 (+ 1 (fn-record-txid *bpr-record*))
                              *bpaj-context*))))))
(assert-event
 (not (car (in-arena-fn-bpaj-replay *bpr-payloads* *bpr-store* (list *bpaj-config* *bpaj-intent*
                  (update-nth 7 :accepted *bpaj-context*))))))

; Reachable examples for the dispatcher projections: a matching current intent
; over an absent Store submits, while a stale generation or committed context
; does not.
(defconst *bpaj-fresh-store* (fn-sn-initial *bpr-groups* 20))
(make-event `(defconst *bpaj-accept-intent* ',(bpaj-test-intent "bundle-new" *bpaj-request-octets* 9 0 :accepted
                         (fn-record-payload *bpr-record*))))
(make-event `(defconst *bpaj-accept-replay* ',(in-arena-fn-bpaj-replay *bpr-payloads* *bpaj-fresh-store* (list *bpaj-config* *bpaj-accept-intent*))))
(assert-event (car *bpaj-accept-replay*))
(assert-event
 (equal (in-arena-fn-bpaj-dispatch *bpr-payloads* (fn-bpaj-nth 1 *bpaj-accept-replay*) *bpaj-fresh-store* *bpaj-request-octets* 9)
        (list :submit)))
(assert-event
 (not (equal (in-arena-fn-bpaj-dispatch *bpr-payloads* (fn-bpaj-nth 1 *bpaj-accept-replay*) *bpaj-fresh-store* *bpaj-request-octets* 10)
             (list :submit))))
(assert-event
 (not (equal (in-arena-fn-bpaj-dispatch *bpr-payloads* (fn-bpaj-nth 1 *bpaj-context-replay*) *bpr-store* *bpaj-request-octets* 7)
             (list :submit))))

; Legacy journals remain replayable only before the append-only intent
; vocabulary appears; a legacy context after strict mode is rejected.
(assert-event
 (car (in-arena-fn-bpaj-replay *bpr-payloads* *bpr-store* (list *bpaj-config* *bprr-request-record*))))
(assert-event
 (not (car (in-arena-fn-bpaj-replay *bpr-payloads* *bpr-store* (list *bpaj-config* *bpaj-intent* *bprr-request-record*)))))
