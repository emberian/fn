; PKT-646, PRF-249: the BP application join carries a request by
; REFERENCE, and every read of a durable record binds exactly the receiver
; context the live request defines, without reading the request's bytes.
;
; Host subjects (books/bp-native-app.lisp, books/bp-transit-join.lisp;
; host/bp-receipt-journal-host.lisp calls the builders, host/native/bp-app.lisp
; `fnn-bpapp-request-intent' and `fnn-bpapp-bind-context' publish their
; records):
;   - `fn-bpaj-transit-intent-from-plan' (called by host/bp-native-app-host.lisp
;     `fn-owner-app-plan-install'), `fn-bpaj-transit-context-record': the FNRJ
;     records carry (HEAD LENGTH DIGEST), `fn-bpaj-request-ref', and the
;     intent the relay projection's LENGTH and DIGEST;
;   - every read of a transit context (`fn-bpaj-apply-record' and its fast
;     twin, called by `fn-bprj-install' at every journal open, recovery
;     included, and by `fn-bprj-preflight'/`fn-bprj-apply' at publication)
;     resolves the Store record by identity (`fn-bpaj-context-record') and
;     binds the receiver context from the reference
;     (`fn-bpr-accept-projected-ref', `fn-bpr-context-from-ref');
;   - `fn-bpaj-intent-names-requestp': how `fn-bpaj-request-status' (and the
;     fast twin the host calls) compares a live request with an intent.
;
; What is proved:
;   KEYSTONE fn-bpaj-ref-request-resolves-exactly (books/bp-request-ref.lisp):
;     a request's reference resolves over its own article to that request;
;     -to-the-bytes below: the encoding of that resolution is its octets.
;   KEYSTONE fn-bpaj-transit-context-binds-the-live-request: the receiver
;     context a replay binds from a context the host published for request
;     octets R and Store record S is exactly the context binding R to S
;     defines, and its reference is R's (so `fn-bpr-receipt-adu' answers R).
;   KEYSTONE fn-bpaj-transit-intent-pins-its-request-and-projection: an
;     intent the host publishes names R, and pins the length and digest of
;     the relay projection of R's article under the intent's own Path
;     identities, the bytes the Store will hold.
;   fn-bpaj-one-reference-is-one-request-or-a-digest-collision: a different
;     request an intent names has the same metadata and an article of the
;     same length and `fn-frame-digest' (A-CRYPTO, books/frame-octets:
;     SHA-256, whose collision resistance is outside the logic; for n
;     distinct articles the collision probability is at most n(n-1)/2^257).
(in-package "ACL2")
(include-book "bp-native-app-fast")
(include-book "bp-transit-join")
(local (include-book "bp-receiver-state-invariants"))

; ... and its encoding is the request's octets.
(defthm fn-bpaj-ref-request-resolves-to-the-bytes
  (implies (fn-bpaj-request octets)
           (equal (fn-bpa-encode
                   (fn-bpaj-ref-request
                    (car (fn-bpaj-request-ref (fn-bpaj-request octets)))
                    (cadr (fn-bpaj-request-ref (fn-bpaj-request octets)))
                    (caddr (fn-bpaj-request-ref (fn-bpaj-request octets)))
                    (fn-bpa-request-article (fn-bpaj-request octets))))
                  octets))
  :hints (("Goal"
           :use ((:instance fn-bpaj-ref-request-resolves-exactly
                            (request (fn-bpaj-request octets)))
                 (:instance fn-bpa-success-is-canonical))
           :in-theory (e/d (fn-bpaj-request)
                           (fn-bpaj-ref-request-resolves-exactly
                            fn-bpa-success-is-canonical
                            fn-bpaj-ref-request fn-bpaj-request-ref
                            fn-bpa-encode fn-bpa-decode-exact
                            fn-bpa-requestp)))))


(local
 (defthm fn-bprf-request-is-requestp
   (implies (fn-bpaj-request octets)
            (fn-bpa-requestp (fn-bpaj-request octets)))
   :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                                              '(fn-bpaj-request))))))

(local
 (defthm fn-bprf-transit-context-record-ref
   (implies (fn-bpaj-transit-context-record inbound octets store-record
                                            generation txid rg result)
            (and (fn-bpaj-request octets)
                 (equal (fn-bpaj-context-ref
                         (fn-bpaj-transit-context-record
                          inbound octets store-record generation txid rg
                          result))
                        (fn-bpaj-request-ref (fn-bpaj-request octets)))))
   :hints (("Goal" :in-theory (e/d (fn-bpaj-transit-context-record
                                    fn-bpaj-context-ref fn-bpaj-nth
                                    fn-bpaj-request-ref)
                                   (fn-bpaj-transit-contextp fn-bpaj-request
                                    fn-bpaj-head-octets))))))

; KEYSTONE.  Every read of a context the host published for request octets
; R binds, over whatever Store record RECORD the read resolves, exactly the
; receiver context binding R's request to RECORD defines -- no bytes of R
; read -- and that context's reference is R's, the key
; `fn-bpr-receipt-adu' compares.
(defthm fn-bpaj-transit-context-binds-the-live-request
  (implies (fn-bpaj-transit-context-record inbound octets store-record
                                           generation txid rg result)
           (let ((ctx (fn-bpaj-transit-context-record
                       inbound octets store-record generation txid rg
                       result)))
             (and (equal (fn-bpr-context-from-ref
                          record (fn-bpaj-context-ref ctx))
                         (fn-bpr-context-from-request
                          record (fn-bpaj-request octets)))
                  (equal (fn-bpr-context-request-ref
                          (fn-bpr-context-from-ref
                           record (fn-bpaj-context-ref ctx)))
                         (fn-bpaj-request-ref (fn-bpaj-request octets))))))
  :hints (("Goal"
           :use ((:instance fn-bprf-transit-context-record-ref)
                 (:instance fn-bprf-request-is-requestp)
                 (:instance fn-bpr-context-from-ref-of-request-ref
                            (request (fn-bpaj-request octets))))
           :in-theory (e/d (fn-bpr-context-from-request fn-bpr-make-context
                            fn-bpr-context-request-ref fn-bpa-nth)
                           (fn-bprf-transit-context-record-ref
                            fn-bprf-request-is-requestp
                            fn-bpr-context-from-ref-of-request-ref
                            fn-bpaj-transit-context-record
                            fn-bpaj-context-ref fn-bpr-context-from-ref
                            fn-bpaj-request fn-bpaj-request-ref
                            fn-bpa-requestp)))))

(local
 (defthm fn-bprf-request-ref-parts
   (equal (list (car (fn-bpaj-request-ref request))
                (cadr (fn-bpaj-request-ref request))
                (caddr (fn-bpaj-request-ref request)))
          (fn-bpaj-request-ref request))
   :hints (("Goal" :in-theory (enable fn-bpaj-request-ref)))))

; KEYSTONE.  An intent the host publishes names the request it was written
; for, and pins the length and digest of the relay projection of that
; request's article under the intent's own local and peer Path identities.
(defthm fn-bpaj-transit-intent-pins-its-request-and-projection
  (implies (fn-bpaj-transit-intent-from-plan
            cfg inbound octets generation txid result plan)
           (let* ((intent (fn-bpaj-transit-intent-from-plan
                           cfg inbound octets generation txid result plan))
                  (request (fn-bpaj-request octets))
                  (projection (fn-pu-relay-article
                               (fn-bpa-request-article request)
                               (fn-record-string-octets (fn-bpaj-nth 7 intent))
                               (fn-record-string-octets (fn-bpaj-nth 8 intent)))))
             (and (fn-bpaj-transit-intentp intent)
                  (fn-bpaj-intent-names-requestp intent request)
                  (equal (fn-bpaj-nth 11 intent) (len projection))
                  (equal (fn-bpaj-nth 12 intent)
                         (fn-frame-digest projection))
                  (equal projection (fn-bpaj-transit-stored-octets plan)))))
  :hints (("Goal"
           :use ((:instance fn-bprf-request-is-requestp)
                 (:instance fn-bprf-request-ref-parts
                            (request (fn-bpaj-request octets))))
           :in-theory (e/d (fn-bpaj-transit-intent-from-plan
                            fn-bpaj-intent-names-requestp
                            fn-bpaj-request-ref-matchesp fn-bpaj-nth)
                           (fn-bprf-request-is-requestp
                            fn-bprf-request-ref-parts
                            fn-bpaj-transit-intentp fn-bpaj-request
                            fn-bpaj-request-ref fn-pu-relay-article
                            fn-bpaj-transit-stored-octets
                            fn-cfg-peer-find fn-cfg-policy
                            fn-bpa-requestp)))))

; One reference names one request, unless two articles of one length share a
; digest (A-CRYPTO).
(defthm fn-bpaj-one-reference-is-one-request-or-a-digest-collision
  (implies (and (fn-bpa-requestp a) (fn-bpa-requestp b)
                (equal (fn-bpaj-request-ref a) (fn-bpaj-request-ref b)))
           (or (equal a b)
               (and (not (equal (fn-bpa-request-article a)
                                (fn-bpa-request-article b)))
                    (equal (len (fn-bpa-request-article a))
                           (len (fn-bpa-request-article b)))
                    (equal (fn-frame-digest (fn-bpa-request-article a))
                           (fn-frame-digest (fn-bpa-request-article b))))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-bpaj-ref-request-resolves-exactly (request a))
                 (:instance fn-bpaj-ref-request-resolves-exactly (request b)))
           :in-theory (e/d (fn-bpaj-request-ref)
                           (fn-bpaj-ref-request-resolves-exactly
                            fn-bpaj-ref-request fn-bpaj-head-octets
                            fn-bpa-requestp)))))
