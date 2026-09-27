; PKT-646, PRF-244: the receipt journal carries a local request by
; REFERENCE, and every read resolves the reference to exactly the request.
;
; Host subjects (books/bp-native-app.lisp; host/bp-receipt-journal-host.lisp
; calls the builders, host/native/bp-app.lisp `fnn-bpapp-request-intent' and
; `fnn-bpapp-bind-context' publish their records):
;   - `fn-bpaj-intent-record', `fn-bpaj-context-v2-record': the FNRJ records
;     the host publishes carry (HEAD LENGTH DIGEST), `fn-bpaj-request-ref';
;   - `fn-bpaj-context-request' over `fn-bpaj-context-record': the request
;     every replay of a context binds (fn-bpaj-apply-record and its fast twin,
;     called by `fn-bprj-install' at every journal open, recovery included,
;     and by `fn-bprj-preflight'/`fn-bprj-apply' at publication);
;   - `fn-bpaj-intent-names-requestp': how `fn-bpaj-request-status' (and the
;     fast twin the host calls) compares a live request with an intent.
;
; What is proved:
;   KEYSTONE fn-bpaj-ref-request-resolves-exactly: a request's reference
;     resolves over its own article to that request, and (-to-the-bytes) the
;     encoding of that resolution is the request's octets.
;   KEYSTONE fn-bpaj-context-read-resolves-exactly: a context the host
;     published for request octets R and Store record S resolves, at any read
;     whose Store still names S, to exactly R's request.
;   fn-bpaj-context-request-is-the-referenced-article: whenever a read
;     resolves, the bound request's article IS the Store record's payload,
;     of the recorded length and digest (no hypothesis on the writer).
;   fn-bpaj-intent-names-its-request, and
;   fn-bpaj-one-reference-is-one-request-or-a-digest-collision: an intent
;     names the request it was written for; a different request it names has
;     the same metadata and an article of the same length and
;     `fn-frame-digest' (A-CRYPTO, books/frame-octets: SHA-256, whose
;     collision resistance is outside the logic; for n distinct articles the
;     collision probability is at most n(n-1)/2^257).
(in-package "ACL2")
(include-book "bp-native-app-fast")
(local (include-book "bp-receiver-state-invariants"))

(local (in-theory (enable fn-bpa-encoded-fields-are-octets)))

(local
 (defthm fn-bprf-append-nil-when-true-listp
   (implies (true-listp x) (equal (append x nil) x))))

(local
 (defthm fn-bprf-encode-fields-true-listp
   (true-listp (fn-bpa-encode-fields fields))
   :hints (("Goal" :in-theory (disable fn-record-item-encode)))))

(local
 (defthm fn-bprf-byte-field-listp-of-append
   (implies (and (true-listp xs)
                 (fn-bpa-byte-field-listp (append xs ys)))
            (fn-bpa-byte-field-listp xs))
   :hints (("Goal" :in-theory (disable fn-record-payloadp)))))

(local
 (defthm fn-bprf-request-fields-are-head-and-article
   (equal (fn-bpa-request-fields request)
          (append (fn-bpaj-head-fields request)
                  (list (fn-bpa-request-article request))))
   :hints (("Goal" :in-theory (enable fn-bpa-request-fields
                                      fn-bpaj-head-fields)))))

(local
 (defthm fn-bprf-head-fields-byte-fields
   (implies (fn-bpa-requestp request)
            (fn-bpa-byte-field-listp (fn-bpaj-head-fields request)))
   :hints (("Goal"
            :use ((:instance fn-bpa-request-fields-domain)
                  (:instance fn-bprf-byte-field-listp-of-append
                             (xs (fn-bpaj-head-fields request))
                             (ys (list (fn-bpa-request-article request)))))
            :in-theory (disable fn-bpa-request-fields-domain
                                fn-bprf-byte-field-listp-of-append
                                fn-bpaj-head-fields fn-bpa-requestp
                                fn-bpa-byte-field-listp)))))

(local
 (defthm fn-bprf-head-fields-len
   (equal (len (fn-bpaj-head-fields request)) 8)))

(local
 (defthm fn-bprf-head-read-of-head-octets
   (implies (fn-bpa-requestp request)
            (equal (fn-bpaj-head-read (fn-bpaj-head-octets request))
                   (fn-bpaj-head-fields request)))
   :hints (("Goal"
            :use ((:instance fn-bpa-read-encoded-fields-wide
                             (fields (fn-bpaj-head-fields request))
                             (rest nil)))
            :in-theory (e/d (fn-bpaj-head-read fn-bpaj-head-octets)
                            (fn-bpa-read-encoded-fields-wide
                             fn-bpaj-head-fields fn-bpa-requestp
                             fn-bpa-read-fields fn-bpa-encode-fields))))))

(local
 (defthm fn-bprf-request-article-octets
   (implies (fn-bpa-requestp request)
            (fn-cbor-octet-listp (fn-bpa-request-article request)))
   :hints (("Goal" :in-theory (enable fn-bpa-requestp fn-record-payloadp)))))

(local
 (defthm fn-bprf-head-fields-consp
   (consp (fn-bpaj-head-fields request))))

; KEYSTONE.  A request's reference resolves over its own article to it.
(defthm fn-bpaj-ref-request-resolves-exactly
  (implies (fn-bpa-requestp request)
           (equal (fn-bpaj-ref-request
                   (car (fn-bpaj-request-ref request))
                   (cadr (fn-bpaj-request-ref request))
                   (caddr (fn-bpaj-request-ref request))
                   (fn-bpa-request-article request))
                  request))
  :hints (("Goal"
           :use ((:instance fn-bpa-request-fields-reconstruct)
                 (:instance fn-bprf-request-fields-are-head-and-article)
                 (:instance fn-bprf-request-article-octets))
           :in-theory (e/d (fn-bpaj-ref-request fn-bpaj-request-ref)
                           (fn-bpa-request-fields-reconstruct
                            fn-bprf-request-article-octets fn-bpa-request-article
                            fn-bprf-request-fields-are-head-and-article
                            fn-bpaj-head-read fn-bpaj-head-octets
                            fn-bpaj-head-fields fn-bpa-requestp
                            fn-bpa-request-from-fields
                            fn-bpa-request-fields)))))

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
 (defthm fn-bprf-read-fields-len
   (implies (fn-record-parse-okp (fn-bpa-read-fields n x))
            (equal (len (fn-record-parse-value (fn-bpa-read-fields n x)))
                   (nfix n)))
   :hints (("Goal" :induct (fn-bpa-read-fields n x)
            :in-theory (e/d (fn-bpa-read-fields) (fn-record-read-bytes))))))

(local
 (defthm fn-bprf-head-read-len
   (implies (fn-bpaj-head-read h)
            (equal (len (fn-bpaj-head-read h)) 8))
   :hints (("Goal" :in-theory (e/d (fn-bpaj-head-read)
                                   (fn-bpa-read-fields))))))

(local
 (defthm fn-bprf-nth-len-of-append
   (equal (fn-bpa-nth (len xs) (append xs (list a))) a)
   :hints (("Goal" :induct (len xs)
            :in-theory (enable fn-bpa-nth fn-bpa-car fn-bpa-cdr)))))

(local
 (defthm fn-bprf-nth-8-of-append
   (implies (equal (len xs) 8)
            (equal (fn-bpa-nth 8 (append xs (list a))) a))
   :hints (("Goal" :use ((:instance fn-bprf-nth-len-of-append))
            :in-theory (disable fn-bprf-nth-len-of-append)))))

; Whenever a read resolves, the request it binds carries the Store record's
; payload as its article, of the recorded length and digest.
(defthm fn-bpaj-context-request-is-the-referenced-article
  (implies (fn-bpaj-context-request ctx record)
           (and (fn-bpa-requestp (fn-bpaj-context-request ctx record))
                (equal (fn-bpa-request-article
                        (fn-bpaj-context-request ctx record))
                       (fn-record-payload record))
                (equal (len (fn-record-payload record)) (fn-bpaj-nth 9 ctx))
                (equal (fn-frame-digest (fn-record-payload record))
                       (fn-bpaj-nth 10 ctx))))
  :hints (("Goal" :in-theory (e/d (fn-bpaj-context-request
                                   fn-bpaj-ref-request)
                                  (fn-bpa-requestp fn-bpaj-head-read)))))

(local
 (defthm fn-bprf-context-v2-record-fields
   (implies (fn-bpaj-context-v2-record inbound octets store-record
                                       generation txid rg result)
            (let ((ctx (fn-bpaj-context-v2-record inbound octets store-record
                                                  generation txid rg result))
                  (ref (fn-bpaj-request-ref (fn-bpaj-request octets))))
              (and (equal (fn-bpaj-nth 2 ctx) (car ref))
                   (equal (fn-bpaj-nth 9 ctx) (cadr ref))
                   (equal (fn-bpaj-nth 10 ctx) (caddr ref))
                   (fn-bpaj-request octets))))
   :hints (("Goal" :in-theory (e/d (fn-bpaj-context-v2-record fn-bpaj-nth)
                                   (fn-bpaj-context-v2p fn-bpaj-request
                                    fn-bpaj-request-ref))))))

(local
 (defthm fn-bprf-request-is-requestp
   (implies (fn-bpaj-request octets)
            (fn-bpa-requestp (fn-bpaj-request octets)))
   :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                                              '(fn-bpaj-request))))))

; KEYSTONE.  At every read of a context the host published for request
; octets R, whose Store (the one the replay reads) names a record whose
; payload is R's article (the binding the context recorded:
; `fn-bpr-request-acceptablep' checked it when the context was written),
; the reference resolves to exactly R's request.  The read is
; `fn-bpaj-apply-record' / `-fast' at `fn-bprj-install' (recovery),
; `fn-bprj-preflight' and `fn-bprj-apply' (publication).
(local
 (defthm fn-bprf-context-read-resolves-exactly-when-built
  (implies (and (fn-bpaj-context-v2-record inbound octets store-record
                                           generation txid rg result)
                (equal ctx (fn-bpaj-context-v2-record
                            inbound octets store-record
                            generation txid rg result))
                (equal (fn-bpaj-context-record store ctx) record)
                (fn-record-p record)
                (equal (fn-record-payload record)
                       (fn-bpa-request-article (fn-bpaj-request octets))))
           (and (equal (fn-bpaj-context-request
                        ctx (fn-bpaj-context-record store ctx))
                       (fn-bpaj-request octets))
                (equal (fn-bpa-encode
                        (fn-bpaj-context-request
                         ctx (fn-bpaj-context-record store ctx)))
                       octets)))
  :hints (("Goal"
           :use ((:instance fn-bprf-context-v2-record-fields)
                 (:instance fn-bpaj-ref-request-resolves-exactly
                            (request (fn-bpaj-request octets)))
                 (:instance fn-bpaj-ref-request-resolves-to-the-bytes)
                 (:instance fn-bprf-request-is-requestp))
           :in-theory (e/d (fn-bpaj-context-request)
                           (fn-bprf-context-v2-record-fields
                            fn-bpaj-ref-request-resolves-exactly
                            fn-bpaj-ref-request-resolves-to-the-bytes
                            fn-bprf-request-is-requestp
                            fn-bpaj-context-v2-record fn-bpaj-context-record
                            fn-bpaj-ref-request fn-bpaj-request-ref
                            fn-bpaj-request fn-bpa-encode fn-bpa-requestp))))))

(defthm fn-bpaj-context-read-resolves-exactly
  (implies (and (equal ctx (fn-bpaj-context-v2-record
                            inbound octets store-record
                            generation txid rg result))
                (equal (fn-bpaj-context-record store ctx) record)
                (fn-record-p record)
                (equal (fn-record-payload record)
                       (fn-bpa-request-article (fn-bpaj-request octets))))
           (and (equal (fn-bpaj-context-request
                        ctx (fn-bpaj-context-record store ctx))
                       (fn-bpaj-request octets))
                (equal (fn-bpa-encode
                        (fn-bpaj-context-request
                         ctx (fn-bpaj-context-record store ctx)))
                       octets)))
  :hints (("Goal" :cases ((fn-bpaj-context-v2-record
                           inbound octets store-record
                           generation txid rg result))
           :use ((:instance fn-bprf-context-read-resolves-exactly-when-built))
           :in-theory (e/d (fn-bpaj-context-record fn-bpaj-nth)
                           (fn-bprf-context-read-resolves-exactly-when-built
                            fn-bpaj-context-v2-record fn-bpaj-context-request
                            fn-bpaj-context-record-of
                            fn-bpaj-record-for-msgid)))))

; An intent names the request it was written for.
(defthm fn-bpaj-intent-names-its-request
  (implies (fn-bpaj-intent-record inbound octets generation txid result)
           (fn-bpaj-intent-names-requestp
            (fn-bpaj-intent-record inbound octets generation txid result)
            (fn-bpaj-request octets)))
  :hints (("Goal" :use ((:instance fn-bprf-request-is-requestp))
           :in-theory (e/d (fn-bpaj-intent-record
                            fn-bpaj-intent-names-requestp
                            fn-bpaj-request-ref-matchesp fn-bpaj-nth
                            fn-bpaj-request-ref)
                           (fn-bpaj-request fn-bpaj-head-octets
                            fn-bpa-requestp fn-bpaj-intentp)))))

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
