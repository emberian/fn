; fn: a retry is the saved artifact, and only the saved artifact is
; "already stored here" (PRF-137; gpt-6's review of wave 2, section 2).
;
; The consumer (tools/fn_consumer.py, an external client) keeps each
; submission as an immutable artifact -- authored source, both signatures,
; the author's keys and keyring generation -- and reconciles an attempt
; without a durable answer by resending exactly that artifact.  What it
; relies on from fn is D25 at the signed control route: the host calls
; fn-rcl-existing-action (host/owner-host.lisp fn-owner-existing-action)
; from host/native/hybrid-control.lisp fnn-hybrid-control-author on the
; octets fn-hsig-injected-carrier-octets computes, before it commits.
;
;   * The same artifact resent is :duplicate.  That is
;     fn-sr-a-signed-retry-is-already-stored (books/source-routes, PRF on
;     PKT-166); it is cited, not restated.
;   * The same authored source signed AGAIN is :conflict.  Randomized
;     ML-DSA-65 signing gives new signatures for an unchanged authored
;     source; the signatures are carrier octets, so the stored carrier
;     changes and D25 refuses it as another article under the held
;     Message-ID (fn-sr-a-re-signed-carrier-is-a-conflict, below).  This is
;     why the consumer saves and resends the artifact and never re-signs.
;
; The step the second needs is that rendering a carrier is injective in the
; signatures: the FN-Authorship field is the folded base64 of the canonical
; CBOR carrier, and the carrier decodes back to exactly its signatures
; (fn-hc-decode-at-of-encode-at).  Folding only inserts octets outside the
; base64 alphabet, so dropping them recovers the field value.

(in-package "ACL2")
(include-book "source-routes")

; -----------------------------------------------------------------------------
; Folding is invertible on base64 text.

(local
 (defun fn-cra-vcharsp (x)
   (declare (xargs :guard t))
   (if (consp x)
       (and (integerp (car x)) (<= 33 (car x)) (<= (car x) 126)
            (fn-cra-vcharsp (cdr x)))
     (null x))))

(local
 (defun fn-cra-keep (x)
   (declare (xargs :guard t))
   (if (consp x)
       (if (and (integerp (car x)) (<= 33 (car x)) (<= (car x) 126))
           (cons (car x) (fn-cra-keep (cdr x)))
         (fn-cra-keep (cdr x)))
     nil)))

(local
 (defthm fn-cra-keep-of-append
   (equal (fn-cra-keep (append a b))
          (append (fn-cra-keep a) (fn-cra-keep b)))))

(local
 (defthm fn-cra-keep-of-vchars
   (implies (fn-cra-vcharsp x)
            (equal (fn-cra-keep x) x))))

(local
 (defthm fn-cra-vchars-are-a-true-list
   (implies (fn-cra-vcharsp x) (true-listp x))
   :rule-classes :forward-chaining))

(local
 (defthm fn-cra-vchars-of-take
   (implies (fn-cra-vcharsp x) (fn-cra-vcharsp (fn-hc-take n x)))
   :hints (("Goal" :induct (fn-hc-take n x) :in-theory (enable fn-hc-take)))))

(local
 (defthm fn-cra-vchars-of-drop
   (implies (fn-cra-vcharsp x) (fn-cra-vcharsp (fn-hc-drop n x)))
   :hints (("Goal" :induct (fn-hc-drop n x) :in-theory (enable fn-hc-drop)))))

(local
 (defthm fn-cra-take-then-drop
   (implies (true-listp x)
            (equal (append (fn-hc-take n x) (fn-hc-drop n x)) x))
   :hints (("Goal" :induct (fn-hc-take n x)
            :in-theory (enable fn-hc-take fn-hc-drop)))))

(local
 (defthm fn-cra-keep-of-fold-rest
   (implies (fn-cra-vcharsp v)
            (equal (fn-cra-keep (fn-hc-fold-rest v)) v))
   :hints (("Goal" :induct (fn-hc-fold-rest v) :in-theory (enable fn-hc-fold-rest)))))

(local
 (defthm fn-cra-keep-of-field-lines
   (implies (fn-cra-vcharsp v)
            (equal (fn-cra-keep (fn-hc-field-lines v))
                   (if (consp v)
                       (append '(70 78 45 65 117 116 104 111 114 115 104 105 112 58) v)
                     nil)))
   :hints (("Goal" :in-theory (enable fn-hc-field-lines)))))

(local
 (defthm fn-cra-field-lines-are-injective
   (implies (and (fn-cra-vcharsp v1) (fn-cra-vcharsp v2)
                 (equal (fn-hc-field-lines v1) (fn-hc-field-lines v2)))
            (equal v1 v2))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn-cra-keep-of-field-lines (v v1))
                         (:instance fn-cra-keep-of-field-lines (v v2)))
            :in-theory (disable fn-cra-keep-of-field-lines)))))

(local
 (defthm fn-cra-base64-is-vchars
   (fn-cra-vcharsp (fn-stx-b64-encode octets))
   :hints (("Goal" :induct (fn-stx-b64-encode octets)
            :in-theory (e/d (fn-stx-b64-encode) (floor mod))))))

(local
 (defthm fn-cra-base64-is-injective
   (implies (and (fn-cbor-octet-listp a) (fn-cbor-octet-listp b)
                 (equal (fn-stx-b64-encode a) (fn-stx-b64-encode b)))
            (equal a b))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn-stx-b64-round-trip (octets a))
                         (:instance fn-stx-b64-round-trip (octets b)))
            :in-theory (e/d (fn-stx-ok)
                            (fn-stx-b64-round-trip fn-stx-b64-encode
                             fn-stx-b64-decode-exact))))))

; -----------------------------------------------------------------------------
; The carrier binary is injective in the signatures.

(local
 (defthm fn-cra-encode-at-is-octets
   (implies (fn-hc-encode-at version principal keys signatures)
            (fn-cbor-octet-listp (fn-hc-encode-at version principal keys signatures)))
   :hints (("Goal" :in-theory (enable fn-hc-encode-at)))))

(local
 (defthm fn-cra-encode-at-is-injective
   (implies (and (fn-hc-encode-at version principal keys s1)
                 (equal (fn-hc-encode-at version principal keys s1)
                        (fn-hc-encode-at version principal keys s2)))
            (equal s1 s2))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn-hc-decode-at-of-encode-at (signatures s1))
                         (:instance fn-hc-decode-at-of-encode-at (signatures s2)))
            :in-theory (e/d (fn-hc-ok) (fn-hc-decode-at-of-encode-at fn-hc-decode-at
                                        fn-hc-encode-at))))))

(local
 (defthm fn-cra-field-encode-at-is-base64-of-encode-at
   (implies (fn-hc-field-encode-at version principal keys signatures)
            (and (fn-hc-encode-at version principal keys signatures)
                 (equal (fn-hc-field-encode-at version principal keys signatures)
                        (fn-stx-b64-encode
                         (fn-hc-encode-at version principal keys signatures)))))
   :hints (("Goal" :in-theory (e/d (fn-hc-field-encode-at) (fn-hc-encode-at))))))

(local
 (defthm fn-cra-render-is-the-field-then-the-source
   (implies (fn-hc-render source principal keys signatures)
            (and (fn-hc-field-encode-at (fn-hsig-source-version source)
                                        principal keys signatures)
                 (equal (fn-hc-render source principal keys signatures)
                        (append (fn-hc-field-lines
                                 (fn-hc-field-encode-at (fn-hsig-source-version source)
                                                        principal keys signatures))
                                source))))
   :hints (("Goal" :in-theory (e/d (fn-hc-render fn-hc-native-plan fn-hc-okp
                                    fn-hc-value fn-hc-ok fn-hc-error)
                                   (fn-hc-field-lines fn-hc-field-encode-at
                                    fn-hsig-source-version fn-article-parse
                                    fn-cra-field-encode-at-is-base64-of-encode-at))))))

(local
 (defthm fn-cra-len-of-append
   (equal (len (append a b)) (+ (len a) (len b)))))

(local
 (defthm fn-cra-append-onto-z-is-not-z
   (implies (consp y) (not (equal z (append y z))))
   :hints (("Goal" :use ((:instance (:theorem (implies (equal a b)
                                                        (equal (len a) (len b))))
                                    (a z) (b (append y z))))
            :expand ((len y))))))

(local
 (defun fn-cra-two (x y)
   (if (and (consp x) (consp y)) (fn-cra-two (cdr x) (cdr y)) (list x y))))

(local
 (defthm fn-cra-append-cancels-on-the-right
   (implies (and (true-listp x) (true-listp y)
                 (equal (append x z) (append y z)))
            (equal x y))
   :rule-classes nil
   :hints (("Goal" :induct (fn-cra-two x y)))))

; KEYSTONE (lemma, rendering).  Two carriers of one authored source under
; one principal and key set, with different signatures, are different
; octets.
(defthm fn-cra-a-re-signed-carrier-is-other-octets
  (implies (and (fn-hc-render-at-most max-octets source principal keys s1)
                (fn-hc-render-at-most max-octets source principal keys s2)
                (not (equal s1 s2)))
           (not (equal (fn-hc-render-at-most max-octets source principal keys s1)
                       (fn-hc-render-at-most max-octets source principal keys s2))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (fn-hc-render-at-most)
                           (fn-hc-render fn-hc-field-lines fn-hc-field-encode-at
                            fn-hc-encode-at fn-stx-b64-encode fn-hsig-source-version
                            fn-cbor-at-mostp fn-cbor-octet-listp))
           :use ((:instance fn-cra-render-is-the-field-then-the-source (signatures s1))
                 (:instance fn-cra-render-is-the-field-then-the-source (signatures s2))
                 (:instance fn-cra-append-cancels-on-the-right
                  (x (fn-hc-field-lines (fn-hc-field-encode-at
                                         (fn-hsig-source-version source)
                                         principal keys s1)))
                  (y (fn-hc-field-lines (fn-hc-field-encode-at
                                         (fn-hsig-source-version source)
                                         principal keys s2)))
                  (z source))
                 (:instance fn-cra-field-lines-are-injective
                  (v1 (fn-hc-field-encode-at (fn-hsig-source-version source)
                                             principal keys s1))
                  (v2 (fn-hc-field-encode-at (fn-hsig-source-version source)
                                             principal keys s2)))
                 (:instance fn-cra-field-encode-at-is-base64-of-encode-at
                  (version (fn-hsig-source-version source)) (signatures s1))
                 (:instance fn-cra-field-encode-at-is-base64-of-encode-at
                  (version (fn-hsig-source-version source)) (signatures s2))
                 (:instance fn-cra-base64-is-injective
                  (a (fn-hc-encode-at (fn-hsig-source-version source) principal keys s1))
                  (b (fn-hc-encode-at (fn-hsig-source-version source) principal keys s2)))
                 (:instance fn-cra-encode-at-is-injective
                  (version (fn-hsig-source-version source)))))))

; The route's octets are an injection of the rendered carrier.
(local
 (defthm fn-cra-carrier-octets-are-an-injection
   (implies (fn-hsig-injected-carrier-octets source principal keys signatures
                                             config obs)
            (and (fn-hc-render-at-most *fn-article-max-octets*
                                       source principal keys signatures)
                 (equal (fn-hsig-injected-carrier-plan source principal keys
                                                       signatures config obs)
                        (fn-inj-decide (fn-hc-render-at-most *fn-article-max-octets*
                                                             source principal keys
                                                             signatures)
                                       config obs))
                 (fn-inj-injectedp
                  (fn-inj-decide (fn-hc-render-at-most *fn-article-max-octets*
                                                       source principal keys signatures)
                                 config obs))
                 (equal (fn-hsig-injected-carrier-octets source principal keys
                                                         signatures config obs)
                        (fn-inj-decision-octets
                         (fn-inj-decide (fn-hc-render-at-most *fn-article-max-octets*
                                                              source principal keys
                                                              signatures)
                                        config obs)))))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn-hsig-injected-carrier-octets
                                    fn-hsig-injected-carrier-plan fn-inj-refuse)
                                   (fn-inj-decide fn-hc-render-at-most
                                    fn-inj-supplies-pathp))))))

; KEYSTONE (D25, the signed control route).  The held payload is the carrier
; of SOURCE under signatures S1 (the first acceptance).  The same authored
; source under the same principal and keys, signed again with signatures S2
; that differ, is :conflict at any clock and for any groups: a re-signed
; retry is never "already stored here".  (With S2 = S1 the answer is
; :duplicate, fn-sr-a-signed-retry-is-already-stored.)
(defthm fn-sr-a-re-signed-carrier-is-a-conflict
  (let ((held (fn-find-article
               msgid (fn-state-articles (fn-node-acceptance (fn-sn-node s)))))
        (pa (fn-hsig-injected-carrier-plan source principal keys s1 config a))
        (pb (fn-hsig-injected-carrier-plan source principal keys s2 config b))
        (oa (fn-hsig-injected-carrier-octets source principal keys s1 config a))
        (ob (fn-hsig-injected-carrier-octets source principal keys s2 config b)))
    (implies (and oa ob
                  (equal (fn-article-payload held) oa)
                  (equal (fn-inj-decision-msgid pa) (fn-record-string-octets msgid))
                  (equal (fn-inj-decision-msgid pb) (fn-record-string-octets msgid))
                  (not (equal s1 s2)))
             (equal (fn-rcl-existing-action msgid ob groups s) :conflict)))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use ((:instance fn-cra-carrier-octets-are-an-injection
                  (signatures s1) (obs a))
                 (:instance fn-cra-carrier-octets-are-an-injection
                  (signatures s2) (obs b))
                 (:instance fn-sr-a-changed-source-is-a-conflict
                  (source1 (fn-hc-render-at-most *fn-article-max-octets*
                                                 source principal keys s1))
                  (source2 (fn-hc-render-at-most *fn-article-max-octets*
                                                 source principal keys s2)))
                 (:instance fn-cra-a-re-signed-carrier-is-other-octets
                  (max-octets *fn-article-max-octets*)))))
  :rule-classes nil)
