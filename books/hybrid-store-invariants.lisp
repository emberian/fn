; The native hybrid-author projection is the ordinary ACL2 injecting agent
; applied to the portable carrier.  It adds trace fields before the exact
; signed source; neither the host nor the peer re-signs the source.
(in-package "ACL2")
(include-book "hybrid-store")
(include-book "injection-invariants")

(local
 (defthm fn-hsig-suffix-of-append
   (fn-inj-suffixp b (append a b))
   :hints (("Goal" :induct (append a b)
            :in-theory (enable fn-inj-suffixp)))))

(local
 (defthm fn-hsig-render-keeps-source-suffix
   (implies (fn-hc-render-at-most max source principal keys signatures)
            (fn-inj-suffixp
             source
             (fn-hc-render-at-most max source principal keys signatures)))
   :hints (("Goal" :do-not-induct t
            :in-theory (enable fn-hc-render-at-most fn-hc-render)))))

(local
 (defthm fn-hsig-suffix-transitive
   (implies (and (fn-inj-suffixp a b) (fn-inj-suffixp b c))
            (fn-inj-suffixp a c))
   :rule-classes nil
   :hints (("Goal" :induct (fn-inj-suffixp b c)
            :in-theory (enable fn-inj-suffixp)))))

; Host/native/hybrid-control.lisp calls this function after reading the live
; owner post configuration and clock. The received bytes keep the exact
; signed source as a suffix through BOTH the carrier and the injection.
(defthm fn-hsig-injected-carrier-retains-exact-signed-source
  (implies
   (fn-hsig-injected-carrier-octets
    source principal keys signatures config observation)
   (fn-inj-suffixp
    source
    (fn-hsig-injected-carrier-octets
     source principal keys signatures config observation)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-inj-injected-article-retains-the-source-octets
                            (source (fn-hc-render-at-most
                                     *fn-article-max-octets*
                                     source principal keys signatures)))
                 (:instance fn-hsig-suffix-transitive
                            (a source)
                            (b (fn-hc-render-at-most
                                *fn-article-max-octets*
                                source principal keys signatures))
                            (c (fn-hsig-injected-carrier-octets
                                source principal keys signatures
                                config observation))))
           :in-theory
           (e/d (fn-hsig-injected-carrier-octets
                 fn-hsig-injected-carrier-plan)
                (fn-inj-decide fn-hc-render-at-most fn-inj-suffixp)))))

; The same host-called result has the news injecting agent's Path and trace
; grammar, witnessed by the existing fn-inj-reinjectionp theorem. This is the
; substantive bridge from the portable carrier to a local stored news article.
(defthm fn-hsig-injected-carrier-is-a-news-injection
  (implies
   (fn-hsig-injected-carrier-octets
    source principal keys signatures config observation)
   (fn-inj-reinjectionp
    (fn-hsig-injected-carrier-octets
     source principal keys signatures config observation)
    (fn-hc-render-at-most
     *fn-article-max-octets* source principal keys signatures)
    (fn-inj-config-agent config)
    (fn-inj-decision-msgid
     (fn-hsig-injected-carrier-plan
      source principal keys signatures config observation))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance
                  fn-inj-injected-article-is-a-reinjection-of-its-source
                  (source (fn-hc-render-at-most
                           *fn-article-max-octets*
                           source principal keys signatures))))
           :in-theory
           (e/d (fn-hsig-injected-carrier-octets
                 fn-hsig-injected-carrier-plan)
                (fn-inj-decide fn-hc-render-at-most fn-inj-reinjectionp)))))
