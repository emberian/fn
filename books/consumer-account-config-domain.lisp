; Establish/preserve the actual binding-intent domain at its constructors.
; Proof-only relations never run as readiness checks at a served fence.
(in-package "ACL2")
(include-book "consumer-account-config-preparation")

(local
 (defthm fn-bcp-binding-name-bound
  (implies (fn-cab-eventp event)
           (<= (len (fn-cp-nth 3 (fn-cp-nth 4 event))) 64))
  :hints (("Goal" :use ((:instance fn-cp-id-length-bound
                                  (x (fn-cp-nth 3 (fn-cp-nth 4 event)))))
           :in-theory
           (e/d (fn-cab-eventp fn-cab-operationp fn-cac-fields-validp
                  fn-cac-fieldp fn-cp-nth)
                (fn-cakd-domainp fn-cab-decisionp fn-cac-u64p
                 fn-cp-idp fn-cp-id-length-bound))))))

(defthm fn-bcp-begin-establishes-intent-domain
 (fn-cakd-domainp (fn-cp-nth 7 (fn-bcp-begin candidate base revision)) 64)
 :hints (("Goal" :in-theory (enable fn-bcp-begin fn-bcp-state
                                    fn-cp-nth fn-cakd-domainp))))

(defthm fn-bcp-stage-preserves-intent-domain
 (implies (fn-cakd-domainp (fn-cp-nth 7 s) 64)
          (fn-cakd-domainp (fn-cp-nth 7 (fn-cp-nth 1 (fn-bcp-stage s event))) 64))
 :hints (("Goal"
          :use ((:instance fn-bcp-binding-name-bound)
                (:instance fn-cakd-put-preserves-domain
                           (depth 64) (trie (fn-cp-nth 7 s))
                           (name (fn-cp-nth 3 (fn-cp-nth 4 event)))
                           (value (fn-aic-intent (fn-cp-nth 4 (fn-cp-nth 4 event))
                                                (fn-cp-nth 5 (fn-cp-nth 4 event))
                                                (fn-cp-nth 6 (fn-cp-nth 4 event))))))
          :in-theory (e/d (fn-bcp-stage fn-bcp-with fn-bcp-state fn-cp-nth)
                           (fn-cakd-domainp fn-cakd-put-preserves-domain
                            fn-cai-put-is-existing-trie-put
                            fn-bcp-binding-name-bound fn-cab-eventp fn-cab-operationp
                            fn-cait-put-octets fn-cai-put-octets fn-aic-intent
                            fn-aic-intent-carry fn-bcp-binding-row
                            fn-bcp-binding-row-carry fn-caac-list-cons)))))

(defthm fn-bcp-tick-preserves-intent-domain
 (implies (fn-cakd-domainp (fn-cp-nth 7 s) 64)
          (fn-cakd-domainp (fn-cp-nth 7 (fn-cp-nth 1 (fn-bcp-tick s rowcarry))) 64))
 :hints (("Goal" :in-theory
          (e/d (fn-bcp-tick fn-bcp-with fn-bcp-state fn-cp-nth)
               (fn-cakd-domainp fn-bcp-intent-lookup fn-caac-list-cons
                fn-cfg-accounts fn-cfg-value fn-cfg-row-a fn-cfg-row-n)))))

(defthm fn-bcp-expect-and-seal-preserve-intent-domain
 (implies (fn-cakd-domainp (fn-cp-nth 7 s) 64)
          (and (fn-cakd-domainp (fn-cp-nth 7 (fn-cp-nth 1 (fn-bcp-expect s login kind))) 64)
               (fn-cakd-domainp (fn-cp-nth 7 (fn-cp-nth 1 (fn-bcp-seal s))) 64)))
 :hints (("Goal" :in-theory
          (e/d (fn-bcp-expect fn-bcp-seal fn-bcp-with fn-bcp-state fn-cp-nth)
               (fn-cakd-domainp fn-cp-idp)))))
