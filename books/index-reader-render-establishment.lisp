(in-package "ACL2")
(include-book "index-reader-render-slot")
; Exact actual serialized intent/install composition, not a supplied plan or
; a shape-only ready assertion. The initial root stays immutable thereafter.
(defthm fn-irc-slot-intent-install-establishes-current-plan-and-root
 (let* ((intent (fn-irc-slot-render-intent token fn-ibp-query-segment))
        (answer (fn-irc-slot-render-install token (mv-nth 1 intent) fn-render-holder))
        (qs (mv-nth 1 answer)) (rh (mv-nth 2 answer))
        (context (fn-ibp-qs-inputsi (nth 3 token) qs))
        (row (fn-irc-context-custody context)))
  (implies (and (eq (mv-nth 0 intent) :render-intent-recorded)
                (eq (mv-nth 0 answer) :installed))
   (and (equal (fn-rh-plan rh)
               (fn-spp-at 4 (fn-ibp-qs-controlsi (nth 3 token) qs)))
        (eq (fn-omk-at 6 row) :render-owned)
        (equal (fn-omk-at 8 row)
               (list :receiver-render-root (fn-rh-live rh) (fn-rh-plan rh)
                     (fn-rh-pin rh) (fn-rh-query rh) (fn-rh-resource rh)
                     (fn-rh-origin rh))))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :in-theory
  (e/d (fn-irc-slot-render-intent fn-irc-slot-render-install
        fn-irc-context-custody fn-ibr-registered-render-custody-install
        fn-ibr-registered-render-install fn-rh-producer-install-positioned
        fn-ric-custody-render-acquire fn-omk-at fn-spp-at fn-ag-car fn-ag-cdr
        update-fn-ibp-qs-inputsi fn-ibp-qs-inputsi fn-ibp-qs-controlsi
        fn-rh-live fn-rh-plan fn-rh-pin fn-rh-query fn-rh-resource fn-rh-origin)
       (fn-irc-slot-sourcep fn-omk-widthp fn-spp-resource fn-spp-origin
        fn-ibp-query-tokenp nth update-nth nth-add1)))))
