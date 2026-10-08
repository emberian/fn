; The context projection survives canonical handle changes; the CPR root does
; not. This is the narrower, useful lemma, not a claim of four-root equality.
(in-package "ACL2")
(include-book "../../books/paged-checkpoint-intern-context")
(include-book "paged-checkpoint-held-tests")

(defconst *pckic-seed* (fn-ssr-seed (fn-stxk-initial-context 0)))
(make-event `(defconst *pckic-zero* ',(fn-scka-fold-at *pckic-seed* *pckh-wire* 0)))
(make-event `(defconst *pckic-five* ',(fn-scka-fold-at *pckic-seed* *pckh-wire* 5)))

(assert-event
 (and (fn-pck-context-agreep *pckic-seed* *pckic-seed*) (natp 0) (natp 5)
      (not (equal *pckic-zero* :bad)) (not (equal *pckic-five* :bad))
      (fn-pck-context-agreep *pckic-zero* *pckic-five*)
      (not (equal (fn-ssr-rows *pckic-zero*) (fn-ssr-rows *pckic-five*)))
      (not (equal (fn-sco-cpr (fn-sco-capture *pckh-configs* (fn-ssr-rows *pckic-zero*)))
                  (fn-sco-cpr (fn-sco-capture *pckh-configs* (fn-ssr-rows *pckic-five*)))))))

; Remove the agreeing-context premise: the wrong initial sequence faults.
(must-fail-checked
 (assert-event
  (fn-pck-context-agreep
   *pckic-zero*
   (fn-scka-fold-at (fn-ssr-seed (fn-stxk-initial-context 1)) *pckh-wire* 5))))

; Remove the natural-handle premise: a malformed held row faults the fold.
(must-fail-checked
 (assert-event
  (with-guard-checking :none
   (fn-pck-context-agreep *pckic-zero*
                         (fn-scka-fold-at *pckic-seed* *pckh-wire* -1)))))
