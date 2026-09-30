; Real world metadata: a stobj field accessor is not its recognizer.
(in-package "ACL2")
(include-book "../../books/definterface")

(defstobj fn-dirt-st (fn-dirt-ready :type t :initially nil))
(defstobj fn-dirt-other (fn-dirt-other-field :type t :initially nil))

; Creator calls are logical terms in a theorem, not top-level executable
; calls: the fresh object is valid while its contents predicate is false.
(defthm fn-dirt-created-contents-by-definition
 (and (fn-dirt-stp (create-fn-dirt-st))
      (not (fn-dirt-ready (create-fn-dirt-st))))
 :rule-classes nil)

; Both functions have the same stobj-function property. That property alone
; cannot justify dropping a guard conjunct about the stored field.
(assert-event
 (and (eq (getpropc 'fn-dirt-stp 'stobj-function nil (w state)) 'fn-dirt-st)
      (eq (getpropc 'fn-dirt-ready 'stobj-function nil (w state)) 'fn-dirt-st)
      (fn-di-stobj-recognizer-conjunctp '(fn-dirt-stp fn-dirt-st)
                                       '(fn-dirt-st) '(fn-dirt-st) (w state))
      (not (fn-di-stobj-recognizer-conjunctp '(fn-dirt-ready fn-dirt-st)
                                            '(fn-dirt-st) '(fn-dirt-st) (w state)))))

; The actual raw-with filter retains the contents obligation while removing
; only the representation recognizer from the conjunction.
(assert-event
 (equal (fn-di-invariant-conjuncts
          '((fn-dirt-stp fn-dirt-st) (fn-dirt-ready fn-dirt-st))
          '(fn-dirt-st) '(fn-dirt-st) nil (w state))
        '((fn-dirt-ready fn-dirt-st))))

; Wrong object, ordinary formal, arity mismatch and non-functions stay out;
; ACL2's distinguished STATE recognizer remains supported.
(assert-event
 (and (not (fn-di-stobj-recognizer-conjunctp '(fn-dirt-otherp fn-dirt-st)
                                            '(fn-dirt-st) '(fn-dirt-st) (w state)))
      (not (fn-di-stobj-recognizer-conjunctp '(fn-dirt-stp fn-dirt-st)
                                            '(fn-dirt-st) '(nil) (w state)))
      (not (fn-di-stobj-recognizer-conjunctp '(fn-dirt-stp x)
                                            '(fn-dirt-st) '(fn-dirt-st) (w state)))
      (not (fn-di-stobj-recognizer-conjunctp '(fn-dirt-stp fn-dirt-st extra)
                                            '(fn-dirt-st) '(fn-dirt-st) (w state)))
      (not (fn-di-stobj-recognizer-conjunctp '(unknown fn-dirt-st)
                                            '(fn-dirt-st) '(fn-dirt-st) (w state)))
      (fn-di-stobj-recognizer-conjunctp '(state-p state) '(state) '(state) (w state))))
