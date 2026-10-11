; Teeth for books/post-acceptance-bound.lisp: K's value is the derived one
; (2782 = 290 + 2492, above the tail's 795), the injected-block bound is
; attained by a configuration's widest agent (not slack), an agent one octet
; past the configuration's bound breaks it (the hypothesis has teeth), and a
; real configuration with that widest agent satisfies fn-inj-configp (the
; premise is inhabited).  Each is an `assert-event' on a concrete value.

(in-package "ACL2")
(include-book "../../books/post-acceptance-bound")

(defconst *pabt-agent* (make-list *fn-inj-max-agent-octets* :initial-element 97))
(defconst *pabt-config*
  (fn-inj-make-config-full t *pabt-agent* nil 65536 nil nil))

; 1. K and the block at their derived values.
(assert-event (equal (fn-adm-injected-block-max) 2492))
(assert-event (equal (fn-adm-acc-out-max) 2782))
(assert-event (equal (fn-adm-acc-out-max)
                     (+ *fn-record-head-max-octets* (fn-adm-injected-block-max))))
(assert-event (< *fn-record-tail-max-octets* (fn-adm-acc-out-max)))

; 2. Premise inhabited and the bound attained: a configuration whose agent is
;    as wide as the configuration admits injects exactly the max.
(assert-event (fn-inj-configp *pabt-config*))
(assert-event (equal (fn-o1-injected-block-octets (fn-inj-config-agent *pabt-config*))
                     (fn-adm-injected-block-max)))

; 3. The hypothesis has teeth: one octet more of agent exceeds the max, and
;    such a configuration is refused by fn-inj-configp.
(assert-event (< (fn-adm-injected-block-max)
                 (fn-o1-injected-block-octets (cons 97 *pabt-agent*))))
(assert-event (not (fn-inj-configp
                    (fn-inj-make-config-full t (cons 97 *pabt-agent*) nil 65536 nil nil))))
