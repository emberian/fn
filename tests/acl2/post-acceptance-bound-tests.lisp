; Teeth for books/post-acceptance-bound.lisp: K's value is the derived one
; (3439 = max(290 + 2492, 795, envelope), the injected-block bound is
; attained by a configuration's widest agent (not slack), an agent one octet
; past the configuration's bound breaks it (the hypothesis has teeth), and a
; real configuration with that widest agent satisfies fn-inj-configp (the
; premise is inhabited).  Each is an `assert-event' on a concrete value.

(in-package "ACL2")
(include-book "../../books/post-acceptance-bound")
(include-book "../../books/post-context")
(include-book "../../books/stx-keyring-records")
(include-book "../../books/byte-store-frame")
(include-book "../../books/article")

(defconst *pabt-agent* (make-list *fn-inj-max-agent-octets* :initial-element 97))
(defconst *pabt-config*
  (fn-inj-make-config-full t *pabt-agent* nil 65536 nil nil))

; 1. K and the block at their derived values.
(assert-event (equal (fn-adm-injected-block-max) 2492))
(assert-event (equal (fn-adm-acc-out-max) 3439))
(assert-event (equal (fn-adm-acc-out-max)
                     (max (+ *fn-record-head-max-octets* (fn-adm-injected-block-max))
                          (max *fn-record-tail-max-octets* (fn-adm-envelope-pre-max)))))
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

; M24 resource arithmetic. Consumer integration is tracked in c9/A1-INTEGRATION-S3.md.
(with-guard-checking-event :none
 (encapsulate ()
  (defconst *pabt-batch-max*
    (len (fn-stxk-encode
      (fn-stxk-make *fn-cbor-max-uint* *fn-cbor-max-uint* *fn-cbor-max-uint* *fn-cbor-max-uint*
        (make-list *fn-stxk-max-profile* :initial-element 97)
        (make-list *fn-stxk-max-snapshot* :initial-element 97)))))
  (defconst *pabt-homes-max*
    (max (+ 42 (* 2 (fn-adm-acc-out-max)))
         (+ *fn-pctx-sufhead-max* (fn-adm-acc-out-max) 32)))
  (defconst *pabt-static-max*
    (max *pabt-homes-max* (+ (len (fn-pctx-encode (list 0 nil nil 0 nil nil 0))) *pabt-batch-max*)))
  (defthm pabt-batch-ceiling-is-derived (equal *pabt-batch-max* 65634) :rule-classes nil)
  (defthm pabt-homes-ceiling-is-derived (equal *pabt-homes-max* 6920) :rule-classes nil)
  (defthm pabt-static-ceiling-is-derived (equal *pabt-static-max* 65667) :rule-classes nil)
  (defthm pabt-development-post-buffer-is-derived
    (equal (+ *fn-pctx-max* (fn-bs-profile-max-article-octets *fn-bs-profile-development*)
       3 (* 3 (fn-bs-profile-max-groups-per-article *fn-bs-profile-development*))
       (fn-article-limit-octets (fn-bs-profile-header-limits *fn-bs-profile-development*))) 256119))
  (defthm pabt-default-post-buffer-is-derived
    (equal (+ *fn-pctx-max* (fn-bs-profile-max-article-octets *fn-bs-profile-defaults*)
       3 (* 3 (fn-bs-profile-max-groups-per-article *fn-bs-profile-defaults*))
       (fn-article-limit-octets (fn-bs-profile-header-limits *fn-bs-profile-defaults*))) 16816250))))
