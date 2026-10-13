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
(include-book "../../books/post-transaction")
(include-book "../../books/post-acceptance")
(include-book "../../books/memory-model")

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

; M24 C1: execute the actual machine resource getters under the certified
; concrete acceptance. Defattach is an evaluation binding, never a proof rewrite.
(with-guard-checking-event :none
 (encapsulate ()
 (defattach (fn-ptx-acc-begin fn-pacc-begin)
  (fn-ptx-acc-feed fn-pacc-feed) (fn-ptx-acc-feed-cost fn-pacc-feed-cost)
  (fn-ptx-acc-end fn-pacc-end) (fn-ptx-acc-max-state fn-pacc-max-state)
  (fn-ptx-acc-out-max fn-pacc-out-max)
  :hints (("Goal" :use
   (fn-pacc-meets-fn-ptx-acc-max-state-natp fn-pacc-meets-fn-ptx-acc-out-max-natp
    fn-pacc-meets-fn-ptx-acc-begin-bounded fn-pacc-meets-fn-ptx-acc-feed-bounded
    fn-pacc-meets-fn-ptx-acc-feed-cost-bounded fn-pacc-meets-fn-ptx-acc-feed-shape
    fn-pacc-meets-fn-ptx-acc-end-shape))))
 (make-event (value `(defconst *pabt-machine-bounds*
                       ',(list (fn-ptx-max-state) (fn-ptx-c)))))
 (defthm pabt-concrete-machine-state-ceiling-is-29193
  (equal (nth 0 *pabt-machine-bounds*) 29193) :rule-classes nil)
 (defthm pabt-concrete-machine-charge-ceiling-is-89315
  (equal (nth 1 *pabt-machine-bounds*) 89315) :rule-classes nil)))

; M24 C2: M's gate-limit construction (memory-model-tests.lisp:16-18,
; :116-118), over the whole profile-bound resident store (memory-model.lisp:591).
; No hardware-capacity claim: the configured limit is the maximum of serving
; and reopen figures. Both the new native pool and static homes fit its LARGE
; term, at the host's Q=16384, four holders and three static homes.
(with-guard-checking-event :none
 (encapsulate ()
 (defconst *pabt-mm-img* (list (* 100 1048576) (* 23 1048576) 1090519))
 (defconst *pabt-mm-cfg* '(32 t 8388608 8388608 nil 0 8388608 16 256 64 4))
 (defun pabt-post-capl (profile)
  (max (+ (min (* 2 16384) (* 2 (nfix (fn-bs-profile-max-article-octets profile))))
          *fn-cbud-reply-status-octets*)
       (+ *fn-pctx-max* (nfix (fn-bs-profile-max-article-octets profile))
          3 (* 3 (nfix (fn-bs-profile-max-groups-per-article profile)))
          (fn-article-limit-octets (fn-bs-profile-header-limits profile)))))
 (defun pabt-mm-preset-limit (profile)
  (let ((tot (fn-mm-profile-bound-tot profile :resident)))
   (max (fn-mm-sum profile *pabt-mm-img* *pabt-mm-cfg* tot)
        (fn-mm-reopen-need profile *pabt-mm-img* *pabt-mm-cfg* tot))))
 (defthm pabt-development-preset-passes-the-new-pool-gate
  (and (equal (pabt-post-capl *fn-bs-profile-development*) 256119)
       (equal *pabt-static-max* 65667)
       (<= (+ (* 4 (pabt-post-capl *fn-bs-profile-development*))
              (* 3 *pabt-static-max*))
           (fn-mm-large-pool *fn-bs-profile-development* *pabt-mm-cfg*))
       (fn-mm-gate-p *fn-bs-profile-development* *pabt-mm-img* *pabt-mm-cfg*
         (pabt-mm-preset-limit *fn-bs-profile-development*)
         (fn-mm-profile-bound-tot *fn-bs-profile-development* :resident)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
   '((:executable-counterpart pabt-post-capl) (:executable-counterpart pabt-mm-preset-limit)
     (:executable-counterpart fn-mm-large-pool) (:executable-counterpart fn-mm-gate-p)
     (:executable-counterpart fn-mm-profile-bound-tot) (:executable-counterpart equal)
     (:executable-counterpart binary-+) (:executable-counterpart binary-*)
     (:executable-counterpart not))))))
 (defthm pabt-default-preset-passes-the-new-pool-gate
  (and (equal (pabt-post-capl *fn-bs-profile-defaults*) 16816250)
       (equal *pabt-static-max* 65667)
       (<= (+ (* 4 (pabt-post-capl *fn-bs-profile-defaults*))
              (* 3 *pabt-static-max*))
           (fn-mm-large-pool *fn-bs-profile-defaults* *pabt-mm-cfg*))
       (fn-mm-gate-p *fn-bs-profile-defaults* *pabt-mm-img* *pabt-mm-cfg*
         (pabt-mm-preset-limit *fn-bs-profile-defaults*)
         (fn-mm-profile-bound-tot *fn-bs-profile-defaults* :resident)))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
   '((:executable-counterpart pabt-post-capl) (:executable-counterpart pabt-mm-preset-limit)
     (:executable-counterpart fn-mm-large-pool) (:executable-counterpart fn-mm-gate-p)
     (:executable-counterpart fn-mm-profile-bound-tot) (:executable-counterpart equal)
     (:executable-counterpart binary-+) (:executable-counterpart binary-*)
     (:executable-counterpart not))))))))
