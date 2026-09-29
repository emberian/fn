; fn: witnesses and teeth for books/owner-reclaim-instant.lisp (row Q16,
; PRF-987): the reclaim's instant recorded LIVE through the owner's
; reconfiguration record (host/owner-host.lisp fn-owner-orc-instant-stage)
; decides the context the offline record decides.  Owner fixture: the ready
; store of tests/acl2/config-observed-tests; retention rules and store of
; tests/acl2/reclaim-instant-tests.
(in-package "ACL2")
(include-book "../../books/owner-reclaim-instant")
(include-book "must-fail-checked")
(include-book "reclaim-instant-tests")
(include-book "config-observed-tests")

; A started owner whose configuration carries RULE.
(defmacro orlit-oc (rule)
  `(fn-ocfg-make (fn-own-start *cpo-t-ready* 3) (rcit-cfg ,rule) nil nil))
; The configuration the live record at NOW yields over the owner's own.
(defmacro orlit-v (rule now)
  `(fn-cfg-value
    (fn-cfg-apply-record (fn-ocfg-config (orlit-oc ,rule))
                         (fn-ocfg-reconfig-record (orlit-oc ,rule)
                                                  (list (fn-rci-delta ,now))))))

; fn-orli-live-record-is-the-recorded-config-by-definition, reachable: the
; live record over the owner's configuration is the offline record at the
; owner's generation, next txid, generation + 1 and clock stamp.
(assert-event
 (equal (fn-cfg-apply-record (fn-ocfg-config (orlit-oc *rpt-rule*))
                             (fn-ocfg-reconfig-record (orlit-oc *rpt-rule*)
                                                      (list (fn-rci-delta 0))))
        (fn-rci-recorded-config
         (fn-ocfg-config (orlit-oc *rpt-rule*))
         (fn-cfg-generation (fn-ocfg-config (orlit-oc *rpt-rule*)))
         (fn-state-next-txid (fn-node-acceptance
                              (fn-sn-node (fn-own-store (fn-ocfg-owner (orlit-oc *rpt-rule*))))))
         (+ 1 (fn-cfg-generation (fn-ocfg-config (orlit-oc *rpt-rule*))))
         (fn-ocfg-config-stamp (fn-own-clock (fn-ocfg-owner (orlit-oc *rpt-rule*))))
         0)))

; KEYSTONE fn-orli-live-record-decides-the-context, reachable: the antecedent
; holds and the live record's context is the fixture's decided context.
(assert-event (fn-rci-instantp 0))
(assert-event (equal (fn-rcl-config-rule (fn-cfg-value (fn-ocfg-config (orlit-oc *rpt-rule*))))
                     *rpt-rule*))
(assert-event (equal (fn-rci-context (orlit-v *rpt-rule* 0) *rpt-s*)
                     (fn-rclp-ctx *rpt-rule* 0 *rpt-s*)))
(assert-event (equal (fn-rci-context (orlit-v *rpt-rule* 0) *rpt-s*) *rpt-ctx*))
; Not degenerate: under release-after 1 the instant recorded live decides,
; a day after the article's stamp and at the stamp giving different contexts,
; each the offline decision's at that instant.
(assert-event (fn-rci-instantp *rcit-late*))
(assert-event (equal (fn-rci-context (orlit-v *rcit-after* *rcit-late*) *rpt-s*) *rcit-ctx-late*))
(assert-event (equal (fn-rci-context (orlit-v *rcit-after* *rcit-stamp*) *rpt-s*) *rcit-ctx-now*))
(assert-event (not (equal *rcit-ctx-late* *rcit-ctx-now*)))
; The live record's context drives the recorded decision to the offline
; decision at that clock, which reclaims.
(assert-event (equal (car (in-arena-fn-rci-decide-stream *rpt-payloads* *rpt-profile*
                                                         (orlit-v *rcit-after* *rcit-late*)
                                                         *rpt-s* (rcit-acc *rcit-ctx-late*) nil))
                     :reclaim))

; Hypothesis removal (fn-rci-instantp): the rule is retained, the instant is
; neither nil nor a natural, and the conclusion fails.
(assert-event (equal (fn-rcl-config-rule (fn-cfg-value (fn-ocfg-config (orlit-oc *rpt-rule*))))
                     *rpt-rule*))
(assert-event (not (fn-rci-instantp :late)))
(assert-event (not (equal (fn-rci-context (orlit-v *rpt-rule* :late) *rpt-s*)
                          (fn-rclp-ctx *rpt-rule* :late *rpt-s*))))
(must-fail-checked
 (assert-event (equal (fn-rci-context (orlit-v *rpt-rule* :late) *rpt-s*)
                      (fn-rclp-ctx *rpt-rule* :late *rpt-s*))))

; Mutation (the recorded instant is the input): the live record at the
; stamp does not yield the late context.
(must-fail-checked
 (assert-event (equal (fn-rci-context (orlit-v *rcit-after* *rcit-stamp*) *rpt-s*)
                      *rcit-ctx-late*)))
