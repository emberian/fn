; fn: witnesses and teeth for books/reclaim-instant.lisp (lane log-leftovers,
; PKT-857): the reclaim's instant as a configuration row, over the reclaiming
; fixture of tests/acl2/store-reclaim-pack-tests (the owner fixture's store
; after its article completed) and the streamed decision's lifts of
; tests/acl2/store-log-reclaim-tests.
(in-package "ACL2")
(include-book "../../books/reclaim-instant")
(include-book "must-fail-checked")
(include-book "store-log-reclaim-tests")
(bpr-lift fn-rci-decide-stream 5)

; A configuration carrying a rule, and the value the host's published record
; yields over it at an instant (the record's sequence, txid, generation and
; stamp are the record's own; the fold reads only the change).
(defmacro rcit-cfg (rule)
  `(fn-cfg-make 1 (fn-cfg-apply (fn-cfg-value (fn-cfg-initial)) 1 0 (fn-rcl-rule-deltas ,rule))))
(defmacro rcit-v (rule now)
  `(fn-cfg-value (fn-rci-recorded-config (rcit-cfg ,rule) 1 0 2 0 ,now)))
(defmacro rcit-acc (ctx) `(fn-rcls-fold (rpt-events) ,ctx (fn-rcls-init)))
(defconst *rcit-stamp* (fn-article-stamp *rpt-art*))
(defconst *rcit-late* (+ *rcit-stamp* 86400))
(defconst *rcit-after* '(:release-after 1))

; fn-rci-recorded-instant-reads-back / fn-rci-recorded-context-is-the-
; decided-context, reachable: the fixture's rule, recorded at the fixture's
; instant 0; the antecedent holds and the recorded context is the fixture's
; context (the one its rewrite used).
(assert-event (fn-rci-instantp 0))
(assert-event (equal (fn-rcl-config-rule (fn-cfg-value (rcit-cfg *rpt-rule*))) *rpt-rule*))
(assert-event (and (fn-rci-recordedp (rcit-v *rpt-rule* 0))
                   (equal (fn-rci-config-now (rcit-v *rpt-rule* 0)) 0)
                   (equal (fn-rcl-config-rule (rcit-v *rpt-rule* 0)) *rpt-rule*)))
(assert-event (equal (fn-rci-context (rcit-v *rpt-rule* 0) *rpt-s*) *rpt-ctx*))
; No wall reading: the row reads back nil.
(assert-event (and (fn-rci-instantp nil)
                   (fn-rci-recordedp (rcit-v *rpt-rule* nil))
                   (equal (fn-rci-config-now (rcit-v *rpt-rule* nil)) nil)))
; Hypothesis removal (fn-rci-instantp): an instant that is neither nil nor a
; natural is not what the row reads back, and the contexts differ.
(assert-event (not (fn-rci-instantp :late)))
(assert-event (not (equal (fn-rci-context (rcit-v *rpt-rule* :late) *rpt-s*)
                          (fn-rclp-ctx *rpt-rule* :late *rpt-s*))))
(must-fail-checked
 (assert-event (equal (fn-rci-context (rcit-v *rpt-rule* :late) *rpt-s*)
                      (fn-rclp-ctx *rpt-rule* :late *rpt-s*))))

; fn-rci-recorded-decision-is-the-decision, reachable and not degenerate: the
; recorded decision over the fixture's fold is the decision at the clock, and
; it reclaims (the article's Message-ID, the freed octets).
(assert-event (equal (in-arena-fn-rci-decide-stream *rpt-payloads* *rpt-profile* (rcit-v *rpt-rule* 0)
                                                    *rpt-s* (rcit-acc *rpt-ctx*) nil)
                     (in-arena-fn-lgr-decide-stream *rpt-payloads* *rpt-profile* *rpt-rule* 0
                                                    *rpt-s* (rcit-acc *rpt-ctx*) nil)))
(assert-event (equal (car (in-arena-fn-rci-decide-stream *rpt-payloads* *rpt-profile* (rcit-v *rpt-rule* 0)
                                                         *rpt-s* (rcit-acc *rpt-ctx*) nil))
                     :reclaim))
; The instant decides, under release-after 1: recorded a day after the
; article's stamp it reclaims, recorded at the stamp it does not (too recent);
; each equals the decision at that clock.
(defconst *rcit-ctx-late* (fn-rclp-ctx *rcit-after* *rcit-late* *rpt-s*))
(defconst *rcit-ctx-now* (fn-rclp-ctx *rcit-after* *rcit-stamp* *rpt-s*))
(assert-event (equal (fn-rci-context (rcit-v *rcit-after* *rcit-late*) *rpt-s*) *rcit-ctx-late*))
(assert-event (equal (car (in-arena-fn-rci-decide-stream *rpt-payloads* *rpt-profile*
                                                         (rcit-v *rcit-after* *rcit-late*)
                                                         *rpt-s* (rcit-acc *rcit-ctx-late*) nil))
                     :reclaim))
(assert-event (equal (car (in-arena-fn-rci-decide-stream *rpt-payloads* *rpt-profile*
                                                         (rcit-v *rcit-after* *rcit-stamp*)
                                                         *rpt-s* (rcit-acc *rcit-ctx-now*) nil))
                     :none))
(assert-event (equal (in-arena-fn-rci-decide-stream *rpt-payloads* *rpt-profile*
                                                    (rcit-v *rcit-after* *rcit-late*)
                                                    *rpt-s* (rcit-acc *rcit-ctx-late*) nil)
                     (in-arena-fn-lgr-decide-stream *rpt-payloads* *rpt-profile* *rcit-after* *rcit-late*
                                                    *rpt-s* (rcit-acc *rcit-ctx-late*) nil)))
; Mutation (the record is the input, not decoration): the same store and fold
; with the other instant recorded decide differently.
(must-fail-checked
 (assert-event (equal (in-arena-fn-rci-decide-stream *rpt-payloads* *rpt-profile*
                                                     (rcit-v *rcit-after* *rcit-stamp*)
                                                     *rpt-s* (rcit-acc *rcit-ctx-late*) nil)
                      (in-arena-fn-lgr-decide-stream *rpt-payloads* *rpt-profile* *rcit-after* *rcit-late*
                                                     *rpt-s* (rcit-acc *rcit-ctx-late*) nil))))

; fn-rci-unrecorded-is-refused-by-definition: a configuration with no recorded instant is
; refused by name on --recorded (the retention rule alone decides nothing).
(assert-event (not (fn-rci-recordedp (fn-cfg-value (rcit-cfg *rpt-rule*)))))
(assert-event (equal (in-arena-fn-rci-decide-stream *rpt-payloads* *rpt-profile* (fn-cfg-value (rcit-cfg *rpt-rule*))
                                                    *rpt-s* (rcit-acc *rpt-ctx*) nil)
                     '(:refused :no-recorded-instant)))

; fn-rci-delta-is-a-delta: the staged delta passes the configuration's delta
; test at the fixture's instant; past the uint32 code it does not.
(assert-event (fn-cfg-delta-listp (list (fn-rci-delta *rcit-late*))))
(assert-event (not (fn-rci-representablep 4294967295)))
(must-fail-checked (assert-event (fn-cfg-delta-listp (list (fn-rci-delta 4294967295)))))
