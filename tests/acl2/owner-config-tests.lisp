; Evidence for the configured owner (books/owner-config.lisp): the
; per-connection configuration pin of specs/reconfiguration.md section 2.2.
;
; Order follows docs/proof-style.md section 6: the guard-world audit, then the
; scenario (an owner over the initial store, a connection opened under
; generation 1, the live configuration moved to generation 2 and a second
; connection opened under it, then the first connection advanced across the
; move), then the teeth: one concrete violating value per hypothesis of each
; keystone, each an assert-event on the negated conclusion.
;
; The scenario is built so that no assertion can hold by accident of an
; empty value.  Its two configurations differ in generation AND in served
; table, its two pins are two different configurations at once, and the
; advance it measures MOVES a pin rather than confirming one.

(in-package "ACL2")
(include-book "../../books/owner-config")

; -----------------------------------------------------------------------------
; Guard-world audit: the pin table, the recognizer and the three connection
; events are total in the executable sense.

(assert-event (equal (symbol-class 'fn-ocfg-statep (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-ocfg-statep nil (w state)) *t*))
(assert-event (equal (symbol-class 'fn-ocfg-open (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-ocfg-open nil (w state)) *t*))
(assert-event (equal (symbol-class 'fn-ocfg-advance (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-ocfg-advance nil (w state)) *t*))
(assert-event (equal (symbol-class 'fn-ocfg-conn-config (w state)) :common-lisp-compliant))
(assert-event (equal (symbol-class 'fn-ocfg-list-active (w state)) :common-lisp-compliant))
(assert-event (equal (symbol-class 'fn-ocfg-pin-add (w state)) :common-lisp-compliant))
(assert-event (equal (symbol-class 'fn-ocfg-pin-set (w state)) :common-lisp-compliant))

; -----------------------------------------------------------------------------
; Two configurations that differ in what they serve.

(defconst *ocfg-t-groups* '("fn.letters" "fn.test"))

(defconst *ocfg-t-g1*
  (fn-config-replay 0 (fn-cnode-line-ceiling) (list *fn-cfg-default-record*)))

(defconst *ocfg-t-record2*
  (fn-cfg-record-make 1 1 2
                      (list (fn-cfg-create-group "fn.dtn" *fn-cfg-default-policy-id*))
                      *fn-cfg-default-stamp*))

(defconst *ocfg-t-g2*
  (fn-config-replay 0 (fn-cnode-line-ceiling)
                    (list *fn-cfg-default-record* *ocfg-t-record2*)))

(assert-event (fn-cfgp *ocfg-t-g1*))
(assert-event (fn-cfgp *ocfg-t-g2*))
(assert-event (equal (fn-cfg-generation *ocfg-t-g1*) 1))
(assert-event (equal (fn-cfg-generation *ocfg-t-g2*) 2))
(assert-event (equal (fn-cnode-served-of *ocfg-t-g1*) '("fn.letters" "fn.test")))
(assert-event (equal (fn-cnode-served-of *ocfg-t-g2*)
                     '("fn.letters" "fn.test" "fn.dtn")))
(assert-event (not (equal *ocfg-t-g1* *ocfg-t-g2*)))

; -----------------------------------------------------------------------------
; The scenario.

; An owner over the initial store, bound to three connections, with the
; generation-1 configuration live and no connection open.
(defconst *ocfg-t-owner0* (fn-own-start (fn-sn-initial *ocfg-t-groups* 10) 3))
(defconst *ocfg-t-0* (fn-ocfg-make *ocfg-t-owner0* *ocfg-t-g1* nil nil))
(assert-event (fn-ocfg-statep *ocfg-t-0*))
(assert-event (equal (fn-own-next-id (fn-ocfg-owner *ocfg-t-0*)) 0))

; Connection 0 opens under generation 1.
(defconst *ocfg-t-1* (cdr (fn-ocfg-open *ocfg-t-0* nil)))
(assert-event (fn-ocfg-statep *ocfg-t-1*))
(assert-event (fn-own-find-conn 0 (fn-own-conns (fn-ocfg-owner *ocfg-t-1*))))
(assert-event (equal (fn-own-next-id (fn-ocfg-owner *ocfg-t-1*)) 1))

; The live configuration moves to generation 2.  The pin table does not: the
; recognizer constrains its DOMAIN (one pin per open connection) and not its
; values, so this state is as related as the one before it.
(defconst *ocfg-t-2*
  (fn-ocfg-make (fn-ocfg-owner *ocfg-t-1*) *ocfg-t-g2*
                (fn-ocfg-pins *ocfg-t-1*) nil))
(assert-event (fn-ocfg-statep *ocfg-t-2*))

; Connection 1 opens under generation 2, beside connection 0 at generation 1.
(defconst *ocfg-t-3* (cdr (fn-ocfg-open *ocfg-t-2* nil)))
(assert-event (fn-ocfg-statep *ocfg-t-3*))
(assert-event (equal (fn-own-next-id (fn-ocfg-owner *ocfg-t-3*)) 2))

; -----------------------------------------------------------------------------
; fn-ocfg-open-pins-the-live-configuration.  Witness, then one violating
; value per hypothesis.
;
; The witness is the second open, not the first: at the first open the live
; configuration is the only configuration in the state, so a pin of anything
; at all would satisfy the conclusion.  At the second, two configurations are
; live in the same state and the pin table already holds the other one.

(assert-event (equal (fn-ocfg-conn-config *ocfg-t-3* 1) *ocfg-t-g2*))
(assert-event (equal (fn-ocfg-conn-generation *ocfg-t-3* 1) 2))
(assert-event (equal (fn-ocfg-conn-generation *ocfg-t-3* 0) 1))
(assert-event (not (equal (fn-ocfg-conn-config *ocfg-t-3* 0)
                          (fn-ocfg-conn-config *ocfg-t-3* 1))))
(assert-event (equal (fn-ocfg-served *ocfg-t-3* 0) '("fn.letters" "fn.test")))
(assert-event (equal (fn-ocfg-served *ocfg-t-3* 1)
                     '("fn.letters" "fn.test" "fn.dtn")))

; Hypothesis 1, (fn-ocfg-statep oc): a STALE pin at the identifier the next
; open will allocate.  fn-ocfg-pin-add never overwrites, so the pin survives
; the open and the new connection serves generation 1 while the live
; configuration is generation 2.  The wrong value is a whole configuration,
; not an absence.
(defconst *ocfg-t-stale*
  (fn-ocfg-make *ocfg-t-owner0* *ocfg-t-g2* (list (cons 0 *ocfg-t-g1*)) nil))
(assert-event (not (fn-ocfg-statep *ocfg-t-stale*)))
(defconst *ocfg-t-stale-open* (cdr (fn-ocfg-open *ocfg-t-stale* nil)))
(assert-event (fn-own-find-conn 0 (fn-own-conns (fn-ocfg-owner *ocfg-t-stale-open*))))
(assert-event (not (equal (fn-ocfg-conn-config *ocfg-t-stale-open* 0)
                          (fn-ocfg-config *ocfg-t-stale*))))
(assert-event (equal (fn-ocfg-conn-config *ocfg-t-stale-open* 0) *ocfg-t-g1*))
(assert-event (equal (fn-ocfg-served *ocfg-t-stale-open* 0)
                     '("fn.letters" "fn.test")))

; Hypothesis 2, the open installed a connection at that identifier: an owner
; already at its connection bound REFUSES the open, and the identifier it
; would have used has no pin, so the conclusion is false at a state the
; recognizer accepts.  fn-ocfg-statep holds here; only this hypothesis fails.
(defconst *ocfg-t-full0*
  (fn-ocfg-make (fn-own-start (fn-sn-initial *ocfg-t-groups* 10) 1)
                *ocfg-t-g1* nil nil))
(defconst *ocfg-t-full1* (cdr (fn-ocfg-open *ocfg-t-full0* nil)))
(assert-event (fn-ocfg-statep *ocfg-t-full1*))
(assert-event (equal (fn-own-next-id (fn-ocfg-owner *ocfg-t-full1*)) 1))
(defconst *ocfg-t-full2* (cdr (fn-ocfg-open *ocfg-t-full1* nil)))
(assert-event (not (fn-own-find-conn 1 (fn-own-conns (fn-ocfg-owner *ocfg-t-full2*)))))
(assert-event (not (equal (fn-ocfg-conn-config *ocfg-t-full2* 1)
                          (fn-ocfg-config *ocfg-t-full1*))))
(assert-event (equal (fn-ocfg-conn-config *ocfg-t-full2* 1) nil))

; -----------------------------------------------------------------------------
; fn-ocfg-advance-observes-the-live-configuration.  Witness, then one
; violating value per hypothesis.
;
; The witness MOVES a pin: connection 0 is at generation 1 before the advance
; and at generation 2 after it, so an advance that did nothing would fail the
; assertion rather than pass it.

(defconst *ocfg-t-4* (fn-ocfg-advance *ocfg-t-3* 0))
(assert-event (fn-own-find-conn
               0 (fn-own-conns (fn-own-advance (fn-ocfg-owner *ocfg-t-3*) 0))))
(assert-event (equal (fn-ocfg-conn-config *ocfg-t-4* 0) *ocfg-t-g2*))
(assert-event (equal (fn-ocfg-conn-generation *ocfg-t-4* 0) 2))
(assert-event (not (equal (fn-ocfg-conn-config *ocfg-t-4* 0)
                          (fn-ocfg-conn-config *ocfg-t-3* 0))))
(assert-event (equal (fn-ocfg-served *ocfg-t-4* 0)
                     '("fn.letters" "fn.test" "fn.dtn")))
(assert-event (fn-ocfg-statep *ocfg-t-4*))
; the other connection's pin did not move with it
(assert-event (equal (fn-ocfg-conn-config *ocfg-t-4* 1) *ocfg-t-g2*))

; Hypothesis 1, (fn-ocfg-statep oc): an open connection with NO pin.
; fn-ocfg-pin-set replaces and never adds -- it returns nil on an empty table
; -- so the re-pin is a silent no-op and the advanced connection serves
; NOTHING where the live configuration serves three groups.
(defconst *ocfg-t-unpinned*
  (fn-ocfg-make (fn-ocfg-owner *ocfg-t-3*) *ocfg-t-g2* nil nil))
(assert-event (not (fn-ocfg-statep *ocfg-t-unpinned*)))
(assert-event (fn-own-find-conn
               0 (fn-own-conns (fn-own-advance (fn-ocfg-owner *ocfg-t-unpinned*) 0))))
(assert-event (not (equal (fn-ocfg-conn-config (fn-ocfg-advance *ocfg-t-unpinned* 0) 0)
                          (fn-ocfg-config *ocfg-t-unpinned*))))
(assert-event (equal (fn-ocfg-served (fn-ocfg-advance *ocfg-t-unpinned* 0) 0) nil))
(assert-event (equal (fn-cnode-served-of (fn-ocfg-config *ocfg-t-unpinned*))
                     '("fn.letters" "fn.test" "fn.dtn")))

; Hypothesis 2, the advance kept a connection at that identifier: an
; identifier no connection holds.  fn-ocfg-statep holds of the state; only
; this hypothesis fails, and the conclusion fails with it.
(assert-event (not (fn-own-find-conn
                    9 (fn-own-conns (fn-own-advance (fn-ocfg-owner *ocfg-t-3*) 9)))))
(assert-event (not (equal (fn-ocfg-conn-config (fn-ocfg-advance *ocfg-t-3* 9) 9)
                          (fn-ocfg-config *ocfg-t-3*))))
(assert-event (equal (fn-ocfg-conn-config (fn-ocfg-advance *ocfg-t-3* 9) 9) nil))
(assert-event (equal (fn-ocfg-pins (fn-ocfg-advance *ocfg-t-3* 9))
                     (fn-ocfg-pins *ocfg-t-3*)))

; -----------------------------------------------------------------------------
; fn-ocfg-pin-is-stable-without-advance.  Witness, then one violating value
; per hypothesis.
;
; The witness is non-degenerate in the direction that matters: the event list
; is not empty and not inert, it OPENS another connection (which writes the
; pin table) and observes a clock, and the pin it must not move is a real
; configuration that differs from the live one.

(defconst *ocfg-t-quiet* (list '(:open) (list :observe (fn-clock-observation 9 90 3 t))))
(assert-event (with-guard-checking :none
               (not (fn-ocfg-repins-forp 0 *ocfg-t-quiet*))))
(defconst *ocfg-t-quiet-run*
  (with-guard-checking :none (fn-ocfg-run *ocfg-t-3* *ocfg-t-quiet*)))
(assert-event (equal (fn-ocfg-pin-find 0 (fn-ocfg-pins *ocfg-t-quiet-run*))
                     (fn-ocfg-pin-find 0 (fn-ocfg-pins *ocfg-t-3*))))
(assert-event (equal (fn-ocfg-conn-generation *ocfg-t-quiet-run* 0) 1))
; the list really did write the table: a third connection is pinned now
(assert-event (equal (fn-ocfg-conn-generation *ocfg-t-quiet-run* 2) 2))

; Hypothesis 1, (fn-ocfg-pin-find id (fn-ocfg-pins oc)): an identifier with no
; pin, which one (:open) then gives one.  The two sides differ, so the
; conclusion is false without the hypothesis.
(assert-event (null (fn-ocfg-pin-find 2 (fn-ocfg-pins *ocfg-t-3*))))
(assert-event (with-guard-checking :none
               (not (fn-ocfg-repins-forp 2 (list '(:open))))))
(assert-event (with-guard-checking :none
               (not (equal (fn-ocfg-pin-find
                            2 (fn-ocfg-pins (fn-ocfg-run *ocfg-t-3* (list '(:open)))))
                           (fn-ocfg-pin-find 2 (fn-ocfg-pins *ocfg-t-3*))))))
(assert-event (with-guard-checking :none
               (equal (cdr (fn-ocfg-pin-find
                            2 (fn-ocfg-pins (fn-ocfg-run *ocfg-t-3* (list '(:open))))))
                      *ocfg-t-g2*)))

; Hypothesis 2, (not (fn-ocfg-repins-forp id events)): a list that DOES
; re-pin it.  The pin moves from generation 1 to generation 2.
(defconst *ocfg-t-loud* (list '(:advance 0)))
(assert-event (with-guard-checking :none (fn-ocfg-repins-forp 0 *ocfg-t-loud*)))
(assert-event (with-guard-checking :none
               (not (equal (fn-ocfg-pin-find
                            0 (fn-ocfg-pins (fn-ocfg-run *ocfg-t-3* *ocfg-t-loud*)))
                           (fn-ocfg-pin-find 0 (fn-ocfg-pins *ocfg-t-3*))))))
(assert-event (with-guard-checking :none
               (equal (fn-ocfg-conn-generation
                       (fn-ocfg-run *ocfg-t-3* *ocfg-t-loud*) 0)
                      2)))

; -----------------------------------------------------------------------------
; fn-ocfg-list-active-lists-the-pinned-served-table.  One hypothesis, so the
; negative assertion is the case: an identifier with no connection lists
; nothing.  The positive witness is the separating one -- the same command on
; two connections of the same owner answers two different group lists,
; because they are pinned at two generations.

(assert-event (not (equal (fn-ocfg-list-active *ocfg-t-3* 0)
                          (fn-ocfg-list-active *ocfg-t-3* 1))))
(assert-event (null (fn-ocfg-list-active *ocfg-t-3* 9)))
(assert-event (equal (fn-ocfg-list-active *ocfg-t-4* 0)
                     (fn-ocfg-list-active *ocfg-t-3* 1)))

; -----------------------------------------------------------------------------
; The identifier bound the pin table rests on (fn-own-ids-below-next-p,
; books/owner-invariants.lisp): the owner never holds an open connection at
; the identifier its next open will take, so fn-ocfg-pin-add cannot meet a
; stale pin there.  Evaluated here rather than only proved, because the
; keystone above is exactly as good as this bound.

(assert-event (not (fn-own-find-conn (fn-own-next-id (fn-ocfg-owner *ocfg-t-3*))
                                     (fn-own-conns (fn-ocfg-owner *ocfg-t-3*)))))
(assert-event (fn-own-ids-below-next-p (fn-own-conns (fn-ocfg-owner *ocfg-t-3*)) 2))
(assert-event (not (fn-own-ids-below-next-p (fn-own-conns (fn-ocfg-owner *ocfg-t-3*)) 1)))
(assert-event (not (fn-own-relation
                    (fn-own-set-conns (fn-ocfg-owner *ocfg-t-3*)
                                      (list (fn-own-conn-make
                                             2 0 0 nil nil nil nil nil))))))
