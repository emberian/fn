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

; -----------------------------------------------------------------------------
; THE TWO HEADLINE THEOREMS (plan T8): the live scenario.
;
; The host's live administrative arm, event for event
; (host/native/admin.lisp `fnn-owner-live-admin-serialized'): open a private
; connection, (:reconfigure cid deltas), (:close cid), the durable
; publication, (:complete).  Run TWICE, the first creating a group and the
; second adding a peer, over an owner holding a reader that opened at
; generation 1 and never advances.  The second run is the one the old
; `fn-ocfg-complete' could not publish: after a live group creation the live
; node's domain no longer matched the configuration, and completion gated on
; `fn-cnode-statep' of that pair (the finding recorded above
; `fn-ocfg-published-config').

(defconst *ocfg-l-history1* (list *fn-cfg-default-record*))
(defconst *ocfg-l-replay1* (fn-cnode-config-replay *ocfg-l-history1*))
(assert-event (equal (fn-replay-result-kind *ocfg-l-replay1*) :ok))
(assert-event (equal (fn-cnode-config (fn-replay-result-node *ocfg-l-replay1*))
                     *ocfg-t-g1*))

; The recovered owner exactly as fn-owner-recover installs it: the replayed
; configuration, no pins, nothing staged; a clock observed; one reader open.
(defconst *ocfg-l-0*
  (fn-ocfg-make (fn-own-start (fn-sn-initial *ocfg-t-groups*
                                             (fn-cfg-capacity (fn-cfg-value *ocfg-t-g1*)))
                              4)
                *ocfg-t-g1* nil nil))
(defconst *ocfg-l-clocked*
  (fn-ocfg-step *ocfg-l-0*
                (list :observe (fn-clock-observation 5000000 1790000000000 0 t))))
(defconst *ocfg-l-reader* (cdr (fn-ocfg-open *ocfg-l-clocked* nil)))
(assert-event (fn-ocfg-statep *ocfg-l-reader*))
(assert-event (equal (fn-ocfg-conn-generation *ocfg-l-reader* 0) 1))

(defun ocfg-l-live-admin (oc deltas)
  ; The host's three events around one private connection, returning the
  ; state at the instant before durability and the published state.
  (declare (xargs :mode :program))
  (let* ((cid (fn-own-next-id (fn-ocfg-owner oc)))
         (opened (cdr (fn-ocfg-open oc nil)))
         (staged (fn-ocfg-step (fn-ocfg-step opened (list :reconfigure cid deltas))
                               (list :close cid))))
    (list opened staged (fn-ocfg-step staged (list :complete)))))

(defconst *ocfg-l-deltas1*
  (list (fn-cfg-create-group "fn.dtn" *fn-cfg-default-policy-id*)))
(defconst *ocfg-l-peer*
  (fn-cfg-peer-make "far" "far.example.invalid"
                    (list :nntp 1 "192.0.2.44" 1119 '(:clear))
                    (list "fn.*" *fn-record-max-payload* 16) nil
                    (list :source-address "192.0.2.44")))
(assert-event (fn-cfg-peerp *ocfg-l-peer*))
(defconst *ocfg-l-deltas2* (list (fn-cfg-set-peer-delta *ocfg-l-peer*)))

(defconst *ocfg-l-run1* (ocfg-l-live-admin *ocfg-l-reader* *ocfg-l-deltas1*))
(defconst *ocfg-l-open1* (first *ocfg-l-run1*))
(defconst *ocfg-l-staged1* (second *ocfg-l-run1*))
(defconst *ocfg-l-pub1* (third *ocfg-l-run1*))
(defconst *ocfg-l-record1* (fn-ocfg-staged *ocfg-l-staged1*))
(assert-event (fn-cfg-recordp *ocfg-l-record1*))
(assert-event (equal (fn-cfg-generation (fn-ocfg-config *ocfg-l-pub1*)) 2))
(assert-event (equal (fn-cnode-served-of (fn-ocfg-config *ocfg-l-pub1*))
                     '("fn.letters" "fn.test" "fn.dtn")))

(defconst *ocfg-l-run2* (ocfg-l-live-admin *ocfg-l-pub1* *ocfg-l-deltas2*))
(defconst *ocfg-l-open2* (first *ocfg-l-run2*))
(defconst *ocfg-l-staged2* (second *ocfg-l-run2*))
(defconst *ocfg-l-pub2* (third *ocfg-l-run2*))
(defconst *ocfg-l-record2* (fn-ocfg-staged *ocfg-l-staged2*))
(assert-event (fn-cfg-recordp *ocfg-l-record2*))
; The second live reconfiguration IS published, as generation 3, and the
; peer is in it.
(assert-event (equal (fn-cfg-generation (fn-ocfg-config *ocfg-l-pub2*)) 3))
(assert-event (fn-cfg-peer-find "far" (fn-cfg-peers (fn-cfg-value (fn-ocfg-config *ocfg-l-pub2*)))))
; ...where the live pair it is checked against is NOT a configured node: the
; domain moved and the node did not.  This is the state the old completion
; refused to publish from.
(assert-event (not (fn-cnode-statep (fn-ocfg-live-cnode *ocfg-l-staged2*))))

; ---- fn-ocfg-no-reader-observes-a-half-change: witness ----
; Reader 0 opened at generation 1.  Across both live reconfigurations its
; connection record and its pin are the ones it opened with, and it serves
; the two-group table while the live configuration serves four groups' worth
; of change (a group and a peer).
(assert-event (equal (fn-own-find-conn 0 (fn-own-conns (fn-ocfg-owner *ocfg-l-pub2*)))
                     (fn-own-find-conn 0 (fn-own-conns (fn-ocfg-owner *ocfg-l-reader*)))))
(assert-event (equal (fn-ocfg-conn-config *ocfg-l-pub2* 0) *ocfg-t-g1*))
(assert-event (equal (fn-ocfg-served *ocfg-l-pub2* 0) '("fn.letters" "fn.test")))
(assert-event (not (equal (fn-ocfg-config *ocfg-l-pub2*) (fn-ocfg-conn-config *ocfg-l-pub2* 0))))
; The theorem's own instance over the two events that carry the change.
(defconst *ocfg-l-cid2* (fn-own-next-id (fn-ocfg-owner *ocfg-l-pub1*)))
(defconst *ocfg-l-s2* (fn-ocfg-step *ocfg-l-open2* (list :reconfigure *ocfg-l-cid2* *ocfg-l-deltas2*)))
(assert-event (fn-ocfg-staged *ocfg-l-s2*))
(assert-event (equal (fn-ocfg-owner (fn-ocfg-step *ocfg-l-s2* '(:complete)))
                     (fn-ocfg-owner *ocfg-l-open2*)))
(assert-event (equal (fn-ocfg-pins (fn-ocfg-step *ocfg-l-s2* '(:complete)))
                     (fn-ocfg-pins *ocfg-l-open2*)))
(assert-event (equal (fn-ocfg-config *ocfg-l-s2*) (fn-ocfg-config *ocfg-l-open2*)))
; published is the WHOLE record: every intermediate value of the delta list
; differs from it (a two-delta record, applied whole).
(defconst *ocfg-l-two*
  (list (fn-cfg-create-group "fn.two" *fn-cfg-default-policy-id*)
        (fn-cfg-set-capacity 2000000)))
(defconst *ocfg-l-s3* (fn-ocfg-step *ocfg-l-open2* (list :reconfigure *ocfg-l-cid2* *ocfg-l-two*)))
(defconst *ocfg-l-p3* (fn-ocfg-config (fn-ocfg-step *ocfg-l-s3* '(:complete))))
(assert-event (equal (fn-cnode-served-of *ocfg-l-p3*)
                     '("fn.letters" "fn.test" "fn.dtn" "fn.two")))
(assert-event (equal (fn-cfg-capacity (fn-cfg-value *ocfg-l-p3*)) 2000000))

; Its one hypothesis, that something was staged: a refused reconfiguration
; (an empty delta list) over an owner in the middle of an article
; completion.  `(:complete)' is then the ARTICLE completion and the owner
; moves -- the first conjunct fails.
(defun ocfg-l-record (sequence txid msgid)
  (fn-record-make sequence txid txid msgid
                  (list 77 101 115 115 97 103 101 45 73 68 58 32 60 120 62 13 10 13 10
                        72 105 13 10)
                  '("fn.letters")
                  (concatenate 'string "ocfg-pin:" msgid)
                  (concatenate 'string "ocfg-content:" msgid)
                  (concatenate 'string "ocfg-release:" msgid)
                  2))
(defconst *ocfg-l-completing*
  (fn-ocfg-make
   (fn-own-run (fn-own-step (fn-own-step (fn-own-start (fn-sn-initial *ocfg-t-groups* 10) 4)
                                         '(:open))
                            '(:begin 0))
               (list '(:store (:io :start-frontier nil))
                     '(:store (:io :frontier-file :ok))
                     '(:store (:io :frontier-replace :ok))
                     '(:store (:io :frontier-directory :ok))
                     (list :store (list :prepare (ocfg-l-record 0 0 "<t8@example>")))
                     '(:store (:io :record-file :ok))
                     '(:store (:io :record-link :ok))
                     '(:store (:io :record-directory :ok))))
   *ocfg-t-g1* (list (cons 0 *ocfg-t-g1*)) nil))
(assert-event (equal (fn-sf-phase (fn-sn-files (fn-own-store (fn-ocfg-owner *ocfg-l-completing*))))
                     :completing))
(defconst *ocfg-l-refused* (fn-ocfg-step *ocfg-l-completing* (list :reconfigure 0 nil)))
(assert-event (not (fn-ocfg-staged *ocfg-l-refused*)))
(assert-event (not (equal (fn-ocfg-owner (fn-ocfg-step *ocfg-l-refused* '(:complete)))
                          (fn-ocfg-owner *ocfg-l-completing*))))

; ---- fn-ocfg-crash-at-any-instant-recovers-the-live-generation: witness ----
; Every instant of both runs.  Before each record is durable the durable
; history replays to the live configuration; once it is durable, the history
; with it appended replays to exactly the configuration completion publishes.
(defconst *ocfg-l-history2* (append *ocfg-l-history1* (list *ocfg-l-record1*)))
(defconst *ocfg-l-history3* (append *ocfg-l-history2* (list *ocfg-l-record2*)))
(assert-event (equal (fn-cnode-config (fn-replay-result-node (fn-cnode-config-replay *ocfg-l-history1*)))
                     (fn-ocfg-config *ocfg-l-staged1*)))
(assert-event (equal (fn-replay-result-kind (fn-cnode-config-replay *ocfg-l-history2*)) :ok))
(assert-event (equal (fn-cnode-config (fn-replay-result-node (fn-cnode-config-replay *ocfg-l-history2*)))
                     (fn-ocfg-config *ocfg-l-pub1*)))
(assert-event (equal (fn-cnode-config (fn-replay-result-node (fn-cnode-config-replay *ocfg-l-history2*)))
                     (fn-ocfg-config *ocfg-l-staged2*)))
(assert-event (equal (fn-replay-result-kind (fn-cnode-config-replay *ocfg-l-history3*)) :ok))
(assert-event (equal (fn-cnode-config (fn-replay-result-node (fn-cnode-config-replay *ocfg-l-history3*)))
                     (fn-ocfg-config *ocfg-l-pub2*)))
(assert-event (equal (fn-cfg-generation (fn-ocfg-config *ocfg-l-pub2*))
                     (fn-cfg-record-generation *ocfg-l-record2*)))
(assert-event (null (fn-ocfg-staged *ocfg-l-pub2*)))
; The old completion on the same state: it keeps generation 2, so the
; durable history (generation 3) and the live owner disagree -- the defect,
; evaluated rather than described.
(assert-event (with-guard-checking :none
               (equal (fn-cnode-config
                       (fn-cnode-apply-config (fn-ocfg-live-cnode *ocfg-l-staged2*)
                                              *ocfg-l-record2* (fn-cnode-line-ceiling)))
                      (fn-ocfg-config *ocfg-l-staged2*))))

; Hypothesis 1, nothing staged: a stale staged record whose sequence is not
; the replay's next.  Completion publishes it (it is acceptable), but the
; durable history with it appended does not replay.
(defconst *ocfg-l-stale-record*
  (fn-cfg-record-make 7 0 2 *ocfg-l-deltas1* *fn-cfg-default-stamp*))
(defconst *ocfg-l-stale*
  (fn-ocfg-make (fn-ocfg-owner *ocfg-l-reader*) *ocfg-t-g1*
                (fn-ocfg-pins *ocfg-l-reader*) *ocfg-l-stale-record*))
(defconst *ocfg-l-stale-staged*
  (fn-ocfg-step (fn-ocfg-step *ocfg-l-stale* (list :reconfigure 0 *ocfg-l-deltas2*))
                (list :close 0)))
(assert-event (equal (fn-ocfg-staged *ocfg-l-stale-staged*) *ocfg-l-stale-record*))
(assert-event (not (equal (fn-replay-result-kind
                           (fn-cnode-config-replay
                            (append *ocfg-l-history1* (list *ocfg-l-stale-record*))))
                          :ok)))

; Hypothesis 2, the durable history replays :ok, at the theorem's own
; instance oc = *ocfg-l-open1* (whose staged record is *ocfg-l-record1*): a
; history whose second
; record is refused, so the replay FAULTS at a last-good node whose
; configuration is still the live one (hypothesis 3 holds).  The staged
; record lands after the refused one and the durable history does not
; replay.
(defconst *ocfg-l-bad-history*
  (list *fn-cfg-default-record*
        (fn-cfg-record-make 1 0 2 (list (fn-cfg-remove-group "fn.absent"))
                            *fn-cfg-default-stamp*)))
(assert-event (equal (fn-replay-result-kind (fn-cnode-config-replay *ocfg-l-bad-history*)) :fault))
(assert-event (equal (fn-cnode-config (fn-replay-result-node (fn-cnode-config-replay *ocfg-l-bad-history*)))
                     (fn-ocfg-config *ocfg-l-reader*)))
(assert-event (not (equal (fn-replay-result-kind
                           (fn-cnode-config-replay
                            (append *ocfg-l-bad-history* (list *ocfg-l-record1*))))
                          :ok)))

; Hypothesis 3, the history replays to the LIVE configuration, at the
; theorem's own instance oc = *ocfg-l-open2* (staged record
; *ocfg-l-record2*): after the
; first publication the live configuration is generation 2, but the durable
; history offered is generation 1's.  The second record's sequence is 2, the
; replay expects 1, and the history with it appended does not replay.
(assert-event (not (equal (fn-cnode-config (fn-replay-result-node (fn-cnode-config-replay *ocfg-l-history1*)))
                          (fn-ocfg-config *ocfg-l-pub1*))))
(assert-event (not (equal (fn-replay-result-kind
                           (fn-cnode-config-replay
                            (append *ocfg-l-history1* (list *ocfg-l-record2*))))
                          :ok)))

; The seam this step does NOT close (books/owner-config.lisp OPEN item 3):
; the live node's acceptance state never learns the group the live
; configuration published, so GROUP and LIST ACTIVE, which answer from that
; list, do not show `fn.dtn' until a restart replays the configuration.
(assert-event (member-equal "fn.dtn" (fn-cnode-served-of (fn-ocfg-config *ocfg-l-pub2*))))
(assert-event (not (member-equal "fn.dtn"
                                 (fn-state-groups
                                  (fn-node-acceptance
                                   (fn-sn-node (fn-own-store (fn-ocfg-owner *ocfg-l-pub2*))))))))
