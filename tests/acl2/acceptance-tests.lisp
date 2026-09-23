; Acceptance test book: executable traces, the guard-world audit, malformed
; logical-input regressions, and the teeth of the acceptance keystones.
;
; Folded from acceptance-tests, acceptance-guards-tests and
; acceptance-teeth-tests (2026-09-19).  Every negative case is a concrete
; violating value that ACL2 evaluates; nothing here is a `must-fail'.  A call
; outside a transition's guard is made under `with-guard-checking :none',
; which is the point: the :logic body is total, the :exec path is not.
(in-package "ACL2")
(include-book "../../books/acceptance-invariants")

; -----------------------------------------------------------------------------
; Guard world.  The three host transitions carry `fn-statep'; everything else
; is total.

(assert-event (equal (symbol-class 'fn-octetp (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-octetp nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-octet-listp (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-octet-listp nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-string-listp (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-string-listp nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-no-duplicatesp (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-no-duplicatesp nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-subsetp (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-subsetp nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-selection-validp (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-selection-validp nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-fencedp (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-fencedp nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-nexts-for-p (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-nexts-for-p nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-initial-nexts (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-initial-nexts nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-next-number (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-next-number nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-bump-number (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-bump-number nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-allocate-memberships (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-allocate-memberships nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-advance-nexts (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-advance-nexts nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-membership-listp (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-membership-listp nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-memberships-at-watermarkp (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-memberships-at-watermarkp nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-memberships-below-nextsp (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-memberships-below-nextsp nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-article-shapep (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-article-shapep nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-article-msgid (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-article-msgid nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-article-payload (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-article-payload nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-article-groups (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-article-groups nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-article-memberships (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-article-memberships nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-article-pin (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-article-pin nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-make-article (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-make-article nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-articlep (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-articlep nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-article-msgids (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-article-msgids nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-article-listp (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-article-listp nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-acceptedp (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-acceptedp nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-find-article (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-find-article nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-pair-equalp (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-pair-equalp nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-pair-memberp (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-pair-memberp nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-all-article-memberships (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-all-article-memberships nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-memberships-conflictsp (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-memberships-conflictsp nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-articles-freshp (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-articles-freshp nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-articles-below-nextsp (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-articles-below-nextsp nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-pending-shapep (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-pending-shapep nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-pending-txid (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-pending-txid nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-pending-generation (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-pending-generation nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-pending-msgid (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-pending-msgid nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-pending-payload (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-pending-payload nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-pending-groups (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-pending-groups nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-pending-memberships (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-pending-memberships nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-pending-pin (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-pending-pin nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-make-pending (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-make-pending nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-pendingp (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-pendingp nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-state-shapep (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-state-shapep nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-make-state (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-make-state nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-state-groups (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-state-groups nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-state-nexts (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-state-nexts nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-state-articles (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-state-articles nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-state-next-txid (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-state-next-txid nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-state-pending (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-state-pending nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-state-fenced (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-state-fenced nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-statep (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-statep nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-initial-state (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-initial-state nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-pending-matchesp (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-pending-matchesp nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-article-from-pending (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-article-from-pending nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-install-pending (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-install-pending nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-clear-pending (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-clear-pending nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-accept-prepare (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-accept-prepare nil (w state)) '(fn-statep s)))
(assert-event (equal (symbol-class 'fn-accept-complete (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-accept-complete nil (w state)) '(fn-statep s)))
(assert-event (equal (symbol-class 'fn-accept-recover (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-accept-recover nil (w state)) '(fn-statep s)))
(assert-event (equal (symbol-class 'fn-ag-car (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-ag-car nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-ag-cdr (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-ag-cdr nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-ag-member (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-ag-member nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-ag-append (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-ag-append nil (w state)) ''t))
(assert-event (equal (symbol-class 'fn-ag-less (w state)) :common-lisp-compliant))
(assert-event (equal (guard 'fn-ag-less nil (w state)) ''t))

; Total accessors and helpers on atoms and dotted lists.
(assert-event (equal (fn-article-msgid 7) nil))
(assert-event (equal (fn-pending-pin '(a b . c)) nil))
(assert-event (equal (fn-state-fenced #c(2 3)) nil))
(assert-event (fn-no-duplicatesp '(a . b)))
(assert-event (not (fn-no-duplicatesp '(a a . b))))
(assert-event (fn-subsetp '(a . b) '(a . c)))
(assert-event (equal (fn-article-msgids '(7 ("m") . tail)) '(nil "m")))
(assert-event (equal (fn-all-article-memberships
                      '(("m" nil nil (a . b)) 7 ("n" nil nil (c)) . tail))
                     '(a c)))
(assert-event (equal (fn-next-number "x" '(7 ("x" . #c(2 3)) . tail)) #c(2 3)))
(assert-event (equal (fn-bump-number "x" '(7 ("x" . #c(2 3)) . tail))
                     '(7 ("x" . #c(3 3)) . tail)))
(assert-event (fn-memberships-below-nextsp '(("x" . #c(0 -1))) nil))
(assert-event (not (fn-memberships-below-nextsp '(("x" . #c(0 1))) nil)))
(assert-event (fn-pendingp '("fn.test") '(("fn.test" . 1)) #c(0 1)
                           '(0 0 "m" nil ("fn.test") (("fn.test" . 1)) t)))

; The :logic bodies of the transitions are total: a non-state is returned
; unchanged.  These calls are outside the guard, so they run in the logic.
(defconst *ag-bad-pending* '(("fn.test") (("fn.test" . 1)) nil 0 7 nil))
(defconst *ag-bad-article-tail*
 '(("fn.test") (("fn.test" . 2))
   (("m" nil ("fn.test") (("fn.test" . 1)) t) 7) 0 nil nil))
(assert-event (not (fn-statep *ag-bad-pending*)))
(assert-event (not (fn-statep *ag-bad-article-tail*)))
(assert-event (not (fn-statep 7)))
(assert-event
 (with-guard-checking :none
  (equal (fn-accept-prepare *ag-bad-pending* 0 "m" nil '("fn.test") 841000000)
         *ag-bad-pending*)))
(assert-event
 (with-guard-checking :none
  (equal (fn-accept-complete *ag-bad-pending* 0 0 :durable) *ag-bad-pending*)))
(assert-event
 (with-guard-checking :none
  (equal (fn-accept-recover *ag-bad-pending* 0 0 :committed) *ag-bad-pending*)))
(assert-event
 (with-guard-checking :none
  (equal (fn-accept-prepare *ag-bad-article-tail* 0 "m" nil '("fn.test") 841000000)
         *ag-bad-article-tail*)))
(assert-event
 (with-guard-checking :none (equal (fn-accept-complete 7 0 0 :durable) 7)))
(assert-event
 (with-guard-checking :none
  (equal (fn-accept-recover '(a . b) 0 0 :committed) '(a . b))))

; -----------------------------------------------------------------------------
; Independent executable traces for the abstract acceptance machine.  These
; exercise logical transitions, not disk persistence or NNTP bytes.

(defconst *test-groups* '("fn.letters" "fn.test"))
(defconst *test-id-a* "<a@example.invalid>")
(defconst *test-id-b* "<b@example.invalid>")
(defconst *test-payload* '(72 105 13 10))
(defconst *test-empty* (fn-initial-state *test-groups*))

(assert-event (fn-statep *test-empty*))
(assert-event (equal (fn-state-articles *test-empty*) nil))
(assert-event (not (fn-statep '(nil nil nil 0))))
(assert-event (not (fn-statep (append *test-empty* '(hidden-field)))))
(assert-event (not (fn-statep '(nil nil nil 0 nil nil . hidden-tail))))

; Input policy rejects the entire local cross-post.
(assert-event
 (equal (fn-accept-prepare *test-empty* 7 *test-id-a* *test-payload*
                           '("fn.letters" "unknown") 841000000)
        *test-empty*))
(assert-event
 (equal (fn-accept-prepare *test-empty* 7 *test-id-a* *test-payload*
                           '("fn.letters" "fn.letters") 841000000)
        *test-empty*))
(assert-event
 (equal (fn-accept-prepare *test-empty* 7 *test-id-a* '(256) *test-groups* 841000000)
        *test-empty*))

(defconst *test-prepared*
  (fn-accept-prepare *test-empty* 7 *test-id-a* *test-payload* *test-groups* 841000000))
(assert-event (fn-statep *test-prepared*))
(assert-event (equal (fn-state-articles *test-prepared*) nil))
(assert-event (equal (fn-state-nexts *test-prepared*)
                     (fn-state-nexts *test-empty*)))
(assert-event (equal (fn-state-next-txid *test-prepared*) 1))
(assert-event
 (not (fn-pendingp *test-groups* (fn-state-nexts *test-empty*) 1
                   (append (fn-state-pending *test-prepared*) 'hidden-tail))))
(assert-event
 (equal (fn-pending-memberships (fn-state-pending *test-prepared*))
        '(("fn.letters" . 1) ("fn.test" . 1))))

; Wrong transaction, wrong generation, and arbitrary status do not publish.
(assert-event
 (equal (fn-accept-complete *test-prepared* 19 7 :durable) *test-prepared*))
(assert-event
 (equal (fn-accept-complete *test-prepared* 0 8 :durable) *test-prepared*))
(assert-event
 (equal (fn-accept-complete *test-prepared* 0 7 :nonsense) *test-prepared*))

(defconst *test-committed* (fn-accept-complete *test-prepared* 0 7 :durable))
(assert-event (fn-statep *test-committed*))
(assert-event (equal (len (fn-state-articles *test-committed*)) 1))
(assert-event
 (not (fn-articlep *test-groups*
                   (append (car (fn-state-articles *test-committed*))
                           'hidden-tail))))
(assert-event
 (equal (fn-article-memberships
         (fn-find-article *test-id-a* (fn-state-articles *test-committed*)))
        '(("fn.letters" . 1) ("fn.test" . 1))))
(assert-event
 (equal (fn-article-payload
         (fn-find-article *test-id-a* (fn-state-articles *test-committed*)))
        *test-payload*))
(assert-event
 (equal (fn-article-pin
         (fn-find-article *test-id-a* (fn-state-articles *test-committed*)))
        t))
(assert-event (equal (fn-state-nexts *test-committed*)
                     '(("fn.letters" . 2) ("fn.test" . 2))))

; A lost response/retry and a conflicting payload cannot overwrite or allocate.
(assert-event
 (equal (fn-accept-prepare *test-committed* 7 *test-id-a* *test-payload* *test-groups* 841000000)
        *test-committed*))
(assert-event
 (equal (fn-accept-prepare *test-committed* 7 *test-id-a* '(69 118 105 108) *test-groups* 841000000)
        *test-committed*))
(assert-event
 (equal (fn-accept-prepare *test-committed* 7 *test-id-a* *test-payload* '("fn.test") 841000000)
        *test-committed*))

(defconst *test-second-prepared*
  (fn-accept-prepare *test-committed* 7 *test-id-b* *test-payload* '("fn.letters") 841000000))
(assert-event (fn-statep *test-second-prepared*))
(assert-event
 (equal (fn-accept-complete *test-second-prepared* 0 7 :durable)
        *test-second-prepared*))
(defconst *test-second-committed*
  (fn-accept-complete *test-second-prepared* 1 7 :durable))
(assert-event (fn-statep *test-second-committed*))
(assert-event
 (equal (fn-find-article *test-id-a* (fn-state-articles *test-second-committed*))
        (fn-find-article *test-id-a* (fn-state-articles *test-committed*))))
(assert-event
 (equal (fn-article-memberships
         (fn-find-article *test-id-b* (fn-state-articles *test-second-committed*)))
        '(("fn.letters" . 2))))

; Indeterminate result preserves the proposal and fences all ordinary completion.
(defconst *test-fenced*
  (fn-accept-complete *test-second-prepared* 1 7 :indeterminate))
(assert-event (fn-statep *test-fenced*))
(assert-event (equal (fn-state-fenced *test-fenced*) t))
(assert-event
 (equal (fn-state-pending *test-fenced*) (fn-state-pending *test-second-prepared*)))
(assert-event
 (equal (fn-accept-prepare *test-fenced* 7 "<c@example.invalid>" '(1) '("fn.test") 841000000)
        *test-fenced*))
(assert-event (equal (fn-accept-complete *test-fenced* 1 7 :durable) *test-fenced*))
(assert-event (equal (fn-accept-complete *test-fenced* 1 7 :aborted) *test-fenced*))
(assert-event (equal (fn-accept-recover *test-fenced* 0 7 :committed) *test-fenced*))
(assert-event (equal (fn-accept-recover *test-fenced* 1 8 :absent) *test-fenced*))
(assert-event (equal (fn-accept-recover *test-fenced* 1 7 :nonsense) *test-fenced*))

(defconst *test-recovered-committed* (fn-accept-recover *test-fenced* 1 7 :committed))
(assert-event (equal *test-recovered-committed* *test-second-committed*))
(assert-event (fn-statep *test-recovered-committed*))
(assert-event
 (equal (fn-accept-prepare *test-recovered-committed* 7 *test-id-b* *test-payload* '("fn.letters") 841000000)
        *test-recovered-committed*))

(defconst *test-recovered-absent* (fn-accept-recover *test-fenced* 1 7 :absent))
(assert-event (fn-statep *test-recovered-absent*))
(assert-event
 (equal (fn-state-articles *test-recovered-absent*) (fn-state-articles *test-committed*)))
(assert-event (equal (fn-state-next-txid *test-recovered-absent*) 2))
(defconst *test-after-absent*
  (fn-accept-prepare *test-recovered-absent* 7 *test-id-b* *test-payload* '("fn.letters") 841000000))
(assert-event (fn-statep *test-after-absent*))
(assert-event (equal (fn-pending-txid (fn-state-pending *test-after-absent*)) 2))
(assert-event
 (equal (fn-accept-complete *test-after-absent* 1 7 :durable) *test-after-absent*))

; Successful known abort also leaves the transaction identity consumed.
(defconst *test-aborted* (fn-accept-complete *test-prepared* 0 7 :aborted))
(assert-event (fn-statep *test-aborted*))
(assert-event (equal (fn-state-next-txid *test-aborted*) 1))
(assert-event (equal (fn-state-articles *test-aborted*) nil))
(defconst *test-after-abort*
  (fn-accept-prepare *test-aborted* 7 *test-id-b* *test-payload* '("fn.test") 841000000))
(assert-event (fn-statep *test-after-abort*))
(assert-event (equal (fn-pending-txid (fn-state-pending *test-after-abort*)) 1))
(assert-event
 (equal (fn-accept-complete *test-after-abort* 0 7 :durable) *test-after-abort*))
(assert-event
 (equal (fn-article-memberships
         (fn-find-article *test-id-b*
                          (fn-state-articles
                           (fn-accept-complete *test-after-abort* 1 7 :durable))))
        '(("fn.test" . 1))))

; Case in a Message-ID is significant, including its domain-looking part.
(defconst *test-case-prepared*
  (fn-accept-prepare *test-committed* 7 "<a@EXAMPLE.invalid>" *test-payload* '("fn.test") 841000000))
(assert-event (fn-statep *test-case-prepared*))
(assert-event (consp (fn-state-pending *test-case-prepared*)))
(defconst *test-case-committed* (fn-accept-complete *test-case-prepared* 1 7 :durable))
(assert-event (fn-statep *test-case-committed*))
(assert-event (equal (len (fn-state-articles *test-case-committed*)) 2))

; -----------------------------------------------------------------------------
; Teeth for the acceptance keystones.
;
; The 2026-09-18 independent review names local-number freshness as genuinely
; strong: `fn-install-preserves-state' with `fn-watermark-does-not-conflict'
; and `fn-allocate-at-watermark'.  A keystone earns that name only with teeth:
; a reachable non-degenerate witness, and one concrete violating value per
; hypothesis on which the conclusion is false.

; A reachable, non-degenerate witness: two configured groups, two committed
; articles, and a third staged but not published.  The two articles differ in
; every field the invariant constrains, so a predicate that separated them
; only by its weakest clause would not do.
(defconst *acc-teeth-groups* '("fn.letters" "fn.test"))
(defconst *acc-teeth-payload-a* '(72 105 13 10))
(defconst *acc-teeth-payload-b* '(66 121 101 13 10))
(defconst *acc-teeth-id-a* "<a@example.invalid>")
(defconst *acc-teeth-id-b* "<b@example.invalid>")

(defconst *acc-teeth-empty* (fn-initial-state *acc-teeth-groups*))
(assert-event (fn-statep *acc-teeth-empty*))
(assert-event (null (fn-state-pending *acc-teeth-empty*)))

(defconst *acc-teeth-prepared-a*
  (fn-accept-prepare *acc-teeth-empty* 7 *acc-teeth-id-a*
                     *acc-teeth-payload-a* *acc-teeth-groups* 841000000))
(defconst *acc-teeth-committed-a*
  (fn-accept-complete *acc-teeth-prepared-a* 0 7 :durable))
(defconst *acc-teeth-prepared-b*
  (fn-accept-prepare *acc-teeth-committed-a* 8 *acc-teeth-id-b*
                     *acc-teeth-payload-b* *acc-teeth-groups* 841000000))
(defconst *acc-teeth-committed-b*
  (fn-accept-complete *acc-teeth-prepared-b* 1 8 :durable))

; The witness is reached by actual transitions, not constructed by hand.
(assert-event (fn-statep *acc-teeth-prepared-a*))
(assert-event (fn-statep *acc-teeth-committed-a*))
(assert-event (fn-statep *acc-teeth-prepared-b*))
(assert-event (fn-statep *acc-teeth-committed-b*))

; It is non-degenerate: two articles, two memberships each, all four local
; numbers distinct within their group, and the second article strictly above
; the first in both groups.
(assert-event (equal (len (fn-state-articles *acc-teeth-committed-b*)) 2))
(assert-event
 (equal (fn-article-memberships
         (fn-find-article *acc-teeth-id-a*
                          (fn-state-articles *acc-teeth-committed-b*)))
        '(("fn.letters" . 1) ("fn.test" . 1))))
(assert-event
 (equal (fn-article-memberships
         (fn-find-article *acc-teeth-id-b*
                          (fn-state-articles *acc-teeth-committed-b*)))
        '(("fn.letters" . 2) ("fn.test" . 2))))
(assert-event
 (equal (fn-state-nexts *acc-teeth-committed-b*)
        '(("fn.letters" . 3) ("fn.test" . 3))))
(assert-event
 (not (equal (fn-article-payload
              (fn-find-article *acc-teeth-id-a*
                               (fn-state-articles *acc-teeth-committed-b*)))
             (fn-article-payload
              (fn-find-article *acc-teeth-id-b*
                               (fn-state-articles *acc-teeth-committed-b*))))))

; The staged article that `fn-install-pending' is about: pending is a cons and
; the state is still a state, which is exactly the keystone's premise pair.
(assert-event (consp (fn-state-pending *acc-teeth-prepared-b*)))
(assert-event (fn-statep (fn-install-pending *acc-teeth-prepared-b*)))
(assert-event
 (equal (len (fn-state-articles (fn-install-pending *acc-teeth-prepared-b*))) 2))

; Teeth for `fn-install-preserves-state'
;   (implies (and (fn-statep s) (consp (fn-state-pending s)))
;            (fn-statep (fn-install-pending s)))

; Hypothesis 1, `(fn-statep s)', dropped.  A forged state whose group list is
; the integer 7 still has a well-formed pending slot, so the second hypothesis
; holds; installing it publishes an article into a state with no group list.
(defconst *acc-teeth-forged*
  (list 7 nil nil 0
        (list *acc-teeth-id-a* *acc-teeth-payload-a* *acc-teeth-groups*
              '(("fn.letters" . 1) ("fn.test" . 1)) t)
        nil))
(assert-event (not (fn-statep *acc-teeth-forged*)))
(assert-event (consp (fn-state-pending *acc-teeth-forged*)))
(assert-event (not (fn-statep (fn-install-pending *acc-teeth-forged*))))

; Hypothesis 2, `(consp (fn-state-pending s))', dropped.  The empty state is a
; state; installing its absent pending slot publishes an article whose
; Message-ID is NIL, which `fn-articlep' rejects.
(assert-event (fn-statep *acc-teeth-empty*))
(assert-event (not (consp (fn-state-pending *acc-teeth-empty*))))
(assert-event (not (fn-statep (fn-install-pending *acc-teeth-empty*))))

; Teeth for `fn-watermark-does-not-conflict'
;   (implies (and (fn-memberships-at-watermarkp memberships nexts)
;                 (fn-articles-below-nextsp articles nexts))
;            (not (fn-memberships-conflictsp memberships articles)))
;
; The conclusion mentions no next-number table, so each case is built from
; data that violates exactly one hypothesis while satisfying the other.

; Hypothesis 1, at-watermark, dropped.  A committed article already holds
; ("fn.test" . 1); the table has moved past it, so the article is below the
; watermark, but a stale allocation claims 1 again.
(defconst *acc-teeth-held-test*
  (list (fn-make-article *acc-teeth-id-a* *acc-teeth-payload-a*
                         '("fn.test") '(("fn.test" . 1)) t 841000000)))
(defconst *acc-teeth-stale-claim* '(("fn.test" . 1)))
(assert-event
 (not (fn-memberships-at-watermarkp *acc-teeth-stale-claim* '(("fn.test" . 2)))))
(assert-event (fn-articles-below-nextsp *acc-teeth-held-test* '(("fn.test" . 2))))
(assert-event
 (fn-memberships-conflictsp *acc-teeth-stale-claim* *acc-teeth-held-test*))

; Hypothesis 2, articles-below-nexts, dropped.  A different group and number:
; the allocation is exactly at the watermark, but a committed article was
; published at the watermark rather than below it, so it collides.
(defconst *acc-teeth-held-letters*
  (list (fn-make-article *acc-teeth-id-b* *acc-teeth-payload-b*
                         '("fn.letters") '(("fn.letters" . 5)) t 841000000)))
(defconst *acc-teeth-fresh-claim* '(("fn.letters" . 5)))
(assert-event
 (fn-memberships-at-watermarkp *acc-teeth-fresh-claim* '(("fn.letters" . 5))))
(assert-event
 (not (fn-articles-below-nextsp *acc-teeth-held-letters* '(("fn.letters" . 5)))))
(assert-event
 (fn-memberships-conflictsp *acc-teeth-fresh-claim* *acc-teeth-held-letters*))

; `fn-allocate-at-watermark': two hypotheses have no teeth and none are forged.
;
;   (implies (and (fn-nexts-for-p configured nexts)      ; H1
;                 (fn-subsetp groups configured)         ; H2
;                 (fn-no-duplicatesp groups))            ; H3
;            (fn-memberships-at-watermarkp
;             (fn-allocate-memberships groups nexts) nexts))
;
; H1 and H2 are believed unnecessary: `fn-bump-number' rebuilds its argument
; unchanged for an absent group and `fn-next-number' returns 0 for one, so
; under H3 both sides agree whatever `configured' is and whether or not
; `nexts' is well formed.  Dropping them needs a watermark lemma without the
; membership-list hypothesis, which is recorded open in
; planning/deputies/core.md rather than closed with a witness that does not
; exist.

; Hypothesis 3, no-duplicatesp, dropped: a repeated group is allocated twice,
; and the second copy sits one above the watermark it is compared to.
(defconst *acc-teeth-dup-groups* '("fn.test" "fn.test"))
(defconst *acc-teeth-nexts-one* '(("fn.test" . 1)))
(assert-event (not (fn-no-duplicatesp *acc-teeth-dup-groups*)))
(assert-event (fn-nexts-for-p '("fn.test") *acc-teeth-nexts-one*))
(assert-event (fn-subsetp *acc-teeth-dup-groups* '("fn.test")))
(assert-event
 (equal (fn-allocate-memberships *acc-teeth-dup-groups* *acc-teeth-nexts-one*)
        '(("fn.test" . 1) ("fn.test" . 2))))
(assert-event
 (not (fn-memberships-at-watermarkp
       (fn-allocate-memberships *acc-teeth-dup-groups* *acc-teeth-nexts-one*)
       *acc-teeth-nexts-one*)))
