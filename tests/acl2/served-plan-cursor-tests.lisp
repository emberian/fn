; served-plan-cursor-tests.lisp -- teeth for books/served-plan-cursor.lisp
; (lane join-f2-13, 2026-09-29; PRF-1020).
; POSITIVE: over the three-article catalog of tests/acl2/over-window-tests
; (its fixture repeated under spct-), the arm's plan starts at a cursor
; (fn-splan-at-cursorp; window size 0; not done; every cursor fresh and the
; plan fn-splan-cw-okp), and the host's loop -- windows of W octets off the
; mutex, a quantum of WL numbers at each cursor -- once done wrote exactly the
; unbounded reader's reply, at three (W, WL) pairs including one quantum and
; one window (fn-splan-cw-drain-of-the-arm-is-the-unbounded-reply's complete
; antecedent and conclusion).  The loop really takes its rounds: too few and
; the plan is not done and the octets are a strict prefix (the keystone's
; hypothesis, its teeth).  A plan whose cursor is not one answers :malformed
; and is left where it is (fn-splan-cursor-step; never for an okp plan:
; fn-splan-cursor-step-of-okp-is-ok).  MUST-FAIL: the malformed plan's step
; is not :ok; a plan at a cursor has no positive window size and is not done.

(in-package "ACL2")
(include-book "../../books/served-plan-cursor")
(include-book "must-fail-checked")

(local (in-theory (enable fn-splan-cursor-window fn-splan-rest-cursor-step fn-splan-cursor-step
                          fn-splan-cw-octets fn-splan-cw-remaining fn-splan-cw-drain
                          fn-splan-fresh-cursorp fn-splan-fresh-effectsp
                          fn-splan-cw-rest-okp fn-splan-cw-okp
                          fn-splan-rest-empties fn-splan-empties)))

(defconst *spct-p0* (append (fn-record-string-octets "Subject: a") '(13 10 13 10 65 13 10)))
(defconst *spct-p1* (append (fn-record-string-octets "Subject: b") '(13 10 13 10 66 13 10)))
(defconst *spct-p2* (append (fn-record-string-octets "Subject: c") '(13 10 13 10 67 13 10)))
(defconst *spct-w0* (fn-record-make 0 1 1 "<a@x>" *spct-p0* '("fn.test") "o" "s" "e" 1 5))
(defconst *spct-w1* (fn-record-make 1 2 2 "<b@x>" *spct-p1* '("fn.test" "fn.other") "o" "s" "e" 1 5))
(defconst *spct-w2* (fn-record-make 2 3 3 "<c@x>" *spct-p2* '("fn.test") "o" "s" "e" 1 5))

(defun spct-held (w handle numbers)
  (fn-held-make (fn-record-sequence w) (fn-record-txid w) (fn-record-generation w)
                (fn-record-msgid w) handle (fn-record-groups w) (fn-record-obligation-id w)
                (fn-record-content-subject w) (fn-record-release-evidence w)
                (fn-record-charge w) (fn-record-stamp w)
                (fn-held-facts-of (fn-record-payload w))
                (fn-held-context-of (fn-record-payload w) nil 0) numbers nil))

(defconst *spct-a* (list *spct-p0* *spct-p1* *spct-p2*))
(defconst *spct-r0* (fn-cat-assign (spct-held *spct-w0* 0 nil) nil))
(defconst *spct-r1* (fn-cat-assign (spct-held *spct-w1* 1 nil) (list *spct-r0*)))
(defconst *spct-r2* (fn-cat-assign (spct-held *spct-w2* 2 nil) (list *spct-r0* *spct-r1*)))
(defconst *spct-c* (list *spct-r0* *spct-r1* *spct-r2*))

(defun spct-session (group)
  (fn-nntp-make-session t group nil t))

(defconst *spct-range* (fn-record-string-octets "1-10"))

; The unbounded reader's reply octets, the arm's effects, and the loop.
(defmacro spct-old (session token legacyp)
  `(fn-served-reply-octets
    (cdr (fn-nntp-over-range-cat ,session 3 ,token ,legacyp *spct-a* *spct-c*))))
(defmacro spct-effects (session token legacyp)
  `(cdr (fn-nntp-over-range-ovw ,session 3 ,token ,legacyp nil *spct-c*)))
(defmacro spct-plan (session token legacyp)
  `(fn-splan-of-effects (spct-effects ,session ,token ,legacyp)))
(defmacro spct-drain (session token legacyp w wl n)
  `(fn-splan-cw-drain (spct-plan ,session ,token ,legacyp) ,w ,wl ,n *spct-a* *spct-c*))

;; POSITIVE: the keystone, complete antecedent and conclusion, at (W, WL) =
;; (5, 1) (windows of five octets, one number per quantum), (3, 2) and
;; (1000, 100) (one quantum, one window); the plan starts at a cursor.
(defthm spct-keystone-witness
  (let* ((s (spct-session "fn.test"))
         (old (spct-old s *spct-range* nil)))
    (and (fn-splan-fresh-effectsp (spct-effects s *spct-range* nil))
         (fn-splan-cw-okp (spct-plan s *spct-range* nil))
         (fn-splan-at-cursorp (spct-plan s *spct-range* nil))
         (equal (fn-splan-window-size (spct-plan s *spct-range* nil)) 0)
         (not (fn-splan-donep (spct-plan s *spct-range* nil)))
         (equal (mv-nth 0 (spct-drain s *spct-range* nil 5 1 200)) :ok)
         (fn-splan-donep (mv-nth 2 (spct-drain s *spct-range* nil 5 1 200)))
         (equal (mv-nth 1 (spct-drain s *spct-range* nil 5 1 200)) old)
         (fn-splan-donep (mv-nth 2 (spct-drain s *spct-range* nil 3 2 200)))
         (equal (mv-nth 1 (spct-drain s *spct-range* nil 3 2 200)) old)
         (fn-splan-donep (mv-nth 2 (spct-drain s *spct-range* nil 1000 100 2)))
         (equal (mv-nth 1 (spct-drain s *spct-range* nil 1000 100 2)) old)
         (equal (take 3 old) '(50 50 52))
         (equal (last old) '(10))
         (equal (len (fn-ovw-lines "fn.test" 1 3 nil 3 *spct-a* *spct-c*)) 3)))
  :rule-classes nil)

;; The loop really takes its rounds (the keystone's one hypothesis): after
;; four rounds at (5, 1) the plan is not done, the octets written are a
;; strict prefix of the reply, and the plan still carries a cursor (okp).
(defthm spct-rounds-are-needed
  (let* ((s (spct-session "fn.test"))
         (old (spct-old s *spct-range* nil))
         (r (spct-drain s *spct-range* nil 5 1 4)))
    (and (equal (mv-nth 0 r) :ok)
         (not (fn-splan-donep (mv-nth 2 r)))
         (not (equal (mv-nth 1 r) old))
         (< (len (mv-nth 1 r)) (len old))
         (equal (mv-nth 1 r) (take (len (mv-nth 1 r)) old))
         (fn-splan-cw-okp (mv-nth 2 r))))
  :rule-classes nil)

;; One quantum at WL = 1 of the arm's plan: :ok, the status line and ONE
;; line rendered next, a live cursor kept behind them (the plan is okp and
;; owes the same: fn-splan-cursor-step-keeps-cw-remaining).
(defthm spct-first-quantum
  (let* ((s (spct-session "fn.test"))
         (p (spct-plan s *spct-range* nil))
         (r (fn-splan-cursor-step p 1 *spct-a* *spct-c*)))
    (and (equal (mv-nth 0 r) :ok)
         (not (fn-splan-at-cursorp (mv-nth 1 r)))
         (posp (fn-splan-window-size (mv-nth 1 r)))
         (equal (take 3 (fn-splan-remaining (mv-nth 1 r))) '(50 50 52))
         (fn-splan-cw-okp (mv-nth 1 r))
         (fn-splan-rest-at-cursorp (cdr (fn-splan-rest (mv-nth 1 r))))
         (equal (fn-splan-cw-remaining (mv-nth 1 r) 1 *spct-a* *spct-c*)
                (fn-splan-cw-remaining p 1 *spct-a* *spct-c*))))
  :rule-classes nil)

;; CORRUPTED STATE: a plan whose cursor is not one (never the arm's) is
;; :malformed and left where it is; it is not okp.
(defconst *spct-bad* (fn-splan-of-effects (list (list :reply '(50 50)) (list :over-cursor 5))))

(defthm spct-malformed-cursor-witness
  (and (not (fn-splan-cw-okp *spct-bad*))
       (equal (mv-nth 0 (fn-splan-cursor-step *spct-bad* 1 *spct-a* *spct-c*)) :malformed)
       (equal (mv-nth 1 (fn-splan-cursor-step *spct-bad* 1 *spct-a* *spct-c*)) *spct-bad*))
  :rule-classes nil)

(must-fail-checked
 (defthm spct-malformed-is-not-ok
   (equal (mv-nth 0 (fn-splan-cursor-step *spct-bad* 1 *spct-a* *spct-c*)) :ok)
   :rule-classes nil))

;; MUST-FAIL: a plan at a cursor has no positive window size and is not
;; done (fn-splan-window-size-is-positive-until-done's two conjuncts).
(must-fail-checked
 (defthm spct-cursor-plan-has-no-window
   (posp (fn-splan-window-size (spct-plan (spct-session "fn.test") *spct-range* nil)))
   :rule-classes nil))

(must-fail-checked
 (defthm spct-cursor-plan-is-not-done
   (fn-splan-donep (spct-plan (spct-session "fn.test") *spct-range* nil))
   :rule-classes nil))

;; The quantum ACL2 decides: the constant, or a positive override.
(assert-event (equal (fn-splan-cursor-window nil) *fn-splan-cursor-window*))
(assert-event (equal (fn-splan-cursor-window 0) *fn-splan-cursor-window*))
(assert-event (equal (fn-splan-cursor-window 97) 97))

;; PIPELINED (GPT-6, section 4: one cursor per outstanding response): two
;; range commands outstanding are two cursor effects in stream order -- an
;; OVER of 1-10 and an XOVER of 7-9 (past the group: its 420) -- and the
;; loop drains them to the two unbounded replies, in order, at (5, 1).
(defconst *spct-past* (fn-record-string-octets "7-9"))
(defthm spct-pipelined-cursors-witness
  (let* ((s (spct-session "fn.test"))
         (effects (append (spct-effects s *spct-range* nil) (spct-effects s *spct-past* t)))
         (r (fn-splan-cw-drain (fn-splan-of-effects effects) 5 1 400 *spct-a* *spct-c*)))
    (and (fn-splan-fresh-effectsp effects)
         (equal (len effects) 2)
         (fn-splan-cw-okp (fn-splan-of-effects effects))
         (equal (mv-nth 0 r) :ok)
         (fn-splan-donep (mv-nth 2 r))
         (equal (mv-nth 1 r) (append (spct-old s *spct-range* nil) (spct-old s *spct-past* t)))
         (equal (take 3 (spct-old s *spct-past* t)) '(52 50 48))))
  :rule-classes nil)

;; RESIDUAL RENDERING after four rounds (fn-splan-cw-residual-rendering): the
;; octets written followed by what the continuation owes are the whole reply,
;; though the plan is not done.
(defthm spct-residual-rendering-witness
  (let* ((s (spct-session "fn.test"))
         (r (spct-drain s *spct-range* nil 5 1 4)))
    (and (not (fn-splan-donep (mv-nth 2 r)))
         (equal (append (mv-nth 1 r) (fn-splan-cw-remaining (mv-nth 2 r) 1 *spct-a* *spct-c*))
                (spct-old s *spct-range* nil))))
  :rule-classes nil)

;; THE SERVED ARM (lane served-catalog-live): with an Xref server name -- a
;; configured node's environment -- the arm's cursor is fresh, the plan okp,
;; and the loop writes the SERVED unbounded reader's reply
;; (fn-splan-cw-drain-of-the-arm-is-the-unbounded-reply at a server:
;; fn-splan-arm-reference is fn-nntp-over-range-served-cat), at two (W, WL)
;; pairs; that reply is not the nameless one.
(defconst *spct-server* (fn-record-string-octets "news.example"))
(defthm spct-served-arm-witness
  (let* ((s (spct-session "fn.test"))
         (effects (cdr (fn-nntp-over-range-ovw s 3 *spct-range* nil *spct-server* *spct-c*)))
         (old (fn-served-reply-octets
               (cdr (fn-nntp-over-range-served-cat s 3 *spct-range* nil *spct-server*
                                                   *spct-a* *spct-c*))))
         (r1 (fn-splan-cw-drain (fn-splan-of-effects effects) 5 1 400 *spct-a* *spct-c*))
         (r2 (fn-splan-cw-drain (fn-splan-of-effects effects) 1000 100 2 *spct-a* *spct-c*)))
    (and (natp 3)
         (fn-splan-fresh-effectsp effects)
         (fn-splan-cw-okp (fn-splan-of-effects effects))
         (fn-splan-at-cursorp (fn-splan-of-effects effects))
         (fn-splan-donep (mv-nth 2 r1))
         (equal (mv-nth 1 r1) old)
         (fn-splan-donep (mv-nth 2 r2))
         (equal (mv-nth 1 r2) old)
         (equal (fn-splan-arm-reference s 3 *spct-range* nil *spct-server* *spct-a* *spct-c*)
                (fn-nntp-over-range-served-cat s 3 *spct-range* nil *spct-server*
                                               *spct-a* *spct-c*))
         (not (equal old (spct-old s *spct-range* nil)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-splan-arm-reference))))

;; EMPTY QUANTA LEAVE NOTHING BEHIND (CONVERGE-3 row 44;
;; fn-splan-rest-cursor-step-adds-no-empty-effect).  A cursor over a sparse
;; stretch (numbers 4-60 of a three-article group: no line in any quantum of
;; one number) answers only its next cursor: after twenty empty quanta the
;; plan is still one cursor effect with no effect in front of it, so the work
;; the next at-cursor scan does is the same as at the first.  The legacy step
;; (a reply effect for every quantum, empty or not) left one octet-less effect
;; per empty quantum -- spct-legacy-quanta below -- and breaks the keystone's
;; inequality at the first one.
(defconst *spct-sparse*
  (fn-splan-of-effects (list (fn-ovw-cursor-effect (fn-ovw-cursor "fn.test" 4 60 3 nil t nil)))))

(defun spct-quanta (p wl n fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil :measure (nfix n)))
  (if (zp n)
      p
    (mv-let (status p2) (fn-splan-cursor-step p wl fn-arena fn-cat)
      (declare (ignore status))
      (spct-quanta p2 wl (- n 1) fn-arena fn-cat))))

;; The step as it was: its reply effect is consed even when it holds no octets,
;; and the effects in front of the cursor are kept.
(defun spct-legacy-quantum (rest wl fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil))
  (if (consp rest)
      (if (fn-splan-cursor-effectp (car rest))
          (mv-let (octets next) (fn-ovw-step (car (cdr (car rest))) wl fn-arena fn-cat)
            (cons (fn-nntp-reply-effect octets)
                  (if next (cons (fn-ovw-cursor-effect next) (cdr rest)) (cdr rest))))
        (cons (car rest) (spct-legacy-quantum (cdr rest) wl fn-arena fn-cat)))
    rest))

(defun spct-legacy-quanta (rest wl n fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil :measure (nfix n)))
  (if (zp n)
      rest
    (spct-legacy-quanta (spct-legacy-quantum rest wl fn-arena fn-cat) wl (- n 1) fn-arena fn-cat)))

(defthm spct-empty-quanta-leave-nothing-behind-witness
  (let ((p20 (spct-quanta *spct-sparse* 1 20 *spct-a* *spct-c*))
        (p40 (spct-quanta *spct-sparse* 1 40 *spct-a* *spct-c*)))
    (and (fn-splan-cw-okp *spct-sparse*)
         (fn-splan-at-cursorp *spct-sparse*)
         (equal (fn-splan-empties *spct-sparse*) 0)
         ;; twenty and forty quanta later: the same single cursor effect, the
         ;; next one, with nothing in front of it
         (fn-splan-cw-okp p20)
         (fn-splan-at-cursorp p20)
         (equal (len (fn-splan-rest p20)) 1)
         (equal (fn-splan-empties p20) 0)
         (equal (fn-splan-rest p20)
                (list (fn-ovw-cursor-effect (fn-ovw-cursor "fn.test" 24 60 3 nil t nil))))
         (equal (len (fn-splan-rest p40)) 1)
         (equal (fn-splan-empties p40) 0)
         ;; the keystone's inequality at both
         (<= (fn-splan-empties p20) (fn-splan-empties *spct-sparse*))
         (<= (fn-splan-empties p40) (fn-splan-empties p20))))
  :rule-classes nil)

;; The legacy step's red: twenty empty quanta, twenty octet-less effects (and
;; the rest twenty-one effects long) in front of the cursor.
(defthm spct-legacy-step-accumulates-witness
  (let ((rest (spct-legacy-quanta (fn-splan-rest *spct-sparse*) 1 20 *spct-a* *spct-c*)))
    (and (equal (fn-splan-rest-empties rest) 20)
         (equal (len rest) 21)
         (fn-splan-rest-at-cursorp rest)))
  :rule-classes nil)

;; MUST-FAIL: the keystone's inequality for the legacy step, at the first
;; empty quantum.
(must-fail-checked
 (defthm spct-legacy-step-adds-no-empty-effect
   (<= (fn-splan-rest-empties
        (spct-legacy-quantum (fn-splan-rest *spct-sparse*) 1 *spct-a* *spct-c*))
       (fn-splan-rest-empties (fn-splan-rest *spct-sparse*)))
   :rule-classes nil))

;; A quantum that does find lines still answers them in a reply effect ahead of
;; the next cursor: the one non-empty effect the window renders and consumes.
(defthm spct-nonempty-quantum-keeps-its-reply-witness
  (let* ((p (fn-splan-of-effects (spct-effects (spct-session "fn.test") *spct-range* nil)))
         (r (mv-nth 1 (fn-splan-cursor-step p 1 *spct-a* *spct-c*))))
    (and (equal (len (fn-splan-rest r)) 2)
         (consp (fn-srb-effect-octets (car (fn-splan-rest r))))
         (equal (fn-splan-empties r) 0)
         (fn-splan-rest-at-cursorp (cdr (fn-splan-rest r)))))
  :rule-classes nil)

;; THE QUANTUM'S GUARD IS O(1) (Codex r67 F1; lane served-catalog-live).  With
;; no raw dispatch the counterpart evaluates the host-called entry's guard on
;; every quantum under the owner mutex; these are the guards as the world
;; holds them, stobj recognizers aside: no fact about the whole catalog.  A
;; guard that asks fn-cat-handles-inp again fails here by name.
(assert-event (equal (guard 'fn-splan-cursor-step t (w state)) '(natp w)))
(assert-event (equal (guard 'fn-ovw-step t (w state)) '(fn-ovw-cursorp cur)))
(assert-event (not (member-eq 'fn-cat-handles-inp
                              (all-ffn-symbs (guard 'fn-cat-row-article t (w state)) nil))))
