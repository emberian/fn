; Teeth for books/def-carried.lisp.
;
;   1. A carried invariant over a stobj the world confirms: the row, the
;      trace theorem (fn-cdt-carried-run-carries, its statement pinned, and
;      an instance at a literal trace), the D40 row data, and the
;      `:raw-with (:carried NAME)' declaration definterface resolves from it.
;   2. One refusal per world check, each under must-fail with the check
;      asserted by name: an invariant that is no function or not unary; a
;      transition whose theorem is missing, carries nothing (no hypothesis
;      applying the invariant), concludes another predicate or never calls
;      the transition; an establishing theorem that concludes something
;      else; a bridge with no invariant hypothesis or the wrong conclusion;
;      a bare transition (the obligation owed); a declared host entry that
;      reaches a writer and is unlisted (completeness), including one
;      declared AFTER the row (def-carried-check); `:trace t' on a theorem
;      without the trace shape.
;   3. One refusal per malformed form (fn-cd-refusal).
;   4. The `:raw-with (:carried NAME)' refusals: an establishing point is
;      not a transition; no such carried invariant.

(in-package "ACL2")
(include-book "../../books/def-carried")
(include-book "../../books/definterface")
(include-book "../../books/payload-kinds") ; *fn-entry-guard-kinds*
(include-book "must-fail-checked")

(defstobj fn-cdt-st
  (fn-cdt-n :type integer :initially 0)
  (fn-cdt-log :type t :initially nil))

; The carried relation and a predicate it implies.
(defun fn-cdt-relp (fn-cdt-st)
  (declare (xargs :stobjs fn-cdt-st))
  (< 0 (fn-cdt-n fn-cdt-st)))

(defun fn-cdt-nonzerop (fn-cdt-st)
  (declare (xargs :stobjs fn-cdt-st))
  (not (equal (fn-cdt-n fn-cdt-st) 0)))

; The establishing point, three transitions (one answering a value), and a
; reader that writes nothing.
(defun fn-cdt-open (fn-cdt-st)
  (declare (xargs :stobjs fn-cdt-st))
  (update-fn-cdt-n 1 fn-cdt-st))

(defun fn-cdt-bump (n fn-cdt-st)
  (declare (xargs :stobjs fn-cdt-st :guard (and (natp n) (fn-cdt-relp fn-cdt-st))))
  (update-fn-cdt-n (+ n (fn-cdt-n fn-cdt-st)) fn-cdt-st))

(defun fn-cdt-note (x fn-cdt-st)
  (declare (xargs :stobjs fn-cdt-st :guard (fn-cdt-relp fn-cdt-st)))
  (let ((fn-cdt-st (update-fn-cdt-log (cons x (fn-cdt-log fn-cdt-st)) fn-cdt-st)))
    (mv x fn-cdt-st)))

(defun fn-cdt-reset (fn-cdt-st)
  (declare (xargs :stobjs fn-cdt-st))
  (update-fn-cdt-n 1 fn-cdt-st))

(defun fn-cdt-peek (fn-cdt-st)
  (declare (xargs :stobjs fn-cdt-st))
  (fn-cdt-n fn-cdt-st))

(defthm fn-cdt-open-establishes
  (fn-cdt-relp (fn-cdt-open fn-cdt-st)))

(defthm fn-cdt-bump-carries
  (implies (and (natp n) (fn-cdt-relp fn-cdt-st))
           (fn-cdt-relp (fn-cdt-bump n fn-cdt-st))))

(defthm fn-cdt-note-carries
  (implies (fn-cdt-relp fn-cdt-st)
           (fn-cdt-relp (mv-nth 1 (fn-cdt-note x fn-cdt-st)))))

(defthm fn-cdt-reset-carries
  (implies (fn-cdt-relp fn-cdt-st)
           (fn-cdt-relp (fn-cdt-reset fn-cdt-st))))

(defthm fn-cdt-relp-nonzero
  (implies (fn-cdt-relp fn-cdt-st)
           (fn-cdt-nonzerop fn-cdt-st)))

(defthm fn-cdt-unrelated
  (equal (len (list x)) 1))

; Carries, but not in the trace shape: the call's argument is not a variable.
(defthm fn-cdt-bump-carries-shifted
  (implies (and (natp n) (fn-cdt-relp fn-cdt-st))
           (fn-cdt-relp (fn-cdt-bump (+ 1 n) fn-cdt-st))))

; The host-called entries, declared (the completeness check reads this table).
(definterface fn-cdt-open :class :common-lisp-compliant)
(definterface fn-cdt-bump :class :common-lisp-compliant :kinds ((n natp)))
(definterface fn-cdt-note :class :common-lisp-compliant)
(definterface fn-cdt-reset :class :common-lisp-compliant)
(definterface fn-cdt-peek :class :common-lisp-compliant)

; The reads-only entry is not demanded; the note writes the log, not the
; count, so it is reached from the log's writer alone.
(assert-event
 (equal (fn-cd-reaching-entries (table-alist 'fn-interfaces (w state))
                                '(update-fn-cdt-n) nil (w state))
        '(fn-cdt-reset fn-cdt-bump fn-cdt-open)))
(assert-event
 (equal (fn-cd-reaching-entries (table-alist 'fn-interfaces (w state))
                                '(update-fn-cdt-n update-fn-cdt-log) nil (w state))
        '(fn-cdt-reset fn-cdt-note fn-cdt-bump fn-cdt-open)))

; ---------------------------------------------------------------------------
; 3. Malformed forms.

(must-fail-checked
 (def-carried fn-cdt-x :invariant fn-cdt-relp
   :established ((fn-cdt-open fn-cdt-open-establishes)) :bogus 1)
 :unchecked "def-carried refuses an unknown keyword at expansion")
(must-fail-checked
 (def-carried fn-cdt-x :established ((fn-cdt-open fn-cdt-open-establishes)))
 :unchecked "def-carried refuses a form with no :invariant")
(must-fail-checked
 (def-carried fn-cdt-x :invariant fn-cdt-relp)
 :unchecked "def-carried refuses a form with no establishing point")
(must-fail-checked
 (def-carried fn-cdt-x :invariant fn-cdt-relp
   :established ((fn-cdt-open fn-cdt-open-establishes))
   :transitions ((fn-cdt-bump)))
 :unchecked "def-carried refuses a transition entry that is neither FN nor (FN THM)")
(assert-event
 (equal (fn-cd-refusal 'fn-cdt-x '(:invariant fn-cdt-relp
                                   :established ((fn-cdt-open fn-cdt-open-establishes))
                                   :trace :maybe))
        '(:bad-trace :maybe)))
(assert-event
 (equal (fn-cd-refusal 'fn-cdt-x '(:invariant fn-cdt-relp
                                   :established ((fn-cdt-open fn-cdt-open-establishes))
                                   :concludes (fn-cdt-nonzerop)))
        '(:bad-concludes (fn-cdt-nonzerop))))

; ---------------------------------------------------------------------------
; 2. World refusals.  Each: the problem asserted by the check's words, then
; the form under must-fail.

; WORDS is searched in the msg's raw format string (a `~'-newline
; continuation is not joined there), so a phrase never straddles one.
(defmacro fn-cdt-problem-says (words kvs)
  `(assert-event
    (let ((problem (fn-cd-problem 'fn-cdt-x ',kvs (w state))))
      (and problem (search ,words (car problem)) t))))

(fn-cdt-problem-says "is not a function in this world"
 (:invariant fn-cdt-nope :established ((fn-cdt-open fn-cdt-open-establishes))))
(must-fail-checked
 (def-carried fn-cdt-x :invariant fn-cdt-nope
   :established ((fn-cdt-open fn-cdt-open-establishes)))
 :unchecked "the invariant is no function")

(fn-cdt-problem-says "of one formal"
 (:invariant fn-cdt-bump :established ((fn-cdt-open fn-cdt-open-establishes))))
(must-fail-checked
 (def-carried fn-cdt-x :invariant fn-cdt-bump
   :established ((fn-cdt-open fn-cdt-open-establishes)))
 :unchecked "the invariant is not unary")

(fn-cdt-problem-says "is not a theorem in this world"
 (:invariant fn-cdt-relp :established ((fn-cdt-open fn-cdt-open-establishes))
  :transitions ((fn-cdt-bump fn-cdt-no-such-theorem))))
(must-fail-checked
 (def-carried fn-cdt-x :invariant fn-cdt-relp
   :established ((fn-cdt-open fn-cdt-open-establishes))
   :transitions ((fn-cdt-bump fn-cdt-no-such-theorem)))
 :unchecked "the transition's theorem is not in the world")

(fn-cdt-problem-says "no hypothesis applying"
 (:invariant fn-cdt-relp :established ((fn-cdt-open fn-cdt-open-establishes))
  :transitions ((fn-cdt-bump fn-cdt-open-establishes))))
(must-fail-checked
 (def-carried fn-cdt-x :invariant fn-cdt-relp
   :established ((fn-cdt-open fn-cdt-open-establishes))
   :transitions ((fn-cdt-bump fn-cdt-open-establishes)))
 :unchecked "an establishing theorem carries nothing across a transition")

(fn-cdt-problem-says "does not conclude"
 (:invariant fn-cdt-relp :established ((fn-cdt-open fn-cdt-open-establishes))
  :transitions ((fn-cdt-bump fn-cdt-relp-nonzero))))
(must-fail-checked
 (def-carried fn-cdt-x :invariant fn-cdt-relp
   :established ((fn-cdt-open fn-cdt-open-establishes))
   :transitions ((fn-cdt-bump fn-cdt-relp-nonzero)))
 :unchecked "the transition's theorem concludes another predicate")

(fn-cdt-problem-says "never calls"
 (:invariant fn-cdt-relp :established ((fn-cdt-open fn-cdt-open-establishes))
  :transitions ((fn-cdt-bump fn-cdt-reset-carries))))
(must-fail-checked
 (def-carried fn-cdt-x :invariant fn-cdt-relp
   :established ((fn-cdt-open fn-cdt-open-establishes))
   :transitions ((fn-cdt-bump fn-cdt-reset-carries)))
 :unchecked "the transition's theorem is about another transition")

(fn-cdt-problem-says "establishing point"
 (:invariant fn-cdt-relp :established ((fn-cdt-open fn-cdt-unrelated))))
(must-fail-checked
 (def-carried fn-cdt-x :invariant fn-cdt-relp
   :established ((fn-cdt-open fn-cdt-unrelated)))
 :unchecked "the establishing theorem concludes something else")

(fn-cdt-problem-says "consequence of the carried invariant"
 (:invariant fn-cdt-relp :established ((fn-cdt-open fn-cdt-open-establishes))
  :concludes ((fn-cdt-nonzerop fn-cdt-open-establishes))))
(must-fail-checked
 (def-carried fn-cdt-x :invariant fn-cdt-relp
   :established ((fn-cdt-open fn-cdt-open-establishes))
   :concludes ((fn-cdt-nonzerop fn-cdt-open-establishes)))
 :unchecked "the bridge has no invariant hypothesis")

(fn-cdt-problem-says "does not conclude"
 (:invariant fn-cdt-relp :established ((fn-cdt-open fn-cdt-open-establishes))
  :concludes ((fn-cdt-peek fn-cdt-relp-nonzero))))
(must-fail-checked
 (def-carried fn-cdt-x :invariant fn-cdt-relp
   :established ((fn-cdt-open fn-cdt-open-establishes))
   :concludes ((fn-cdt-peek fn-cdt-relp-nonzero)))
 :unchecked "the bridge concludes another predicate")

; The obligation owed: a bare transition, refused with the statement.
(fn-cdt-problem-says "has no preservation theorem"
 (:invariant fn-cdt-relp :established ((fn-cdt-open fn-cdt-open-establishes))
  :transitions ((fn-cdt-bump fn-cdt-bump-carries) fn-cdt-reset)))
(must-fail-checked
 (def-carried fn-cdt-x :invariant fn-cdt-relp
   :established ((fn-cdt-open fn-cdt-open-establishes))
   :transitions ((fn-cdt-bump fn-cdt-bump-carries) fn-cdt-reset))
 :unchecked "a transition with no theorem is an obligation owed")

; Completeness: fn-cdt-reset is declared, reaches the writer and is unlisted.
(fn-cdt-problem-says "reaches a writer"
 (:invariant fn-cdt-relp :established ((fn-cdt-open fn-cdt-open-establishes))
  :transitions ((fn-cdt-bump fn-cdt-bump-carries) (fn-cdt-note fn-cdt-note-carries))
  :writers (update-fn-cdt-n update-fn-cdt-log)))
(assert-event
 (eq (cdr (assoc #\0 (cdr (fn-cd-problem
                           'fn-cdt-x
                           '(:invariant fn-cdt-relp
                             :established ((fn-cdt-open fn-cdt-open-establishes))
                             :transitions ((fn-cdt-bump fn-cdt-bump-carries)
                                           (fn-cdt-note fn-cdt-note-carries))
                             :writers (update-fn-cdt-n update-fn-cdt-log))
                           (w state)))))
     'fn-cdt-reset))
(must-fail-checked
 (def-carried fn-cdt-x :invariant fn-cdt-relp
   :established ((fn-cdt-open fn-cdt-open-establishes))
   :transitions ((fn-cdt-bump fn-cdt-bump-carries) (fn-cdt-note fn-cdt-note-carries))
   :writers (update-fn-cdt-n update-fn-cdt-log))
 :unchecked "a declared entry that writes the carried state and is unlisted")

; :trace t demands the shape.
(fn-cdt-problem-says "has not the trace"
 (:invariant fn-cdt-relp :established ((fn-cdt-open fn-cdt-open-establishes))
  :transitions ((fn-cdt-bump fn-cdt-bump-carries-shifted)) :trace t))
(must-fail-checked
 (def-carried fn-cdt-x :invariant fn-cdt-relp
   :established ((fn-cdt-open fn-cdt-open-establishes))
   :transitions ((fn-cdt-bump fn-cdt-bump-carries-shifted)) :trace t)
 :unchecked ":trace t on a theorem without the trace shape")

; ---------------------------------------------------------------------------
; 1. Accepted.

(def-carried fn-cdt-carried
  :invariant fn-cdt-relp
  :established ((fn-cdt-open fn-cdt-open-establishes))
  :transitions ((fn-cdt-bump fn-cdt-bump-carries)
                (fn-cdt-note fn-cdt-note-carries)
                (fn-cdt-reset fn-cdt-reset-carries))
  :concludes ((fn-cdt-nonzerop fn-cdt-relp-nonzero))
  :writers (update-fn-cdt-n update-fn-cdt-log)
  :trace t)

(assert-event
 (equal (cdr (assoc-eq 'fn-cdt-carried (table-alist 'fn-carried (w state))))
        '(:invariant fn-cdt-relp
          :established ((fn-cdt-open fn-cdt-open-establishes))
          :transitions ((fn-cdt-bump fn-cdt-bump-carries)
                        (fn-cdt-note fn-cdt-note-carries)
                        (fn-cdt-reset fn-cdt-reset-carries))
          :concludes ((fn-cdt-nonzerop fn-cdt-relp-nonzero))
          :writers (update-fn-cdt-n update-fn-cdt-log)
          :trace t)))

; The trace theorem, its statement pinned.
(assert-event
 (equal (getpropc 'fn-cdt-carried-run-carries 'theorem nil (w state))
        '(implies (if (fn-cdt-relp s) (fn-cdt-carried-run-okp s es) 'nil)
                  (fn-cdt-relp (fn-cdt-carried-run s es)))))

; Its instance at a literal trace: bump by 3, note x, reset.
(defthm fn-cdt-trace-witness
  (implies (fn-cdt-relp s)
           (fn-cdt-relp (fn-cdt-carried-run
                         s '((fn-cdt-bump 3) (fn-cdt-note x) (fn-cdt-reset)))))
  :hints (("Goal" :use ((:instance fn-cdt-carried-run-carries
                                   (es '((fn-cdt-bump 3) (fn-cdt-note x) (fn-cdt-reset)))))
           :in-theory (e/d (fn-cdt-carried-run-okp fn-cdt-carried-okp)
                           (fn-cdt-carried-run-carries fn-cdt-carried-run)))))

; The D40 row data.
(assert-event
 (equal (fn-cd-raw-with 'fn-cdt-carried 'fn-cdt-bump (w state))
        '(fn-cdt-relp-nonzero fn-cdt-open-establishes fn-cdt-bump-carries)))
(assert-event (null (fn-cd-raw-with 'fn-cdt-carried 'fn-cdt-open (w state))))
(assert-event (null (fn-cd-raw-with 'fn-cdt-carried 'fn-cdt-peek (w state))))
(assert-event (null (fn-cd-raw-with 'fn-cdt-nope 'fn-cdt-bump (w state))))

(def-carried-check fn-cdt-carried)
(must-fail-checked (def-carried-check fn-cdt-nope)
                   :unchecked "no such carried invariant")

; Accepted without the trace: a carrying theorem outside the shape leaves the
; row with :trace nil and no trace theorem.
(def-carried fn-cdt-carried-plain
  :invariant fn-cdt-relp
  :established ((fn-cdt-open fn-cdt-open-establishes))
  :transitions ((fn-cdt-bump fn-cdt-bump-carries-shifted)
                (fn-cdt-note fn-cdt-note-carries)
                (fn-cdt-reset fn-cdt-reset-carries))
  :writers (update-fn-cdt-n update-fn-cdt-log))
(assert-event
 (null (fn-cd-get :trace (cdr (assoc-eq 'fn-cdt-carried-plain
                                        (table-alist 'fn-carried (w state)))))))
(assert-event
 (null (getpropc 'fn-cdt-carried-plain-run-carries 'theorem nil (w state))))

; ---------------------------------------------------------------------------
; 4. definterface's `:raw-with (:carried NAME)': the D40 checker over the
; resolved theorems (the bridge, the open, the entry's own preservation).

(definterface fn-cdt-bump
  :class :common-lisp-compliant
  :kinds ((n natp))
  :raw-with (:carried fn-cdt-carried))
(definterface fn-cdt-note
  :class :common-lisp-compliant
  :raw-with (:carried fn-cdt-carried))

(assert-event
 (equal (cdr (assoc-eq 'fn-cdt-bump (table-alist 'fn-interfaces (w state))))
        '(:class :common-lisp-compliant :kinds ((n natp))
          :raw-with (:carried fn-cdt-carried))))
(assert-event
 (equal (fn-di-raw-with-theorems 'fn-cdt-bump
                                 '(:raw-with (:carried fn-cdt-carried)) (w state))
        '(fn-cdt-relp-nonzero fn-cdt-open-establishes fn-cdt-bump-carries)))

; Refused: an establishing point is not a transition of the invariant.
(assert-event
 (fn-di-problem 'fn-cdt-open '(:class :common-lisp-compliant
                               :raw-with (:carried fn-cdt-carried)) (w state)))
(must-fail-checked
 (definterface fn-cdt-open :class :common-lisp-compliant
   :raw-with (:carried fn-cdt-carried))
 :unchecked "fn-cdt-open establishes the invariant; it is not a transition")

; Refused: no such carried invariant.
(assert-event
 (fn-di-problem 'fn-cdt-bump '(:class :common-lisp-compliant :kinds ((n natp))
                               :raw-with (:carried fn-cdt-nope)) (w state)))
(must-fail-checked
 (definterface fn-cdt-bump :class :common-lisp-compliant :kinds ((n natp))
   :raw-with (:carried fn-cdt-nope))
 :unchecked "no carried invariant fn-cdt-nope in this world")

; Completeness bites after the row: a writer-reaching entry declared later.
(defun fn-cdt-zap (fn-cdt-st)
  (declare (xargs :stobjs fn-cdt-st))
  (update-fn-cdt-n 0 fn-cdt-st))
(definterface fn-cdt-zap :class :common-lisp-compliant)
(assert-event
 (eq (cdr (assoc #\0 (cdr (fn-cd-problem
                           'fn-cdt-carried
                           (cdr (assoc-eq 'fn-cdt-carried
                                          (table-alist 'fn-carried (w state))))
                           (w state)))))
     'fn-cdt-zap))
(must-fail-checked (def-carried-check fn-cdt-carried)
                   :unchecked "fn-cdt-zap writes the carried state and has no theorem")
