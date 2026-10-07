; Teeth for books/decision-trace.lisp and the `:trace' clause of
; books/definterface.lisp (lane obs-decision-trace; keystones DT-1, DT-2).
;
;   1. Accepted declarations over fixture entries, and what they register: the
;      table fn-dtrace-points, DT-1 (NAME-dtrace-keeps-the-decision) and its
;      companion (NAME-dtrace-outcome-is-a-record), stated as the clause
;      says.
;   2. The hypothesis-removal witness for DT-1: the recordp hypotheses are
;      needed, shown by a ground pair of results the projection does not tell
;      apart and whose decisions differ.
;   3. One refusal per check, each by name: a collapsing projection (the
;      mutation the program names: :refused and :busy to one word), a :value
;      on an octet formal (a secret kind), on a list (unbounded) and on a
;      kindless formal, a :length on a kindless formal, a stobj formal, a
;      :digest on a non-stobj formal, an input that is no formal, a duplicate
;      input, nine inputs, an outcome that is not guard-verified or whose
;      guard is not T or that is no function, a decision that is the
;      outcome, witnesses that are unbounded, and a malformed clause.
;   4. The generated dispatch: `fn-dtrace-define-project' builds the one entry
;      the host calls, and its rows are rows.
;   5. The plan: `fn-dtrace-admit', `fn-dtrace-ring-octets', `fn-dtrace-verb'.

(in-package "ACL2")
(include-book "../../books/definterface")
(include-book "../../books/payload-kinds") ; *fn-entry-guard-kinds*
(include-book "../../books/decision-trace")
(include-book "must-fail-checked")

; ---------------------------------------------------------------------------
; Fixtures.

(defun fn-dtt-verdict (n)
  ; the decision: :ok, :busy or :refused
  (declare (xargs :guard (natp n)))
  (cond ((equal n 0) :ok) ((equal n 1) :busy) (t :refused)))

(defun fn-dtt-octets (octets)
  (declare (xargs :guard (fn-cbor-octet-listp octets)))
  (if (consp octets) :some :empty))

(defun fn-dtt-list (xs)
  (declare (xargs :guard (true-listp xs)))
  (len xs))

(defun fn-dtt-sched (s)
  ; a state-like argument with no kind, whose sequence number is its car
  (declare (xargs :guard t))
  (if (consp s) :busy :idle))

(defun fn-dtt-seq (s)
  (declare (xargs :guard t))
  (if (consp s) (nfix (car s)) 0))

(defun fn-dtt-step (s kind reading)
  ; (mv word s') as an entry returns it: the values are (word s')
  (declare (xargs :guard (and (symbolp kind) (natp reading)))
           (ignorable kind))
  (mv (if (< reading 5) :ok :late) (cons reading s)))

(defun fn-dtt-wide (a b c d e f g h i)
  (declare (xargs :guard (and (natp a) (natp b) (natp c) (natp d) (natp e) (natp f)
                              (natp g) (natp h) (natp i))))
  (+ a b c d e f g h i))

(defstobj fn-dtt-st (fn-dtt-fld :type integer :initially 0))

(defun fn-dtt-read (fn-dtt-st)
  (declare (xargs :stobjs fn-dtt-st))
  (fn-dtt-fld fn-dtt-st))

; outcome projections, good and bad
(defun fn-dtt-collapse (vals)
  ; refused and busy to one word: the mutation DT-1 refuses by name
  (declare (xargs :guard t))
  (if (member-eq (fn-dtrace-v0 vals) '(:refused :busy)) :no (fn-dtrace-v0-clip vals)))

(defun fn-dtt-whole (vals)
  ; the values themselves: not a record when a value is a long list
  (declare (xargs :guard t))
  vals)

(defun fn-dtt-guarded (vals)
  (declare (xargs :guard (consp vals)))
  (fn-dtrace-clip (car vals)))

(defun fn-dtt-program (vals)
  (declare (xargs :mode :program))
  (fn-dtrace-clip (car vals)))

(defun fn-dtt-two (a b)
  (declare (xargs :guard t))
  (list a b))

; ---------------------------------------------------------------------------
; 1. Accepted.

(definterface fn-dtt-verdict
  :class :common-lisp-compliant
  :kinds ((n natp))
  :trace (:class :verdict
          :inputs ((n :value))
          :outcome fn-dtrace-v0-clip
          :decision fn-dtrace-v0
          :witnesses ((:ok) (:busy) (:refused))))

(definterface fn-dtt-octets
  :class :common-lisp-compliant
  :kinds ((octets fn-cbor-octet-listp))
  :trace (:class :refusal
          :inputs ((octets :length))
          :outcome fn-dtrace-v0-clip
          :decision fn-dtrace-v0
          :witnesses ((:some) (:empty))))

(definterface fn-dtt-sched
  :class :common-lisp-compliant
  :trace (:class :schedule
          :inputs ((s (:with fn-dtt-seq)))
          :outcome fn-dtrace-v0-clip
          :decision fn-dtrace-v0
          :witnesses ((:busy) (:idle))))

; An entry that returns (word s'): the decision is the first value, the
; second (the scheduling state) is not recorded.
(definterface fn-dtt-step
  :class :common-lisp-compliant
  :kinds ((kind symbolp) (reading natp))
  :trace (:class :plan
          :inputs ((s (:with fn-dtt-seq)) (kind :value) (reading :value))
          :outcome fn-dtrace-v0-clip
          :decision fn-dtrace-v0
          :witnesses ((:ok (5)) (:late (9 5)))))

(definterface fn-dtt-read
  :class :common-lisp-compliant
  :trace (:class :tariff
          :inputs ((fn-dtt-st :redact))
          :outcome fn-dtrace-v0-clip
          :decision fn-dtrace-v0
          :witnesses ((0) (7))))

(assert-event
 (equal (cdr (assoc-eq 'fn-dtt-verdict (table-alist 'fn-dtrace-points (w state))))
        '(:class :verdict :inputs ((n :value)) :positions (0) :projs (:value)
          :outcome fn-dtrace-v0-clip :decision fn-dtrace-v0 :stobjs-out (nil))))

(assert-event
 (equal (cdr (assoc-eq 'fn-dtt-step (table-alist 'fn-dtrace-points (w state))))
        '(:class :plan :inputs ((s (:with fn-dtt-seq)) (kind :value) (reading :value))
          :positions (0 1 2) :projs ((:with fn-dtt-seq) :value :value)
          :outcome fn-dtrace-v0-clip :decision fn-dtrace-v0 :stobjs-out (nil nil))))

; a :redact formal is named in the row but never passed
(assert-event
 (equal (cdr (assoc-eq 'fn-dtt-read (table-alist 'fn-dtrace-points (w state))))
        '(:class :tariff :inputs ((fn-dtt-st :redact)) :positions () :projs ()
          :outcome fn-dtrace-v0-clip :decision fn-dtrace-v0 :stobjs-out (nil))))

; The fn-interfaces row keeps the declaration, trace and all.
(assert-event
 (equal (fn-di-get :trace (cdr (assoc-eq 'fn-dtt-verdict (table-alist 'fn-interfaces (w state)))))
        '(:class :verdict :inputs ((n :value)) :outcome fn-dtrace-v0-clip
          :decision fn-dtrace-v0 :witnesses ((:ok) (:busy) (:refused)))))

; DT-1 as generated: stated as the clause says, not about another function.
(assert-event
 (equal (getpropc 'fn-dtt-verdict-dtrace-keeps-the-decision 'theorem nil (w state))
        '(implies (if (fn-dtrace-recordp (fn-dtrace-v0 a))
                      (if (fn-dtrace-recordp (fn-dtrace-v0 b))
                          (equal (fn-dtrace-v0-clip a) (fn-dtrace-v0-clip b))
                        'nil)
                    'nil)
                  (equal (fn-dtrace-v0 a) (fn-dtrace-v0 b)))))

(assert-event
 (equal (getpropc 'fn-dtt-verdict-dtrace-outcome-is-a-record 'theorem nil (w state))
        '(fn-dtrace-recordp (fn-dtrace-v0-clip vals))))

; ---------------------------------------------------------------------------
; 2. The hypothesis-removal witness.  The recordp hypotheses of DT-1 are
; needed: two results with long-list decisions are told apart by nothing (both
; are :unbounded) while their decisions differ, so the conclusion fails for
; them -- and the hypothesis they fail is exactly "the decision part is a
; record", which the declared witnesses show holds of what the entry returns.
(assert-event
 (let ((a '((1 2 3 4 5 6 7 8 9))) (b '((9 8 7 6 5 4 3 2 1))))
   (and (not (fn-dtrace-recordp (fn-dtrace-v0 a)))
        (not (fn-dtrace-recordp (fn-dtrace-v0 b)))
        (equal (fn-dtrace-v0-clip a) (fn-dtrace-v0-clip b))
        (not (equal (fn-dtrace-v0 a) (fn-dtrace-v0 b))))))

; ... and the same pair is what the admission refuses by name when it is
; declared as the entry's witnesses, with the decision itself unbounded.
(assert-event
 (equal (car (fn-di-trace-refusal
              'fn-dtt-verdict
              '(:class :verdict :inputs ((n :value)) :outcome fn-dtrace-v0-clip
                :decision fn-dtrace-v0 :witnesses (((1 2 3 4 5 6 7 8 9))))
              state))
        :decision-unbounded))

; ---------------------------------------------------------------------------
; 3. The world refutes, each by name.

; THE MUTATION THE PROGRAM NAMES: a projection that maps :refused and :busy to
; one word is refused at admission, by name, with the two results it confuses.
(assert-event
 (equal (fn-di-trace-refusal
         'fn-dtt-verdict
         '(:class :verdict :inputs ((n :value)) :outcome fn-dtt-collapse
           :decision fn-dtrace-v0 :witnesses ((:ok) (:busy) (:refused)))
         state)
        '(:collapsing-projection (:busy) (:refused) :no)))

(must-fail-checked
 (definterface fn-dtt-verdict :class :common-lisp-compliant :kinds ((n natp))
   :trace (:class :verdict :inputs ((n :value)) :outcome fn-dtt-collapse
           :decision fn-dtrace-v0 :witnesses ((:ok) (:busy) (:refused))))
 :unchecked "definterface's refusal is its claim; the assert-event above names the check")

; DT-2's mutation: a :value on an octet-list formal.
(assert-event
 (equal (fn-di-trace-refusal
         'fn-dtt-octets
         '(:class :refusal :inputs ((octets :value)) :outcome fn-dtrace-v0-clip
           :decision fn-dtrace-v0 :witnesses ((:some) (:empty)))
         state)
        '(:secret-formal octets fn-cbor-octet-listp :value)))
(must-fail-checked
 (definterface fn-dtt-octets :class :common-lisp-compliant
   :kinds ((octets fn-cbor-octet-listp))
   :trace (:class :refusal :inputs ((octets :value)) :outcome fn-dtrace-v0-clip
           :decision fn-dtrace-v0 :witnesses ((:some) (:empty))))
 :unchecked "definterface's refusal is its claim; the assert-event above names the check")

; ... nor a :digest nor a (:with FN): a secret formal admits :redact or :length.
(assert-event
 (equal (car (fn-di-trace-refusal
              'fn-dtt-octets
              '(:class :refusal :inputs ((octets (:with fn-dtt-seq))) :outcome fn-dtrace-v0-clip
                :decision fn-dtrace-v0 :witnesses ((:some) (:empty)))
              state))
        :secret-formal))

; a :value on a list (an unbounded kind that is not secret)
(assert-event
 (equal (fn-di-trace-refusal
         'fn-dtt-list
         '(:class :verdict :inputs ((xs :value)) :outcome fn-dtrace-v0-clip
           :decision fn-dtrace-v0 :witnesses ((0)))
         state)
        '(:value-on-unbounded-formal xs true-listp)))

; a :value on a formal with no kind at all: nothing bounds it
(assert-event
 (equal (fn-di-trace-refusal
         'fn-dtt-sched
         '(:class :verdict :inputs ((s :value)) :outcome fn-dtrace-v0-clip
           :decision fn-dtrace-v0 :witnesses ((:busy)))
         state)
        '(:value-on-unbounded-formal s nil)))

; a :length on a formal with no kind
(assert-event
 (equal (fn-di-trace-refusal
         'fn-dtt-sched
         '(:class :verdict :inputs ((s :length)) :outcome fn-dtrace-v0-clip
           :decision fn-dtrace-v0 :witnesses ((:busy)))
         state)
        '(:length-on-unbounded-formal s nil)))

; a stobj formal: only :redact
(assert-event
 (equal (fn-di-trace-refusal
         'fn-dtt-read
         '(:class :verdict :inputs ((fn-dtt-st :value)) :outcome fn-dtrace-v0-clip
           :decision fn-dtrace-v0 :witnesses ((0)))
         state)
        '(:stobj-formal fn-dtt-st fn-dtt-st :value)))

; a :digest of a formal that is not an octets stobj
(assert-event
 (equal (fn-di-trace-refusal
         'fn-dtt-verdict
         '(:class :verdict :inputs ((n :digest)) :outcome fn-dtrace-v0-clip
           :decision fn-dtrace-v0 :witnesses ((:ok)))
         state)
        '(:digest-needs-an-octets-stobj n)))

; an input that is no formal; the same input twice; nine inputs
(assert-event
 (equal (fn-di-trace-refusal
         'fn-dtt-verdict
         '(:class :verdict :inputs ((m :value)) :outcome fn-dtrace-v0-clip
           :decision fn-dtrace-v0 :witnesses ((:ok)))
         state)
        '(:no-such-formal m)))
(assert-event
 (equal (fn-di-trace-refusal
         'fn-dtt-verdict
         '(:class :verdict :inputs ((n :value) (n :redact)) :outcome fn-dtrace-v0-clip
           :decision fn-dtrace-v0 :witnesses ((:ok)))
         state)
        '(:duplicate-input n)))
(assert-event
 (equal (fn-di-trace-refusal
         'fn-dtt-wide
         '(:class :verdict
           :inputs ((a :value) (b :value) (c :value) (d :value) (e :value)
                    (f :value) (g :value) (h :value) (i :value))
           :outcome fn-dtrace-v0-clip :decision fn-dtrace-v0 :witnesses ((0)))
         state)
        '(:too-many-inputs 9)))
; a declaration with no refusal is admitted by the checks
(assert-event
 (null (fn-di-trace-refusal
        'fn-dtt-verdict
        '(:class :verdict :inputs ((n :value)) :outcome fn-dtrace-v0-clip
          :decision fn-dtrace-v0 :witnesses ((:ok) (:busy)))
        state)))

; the functions the declaration names
(assert-event
 (equal (fn-di-trace-refusal
         'fn-dtt-verdict
         '(:class :verdict :inputs ((n :value)) :outcome fn-dtt-program
           :decision fn-dtrace-v0 :witnesses ((:ok)))
         state)
        '(:not-guard-verified :outcome fn-dtt-program)))
(assert-event
 (equal (fn-di-trace-refusal
         'fn-dtt-verdict
         '(:class :verdict :inputs ((n :value)) :outcome fn-dtt-guarded
           :decision fn-dtrace-v0 :witnesses ((:ok)))
         state)
        '(:guard-is-not-t :outcome fn-dtt-guarded)))
(assert-event
 (equal (fn-di-trace-refusal
         'fn-dtt-verdict
         '(:class :verdict :inputs ((n :value)) :outcome fn-dtt-no-such-function
           :decision fn-dtrace-v0 :witnesses ((:ok)))
         state)
        '(:not-a-function :outcome fn-dtt-no-such-function)))
(assert-event
 (equal (fn-di-trace-refusal
         'fn-dtt-verdict
         '(:class :verdict :inputs ((n :value)) :outcome fn-dtt-two
           :decision fn-dtrace-v0 :witnesses ((:ok)))
         state)
        '(:not-a-function-of-the-values :outcome fn-dtt-two)))
; the decision may not be the outcome: DT-1 would then be P -> P
(assert-event
 (equal (fn-di-trace-refusal
         'fn-dtt-verdict
         '(:class :verdict :inputs ((n :value)) :outcome fn-dtrace-v0-clip
           :decision fn-dtrace-v0-clip :witnesses ((:ok)))
         state)
        '(:decision-is-the-outcome fn-dtrace-v0-clip)))

; witnesses: an outcome that is not a record; a witness that is no values list
(assert-event
 (equal (fn-di-trace-refusal
         'fn-dtt-verdict
         '(:class :verdict :inputs ((n :value)) :outcome fn-dtt-whole
           :decision fn-dtrace-v0 :witnesses (((1 2 3 4 5 6 7 8 9))))
         state)
        '(:outcome-unbounded ((1 2 3 4 5 6 7 8 9)))))
(assert-event
 (equal (fn-di-trace-refusal
         'fn-dtt-verdict
         '(:class :verdict :inputs ((n :value)) :outcome fn-dtrace-v0-clip
           :decision fn-dtrace-v0 :witnesses (5))
         state)
        '(:witness-is-not-a-values-list 5)))

(must-fail-checked
 (definterface fn-dtt-verdict :class :common-lisp-compliant :kinds ((n natp))
   :trace (:class :verdict :inputs ((n :value)) :outcome fn-dtt-whole
           :decision fn-dtrace-v0 :witnesses (((1 2 3 4 5 6 7 8 9)))))
 :unchecked "definterface's refusal is its claim; the assert-event above names the check")

; a malformed clause (fn-di-refusal)
(assert-event
 (equal (car (fn-di-refusal
              'fn-dtt-verdict
              '(:class :common-lisp-compliant :kinds ((n natp))
                :trace (:class :elsewhere :inputs ((n :value)) :outcome fn-dtrace-v0-clip
                        :decision fn-dtrace-v0 :witnesses ((:ok))))))
        :bad-trace))
(assert-event
 (equal (car (fn-di-refusal
              'fn-dtt-verdict
              '(:class :common-lisp-compliant :kinds ((n natp))
                :trace (:class :verdict :inputs ((n :everything)) :outcome fn-dtrace-v0-clip
                        :decision fn-dtrace-v0 :witnesses ((:ok))))))
        :bad-trace))
(assert-event
 (equal (car (fn-di-refusal
              'fn-dtt-verdict
              '(:class :common-lisp-compliant :kinds ((n natp))
                :trace (:class :verdict :inputs ((n :value)) :outcome fn-dtrace-v0-clip
                        :decision fn-dtrace-v0 :witnesses nil))))
        :bad-trace))
(must-fail-checked
 (definterface fn-dtt-verdict :class :common-lisp-compliant :kinds ((n natp))
   :trace (:class :elsewhere :inputs ((n :value)) :outcome fn-dtrace-v0-clip
           :decision fn-dtrace-v0 :witnesses ((:ok))))
 :unchecked "definterface's refusal is its claim; the assert-event above names the check")

; ---------------------------------------------------------------------------
; 4. The generated dispatch.

(fn-dtrace-define-project)

(assert-event
 (equal (fn-dtrace-project 'fn-dtt-verdict '(1) '(:busy))
        '(fn-dtt-verdict (1) :busy)))
(assert-event
 (equal (fn-dtrace-project 'fn-dtt-octets '((7 8 9)) '(:some))
        '(fn-dtt-octets (3) :some)))
; the (:with FN) input is FN's value, taken of the argument, not the argument
(assert-event
 (equal (fn-dtrace-project 'fn-dtt-sched '((7 8 9)) '(:busy))
        '(fn-dtt-sched (7) :busy)))
; three inputs, the first through FN; the second value (s') is not recorded
(assert-event
 (equal (fn-dtrace-project 'fn-dtt-step '((4) :late 9) '(:late (9 4)))
        '(fn-dtt-step (4 :late 9) :late)))
; a redacted input is named and hidden
(assert-event
 (equal (fn-dtrace-project 'fn-dtt-read nil '(7))
        '(fn-dtt-read (:redacted) 7)))
; a point the table does not hold is no row of an entry
(assert-event
 (equal (fn-dtrace-project 'fn-dtt-nothing '(1) '(:busy))
        '(:unknown-point nil nil)))
; an argument that does not fit is :unbounded, never truncated
(assert-event
 (equal (fn-dtrace-project 'fn-dtt-verdict '(18446744073709551616) '(:ok))
        '(fn-dtt-verdict (:unbounded) :ok)))
(assert-event
 (equal (fn-dtrace-project 'fn-dtt-verdict '(1) '((1 2 3 4 5 6 7 8 9)))
        '(fn-dtt-verdict (1) :unbounded)))
(assert-event
 (and (fn-dtrace-rowp (fn-dtrace-project 'fn-dtt-step '((4) :late 9) '(:late (9 4))))
      (fn-dtrace-rowp (fn-dtrace-project 'fn-dtt-verdict '(1) '((1 2 3 4 5 6 7 8 9))))
      (fn-dtrace-rowp (fn-dtrace-project 'fn-dtt-nothing nil nil))))

; the theorem the registry's definterface names
(assert-event
 (equal (getpropc 'fn-dtrace-project-is-a-row 'theorem nil (w state))
        '(fn-dtrace-rowp (fn-dtrace-project point args vals))))

; ---------------------------------------------------------------------------
; 5. The plan.  The statements are theorems in the book; here the same
; witnesses are checked through the book's own functions as values, so that a
; change of the book that keeps its theorems but moves a default is seen.

(assert-event (equal (fn-dtrace-admit nil :production) '(:off)))
(assert-event (equal (fn-dtrace-ring-octets '(:off)) 0))
(assert-event (equal (fn-dtrace-ring-octets (fn-dtrace-admit '(nil 8 nil nil nil) :production))
                     (+ 4096 (* 1024 8))))
(assert-event (equal (fn-dtrace-admit '(nil 0 nil nil nil) :production) '(:refused :capacity)))
(assert-event (equal (fn-dtrace-admit '(nil nil nil :isolated-process nil) :production)
                     '(:refused :isolated-allocation-needs-developer-image)))
(assert-event (equal (fn-dtrace-verb :on '(:off) nil) '(:refused :not-configured)))
