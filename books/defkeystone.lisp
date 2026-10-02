; fn: `defkeystone' and `defteeth' --- a keystone's teeth, generated from one
; form, for a theorem the form states or for one already in the world.
;
; AGENTS.md ("What makes a claim") fixes what a keystone ships with: a
; reachable positive witness asserting the complete antecedent and
; conclusion; per hypothesis a removal witness that checks every retained
; hypothesis, the failure of the omitted one and the failure of the
; conclusion; corrupted-state and mutation witnesses labelled apart; the
; weakened theorem registered as a checked must-fail; and a registry row
; naming the subject, the function the host calls.  Until this book every
; one of those was written by hand (2,161 must-fail forms in 574 test books)
; and policed after the fact by four tools.  Here the schema is the macro:
;
;   (defkeystone NAME
;     (implies (and H1 ... Hn) C)        ; or a term with no hypothesis
;     :subject FN                        ; the host-called function
;     [:id "PRF-NNN"]                    ; the registry row it is evidence for
;     [:restates KEYSTONE]               ; a theorem whose formula NAME's equals
;     . SPEC)                            ; the teeth, below
;
;   (defteeth NAME . SPEC)               ; NAME an admitted theorem (any book);
;                                        ; its LITERAL statement is read from
;                                        ; the world and untranslated
;
;   SPEC:
;     [:hyps (L1 ... Ln)]                ; labels; default H1 ... Hn
;     :witness ((VAR VAL) ...)           ; the reachable positive witness
;     :breaks ((Li ((VAR VAL) ...) [:corrupt "why unreachable"]) ...)
;     :mutations ((L TERM ((VAR VAL) ...)) ...) | (:none "why")
;     [:corrupt ((L ((VAR VAL) ...)) ...)]
;     [:visits ((L VISITS BOUND :attains ((VAR VAL) ...) | :none "why"
;                 [:rests-on (A ...)] [:hints ...]) ...)]   ; a cost claim
;     [:allocation ((L CONSES BOUND ...same options...) ...)]   ; the other kind
;     [:hints ...] [:rule-classes ...] [:otf-flg ...]
;
; expands, in this order, to
;
;   (defthm NAME TERM :hints ...)                       ; defkeystone only
;   (assert-event (equal (getpropc 'NAME 'theorem nil (w state))
;                        (getpropc 'KEYSTONE 'theorem nil (w state))))
;                                            ; with :restates only
;   (assert-event (and (let* W H1) ... (let* W Hn) (let* W C)))
;   ; for each Hi, with Bi = W overridden by Li's bindings:
;   (assert-event (with-guard-checking :none
;                  (and (let* Bi Hj) ... (not (let* Bi Hi)) (not (let* Bi C)))))
;   (local (must-fail-checked (defthm NAME-without-Li <TERM less Hi> :hints ...)))
;   ; for each mutation (a false neighbour of the statement):
;   (assert-event (with-guard-checking :none (not (let* Bm M))))
;   (local (must-fail-checked (defthm NAME-mutant-L M :hints ...)))
;   ; for each corrupted state (outside the hypotheses, conclusion false):
;   (assert-event (with-guard-checking :none
;                  (and (not (let* Bc (and H1 ... Hn))) (not (let* Bc C)))))
;   ; for each visit bound L (a cost claim), with Ba = W overridden by :attains:
;   (defthm NAME-visits-L (implies (and H1 ... Hn) (<= VISITS BOUND)) :hints ...)
;   (assert-event (and (let* W H1) ... (let* W (<= VISITS BOUND))))
;   (assert-event (and (let* Ba H1) ... (let* Ba (equal VISITS BOUND))))
;   ; for each allocation bound L: the same three, named NAME-allocation-L
;   (table fn-teeth 'NAME '(:by defkeystone|defteeth :hyps (L...) :mutations
;                           (L...)|:none :corrupt (L...)
;                           :visits ((L VISITS BOUND :attains|:none :rests-on (A...)) ...)
;                           :allocation (... the same shape ...)))
;
; (the positive witness and the visit witnesses run under the guards, as the
; host would; the others are LOGICAL values, since a corrupted state may lie
; outside a guard), so a removal witness is a ground COUNTEREXAMPLE to the
; weakened theorem, evaluated, and the must-fail beside it is the same
; weakened theorem under the keystone's own hints (admitted first as NAME, so
; no must-fail can pass on a hint that stopped working).  An assert-event
; carries its label in `:msg' ("NAME: witness", "NAME: without L", "NAME:
; without L (corrupted state: why)", "NAME: mutant L", "NAME: corrupt L",
; "NAME: visits L", "NAME: attains L").
;
; VISITS.  A cost claim is a bound on the elements a function VISITS, never
; on its output (build/coordinator/ORIENTATION-2026-10-02.md lesson 3: a
; quantum that answers Q lines may walk the whole catalog in its guard).  A
; :visits entry states (<= VISITS BOUND) over the keystone's own hypotheses
; and variables, proves it as NAME-visits-L, evaluates it at the witness, and
; evaluates (equal VISITS BOUND) at the :attains bindings: a bound nothing
; attains is slack, not a claim; `:none "why"' says why no state attains it
; (the row records which).  VISITS is the author's visit-counting term (a
; `-visits' twin, or a `def-loop' step count); this book does not derive it.
; `:allocation' is the same claim about conses.  `:rests-on (A ...)' names
; the host cost facts the bound rests on, each a NAMED ASSUMPTION (a
; constrained function an encapsulate in books/assumptions.lisp or
; books/assumptions-*.lisp introduces, by the world's record of the book, as
; books/def-carried.lisp checks a producer's): an `equal' or `member' over
; shared structure is a walk unless the fact that makes it a pointer test is
; named (A-SBCL-EQUAL-SHARED).
;
; MUTATIONS are REQUIRED: a keystone with no false neighbour named shows
; nothing bites beyond its hypotheses, so `:mutations (:none "why")' says so
; in the row (fn-teeth :mutations :none), where tools/teeth_check.py counts
; it, rather than leaving it unsaid.
;
; REFUSED at expansion, each by name (fn-dk-refusal / fn-dt-refusal): no
; :witness; no :subject (defkeystone); a hypothesis with no :breaks entry
; (the error names its label and its term); no :mutations; a :breaks,
; :mutations, :corrupt or :visits entry that is malformed or names no
; hypothesis; :hyps of the wrong length or with a repeated label; a repeated
; mutation or visits label; defteeth of a name that is not a theorem in this
; world, or whose teeth were declared already; an unknown keyword.  A
; variable the witness does not bind is refused by ACL2 itself when the
; assert-event translates (a stobj formal is left unbound on purpose: the
; live stobj is the witness).
;
; FOR A GENERATOR.  A macro that admits keystones from a declaration (a
; sibling of books/def-carried.lisp) splices (defteeth NAME . SPEC) into its
; expansion when the teeth are in hand, or records the debt as
;   (table fn-teeth-owed 'NAME '(:by MACRO [:visits ((VISITS BOUND [:rests-on
;                                 (A ...)]) ...)] [:allocation (...)]))
; and the test book that includes it ends with (defteeth-check), which
; refuses the first owed keystone with no fn-teeth row in that world, or
; whose teeth do not state every owed bound (the same VISITS and BOUND
; terms, resting on the same named facts): the declaration is the source of
; truth for what the teeth must say.  fn-teeth-refusal and fn-teeth-events
; are the :program entry points for a generator that checks or builds a SPEC
; at its own expansion time.
;
; The static tools read the SAME expansion without evaluating anything:
; tools/ledger.py `defkeystone_expansion' mirrors `fn-dk-expand' form for
; form, and tests/acl2/defkeystone-tests.lisp pins both to one literal
; expansion (tests/test_ledger.py reads that literal).  Change one, change
; the other and the literal together.  `defteeth' needs the theorem's
; statement, which the ledger has only once every book is read:
; tools/teeth_check.py expands it from the tree's theorem list
; (`defteeth_expansion'), and tools/keystone_emit.py counts, per registry
; event, generated teeth against hand ones under a baseline that only
; shrinks.
;
; A book that uses `defkeystone' or `defteeth' includes "must-fail-checked"
; (tests/acl2) itself: the expansion names `must-fail-checked', which this
; book does not define, so a keystone's teeth live in a test book.  This
; book has no `include-book' and leaves no rule: its helpers are `:program'
; mode (declared per defun, as books/defrecord.lisp does, so tools/ledger.py's
; `exports_no_rule' sees a macro book).

(in-package "ACL2")


(defconst *fn-dk-spec-keys*
  '(:hyps :witness :breaks :mutations :corrupt :visits :allocation :hints))

(defconst *fn-dk-bound-kinds* '((:visits . -visits-) (:allocation . -allocation-)))

(defconst *fn-dk-keys*
  (append '(:subject :id :restates) *fn-dk-spec-keys* '(:rule-classes :otf-flg)))

(defun fn-dk-get (key kvs)
  (declare (xargs :mode :program))
  (cadr (assoc-keyword key kvs)))

(defun fn-dk-hyps (term)
  (declare (xargs :mode :program))
  ; the hypotheses of (implies (and H1 .. Hn) C) or (implies H C); else none
  (if (and (consp term) (eq (car term) 'implies) (true-listp term)
           (equal (len term) 3))
      (let ((h (cadr term)))
        (if (and (consp h) (eq (car h) 'and))
            (cdr h)
          (list h)))
    nil))

(defun fn-dk-concl (term)
  (declare (xargs :mode :program))
  (if (and (consp term) (eq (car term) 'implies) (true-listp term)
           (equal (len term) 3))
      (caddr term)
    term))

(defun fn-dk-default-labels (i n name)
  (declare (xargs :mode :program))
  (if (zp n)
      nil
    (cons (packn-pos (list 'h i) name)
          (fn-dk-default-labels (1+ i) (1- n) name))))

(defun fn-dk-labels (name hyps kvs)
  (declare (xargs :mode :program))
  (if (assoc-keyword :hyps kvs)
      (fn-dk-get :hyps kvs)
    (fn-dk-default-labels 1 (len hyps) name)))

(defun fn-dk-bindingsp (x)
  (declare (xargs :mode :program))
  ; ((VAR VAL) ...) with distinct symbol VARs
  (and (true-listp x)
       (doublet-listp x)
       (symbol-listp (strip-cars x))
       (no-duplicatesp-eq (strip-cars x))))

(defun fn-dk-break-entryp (x)
  (declare (xargs :mode :program))
  ; (LABEL BINDINGS) or (LABEL BINDINGS :corrupt "why")
  (and (true-listp x)
       (symbolp (car x))
       (fn-dk-bindingsp (cadr x))
       (or (equal (len x) 2)
           (and (equal (len x) 4)
                (eq (caddr x) :corrupt)
                (stringp (cadddr x))
                (< 0 (length (cadddr x)))))))

(defun fn-dk-break-entriesp (x)
  (declare (xargs :mode :program))
  (if (atom x)
      (null x)
    (and (fn-dk-break-entryp (car x))
         (fn-dk-break-entriesp (cdr x)))))

(defun fn-dk-nonep (x)
  (declare (xargs :mode :program))
  ; (:none "why")
  (and (true-listp x) (equal (len x) 2) (eq (car x) :none)
       (stringp (cadr x)) (< 0 (length (cadr x)))))

(defun fn-dk-mutationsp (x)
  (declare (xargs :mode :program))
  ; ((LABEL TERM BINDINGS) ...)
  (if (atom x)
      (null x)
    (and (true-listp (car x))
         (equal (len (car x)) 3)
         (symbolp (car (car x)))
         (fn-dk-bindingsp (caddr (car x)))
         (fn-dk-mutationsp (cdr x)))))

(defun fn-dk-mutation-entries (x)
  (declare (xargs :mode :program))
  (if (fn-dk-nonep x) nil x))

(defun fn-dk-corruptsp (x)
  (declare (xargs :mode :program))
  ; ((LABEL BINDINGS) ...)
  (if (atom x)
      (null x)
    (and (true-listp (car x))
         (equal (len (car x)) 2)
         (symbolp (car (car x)))
         (fn-dk-bindingsp (cadr (car x)))
         (fn-dk-corruptsp (cdr x)))))

(defun fn-dk-unknown-keys-of (kvs keys)
  (declare (xargs :mode :program))
  (cond ((atom kvs) nil)
        ((member-eq (car kvs) keys) (fn-dk-unknown-keys-of (cddr kvs) keys))
        (t (cons (car kvs) (fn-dk-unknown-keys-of (cddr kvs) keys)))))

(defun fn-dk-unknown-keys (kvs)
  (declare (xargs :mode :program))
  (fn-dk-unknown-keys-of kvs *fn-dk-keys*))

(defun fn-dk-visits-entryp (x)
  (declare (xargs :mode :program))
  ; (LABEL VISITS BOUND :attains BINDINGS [:rests-on (A ...)] [:hints H])
  ; or (LABEL VISITS BOUND :none "why" [:rests-on (A ...)] [:hints H])
  (and (true-listp x)
       (<= 3 (len x))
       (symbolp (car x)) (car x)
       (keyword-value-listp (cdddr x))
       (null (fn-dk-unknown-keys-of (cdddr x) '(:attains :none :rests-on :hints)))
       (true-listp (fn-dk-get :rests-on (cdddr x)))
       (let ((attains (assoc-keyword :attains (cdddr x)))
             (none (assoc-keyword :none (cdddr x))))
         (and (or attains none)
              (not (and attains none))
              (or (null attains) (fn-dk-bindingsp (cadr attains)))
              (or (null none)
                  (and (stringp (cadr none)) (< 0 (length (cadr none)))))))))

(defun fn-dk-visitsp (x)
  (declare (xargs :mode :program))
  (if (atom x)
      (null x)
    (and (fn-dk-visits-entryp (car x))
         (fn-dk-visitsp (cdr x)))))

(defun fn-dk-first-unbroken (labels hyps breaks)
  (declare (xargs :mode :program))
  ; the first (LABEL HYP) with no :breaks entry, or nil
  (cond ((atom labels) nil)
        ((assoc-eq (car labels) breaks)
         (fn-dk-first-unbroken (cdr labels) (cdr hyps) breaks))
        (t (list (car labels) (car hyps)))))

(defun fn-dk-first-stray (entries labels)
  (declare (xargs :mode :program))
  ; the first entry label that names no hypothesis, or nil
  (cond ((atom entries) nil)
        ((member-eq (car (car entries)) labels)
         (fn-dk-first-stray (cdr entries) labels))
        (t (car (car entries)))))

(defun fn-dk-spec-refusal (name hyps kvs keys)
  (declare (xargs :mode :program))
  ; nil when SPEC (the keyword-value list KVS, over KEYS) is well-formed for
  ; a statement with hypotheses HYPS; else (REASON . DETAILS), which names
  ; the offending hypothesis, entry or keyword.  tests/acl2/defkeystone-tests
  ; asserts each reason.
  (let* ((labels (fn-dk-labels name hyps kvs))
         (breaks (fn-dk-get :breaks kvs))
         (mutations (fn-dk-get :mutations kvs))
         (visits (fn-dk-get :visits kvs)))
    (cond
     ((not (keyword-value-listp kvs)) (list :bad-options kvs))
     ((fn-dk-unknown-keys-of kvs keys)
      (cons :unknown-keyword (fn-dk-unknown-keys-of kvs keys)))
     ((not (and (fn-dk-get :witness kvs)
                (fn-dk-bindingsp (fn-dk-get :witness kvs))))
      (list :no-witness name))
     ((not (and (symbol-listp labels)
                (no-duplicatesp-eq labels)
                (equal (len labels) (len hyps))))
      (list :bad-labels labels (len hyps)))
     ((not (fn-dk-break-entriesp breaks)) (list :bad-breaks breaks))
     ((not (no-duplicatesp-eq (strip-cars breaks)))
      (list :duplicate-break (strip-cars breaks)))
     ((fn-dk-first-stray breaks labels)
      (list :break-names-no-hypothesis (fn-dk-first-stray breaks labels)))
     ((fn-dk-first-unbroken labels hyps breaks)
      (cons :no-breaking-value (fn-dk-first-unbroken labels hyps breaks)))
     ((null (assoc-keyword :mutations kvs)) (list :no-mutation name))
     ((not (or (fn-dk-nonep mutations) (fn-dk-mutationsp mutations)))
      (list :bad-mutations mutations))
     ((not (no-duplicatesp-eq (strip-cars (fn-dk-mutation-entries mutations))))
      (list :duplicate-mutation (strip-cars (fn-dk-mutation-entries mutations))))
     ((not (fn-dk-corruptsp (fn-dk-get :corrupt kvs)))
      (list :bad-corrupt (fn-dk-get :corrupt kvs)))
     ((not (fn-dk-visitsp visits)) (list :bad-visits visits))
     ((not (no-duplicatesp-eq (strip-cars visits)))
      (list :duplicate-visits (strip-cars visits)))
     ((not (fn-dk-visitsp (fn-dk-get :allocation kvs)))
      (list :bad-visits (fn-dk-get :allocation kvs)))
     ((not (no-duplicatesp-eq (strip-cars (fn-dk-get :allocation kvs))))
      (list :duplicate-visits (strip-cars (fn-dk-get :allocation kvs))))
     (t nil))))

(defun fn-dk-refusal (name term kvs)
  (declare (xargs :mode :program))
  ; defkeystone: the form's own checks, then the SPEC's
  (cond
   ((not (symbolp name)) (list :bad-name name))
   ((not (keyword-value-listp kvs)) (list :bad-options kvs))
   ((fn-dk-unknown-keys kvs) (cons :unknown-keyword (fn-dk-unknown-keys kvs)))
   ((not (and (fn-dk-get :subject kvs) (symbolp (fn-dk-get :subject kvs))))
    (list :no-subject name))
   (t (fn-dk-spec-refusal name (fn-dk-hyps term) kvs *fn-dk-keys*))))

; ---------------------------------------------------------------------------
; The events.

(defun fn-dk-override (base over)
  (declare (xargs :mode :program))
  ; BASE's bindings with OVER's values where OVER binds the same variable,
  ; then OVER's other bindings, in order
  (cond ((atom base) over)
        ((assoc-eq (car (car base)) over)
         (cons (assoc-eq (car (car base)) over)
               (fn-dk-override (cdr base)
                               (remove1-assoc-eq (car (car base)) over))))
        (t (cons (car base) (fn-dk-override (cdr base) over)))))

(defun fn-dk-at (bindings term)
  (declare (xargs :mode :program))
  `(let* ,bindings (declare (ignorable ,@(strip-cars bindings))) ,term))

(defun fn-dk-logical (term)
  (declare (xargs :mode :program))
  ; a removal, mutant or corrupted-state witness is evaluated for its LOGICAL
  ; value: it may lie outside a guard by design (a corrupted state)
  `(with-guard-checking :none ,term))

(defun fn-dk-all-at (bindings terms)
  (declare (xargs :mode :program))
  (if (atom terms)
      nil
    (cons (fn-dk-at bindings (car terms))
          (fn-dk-all-at bindings (cdr terms)))))

(defun fn-dk-without (i hyps)
  (declare (xargs :mode :program))
  ; HYPS less its I-th (0-based) element
  (if (zp i)
      (cdr hyps)
    (cons (car hyps) (fn-dk-without (1- i) (cdr hyps)))))

(defun fn-dk-implies (hyps concl)
  (declare (xargs :mode :program))
  (cond ((atom hyps) concl)
        ((atom (cdr hyps)) `(implies ,(car hyps) ,concl))
        (t `(implies (and ,@hyps) ,concl))))

(defun fn-dk-conj (terms)
  (declare (xargs :mode :program))
  (if (and (consp terms) (atom (cdr terms)))
      (car terms)
    `(and ,@terms)))

(defun fn-dk-hint-args (kvs)
  (declare (xargs :mode :program))
  (if (assoc-keyword :hints kvs) (list :hints (fn-dk-get :hints kvs)) nil))

(defun fn-dk-label-msg (name words)
  (declare (xargs :mode :program))
  (concatenate 'string (symbol-name name) ": " words))

(defun fn-dk-removals (name i labels hyps concl witness breaks hint-args)
  (declare (xargs :mode :program))
  ; LABELS is the tail from the I-th hypothesis on; HYPS is all of them
  (if (atom labels)
      nil
    (let* ((entry (assoc-eq (car labels) breaks))
           (b (fn-dk-override witness (cadr entry)))
           (retained (fn-dk-without i hyps))
           (why (if (equal (len entry) 4)
                    (concatenate 'string " (corrupted state: " (cadddr entry) ")")
                  ""))
           (label (symbol-name (car labels))))
      (list*
       `(assert-event
         ,(fn-dk-logical
           `(and ,@(fn-dk-all-at b retained)
                 (not ,(fn-dk-at b (nth i hyps)))
                 (not ,(fn-dk-at b concl))))
         :msg ,(fn-dk-label-msg name (concatenate 'string "without " label why)))
       `(local (must-fail-checked
                (defthm ,(packn-pos (list name '-without- (car labels)) name)
                  ,(fn-dk-implies retained concl)
                  ,@hint-args)))
       (fn-dk-removals name (1+ i) (cdr labels) hyps concl witness
                       breaks hint-args)))))

(defun fn-dk-mutants (name witness mutations hint-args)
  (declare (xargs :mode :program))
  (if (atom mutations)
      nil
    (let* ((m (car mutations))
           (b (fn-dk-override witness (caddr m))))
      (list*
       `(assert-event ,(fn-dk-logical `(not ,(fn-dk-at b (cadr m))))
                      :msg ,(fn-dk-label-msg
                             name (concatenate 'string "mutant "
                                               (symbol-name (car m)))))
       `(local (must-fail-checked
                (defthm ,(packn-pos (list name '-mutant- (car m)) name)
                  ,(cadr m)
                  ,@hint-args)))
       (fn-dk-mutants name witness (cdr mutations) hint-args)))))

(defun fn-dk-corrupts (name hyps concl witness corrupts)
  (declare (xargs :mode :program))
  (if (atom corrupts)
      nil
    (let ((b (fn-dk-override witness (cadr (car corrupts)))))
      (cons `(assert-event
              ,(fn-dk-logical
                `(and (not ,(fn-dk-at b (fn-dk-conj hyps)))
                      (not ,(fn-dk-at b concl))))
              :msg ,(fn-dk-label-msg
                     name (concatenate 'string "corrupt "
                                       (symbol-name (car (car corrupts))))))
            (fn-dk-corrupts name hyps concl witness (cdr corrupts))))))

(defun fn-dk-bound-events (name kind hyps witness entries)
  (declare (xargs :mode :program))
  ; per bound (L TERM BOUND . OPTS) of KIND (:visits or :allocation): the
  ; cost theorem, its witness, and the state that attains it
  (if (atom entries)
      nil
    (let* ((entry (car entries))
           (label (car entry))
           (v (cadr entry))
           (bound (caddr entry))
           (opts (cdddr entry))
           (attains (assoc-keyword :attains opts))
           (hint-args (fn-dk-hint-args opts))
           (word (string-downcase (symbol-name kind))))
      (append
       `((defthm ,(packn-pos (list name (cdr (assoc-eq kind *fn-dk-bound-kinds*)) label)
                             name)
           ,(fn-dk-implies hyps `(<= ,v ,bound))
           ,@hint-args)
         (assert-event
          ,(fn-dk-conj (append (fn-dk-all-at witness hyps)
                               (list (fn-dk-at witness `(<= ,v ,bound)))))
          :msg ,(fn-dk-label-msg name (concatenate 'string word " "
                                                   (symbol-name label)))))
       (and attains
            (let ((b (fn-dk-override witness (cadr attains))))
              `((assert-event
                 ,(fn-dk-conj (append (fn-dk-all-at b hyps)
                                      (list (fn-dk-at b `(equal ,v ,bound)))))
                 :msg ,(fn-dk-label-msg name (concatenate 'string "attains "
                                                          (symbol-name label)))))))
       (fn-dk-bound-events name kind hyps witness (cdr entries))))))

(defun fn-dk-bound-rows (entries)
  (declare (xargs :mode :program))
  ; (L TERM BOUND :attains|:none :rests-on (A ...)) per entry: the terms, so
  ; defteeth-check can hold them against what a generator owes
  (if (atom entries)
      nil
    (let ((opts (cdddr (car entries))))
      (cons (list (car (car entries)) (cadr (car entries)) (caddr (car entries))
                  (if (assoc-keyword :attains opts) :attains :none)
                  :rests-on (fn-dk-get :rests-on opts))
            (fn-dk-bound-rows (cdr entries))))))

(defun fn-dk-row (name by labels kvs)
  (declare (xargs :mode :program))
  ; the fn-teeth row: labels only, never a binding
  (let ((mutations (fn-dk-get :mutations kvs)))
    `(table fn-teeth ',name
            '(:by ,by
              :hyps ,labels
              :mutations ,(if (fn-dk-nonep mutations)
                              :none
                            (strip-cars mutations))
              :corrupt ,(strip-cars (fn-dk-get :corrupt kvs))
              :visits ,(fn-dk-bound-rows (fn-dk-get :visits kvs))
              :allocation ,(fn-dk-bound-rows (fn-dk-get :allocation kvs))))))

(defun fn-dk-teeth-events (name by hyps concl kvs)
  (declare (xargs :mode :program))
  ; the teeth of NAME, whose statement has hypotheses HYPS and conclusion
  ; CONCL, from a well-formed SPEC KVS; BY names the macro for the row
  (let* ((labels (fn-dk-labels name hyps kvs))
         (witness (fn-dk-get :witness kvs))
         (hint-args (fn-dk-hint-args kvs)))
    (append
     `((assert-event
        ,(fn-dk-conj (append (fn-dk-all-at witness hyps)
                             (list (fn-dk-at witness concl))))
        :msg ,(fn-dk-label-msg name "witness")))
     (fn-dk-removals name 0 labels hyps concl witness
                     (fn-dk-get :breaks kvs) hint-args)
     (fn-dk-mutants name witness (fn-dk-mutation-entries (fn-dk-get :mutations kvs))
                    hint-args)
     (fn-dk-corrupts name hyps concl witness (fn-dk-get :corrupt kvs))
     (fn-dk-bound-events name :visits hyps witness (fn-dk-get :visits kvs))
     (fn-dk-bound-events name :allocation hyps witness (fn-dk-get :allocation kvs))
     (list (fn-dk-row name by labels kvs)))))

(defun fn-dk-expand (form)
  (declare (xargs :mode :program))
  ; FORM is the whole (defkeystone NAME TERM . KVS); the events it stands for
  (let* ((name (cadr form))
         (term (caddr form))
         (kvs (cdddr form))
         (hint-args (fn-dk-hint-args kvs))
         (restates (fn-dk-get :restates kvs)))
    `(progn
       (defthm ,name ,term
         ,@hint-args
         ,@(if (assoc-keyword :rule-classes kvs)
               (list :rule-classes (fn-dk-get :rule-classes kvs))
             nil)
         ,@(if (assoc-keyword :otf-flg kvs)
               (list :otf-flg (fn-dk-get :otf-flg kvs))
             nil))
       ,@(if restates
             `((assert-event
                (equal (getpropc ',name 'theorem nil (w state))
                       (getpropc ',restates 'theorem nil (w state)))
                :msg ,(fn-dk-label-msg name "restates")))
           nil)
       ,@(fn-dk-teeth-events name 'defkeystone (fn-dk-hyps term) (fn-dk-concl term)
                             kvs))))

(defun fn-dk-refusal-text (reason)
  (declare (xargs :mode :program))
  (case (car reason)
    (:no-breaking-value
     (msg "hypothesis ~x0, ~x1, has no breaking value in :breaks.  A keystone ~
           ships a removal witness per hypothesis (AGENTS.md): give (~x0 ((VAR ~
           VAL) ...)) at which the other hypotheses hold and this one and the ~
           conclusion fail."
          (cadr reason) (caddr reason)))
    (:no-witness (msg "~x0 has no :witness ((VAR VAL) ...): a keystone with no ~
                       reachable positive witness is refused."
                      (cadr reason)))
    (:no-subject (msg "~x0 has no :subject: name the function the host calls."
                      (cadr reason)))
    (:no-mutation (msg "~x0 names no :mutations: give a false neighbour of the ~
                        statement as ((LABEL TERM ((VAR VAL) ...)) ...), or say ~
                        :mutations (:none \"why\") so the row records it."
                       (cadr reason)))
    (:break-names-no-hypothesis
     (msg ":breaks names ~x0, which labels no hypothesis." (cadr reason)))
    (:bad-visits (msg ":visits ~x0 is not ((LABEL VISITS BOUND :attains ((VAR VAL) ~
                       ...) | :none \"why\" [:hints ...]) ...)." (cadr reason)))
    (:not-a-theorem (msg "~x0 is not a theorem in this world: defteeth names an ~
                          admitted theorem, whose literal statement it reads."
                         (cadr reason)))
    (:declared-twice (msg "~x0 already has teeth in this world (table fn-teeth); ~
                           teeth are declared once." (cadr reason)))
    (:unknown-keyword (msg "unknown keyword(s) ~&0; the keywords are ~&1."
                           (cdr reason) *fn-dk-keys*))
    (otherwise (msg "malformed form: ~x0." reason))))


(defmacro defkeystone (&whole form name term &rest kvs)
  ; A refusal is a SOFT error event, so it fails like any refused event (and
  ; under must-fail prints nothing a certification log reads as a failure).
  (let ((reason (fn-dk-refusal name term kvs)))
    (if reason
        `(make-event (er soft 'defkeystone "~x0: ~@1" ',name
                         ',(fn-dk-refusal-text reason)))
      (fn-dk-expand form))))

; ---------------------------------------------------------------------------
; defteeth: the teeth of a theorem already in the world.

(defun fn-dt-statement (name w)
  (declare (xargs :mode :program))
  ; the untranslated literal statement of the theorem NAME, or nil
  (let ((formula (getpropc name 'theorem nil w)))
    (and formula (untranslate formula t w))))

(defun fn-teeth-refusal (name kvs w)
  (declare (xargs :mode :program))
  ; nil when (defteeth NAME . KVS) is well-formed in the world W; else
  ; (REASON . DETAILS)
  (cond
   ((not (and (symbolp name) name)) (list :bad-name name))
   ((null (getpropc name 'theorem nil w)) (list :not-a-theorem name))
   ((assoc-eq name (table-alist 'fn-teeth w)) (list :declared-twice name))
   (t (fn-dk-spec-refusal name (fn-dk-hyps (fn-dt-statement name w)) kvs
                          *fn-dk-spec-keys*))))

(defun fn-teeth-events (name kvs w)
  (declare (xargs :mode :program))
  ; the events (defteeth NAME . KVS) stands for in W, for a SPEC
  ; fn-teeth-refusal accepts
  (let ((statement (fn-dt-statement name w)))
    (fn-dk-teeth-events name 'defteeth (fn-dk-hyps statement) (fn-dk-concl statement)
                        kvs)))

(defmacro defteeth (name &rest kvs)
  `(make-event
    (let ((reason (fn-teeth-refusal ',name ',kvs (w state))))
      (if reason
          (er soft 'defteeth "~x0: ~@1" ',name (fn-dk-refusal-text reason))
        (value (cons 'progn (fn-teeth-events ',name ',kvs (w state))))))))

; A generator's debt: (table fn-teeth-owed 'NAME '(:by MACRO [:visits ((TERM
; BOUND [:rests-on (A ...)]) ...)] [:allocation (...)])) in the book that
; admits NAME; the test world that declares the teeth checks it: a row, and
; every owed bound stated with the same terms and the same named facts.

(defun fn-dt-bound-statedp (owed rows)
  (declare (xargs :mode :program))
  ; OWED = (TERM BOUND [:rests-on (A ...)]) is among the declared ROWS
  ; (L TERM BOUND :attains|:none :rests-on (A ...))
  (cond ((atom rows) nil)
        ((and (equal (cadr (car rows)) (car owed))
              (equal (caddr (car rows)) (cadr owed))
              (set-equalp-equal (fn-dk-get :rests-on (cddddr (car rows)))
                                (fn-dk-get :rests-on (cddr owed))))
         t)
        (t (fn-dt-bound-statedp owed (cdr rows)))))

(defun fn-dt-first-unstated (owed rows)
  (declare (xargs :mode :program))
  (cond ((atom owed) nil)
        ((fn-dt-bound-statedp (car owed) rows) (fn-dt-first-unstated (cdr owed) rows))
        (t (car owed))))

(defun fn-dt-owed-problem (owed teeth)
  (declare (xargs :mode :program))
  ; nil, or a msg for the first owed keystone whose teeth are missing or
  ; state a different bound
  (if (atom owed)
      nil
    (let* ((name (car (car owed)))
           (debt (cdr (car owed)))
           (row (cdr (assoc-eq name teeth)))
           (visits (and row (fn-dt-first-unstated (fn-dk-get :visits debt)
                                                  (fn-dk-get :visits row))))
           (allocation (and row (fn-dt-first-unstated (fn-dk-get :allocation debt)
                                                      (fn-dk-get :allocation row)))))
      (cond ((null row)
             (msg "~x0 (admitted by ~x1) has no teeth in this world: (defteeth ~x0 ~
                   ...) is owed" name (fn-dk-get :by debt)))
            (visits
             (msg "~x0's teeth do not state the visit bound ~x1 (admitted by ~x2) ~
                   with the same terms and the same :rests-on facts"
                  name visits (fn-dk-get :by debt)))
            (allocation
             (msg "~x0's teeth do not state the allocation bound ~x1 (admitted by ~
                   ~x2) with the same terms and the same :rests-on facts"
                  name allocation (fn-dk-get :by debt)))
            (t (fn-dt-owed-problem (cdr owed) teeth))))))

(defmacro defteeth-check ()
  `(make-event
    (let ((problem (fn-dt-owed-problem (table-alist 'fn-teeth-owed (w state))
                                       (table-alist 'fn-teeth (w state)))))
      (if problem
          (er soft 'defteeth-check "~@0." problem)
        (value '(value-triple :teeth-complete))))))
