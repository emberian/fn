; fn: `defkeystone' --- a keystone with its teeth, generated from one form.
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
;     [:hyps (L1 ... Ln)]                ; labels; default H1 ... Hn
;     :witness ((VAR VAL) ...)           ; the reachable positive witness
;     :breaks ((Li ((VAR VAL) ...) [:corrupt "why unreachable"]) ...)
;     [:mutations ((L TERM ((VAR VAL) ...)) ...)]
;     [:corrupt ((L ((VAR VAL) ...)) ...)]
;     [:hints ...] [:rule-classes ...] [:otf-flg ...])
;
; expands, in this order, to
;
;   (defthm NAME TERM :hints ...)
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
;
; (the positive witness runs under the guards, as the host would; the others
; are LOGICAL values, since a corrupted state may lie outside a guard), so a
; removal witness is a ground COUNTEREXAMPLE to the weakened theorem,
; evaluated, and the must-fail beside it is the same weakened theorem under
; the keystone's own hints (admitted first as NAME, so no must-fail can pass
; on a hint that stopped working).  An assert-event carries its label in
; `:msg' ("NAME: witness", "NAME: without L", "NAME: without L (corrupted
; state: why)", "NAME: mutant L", "NAME: corrupt L").
;
; REFUSED at expansion, each by name (fn-dk-refusal): no :witness; no
; :subject; a hypothesis with no :breaks entry (the error names its label and
; its term); a :breaks, :mutations or :corrupt entry that is malformed or
; names no hypothesis; :hyps of the wrong length or with a repeated label; a
; keystone with no hypothesis and no mutation (nothing would show it bites);
; an unknown keyword.  A variable the witness does not bind is refused by
; ACL2 itself when the assert-event translates.
;
; The static tools read the SAME expansion without evaluating anything:
; tools/ledger.py `defkeystone_expansion' mirrors `fn-dk-expand' form for
; form, and tests/acl2/defkeystone-tests.lisp pins both to one literal
; expansion (tests/test_ledger.py reads that literal).  Change one, change
; the other and the literal together.
;
; A book that uses `defkeystone' includes "must-fail-checked" (tests/acl2)
; itself: the expansion names `must-fail-checked', which this book does not
; define, so a keystone's teeth live in a test book.  This book has no
; `include-book' and leaves no rule: its helpers are `:program' mode
; (declared per defun, as books/defrecord.lisp does, so tools/ledger.py's
; `exports_no_rule' sees a macro book).
; What the form cannot express yet, and the plan for each:
; planning/evidence/defkeystone-2026-09-27.md.

(in-package "ACL2")


(defconst *fn-dk-keys*
  '(:subject :id :restates :hyps :witness :breaks :mutations :corrupt
    :hints :rule-classes :otf-flg))

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

(defun fn-dk-unknown-keys (kvs)
  (declare (xargs :mode :program))
  (cond ((atom kvs) nil)
        ((member-eq (car kvs) *fn-dk-keys*) (fn-dk-unknown-keys (cddr kvs)))
        (t (cons (car kvs) (fn-dk-unknown-keys (cddr kvs))))))

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

(defun fn-dk-refusal (name term kvs)
  (declare (xargs :mode :program))
  ; nil when the form is well-formed; else (REASON . DETAILS), which names
  ; the offending hypothesis, entry or keyword.  tests/acl2/defkeystone-tests
  ; asserts each reason.
  (let* ((hyps (fn-dk-hyps term))
         (labels (fn-dk-labels name hyps kvs))
         (breaks (fn-dk-get :breaks kvs)))
    (cond
     ((not (symbolp name)) (list :bad-name name))
     ((not (keyword-value-listp kvs)) (list :bad-options kvs))
     ((fn-dk-unknown-keys kvs) (cons :unknown-keyword (fn-dk-unknown-keys kvs)))
     ((not (and (fn-dk-get :subject kvs) (symbolp (fn-dk-get :subject kvs))))
      (list :no-subject name))
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
     ((not (fn-dk-mutationsp (fn-dk-get :mutations kvs)))
      (list :bad-mutations (fn-dk-get :mutations kvs)))
     ((not (fn-dk-corruptsp (fn-dk-get :corrupt kvs)))
      (list :bad-corrupt (fn-dk-get :corrupt kvs)))
     ((and (null hyps) (null (fn-dk-get :mutations kvs)))
      (list :no-teeth name))
     (t nil))))

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

(defun fn-dk-expand (form)
  (declare (xargs :mode :program))
  ; FORM is the whole (defkeystone NAME TERM . KVS); the events it stands for
  (let* ((name (cadr form))
         (term (caddr form))
         (kvs (cdddr form))
         (hyps (fn-dk-hyps term))
         (concl (fn-dk-concl term))
         (labels (fn-dk-labels name hyps kvs))
         (witness (fn-dk-get :witness kvs))
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
       (assert-event
        ,(fn-dk-conj (append (fn-dk-all-at witness hyps)
                             (list (fn-dk-at witness concl))))
        :msg ,(fn-dk-label-msg name "witness"))
       ,@(fn-dk-removals name 0 labels hyps concl witness
                         (fn-dk-get :breaks kvs) hint-args)
       ,@(fn-dk-mutants name witness (fn-dk-get :mutations kvs) hint-args)
       ,@(fn-dk-corrupts name hyps concl witness (fn-dk-get :corrupt kvs)))))

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
    (:no-teeth (msg "~x0 has no hypothesis and no :mutations, so nothing would ~
                     show it bites; give a false neighbour as a mutation."
                    (cadr reason)))
    (:break-names-no-hypothesis
     (msg ":breaks names ~x0, which labels no hypothesis." (cadr reason)))
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
