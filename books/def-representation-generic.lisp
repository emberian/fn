; fn: `def-generic' --- an ATTACHABLE abstract stobj over a LIST foundation,
; derived from a given logical side (lane s-twins 2026-10-08; the payload
; arena's generic, books/payload-arena.lisp, was written by hand before).
;
;   (def-generic NAME
;     :model (:recognizer R :creator C)
;     :exports ((:read   EXPORT :logic FN) ...
;               (:update EXPORT :logic FN) ...)
;     [:lemmas (THM ...)] [:disable (THM ...)])
;
; The logical side is GIVEN: R recognizes the logical value, C creates it, and
; every export's :logic FN is a function of the value, its LAST formal.  What
; the generator derives is everything the hand-written generic repeated:
;
;   * the list foundation NAME$L (one field, NAME$L-ITEMS, holding the value),
;     its well-formedness NAME$L-WFP (R of the field) and the abstraction
;     relation NAME$LCORR (R of the value, and the field is the value);
;   * one :exec per export, NAME$L-SUFFIX for the export NAME-SUFFIX.  A
;     :read export's exec is FN applied to the field; an :update export's is
;     the field replaced by FN applied to it (and is exported with :protect
;     t).  The exec's guard is NAME$L-WFP and FN's own guard over the field,
;     read from the world; its stobj formals are FN's other stobj formals
;     (the octet buffer a seal reads is one);
;   * the three obligations of every export (and the creator's), as
;     `defabsstobj-missing-events' states them, closed by one uniform hint.
;     {correspondence} and {guard-thm} are the unfolding of the exec;
;     {preserved} is the one content of the model, that FN keeps R, and it
;     reads the theorems of :lemmas (already proved, about FN and R);
;   * the `defabsstobj' with :attachable t, the exports in the order given, so
;     that (attach-stobj NAME IMPL) evaluated before this event, with IMPL's
;     export list positionally this one, replaces the foundation and the
;     execs while the :logic functions stay (books/payload-arena-attach.lisp).
;
; Nothing is attached here: the implementation is chosen where the image is
; built.  Every generated name is derived from NAME and the instance is
; recorded in the world table `fn-generated'.  A malformed declaration is
; refused at expansion by the check that names it.  See
; tests/acl2/def-generic-tests.lisp.

(in-package "ACL2")
(include-book "def-representation")

(program)

(defun dg-others (formals)
  (if (or (endp formals) (endp (cdr formals))) nil (cons (car formals) (dg-others (cdr formals)))))

(defun dg-stobj-formals (formals stobjs-in)
  (cond ((endp formals) nil)
        ((car stobjs-in) (cons (car formals) (dg-stobj-formals (cdr formals) (cdr stobjs-in))))
        (t (dg-stobj-formals (cdr formals) (cdr stobjs-in)))))

(defun dg-suffix (name export)
  ; EXPORT is NAME-SUFFIX: the suffix string, or nil.
  (let* ((n (symbol-name name)) (e (symbol-name export)) (k (+ 1 (length n))))
    (and (> (length e) k)
         (equal (subseq e 0 k) (concatenate 'string n "-"))
         (subseq e k (length e)))))

(defun dg-row-ok (name row wrld)
  (and (true-listp row) (equal (len row) 4)
       (member-eq (car row) '(:read :update))
       (symbolp (cadr row)) (cadr row) (not (keywordp (cadr row)))
       (dg-suffix name (cadr row))
       (eq (caddr row) :logic)
       (let ((f (cadddr row)))
         (and (symbolp f) f (function-symbolp f wrld)
              (< 0 (arity f wrld))
              (not (car (last (stobjs-in f wrld))))
              (equal (stobjs-out f wrld) '(nil))))))

(defun dg-rows-ok (name rows wrld)
  (cond ((atom rows) (null rows))
        (t (and (dg-row-ok name (car rows) wrld) (dg-rows-ok name (cdr rows) wrld)))))

(defun dg-exec-name (l name export)
  (adt-sym l (concatenate 'string "-" (dg-suffix name export))))

(defun dg-exec-event (row name l items upd wfp wrld)
  (let* ((kind (car row)) (export (cadr row)) (fn (cadddr row))
         (formals (formals fn wrld))
         (others (dg-others formals))
         (itemsl (list items l))
         (g (guard fn nil wrld))
         (g2 (untranslate (subst-var itemsl (car (last formals)) g) t wrld))
         (stobjs (append (dg-stobj-formals formals (stobjs-in fn wrld)) (list l)))
         (call `(,fn ,@others ,itemsl)))
    `(defun ,(dg-exec-name l name export) (,@others ,l)
       (declare (xargs :stobjs ,stobjs
                       :guard ,(if (eq g2 t) `(,wfp ,l) `(and (,wfp ,l) ,g2))))
       ,(if (eq kind :read) call `(,upd ,call ,l)))))

(defun dg-exec-events (rows name l items upd wfp wrld)
  (if (endp rows)
      nil
    (cons (dg-exec-event (car rows) name l items upd wfp wrld)
          (dg-exec-events (cdr rows) name l items upd wfp wrld))))

(defun dg-exec-names (rows name l)
  (if (endp rows) nil (cons (dg-exec-name l name (cadr (car rows))) (dg-exec-names (cdr rows) name l))))

(defun dg-logic-names (rows)
  (if (endp rows) nil (cons (cadddr (car rows)) (dg-logic-names (cdr rows)))))

(defun dg-export-rows (rows name l omit)
  (if (endp rows)
      nil
    (let ((r (car rows)))
      (cons `(,(cadr r) :logic ,(cadddr r) :exec ,(dg-exec-name l name (cadr r))
              ,@(and (assoc-eq (cadr r) omit)
                     (list :correspondence (adt-sym (cadr r) "{GUARDED-CORRESPONDENCE}")))
              ,@(if (eq (car r) :update) '(:protect t) nil))
            (dg-export-rows (cdr rows) name l omit)))))

; The obligations, as `defabsstobj-missing-events' states them (each named
; EXPORT{KIND}).  {preserved} first: it is the model's content and opens the
; recognizer; {correspondence} of an update export reads the export's own
; {preserved} (the new value is well-formed), and every other obligation is
; the unfolding of the execs, with the recognizer closed.
(defun dg-ob-prefix (ob)
  (let* ((s (symbol-name ob)) (i (position #\{ s))) (subseq s 0 i)))

(defun dg-ob-kind (ob)
  (let* ((s (symbol-name ob)) (i (position #\{ s))) (subseq s (+ i 1) (- (length s) 1))))

(defun dg-preserved-obs (missing)
  (cond ((endp missing) nil)
        ((equal (dg-ob-kind (car (car missing))) "PRESERVED")
         (cons (car (car missing)) (dg-preserved-obs (cdr missing))))
        (t (dg-preserved-obs (cdr missing)))))

 ; Explicit strengthening retains ACL2's exact guarded obligation under a
; generated companion name.  The public correspondence theorem has only
; the remaining premises.  Both are proved; no missing-event is bypassed.
(defun dg-drop-hyps (drops hyps)
 (cond ((endp drops) hyps)
       ((member-equal (car drops) hyps)
        (dg-drop-hyps (cdr drops) (remove-equal (car drops) hyps)))
       (t (er hard 'def-generic "Not an obligation hypothesis: ~x0" (car drops)))))
(defun dg-strengthen (term drops)
 (if (endp drops) term
  (if (and (consp term) (eq (car term) 'implies))
   (let* ((h (cadr term))
          (hs (if (and (consp h) (eq (car h) 'and)) (cdr h) (list h)))
          (kept (dg-drop-hyps drops hs)))
    (if (endp kept) (caddr term)
      (list 'implies (if (endp (cdr kept)) (car kept) (cons 'and kept)) (caddr term))))
   (er hard 'def-generic "Cannot remove hypotheses from ~x0" term))))

(defun dg-ob-thm (ob formula preserved hints-pre hints-unfold omit wrld)
  (let* ((k (dg-ob-kind ob))
         (pob (intern-in-package-of-symbol (concatenate 'string (dg-ob-prefix ob) "{PRESERVED}") ob))
         (hints (cond ((equal k "PRESERVED") hints-pre)
                      ((and (member-equal k '("CORRESPONDENCE" "GUARDED-CORRESPONDENCE")) (member-eq pob preserved))
                       `(("Goal" :use ((:instance ,pob))
                          :in-theory ,(cadr (cdr (car hints-unfold))))))
                      (t hints-unfold))))
    (let* ((term (untranslate formula t wrld))
           (export (intern-in-package-of-symbol (dg-ob-prefix ob) ob))
           (drops (cdr (assoc-eq export omit))))
      (if (equal k "GUARDED-CORRESPONDENCE")
          `(progn
             (defthm ,ob ,term :rule-classes nil :hints ,hints)
             (defthm ,(adt-sym export "{CORRESPONDENCE}")
               ,(dg-strengthen term drops) :rule-classes nil :hints ,hints-unfold))
        `(defthm ,ob ,term :rule-classes nil :hints ,hints)))))

(defun dg-ob-thms (missing pass preserved hints-pre hints-unfold omit wrld)
  ; PASS :pre emits the {preserved} obligations, :post the rest.
  (cond ((endp missing) nil)
        (t (let ((pre (equal (dg-ob-kind (car (car missing))) "PRESERVED")))
             (if (eq (eq pass :pre) pre)
                 (cons (dg-ob-thm (car (car missing)) (cadr (car missing)) preserved
                                  hints-pre hints-unfold omit wrld)
                       (dg-ob-thms (cdr missing) pass preserved hints-pre hints-unfold omit wrld))
               (dg-ob-thms (cdr missing) pass preserved hints-pre hints-unfold omit wrld))))))

(defun dg-all-ob-thms (missing hints-pre hints-unfold omit wrld)
  (let ((pres (dg-preserved-obs missing)))
    (append (dg-ob-thms missing :pre pres hints-pre hints-unfold omit wrld)
            (dg-ob-thms missing :post pres hints-pre hints-unfold omit wrld))))

(defun dg-events (name model rows lemmas disabled omit wrld)
  (let* ((l (adt-sym name "$L"))
         (items (adt-sym l "-ITEMS"))
         (upd (adt-sym-pre "UPDATE-" items))
         (lp (adt-sym l "P"))
         (wfp (adt-sym l "-WFP"))
         (lcorr (adt-sym name "$LCORR"))
         (recog (cadr (assoc-keyword :recognizer model)))
         (creator (cadr (assoc-keyword :creator model)))
         (create-l (adt-sym-pre "CREATE-" l))
         (execs (dg-exec-events rows name l items upd wfp wrld))
         (exec-names (dg-exec-names rows name l))
         (defabs
           `(defabsstobj ,name
              :foundation ,l
              :recognizer (,(adt-sym name "-P") :logic ,recog :exec ,lp)
              :creator (,(adt-sym-pre "CREATE-" name) :logic ,creator :exec ,create-l)
              :corr-fn ,lcorr
              :exports ,(dg-export-rows rows name l omit)
              :attachable t))
         (hints-pre `(("Goal" :in-theory (e/d (,wfp ,recog ,creator ,@(dg-logic-names rows) ,@lemmas)
                                             ,disabled))))
         (hints-unfold `(("Goal" :in-theory (e/d (,lcorr ,wfp ,items ,creator ,create-l ,@exec-names) ,disabled)))))
    `((defstobj ,l (,items :type t :initially nil) :inline t)
      (defun ,wfp (,l)
        (declare (xargs :stobjs ,l))
        (,recog (,items ,l)))
      (defun ,lcorr (,l a)
        (declare (xargs :stobjs ,l :verify-guards nil))
        (and (,recog a) (equal (,items ,l) a)))
      ,@execs
      (encapsulate
        ()
        (make-event
         (er-let* ((missing (defabsstobj-missing-events ,@(cdr defabs))))
           (value (cons 'progn (dg-all-ob-thms missing ',hints-pre ',hints-unfold ',omit (w state)))))))
      ,defabs
      (table fn-generated ',name
             '(:def-generic :model ,model :exports ,rows :lemmas ,lemmas :disable ,disabled :omit-hypotheses ,omit)))))

(defun def-generic-fn (name model rows lemmas disabled omit state)
  (declare (xargs :stobjs state))
  (let ((wrld (w state)) (ctx 'def-generic))
    (cond
     ((not (and (symbolp name) name (not (keywordp name))))
      (er soft ctx "the name must be a non-nil symbol; ~x0 is not." name))
     ((not (rep-model-ok model wrld))
      (er soft ctx "~x0: :model must be (:recognizer R :creator C) with R a unary and C a nullary function already in the world." name))
     ((not (and (consp rows) (dg-rows-ok name rows wrld)))
      (er soft ctx "~x0: :exports must be a non-empty list of (:read|:update NAME-SUFFIX :logic FN) with FN a function already in the world, of one result, whose last formal is not a stobj." name))
     ((not (no-duplicatesp-eq (strip-cadrs rows)))
      (er soft ctx "~x0: an export is named twice." name))
     ((not (and (symbol-listp lemmas) (rep-theorem-names-p lemmas wrld)))
      (er soft ctx "~x0: :lemmas must name theorems already proved." name))
     ((not (and (symbol-listp disabled) (rep-theorem-names-p disabled wrld)))
      (er soft ctx "~x0: :disable must name theorems already proved." name))
     (t (value `(progn ,@(dg-events name model rows lemmas disabled omit wrld)))))))

(defmacro def-generic (name &key model exports lemmas disable omit-hypotheses)
  `(make-event (def-generic-fn ',name ',model ',exports ',lemmas ',disable ',omit-hypotheses state)))

(logic)
