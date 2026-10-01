; fn: `def-representation' --- an abstract stobj from one declaration of
; its schema, promoted from the prototype `defadt' (books/proto/adt.lisp,
; lane proto-adt 2026-09-27) for stage 1 of
; planning/design-store-representation-2026-10-01.md.
;
;   (def-representation NAME (FIELD KIND) ...
;     [:scalar t] [:generic t] [:invariant PRED :invariant-lemmas (L ...)])
;
; KIND is :u8 :u32 :u64 :bool :octets, (:nat B) or (:enum OBJ ...).  What
; `defadt' already generates, this generates (the foundation of typed
; columns and one octet pool, the executables, the bridges by functional
; instance and by unfolding, the obligations obtained from ACL2 itself by
; `defabsstobj-missing-events' and closed by one uniform hint, the
; `defabsstobj', the `-is-' meaning of each export); the prototype's
; generator function is reused, not copied.  Added here:
;
;   * the ATTACHMENT CHECK at expansion.  ACL2 refuses an abstract stobj
;     whose recognizer or correspondence has an attached ancestor
;     (:DOC stobj-attachment-restrictions); the tree learned that when the
;     catalog's recognizer reached `fn-digest' (books/catalog.lisp,
;     2026-09-27) and no book could include it beside crypto-attach.  Here
;     the ancestors of what the recognizer and correspondence will call
;     (the library's `adt-corr' and `adt-seq-p', and the :invariant) are
;     checked in the world BEFORE anything is generated, with
;     `canonical-ancestors-lst' and `attached-fns', the functions ACL2's
;     own check uses, and a reachable attachment is refused by name.
;   * `:invariant PRED', a unary predicate over the logical sequence
;     conjoined into the recognizer.  Its preservation is content, not
;     ceremony: the instance is refused unless `:invariant-lemmas' names
;     theorems already in the world, which the uniform hint enables for the
;     `{preserved}' obligations (PRED of the empty sequence, of an append
;     of a well-formed record, of a field update).
;   * `:scalar t', for a one-field schema: the logical value is the list of
;     the field's values (`adt-scalar-seq-p'), not of one-element records,
;     so a buffer of payloads has the arena's logical view
;     (books/payload-arena.lisp: `fn-arn-payload-listp', `len', `nth',
;     `append').  The exports are NAME-count, NAME-get, NAME-set,
;     NAME-append.
;   * `:generic t': the columnar instance is emitted as NAME-cols, then
;     `(attach-stobj NAME NAME-cols)', then NAME itself as an ATTACHABLE
;     generic over a LIST foundation (one field holding the logical value,
;     every :exec a total list operation from
;     books/def-representation-lib.lisp), with the same :logic functions
;     and the same export skeleton, so that a book certified against NAME
;     is included unchanged under the attachment (the pattern of
;     books/payload-arena.lisp and payload-arena-attach.lisp, generated).
;
; Every generated name is derived from NAME (`NAME$c', `NAME$a', `NAME$ap',
; `NAME$corr', `NAME-count', `NAME-get-FIELD', ...; `NAME$l' for the list
; foundation) and the instance is recorded in the world table
; `fn-generated'.  Malformed input is refused at expansion with a soft
; error naming the check.  Nothing of the library is left enabled by an
; instance beyond what `defadt' leaves.

(in-package "ACL2")
(include-book "proto/adt")
(include-book "def-representation-lib")

(program)

; -----------------------------------------------------------------------------
; The scalar instance: one field, the logical value is the list of values.
; The foundation and its executables are the prototype's (one record of one
; field); only the logical side and the correspondence differ, and the
; obligations are closed by the library's wrap lemmas.

(defun rep-scalar-events (name fields invariant invariant-lemmas)
  (let* ((kind (cadr (car fields)))
         (schema-const (adt-sym3 '* (symbol-name name) '-schema*))
         (cols (adt-columns name fields))
         (p (len cols))
         (st (adt-sym name "$C"))
         (a (adt-sym name "$A"))
         (ap (adt-sym name "$AP"))
         (corr (adt-sym name "$CORR"))
         (count-of (adt-sym name "$C-COUNT-OF"))
         (append-c (adt-sym name "$C-APPEND"))
         (append-a (adt-sym name "$A-APPEND"))
         (count-a (adt-sym name "$A-COUNT"))
         (get-a (adt-sym name "$A-GET"))
         (set-a (adt-sym name "$A-SET"))
         (get-c (adt-sym3 name "$C-GET-" (car (car fields))))
         (set-c (adt-sym3 name "$C-SET-" (car (car fields))))
         (create-a (adt-sym "CREATE-" (symbol-name a)))
         (create-c (adt-sym "CREATE-" (symbol-name st)))
         (recog (adt-sym name "P"))
         (append-c1 (adt-sym name "$C-APPEND1"))
         (clear-a (adt-sym name "$A-CLEAR"))
         (clear-c (adt-sym name "$C-CLEAR"))
         (defabs
           `(defabsstobj ,name
              :foundation ,st
              :recognizer (,recog :logic ,ap :exec ,(adt-sym name "$CP"))
              :creator (,(adt-sym "CREATE-" (symbol-name name)) :logic ,create-a :exec ,create-c)
              :corr-fn ,corr
              :corr-fn-exists t
              :exports ((,(adt-sym name "-COUNT") :logic ,count-a :exec ,count-of)
                        (,(adt-sym name "-GET") :logic ,get-a :exec ,get-c)
                        (,(adt-sym name "-SET") :logic ,set-a :exec ,set-c :protect t)
                        (,(adt-sym name "-APPEND") :logic ,append-a :exec ,append-c1 :protect t)
                        (,(adt-sym name "-CLEAR") :logic ,clear-a :exec ,clear-c :protect t))))
         (ob-hints `(("Goal" :in-theory (enable ,corr ,ap ,create-a ,count-a ,append-a ,get-a ,set-a
                                                 ,clear-a ,append-c1 adt-scalar-seq-p adt-val-okp
                                                 ,@invariant-lemmas)))))
    `(encapsulate
       ()
       (local (in-theory (disable nth update-nth resize-list)))
       ,@(adt-foundation-events name fields schema-const nil (+ 3 p))
       (defthm ,(adt-sym create-c "-IS-CANONICAL-EMPTY")
         (equal (,create-c) (adt-empty-c ,schema-const))
         :hints (("Goal" :in-theory (enable adt-empty-c))))
       ; The one-record append, over the field value.
       (defun ,append-c1 (v ,st)
         (declare (xargs :stobjs ,st :guard (adt-val-okp ',kind v)
                         :guard-hints (("Goal" :in-theory (enable adt-rec-p-of-list1)))))
         (,append-c (list v) ,st))
       ; The logical side: the list of values.
       (defun ,ap (,a)
         (declare (xargs :guard t))
         (and (adt-scalar-seq-p ',kind ,a)
              ,@(if invariant `((,invariant ,a)) nil)))
       (defun ,create-a ()
         (declare (xargs :guard t))
         nil)
       (defun ,count-a (,a)
         (declare (xargs :guard (,ap ,a)))
         (len ,a))
       (defun ,get-a (i ,a)
         (declare (xargs :guard (and (,ap ,a) (natp i) (< i (,count-a ,a)))))
         (nth i ,a))
       (defun ,set-a (i v ,a)
         (declare (xargs :guard (and (,ap ,a) (natp i) (< i (,count-a ,a)) (adt-val-okp ',kind v))))
         (update-nth i v ,a))
       (defun ,append-a (v ,a)
         (declare (xargs :guard (and (,ap ,a) (adt-val-okp ',kind v))))
         (append ,a (list v)))
       (defun ,clear-a (,a)
         (declare (xargs :guard (,ap ,a)) (ignore ,a))
         nil)
       (defun ,corr (c a)
         (declare (xargs :guard t :verify-guards nil))
         (adt-corr ,schema-const c (adt-wrap1 a)))
       (make-event
        (er-let* ((missing (defabsstobj-missing-events ,@(cdr defabs))))
          (value (cons 'progn (adt-obligation-thms missing ',ob-hints (w state))))))
       ,defabs
       (defthm ,(adt-sym name "-COUNT-IS-LEN")
         (equal (,(adt-sym name "-COUNT") ,name) (len ,name))
         :hints (("Goal" :in-theory (enable ,count-a))))
       (defthm ,(adt-sym name "-GET-IS-NTH")
         (equal (,(adt-sym name "-GET") i ,name) (nth i ,name))
         :hints (("Goal" :in-theory (enable ,get-a))))
       (defthm ,(adt-sym name "-SET-IS-UPDATE-NTH")
         (equal (,(adt-sym name "-SET") i v ,name) (update-nth i v ,name))
         :hints (("Goal" :in-theory (enable ,set-a))))
       (defthm ,(adt-sym name "-APPEND-IS-APPEND")
         (equal (,(adt-sym name "-APPEND") v ,name) (append ,name (list v)))
         :hints (("Goal" :in-theory (enable ,append-a))))
       (defthm ,(adt-sym name "-CLEAR-IS-NIL")
         (equal (,(adt-sym name "-CLEAR") ,name) nil)
         :hints (("Goal" :in-theory (enable ,clear-a))))
       (defthm ,(adt-sym recog "-IS-SCALAR-SEQ-P")
         (equal (,recog x) (and (adt-scalar-seq-p ',kind x)
                                ,@(if invariant `((,invariant x)) nil)))
         :hints (("Goal" :in-theory (enable ,ap)))))))

; -----------------------------------------------------------------------------
; The generic over a list foundation, attached to the columnar instance.
; IMPL is the columnar instance's name (NAME-cols); its logical functions
; are the generic's.  EXPORTS are (export-name logic-fn exec-kind . args)
; rows computed from the schema: the exec of each is a total list
; operation over the one field.

(defun rep-l-field-execs (l items upd fields j)
  (if (endp fields)
      nil
    (let ((f (car (car fields))))
      (list* `(defun ,(adt-sym3 l "-GET-" f) (i ,l)
                (declare (xargs :stobjs ,l))
                (adt-l-nth ,j (adt-l-nth i (,items ,l))))
             `(defun ,(adt-sym3 l "-SET-" f) (i v ,l)
                (declare (xargs :stobjs ,l))
                (,upd (adt-l-update-nth i (adt-l-update-nth ,j v (adt-l-nth i (,items ,l)))
                                        (,items ,l))
                      ,l))
             (rep-l-field-execs l items upd (cdr fields) (+ 1 j))))))

(defun rep-l-exec-events (name fields scalar)
  ; The :exec functions of the list foundation, each :guard t.
  (let* ((l (adt-sym name "$L"))
         (items (adt-sym l "-ITEMS"))
         (upd (adt-sym "UPDATE-" (symbol-name items))))
    (append
     `((defun ,(adt-sym l "-COUNT") (,l)
         (declare (xargs :stobjs ,l))
         (len (,items ,l)))
       (defun ,(adt-sym l "-APPEND") (rec ,l)
         (declare (xargs :stobjs ,l))
         (,upd (adt-l-snoc (,items ,l) rec) ,l))
       (defun ,(adt-sym l "-CLEAR") (,l)
         (declare (xargs :stobjs ,l))
         (,upd nil ,l)))
     (if scalar
         `((defun ,(adt-sym l "-GET") (i ,l)
             (declare (xargs :stobjs ,l))
             (adt-l-nth i (,items ,l)))
           (defun ,(adt-sym l "-SET") (i v ,l)
             (declare (xargs :stobjs ,l))
             (,upd (adt-l-update-nth i v (,items ,l)) ,l)))
       (rep-l-field-execs l items upd fields 0)))))


(defun rep-generic-field-exports (name impl l fields)
  (if (endp fields)
      nil
    (let ((f (car (car fields))))
      (list* `(,(adt-sym3 name "-GET-" f) :logic ,(adt-sym3 impl "$A-GET-" f)
               :exec ,(adt-sym3 l "-GET-" f))
             `(,(adt-sym3 name "-SET-" f) :logic ,(adt-sym3 impl "$A-SET-" f)
               :exec ,(adt-sym3 l "-SET-" f) :protect t)
             (rep-generic-field-exports name impl l (cdr fields))))))

(defun rep-generic-exports (name impl fields scalar)
  ; In the implementation's order: `attach-stobj' matches the two export
  ; lists positionally.
  (let ((l (adt-sym name "$L")))
    (if scalar
        `((,(adt-sym name "-COUNT") :logic ,(adt-sym impl "$A-COUNT") :exec ,(adt-sym l "-COUNT"))
          (,(adt-sym name "-GET") :logic ,(adt-sym impl "$A-GET") :exec ,(adt-sym l "-GET"))
          (,(adt-sym name "-SET") :logic ,(adt-sym impl "$A-SET") :exec ,(adt-sym l "-SET")
           :protect t)
          (,(adt-sym name "-APPEND") :logic ,(adt-sym impl "$A-APPEND") :exec ,(adt-sym l "-APPEND")
           :protect t)
          (,(adt-sym name "-CLEAR") :logic ,(adt-sym impl "$A-CLEAR") :exec ,(adt-sym l "-CLEAR")
           :protect t))
      `((,(adt-sym name "-COUNT") :logic ,(adt-sym impl "$A-COUNT") :exec ,(adt-sym l "-COUNT"))
        (,(adt-sym name "-APPEND") :logic ,(adt-sym impl "$A-APPEND") :exec ,(adt-sym l "-APPEND")
         :protect t)
        ,@(rep-generic-field-exports name impl l fields)
        (,(adt-sym name "-CLEAR") :logic ,(adt-sym impl "$A-CLEAR") :exec ,(adt-sym l "-CLEAR")
         :protect t)))))


(defun rep-logic-names (impl fields scalar)
  (if scalar
      (list (adt-sym impl "$A-GET") (adt-sym impl "$A-SET"))
    (adt-logic-names impl fields)))

(defun rep-generic-events (name impl fields scalar)
  (let* ((l (adt-sym name "$L"))
         (items (adt-sym l "-ITEMS"))
         (lp (adt-sym l "P"))
         (lcorr (adt-sym name "$LCORR"))
         (ap (adt-sym impl "$AP"))
         (create-a (adt-sym "CREATE-" (symbol-name (adt-sym impl "$A"))))
         (create-l (adt-sym "CREATE-" (symbol-name l)))
         (recog (adt-sym name "P"))
         (execs (rep-l-exec-events name fields scalar))
         (exec-names (strip-cadrs execs))
         (defabs
           `(defabsstobj ,name
              :foundation ,l
              :recognizer (,recog :logic ,ap :exec ,lp)
              :creator (,(adt-sym "CREATE-" (symbol-name name)) :logic ,create-a :exec ,create-l)
              :corr-fn ,lcorr
              :exports ,(rep-generic-exports name impl fields scalar)
              :attachable t))
         (ob-hints `(("Goal" :in-theory (enable ,lcorr ,ap ,create-a ,create-l
                                                 ,(adt-sym impl "$A-COUNT") ,(adt-sym impl "$A-APPEND")
                                                 ,(adt-sym impl "$A-CLEAR")
                                                 ,@(rep-logic-names impl fields scalar)
                                                 ,@exec-names ,items
                                                 adt-set-a adt-scalar-seq-p)))))
    `((defstobj ,l (,items :type t :initially nil) :inline t)
      (defun ,lcorr (,l a)
        (declare (xargs :stobjs ,l :verify-guards nil))
        (and (,ap a) (equal (,items ,l) a)))
      ,@execs
      (encapsulate
        ()
        (local (in-theory (disable nth update-nth)))
        (make-event
         (er-let* ((missing (defabsstobj-missing-events ,@(cdr defabs))))
           (value (cons 'progn (adt-obligation-thms missing ',ob-hints (w state)))))))
      (attach-stobj ,name ,impl)
      ,defabs)))

; -----------------------------------------------------------------------------
; The attachment check and the form.

(defun rep-attached-ancestors (fns wrld)
  ; The functions among the ancestors of FNS (the functions the recognizer
  ; and correspondence will call) that have an attachment: what
  ; `defabsstobj' would refuse, found before anything is generated.
  (attached-fns (canonical-ancestors-lst fns wrld) wrld))

(defun rep-theorem-names-p (names wrld)
  (cond ((atom names) (null names))
        ((and (symbolp (car names)) (getpropc (car names) 'theorem nil wrld))
         (rep-theorem-names-p (cdr names) wrld))
        (t nil)))

; The prototype's naming helpers have other callers and intentionally use
; ACL2.  Relocate only NAME-derived symbols in this generator's output.
; Expand the same schema with a second name to identify those occurrences:
; library symbols, field names, enum values and supplied invariant lemmas
; are identical in both expansions, even when their spelling resembles NAME.
; This also covers the prototype-generated foundation without copying it.
(defun rep-package-events (events probe name)
  (cond ((and (consp events) (consp probe))
         (cons (rep-package-events (car events) (car probe) name)
               (rep-package-events (cdr events) (cdr probe) name)))
        ((and (symbolp events) (symbolp probe) (not (eq events probe)))
         (intern-in-package-of-symbol (symbol-name events) name))
        (t events)))

(defun rep-instance-events (name fields0 scalar generic invariant invariant-lemmas)
  (let* ((fields (adt-norm-fields fields0))
         (impl (if generic (adt-sym name "-COLS") name))
         (instance (if scalar
                       (rep-scalar-events impl fields invariant invariant-lemmas)
                     (defadt-fn impl fields0))))
    `(progn
       ,instance
       ,@(if generic (rep-generic-events name impl fields scalar) nil)
       (table fn-generated ',name
              '(:def-representation :scalar ,scalar :generic ,generic
                :implementation ,impl :invariant ,invariant)))))

(defun rep-named-events (name fields0 scalar generic invariant invariant-lemmas)
  (rep-package-events
   (rep-instance-events name fields0 scalar generic invariant invariant-lemmas)
   (rep-instance-events
    (intern-in-package-of-symbol
     (concatenate 'string (symbol-name name) "-REP-PACKAGE-PROBE") name)
    fields0 scalar generic invariant invariant-lemmas)
   name))

(defun def-representation-fn (name fields0 scalar generic invariant invariant-lemmas state)
  (declare (xargs :stobjs state))
  (let* ((wrld (w state))
         (ctx 'def-representation)
         (fields (adt-norm-fields fields0))
         (roots (append '(adt-corr adt-seq-p adt-scalar-seq-p)
                        (if invariant (list invariant) nil)))
         (attached (and (symbol-listp roots) (rep-attached-ancestors roots wrld))))
    (cond
     ((not (and (symbolp name) name))
      (er soft ctx "the name must be a non-nil symbol; ~x0 is not." name))
     ((or (atom fields) (not (adt-schemap (adt-schema-of fields))))
      (er soft ctx "~x0: the fields must be a non-empty list of (FIELD KIND) with KIND one of :u8 :u32 :u64 :bool :octets (:nat B) (:enum ...); ~x1 is not." name fields0))
     ((and scalar (not (equal (len fields) 1)))
      (er soft ctx "~x0: :scalar t needs exactly one field; ~x1 were given." name (len fields)))
     ((and invariant (not (and (symbolp invariant) (function-symbolp invariant wrld)
                                (equal (arity invariant wrld) 1))))
      (er soft ctx "~x0: :invariant ~x1 must be a unary function in the world." name invariant))
     (attached
      (er soft ctx "~x0: the recognizer or correspondence would reach ~&1, which ~#1~[has~/have~] an attachment; ACL2 refuses such an abstract stobj (:DOC stobj-attachment-restrictions).  Carry that part of the invariant beside the stobj (def-carried), not in it." name attached))
     ((and invariant (not (and invariant-lemmas (rep-theorem-names-p invariant-lemmas wrld))))
      (er soft ctx "~x0: :invariant ~x1 needs :invariant-lemmas naming theorems already proved (of the empty sequence, of an append, of a field update); ~x2 does not." name invariant invariant-lemmas))
     ((and invariant (not scalar))
      (er soft ctx "~x0: :invariant is supported with :scalar t in this stage." name))
     (t
      (value (rep-named-events name fields0 scalar generic invariant invariant-lemmas))))))

(defun rep-fields-of (args)
  (if (or (endp args) (keywordp (car args)))
      nil
    (cons (car args) (rep-fields-of (cdr args)))))

(defmacro def-representation (name &rest args)
  ; Fields come first; the keyword options after them.
  (let* ((fields (rep-fields-of args))
         (opts (nthcdr (len fields) args)))
    `(make-event
      (def-representation-fn ',name ',fields
        ',(cadr (assoc-keyword :scalar opts))
        ',(cadr (assoc-keyword :generic opts))
        ',(cadr (assoc-keyword :invariant opts))
        ',(cadr (assoc-keyword :invariant-lemmas opts))
        state))))


(logic)
