; A book's theory scoped to the stobjs it reasons about. Each stobj's column
; generator (columns.lisp) proves facts keyed on NTH and LEN (and the
; layouts' on NATP, MV-NTH, ...) whose hypotheses name that stobj's
; recognizer or well-formedness predicate. In a world holding every kind's
; children, each NTH term then tries every stobj's facts and relieves each
; one's recognizer hypothesis by type-set: in commit-durable-all (58 stobjs,
; 1690 enabled rewrite rules and 1238 type prescriptions on NTH) that was a
; fifth of its proof time. (fn2-stobj-scope S...) disables those facts of
; every stobj but S..., read from the world, so a book names what it
; reasons about rather than listing what it does not.
(in-package "ACL2")

(defun fn2-scope-fn-stobj (fn wrld)
  ; the stobj a function belongs to: defstobj's own functions, or the first
  ; stobj among its inputs
  (declare (xargs :guard (and (symbolp fn) (plist-worldp wrld))))
  (or (getpropc fn 'stobj-function nil wrld)
      (let ((ins (getpropc fn 'stobjs-in nil wrld)))
        (and (true-listp ins)
             (car (remove-eq 'state (remove-eq nil ins)))))))
(defun fn2-scope-fns-stobjs (fns wrld)
  (declare (xargs :guard (and (symbol-listp fns) (plist-worldp wrld))))
  (if (endp fns) nil
    (let ((s (fn2-scope-fn-stobj (car fns) wrld)) (rest (fn2-scope-fns-stobjs (cdr fns) wrld)))
      (if (and s (symbolp s)) (add-to-set-eq s (if (symbol-listp rest) rest nil)) rest))))
(defun fn2-scope-rule-hyps (kind r)
  (declare (xargs :verify-guards nil))
  (case kind
    (:rewrite (access rewrite-rule r :hyps))
    (:type-prescription (access type-prescription r :hyps))
    (otherwise (access linear-lemma r :hyps))))
(defun fn2-scope-rule-rune (kind r)
  (declare (xargs :verify-guards nil))
  (case kind
    (:rewrite (access rewrite-rule r :rune))
    (:type-prescription (access type-prescription r :rune))
    (otherwise (access linear-lemma r :rune))))
(defun fn2-scope-out-runes (kind rules keep wrld)
  ; the runes among RULES whose hypotheses name a stobj outside KEEP
  (declare (xargs :verify-guards nil))
  (if (atom rules) nil
    (let ((rest (fn2-scope-out-runes kind (cdr rules) keep wrld))
          (hyps (fn2-scope-rule-hyps kind (car rules))))
      (if (and (pseudo-term-listp hyps)
               (set-difference-eq (fn2-scope-fns-stobjs (all-fnnames-lst hyps) wrld) keep))
          (cons (fn2-scope-rule-rune kind (car rules)) rest)
        rest))))
(defun fn2-scope-runes (fns keep wrld)
  (declare (xargs :verify-guards nil))
  (if (atom fns) nil
    (append (fn2-scope-out-runes :rewrite (getpropc (car fns) 'lemmas nil wrld) keep wrld)
            (fn2-scope-out-runes :type-prescription (getpropc (car fns) 'type-prescriptions nil wrld) keep wrld)
            (fn2-scope-out-runes :linear (getpropc (car fns) 'linear-lemmas nil wrld) keep wrld)
            (fn2-scope-runes (cdr fns) keep wrld))))
(defconst *fn2-scope-keys*
  ; the function symbols the column and layout facts are keyed on
  '(nth len natp mv-nth member-equal update-nth true-listp))
(defmacro fn2-stobj-scope (&rest keep)
  `(make-event
    (let ((runes (remove-duplicates-equal (fn2-scope-runes *fn2-scope-keys* ',keep (w state)))))
      (if runes (list 'in-theory (cons 'disable runes)) '(value-triple :fn2-stobj-scope-empty)))))
