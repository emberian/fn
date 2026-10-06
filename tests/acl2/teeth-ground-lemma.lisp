; teeth-ground-lemma: the ground theorem a defteeth witness cites with
; `:witness-lemma' or an entry's `:lemma' (books/defkeystone.lisp, WITNESS
; MODES), for a claim a predicate no evaluator runs (a defun-sk such as
; fn-bs-crash-imagep) takes part in.
;
;   (defconst *K* '(((L1 H1) ... (Ln Hn)) C))        ; the :claim, once
;   (teeth-ground-lemma NAME *K* ((VAR VAL) ...) [:without Li | :mutation EDIT]
;     [:suff (S IMAGE CHOICES)] [:keystone THM] [:hints H])
;
; defines NAME, a theorem whose formula is what defteeth demands: the claim
; translated and instantiated at the bindings, as the conjunction
; (and H1 .. Hn C) for the positive witness and (and RETAINED.. (not Hi)
; (not C)) under :without Li, (and H1 .. Hn C (not C2)) under :mutation
; (:conclusion C2) (fn-dk-witness-event, fn-dk-mutant-witness-terms).  The proof is the caller's
; hints; a removal of the defun-sk's own hypothesis follows from the keystone
; itself (the retained hypotheses and the failed conclusion leave no image).
(in-package "ACL2")
(include-book "../../books/defkeystone")

(defun tgl-const-value (sym w)
  (declare (xargs :mode :program))
  (let ((q (getpropc sym 'const nil w)))
    (if (and (consp q) (eq (car q) 'quote)) (cadr q) q)))

(defun tgl-index (label labels i)
  (declare (xargs :mode :program))
  (cond ((atom labels) nil)
        ((eq label (car labels)) i)
        (t (tgl-index label (cdr labels) (1+ i)))))

(defun tgl-terms (claim without mutation)
  (declare (xargs :mode :program))
  (let ((hyps (fn-dk-claim-hyps claim))
        (concl (fn-dk-claim-concl claim)))
    (cond (mutation (fn-dk-mutant-witness-terms claim mutation))
          (without
           (let ((i (tgl-index without (fn-dk-claim-labels claim) 0)))
             (append (fn-dk-without i hyps)
                     (list `(not ,(nth i hyps)) `(not ,concl)))))
          (t (append hyps (list concl))))))

; The proof: SUFF = (S IMAGE CHOICES) instantiates fn-bs-crash-imagep-suff
; (the image the choices make); KEYSTONE = the theorem itself at the bindings
; (an image the retained hypotheses and the failed conclusion leave none).
(defun tgl-hints (suff keystone bindings hints)
  (declare (xargs :mode :program))
  (let ((uses (append (and suff
                           `((:instance fn-bs-crash-imagep-suff
                                        (s ,(nth 0 suff)) (image ,(nth 1 suff))
                                        (choices ,(nth 2 suff)))))
                      (and keystone `((:instance ,keystone ,@bindings))))))
    (cond (hints hints)
          (uses `(("Goal" :use ,uses)))
          (t nil))))

(defmacro teeth-ground-lemma (name const bindings &key without mutation suff keystone hints)
  `(make-event
    (let* ((claim (tgl-const-value ',const (w state))))
      (mv-let (bad term)
        (fn-dt-translate (fn-dk-conj (tgl-terms claim ',without ',mutation)) (w state))
        (mv-let (badb alist) (fn-dt-bindings-alist ',bindings (w state))
          (if (or bad badb)
              (er soft 'teeth-ground-lemma "~x0 does not translate" ',name)
            (let ((h (tgl-hints ',suff ',keystone ',bindings ',hints)))
              (value `(defthm ,',name ,(fn-dt-subst term alist)
                        :rule-classes nil
                        ,@(and h (list :hints h)))))))))))

; A ground fixture computed once: (defconst-eval *NAME* FORM) is (defconst
; *NAME* 'VALUE) with VALUE what FORM evaluates to.  A ground lemma over the
; constant lets the prover compute with literals; over the evaluation of a
; whole run (a host run, a recovery) it rewrites without end.
(defmacro defconst-eval (name form)
  `(make-event
    (mv-let (erp val state)
      (trans-eval ',form 'defconst-eval state t)
      (if (or erp (not (consp val)))
          (er soft 'defconst-eval "~x0 did not evaluate" ',form)
        (value `(defconst ,',name ',(cdr val)))))))
