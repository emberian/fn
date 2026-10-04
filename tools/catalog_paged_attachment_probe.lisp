; Run in a world that has included catalog-paged-attach, using proof_repl
; send-file or the developer image's ACL2 session.  No include-book here:
; loading the generic before its attachment would ask a different question.
(in-package "ACL2")

(make-event
 (let* ((world (w state))
        (info (getpropc 'fn-cat 'absstobj-info nil world))
        (exports (cdr info)))
   (if (and (equal (car info) 'fn-cat$p)
            (equal (caddr (assoc-eq 'create-fn-cat exports)) 'create-fn-cat$p)
            (equal (get-stobj-creator 'fn-cat$p world) 'create-fn-cat$p)
            (equal (caddr (assoc-eq 'fn-cat-count exports)) 'fn-cat$p-count)
            (equal (caddr (assoc-eq 'fn-cat-at exports)) 'fn-cat$p-at)
            (equal (caddr (assoc-eq 'fn-cat-group-number exports)) 'fn-cat$p-group-number)
            (equal (caddr (assoc-eq 'fn-cat-msgid-seqs exports)) 'fn-cat$p-msgid-seqs)
            (equal (caddr (assoc-eq 'fn-cat-visible-at exports)) 'fn-cat$p-visible-at)
            (equal (caddr (assoc-eq 'fn-cat-commit exports)) 'fn-cat$p-commit-w)
            (equal (caddr (assoc-eq 'fn-cat-withdraw exports)) 'fn-cat$p-withdraw-w)
            (equal (symbol-class 'fn-cpa-smoke world) :common-lisp-compliant))
       (value '(value-triple :paged-catalog-metadata-passed))
     (er soft 'catalog-paged-attachment-probe
         "Expected guarded paged generic catalog; actual metadata: ~x0" info))))

(set-guard-checking t)

; The existing generic live stobj, including commit/withdraw/redecide and
; its reader effects, agrees with the same program on the logical model.
(assert-event
 (mv-let (result fn-cat) (fn-cpa-smoke fn-cat)
   (mv (equal result *cpa-expected*) fn-cat))
 :stobjs-out '(nil fn-cat))

; WITH-LOCAL-STOBJ must be inside a function.  This also exercises the
; selected generic creator, rather than only the pre-existing live object.
(defun fn-cpa-fresh-smoke-probe ()
  (declare (xargs :guard t))
  (with-local-stobj fn-cat
    (mv-let (result fn-cat) (fn-cpa-smoke fn-cat)
      (equal result *cpa-expected*))))

(assert-event (fn-cpa-fresh-smoke-probe))

(make-event
 (if (eq (symbol-class 'fn-cpa-fresh-smoke-probe (w state))
         :common-lisp-compliant)
     (value '(value-triple :paged-catalog-fresh-guarded-smoke-passed))
   (er soft 'catalog-paged-attachment-probe "Fresh creator smoke is not guard verified.")))
