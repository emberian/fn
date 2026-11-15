; Focused shared constructor controls: TYPE/WFP are independent proof options.
(in-package "ACL2")
(include-book "../books/columns-carrier-contracts")

(defcolumns fn2-carrier-hint-table ((value :u60)))
(defun fn2-carrier-hint-identity (fn2-carrier-hint-table)
 (declare (xargs :stobjs fn2-carrier-hint-table
                 :guard (fn2-carrier-hint-table-wfp fn2-carrier-hint-table)))
 fn2-carrier-hint-table)

(assert-event
 (let* ((world (w state))
        (name 'fn2-carrier-hint-identity)
        (type-hints '(("Goal" :in-theory (enable fn2-carrier-hint-identity)
                              :do-not '(generalize))))
        (wfp-hints '(("Goal" :in-theory (enable fn2-carrier-hint-identity)
                             :do-not '(fertilize))))
        (outer '(("Goal" :do-not '(eliminate-destructors))))
        (plain (fn2-columns-guarded-contract-events name
                 '((fn2-carrier-hint-table nil)) outer nil world))
        (events (fn2-columns-guarded-contract-events name
                  (list (list 'fn2-carrier-hint-table nil :type-hints type-hints :hints wfp-hints))
                  outer nil world))
        (without (fn2-columns-guarded-contract-events name
                   (list (list 'fn2-carrier-hint-table nil :type-hints nil :hints wfp-hints))
                   outer nil world)))
  (and
   (equal (fn2-decl-get :hints (cdddr (cadr events))) type-hints)
   (equal (fn2-decl-get :hints (cdddr (caddr events))) wfp-hints)
   (equal (fn2-decl-get :hints (cdddr (cadr plain))) outer)
   (equal (fn2-decl-get :hints (cdddr (caddr plain))) outer)
   (not (member-eq :hints (cdddr (cadr without))))
   ; The whole generated H and output predicate/projection stay identical.
   (equal (take 3 (cadr plain)) (take 3 (cadr events)))
   (equal (take 3 (caddr plain)) (take 3 (caddr events)))
   (equal (take 3 (cadr plain)) (take 3 (cadr without))))))

; Actual admission uses the same public constructor on registered metadata.
(defcolumns-guarded-contracts fn2-carrier-hint-identity
 :carriers ((fn2-carrier-hint-table nil
             :type-hints (("Goal" :in-theory (enable fn2-carrier-hint-identity)
                                   :do-not '(generalize)))
             :hints (("Goal" :in-theory (enable fn2-carrier-hint-identity)
                              :do-not '(fertilize)))))
 :hints (("Goal" :do-not '(eliminate-destructors))))

; Actual low-level expansion keeps absent and explicit NIL distinct for WFP,
; including custom invariant names, direct output and MV zero projections.
(assert-event
 (let* ((outer '(("Goal" :use caller-fact)))
        (absent (fn2-columns-carrier-specs
                  '((left nil :prefix "-L") (right 0 :invariant right-shape :suffix "-SHAPE"))))
        (explicit (fn2-columns-carrier-specs
                    '((left nil :prefix "-L" :hints nil)
                      (right 0 :invariant right-shape :suffix "-SHAPE" :hints nil))))
        (a (fn2-columns-preservation-facts 'subject '(subject left right) absent '((whole-hyp left right)) outer))
        (e (fn2-columns-preservation-facts 'subject '(subject left right) explicit '((whole-hyp left right)) outer)))
  (and (equal (fn2-decl-get :hints (cdddr (cadr a))) outer)
       (equal (fn2-decl-get :hints (cdddr (cadddr a))) outer)
       (not (member-eq :hints (cdddr (cadr e))))
       (not (member-eq :hints (cdddr (cadddr e))))
       (equal (take 3 (cadr a)) (take 3 (cadr e)))
       (equal (take 3 (cadddr a)) (take 3 (cadddr e)))
       (equal (caddr (cadddr a))
              '(implies (and (whole-hyp left right))
                        (right-shape (car (subject left right))))))))
