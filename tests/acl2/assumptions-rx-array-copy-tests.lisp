(in-package "ACL2")
(include-book "../../books/assumptions-rx-array-copy")

; Executable local-witness teeth. These exercise a consistent conditional
; model, not Common Lisp REPLACE or a qualified receiver installation.
(assert-event
 (let* ((src '(1 2 3)) (dst '(8 9 10 11))
        (obs (fn-rxac-model-observe :source :destination src dst 1 2 t :registered :copied)))
  (and (fn-rxac-domain-p :source :destination src dst 1 2 t)
       (member-eq :copied '(:copied :not-invoked :uncertain))
       (fn-rxac-observation-contract-p obs :source :destination src dst 1 2 :registered :copied)
       (equal (nth 4 obs) '(1 2 10 11)) (equal (nth 5 obs) 2)
       (equal (len (fn-rxac-copy-prefix src dst 2)) (len dst))
       (equal (nthcdr 2 (fn-rxac-copy-prefix src dst 2)) (nthcdr 2 dst))
       (equal (nthcdr 2 (nth 4 obs)) '(10 11)))))

; Removal of the literal theorem's domain predicate; all other retained
; hypotheses hold. Aliased identities deliberately violate that domain.
(assert-event
 (let* ((src '(1 2 3)) (dst '(8 9 10 11))
        (obs (fn-rxac-model-observe :same :same src dst 1 2 t :registered :copied)))
  (and (member-eq :copied '(:copied :not-invoked :uncertain))
       (not (fn-rxac-domain-p :same :same src dst 1 2 t))
       (not (fn-rxac-observation-contract-p obs :same :same src dst 1 2 :registered :copied)))))

; Removal of the literal outcome-membership hypothesis, full domain retained.
(assert-event
 (let* ((src '(1 2 3)) (dst '(8 9 10 11))
        (obs (fn-rxac-model-observe :source :destination src dst 1 2 t :registered :alien)))
  (and (fn-rxac-domain-p :source :destination src dst 1 2 t)
       (not (member-eq :alien '(:copied :not-invoked :uncertain)))
       (not (fn-rxac-observation-contract-p obs :source :destination src dst 1 2 :registered :alien)))))

; Uncertain partial mutation is permitted, but quarantine is mandatory.
(assert-event
 (and (fn-rxac-domain-p :source :destination '(1 2 3) '(8 9 10 11) 1 2 t)
      (fn-rxac-observation-contract-p
       '(:uncertain :source :destination (1 2 3) (1 9 10 11) 2 4 :registered t)
       :source :destination '(1 2 3) '(8 9 10 11) 1 2 :registered :uncertain)
      (not (fn-rxac-observation-contract-p
       '(:uncertain :source :destination (1 2 3) (1 9 10 11) 2 4 :registered nil)
       :source :destination '(1 2 3) '(8 9 10 11) 1 2 :registered :uncertain))))

(assert-event
 (fn-rxac-observation-contract-p
  (fn-rxac-model-observe :source :destination '(1 2 3) '(8 9 10 11) 1 2 t :registered :not-invoked)
  :source :destination '(1 2 3) '(8 9 10 11) 1 2 :registered :not-invoked))
