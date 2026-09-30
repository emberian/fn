; Actual register source roster joined to a conditional standalone object family.
(in-package "ACL2")
(include-book "decoded-window-initial-write-domains")
(include-book "assumptions-selected-runtime-initializer-register")
(defun-nx fn-pir-object-octets (roster coordinate)
 (if (atom roster) 0
  (+ (fn-assume-srir-primary-object-octets (caar roster) (cadar roster) coordinate)
     (fn-pir-object-octets (cdr roster) coordinate))))
(defthm fn-pir-qualified-register-roster-primary-objects
 (implies (and (fn-piw-register-write-domainp roster)
               (equal coordinate *fn-srir-coordinate*))
  (equal (fn-pir-object-octets roster coordinate) 0))
 :rule-classes nil
 :hints (("Goal" :induct (fn-pir-object-octets roster coordinate)
  :in-theory (enable fn-pir-object-octets fn-piw-register-write-domainp fn-srir-domain-p))
 ("Subgoal *1/2" :use (:instance fn-assume-srir-qualified-primary-object-bound
      (i (caar roster)) (v (cadar roster)) (c coordinate)))))
(defthm fn-pir-actual-begin-register-objects-conditional
 (implies (equal coordinate *fn-srir-coordinate*)
  (equal (fn-pir-object-octets
    (fn-piw-register-write-roster
      (cdr (fn-piw-pwz-begin token incarnation hash zin win tab out))) coordinate) 0))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
  :use (fn-piw-actual-begin-register-write-domain
        (:instance fn-pir-qualified-register-roster-primary-objects
          (roster (fn-piw-register-write-roster
                    (cdr (fn-piw-pwz-begin token incarnation hash zin win tab out))))))
  :in-theory (disable fn-piw-pwz-begin fn-piw-register-write-roster
     fn-piw-register-write-domainp fn-pir-object-octets (:e fn-piw-pwz-begin)))))
; Comparing this coordinate does not install genuine backing/HONS/caller facts.
(defun fn-pir-initial-register-primary-component (coordinate)
 (declare (xargs :guard t))
 (if (equal coordinate *fn-srir-coordinate*)
  (mv :primary-object 0 0) (mv :unavailable nil nil)))
(defthm fn-pir-actual-begin-register-primary-object-boundary
 (let* ((o (fn-piw-pwz-begin token incarnation hash zin win tab out))
        (roster (fn-piw-register-write-roster (cdr o))))
  (and (equal (car o) (fn-pwz-begin token incarnation hash zin win tab out))
       (equal roster (append (fn-piw-reset-register-roster 0)
         (list '(19 0) '(11 1) (list 18 (min (len (fn-pwz-dictionary token)) 32768)))))
       (fn-piw-register-write-domainp roster)
       (implies (equal coordinate *fn-srir-coordinate*)
                (equal (fn-pir-object-octets roster coordinate) 0))))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
  :use (fn-piw-pwz-begin-value-and-effects-projection
        fn-piw-begin-exact-register-write-roster
        fn-piw-actual-begin-register-write-domain
        fn-pir-actual-begin-register-objects-conditional)
  :in-theory (disable fn-piw-pwz-begin fn-pwz-begin fn-piw-register-write-roster
   fn-piw-register-write-domainp fn-piw-reset-register-roster fn-pir-object-octets
   fn-pwz-dictionary (:e fn-piw-pwz-begin) (:e fn-pwz-begin) (:e fn-pwz-dictionary)))))
