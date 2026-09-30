(in-package "ACL2")
(include-book "../../books/decoded-window-initial-register-objects")
(defmacro pir-complete-register-family (token)
 `(let* ((o (fn-piw-pwz-begin ,token 301 (create-pgs-digest-state)
                (create-fn-zin-st) nil nil nil))
         (roster (fn-piw-register-write-roster (cdr o))))
  (and (equal (car o) (fn-pwz-begin ,token 301 (create-pgs-digest-state)
                          (create-fn-zin-st) nil nil nil))
       (equal roster (append (fn-piw-reset-register-roster 0)
         (list '(19 0) '(11 1) (list 18 (min (len (fn-pwz-dictionary ,token)) 32768)))))
       (fn-piw-register-write-domainp roster)
       (implies (equal coordinate *fn-srir-coordinate*)
                (equal (fn-pir-object-octets roster coordinate) 0)))))
(defthm pir-literal-empty-actual-complete-family-positive
 (let ((token '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 0)))
  (and (fn-pwz-tokenp token) (pir-complete-register-family token)))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
  :use (:instance fn-pir-actual-begin-register-primary-object-boundary
    (token '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 0))
    (incarnation 301) (hash (create-pgs-digest-state)) (zin (create-fn-zin-st))
    (win nil) (tab nil) (out nil))
  :in-theory (disable fn-piw-pwz-begin fn-pwz-begin fn-piw-register-write-roster
   fn-piw-register-write-domainp fn-pir-object-octets fn-pwz-dictionary
   (:e fn-piw-pwz-begin) (:e fn-pwz-begin) (:e fn-pwz-dictionary)))))
(defthm pir-literal-shipped-actual-complete-family-positive
 (let ((token '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 2220533217)))
  (and (fn-pwz-tokenp token) (pir-complete-register-family token)))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
  :use (:instance fn-pir-actual-begin-register-primary-object-boundary
    (token '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 2220533217))
    (incarnation 301) (hash (create-pgs-digest-state)) (zin (create-fn-zin-st))
    (win nil) (tab nil) (out nil))
  :in-theory (disable fn-piw-pwz-begin fn-pwz-begin fn-piw-register-write-roster
   fn-piw-register-write-domainp fn-pir-object-octets fn-pwz-dictionary
   (:e fn-piw-pwz-begin) (:e fn-pwz-begin) (:e fn-pwz-dictionary)))))
; Candidate selectors do not install the named runtime coordinate.
(defthm pir-literal-qualified-candidate-and-unavailable-coordinate
 (and (equal (fn-pir-initial-register-primary-component *fn-srir-coordinate*)
             '(:primary-object 0 0))
      (equal (fn-pir-initial-register-primary-component '(:shape-only vector20))
             '(:unavailable nil nil))
      (not (equal (fn-pir-initial-register-primary-component '(:shape-only vector20))
                  '(:primary-object 0 0))))
 :rule-classes nil)
; Labelled source-argument/count mutations, not whole initializer prices.
(defthm pir-literal-register-domain-and-count-mutations
 (and (fn-srir-domain-p 18 32768 *fn-srir-coordinate*)
      (not (fn-srir-domain-p 20 0 *fn-srir-coordinate*))
      (not (fn-srir-domain-p 18 32769 *fn-srir-coordinate*))
      (equal (len (append (fn-piw-reset-register-roster 0) '((19 0) (11 1) (18 0)))) 21)
      (not (equal (len (append (fn-piw-reset-register-roster 0) '((19 0) (11 1) (18 0)))) 20))
      (not (fn-srir-domain-p 18 0 '(:shape-only vector20))))
 :rule-classes nil)
