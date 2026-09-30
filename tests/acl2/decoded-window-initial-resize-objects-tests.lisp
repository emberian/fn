(in-package "ACL2")
(include-book "../../books/decoded-window-initial-resize-objects")
(include-book "decoded-window-initial-buffer-refinement-tests")
(defmacro pibr-full-boundary (token cw ct co coordinate)
 `(let* ((o (fn-pib-piwc-begin ,token 301 (create-pgs-digest-state)
                  (create-fn-zin-st) ,cw ,ct ,co))
         (r (car o)) (roster (fn-pibr-request-roster (cdr o)))
         (a (fn-pwz-begin ,token 301 (create-pgs-digest-state)
                         (create-fn-zin-st) nil nil nil)))
  (and (equal (mv-nth 0 r) (mv-nth 0 a))
       (equal (mv-nth 1 r) (mv-nth 1 a))
       (equal (mv-nth 2 r) (mv-nth 2 a))
       (fn-octets$corr (mv-nth 3 r) (mv-nth 3 a))
       (fn-octets$corr (mv-nth 4 r) (mv-nth 4 a))
       (fn-octets$corr (mv-nth 5 r) (mv-nth 5 a))
       (equal roster (fn-pibr-initial-request-roster
          (fn-octets$c-buf-length ,cw) (fn-octets$c-buf-length ,ct)
          (fn-octets$c-buf-length ,co)))
       (fn-pibr-fixed-resize-rosterp roster)
       (implies (equal ,coordinate *fn-sror-coordinate*)
         (<= (fn-pibr-roster-object-octets roster ,coordinate)
             (fn-pibr-initial-primary-object-octets
                (fn-octets$c-buf-length ,cw) (fn-octets$c-buf-length ,ct)
                (fn-octets$c-buf-length ,co)))))))

(defthm pibr-literal-fresh-complete-primary-positive
 (let ((token '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 0)) (cw (create-fn-octets$c)) (ct (create-fn-octets$c)) (co (create-fn-octets$c)))
  (and (fn-pwz-tokenp token) (fn-octets$cp cw) (fn-octets$cp ct) (fn-octets$cp co)
       (pibr-full-boundary token cw ct co *fn-sror-coordinate*)
       (equal (fn-pibr-request-roster
          (cdr (fn-pib-piwc-begin token 301 (create-pgs-digest-state)
             (create-fn-zin-st) cw ct co))) '((64 0) (65536 0) (3494 0)))
       (equal (fn-pibr-initial-primary-object-component
               (fn-octets$c-buf-length cw) (fn-octets$c-buf-length ct)
               (fn-octets$c-buf-length co) *fn-sror-coordinate*)
              '(:primary-object 69152 3))))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
 :use ((:instance fn-pibr-actual-begin-primary-object-boundary
   (token '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 0)) (incarnation 301) (hash (create-pgs-digest-state))
   (zin (create-fn-zin-st)) (cwin (create-fn-octets$c)) (ctab (create-fn-octets$c)) (cout (create-fn-octets$c))
   (coordinate *fn-sror-coordinate*) (awin nil) (atab nil) (aout nil)))
 :in-theory (disable fn-pib-piwc-begin fn-piwc-begin fn-pwz-begin fn-pibr-request-roster
  fn-pibr-roster-object-octets fn-octets$corr (:e fn-pib-piwc-begin)
  (:e fn-piwc-begin) (:e fn-pwz-begin)))))

(defthm pibr-literal-preallocated-complete-primary-positive
 (let ((token '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 0)) (cw (resize-fn-octets$c-buf 70000 (create-fn-octets$c))) (ct (resize-fn-octets$c-buf 4000 (create-fn-octets$c))) (co (resize-fn-octets$c-buf 128 (create-fn-octets$c))))
  (and (fn-pwz-tokenp token) (fn-octets$cp cw) (fn-octets$cp ct) (fn-octets$cp co)
       (pibr-full-boundary token cw ct co *fn-sror-coordinate*)
       (equal (fn-pibr-request-roster
          (cdr (fn-pib-piwc-begin token 301 (create-pgs-digest-state)
             (create-fn-zin-st) cw ct co))) nil)
       (equal (fn-pibr-initial-primary-object-component
               (fn-octets$c-buf-length cw) (fn-octets$c-buf-length ct)
               (fn-octets$c-buf-length co) *fn-sror-coordinate*)
              '(:primary-object 0 0))))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
 :use ((:instance fn-pibr-actual-begin-primary-object-boundary
   (token '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 0)) (incarnation 301) (hash (create-pgs-digest-state))
   (zin (create-fn-zin-st)) (cwin (resize-fn-octets$c-buf 70000 (create-fn-octets$c))) (ctab (resize-fn-octets$c-buf 4000 (create-fn-octets$c))) (cout (resize-fn-octets$c-buf 128 (create-fn-octets$c)))
   (coordinate *fn-sror-coordinate*) (awin nil) (atab nil) (aout nil)))
 :in-theory (disable fn-pib-piwc-begin fn-piwc-begin fn-pwz-begin fn-pibr-request-roster
  fn-pibr-roster-object-octets fn-octets$corr (:e fn-pib-piwc-begin)
  (:e fn-piwc-begin) (:e fn-pwz-begin)))))

(defthm pibr-literal-mixed-complete-primary-positive
 (let ((token '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 0)) (cw (resize-fn-octets$c-buf 70000 (create-fn-octets$c))) (ct (create-fn-octets$c)) (co (resize-fn-octets$c-buf 128 (create-fn-octets$c))))
  (and (fn-pwz-tokenp token) (fn-octets$cp cw) (fn-octets$cp ct) (fn-octets$cp co)
       (pibr-full-boundary token cw ct co *fn-sror-coordinate*)
       (equal (fn-pibr-request-roster
          (cdr (fn-pib-piwc-begin token 301 (create-pgs-digest-state)
             (create-fn-zin-st) cw ct co))) '((3494 0)))
       (equal (fn-pibr-initial-primary-object-component
               (fn-octets$c-buf-length cw) (fn-octets$c-buf-length ct)
               (fn-octets$c-buf-length co) *fn-sror-coordinate*)
              '(:primary-object 3520 1))))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
 :use ((:instance fn-pibr-actual-begin-primary-object-boundary
   (token '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 0)) (incarnation 301) (hash (create-pgs-digest-state))
   (zin (create-fn-zin-st)) (cwin (resize-fn-octets$c-buf 70000 (create-fn-octets$c))) (ctab (create-fn-octets$c)) (cout (resize-fn-octets$c-buf 128 (create-fn-octets$c)))
   (coordinate *fn-sror-coordinate*) (awin nil) (atab nil) (aout nil)))
 :in-theory (disable fn-pib-piwc-begin fn-piwc-begin fn-pwz-begin fn-pibr-request-roster
  fn-pibr-roster-object-octets fn-octets$corr (:e fn-pib-piwc-begin)
  (:e fn-piwc-begin) (:e fn-pwz-begin)))))

; Corrupted logical concrete tail, not an executable UB8 input.
(defthm pibr-literal-remove-typed-window-array
 (let ((token '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 0)) (cw (update-fn-octets$c-bufi 65536 300 (resize-fn-octets$c-buf 65537 (create-fn-octets$c)))) (ct (create-fn-octets$c)) (co (create-fn-octets$c)))
  (and (not (fn-octets$cp cw)) (fn-octets$cp ct) (fn-octets$cp co)
       (not (pibr-full-boundary token cw ct co *fn-sror-coordinate*))))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
 :use piwc-literal-remove-typed-window-array
 :in-theory (disable fn-pib-piwc-begin fn-piwc-begin fn-pwz-begin fn-pibr-request-roster
  fn-pibr-roster-object-octets fn-octets$corr (:e fn-pib-piwc-begin)
  (:e fn-piwc-begin) (:e fn-pwz-begin) fn-octets$cp))))

; Corrupted logical concrete tail, not an executable UB8 input.
(defthm pibr-literal-remove-typed-table-array
 (let ((token '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 0)) (cw (create-fn-octets$c)) (ct (update-fn-octets$c-bufi 3494 300 (resize-fn-octets$c-buf 3495 (create-fn-octets$c)))) (co (create-fn-octets$c)))
  (and (fn-octets$cp cw) (not (fn-octets$cp ct)) (fn-octets$cp co)
       (not (pibr-full-boundary token cw ct co *fn-sror-coordinate*))))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
 :use piwc-literal-remove-typed-table-array
 :in-theory (disable fn-pib-piwc-begin fn-piwc-begin fn-pwz-begin fn-pibr-request-roster
  fn-pibr-roster-object-octets fn-octets$corr (:e fn-pib-piwc-begin)
  (:e fn-piwc-begin) (:e fn-pwz-begin) fn-octets$cp))))

; Corrupted logical concrete tail, not an executable UB8 input.
(defthm pibr-literal-remove-typed-output-array
 (let ((token '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 0)) (cw (create-fn-octets$c)) (ct (create-fn-octets$c)) (co (update-fn-octets$c-bufi 64 300 (resize-fn-octets$c-buf 65 (create-fn-octets$c)))))
  (and (fn-octets$cp cw) (fn-octets$cp ct) (not (fn-octets$cp co))
       (not (pibr-full-boundary token cw ct co *fn-sror-coordinate*))))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
 :use piwc-literal-remove-typed-output-array
 :in-theory (disable fn-pib-piwc-begin fn-piwc-begin fn-pwz-begin fn-pibr-request-roster
  fn-pibr-roster-object-octets fn-octets$corr (:e fn-pib-piwc-begin)
  (:e fn-piwc-begin) (:e fn-pwz-begin) fn-octets$cp))))

; Complete scalar candidate refusal, not a claim about a real failed resize.
(defthm pibr-literal-unqualified-primary-component-refusal
 (and (not (equal '(:unqualified) *fn-sror-coordinate*))
      (equal (fn-pibr-initial-primary-object-component 0 0 0 '(:unqualified))
             '(:unavailable nil nil)))
 :rule-classes nil)
; Separate candidate charge and source-domain mutations; actual unconstrained
; runtime object cost is not asserted equal to the candidate upper bound.
(defthm pibr-literal-primary-charge-and-roster-mutations
 (and (equal (fn-pibr-initial-primary-object-component 0 0 0 *fn-sror-coordinate*)
             '(:primary-object 69152 3))
      (not (equal (fn-pibr-initial-primary-object-component 0 0 0 *fn-sror-coordinate*)
                  '(:primary-object 69094 3)))
      (not (equal (fn-pibr-initial-primary-object-component 0 0 0 *fn-sror-coordinate*)
                  '(:primary-object 0 0)))
      (equal (fn-pibr-initial-request-roster 0 0 0) '((64 0) (65536 0) (3494 0)))
      (not (equal (fn-pibr-initial-request-roster 0 0 0) '((65536 0) (3494 0) (64 0))))
      (not (fn-pibr-fixed-resize-rosterp '((65 0))))
      (not (fn-pibr-fixed-resize-rosterp '((64 64))))
      (not (fn-pibr-fixed-resize-rosterp '((64 -1)))))
 :rule-classes nil)
