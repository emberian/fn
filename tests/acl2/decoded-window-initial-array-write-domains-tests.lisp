(in-package "ACL2")
(include-book "../../books/decoded-window-initial-array-write-domains")
(include-book "decoded-window-initial-buffer-refinement-tests")
(defmacro piwa-full-boundary (token cw ct co)
 `(let* ((o (fn-pib-piwc-begin ,token 301 (create-pgs-digest-state)
                  (create-fn-zin-st) ,cw ,ct ,co))
         (r (car o))
         (a (fn-pwz-begin ,token 301 (create-pgs-digest-state)
                         (create-fn-zin-st) nil nil nil)))
  (and (equal (mv-nth 0 r) (mv-nth 0 a))
       (equal (mv-nth 1 r) (mv-nth 1 a))
       (equal (mv-nth 2 r) (mv-nth 2 a))
       (fn-octets$corr (mv-nth 3 r) (mv-nth 3 a))
       (fn-octets$corr (mv-nth 4 r) (mv-nth 4 a))
       (fn-octets$corr (mv-nth 5 r) (mv-nth 5 a))
       (fn-piwa-write-domainp 65536 (cdr o)))))
(defthm piwa-literal-fresh-complete-write-domain-positive
 (let ((token '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 0)) (cw (create-fn-octets$c)) (ct (create-fn-octets$c)) (co (create-fn-octets$c)))
  (and (fn-pwz-tokenp token) (fn-octets$cp cw) (fn-octets$cp ct) (fn-octets$cp co)
       (piwa-full-boundary token cw ct co)))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
 :use ((:instance fn-piwa-actual-begin-array-write-domain-boundary
   (token '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 0)) (incarnation 301) (hash (create-pgs-digest-state))
   (zin (create-fn-zin-st)) (cwin (create-fn-octets$c)) (ctab (create-fn-octets$c)) (cout (create-fn-octets$c))
   (awin nil) (atab nil) (aout nil)))
 :in-theory (disable fn-pib-piwc-begin fn-piwc-begin fn-pwz-begin fn-piwa-write-domainp
  fn-octets$corr (:e fn-pib-piwc-begin) (:e fn-piwc-begin) (:e fn-pwz-begin)))))

(defthm piwa-literal-preallocated-complete-write-domain-positive
 (let ((token '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 0)) (cw (resize-fn-octets$c-buf 70000 (create-fn-octets$c))) (ct (resize-fn-octets$c-buf 4000 (create-fn-octets$c))) (co (resize-fn-octets$c-buf 128 (create-fn-octets$c))))
  (and (fn-pwz-tokenp token) (fn-octets$cp cw) (fn-octets$cp ct) (fn-octets$cp co)
       (piwa-full-boundary token cw ct co)))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
 :use ((:instance fn-piwa-actual-begin-array-write-domain-boundary
   (token '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 0)) (incarnation 301) (hash (create-pgs-digest-state))
   (zin (create-fn-zin-st)) (cwin (resize-fn-octets$c-buf 70000 (create-fn-octets$c))) (ctab (resize-fn-octets$c-buf 4000 (create-fn-octets$c))) (cout (resize-fn-octets$c-buf 128 (create-fn-octets$c)))
   (awin nil) (atab nil) (aout nil)))
 :in-theory (disable fn-pib-piwc-begin fn-piwc-begin fn-pwz-begin fn-piwa-write-domainp
  fn-octets$corr (:e fn-pib-piwc-begin) (:e fn-piwc-begin) (:e fn-pwz-begin)))))

(defthm piwa-literal-mixed-complete-write-domain-positive
 (let ((token '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 0)) (cw (resize-fn-octets$c-buf 70000 (create-fn-octets$c))) (ct (create-fn-octets$c)) (co (resize-fn-octets$c-buf 128 (create-fn-octets$c))))
  (and (fn-pwz-tokenp token) (fn-octets$cp cw) (fn-octets$cp ct) (fn-octets$cp co)
       (piwa-full-boundary token cw ct co)))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
 :use ((:instance fn-piwa-actual-begin-array-write-domain-boundary
   (token '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 0)) (incarnation 301) (hash (create-pgs-digest-state))
   (zin (create-fn-zin-st)) (cwin (resize-fn-octets$c-buf 70000 (create-fn-octets$c))) (ctab (create-fn-octets$c)) (cout (resize-fn-octets$c-buf 128 (create-fn-octets$c)))
   (awin nil) (atab nil) (aout nil)))
 :in-theory (disable fn-pib-piwc-begin fn-piwc-begin fn-pwz-begin fn-piwa-write-domainp
  fn-octets$corr (:e fn-pib-piwc-begin) (:e fn-piwc-begin) (:e fn-pwz-begin)))))

; Corrupted logical concrete tail, not an executable UB8 input.
(defthm piwa-literal-remove-typed-window-array
 (let ((token '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 0)) (cw (update-fn-octets$c-bufi 65536 300 (resize-fn-octets$c-buf 65537 (create-fn-octets$c)))) (ct (create-fn-octets$c)) (co (create-fn-octets$c)))
  (and (not (fn-octets$cp cw)) (fn-octets$cp ct) (fn-octets$cp co) (not (piwa-full-boundary token cw ct co))))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
 :use piwc-literal-remove-typed-window-array
 :in-theory (disable fn-pib-piwc-begin fn-piwc-begin fn-pwz-begin fn-piwa-write-domainp
  fn-octets$corr (:e fn-pib-piwc-begin) (:e fn-piwc-begin) (:e fn-pwz-begin) fn-octets$cp))))

; Corrupted logical concrete tail, not an executable UB8 input.
(defthm piwa-literal-remove-typed-table-array
 (let ((token '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 0)) (cw (create-fn-octets$c)) (ct (update-fn-octets$c-bufi 3494 300 (resize-fn-octets$c-buf 3495 (create-fn-octets$c)))) (co (create-fn-octets$c)))
  (and (fn-octets$cp cw) (not (fn-octets$cp ct)) (fn-octets$cp co) (not (piwa-full-boundary token cw ct co))))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
 :use piwc-literal-remove-typed-table-array
 :in-theory (disable fn-pib-piwc-begin fn-piwc-begin fn-pwz-begin fn-piwa-write-domainp
  fn-octets$corr (:e fn-pib-piwc-begin) (:e fn-piwc-begin) (:e fn-pwz-begin) fn-octets$cp))))

; Corrupted logical concrete tail, not an executable UB8 input.
(defthm piwa-literal-remove-typed-output-array
 (let ((token '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 0)) (cw (create-fn-octets$c)) (ct (create-fn-octets$c)) (co (update-fn-octets$c-bufi 64 300 (resize-fn-octets$c-buf 65 (create-fn-octets$c)))))
  (and (fn-octets$cp cw) (fn-octets$cp ct) (not (fn-octets$cp co)) (not (piwa-full-boundary token cw ct co))))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
 :use piwc-literal-remove-typed-output-array
 :in-theory (disable fn-pib-piwc-begin fn-piwc-begin fn-pwz-begin fn-piwa-write-domainp
  fn-octets$corr (:e fn-pib-piwc-begin) (:e fn-piwc-begin) (:e fn-pwz-begin) fn-octets$cp))))

; Explicit source operand mutations, not executable UB8 states or setter tariffs.
(defthm piwa-literal-byte-and-fill-operand-mutations
 (let ((c '((0 1) 0)))
  (and (fn-octets$cp c)
       (fn-piwa-write-domainp 2 (list (list :array-write 'update-fn-octets$c-bufi (list 1 255 c))))
       (not (fn-piwa-write-domainp 2 (list (list :array-write 'update-fn-octets$c-bufi (list 2 255 c)))))
       (not (fn-piwa-write-domainp 2 (list (list :array-write 'update-fn-octets$c-bufi (list 1 256 c)))))
       (fn-piwa-write-domainp 2 (list (list :fill-write 'update-fn-octets$c-fill (list 2 c))))
       (not (fn-piwa-write-domainp 2 (list (list :fill-write 'update-fn-octets$c-fill (list 3 c)))))))
 :rule-classes nil)
