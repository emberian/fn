(in-package "ACL2")
(include-book "../../books/decoded-window-initial-array-payload")
(include-book "decoded-window-initial-buffer-refinement-tests")
(defmacro piba-full-boundary (token cw ct co)
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
       (equal (fn-pib-resize-request-payload (cdr o))
          (fn-pib-initial-new-array-payload (fn-octets$c-buf-length ,cw)
            (fn-octets$c-buf-length ,ct) (fn-octets$c-buf-length ,co)))
       (<= (+ (fn-octets$c-buf-length (mv-nth 3 r))
               (fn-octets$c-buf-length (mv-nth 4 r))
               (fn-octets$c-buf-length (mv-nth 5 r)))
            (fn-pib-initial-retained-and-requested-payload
              (fn-octets$c-buf-length ,cw) (fn-octets$c-buf-length ,ct)
              (fn-octets$c-buf-length ,co))))))

(defthm piba-literal-fresh-complete-payload-positive
 (let ((token '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 0)) (cw (create-fn-octets$c)) (ct (create-fn-octets$c)) (co (create-fn-octets$c)))
  (and (fn-pwz-tokenp token) (fn-octets$cp cw) (fn-octets$cp ct) (fn-octets$cp co)
       (piba-full-boundary token cw ct co)
       (equal (fn-pib-resize-request-payload
          (cdr (fn-pib-piwc-begin token 301 (create-pgs-digest-state)
             (create-fn-zin-st) cw ct co))) 69094)))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
 :use ((:instance fn-pib-actual-begin-array-payload-boundary
   (token '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 0)) (incarnation 301) (hash (create-pgs-digest-state))
   (zin (create-fn-zin-st)) (cwin (create-fn-octets$c)) (ctab (create-fn-octets$c)) (cout (create-fn-octets$c))
   (awin nil) (atab nil) (aout nil)))
 :in-theory (disable fn-pib-piwc-begin fn-piwc-begin fn-pwz-begin fn-pib-resize-request-payload
  fn-octets$corr (:e fn-pib-piwc-begin) (:e fn-piwc-begin) (:e fn-pwz-begin)))))

(defthm piba-literal-preallocated-complete-payload-positive
 (let ((token '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 0)) (cw (resize-fn-octets$c-buf 70000 (create-fn-octets$c))) (ct (resize-fn-octets$c-buf 4000 (create-fn-octets$c))) (co (resize-fn-octets$c-buf 128 (create-fn-octets$c))))
  (and (fn-pwz-tokenp token) (fn-octets$cp cw) (fn-octets$cp ct) (fn-octets$cp co)
       (piba-full-boundary token cw ct co)
       (equal (fn-pib-resize-request-payload
          (cdr (fn-pib-piwc-begin token 301 (create-pgs-digest-state)
             (create-fn-zin-st) cw ct co))) 0)))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
 :use ((:instance fn-pib-actual-begin-array-payload-boundary
   (token '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 0)) (incarnation 301) (hash (create-pgs-digest-state))
   (zin (create-fn-zin-st)) (cwin (resize-fn-octets$c-buf 70000 (create-fn-octets$c))) (ctab (resize-fn-octets$c-buf 4000 (create-fn-octets$c))) (cout (resize-fn-octets$c-buf 128 (create-fn-octets$c)))
   (awin nil) (atab nil) (aout nil)))
 :in-theory (disable fn-pib-piwc-begin fn-piwc-begin fn-pwz-begin fn-pib-resize-request-payload
  fn-octets$corr (:e fn-pib-piwc-begin) (:e fn-piwc-begin) (:e fn-pwz-begin)))))

(defthm piba-literal-mixed-complete-payload-positive
 (let ((token '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 0)) (cw (resize-fn-octets$c-buf 70000 (create-fn-octets$c))) (ct (create-fn-octets$c)) (co (resize-fn-octets$c-buf 128 (create-fn-octets$c))))
  (and (fn-pwz-tokenp token) (fn-octets$cp cw) (fn-octets$cp ct) (fn-octets$cp co)
       (piba-full-boundary token cw ct co)
       (equal (fn-pib-resize-request-payload
          (cdr (fn-pib-piwc-begin token 301 (create-pgs-digest-state)
             (create-fn-zin-st) cw ct co))) 3494)))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
 :use ((:instance fn-pib-actual-begin-array-payload-boundary
   (token '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 0)) (incarnation 301) (hash (create-pgs-digest-state))
   (zin (create-fn-zin-st)) (cwin (resize-fn-octets$c-buf 70000 (create-fn-octets$c))) (ctab (create-fn-octets$c)) (cout (resize-fn-octets$c-buf 128 (create-fn-octets$c)))
   (awin nil) (atab nil) (aout nil)))
 :in-theory (disable fn-pib-piwc-begin fn-piwc-begin fn-pwz-begin fn-pib-resize-request-payload
  fn-octets$corr (:e fn-pib-piwc-begin) (:e fn-piwc-begin) (:e fn-pwz-begin)))))

; Corrupted logical concrete tail, not an executable UB8 input.
(defthm piba-literal-remove-typed-window-array
 (let ((token '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 0)) (cw (update-fn-octets$c-bufi 65536 300 (resize-fn-octets$c-buf 65537 (create-fn-octets$c)))) (ct (create-fn-octets$c)) (co (create-fn-octets$c)))
  (and (not (fn-octets$cp cw)) (fn-octets$cp ct) (fn-octets$cp co) (not (piba-full-boundary token cw ct co))))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
 :use piwc-literal-remove-typed-window-array
 :in-theory (disable fn-pib-piwc-begin fn-piwc-begin fn-pwz-begin fn-pib-resize-request-payload
  fn-octets$corr (:e fn-pib-piwc-begin) (:e fn-piwc-begin) (:e fn-pwz-begin) fn-octets$cp))))

; Corrupted logical concrete tail, not an executable UB8 input.
(defthm piba-literal-remove-typed-table-array
 (let ((token '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 0)) (cw (create-fn-octets$c)) (ct (update-fn-octets$c-bufi 3494 300 (resize-fn-octets$c-buf 3495 (create-fn-octets$c)))) (co (create-fn-octets$c)))
  (and (fn-octets$cp cw) (not (fn-octets$cp ct)) (fn-octets$cp co) (not (piba-full-boundary token cw ct co))))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
 :use piwc-literal-remove-typed-table-array
 :in-theory (disable fn-pib-piwc-begin fn-piwc-begin fn-pwz-begin fn-pib-resize-request-payload
  fn-octets$corr (:e fn-pib-piwc-begin) (:e fn-piwc-begin) (:e fn-pwz-begin) fn-octets$cp))))

; Corrupted logical concrete tail, not an executable UB8 input.
(defthm piba-literal-remove-typed-output-array
 (let ((token '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 0)) (cw (create-fn-octets$c)) (ct (create-fn-octets$c)) (co (update-fn-octets$c-bufi 64 300 (resize-fn-octets$c-buf 65 (create-fn-octets$c)))))
  (and (fn-octets$cp cw) (fn-octets$cp ct) (not (fn-octets$cp co)) (not (piba-full-boundary token cw ct co))))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
 :use piwc-literal-remove-typed-output-array
 :in-theory (disable fn-pib-piwc-begin fn-piwc-begin fn-pwz-begin fn-pib-resize-request-payload
  fn-octets$corr (:e fn-pib-piwc-begin) (:e fn-piwc-begin) (:e fn-pwz-begin) fn-octets$cp))))

; Source payload mutation: headers and physical lifetime are separate.
(defthm piba-literal-fresh-payload-mutation
 (let ((trace (cdr (fn-pib-piwc-begin '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 0) 301
      (create-pgs-digest-state) (create-fn-zin-st) (create-fn-octets$c) (create-fn-octets$c) (create-fn-octets$c)))))
  (and (equal (fn-pib-resize-request-payload trace) 69094)
       (not (equal (fn-pib-resize-request-payload trace) 0))
       (not (equal (fn-pib-resize-request-payload trace) 69152))))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
 :use ((:instance fn-pib-begin-exact-resize-payload
   (token '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 0)) (incarnation 301) (hash (create-pgs-digest-state))
   (zin (create-fn-zin-st)) (cwin (create-fn-octets$c)) (ctab (create-fn-octets$c)) (cout (create-fn-octets$c))))
 :in-theory (disable fn-pib-piwc-begin fn-piwc-begin fn-pwz-begin fn-pib-resize-request-payload
  fn-octets$corr (:e fn-pib-piwc-begin) (:e fn-piwc-begin) (:e fn-pwz-begin)))))
(defthm piba-literal-retained-request-scalar-positive
 (and (equal (fn-pib-initial-new-array-payload 0 0 0) 69094)
      (equal (fn-pib-initial-retained-and-requested-payload 70000 0 128) 73622)
      (equal (fn-pib-initial-retained-and-requested-payload 70000 4000 128) 74128)
      (not (equal (fn-pib-initial-retained-and-requested-payload 70000 4000 128) 69094)))
 :rule-classes nil)
