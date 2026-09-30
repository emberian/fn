(in-package "ACL2")
(include-book "../../books/decoded-window-initial-buffer-counts")
; Reuse exact complete physical-array countermodels proved at unchanged sources.
(include-book "decoded-window-initial-buffer-refinement-tests")
(defmacro pib-full-boundary (token cw ct co)
 `(let* ((o (fn-pib-piwc-begin ,token 301 (create-pgs-digest-state)
                  (create-fn-zin-st) ,cw ,ct ,co))
         (r (car o)) (trace (cdr o))
         (a (fn-pwz-begin ,token 301 (create-pgs-digest-state)
                         (create-fn-zin-st) '(256) '(256) '(256)))
         (h (min (len (fn-pwz-dictionary ,token)) 32768)))
  (and (equal (mv-nth 0 r) (mv-nth 0 a))
       (equal (mv-nth 1 r) (mv-nth 1 a))
       (equal (mv-nth 2 r) (mv-nth 2 a))
       (fn-octets$corr (mv-nth 3 r) (mv-nth 3 a))
       (fn-octets$corr (mv-nth 4 r) (mv-nth 4 a))
       (fn-octets$corr (mv-nth 5 r) (mv-nth 5 a))
       (equal (fn-pib-event-count :array-resize trace)
        (+ (if (<= 65536 (fn-octets$c-buf-length ,cw)) 0 1)
           (if (<= 3494 (fn-octets$c-buf-length ,ct)) 0 1)
           (if (<= 64 (fn-octets$c-buf-length ,co)) 0 1)))
       (equal (fn-pib-event-count :array-write trace) 69030)
       (equal (fn-pib-event-count :fill-write trace) (+ 7 h (if (< h 32768) 2 0))))))

(defthm pib-literal-fresh-complete-array-source-positive
 (let ((token '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 0)) (cw (create-fn-octets$c)) (ct (create-fn-octets$c)) (co (create-fn-octets$c)))
  (and (fn-pwz-tokenp token) (fn-octets$cp cw) (fn-octets$cp ct) (fn-octets$cp co)
       (pib-full-boundary token cw ct co)
       (equal (fn-pib-event-count :array-resize
         (cdr (fn-pib-piwc-begin token 301 (create-pgs-digest-state)
          (create-fn-zin-st) cw ct co))) 3)))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
 :use ((:instance fn-pib-actual-begin-array-source-boundary
   (token '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 0)) (incarnation 301) (hash (create-pgs-digest-state))
   (zin (create-fn-zin-st)) (cwin (create-fn-octets$c)) (ctab (create-fn-octets$c)) (cout (create-fn-octets$c))
   (awin '(256)) (atab '(256)) (aout '(256))))
 :in-theory (disable fn-pib-piwc-begin fn-piwc-begin fn-pwz-begin fn-pib-event-count
  fn-octets$corr (:e fn-pib-piwc-begin) (:e fn-piwc-begin) (:e fn-pwz-begin)))))

(defthm pib-literal-shipped-complete-array-source-positive
 (let ((token '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 2220533217)) (cw (create-fn-octets$c)) (ct (create-fn-octets$c)) (co (create-fn-octets$c)))
  (and (fn-pwz-tokenp token) (fn-octets$cp cw) (fn-octets$cp ct) (fn-octets$cp co)
       (pib-full-boundary token cw ct co)
       (equal (fn-pib-event-count :array-resize
         (cdr (fn-pib-piwc-begin token 301 (create-pgs-digest-state)
          (create-fn-zin-st) cw ct co))) 3)))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
 :use ((:instance fn-pib-actual-begin-array-source-boundary
   (token '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 2220533217)) (incarnation 301) (hash (create-pgs-digest-state))
   (zin (create-fn-zin-st)) (cwin (create-fn-octets$c)) (ctab (create-fn-octets$c)) (cout (create-fn-octets$c))
   (awin '(256)) (atab '(256)) (aout '(256))))
 :in-theory (disable fn-pib-piwc-begin fn-piwc-begin fn-pwz-begin fn-pib-event-count
  fn-octets$corr (:e fn-pib-piwc-begin) (:e fn-piwc-begin) (:e fn-pwz-begin)))))

(defthm pib-literal-preallocated-complete-array-source-positive
 (let ((token '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 0)) (cw (resize-fn-octets$c-buf 70000 (create-fn-octets$c))) (ct (resize-fn-octets$c-buf 4000 (create-fn-octets$c))) (co (resize-fn-octets$c-buf 128 (create-fn-octets$c))))
  (and (fn-pwz-tokenp token) (fn-octets$cp cw) (fn-octets$cp ct) (fn-octets$cp co)
       (pib-full-boundary token cw ct co)
       (equal (fn-pib-event-count :array-resize
         (cdr (fn-pib-piwc-begin token 301 (create-pgs-digest-state)
          (create-fn-zin-st) cw ct co))) 0)))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
 :use ((:instance fn-pib-actual-begin-array-source-boundary
   (token '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 0)) (incarnation 301) (hash (create-pgs-digest-state))
   (zin (create-fn-zin-st)) (cwin (resize-fn-octets$c-buf 70000 (create-fn-octets$c))) (ctab (resize-fn-octets$c-buf 4000 (create-fn-octets$c))) (cout (resize-fn-octets$c-buf 128 (create-fn-octets$c)))
   (awin '(256)) (atab '(256)) (aout '(256))))
 :in-theory (disable fn-pib-piwc-begin fn-piwc-begin fn-pwz-begin fn-pib-event-count
  fn-octets$corr (:e fn-pib-piwc-begin) (:e fn-piwc-begin) (:e fn-pwz-begin)))))

(defmacro pib-full-boundary-nil (token cw ct co)
 `(let* ((o (fn-pib-piwc-begin ,token 301 (create-pgs-digest-state)
                  (create-fn-zin-st) ,cw ,ct ,co))
         (r (car o)) (trace (cdr o))
         (a (fn-pwz-begin ,token 301 (create-pgs-digest-state)
                         (create-fn-zin-st) nil nil nil))
         (h (min (len (fn-pwz-dictionary ,token)) 32768)))
  (and (equal (mv-nth 0 r) (mv-nth 0 a))
       (equal (mv-nth 1 r) (mv-nth 1 a))
       (equal (mv-nth 2 r) (mv-nth 2 a))
       (fn-octets$corr (mv-nth 3 r) (mv-nth 3 a))
       (fn-octets$corr (mv-nth 4 r) (mv-nth 4 a))
       (fn-octets$corr (mv-nth 5 r) (mv-nth 5 a))
       (equal (fn-pib-event-count :array-resize trace)
        (+ (if (<= 65536 (fn-octets$c-buf-length ,cw)) 0 1)
           (if (<= 3494 (fn-octets$c-buf-length ,ct)) 0 1)
           (if (<= 64 (fn-octets$c-buf-length ,co)) 0 1)))
       (equal (fn-pib-event-count :array-write trace) 69030)
       (equal (fn-pib-event-count :fill-write trace) (+ 7 h (if (< h 32768) 2 0))))))


; Same exact malformed retained-tail countermodel, complete new boundary.
(defthm pib-literal-remove-typed-window-array
 (let ((token '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 0))
       (cw (update-fn-octets$c-bufi 65536 300 (resize-fn-octets$c-buf 65537 (create-fn-octets$c)))) (ct (create-fn-octets$c)) (co (create-fn-octets$c)))
  (and (not (fn-octets$cp cw)) (fn-octets$cp ct) (fn-octets$cp co)
       (not (pib-full-boundary-nil token cw ct co))))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
 :use piwc-literal-remove-typed-window-array
 :in-theory (disable fn-pib-piwc-begin fn-piwc-begin fn-pwz-begin fn-pib-event-count
  fn-octets$corr fn-octets$cp (:e fn-pib-piwc-begin) (:e fn-piwc-begin) (:e fn-pwz-begin)))))

; Same exact malformed retained-tail countermodel, complete new boundary.
(defthm pib-literal-remove-typed-table-array
 (let ((token '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 0))
       (cw (create-fn-octets$c)) (ct (update-fn-octets$c-bufi 3494 300 (resize-fn-octets$c-buf 3495 (create-fn-octets$c)))) (co (create-fn-octets$c)))
  (and (fn-octets$cp cw) (not (fn-octets$cp ct)) (fn-octets$cp co)
       (not (pib-full-boundary-nil token cw ct co))))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
 :use piwc-literal-remove-typed-table-array
 :in-theory (disable fn-pib-piwc-begin fn-piwc-begin fn-pwz-begin fn-pib-event-count
  fn-octets$corr fn-octets$cp (:e fn-pib-piwc-begin) (:e fn-piwc-begin) (:e fn-pwz-begin)))))

; Same exact malformed retained-tail countermodel, complete new boundary.
(defthm pib-literal-remove-typed-output-array
 (let ((token '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 0))
       (cw (create-fn-octets$c)) (ct (create-fn-octets$c)) (co (update-fn-octets$c-bufi 64 300 (resize-fn-octets$c-buf 65 (create-fn-octets$c)))))
  (and (fn-octets$cp cw) (fn-octets$cp ct) (not (fn-octets$cp co))
       (not (pib-full-boundary-nil token cw ct co))))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
 :use piwc-literal-remove-typed-output-array
 :in-theory (disable fn-pib-piwc-begin fn-piwc-begin fn-pwz-begin fn-pib-event-count
  fn-octets$corr fn-octets$cp (:e fn-pib-piwc-begin) (:e fn-piwc-begin) (:e fn-pwz-begin)))))
; Separately labelled source-count mutations; no allocator claim.
(defthm pib-literal-fresh-array-roster-mutation
 (let ((trace (cdr (fn-pib-piwc-begin '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 0)
                   301 (create-pgs-digest-state) (create-fn-zin-st)
                   (create-fn-octets$c) (create-fn-octets$c) (create-fn-octets$c)))))
  (and (equal (fn-pib-event-count :array-resize trace) 3)
       (not (equal (fn-pib-event-count :array-resize trace) 0))
       (equal (fn-pib-event-count :array-write trace) 69030)
       (not (equal (fn-pib-event-count :array-write trace) 69029))
       (equal (fn-pib-event-count :fill-write trace) 9)
       (not (equal (fn-pib-event-count :fill-write trace) 8))))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
 :use ((:instance fn-pib-begin-exact-array-source-roster
   (token '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 0))
   (incarnation 301) (hash (create-pgs-digest-state)) (zin (create-fn-zin-st))
   (cwin (create-fn-octets$c)) (ctab (create-fn-octets$c)) (cout (create-fn-octets$c))))
 :in-theory (disable fn-pib-piwc-begin fn-pib-event-count (:e fn-pib-piwc-begin)))))
