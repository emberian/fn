; fn: teeth for books/sha256-range.lisp and the window digest
; (books/frame-digest-buffer.lisp fn-frame-digest-range, the checkpoint
; reader's frame seal books/store-checkpoint-reader.lisp fn-sccr-window-seal).
;
; `fn-sha256-of-prefixed-range-is-sha256' and
; `fn-frame-digest-range-is-the-frame-digest' have no hypothesis; their
; witnesses are evaluations on a live local buffer, the way the host runs
; them: the FIPS 180-4 "abc" vector read as a WINDOW inside a buffer that
; holds other octets before and after it (the window's base and length
; varied, the prefix split between the list and the window), a window that
; crosses a padding boundary and a 3,000-octet window, each against the list
; model.  `fn-sccr-window-seal-is-seal' has hypotheses (a live buffer, an
; in-range window, an octet header): its reachable witness is a frame the
; checkpoint reader admits, and the omitted-hypothesis witness is a prev
; that is not an octet list (the seal refuses it, :bad, on both sides).
;
; Nothing here bears on collision resistance (A-CRYPTO, specs/failures.md).

(in-package "ACL2")
(include-book "../../books/store-checkpoint-reader")

(assert-event
 (equal (list (symbol-class 'fn-shr-byte (w state))
              (symbol-class 'fn-shr-load-word (w state))
              (symbol-class 'fn-shr-load-block (w state))
              (symbol-class 'fn-shr-compress (w state))
              (symbol-class 'fn-shr-blocks (w state))
              (symbol-class 'fn-shr-digest (w state))
              (symbol-class 'fn-sha256-of-prefixed-range (w state))
              (symbol-class 'fn-sha256-of-prefixed-range-any (w state))
              (symbol-class 'fn-sccr-window-seal (w state))
              (symbol-class 'fn-sccr-open-frame (w state)))
        '(:common-lisp-compliant :common-lisp-compliant :common-lisp-compliant
          :common-lisp-compliant :common-lisp-compliant :common-lisp-compliant
          :common-lisp-compliant :common-lisp-compliant :common-lisp-compliant
          :common-lisp-compliant)))

(defun shrt-repeat (n x)
  (declare (xargs :guard t :measure (nfix n)))
  (let ((n (nfix n)))
    (if (zp n) nil (cons x (shrt-repeat (- n 1) x)))))

(defthm shrt-octet-listp-of-repeat
  (implies (fn-cbor-octetp x)
           (fn-cbor-octet-listp (shrt-repeat n x))))

; The window digest and the frame digest of a window, on XS in a fresh local
; buffer.
(defun shrt-run (prefix a wn xs fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (true-listp prefix) (fn-cbor-octet-listp xs)
                              (natp a) (natp wn))))
  (let ((fn-octets (fn-octets-from-list xs fn-octets)))
    (if (<= (+ a wn) (fn-octets-len fn-octets))
        (mv (list (fn-sha256-of-prefixed-range prefix a wn fn-octets)
                  (fn-frame-digest-range prefix a wn fn-octets))
            fn-octets)
      (mv nil fn-octets))))

(defun shrt (prefix a wn xs)
  (declare (xargs :guard (and (true-listp prefix) (fn-cbor-octet-listp xs)
                              (natp a) (natp wn))))
  (with-local-stobj fn-octets
    (mv-let (d fn-octets) (shrt-run prefix a wn xs fn-octets) d)))

; FIPS 180-4 B.1: SHA-256("abc").
(defconst *shrt-abc*
  '(#xba #x78 #x16 #xbf #x8f #x01 #xcf #xea #x41 #x41 #x40 #xde #x5d #xae #x22 #x23
    #xb0 #x03 #x61 #xa3 #x96 #x17 #x7a #x9c #xb4 #x10 #xff #x61 #xf2 #x00 #x15 #xad))

; "abc" as a window with other octets on both sides, the prefix split three
; ways; the window digest and the frame digest agree with the vector.
(assert-event
 (let ((buf '(120 120 97 98 99 121 121)))
   (and (equal (shrt nil 2 3 buf) (list *shrt-abc* *shrt-abc*))
        (equal (shrt '(97) 3 2 buf) (list *shrt-abc* *shrt-abc*))
        (equal (shrt '(97 98 99) 5 0 buf) (list *shrt-abc* *shrt-abc*))
        ;; a different window of the same buffer is a different digest
        (not (equal (car (shrt nil 1 3 buf)) *shrt-abc*)))))

; Padding boundaries and a window past the array's first 1024 cells, against
; the list model (fn-sha256-stobj over the window's octets).
(defconst *shrt-big* (append (shrt-repeat 100 7) (shrt-repeat 3000 97) (shrt-repeat 50 9)))
(assert-event
 (and (equal (car (shrt '(1 2 3) 100 55 *shrt-big*))
             (fn-sha256-stobj (append '(1 2 3) (shrt-repeat 55 97))))
      (equal (car (shrt nil 100 56 *shrt-big*))
             (fn-sha256-stobj (shrt-repeat 56 97)))
      (equal (car (shrt nil 100 64 *shrt-big*))
             (fn-sha256-stobj (shrt-repeat 64 97)))
      (equal (car (shrt '(5) 100 3000 *shrt-big*))
             (fn-sha256-stobj (cons 5 (shrt-repeat 3000 97))))
      (equal (cadr (shrt '(5) 100 3000 *shrt-big*))
             (fn-sha256-stobj (cons 5 (shrt-repeat 3000 97))))))

; fn-sccr-window-seal-is-seal, reachable: the seal of a window equals the
; list seal (fn-scc-seal over the slice); omitted hypothesis (PREV not an
; octet list): both sides answer :bad, and the retained hypotheses hold.
(defun shrt-seal-run (prev header a b xs fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (true-listp prev) (fn-scc-octet-listp header)
                              (fn-cbor-octet-listp xs) (natp a) (natp b) (<= a b))))
  (let ((fn-octets (fn-octets-from-list xs fn-octets)))
    (if (<= b (fn-octets-len fn-octets))
        (mv (list (fn-sccr-window-seal prev header a b fn-octets)
                  (fn-scc-seal prev header (fn-sccb-slice-acc a b nil fn-octets)))
            fn-octets)
      (mv nil fn-octets))))

(defun shrt-seal (prev header a b xs)
  (declare (xargs :guard (and (true-listp prev) (fn-scc-octet-listp header)
                              (fn-cbor-octet-listp xs) (natp a) (natp b) (<= a b))))
  (with-local-stobj fn-octets
    (mv-let (d fn-octets) (shrt-seal-run prev header a b xs fn-octets) d)))

(assert-event
 (let ((ok (shrt-seal (shrt-repeat 32 0) '(1 2 3) 100 3100 *shrt-big*))
       (bad (shrt-seal '(300) '(1 2 3) 100 3100 *shrt-big*)))
   (and (equal (car ok) (cadr ok))
        (equal (len (car ok)) 32)
        (equal (car ok) (fn-sha256-stobj (append (shrt-repeat 32 0) '(1 2 3)
                                                 (shrt-repeat 3000 97))))
        (true-listp '(300))
        (not (fn-scc-octet-listp '(300)))
        (equal (car bad) :bad)
        (equal (cadr bad) :bad))))
