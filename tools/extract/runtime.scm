;;; tools/extract/runtime.scm -- the hand-written runtime of the CHICKEN backend.
;;;
;;; Everything else in an extracted program comes from the ACL2 world
;;; (tools/extract/frontend.lisp) through tools/extract/chicken.py.  This file
;;; is the whole of the hand code, and it is only:
;;;   1. the representation: ACL2 NIL is Scheme '() (the one false value and
;;;      the empty list); T and every other symbol are interned Scheme symbols
;;;      named "PKG::NAME" by their home package; characters are Scheme chars
;;;      of code 0-255; strings are CHICKEN's byte strings read as Latin-1
;;;      (one byte per ACL2 character); numbers are CHICKEN's exact tower;
;;;   2. ACL2's primitives (*primitive-formals-and-guards*);
;;;   3. the raw-Lisp built-ins ACL2 itself runs as Common Lisp functions
;;;      rather than through their logical definitions (logand, ash, floor ...);
;;;   4. the raw-Lisp-only functions: state globals, errors, the non-standard
;;;      character case table, the durable-extent realizers (the two file
;;;      primitives).
;;; Stobj primitives are generated from each defstobj's field table.

(import scheme (chicken base) (chicken fixnum) (chicken bitwise)
        (chicken string) (chicken io) (chicken process-context)
        (chicken time) (chicken gc) (chicken format) (chicken condition)
        srfi-4 srfi-69)

(define-constant acl2-t '|COMMON-LISP::T|)
(define-inline (a-bool x) (if x '|COMMON-LISP::T| '()))

;; --- symbols -----------------------------------------------------------------
(define (a-split-symbol s)
  ;; "PKG::NAME" -> (values "PKG" "NAME"); package names hold no ':'.
  (let* ((str (symbol->string s))
         (n (string-length str)))
    (let loop ((i 0))
      (cond ((>= (+ i 1) n) (values "" str))
            ((and (char=? (string-ref str i) #\:) (char=? (string-ref str (+ i 1)) #\:))
             (values (substring str 0 i) (substring str (+ i 2) n)))
            (else (loop (+ i 1)))))))
(define (a-symbolp x) (or (null? x) (symbol? x)))
(define (a-symbol-name x)
  (if (null? x) "NIL" (receive (p n) (a-split-symbol x) n)))
(define (a-symbol-package-name x)
  (if (null? x) "COMMON-LISP" (receive (p n) (a-split-symbol x) p)))
(define (a-intern-in-package-of-symbol str sym)
  ;; Only the non-importing case is supported: a name interned in a package
  ;; that imports it would need the package's import list (not met yet).
  (let ((pkg (a-symbol-package-name sym)))
    (if (and (string=? str "NIL") (string=? pkg "COMMON-LISP")) '()
        (string->symbol (string-append pkg "::" str)))))

;; --- primitives ----------------------------------------------------------------
(define-inline (a-car x) (if (pair? x) (car x) '()))
(define-inline (a-cdr x) (if (pair? x) (cdr x) '()))
(define (a-rationalp x) (and (number? x) (exact? x) (real? x)))
(define (a-complex-rationalp x) (and (number? x) (exact? x) (not (real? x))))
(define (a-coerce x y)
  (if (eq? y '|COMMON-LISP::LIST|)
      (if (string? x) (string->list x) '())
      (list->string x)))
(define (a-complex r i) (make-rectangular r i))
(define (a-bad-atom<= x y) (error "bad-atom<= is not executable here" x y))

;; --- raw-Lisp built-ins (Common Lisp's own function runs in ACL2) --------------
(define (a-ash i c) (arithmetic-shift i c))
(define (a-floor i j) (floor (/ i j)))
(define (a-mod i j) (- i (* (floor (/ i j)) j)))
(define (a-expt r i) (if (and (eqv? r 0) (negative? i)) 0 (expt r i)))
(define (a-niq i j) (quotient i j))
(define (a-len x) (let loop ((x x) (n 0)) (if (pair? x) (loop (cdr x) (fx+ n 1)) n)))
(define (a-length x) (if (string? x) (string-length x) (a-len x)))
(define (a-logeqv i j) (bitwise-not (bitwise-xor i j)))
(define (a-logorc1 i j) (bitwise-ior (bitwise-not i) j))
;; CHAR-DOWNCASE-NON-STANDARD is the host Lisp's char-downcase on a character
;; outside the standard characters.  SBCL's, on codes 128-255 (Latin-1):
;; the capitals 192-222 except 215 map to +32; every other code is itself.
(define (a-char-downcase-non-standard c)
  (let ((k (char->integer c)))
    (if (and (fx>= k 192) (fx<= k 222) (not (fx= k 215))) (integer->char (fx+ k 32)) c)))

;; --- state (the live state's globals: a table, as raw Lisp holds them) ---------
(define acl2-state '|ACL2::STATE|)
(define acl2-globals (make-hash-table eq?))
(define (a-boundp-global x st) (a-bool (hash-table-exists? acl2-globals x)))
(define (a-get-global x st) (hash-table-ref/default acl2-globals x '()))
(define (a-put-global x v st) (hash-table-set! acl2-globals x v) st)

;; --- errors ----------------------------------------------------------------------
(define (a-hard-error ctx str alist) (error "ACL2 hard error" ctx str alist))
(define (a-illegal ctx str alist) (error "ACL2 illegal (guard of a raw call)" ctx str alist))
(define (a-throw-nonexec-error fn actuals) (error "non-executable function called" fn))

;; --- the durable-extent realizers (A-DURABLE-EXTENT, books/assumptions.lisp) ------
;; host/native/extent.lisp's raw definitions read a registered durable file.
;; This runtime registers none: exactly the answer of an image whose store
;; registered none (arena-extent-read), and the seeded archive holds no extent.
(define (a-durable-realize-octet file eoff elen poff plen trailer i)
  (error (sprintf "arena-extent-read: no durable file ~a is registered" file)))
(define (a-durable-realize-octets file eoff elen poff plen trailer)
  (error (sprintf "arena-extent-read: no durable file ~a is registered" file)))

;; --- stobj support ----------------------------------------------------------------
;; A defstobj is a Scheme vector of its fields; an array field is a vector,
;; or a srfi-4 u8vector for (unsigned-byte 8); a hash-table field is a
;; srfi-69 table.  An updater mutates and returns the stobj: the single-
;; threadedness ACL2 enforces is what makes that the value semantics.
(define (a-resize-vector old n fill)
  (let ((new (make-vector n '())) (m (vector-length old)))
    (do ((i 0 (fx+ i 1))) ((fx>= i n) new)
      (vector-set! new i (if (fx< i m) (vector-ref old i) (fill))))))
(define (a-resize-u8vector old n init)
  (let ((new (make-u8vector n init)) (m (u8vector-length old)))
    (do ((i 0 (fx+ i 1))) ((fx>= i (fxmin n m)) new)
      (u8vector-set! new i (u8vector-ref old i)))))

;; --- host I/O (the driver's, not ACL2's) -----------------------------------------------
(define (octets->u8vector xs) (list->u8vector xs))
(define (read-file-u8vector path)
  (call-with-input-file path (lambda (p) (read-u8vector #f p)) #:binary))
(define (parse-chunks data)
  ;; the length-prefixed chunk file of tests/test_native_served_differential.py
  (let ((n (u8vector-length data)))
    (let loop ((at 0) (acc '()))
      (if (fx>= at n) (reverse acc)
          (let lp ((i at) (count 0))
            (let ((b (u8vector-ref data i)))
              (if (fx= b 10)
                  (let ((start (fx+ i 1)))
                    (let collect ((k (fx- (fx+ start count) 1)) (octets '()))
                      (if (fx< k start)
                          (loop (fx+ start count) (cons octets acc))
                          (collect (fx- k 1) (cons (u8vector-ref data k) octets)))))
                  (lp (fx+ i 1) (+ (* count 10) (fx- b 48))))))))))
(define (write-octets xs) (write-u8vector (list->u8vector xs)) (flush-output))
