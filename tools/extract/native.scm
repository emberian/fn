;;; tools/extract/native.scm -- native SHA-256 for the extracted program
;;; (lane extract-2; the counterpart of host/native/digest.lisp, lane
;;; digest-native).  Hand code in the trust boundary, beside runtime.scm.
;;;
;;; The image replaces the raw definitions of fn-sha256-stobj,
;;; fn-sha256-of-string and fn-sha256-of-prefixed-buffer by libcrypto's
;;; EVP SHA-256 after a start-up check; this file does the same for the
;;; extracted program: tools/extract/chicken.py (NATIVE) sends every call of
;;; the three, and the window digest fn-sha256-of-prefixed-range (the log
;;; walk's frame check; the image does not replace it yet), (fn-digest reaches fn-sha256-stobj through its attachment) to
;;; the procedures below, and the extracted ACL2 definitions stay as the
;;; reference each falls back to outside the fast domain and the self-check
;;; compares against.  The fast domain is digest.lisp's: a list is digested
;;; while every element is an (unsigned-byte 8) and stops at its first
;;; non-cons tail (fn-sha256-fix-octets' reading); at a non-octet element the
;;; reference answers.  A string is its byte string.  A prefixed buffer is an
;;; fn-octets$c record (slot 0 the u8vector, slot 1 the fill).  That the
;;; primitive computes SHA-256 is A-CRYPTO-NATIVE (specs/failures.md).
(foreign-declare "#include <openssl/evp.h>")

(define %md-new (foreign-lambda c-pointer "EVP_MD_CTX_new"))
(define %md-free (foreign-lambda void "EVP_MD_CTX_free" c-pointer))
(define %md-init
  (foreign-lambda* int ((c-pointer ctx)) "C_return(EVP_DigestInit_ex(ctx, EVP_sha256(), NULL));"))
(define %md-update
  (foreign-lambda* int ((c-pointer ctx) (u8vector buf) (size_t start) (size_t n))
    "C_return(n == 0 ? 1 : EVP_DigestUpdate(ctx, buf + start, n));"))
(define %md-update-string
  (foreign-lambda* int ((c-pointer ctx) (scheme-pointer s) (size_t n))
    "C_return(n == 0 ? 1 : EVP_DigestUpdate(ctx, s, n));"))
(define %md-final
  (foreign-lambda* int ((c-pointer ctx) (u8vector out)) "C_return(EVP_DigestFinal_ex(ctx, out, NULL));"))

(define (native-digest-check code what)
  (unless (eqv? code 1)
    (a-fault 'fault (string-append "native digest: " what " failed"))))

(define native-chunk (make-u8vector 16384 0))

(define (native-with-context proc)
  (let ((ctx (%md-new)))
    (unless ctx (a-fault 'fault "native digest: EVP_MD_CTX_new failed"))
    (native-digest-check (%md-init ctx) "EVP_DigestInit_ex")
    (let ((answer (proc ctx)))
      (if answer
          (let ((out (make-u8vector 32 0)))
            (native-digest-check (%md-final ctx out) "EVP_DigestFinal_ex")
            (%md-free ctx)
            (u8vector->list out))
          (begin (%md-free ctx) #f)))))

;; Feed the list's octets through the chunk; #f at the first non-octet.
(define (native-update-list ctx m)
  (let loop ((m m) (fill 0))
    (cond ((not (pair? m))
           (native-digest-check (%md-update ctx native-chunk 0 fill) "EVP_DigestUpdate") #t)
          ((let ((x (car m))) (and (fixnum? x) (fx>= x 0) (fx< x 256)))
           (u8vector-set! native-chunk fill (car m))
           (if (fx= (fx+ fill 1) 16384)
               (begin (native-digest-check (%md-update ctx native-chunk 0 16384) "EVP_DigestUpdate")
                      (loop (cdr m) 0))
               (loop (cdr m) (fx+ fill 1))))
          (else #f))))

(define (a-native-sha256-list m)
  (or (native-with-context (lambda (ctx) (native-update-list ctx m)))
      (|f:ACL2::FN-SHA256-STOBJ| m)))

(define (a-native-sha256-string s)
  (or (and (string? s)
           (native-with-context
            (lambda (ctx)
              (native-digest-check (%md-update-string ctx s (string-length s)) "EVP_DigestUpdate")
              #t)))
      (|f:ACL2::FN-SHA256-OF-STRING| s)))

(define (a-native-sha256-prefixed-range prefix a wn st)
  ;; fn-sha256-of-prefixed-range: PREFIX's octets, then the buffer's [A, A+WN)
  ;; (its guard: A+WN within the fill); the extracted definition otherwise
  (or (and (fixnum? a) (fixnum? wn) (fx>= a 0) (fx>= wn 0)
           (vector? st) (fx= (vector-length st) 2) (u8vector? (vector-ref st 0))
           (fixnum? (vector-ref st 1)) (fx<= (fx+ a wn) (vector-ref st 1))
           (fx<= (vector-ref st 1) (u8vector-length (vector-ref st 0)))
           (native-with-context
            (lambda (ctx)
              (and (native-update-list ctx prefix)
                   (begin (native-digest-check (%md-update ctx (vector-ref st 0) a wn) "EVP_DigestUpdate")
                          #t)))))
      (|f:ACL2::FN-SHA256-OF-PREFIXED-RANGE| prefix a wn st)))

(define (a-native-sha256-prefixed-buffer prefix st)
  (or (and (vector? st) (fx= (vector-length st) 2)
           (u8vector? (vector-ref st 0)) (fixnum? (vector-ref st 1))
           (fx>= (vector-ref st 1) 0) (fx<= (vector-ref st 1) (u8vector-length (vector-ref st 0)))
           (native-with-context
            (lambda (ctx)
              (and (native-update-list ctx prefix)
                   (begin (native-digest-check
                           (%md-update ctx (vector-ref st 0) 0 (vector-ref st 1)) "EVP_DigestUpdate")
                          #t)))))
      (|f:ACL2::FN-SHA256-OF-PREFIXED-BUFFER| prefix st)))

;; The start-up check (digest.lisp's): the FIPS 180-4 known answers through
;; each of the three, and the reference differential on test messages
;; (the same LCG as fnn-digest-test-message).  A disagreement is a broken
;; library: the program refuses to start (exit 5, fnn-native-startup's).
(define native-known-answers
  '(("" . "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855")
    ("abc" . "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad")
    ("abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"
     . "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1")))

(define (native-hex octets)
  (apply string-append
         (map (lambda (b) (let ((s (number->string b 16))) (if (fx< b 16) (string-append "0" s) s)))
              octets)))

(define (native-test-message n seed)
  (let loop ((i 0) (st seed) (acc '()))
    (if (fx= i n) (reverse acc)
        (let ((st2 (bitwise-and (+ (* st 1103515245) 12345) #x7fffffff)))
          (loop (fx+ i 1) st2 (cons (bitwise-and (arithmetic-shift st2 -16) 255) acc))))))

(define (native-self-check make-buffer)
  (define (fail what)
    (let ((port (current-error-port)))
      (display "fn: native digest self-check failed: " port) (display what port) (newline port))
    (exit 5))
  (for-each
   (lambda (ka)
     (let* ((s (car ka)) (octets (map char->integer (string->list s))))
       (unless (string=? (native-hex (a-native-sha256-list octets)) (cdr ka)) (fail "list"))
       (unless (string=? (native-hex (a-native-sha256-string s)) (cdr ka)) (fail "string"))
       (unless (string=? (native-hex (a-native-sha256-prefixed-buffer '() (make-buffer octets))) (cdr ka))
         (fail "buffer"))))
   native-known-answers)
  (for-each
   (lambda (n)
     (let ((m (native-test-message n (fx+ n 7))))
       (unless (equal? (a-native-sha256-list m) (|f:ACL2::FN-SHA256-STOBJ| m)) (fail "list differential"))
       (let ((k (quotient n 3)) (b (make-buffer m)))
         (unless (equal? (a-native-sha256-prefixed-range (list-head m 5) k (quotient n 2) b)
                         (|f:ACL2::FN-SHA256-OF-PREFIXED-RANGE| (list-head m 5) k (quotient n 2) b))
           (fail "range differential")))
       (let ((k (quotient n 3)))
         (unless (equal? (a-native-sha256-prefixed-buffer (list-head m k) (make-buffer (list-tail m k)))
                         (|f:ACL2::FN-SHA256-OF-PREFIXED-BUFFER| (list-head m k) (make-buffer (list-tail m k))))
           (fail "buffer differential")))))
   '(0 1 55 56 63 64 65 119 120 127 128 1000 16383 16384 16385 40000)))

(define (list-head l k) (if (or (fx= k 0) (not (pair? l))) '() (cons (car l) (list-head (cdr l) (fx- k 1)))))
