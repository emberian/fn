;;; tools/extract/native.scm -- the native digests of the extracted program
;;; (lane extract-2; the counterpart of host/native/digest.lisp).  Hand code
;;; in the trust boundary, beside runtime.scm.
;;;
;;; BLAKE3 (fn's digest since format 10, lane blake3-digest): the image
;;; replaces the raw definitions of fn-blake3-stobj, fn-blake3-of-prefixed-
;;; buffer and fn-blake3-of-prefixed-range by lib/libfn-blake3 (the vendored
;;; reference C behind host/native/fn-blake3.c) after a start-up check; this
;;; file does the same with the same library (tools/extract/build.sh builds it
;;; with tools/build_blake3.sh and links it): tools/extract/chicken.py
;;; (NATIVE) sends every call of the three to the procedures below, and the
;;; extracted ACL2 definitions stay as the reference each falls back to
;;; outside the fast domain and the self-check compares against.
;;;
;;; SHA-256 (libcrypto's EVP) is bound for fn-sha256 alone: RFC 8315's
;;; Cancel-Lock hash (books/control-authority.lisp over books/sha256.lisp),
;;; fn's only SHA-256 since format 10.
;;;
;;; The fast domain is digest.lisp's: a list is digested while every element
;;; is an (unsigned-byte 8) and stops at its first non-cons tail
;;; (fn-b3-fix-octets' and fn-sha256-fix-octets' reading); at a non-octet
;;; element the reference answers.  A prefixed buffer is an fn-octets$c
;;; record (slot 0 the u8vector, slot 1 the fill).  That the primitives
;;; compute BLAKE3 and SHA-256 is A-CRYPTO-NATIVE (specs/failures.md).
(foreign-declare "#include <stddef.h>
#include <stdint.h>
size_t fn_b3_hasher_size(void);
void fn_b3_init(void *h);
void fn_b3_update(void *h, const uint8_t *in, size_t len);
void fn_b3_final(const void *h, uint8_t out[32]);")

(define %b3-size (foreign-lambda size_t "fn_b3_hasher_size"))
(define %b3-init (foreign-lambda void "fn_b3_init" u8vector))
(define %b3-update
  (foreign-lambda* void ((u8vector h) (u8vector buf) (size_t start) (size_t n))
    "if (n) fn_b3_update(h, buf + start, n);"))
(define %b3-final (foreign-lambda void "fn_b3_final" u8vector u8vector))

;; The hasher's state lives in a u8vector (8-aligned, as the C asks; the
;; state holds no pointers, so the collector may move it between calls).
(define (native-b3-with proc)
  (let ((h (make-u8vector (+ (%b3-size) 8) 0)))
    (%b3-init h)
    (and (proc h)
         (let ((out (make-u8vector 32 0)))
           (%b3-final h out)
           (u8vector->list out)))))

(define b3-chunk (make-u8vector 16384 0))

;; Feed the list's octets through the chunk; #f at the first non-octet.
(define (native-b3-update-list h m)
  (let loop ((m m) (fill 0))
    (cond ((not (pair? m)) (%b3-update h b3-chunk 0 fill) #t)
          ((let ((x (car m))) (and (fixnum? x) (fx>= x 0) (fx< x 256)))
           (u8vector-set! b3-chunk fill (car m))
           (if (fx= (fx+ fill 1) 16384)
               (begin (%b3-update h b3-chunk 0 16384) (loop (cdr m) 0))
               (loop (cdr m) (fx+ fill 1))))
          (else #f))))

(define (native-buffer? st)
  (and (vector? st) (fx= (vector-length st) 2) (u8vector? (vector-ref st 0))
       (fixnum? (vector-ref st 1)) (fx>= (vector-ref st 1) 0)
       (fx<= (vector-ref st 1) (u8vector-length (vector-ref st 0)))))

(define (a-native-blake3-list m)
  (or (native-b3-with (lambda (h) (native-b3-update-list h m)))
      (|f:ACL2::FN-BLAKE3-STOBJ| m)))

(define (a-native-blake3-prefixed-range prefix a wn st)
  ;; fn-blake3-of-prefixed-range: PREFIX's octets, then the buffer's [A, A+WN)
  ;; (its guard: A+WN within the fill); the extracted definition otherwise
  (or (and (fixnum? a) (fixnum? wn) (fx>= a 0) (fx>= wn 0) (native-buffer? st)
           (fx<= (fx+ a wn) (vector-ref st 1))
           (native-b3-with
            (lambda (h)
              (and (native-b3-update-list h prefix)
                   (begin (%b3-update h (vector-ref st 0) a wn) #t)))))
      (|f:ACL2::FN-BLAKE3-OF-PREFIXED-RANGE| prefix a wn st)))

(define (a-native-blake3-prefixed-buffer prefix st)
  (or (and (native-buffer? st)
           (native-b3-with
            (lambda (h)
              (and (native-b3-update-list h prefix)
                   (begin (%b3-update h (vector-ref st 0) 0 (vector-ref st 1)) #t)))))
      (|f:ACL2::FN-BLAKE3-OF-PREFIXED-BUFFER| prefix st)))

(foreign-declare "#include <openssl/evp.h>")

(define %md-new (foreign-lambda c-pointer "EVP_MD_CTX_new"))
(define %md-free (foreign-lambda void "EVP_MD_CTX_free" c-pointer))
(define %md-init
  (foreign-lambda* int ((c-pointer ctx)) "C_return(EVP_DigestInit_ex(ctx, EVP_sha256(), NULL));"))
(define %md-update
  (foreign-lambda* int ((c-pointer ctx) (u8vector buf) (size_t start) (size_t n))
    "C_return(n == 0 ? 1 : EVP_DigestUpdate(ctx, buf + start, n));"))
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
      (|f:ACL2::FN-SHA256| m)))

;; The start-up check (digest.lisp's): BLAKE3's known answers (the
;; official vectors' input, octet i = i mod 251, digest.lisp's
;; *fnn-digest-known-answers* up to 16 KiB) through each of the three, the
;; reference differential on test messages (the same LCG as
;; fnn-digest-test-message), and SHA-256's FIPS 180-4 answers through the
;; Cancel-Lock hash.  A disagreement is a broken library: the program refuses
;; to start (exit 5, fnn-native-startup's).
(define native-b3-known-answers
  '((0 . "af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262")
    (1 . "2d3adedff11b61f14c886e35afa036736dcd87a74d27b5c1510225d0f592e213")
    (64 . "4eed7141ea4a5cd4b788606bd23f46e212af9cacebacdc7d1f4c6dc7f2511b98")
    (65 . "de1e5fa0be70df6d2be8fffd0e99ceaa8eb6e8c93a63f2d8d1c30ecb6b263dee")
    (1023 . "10108970eeda3eb932baac1428c7a2163b0e924c9a9e25b35bba72b28f70bd11")
    (1024 . "42214739f095a406f3fc83deb889744ac00df831c10daa55189b5d121c855af7")
    (1025 . "d00278ae47eb27b34faecf67b4fe263f82d5412916c1ffd97c8cb7fb814b8444")
    (2048 . "e776b6028c7cd22a4d0ba182a8bf62205d2ef576467e838ed6f2529b85fba24a")
    (2049 . "5f4d72f40d7a5f82b15ca2b2e44b1de3c2ef86c426c95c1af0b6879522563030")
    (8193 . "bab6c09cb8ce8cf459261398d2e7aef35700bf488116ceb94a36d0f5f1b7bc3b")
    (16384 . "f875d6646de28985646f34ee13be9a576fd515f76b5b0a26bb324735041ddde4")))

(define native-sha-known-answers
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

(define (native-vector-input n)
  (let loop ((i (fx- n 1)) (acc '()))
    (if (fx< i 0) acc (loop (fx- i 1) (cons (fxmod i 251) acc)))))

(define (native-self-check make-buffer)
  (define (fail what)
    (let ((port (current-error-port)))
      (display "fn: native digest self-check failed: " port) (display what port) (newline port))
    (exit 5))
  (for-each
   (lambda (ka)
     (let* ((n (car ka)) (octets (native-vector-input n)) (half (quotient n 2))
            (k (min n 7)))
       (for-each
        (lambda (got) (unless (string=? (native-hex got) (cdr ka)) (fail (list 'blake3 n))))
        (list (a-native-blake3-list octets)
              (a-native-blake3-prefixed-buffer '() (make-buffer octets))
              (a-native-blake3-prefixed-buffer (list-head octets half)
                                               (make-buffer (native-drop octets half)))
              (a-native-blake3-prefixed-range
               (list-head octets k) 3 (fx- n k)
               (make-buffer (append '(9 9 9) (native-drop octets k) '(9))))))))
   native-b3-known-answers)
  (for-each
   (lambda (ka)
     (unless (string=? (native-hex (a-native-sha256-list (map char->integer (string->list (car ka)))))
                       (cdr ka))
       (fail "sha256 list")))
   native-sha-known-answers)
  (for-each
   (lambda (n)
     (let ((m (native-test-message n (fx+ n 7))))
       (unless (equal? (a-native-blake3-list m) (|f:ACL2::FN-BLAKE3-STOBJ| m))
         (fail "blake3 list differential"))
       (let ((k (quotient n 3)) (b (make-buffer m)))
         (unless (equal? (a-native-blake3-prefixed-range (list-head m 5) k (quotient n 2) b)
                         (|f:ACL2::FN-BLAKE3-OF-PREFIXED-RANGE| (list-head m 5) k (quotient n 2) b))
           (fail "blake3 range differential")))
       (let ((k (quotient n 3)))
         (unless (equal? (a-native-blake3-prefixed-buffer (list-head m k) (make-buffer (native-drop m k)))
                         (|f:ACL2::FN-BLAKE3-OF-PREFIXED-BUFFER| (list-head m k)
                                                                (make-buffer (native-drop m k))))
           (fail "blake3 buffer differential")))))
   ;; the block and chunk boundary lengths; the extracted ACL2 reference is
   ;; slow in this program, so the long messages stay in the per-build
   ;; qualification (make extract-check's per-function differential)
   '(0 1 63 64 65 127 128 200 1023 1024 1025)))

(define (native-drop l k) (if (or (fx= k 0) (not (pair? l))) l (native-drop (cdr l) (fx- k 1))))
(define (list-head l k) (if (or (fx= k 0) (not (pair? l))) '() (cons (car l) (list-head (cdr l) (fx- k 1)))))
