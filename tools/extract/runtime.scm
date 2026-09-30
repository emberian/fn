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
        (chicken time) (chicken gc) (chicken format) (chicken condition) (chicken port)
        srfi-4 srfi-69)

(define-constant acl2-t '|COMMON-LISP::T|)
(define-inline (a-bool x) (if x '|COMMON-LISP::T| '()))

;; An extracted world has no ACL2 undo/redefinition operations. Registry
;; identities distinguish congruent stobj names in stobj-table fields.
(define a-stobj-table-keys (make-hash-table eq?))
(define (a-register-stobj-names names)
  (for-each (lambda (name)
              (unless (hash-table-exists? a-stobj-table-keys name)
                (hash-table-set! a-stobj-table-keys name (gensym)))) names))
(define (a-stobj-table-key name)
  (if (hash-table-exists? a-stobj-table-keys name)
      (hash-table-ref a-stobj-table-keys name)
      (error "stobj-table key is not in the extracted registry" name)))

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
; CL's floor and mod (flooring division); on two integers without a ratnum
(define (a-floor i j)
  (if (and (exact-integer? i) (exact-integer? j))
      (let ((q (quotient i j)))
        (if (and (not (= (* q j) i)) (not (eq? (negative? i) (negative? j)))) (- q 1) q))
      (floor (/ i j))))
(define (a-mod i j)
  (if (and (exact-integer? i) (exact-integer? j))
      (modulo i j)
      (- i (* (floor (/ i j)) j))))
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

;; --- faults at the boundary (e1; host/native/io.lisp fnn-entry-guard, fnn-call) --
;; A fault is a condition (fn-fault kind message); the driver reports it as the
;; image's fnn-main reports an fnn-store-fault and exits with ACL2's :fault code.
(define (a-fault kind msg)
  (abort (make-property-condition 'fn-fault 'kind kind 'message msg)))
(define (fn-fault? c) ((condition-predicate 'fn-fault) c))
(define (fn-fault-kind c) ((condition-property-accessor 'fn-fault 'kind) c))
(define (fn-fault-message c) ((condition-property-accessor 'fn-fault 'message) c))
(define (a-downcase s)
  (list->string (map (lambda (c) (if (and (char>=? c #\A) (char<=? c #\Z))
                                     (integer->char (fx+ (char->integer c) 32)) c))
                     (string->list s))))
(define (a-plural n) (if (eqv? n 1) "" "s"))
;; SBCL's ~s of a symbol read in the ACL2 package
(define (a-symbol-text x)
  (if (null? x) "NIL"
      (receive (p n) (a-split-symbol x)
        (cond ((string=? p "KEYWORD") (string-append ":" n))
              ((or (string=? p "ACL2") (string=? p "COMMON-LISP")) n)
              (else (string-append p "::" n))))))
;; SBCL's type-of, printed with ~a, for the values an ACL2 entry can be handed
(define (a-type-of-text x)
  (cond ((eq? x '|COMMON-LISP::T|) "BOOLEAN")
        ((null? x) "NULL")
        ((symbol? x) (receive (p n) (a-split-symbol x) (if (string=? p "KEYWORD") "KEYWORD" "SYMBOL")))
        ((char? x) (let ((k (char->integer x)))
                     (if (or (fx= k 10) (and (fx>= k 32) (fx<= k 126))) "STANDARD-CHAR" "CHARACTER")))
        ((string? x) (sprintf "(SIMPLE-ARRAY CHARACTER (~a))" (string-length x)))
        ((and (number? x) (exact? x) (real? x) (not (integer? x))) "RATIO")
        ((number? x) "(COMPLEX RATIONAL)")
        (else "T")))
;; fnn-entry-guard-describe: a bounded description of a value's kind
(define (a-describe v)
  (cond ((and (exact-integer? v) (>= v 0)) (sprintf "the natural ~a" v))
        ((exact-integer? v) (sprintf "the integer ~a" v))
        ((null? v) "NIL")
        ((string? v) (sprintf "a string of ~a characters" (string-length v)))
        ((symbol? v) (sprintf "the symbol ~a" (a-symbol-text v)))
        ((pair? v)
         (let loop ((tail v) (i 0))
           (if (and (pair? tail) (fx< i 1000000)) (loop (cdr tail) (fx+ i 1))
               (sprintf "a list of ~a element~a (first ~a)" i (a-plural i)
                        (let ((head (car v)))
                          (cond ((exact-integer? head) head)
                                ((pair? head) "a list")
                                (else (a-type-of-text head))))))))
        ((u8vector? v) (let ((n (u8vector-length v))) (sprintf "a vector of ~a element~a" n (a-plural n))))
        ((vector? v) (let ((n (vector-length v))) (sprintf "a vector of ~a element~a" n (a-plural n))))
        (else (sprintf "a ~a" (a-downcase (a-type-of-text v))))))
(define (a-entry-arity name n args)
  (let ((given (length args)))
    (unless (fx= given n)
      (a-fault 'host-entry-guard
               (sprintf "host-entry-guard: ~a takes ~a argument~a (stobjs and state included); the host passed ~a"
                        name n (a-plural n) given)))))
(define (a-entry-kind-fault name position formal kind recognizer value)
  (a-fault 'host-entry-guard
           (sprintf "host-entry-guard: ~a argument ~a (~a) must be ~a (~a); the host passed ~a"
                    name position formal kind recognizer (a-describe value))))
;; The *1* counterpart's guard check failed.  In the image the *1* function
;; prints ACL2's guard-violation diagnostic (the untranslated guard and the
;; arguments, through ACL2's printer) and halts; fnn-call turns the halt into
;; the store fault "ACL2 error in ENTRY: ACL2 Halted" (exit :fault).  The
;; fault's message is the refusal and is reproduced byte for byte; the
;; diagnostic goes to stderr here in one line (the guard is not printed).
(define a-current-entry "")
(define (a-guard-violation name args)
  (let ((port (current-error-port)))
    (display "ACL2 Error in ACL2-INTERFACE:  The guard for the function call (" port)
    (display name port)
    (display " ...) is violated by the arguments in the call." port)
    (newline port))
  (a-fault 'fault (sprintf "ACL2 error in ~a: ACL2 Halted" a-current-entry)))
;; fnn-call around the entry: the entry's name for its faults, and a raw
;; error inside it (an ACL2 hard error, a realizer's refusal) turned into the
;; store fault "ACL2 error in ENTRY: ..." (exit :fault), as fnn-call's
;; handler-case turns a serious-condition into one.  The message after the
;; colon is the condition's own text, which differs between the two Lisps.
(define (a-entry-call name thunk)
  (set! a-current-entry name)
  (condition-case (thunk)
    (e (fn-fault) (abort e))
    (e (exn)
       (a-fault 'fault (sprintf "ACL2 error in ~a: ~a" name
                                ((condition-property-accessor 'exn 'message) e))))))

;; --- the durable-extent realizers: tools/extract/hostio.scm (A-DURABLE-EXTENT) --


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

;; --- built-ins raw Lisp compiles inline (chicken.py INLINE) ---------------------
(define-inline (a-zp x) (or (not (exact-integer? x)) (<= x 0)))
(define-inline (a-zip x) (or (not (exact-integer? x)) (= x 0)))
(define-inline (a-natp x) (and (exact-integer? x) (>= x 0)))
(define-inline (a-posp x) (and (exact-integer? x) (> x 0)))
(define-inline (a-booleanp x) (or (eq? x '()) (eq? x '|COMMON-LISP::T|)))
(define-inline (a-nfix x) (if (and (exact-integer? x) (>= x 0)) x 0))
(define-inline (a-ifix x) (if (exact-integer? x) x 0))
(define-inline (a-fix x) (if (number? x) x 0))
