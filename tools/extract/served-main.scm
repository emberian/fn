;;; tools/extract/served-main.scm -- the host driver of the extracted served
;;; step machine.  It does what host/native/io.lisp does around the same ACL2
;;; functions and nothing more: read the chunk file, create the arena, select
;;; the seeded archive, and either
;;;   model FILE   -- fn-reader-model-octets over the whole chunk list (the
;;;                   `--fn model CHUNKS -' side of the served differential);
;;;   socket FILE  -- fn-reader-reset, then fn-reader-chunk per chunk, a
;;;                   refused outcome after a submission, stopping at close
;;;                   (fnn-serve-client's loop, with the chunks as the reads);
;;;   bench FILE N -- the model N times, printing the per-run time.
;;; Every decision is the extracted code's; this file frames nothing.
(include "runtime.scm")
(include "served.scm")
(include "native.scm")
(include "hostio.scm")
(include "probes.scm")

(define (global name) (a-get-global name acl2-state))
(define-syntax ignore-values
  (syntax-rules () ((_ e) (call-with-values (lambda () e) (lambda vs vs)))))

(define (select-seed arena)
  (ignore-values (|b:ACL2::FN-READER-SET-POSTING| '() acl2-state))
  (call-with-values (lambda () (|b:ACL2::FN-READER-USE-SEED| arena acl2-state))
    (lambda (erp val arena2 st)
      (unless (eq? val '|KEYWORD::READY|)
        (error "reader archive is not NNTP-projectable" val)))))

(define (model-octets chunks arena)
  (call-with-values (lambda () (|b:ACL2::FN-READER-MODEL-OCTETS| chunks arena acl2-state))
    (lambda (erp val st) val)))

(define (outcome-exit class text)
  ;; fnn-main's report and ACL2's exit code for the class (fn-outcome-code)
  (let ((port (current-error-port)))
    (display "store: " port) (display text port) (newline port))
  (exit (|b:ACL2::FN-OUTCOME-CODE|
         (case class
           ((|KEYWORD::REFUSED| |KEYWORD::OPEN-REFUSAL|) '|KEYWORD::REFUSED|)
           ((|KEYWORD::INDETERMINATE|) '|KEYWORD::FENCED|)
           ((|KEYWORD::USAGE|) '|KEYWORD::USAGE|)
           (else '|KEYWORD::FAULT|)))))

;; The reader over a store (fnn-reader-prepare with a store root): the open is
;; host/store-open-host.lisp's fn-xo-open-store, extracted; then the store is
;; selected as fnn-reader-select selects it.
(define (select-store root arena)
  (let ((lg (|f:ACL2::CREATE-FN-OCTETS$C|)))
    (call-with-values (lambda () (|b:ACL2::FN-XO-OPEN-STORE| root lg arena acl2-state))
      (lambda (result lg2 arena2 st)
        (unless (eq? (car result) '|KEYWORD::OK|)
          (outcome-exit (car result) (cadr result)))))
    (ignore-values (|b:ACL2::FN-READER-SET-POSTING| '() acl2-state))
    (call-with-values (lambda () (|b:ACL2::FN-READER-USE-STORE| acl2-state))
      (lambda (erp val st)
        (unless (eq? val '|KEYWORD::READY|)
          (outcome-exit '|KEYWORD::REFUSED| "reader archive is not NNTP-projectable"))))))

(define store-root #f)
(define (select arena) (if store-root (select-store store-root arena) (select-seed arena)))

(define (model chunks)
  (let ((arena (|f:ACL2::CREATE-FN-ARENA$X|)))
    (select arena)
    (model-octets chunks arena)))

(define (socket chunks)
  (let ((arena (|f:ACL2::CREATE-FN-ARENA$X|)) (out '()))
    (select arena)
    (ignore-values (|b:ACL2::FN-READER-RESET| acl2-state))
    (set! out (cons (global '|ACL2::FN-READER-OUTPUT|) out))
    (let loop ((cs chunks))
      (unless (null? cs)
        (ignore-values (|b:ACL2::FN-READER-CHUNK| (car cs) arena acl2-state))
        (set! out (cons (global '|ACL2::FN-READER-OUTPUT|) out))
        (unless (null? (global '|ACL2::FN-READER-SUBMIT-OCTETS|))
          (ignore-values (|b:ACL2::FN-READER-OUTCOME| '|KEYWORD::REFUSED| acl2-state))
          (set! out (cons (global '|ACL2::FN-READER-OUTPUT|) out)))
        (when (null? (global '|ACL2::FN-READER-CLOSEP|))
          (loop (cdr cs)))))
    (apply append (reverse out))))

(define (post chunks)
  ;; posting allowed and one fixed clock observation (post-ref.lisp's)
  (let ((arena (|f:ACL2::CREATE-FN-ARENA$X|)) (out '()))
    (ignore-values (|b:ACL2::FN-READER-SET-POSTING| '|COMMON-LISP::T| acl2-state))
    (call-with-values (lambda () (|b:ACL2::FN-READER-USE-SEED| arena acl2-state))
      (lambda (erp val arena2 st) #t))
    (ignore-values (|b:ACL2::FN-READER-OBSERVE-CLOCK| 123456 843000000000 1000 acl2-state))
    (ignore-values (|b:ACL2::FN-READER-RESET| acl2-state))
    (set! out (cons (global '|ACL2::FN-READER-OUTPUT|) out))
    (let loop ((cs chunks))
      (unless (null? cs)
        (ignore-values (|b:ACL2::FN-READER-CHUNK| (car cs) arena acl2-state))
        (set! out (cons (global '|ACL2::FN-READER-OUTPUT|) out))
        (unless (null? (global '|ACL2::FN-READER-SUBMIT-OCTETS|))
          (ignore-values (|b:ACL2::FN-READER-OUTCOME| '|KEYWORD::REFUSED| acl2-state))
          (set! out (cons (global '|ACL2::FN-READER-OUTPUT|) out)))
        (when (null? (global '|ACL2::FN-READER-CLOSEP|))
          (loop (cdr cs)))))
    (apply append (reverse out))))

(define (probe-value v)
  ;; tools/extract/probes.py's printer: integers and lists of them, NIL, else "value"
  (cond ((exact-integer? v) (number->string v))
        ((null? v) "NIL")
        ((list? v) (string-append "(" (string-intersperse (map probe-value v) " ") ")"))
        (else "value")))

(define (run-probes)
  (let ((arena (|b:ACL2::CREATE-FN-ARENA|)))
    (for-each
     (lambda (p)
       (let ((line
              (condition-case
               (call-with-values (caddr p)
                 (lambda vs (string-append "returned " (probe-value (car vs)))))
               (e (fn-fault)
                  (string-append (symbol->string (fn-fault-kind e)) " " (fn-fault-message e))))))
         (print "PROBE " (car p) " " line)))
     (boundary-probes arena))))

;; ACL2's exit code for a fault (books/outcome-class.lisp fn-outcome-code),
;; as host/native/io.lisp's +fnn-exit-fault+ reads it.
(define (fault-exit e)
  (let ((port (current-error-port)))
    (display "store: " port) (display (fn-fault-message e) port) (newline port))
  (exit (|b:ACL2::FN-OUTCOME-CODE| '|KEYWORD::FAULT|)))

(define (main args)
  ;; model|socket CHUNKS [STORE-ROOT]; bench CHUNKS N [STORE-ROOT]
  (let* ((verb (car args))
         (chunks (parse-chunks (read-file-u8vector (cadr args)))))
    (let ((root (if (string=? verb "bench") (and (pair? (cdddr args)) (cadddr args))
                    (and (pair? (cddr args)) (caddr args)))))
      (when (and root (not (string=? root "-")))
        ;; fnn-absolute
        (set! store-root (if (char=? (string-ref root 0) #\/) root
                             (string-append (current-directory) "/" root)))))
    (cond ((string=? verb "model") (write-octets (model chunks)))
          ((string=? verb "socket") (write-octets (socket chunks)))
          ((string=? verb "post") (write-octets (post chunks)))
          ((string=? verb "bench")
           ;; the archive is selected once, as the reader selects it once
           ;; before it accepts clients; each run is one connection's model
           (let ((n (string->number (caddr args)))
                 (arena (|f:ACL2::CREATE-FN-ARENA$X|)))
             (select arena)
             (model-octets chunks arena)
             (let ((t0 (current-process-milliseconds)) (g0 (current-gc-milliseconds)))
               (do ((i 0 (+ i 1))) ((= i n)) (model-octets chunks arena))
               (let ((t1 (current-process-milliseconds)) (g1 (current-gc-milliseconds)))
                 (fprintf (current-error-port) "bench ~a runs ~a ms ~a us/run gc ~a ms~%"
                          n (- t1 t0) (/ (* 1000.0 (- t1 t0)) n) (- g1 g0))))))
          (else (error "usage: model|socket FILE | bench FILE N")))))

(native-self-check (lambda (octets) (vector (list->u8vector octets) (length octets))))
(let ((args (command-line-arguments)))
  (if (and (pair? args) (string=? (car args) "probe"))
      (run-probes)
      (condition-case (main args)
        (e (fn-fault) (fault-exit e)))))
