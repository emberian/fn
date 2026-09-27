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

(define (global name) (a-get-global name acl2-state))
(define-syntax ignore-values
  (syntax-rules () ((_ e) (call-with-values (lambda () e) (lambda vs vs)))))

(define (select-seed arena)
  (ignore-values (|f:ACL2::FN-READER-SET-POSTING| '() acl2-state))
  (call-with-values (lambda () (|f:ACL2::FN-READER-USE-SEED| arena acl2-state))
    (lambda (erp val arena2 st)
      (unless (eq? val '|KEYWORD::READY|)
        (error "reader archive is not NNTP-projectable" val)))))

(define (model-octets chunks arena)
  (call-with-values (lambda () (|f:ACL2::FN-READER-MODEL-OCTETS| chunks arena acl2-state))
    (lambda (erp val st) val)))

(define (model chunks)
  (let ((arena (|f:ACL2::CREATE-FN-ARENA$X|)))
    (select-seed arena)
    (model-octets chunks arena)))

(define (socket chunks)
  (let ((arena (|f:ACL2::CREATE-FN-ARENA$X|)) (out '()))
    (select-seed arena)
    (ignore-values (|f:ACL2::FN-READER-RESET| acl2-state))
    (set! out (cons (global '|ACL2::FN-READER-OUTPUT|) out))
    (let loop ((cs chunks))
      (unless (null? cs)
        (ignore-values (|f:ACL2::FN-READER-CHUNK| (car cs) arena acl2-state))
        (set! out (cons (global '|ACL2::FN-READER-OUTPUT|) out))
        (unless (null? (global '|ACL2::FN-READER-SUBMIT-OCTETS|))
          (ignore-values (|f:ACL2::FN-READER-OUTCOME| '|KEYWORD::REFUSED| acl2-state))
          (set! out (cons (global '|ACL2::FN-READER-OUTPUT|) out)))
        (when (null? (global '|ACL2::FN-READER-CLOSEP|))
          (loop (cdr cs)))))
    (apply append (reverse out))))

(define (post chunks)
  ;; posting allowed and one fixed clock observation (post-ref.lisp's)
  (let ((arena (|f:ACL2::CREATE-FN-ARENA$X|)) (out '()))
    (ignore-values (|f:ACL2::FN-READER-SET-POSTING| '|COMMON-LISP::T| acl2-state))
    (call-with-values (lambda () (|f:ACL2::FN-READER-USE-SEED| arena acl2-state))
      (lambda (erp val arena2 st) #t))
    (ignore-values (|f:ACL2::FN-READER-OBSERVE-CLOCK| 123456 843000000000 1000 acl2-state))
    (ignore-values (|f:ACL2::FN-READER-RESET| acl2-state))
    (set! out (cons (global '|ACL2::FN-READER-OUTPUT|) out))
    (let loop ((cs chunks))
      (unless (null? cs)
        (ignore-values (|f:ACL2::FN-READER-CHUNK| (car cs) arena acl2-state))
        (set! out (cons (global '|ACL2::FN-READER-OUTPUT|) out))
        (unless (null? (global '|ACL2::FN-READER-SUBMIT-OCTETS|))
          (ignore-values (|f:ACL2::FN-READER-OUTCOME| '|KEYWORD::REFUSED| acl2-state))
          (set! out (cons (global '|ACL2::FN-READER-OUTPUT|) out)))
        (when (null? (global '|ACL2::FN-READER-CLOSEP|))
          (loop (cdr cs)))))
    (apply append (reverse out))))

(define (main args)
  (let* ((verb (car args))
         (chunks (parse-chunks (read-file-u8vector (cadr args)))))
    (cond ((string=? verb "model") (write-octets (model chunks)))
          ((string=? verb "socket") (write-octets (socket chunks)))
          ((string=? verb "post") (write-octets (post chunks)))
          ((string=? verb "bench")
           ;; the archive is selected once, as the reader selects it once
           ;; before it accepts clients; each run is one connection's model
           (let ((n (string->number (caddr args)))
                 (arena (|f:ACL2::CREATE-FN-ARENA$X|)))
             (select-seed arena)
             (model-octets chunks arena)
             (let ((t0 (current-process-milliseconds)) (g0 (current-gc-milliseconds)))
               (do ((i 0 (+ i 1))) ((= i n)) (model-octets chunks arena))
               (let ((t1 (current-process-milliseconds)) (g1 (current-gc-milliseconds)))
                 (fprintf (current-error-port) "bench ~a runs ~a ms ~a us/run gc ~a ms~%"
                          n (- t1 t0) (/ (* 1000.0 (- t1 t0)) n) (- g1 g0))))))
          (else (error "usage: model|socket FILE | bench FILE N")))))

(main (command-line-arguments))
