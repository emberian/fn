; Actual retained segment/framing bodies -> core span plan -> real HMAC.
; Trusted repository sources only are read/evaluated. No external Lisp reader.
; Diagnostic refs are UNISSUED; test-only source slices are not a provider.
(require :sb-posix)
(unless (find-package "ACL2") (make-package "ACL2" :use '("COMMON-LISP")))
(in-package "ACL2")
(declaim (declaration xargs))
(defmacro defconst (name value) `(defparameter ,name ,value))
(defun natp (x) (and (integerp x) (<= 0 x)))
(defun zp (x) (or (not (integerp x)) (<= x 0)))
(defun nfix (x) (if (natp x) x 0))
(defun len (x) (length x))
(defun true-listp (x) (or (null x) (and (consp x) (true-listp (cdr x)))))
(defun member-equal (x xs) (member x xs :test #'equal))
(defmacro mbe (&key logic exec) (declare (ignore logic)) exec)
(defmacro mv (&rest xs) `(values ,@xs))
(defmacro mv-let (vars value &body body) `(multiple-value-bind ,vars ,value ,@body))
(dolist (selection
 '(("books/cbor.lisp" *fn-cbor-max-uint* fn-cbor-octetp fn-cbor-ag-car fn-cbor-ag-cdr
     fn-cbor-u16-bytes fn-cbor-u32-bytes fn-cbor-encode-argument)
   ("books/bp-primary-cbor.lisp" *fn-bpc-max-uint* *fn-bpc-max-text* fn-bpc-u32-octets fn-bpc-u64-bytes fn-bpc-argument)
   ("books/bpsec-model.lisp" fn-bps-field fn-bps-uintp fn-bps-limits-make fn-bps-limitsp
     fn-bps-window-make fn-bps-span-make)
   ("books/bpsec-operation.lisp") ("books/bpsec-primitive-plan.lisp")
   ("books/bpsec-input-plan.lisp") ("books/bpsec-head.lisp") ("books/bpsec-asb.lisp")
   ("build/bpsec-source-observation/tcpcl-segment-source-cursor.lisp")
   ("build/bpsec-source-observation/bp-wire-primary-cursor.lisp")
   ("build/bpsec-source-observation/bp-wire-canonical-cursor.lisp")
   ("build/bpsec-source-observation/bp-segmented-wire-job.lisp")))
 (with-open-file (stream (car selection))
  (loop for form = (read stream nil :end) until (eq form :end)
   when (and (consp form) (member (car form) '(defun defconst))
             (or (null (cdr selection)) (member (second form) (cdr selection))))
   do (eval form))))
(handler-bind ((style-warning #'muffle-warning))
 (load "host/native/crypto.lisp") (load "host/native/tls.lisp")
 (load "host/native/bpsec-crypto.lisp"))
(defvar *source-observation-checks* 0)
(defun source-check (x) (incf *source-observation-checks*) (unless x (error "source check ~d failed" *source-observation-checks*)))
(defun source-hex (s)
 (let ((v (make-array (/ (length s) 2) :element-type '(unsigned-byte 8))))
  (dotimes (i (length v) v)
   (setf (aref v i) (parse-integer s :radix 16 :start (* i 2) :end (+ 2 (* i 2)))))))
(defun source-hex-string (v)
 (format nil "~(~{~2,'0x~}~)" (coerce v 'list)))
(defparameter *a1-wire* (source-hex
 (concatenate 'string
 "9f88070000820282010282028202018202820201820018281a000f4240850b0200"
 "005856810101018202820201828201078203008181820158403bdc69b3a34a2b5d3a"
 "8554368bd1e808f606219d2a10a846eae3886ae4ecc83c4ee550fdfb1cc636b904e2"
 "f1a73e303dcd4b6ccece003e95e8164dcc89a156e185010100005823526561647920"
 "746f2067656e657261746520612033322d62797465207061796c6f6164ff")))
(defparameter *a1-input* (source-hex "005823526561647920746f2067656e657261746520612033322d62797465207061796c6f6164"))
(defparameter *a1-key* (source-hex "1a2b1a2b1a2b1a2b1a2b1a2b1a2b1a2b"))
(defparameter *a1-mac* (source-hex
 "3bdc69b3a34a2b5d3a8554368bd1e808f606219d2a10a846eae3886ae4ecc83c4ee550fdfb1cc636b904e2f1a73e303dcd4b6ccece003e95e8164dcc89a156e1"))
(defparameter *unissued-source* '(:bps-ref 9 1))
(defun source-segments (wire cuts)
 (let ((at 0) (segments nil))
  (dolist (end (append cuts (list (length wire))) segments)
   (push (coerce (subseq wire at end) 'list) segments) (setf at end))))
(defun source-parse (wire cuts quantum &optional (count (length wire)))
 (let* ((root (source-segments wire cuts))
        (job (fn-bpsw-begin *unissued-source* root count)) (events nil))
  (loop repeat (+ 100 (* 8 (length wire))) do
   (multiple-value-bind (word next used event) (fn-bpsw-turn job quantum 0)
    (source-check (and (< 0 used) (<= used quantum)))
    (source-check (eq root (fn-tsc-at 8 (fn-bps-field 5 next))))
    (setf job next)
    (when (eq word :block-source) (push event events))
    (when (member word '(:source-complete :refused))
     (return-from source-parse (values word (reverse events) job)))))
  (error "retained parser failed to terminate")))
(defun source-asb (security wire quantum)
 ; Actual STEP, bounded test windows over the parser-selected original span.
 ; The test's9 backing tag is unissued and supplies no registry authority.
 (let* ((data (ninth security)) (start (third data)) (size (fourth data))
        (end (+ start size))
        (cursor (fn-bps-asb-start (fifth security) 9 start size
                  (fn-bps-limits-make 4096 128 16 16 2048 2048))))
  (loop repeat (+ 100 (* 10 size)) do
   (let* ((at (fn-bps-get :offset cursor))
          (window (coerce (subseq wire at (min end (+ at 64))) 'list))
          (step (fn-bps-asb-step cursor (fn-bps-window-make 9 at window) quantum)))
    (source-check (<= (fourth step) quantum))
    (setf cursor (third step))
    (when (member (first step) '(:parsed :refused :unsupported))
     (source-check (eq (first step) :parsed))
     (source-check (= (fn-bps-get :offset cursor) end))
     (return-from source-asb (fn-bps-asb-span-result cursor)))))
  (error "ASB diagnostic failed to terminate")))
(defun source-asb-pair (id pairs)
 (find id pairs :key #'first :test #'equal))
(defun source-asb-bytes (span wire)
 (source-check (and (eq (first span) :bytes-span) (= (second span) 9)))
 (subseq wire (third span) (+ (third span) (fourth span))))
(defun source-diagnostic-command (command wire)
 ; Test-only alpha: original published wire and exact core-selected slice.
 ; This is deliberately not an installed immutable backing/window supplier.
 (case (first command)
  (:bps-literal (coerce (second command) '(simple-array (unsigned-byte 8) (*))))
  (:bps-span
   (source-check (equal (second command) *unissued-source*))
   (subseq wire (third command) (+ (third command) (fourth command))))
  (otherwise (error "unexpected command"))))
(defparameter *a1-descriptor*
 (fn-bps-op-make :verify-bib '(:bps-ref 1 1) '(:bps-ref 2 1) '(:bps-ref 3 1)
  '(:bps-ref 4 1) 2 1 1 '(:bps-bib-params 7 0 nil) '(:bps-ref 5 1)
  '(:bytes-span 9 0 64)))
; RFC9173 A.1 has a16-byte key, inconsistent with normative section3.5.
; Reproduce its vector diagnostically; the actual core MUST refuse that key.
(source-check (= (length *a1-key*) 16))
(source-check (equal (fn-bps-primitive-select *a1-descriptor* (length *a1-key*))
                     '(:refused :key-width)))
(dolist (cuts '(nil (0 1 28 31 64 128 153 160) (1 2 3 4 5 6 7 8 9)))
 (dolist (q '(1 7 64))
  (multiple-value-bind (word events job) (source-parse *a1-wire* cuts q)
   (format t "PARSE word=~s events=~s reason=~s~%" word events (fn-bps-field 9 job))
   (source-check (eq word :source-complete)) (source-check (= (length events) 3))
   (destructuring-bind (primary security target) events
    (source-check (and (fn-bps-input-primaryp primary) (fn-bps-input-blockp security)
                       (fn-bps-input-blockp target)))
    (source-check (and (= (fifth security) 11) (= (sixth security) 2)
                       (= (fifth target) 1) (= (sixth target) 1)))
    (let* ((asb (source-asb security *a1-wire* q))
           (planned (fn-bps-input-plan *a1-descriptor* primary target security))
           (plan (second planned)) (commands (third plan))
           (actual-input (apply #'concatenate '(simple-array (unsigned-byte 8) (*))
                           (mapcar (lambda (x) (source-diagnostic-command x *a1-wire*)) commands))))
     (source-check (equal (third asb) '(1)))
     (source-check (= (fourth asb) 1))
     (source-check (equal (second (source-asb-pair 1 (seventh asb))) '(:uint . 7)))
     (source-check (equal (second (source-asb-pair 3 (seventh asb))) '(:uint . 0)))
     (source-check (equalp (source-asb-bytes (second (first (first (eighth asb)))) *a1-wire*) *a1-mac*))
     (source-check (eq (first planned) :planned))
     (format t "INPUT ~a KEY ~a~%" (source-hex-string actual-input) (source-hex-string *a1-key*))
     (source-check (equalp actual-input *a1-input*))
     (let ((foreign (copy-list target)))
      (setf (second foreign) '(:bps-ref 9 2))
      (source-check (equal (fn-bps-input-plan *a1-descriptor* primary foreign security)
                           '(:refused :foreign-target-metadata))))
     (let ((handle (fnn-bpsec-hmac-start *a1-descriptor* :sha512 *a1-key* 64)))
      (unwind-protect
       (progn
        (dolist (command commands)
         (let ((bytes (source-diagnostic-command command *a1-wire*)))
          (loop for at from 0 below (length bytes) by q do
           (source-check (null (fnn-bpsec-hmac-update handle bytes at (min q (- (length bytes) at))))))))
        (let ((raw (fnn-bpsec-hmac-final handle)))
         (source-check (eq (first raw) *a1-descriptor*))
         (source-check (eq (second raw) :hmac-bytes)) (source-check (= (fourth raw) 64))
         (format t "MAC ~a~%" (source-hex-string (subseq (third raw) 0 64)))
         (source-check (equalp (subseq (third raw) 0 64) *a1-mac*))
         (format t "OBSERVE q=~d cuts=~s events=~s input=~a mac=~a normative-key=:refused~%"
                 q cuts events (source-hex-string actual-input) (source-hex-string (subseq (third raw) 0 64)))
         (fnn-bpsec-cleanse (third raw))))
       (fnn-bpsec-cancel handle))))))))
; RFC9173 A.2: actual payload data span is the ciphertext, never its
; CBOR byte-string wrapper. The first pass authenticates and publishes NIL.
(defparameter *a2-wire* (source-hex
 (concatenate 'string
 "9f88070000820282010282028202018202820201820018281a000f4240850c0201"
 "0058508101020182028202018482014c5477656c7665313231323132820201820358"
 "1869c411276fecddc4780df42c8a2af89296fabf34d7fae7008204008181820150ef"
 "a4b5ac0108e3816c5606479801bc04850101000058233a09c1e63fe23a7f66a59c73"
 "03837241e070b02619fc59c5214a22f08cd70795e73e9aff")))
(defparameter *a2-key* (source-hex "71776572747975696f70617364666768"))
(defparameter *a2-iv* (source-hex "5477656c7665313231323132"))
(defparameter *a2-tag* (source-hex "efa4b5ac0108e3816c5606479801bc04"))
(defparameter *a2-descriptor*
 (fn-bps-op-make :decrypt-bcb '(:bps-ref 11 1) '(:bps-ref 2 1) '(:bps-ref 3 1)
  '(:bps-ref 4 1) 2 1 2
  '(:bps-bcb-params 1 0 (:bytes-span 9 0 12) nil :separate-tag)
  '(:bps-ref 15 1) '(:bytes-span 9 0 16)))
(defun source-primitive-feed (function handle bytes q)
 (loop for at from 0 below (length bytes) by q do
  (source-check (null (funcall function handle bytes at (min q (- (length bytes) at)))))))
(dolist (cuts '(nil (0 1 28 31 64 100 128) (1 2 3 4 5 6 7 8 9)))
 (dolist (q '(1 7 64))
  (multiple-value-bind (word events job) (source-parse *a2-wire* cuts q)
   (declare (ignore job))
   (source-check (eq word :source-complete)) (source-check (= (length events) 3))
   (destructuring-bind (primary security target) events
    (let* ((asb (source-asb security *a2-wire* q))
           (planned (fn-bps-input-plan *a2-descriptor* primary target security))
           (plan (second planned))
           (aad (apply #'concatenate '(simple-array (unsigned-byte 8) (*))
                  (mapcar (lambda (x) (source-diagnostic-command x *a2-wire*)) (third plan))))
           (ciphertext (source-diagnostic-command (fourth plan) *a2-wire*))
           (primitive (fn-bps-primitive-select *a2-descriptor* (length *a2-key*))))
     (source-check (eq (first planned) :planned))
     (source-check (equal (third asb) '(1)))
     (source-check (= (fourth asb) 2))
     (source-check (equal (second (source-asb-pair 2 (seventh asb))) '(:uint . 1)))
     (source-check (equal (second (source-asb-pair 4 (seventh asb))) '(:uint . 0)))
     (source-check (equalp (source-asb-bytes (second (source-asb-pair 1 (seventh asb))) *a2-wire*) *a2-iv*))
     (source-check (equalp (source-asb-bytes (second (first (first (eighth asb)))) *a2-wire*) *a2-tag*))
     (source-check (equalp aad #(0)))
     (source-check (equalp ciphertext (source-hex
       "3a09c1e63fe23a7f66a59c7303837241e070b02619fc59c5214a22f08cd70795e73e9a")))
     (source-check (eq (third primitive) :aes128-gcm))
     (dolist (corruption '(:none :aad :tag :ciphertext :length))
      (let ((ad (copy-seq aad)) (ct (copy-seq ciphertext)) (tag (copy-seq *a2-tag*)))
       (case corruption
        (:aad (setf (aref ad 0) 1))
        (:tag (setf (aref tag 15) (logxor 1 (aref tag 15))))
        (:ciphertext (setf (aref ct 0) (logxor 1 (aref ct 0))))
        (:length (setf ct (subseq ct 0 (1- (length ct))))))
       (let ((handle (fnn-bpsec-gcm-start *a2-descriptor* (third primitive) *a2-key* *a2-iv* 64)))
        (unwind-protect
         (progn
          (source-primitive-feed #'fnn-bpsec-gcm-aad handle ad q)
          (source-primitive-feed #'fnn-bpsec-gcm-update handle ct q)
          (let* ((raw (fnn-bpsec-gcm-final handle tag))
                 (answer (fn-bps-primitive-answer *a2-descriptor*
                   (list :bps-primitive-observation (first raw) (second raw) (third raw)) nil)))
           (source-check (eq (first raw) *a2-descriptor*))
           (source-check (null (third raw)))
           (if (eq corruption :none)
            (progn
             (source-check (eq (second raw) :authenticated))
             (source-check (eq (second answer) :authenticated))
             (source-check (not (fn-bps-completionp (fourth answer)))))
            (progn
             (source-check (eq (second raw) :bad-tag))
             (source-check (eq (second answer) :failed))))
           (format t "GCM q=~d cuts=~s mutation=~s aad=~a ciphertext=~a tag=~a raw=~s core=~s~%"
             q cuts corruption (source-hex-string ad) (source-hex-string ct)
             (source-hex-string tag) raw answer)))
         (fnn-bpsec-cancel handle))))))))))
; Actual malformed/truncated/maintained-count refusals, with original root held.
(dolist (q '(1 7 64))
 (dolist (row (list (list (subseq *a1-wire* 0 (1- (length *a1-wire*))) nil)
                   (list (concatenate '(simple-array (unsigned-byte 8) (*)) *a1-wire* #(0)) nil)
                   (list *a1-wire* (1- (length *a1-wire*)))
                   (list *a1-wire* (1+ (length *a1-wire*)))))
  (multiple-value-bind (word events job)
      (source-parse (first row) '(1 28) q (or (second row) (length (first row))))
   (declare (ignore events))
   (source-check (eq word :refused))
   (format t "REFUSE q=~d length=~d count=~d reason=~s~%" q (length (first row))
           (or (second row) (length (first row))) (fn-bps-field 9 job)))))
(format t "PASS actual retained framing -> bounded ASB -> span commands -> real RFC9173 A1 HMAC/A2 GCM, checks=~d; unissued refs, test-only slice, no admission~%" *source-observation-checks*)
