;;; tools/runtime_floor/serial.lisp -- one value printer for both images (lane
;;; runtime-floor).  Portable CL: loaded by the SBCL tracer and by the ECL
;;; replay, so a reply compares as the same octets on both sides.
;;; Encoding (a readable s-expression):
;;;   integer, character (as (:c CODE)), string (as (:s "..." ) with escapes
;;;   kept by prin1), symbol (as (:y "PKG" "NAME")), cons (as (:l x... . tail)),
;;;   (unsigned-byte 8) vector (as (:u8 "HEX")), simple-vector (as (:v x...)),
;;;   a live stobj or the state (as (:stobj "NAME")), anything else (:opaque TYPE).
(declaim (optimize (safety 3)))
(defpackage "RF-SERIAL" (:use "COMMON-LISP") (:export "ENC" "*STOBJ-NAMER*" "ENC-STRING" "DEC"))
(in-package "RF-SERIAL")

(defvar *stobj-namer* (lambda (x) (declare (ignore x)) nil)
  "X -> the stobj's name string, or NIL when X is not a live stobj.")

(defun hex (v)
  (let ((s (make-string (* 2 (length v)))))
    (loop for b across v for i from 0 by 2
          do (setf (char s i) (char "0123456789abcdef" (ash b -4))
                   (char s (1+ i)) (char "0123456789abcdef" (logand b 15))))
    s))

(defun unhex (s)
  (let ((v (make-array (floor (length s) 2) :element-type '(unsigned-byte 8))))
    (dotimes (i (length v) v)
      (setf (aref v i) (parse-integer s :start (* 2 i) :end (+ 2 (* 2 i)) :radix 16)))))

(defun enc (x)
  (let ((name (funcall *stobj-namer* x)))
    (cond
      (name (list :stobj name))
      ((integerp x) x)
      ((rationalp x) (list :q (numerator x) (denominator x)))
      ((complexp x) (list :z (enc (realpart x)) (enc (imagpart x))))
      ((characterp x) (list :c (char-code x)))
      ((stringp x) (list :s (map 'list #'char-code x)))
      ((null x) nil)
      ((symbolp x) (list :y (if (symbol-package x) (package-name (symbol-package x)) "")
                         (symbol-name x)))
      ((consp x)
       (let ((items nil) (tail x))
         (loop while (and (consp tail) (not (funcall *stobj-namer* tail)))
               do (push (enc (car tail)) items) (setq tail (cdr tail)))
         (list* :l (enc tail) (nreverse items))))
      ((and (vectorp x) (subtypep (array-element-type x) '(unsigned-byte 8))
            (equal (upgraded-array-element-type (array-element-type x))
                   (upgraded-array-element-type '(unsigned-byte 8))))
       (list :u8 (hex x)))
      ((vectorp x) (cons :v (map 'list #'enc x)))
      (t (list :opaque (princ-to-string (type-of x)))))))

(defun enc-string (x)
  (let ((*print-pretty* nil) (*print-readably* nil) (*package* (find-package "RF-SERIAL"))
        (*print-length* nil) (*print-level* nil) (*print-case* :upcase))
    (prin1-to-string (enc x))))

(defvar *stobj-of-name* (lambda (name) (error "no stobj ~a" name)))
(defvar *state-object* nil)

(defun dec (e)
  (cond
    ((integerp e) e)
    ((null e) nil)
    ((consp e)
     (ecase (car e)
       (:stobj (funcall *stobj-of-name* (cadr e)))
       (:q (/ (cadr e) (caddr e)))
       (:z (complex (dec (cadr e)) (dec (caddr e))))
       (:c (code-char (cadr e)))
       (:s (map 'string #'code-char (cadr e)))
       (:y (if (string= (cadr e) "") (make-symbol (caddr e))
               (intern (caddr e) (or (find-package (cadr e)) (error "no package ~a" (cadr e))))))
       (:l (let ((tail (dec (cadr e))))
             (dolist (item (reverse (cddr e)) tail) (setq tail (cons (dec item) tail)))))
       (:u8 (unhex (cadr e)))
       (:v (map 'vector #'dec (cdr e)))
       (:opaque (error "opaque value ~a" (cadr e)))))
    (t (error "bad encoding ~s" e))))
