;;; The stored-payload encoder (host/native/deflate.lisp fnn-ldf-) on the
;;; Huffman trees with fewer than two used symbols (inspection sweep
;;; 2026-10-03 S005).  A block whose matches all fall in one distance code
;;; C >= 2 used to get lengths 1 for 0, 1 and C: an oversubscribed code
;;; (RFC 1951 3.2.2) that zlib refuses ("invalid distances set") and that
;;; ACL2's decoder (fn-lzr-append-decide) refuses, so the append faulted on
;;; that payload every time.
;;;
;;; Checked here: every code-length vector the encoder builds for 0 or 1
;;; used symbols, over the three alphabets (19, 30, 286), codes exactly two
;;; symbols at length 1 and the used one among them; and the streams for
;;; payloads whose matches use a single distance code (0, 1, 2, 10, 29) or
;;; none inflate octet for octet under an independent decoder, Python's
;;; zlib (raw DEFLATE, wbits -15).  tests/acl2/payload-lz-append-tests.lisp
;;; pins the same case under ACL2's decoder.
(require :sb-posix)
(defpackage "ACL2" (:use "CL"))
(in-package "ACL2")
(defun fnn-fault (control &rest args) (error (apply #'format nil control args)))
(handler-bind ((warning #'muffle-warning))
  (load "host/native/deflate.lisp"))

(defvar *failures* 0)
(defun check (ok fmt &rest args)
  (unless ok
    (incf *failures*)
    (format t "FAIL: ~?~%" fmt args)))

(defun octets (list) (coerce list '(simple-array (unsigned-byte 8) (*))))

;;; 1. The lengths for fewer than two used symbols.
(defun kraft-ok (lens limit)
  (<= (loop for l across lens when (plusp l) sum (ash 1 (- limit l))) (ash 1 limit)))

(dolist (n '(19 30 286))
  (let ((limit (if (= n 19) 7 15)))
    (let ((lens (fnn-ldf-huffman-lengths (fnn-ldf-make-fix n) limit)))
      (check (and (kraft-ok lens limit) (= 2 (count 1 lens)) (= 2 (count-if #'plusp lens)))
             "alphabet ~d, no symbol used: ~s" n (coerce lens 'list)))
    (dotimes (s n)
      (let ((freq (fnn-ldf-make-fix n)))
        (setf (aref freq s) 5)
        (let ((lens (fnn-ldf-huffman-lengths freq limit)))
          (check (and (kraft-ok lens limit) (= 2 (count 1 lens)) (= 2 (count-if #'plusp lens))
                      (= 1 (aref lens s)))
                 "alphabet ~d, only symbol ~d used: ~s" n s
                 (remove 0 (coerce lens 'list))))))))

;;; 2. Streams under zlib.  The payloads: 200 octets over a 64-symbol
;;; alphabet (a dynamic block is cheaper than the fixed one) with one
;;; 24-octet phrase repeated at distance D, so the block's only distance
;;; code is D's; distance 1 and 2 by a run; and no match at all.
(defun inflates-p (src stream)
  "T when Python's zlib inflates STREAM (raw DEFLATE) to SRC exactly."
  (let* ((dir (format nil "/tmp/fn-deflater-raw-~d/" (sb-posix:getpid)))
         (zp (concatenate 'string dir "z")) (sp (concatenate 'string dir "s")))
    (ensure-directories-exist dir)
    (unwind-protect
         (progn
           (with-open-file (o zp :direction :output :element-type '(unsigned-byte 8) :if-exists :supersede)
             (write-sequence stream o))
           (with-open-file (o sp :direction :output :element-type '(unsigned-byte 8) :if-exists :supersede)
             (write-sequence src o))
           (zerop (sb-ext:process-exit-code
                   (sb-ext:run-program
                    "/usr/bin/env"
                    (list "python3" "-c"
                          "import sys,zlib
z=open(sys.argv[1],'rb').read(); s=open(sys.argv[2],'rb').read()
d=zlib.decompressobj(-15); out=d.decompress(z)
sys.exit(0 if out==s and d.eof and not d.unused_data else 1)"
                          zp sp)
                    :output nil :error nil))))
      (ignore-errors (delete-file zp))
      (ignore-errors (delete-file sp))
      (ignore-errors (sb-posix:rmdir dir)))))

(defun phrase-payload (seed d)
  (let* ((rs (sb-ext:seed-random-state seed))
         (body (loop repeat 200 collect (+ 48 (random 64 rs))))
         (at 60))
    (octets (append (subseq body 0 at) (subseq body (- at d) (+ (- at d) 24)) (subseq body at)))))

(defun stream-of (src) (fnn-ldf-deflate-payload (octets nil) src))

(defvar *cases* 0)
(defun check-stream (name src)
  (incf *cases*)
  (check (inflates-p src (stream-of src)) "~a: the stream does not inflate to the payload" name))

;; distance 44 is code 10; 25..32 code 9; 49..64 code 11
(dolist (d '(25 44 50))
  (dotimes (seed 8)
    (check-stream (format nil "one phrase at distance ~d, seed ~d" d seed) (phrase-payload seed d))))
(check-stream "a run (distance 1, code 0)"
              (octets (append (loop for i below 40 collect (+ 48 (mod (* i 7) 64))) (make-list 30 :initial-element 65)
                              (loop for i below 40 collect (+ 48 (mod (* i 11) 64))))))
(check-stream "a two-octet run (distance 2, code 1)"
              (octets (append (loop for i below 40 collect (+ 48 (mod (* i 7) 64)))
                              (loop repeat 15 append (list 65 66))
                              (loop for i below 40 collect (+ 48 (mod (* i 11) 64))))))
(check-stream "no match" (octets (loop for i below 64 collect (+ 48 i))))
(check-stream "one octet" (octets '(65)))
(check-stream "empty" (octets nil))
;; distance 24577..32768 is code 29, the last
(check-stream "one phrase at distance 30000 (code 29)"
              (let* ((rs (sb-ext:seed-random-state 3))
                     (body (loop repeat 30200 collect (+ 128 (random 128 rs)))))
                (octets (append body (subseq body 200 230)))))

(if (zerop *failures*)
    (format t "native_deflater_raw: ~d streams inflate exactly, the short trees are complete: PASS~%" *cases*)
    (progn (format t "native_deflater_raw: ~d failures: FAIL~%" *failures*)
           (sb-ext:exit :code 1)))
