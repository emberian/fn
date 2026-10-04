;;; The inbound COMPRESS DEFLATE layer (host/native/deflate.lisp
;;; fnn-zin-inflate) over ACL2's own decoder (books/deflate-inflate.lisp
;;; fn-zin-feed), loaded by tests/test_native_zin_owed_raw.sh in raw mode
;;; after the book: no answer here is made up.
;;;
;;; fn-zin-feed can answer :full having read every input octet while it still
;;; owes plaintext: the rest of a match it is copying, or codes already in its
;;; bit buffer.  The stream below is one fixed-Huffman block (RFC 1951 3.2.6):
;;; the literals "DATE" CR LF, then sixteen matches of length 258 at distance
;;; 6, padded to an octet -- 35 octets that Python's zlib inflates to "DATE"
;;; CR LF 689 times.  Its last octet is read to decode the last match, whose
;;; copy crosses the 4096th output octet, so the first call stops :full with
;;; nothing left to read and 38 plaintext octets still in the decoder.  The
;;; I/O loop (host/native/mux.lisp fnn-mux-work) inflates again only while
;;; the inflater says something is pending; when it said nothing (the pending
;;; octets were NIL whenever the input was used up) the last six commands
;;; waited for octets the client had no reason to send.
(in-package "ACL2")

;;; ---- derived stubs: BEGIN (python3 tools/harness_check.py --write-stubs; do not edit) ----
(define-condition harness-stub-reached (serious-condition)
  ((name :initarg :name :reader harness-stub-reached-name)
   (source :initarg :source :reader harness-stub-reached-source))
  (:report (lambda (c s)
             (format s "harness: host function ~(~a~) (~a) was reached; this harness neither stubs nor extracts it"
                     (harness-stub-reached-name c) (harness-stub-reached-source c)))))
(defun harness-stub-reached (name source)
  (format *error-output* "harness: host function ~(~a~) (~a) was reached; this harness neither stubs nor extracts it~%"
          name source)
  (finish-output *error-output*)
  (error 'harness-stub-reached :name name :source source))
(defun fnn-make-octets (n)
  (declare (ignorable n))
  (harness-stub-reached 'fnn-make-octets "host/native/io.lisp"))
(defun fnn-mux-service (loop)
  (declare (ignorable loop))
  (harness-stub-reached 'fnn-mux-service "host/native/mux.lisp"))
(defun fnn-mux-step (loop conn)
  (declare (ignorable loop conn))
  (harness-stub-reached 'fnn-mux-step "host/native/mux.lisp"))
(defun fnn-mux-z-in (loop conn raw)
  (declare (ignorable loop conn raw))
  (harness-stub-reached 'fnn-mux-z-in "host/native/mux.lisp"))
(defun fnn-zin-fill-input (zin octets)
  (declare (ignorable zin octets))
  (harness-stub-reached 'fnn-zin-fill-input "host/native/deflate.lisp"))
(defun fnn-zin-private-octets (n)
  (declare (ignorable n))
  (harness-stub-reached 'fnn-zin-private-octets "host/native/deflate.lisp"))
;;; ---- derived stubs: END ----

(defun fnn-fault (control &rest args) (error (apply #'format nil control args)))
(defun fnn-call (name &rest args) (multiple-value-list (apply name args)))
(defun fnn-core (name &rest args) (first (apply #'fnn-call name args)))

(handler-bind ((warning #'muffle-warning))
  (load *fnzo-deflate-path*))

(defvar *fnzo-failures* 0)
(defun fnzo-check (ok fmt &rest args)
  (unless ok
    (incf *fnzo-failures*)
    (format t "~%native_zin_owed_raw: FAIL ~?~%" fmt args)))

(defparameter *fnzo-stream*
  (coerce '(#x72 #x71 #x0c #x71 #xe5 #xe5 #x1a #x25 #x47 #xc9 #x51 #x72 #x94 #x1c
            #x25 #x47 #xc9 #x51 #x72 #x94 #x1c #x25 #x47 #xc9 #x51 #x72 #x94 #x1c
            #x25 #x47 #xc9 #x51 #x72 #x94 #x04)
          '(simple-array (unsigned-byte 8) (*))))

(defparameter *fnzo-plain*
  (let ((one (map '(simple-array (unsigned-byte 8) (*)) #'char-code
                  (coerce (list #\D #\A #\T #\E #\Return #\Newline) 'string))))
    (apply #'concatenate '(simple-array (unsigned-byte 8) (*))
           (loop repeat 689 collect one))))

(defun fnzo-drain (lim)
  "What the I/O loop hands its steps: one read's inflation, then a further one
for as long as the inflater holds something pending (fnn-mux-work)."
  (let ((zin (fnn-zin-new)) (parts nil) (statuses nil) (calls 0))
    (multiple-value-bind (plain status) (fnn-zin-inflate zin *fnzo-stream* lim)
      (push plain parts) (push status statuses))
    (loop while (and (fnn-zin-pending zin) (< (incf calls) 100))
          do (multiple-value-bind (plain status)
                 (fnn-zin-inflate zin (make-array 0 :element-type '(unsigned-byte 8)) lim)
               (push plain parts) (push status statuses)))
    (values (apply #'concatenate '(simple-array (unsigned-byte 8) (*)) (reverse parts))
            (reverse statuses))))

(dolist (lim '(4096 512))
  (multiple-value-bind (plain statuses) (fnzo-drain lim)
    (fnzo-check (equalp plain *fnzo-plain*)
                "lim ~d: ~d of ~d plaintext octets reached the steps (statuses ~s)"
                lim (length plain) (length *fnzo-plain*) statuses)
    (fnzo-check (eq (car (last statuses)) :more)
                "lim ~d: the drain did not end asking for more input (~s)" lim statuses)))

(if (zerop *fnzo-failures*)
    (format t "~%native_zin_owed_raw: PASS~%")
  (format t "~%native_zin_owed_raw: ~d failure~:p~%" *fnzo-failures*))
