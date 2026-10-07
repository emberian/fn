;;; Per-request cost columns (lane obs-request-cost; program section 2b, AT-1),
;;; against the DEPLOYED trace span and the deployed I/O leaves: the shared
;;; write leaf (fnn-write-progress, plain sockets and files), the TLS write
;;; leaf (fnn-tls-write-now-range) and fnn-transport-write-now, with only the
;;; kernel and OpenSSL calls stubbed.  The rows are printed as FN_TRACE lines;
;;; tests/test_native_request_cost.py asserts the numbers (and runs this file
;;; again over mutated copies of the sources, which must turn them red).
;;; FN_COST_IO_SOURCE / FN_COST_TLS_SOURCE name the sources (the mutation seam).
(load "tests/native_section_envelope_raw.lisp")
(in-package "ACL2")

(defun cost-source (variable default)
  (let ((value (sb-posix:getenv variable)))
    (if (and value (plusp (length value))) value default)))

(load-deployed-forms (cost-source "FN_COST_IO_SOURCE" "host/native/io.lisp")
 '((defstruct (fnn-io-counters (:constructor %make-fnn-io-counters)))
   (defvar *fnn-io-counters*) (defmacro fnn-io-count)
   (defvar *fnn-write-syscall*) (defvar *fnn-read-syscall*)
   (defun fnn-eintr-p) (defun fnn-would-block-p) (defun fnn-retry-eintr)
   (defun fnn-write-progress) (defun fnn-transport-write-now)))

;; OpenSSL, stubbed at the FFI edge only: a "record" takes at most 16 KiB.
(defvar *ssl-record* 16384)
(defun fnn-tls-channel-pointer (channel) channel)
(defun fnn-%err-clear-error () nil)
(defun fnn-tls-pointer (data offset) (declare (ignore data)) offset)
(defun fnn-%ssl-write (ssl pointer count) (declare (ignore ssl pointer)) (min count *ssl-record*))
(defun fnn-tls-retry-direction (ssl result) (declare (ignore ssl result)) (error "unreachable stub"))
(defun fnn-tls-operation-error (&rest args) (error "unreachable stub ~s" args))
(load-deployed-forms (cost-source "FN_COST_TLS_SOURCE" "host/native/tls.lisp")
 '((defun fnn-tls-write-now-range)))

;; The article: lines of 70 octets plus CRLF, every seventh starting with a dot
;; (dot-stuffed on the wire).  ARTICLE is its octet count as stored; REPLY adds
;; the "220" header line, one stuffing octet per dotted line and ".\r\n".
(defun make-article (lines)
  (let ((out (make-array 0 :element-type '(unsigned-byte 8) :adjustable t :fill-pointer 0))
        (stuffing 0))
    (dotimes (i lines)
      (dotimes (j 70) (vector-push-extend (if (and (zerop j) (zerop (mod i 7))) 46 97) out))
      (vector-push-extend 13 out) (vector-push-extend 10 out)
      (when (zerop (mod i 7)) (incf stuffing)))
    (values (coerce out '(simple-array (unsigned-byte 8) (*))) stuffing)))
(multiple-value-bind (article stuffing) (make-article 1500)
  (let* ((header-octets (+ (length "220 1 <article@fn.test>") 2))
         (reply-length (+ header-octets (length article) stuffing 3)))
    (format t "COST_FIXTURE article=~d header=~d stuffing=~d reply=~d~%"
            (length article) header-octets stuffing reply-length)
    (setf (symbol-value '*reply*) (make-array reply-length :element-type '(unsigned-byte 8)
                                                           :initial-element 97))))

(defvar *reply* nil)
(defun write-reply (fd channel)
  "fnn-mux-flush's write loop: one transport write at a time until all sent."
  (let ((at 0) (end (length *reply*)))
    (loop while (< at end)
          do (let ((progress (fnn-transport-write-now fd channel *reply* at end)))
               (when (integerp progress) (incf at progress))))))

(defvar *sink* nil)
(defun spin-for-seconds (seconds)
  (let ((until (+ (get-internal-real-time) (* seconds internal-time-units-per-second))) (x 0))
    (loop while (< (get-internal-real-time) until) do (setf x (logxor (1+ x) (ash x 1)) x (logand x #xffff)))
    x))

(let ((*fnn-write-syscall* (lambda (fd data offset count) (declare (ignore fd data offset))
                             (values (min count 4096) nil))))
  ;; OFF: no state, no counters, same values.
  (fnn-trace-reset)
  (assert (null *fnn-io-counters*))
  (write-reply 7 nil)
  (write-reply 7 :tls)
  (assert (null *fnn-io-counters*))

  (fnn-trace-start :capacity 64 :allocation :isolated-process :rss-every 0)
  ;; (i) 8 MiB, allocated and kept live across the span.
  (fnn-trace-span (:alloc-8mib :cid 9 :operation 1)
    (setf *sink* (make-array (* 8 1024 1024) :element-type '(unsigned-byte 8))))
  ;; (ii) the ARTICLE reply, on the plain and on the TLS write leaf.
  (fnn-trace-span (:article-plain :cid 9 :operation 2) (write-reply 7 nil))
  (fnn-trace-span (:article-tls :cid 9 :operation 3) (write-reply 7 :tls))
  ;; Thread scope: another thread's writes and CPU are not this span's.
  (fnn-trace-span (:other-thread :cid 9 :operation 4)
    (sb-thread:join-thread (sb-thread:make-thread (lambda () (write-reply 7 nil) (write-reply 7 :tls)
                                                    (spin-for-seconds 0.1)))))
  (fnn-trace-span (:busy :cid 9 :operation 5) (spin-for-seconds 0.1))
  ;; (iii) a forced collection inside a span.
  (fnn-trace-span (:forced-gc :cid 9 :operation 6) (sb-ext:gc :full t))
  ;; Nested spans share the thread's counters; each reports its own delta.
  (fnn-trace-span (:outer :cid 9 :operation 7)
    (write-reply 7 nil)
    (fnn-trace-span (:inner :cid 9 :operation 7) (write-reply 7 nil)))
  (fnn-trace-span (:quiet :cid 9 :operation 8) nil))
(fnn-trace-report *standard-output*)
(fnn-trace-reset)
(format t "NATIVE_REQUEST_COST_PASS~%")
