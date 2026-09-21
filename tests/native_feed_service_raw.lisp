;;; Raw sequencing test for host/native/feed-service.lisp.
;;;
;;; This is deliberately an external harness: the deployed source still runs
;;; only inside the saved ACL2 image.  It supplies the narrow owner boundary
;;; and verifies that received chunks are handed to the ACL2 reply wrapper
;;; repeatedly with NIL drains, that a split greeting/MODE response follows
;;; only ACL2-projected phase actions, and that no feed tick runs before the
;;; wrapper has returned :READY.  It does not implement NNTP framing or parse
;;; reply codes.

(require :sb-bsd-sockets)

(defpackage "ACL2" (:use "CL"))
(in-package "ACL2")

(define-condition fnn-store-error (error) ())
(define-condition fnn-store-indeterminate (fnn-store-error) ())
(define-condition fnn-store-fault (fnn-store-error) ())
(define-condition fnn-os-error (error) ())

(defconstant +fnn-max-read+ 512)

(defparameter *test-words*
  '(:need-input :mode :need-input :ready :send :need-input))
(defparameter *test-reply-inputs* nil)
(defparameter *test-flushes* 0)
(defparameter *test-sends* nil)
(defparameter *test-ticks* 0)

(defun fnn-fault (control &rest args)
  (error (apply #'format nil control args)))

(defun fnn-core (&rest args)
  (declare (ignore args))
  (error "unexpected raw core call"))
(defun fnn-octet-list-p (x)
  (and (listp x) (every (lambda (b) (and (integerp b) (<= 0 b 255))) x)))
(defun fnn-octets (x) x)
(defun fnn-octet-list (x) x)
(defun fnn-make-octets (n) (make-array n :element-type '(unsigned-byte 8)))
(defun fnn-owner-serialized (service cid thunk)
  (declare (ignore service cid))
  (funcall thunk))
(defun fnn-owner-action (name &rest args)
  (unless (eq name 'fn-owner-feed-reply-chunk)
    (error "unexpected owner action: ~s" name))
  (push (second args) *test-reply-inputs*)
  (or (pop *test-words*) (error "too many reply actions")))
(defun fnn-owner-feed-flush (service)
  (declare (ignore service))
  (incf *test-flushes*))
(defun fnn-owner-octets-global (name)
  (unless (eq name 'fn-owner-feed-command)
    (error "unexpected global: ~s" name))
  #(9 10))
(defun fnn-send-all (fd octets seconds)
  (declare (ignore seconds))
  (push (list fd (coerce octets 'list)) *test-sends*))
(defun fnn-socket-shutdown (socket)
  (declare (ignore socket)) nil)
(defun fnn-socket-shut (socket)
  (declare (ignore socket)) nil)

;;; Only read here; worker/lifecycle functions are not entered until the final
;;; no-offer-before-ready check below.
(load "host/native/feed-service.lisp")

(let* ((runtime (%make-fnn-feed-runtime :service :test
                                         :lock (sb-thread:make-mutex)
                                         :limit 512))
       (link (%make-fnn-feed-link :peer "peer" :peer-octets #(112 101 101 114)
                                  :socket :fake :fd 7)))
  ;; The command state is supplied only by the ACL2 wrapper: split 200, then
  ;; MODE, then a coalesced 203 and ordinary reply.  NIL is the adapter's
  ;; retained-input drain, not a raw-Lisp reconstruction of either line.
  (fnn-feed-consume runtime link '(50 48 48 32 111 107 13) nil 1)
  (fnn-feed-consume runtime link '(10) nil 1)
  (fnn-feed-consume runtime link '(50 48 51 32 111 107 13 10 50 51 56 13 10)
                    nil 1)
  (unless (equal (nreverse *test-reply-inputs*)
                 '((50 48 48 32 111 107 13)
                   (10) nil
                   (50 48 51 32 111 107 13 10 50 51 56 13 10)
                   nil nil))
    (error "reply wrapper did not receive split/coalesced chunks with NIL drains: ~s"
           *test-reply-inputs*))
  (unless (= *test-flushes* 1)
    (error "expected one durable flush for the one post-ready line, got ~s"
           *test-flushes*))
  (unless (fnn-feed-link-ready link)
    (error "ACL2 :READY did not make the raw link ready"))
  (unless (equal (nreverse *test-sends*) '((7 (9 10)) (7 (9 10))))
    (error "expected only ACL2-projected MODE/reply commands: ~s" *test-sends*))
  ;; The actual pump branches on the raw link's ready bit, which is changed
  ;; only by :READY above.  A fake tick makes a premature call observable.
  (setf (symbol-function 'fnn-feed-tick)
        (lambda (service current-link now)
          (declare (ignore service current-link now))
          (incf *test-ticks*)
          (values :offer #(7))))
  (setf (symbol-function 'fnn-recv)
        (lambda (&rest ignored)
          (declare (ignore ignored)) :timeout))
  (let ((unready (%make-fnn-feed-link :peer "unready" :peer-octets #(117)
                                       :socket :fake :fd 8 :ready nil))
        (ready (%make-fnn-feed-link :peer "ready" :peer-octets #(114)
                                     :socket :fake :fd 9 :ready t)))
    (fnn-feed-pump-link runtime unready 2)
    (unless (zerop *test-ticks*)
      (error "feed tick ran before ACL2 :READY"))
    (fnn-feed-pump-link runtime ready 2)
    (unless (= *test-ticks* 1)
      (error "ready feed did not reach its one tick")))
  ;; A handshake refusal is peer-local and has no FNFD port transition.  It
  ;; must therefore neither be elevated to a host fault nor reappend an older
  ;; unrelated command batch while this link is being dropped.
  (let ((*test-words* '(:connection-refused))
        (before *test-flushes*)
        (old-plan (symbol-function 'fnn-feed-dial-plan))
        (old-lost (symbol-function 'fnn-feed-lost)))
    (unwind-protect
         (progn
           (setf (symbol-function 'fnn-feed-dial-plan)
                 (lambda (&rest ignored)
                   (declare (ignore ignored)) (values nil nil 0 0))
                 (symbol-function 'fnn-feed-lost)
                 (lambda (&rest ignored) (declare (ignore ignored)) :ok))
           (fnn-feed-consume runtime link '(52 48 48 13 10) nil 3)
           (unless (= before *test-flushes*)
             (error "connection refusal reappended an FNFD batch")))
      (setf (symbol-function 'fnn-feed-dial-plan) old-plan
            (symbol-function 'fnn-feed-lost) old-lost))))

;; The stop hook may wake a socket but never closes it.  The worker's
;; unwind-protect owns the one close, and a dial completing after stop cannot
;; publish its descriptor into the service table.
(let* ((runtime (%make-fnn-feed-runtime :service :stop-test
                                         :links nil
                                         :lock (sb-thread:make-mutex)
                                         :limit 512))
       (link (%make-fnn-feed-link :peer "stopping" :peer-octets #(115)
                                  :socket :stop-socket :fd 13 :ready t))
       (shutdowns nil) (closes nil)
       (old-shutdown (symbol-function 'fnn-socket-shutdown))
       (old-close (symbol-function 'fnn-socket-shut)))
  (unwind-protect
       (progn
         (setf (fnn-feed-runtime-links runtime) (list link)
               (symbol-function 'fnn-socket-shutdown)
               (lambda (socket) (push socket shutdowns) nil)
               (symbol-function 'fnn-socket-shut)
               (lambda (socket) (push socket closes) nil))
         (fnn-feed-runtime-put :stop-test runtime)
         (fnn-feed-service-wake :stop-test)
         (unless (and (equal shutdowns '(:stop-socket))
                      (eq (fnn-feed-link-socket link) :stop-socket)
                      (null closes))
           (error "stop hook closed or failed to shutdown its live socket"))
         (unless (null (fnn-feed-publish-socket runtime link :late-socket 14))
           (error "dial published a socket after the stop boundary"))
         (fnn-feed-worker runtime)
         (unless (and (null (fnn-feed-link-socket link))
                      (equal closes '(:stop-socket)))
           (error "worker did not own the one final socket close")))
    (fnn-feed-runtime-drop :stop-test)
    (setf (symbol-function 'fnn-socket-shutdown) old-shutdown
          (symbol-function 'fnn-socket-shut) old-close)))

(format t "native feed raw phase/sequencing test passed~%")
