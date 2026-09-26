;;; The deployed owner chunk loop, driven without an image.
;;;
;;; `fnn-owner-serve-client', `fnn-owner-handle-chunk' and
;;; `fnn-owner-advance-clock' are read out of host/native/owner.lisp; the
;;; shared wall-clock helper is read out of host/native/io.lisp.  This
;;; exercises the shipped functions and not copies of them.  Everything they
;;; call that touches a socket, the owner mutex or ACL2 is stubbed, and the
;;; stubs record what the loop did and what the owner was handed.
;;;
;;; Three properties, each a defect found against the native 915 node on
;;; 2026-09-22 (planning/evidence/owner-defects-2026-09-22.md):
;;;
;;;   1. a step that consumes a prefix leaves the rest as the NEXT step's
;;;      input.  It is not a fault, and it is not read from the socket again.
;;;      The reachable case is an article over fn-own-body-limit, which closes
;;;      the wire mid-article (books/wire.lisp `fn-wire-after-line' answers
;;;      `fn-wire-close ... :body-overlimit' and
;;;      books/served-tls-prefix.lisp `fn-served-feed-counted' stops there);
;;;      the old line faulted and the whole process stopped.
;;;   2. a step that consumes nothing and neither closes nor hands the
;;;      transport over IS a fault: the same octets fed again cannot make
;;;      progress.
;;;   3. one clock reading reaches the owner at open and one before every
;;;      chunk, which is what gives each submission its own Injection-Date
;;;      (books/owner.lisp `fn-own-open'; RFC 5537 section 3.4).  A run whose
;;;      articles all carry one Date is exactly a host that read the clock
;;;      once.

(require :sb-posix)
(require :sb-bsd-sockets)
(defpackage "ACL2" (:use "CL"))
(in-package "ACL2")

;;; ---------------------------------------------------------------------------
;;; The boundary host/native/io.lisp and host/native/tls.lisp define.

(deftype fnn-octets () '(simple-array (unsigned-byte 8) (*)))
(defun fnn-make-octets (n)
  (make-array n :element-type '(unsigned-byte 8) :initial-element 0))
(defun fnn-octets (sequence)
  (if (typep sequence 'fnn-octets)
      sequence
      (let ((out (fnn-make-octets (length sequence)))) (replace out sequence) out)))
(defun fnn-octet-list (x) (coerce x 'list))
(defun fnn-octet-list-p (x)
  (and (listp x) (every (lambda (o) (and (integerp o) (<= 0 o 255))) x)))
(defun fnn-ascii (string) (fnn-octets (map 'list #'char-code string)))
(defun fnn-text (octets) (map 'string #'code-char octets))

(defconstant +fnn-exit-uncertain+ 3)

(define-condition fnn-store-error (error)
  ((message :initarg :message :reader fnn-message))
  (:report (lambda (c s) (write-string (fnn-message c) s))))
(define-condition fnn-store-fault (fnn-store-error) ())
(define-condition fnn-store-indeterminate (fnn-store-error) ())
(define-condition fnn-os-error (error) ())
(define-condition fnn-tls-error (error) ())
(define-condition fnn-owner-connection-fault (error)
  ((operation :initarg :operation) (cause :initarg :cause)))

(defun fnn-fault (control &rest args)
  (error 'fnn-store-fault :message (apply #'format nil control args)))
(defun fnn-refuse (control &rest args)
  (error 'fnn-store-error :message (apply #'format nil control args)))
(defun fnn-err (control &rest args)
  (format *error-output* "~a~%" (apply #'format nil control args)))

;;; ---------------------------------------------------------------------------
;;; The recording stubs.

(defvar *fnn-sigterm-requested* nil)

(defparameter *reads* nil)          ; octet vectors the socket will hand out
(defparameter *read-count* 0)       ; how many times the socket was read
(defparameter *chunks* nil)         ; each INCOMING the owner was handed
(defparameter *plans* nil)          ; (consumed closing starttls reply) per step
(defparameter *step* nil)           ; the plan the current step is running
(defparameter *output* nil)         ; the octets fn-owner-output holds now
(defparameter *sent* nil)           ; each reply written to the socket
(defparameter *faults* nil)         ; each fault the service was stopped with
(defparameter *graceful* 0)         ; graceful closes
(defparameter *observations* nil)   ; (monotonic wall error has-wall) per reading

(defun fnn-socket-fd (socket) (declare (ignore socket)) 7)
(defun fnn-socket-shut (socket) (declare (ignore socket)) nil)
(defun fnn-tls-close-channel (channel) (declare (ignore channel)) nil)
(defun fnn-graceful-close (fd) (declare (ignore fd)) (incf *graceful*))
(defun fnn-owner-service-stopping (service) (declare (ignore service)) nil)
(defun fnn-owner-service-tls-context (service) (declare (ignore service)) nil)
(defun fnn-owner-stop-service-locked (service code) (declare (ignore service code)) nil)
(defun fnn-owner-serialized (service cid thunk)
  (declare (ignore service cid)) (funcall thunk))
(defun fnn-owner-connection-call (service operation thunk)
  (declare (ignore service operation)) (funcall thunk))
(defun fnn-owner-socket-address (service socket)
  (declare (ignore service socket)) (values :inet (list 127 0 0 1)))
(defun fnn-owner-drain-one (service) (declare (ignore service)) (values nil nil nil))
(defun fnn-owner-fence-service (service) (declare (ignore service)) nil)
(defun fnn-owner-log () nil)
(defun fnn-owner-fault-service (service cid condition)
  (declare (ignore service cid))
  (push (princ-to-string condition) *faults*))
(defun fnn-owner-abandon-connection (service cid condition)
  (declare (ignore service cid condition)) nil)
(defun fnn-tls-consume-plaintext (fd expected seconds)
  (declare (ignore fd seconds)) expected)
(defun fnn-tls-accept (context fd seconds)
  (declare (ignore context fd seconds)) :channel)
(defun fnn-owner-send (fd channel octets seconds)
  (declare (ignore fd channel seconds))
  (push (fnn-text octets) *sent*))

(defun fnn-owner-receive (service fd channel seconds)
  (declare (ignore service fd channel seconds))
  (incf *read-count*)
  (if *reads* (pop *reads*) (fnn-make-octets 0)))

(defun fnn-owner-core (name &rest args)
  (declare (ignore args))
  (ecase name
    (fn-owner-peer-for-socket-address nil)
    ;; PRF-161: the accept is admitted and opened by one ACL2 call, and every
    ;; step is charged against the address's budget first.
    (fn-owner-exposure-open (setq *output* (fnn-ascii "200 ready")) 1)
    (fn-owner-exposure-charge :proceed)))

;; The four ACL2 globals one served read publishes.  The plan supplies them,
;; so the loop reads them exactly where host/owner-host.lisp puts them.
(defun fnn-owner-action (name &rest args)
  (ecase name
    (fn-owner-observe (push args *observations*) :observed)
    (fn-owner-chunk
     (push (fnn-text (second args)) *chunks*)
     (setq *step* (pop *plans*))
     (unless *step* (error "the loop took a step this scenario did not plan"))
     (setq *output* (fnn-ascii (fourth *step*)))
     :ok)
    (fn-owner-close :closed)
    (fn-owner-exposure-idle :keep)
    (fn-owner-exposure-release :released)
    (fn-owner-tls-established :ok)))

(defun fnn-owner-octets-global (name)
  (ecase name (fn-owner-output *output*)))
(defun fnn-owner-bool-global (name)
  (ecase name
    (fn-owner-closep (second *step*))
    (fn-owner-starttlsp (third *step*))
    (fn-owner-submittedp nil)))
(defun fnn-global (name)
  (ecase name
    ;; No read in these scenarios sends a 441 (books/owner-log.lisp
    ;; fn-olog-served-refusal-lines), so the refusal log lines are empty.
    (fn-owner-refusal-lines nil)
    ;; No step here reaches the failed-login limit (fn-exp-observe).
    (fn-owner-exposure-close nil)
    (fn-owner-consumed
     (if (eq (first *step*) :all) (length (first *chunks*)) (first *step*)))))

;;; ---------------------------------------------------------------------------
;;; The functions under test, read out of the file that ships them.

(dolist (source-and-names
         '(("host/native/io.lisp"
            +fnn-owner-wall-error-ms+ +fnn-owner-unix-dtn-offset-seconds+
            fnn-owner-wall-milliseconds)
           ("host/native/owner.lisp"
            fnn-owner-advance-clock fnn-owner-handle-chunk fnn-owner-serve-client
            fnn-owner-exposure-wait fnn-owner-exposure-idle)))
  (destructuring-bind (source . wanted) source-and-names
    (let ((found nil))
      (with-open-file (stream source)
        (loop for form = (read stream nil :eof)
              until (eq form :eof)
              when (and (consp form) (member (car form) '(defun defconstant))
                        (member (cadr form) wanted))
                do (eval form) (push (cadr form) found)))
      (let ((missing (set-difference wanted found)))
        (when missing
          (error "~a does not define ~{~a~^, ~}" source missing))))))

(defun run-scenario (reads plans)
  (setq *reads* (mapcar #'fnn-ascii reads)
        *read-count* 0 *chunks* nil *plans* plans *step* nil *output* nil
        *sent* nil *faults* nil *graceful* 0 *observations* nil)
  (fnn-owner-serve-client :service :socket)
  (setq *chunks* (reverse *chunks*) *sent* (reverse *sent*)
        *observations* (reverse *observations*)))

(defun check (test control &rest args)
  (unless test (error (apply #'format nil control args))))

;;; 1. A prefix consume leaves the suffix for the next step, and the socket is
;;;    not read for it.  The second read carries "BBBBB" and that step consumes
;;;    two octets; the third step must be handed exactly "BBB".
(run-scenario '("AAA" "BBBBB")
              (list (list :all nil nil "")
                    (list 2 nil nil "")
                    (list :all nil nil "")))
(check (equal *chunks* '("AAA" "BBBBB" "BBB"))
       "the suffix was not the next step's input: ~s" *chunks*)
(check (null *faults*) "a partial consume faulted: ~s" *faults*)
;; Three planned steps, then one read that ends the input: four reads would
;; mean the suffix had been taken from the socket a second time.
(check (= *read-count* 3) "the suffix was read from the socket again: ~d reads"
       *read-count*)

;;; 2. The oversize article: the step consumes the prefix that fitted, answers
;;;    the refusal and closes.  The process must survive, the client must get
;;;    the line, and the connection must end gracefully.
(run-scenario '("HELLO" "ARTICLE-TAIL")
              (list (list :all nil nil "")
                    (list 4 t nil "441 posting failed; the article was not received")))
(check (null *faults*) "an oversize article stopped the owner: ~s" *faults*)
(check (equal *sent* '("200 ready"
                       "441 posting failed; the article was not received"))
       "the refusal did not reach the client: ~s" *sent*)
(check (= *graceful* 1) "the connection did not close gracefully: ~d" *graceful*)
(check (equal *chunks* '("HELLO" "ARTICLE-TAIL"))
       "a closing step's suffix was fed back: ~s" *chunks*)

;;; 3. No progress is a fault: consumed 0, not closing, not handing over.
(run-scenario '("STUCK") (list (list 0 nil nil "")))
(check (= (length *faults*) 1) "a no-progress step did not fault: ~s" *faults*)
(check (search "consumed no octets" (first *faults*))
       "the no-progress fault says something else: ~s" (first *faults*))

;;; 4. One reading at open and two before every chunk (the exposure charge's
;;;    and the chunk's own, PRF-161: a waiting connection must see the clock
;;;    move), each a fresh reading of this host's clocks in the units
;;;    fn-clock-observation takes.
(run-scenario '("ONE" "TWO")
              (list (list :all nil nil "") (list :all nil nil "")))
(check (null *faults*) "an ordinary exchange faulted: ~s" *faults*)
(check (= (length *observations*) 5)
       "the owner was handed ~d clock readings for an open and two chunks"
       (length *observations*))
(let ((now (fnn-owner-wall-milliseconds)))
  (dolist (observation *observations*)
    (destructuring-bind (monotonic wall error has-wall) observation
      (check (and (integerp monotonic) (<= 0 monotonic))
             "a monotonic reading is not a count of milliseconds: ~s" monotonic)
      (check (and (integerp wall) (< (abs (- wall now)) 60000))
             "a wall reading is not this minute's: ~s against ~s" wall now)
      (check (and (integerp error) (< 0 error))
             "a reading carries no error bound: ~s" error)
      (check (eq has-wall t) "a reading claims no wall clock: ~s" has-wall))))
(check (apply #'<= (mapcar #'second *observations*))
       "the wall readings went backwards: ~s" (mapcar #'second *observations*))
;; The defect: one reading reused for the whole run.  A reading taken per
;; event moves with the clock, so sleeping past the resolution must change it.
(let ((before (fnn-owner-wall-milliseconds)))
  (sleep 1.1)
  (check (<= (+ before 1000) (fnn-owner-wall-milliseconds))
         "the wall reading did not advance over 1.1 seconds"))

(format t "native owner chunk loop: suffix, refusal, no-progress and clock passed~%")
