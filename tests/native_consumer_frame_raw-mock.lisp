;;; `fn consumer --frame status|position|ack': the shipped CLI adapter prints
;;; the reply frame the one exchange read, as hex, in place of the line; ACL2
;;; chose the plan ((:frame PLAN), books/consumer-reason.lisp), the exchange
;;; returned the frame octets, and the adapter adds no exchange and no octet
;;; loop of its own (fnn-hex is the host's one hex routine, io.lisp).
(defpackage "ACL2" (:use "CL"))
(in-package "ACL2")

(defvar *calls* nil)
(defvar *out* nil)
(defvar *plan* nil)
(defvar *reply* nil)
(defvar *frame* nil)
(defparameter +fnn-exit-usage+ 2)
(defparameter +fnn-exit-ok+ 0)
(defun fnn-ascii-octet-list (s) (map 'list #'char-code s))
(defun fnn-octets (x) x)
(defun fnn-octet-list (x) (coerce x 'list))
(defun fnn-octets-string (x) (map 'string #'code-char x))
(defun fnn-octet-list-p (x)
  (and (listp x) (every (lambda (b) (and (integerp b) (<= 0 b 255))) x)))
(defun fnn-hex (octets)
  (with-output-to-string (s)
    (map nil (lambda (o) (format s "~(~2,'0x~)" o)) octets)))
(defun fnn-read-regular-bounded (path maximum)
  (declare (ignore path maximum))
  (list 1 2 3))
(defun fnn-core (name &rest args)
  (case name
    (fn-native-control-host-consumer-cli-plan *plan*)
    (fn-native-control-host-status-exit-code (if (eq (first args) :accepted) 0 1))
    (fn-native-control-host-consumer-cli-after nil)
    (fn-native-control-host-reply-detail nil)
    (otherwise (error "unexpected ACL2 entry ~s" name))))
(defun fnn-control-consumer-local (control operation first second)
  (push (list :request control operation first second) *calls*)
  (values *reply* nil *frame*))
(defun fnn-write-staged (path bytes) (push (list :write path bytes) *calls*))
(defun fnn-out (fmt &rest args) (push (apply #'format nil fmt args) *out*))
(defun fnn-err (&rest args) (error "unexpected CLI refusal ~s" args))
(defun fnn-fault (&rest args) (error "native fault ~s" args))
(defun fnn-register-verb (&rest args) (declare (ignore args)))

(let ((found nil))
  (with-open-file (stream "host/native/consumer-local.lisp")
    (loop for form = (read stream nil :eof)
          until (eq form :eof)
          when (and (consp form) (eq (car form) 'defun)
                    (member (cadr form) '(fnn-consumer-local-exchange
                                          fnn-command-consumer-local
                                          fnn-consumer-say)))
            do (eval form)
               (when (eq (cadr form) 'fnn-command-consumer-local)
                 (setf found t))))
  (unless found (error "deployed consumer CLI adapter missing")))

(defun scenario (name plan reply frame argv expected-calls)
  "Run the adapter once; it must print exactly the frame's hex, once."
  (let ((*calls* nil) (*out* nil) (*plan* plan) (*reply* reply) (*frame* frame))
    (let ((code (fnn-command-consumer-local "--frame" argv)))
      (unless (eql code 0) (error "~a: exit ~s" name code))
      (unless (equal (reverse *out*) (list (fnn-hex frame)))
        (error "~a: printed ~s, not the frame's hex ~s" name (reverse *out*) (fnn-hex frame)))
      (unless (equal (mapcar #'third (remove :write (reverse *calls*) :key #'first))
                     expected-calls)
        (error "~a: exchanges ~s, wanted exactly ~s" name *calls* expected-calls))))
  (format t "native consumer --frame ~a boundary passed~%" name))

(scenario "status"
          '(:frame (:run :status (99) (119) nil nil))
          '(:consumer-status-reply :accepted 3 10 7) 
          '(70 78 67 84 1 9 0 0 0 13 0)
          '("status" "control" "worker") '(:status))
(scenario "position"
          '(:frame (:run :position (99) (119) nil (111)))
          '(:consumer-reply :accepted (9 9 9)) 
          '(70 78 67 84 1 5 0 0 0 4 255 0 171)
          '("position" "control" "worker" "out") '(:position))
(scenario "ack"
          '(:frame (:run :ack (99) (119) nil nil))
          '(:consumer-reply :accepted (9 9 9)) 
          '(70 78 67 84 1 5 0 0 0 4 1 2 3 4)
          '("ack" "control" "cursor") '(:ack))

;; Without the flag the plan is the command's own and the line is printed:
;; the frame is never printed.
(let ((*calls* nil) (*out* nil)
      (*plan* '(:run :status (99) (119) nil nil))
      (*reply* '(:consumer-status-reply :accepted 3 10 7))
      (*frame* '(70 78 67 84)))
  (fnn-command-consumer-local "status" '("control" "worker"))
  (unless (and (= (length *out*) 1) (search "consumer status accepted" (first *out*))
               (not (search (fnn-hex *frame*) (first *out*))))
    (error "status without --frame printed ~s" *out*)))
(format t "native consumer --frame absent boundary passed~%")
