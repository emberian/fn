(defpackage "ACL2" (:use "CL"))
(in-package "ACL2")
(defconstant +fnn-exit-fault+ 4)
(defconstant +fnn-exit-uncertain+ 3)
(define-condition fnn-store-error (error) ())
(define-condition fnn-store-indeterminate (fnn-store-error) ())
(define-condition fnn-store-fault (fnn-store-error) ())
(define-condition fnn-os-error (error) ())
(defstruct fnn-owner-service receiver-runtime connection-pool stopping exit-code)
(defstruct fnn-connection-custody token)
(defvar *fnn-extent-lock* (sb-thread:make-mutex :name "parser fixture extent"))
(defvar *owner-lock* (sb-thread:make-mutex :name "parser fixture owner"))
(defvar *the-live-state* :actual-state)
(defvar *calls*)
(defvar *mode*)
(defvar *old-provider*)
(defvar *old-turn*)
(defvar *old-pool*)
(defvar *new-provider*)
(defvar *new-turn*)
(defvar *new-pool*)
(defvar *step*)
(defvar *episode*)
(defvar *scenarios* 0)
(defun fnn-live-arena () :actual-arena)
(defun fnn-live-cat () :actual-cat)
(defun fnn-developer-selector (name) (declare (ignore name)) nil)
(defun fnn-owner-connection-selected-p (service) (declare (ignore service)) t)
(defun fnn-owner-stop-service-locked (service code)
  (assert (sb-thread:holding-mutex-p *owner-lock*))
  (setf (fnn-owner-service-stopping service) t
        (fnn-owner-service-exit-code service) code))
(defun fnn-fixed-callback-fail (subject word detail)
  (error "Callback ~s: ~s: ~a" subject word detail))
(load __SOURCE_FILE__)

(defun recording-parser (cid holder sched ticket provider turn current pool arena cat state)
  (incf *calls*)
  (assert (sb-thread:holding-mutex-p *owner-lock*))
  (assert (sb-thread:holding-mutex-p *fnn-extent-lock*))
  (assert (equal (list cid holder sched ticket current arena cat state)
                 '(7 :actual-holder :actual-sched :actual-ticket :actual-current
                   :actual-arena :actual-cat :actual-state)))
  (assert (eq provider *old-provider*))
  (assert (eq turn *old-turn*))
  (assert (eq pool *old-pool*))
  (case *mode*
    ((:raw-escape :condition)
     ;; Recording actual in-place stobj mutation before nonlocal escape.
     (setf (gethash :phase turn) :parser-installing
           (gethash :rc turn) *step*
           (gethash :capacity provider) nil)
     (if (eq *mode* :raw-escape)
         (throw 'raw-ev-fncall nil)
       (error "recorded parser escape after staged RC")))
    (otherwise
     (values *mode*
             (and (eq *mode* :response-recorded) *step*)
             (and (eq *mode* :response-recorded) *episode*)
             *new-provider* *new-turn* *new-pool* state))))

(defmacro scenario (&body body)
  `(let* ((*calls* 0) (*mode* :response-recorded)
          (*old-provider* (make-hash-table)) (*old-turn* (make-hash-table))
          (*old-pool* (list :actual-pool))
          (*new-provider* (make-hash-table)) (*new-turn* (make-hash-table))
          (*new-pool* (list :returned-pool))
          (*step* (list :actual-step)) (*episode* (list :actual-episode))
          (runtime (fnn-owner-receiver-turn-runtime-make
                    :capacity :actual-current :start :next :ack :fence :limits #'recording-parser))
          (service (make-fnn-owner-service :receiver-runtime runtime :connection-pool *old-pool*))
          (node (make-fnn-connection-custody :token :actual-holder)))
     (incf *scenarios*)
     (setf (gethash :capacity *old-provider*) :published
           (gethash :phase *old-turn*) :filled
           (fnn-owner-receiver-turn-runtime-provider runtime) *old-provider*
           (fnn-owner-receiver-turn-runtime-turn runtime) *old-turn*)
     ,@body))

(defun invoke (service node)
  (sb-thread:with-mutex (*owner-lock*)
    (fnn-owner-shared-action-locked service 7
      (lambda () (fnn-owner-receiver-turn-parser-locked
                  service 7 node :actual-sched :actual-ticket)))))

(dolist (word '(:response-recorded :parser-progress-recorded :parser-fenced :unavailable-parser-source))
  (scenario
    (setf *mode* word)
    (multiple-value-bind (actual step episode) (invoke service node)
      (assert (eq actual word))
      (assert (eq step (and (eq word :response-recorded) *step*)))
      (assert (eq episode (and (eq word :response-recorded) *episode*)))
      (assert (eq (fnn-owner-receiver-turn-runtime-provider runtime) *new-provider*))
      (assert (eq (fnn-owner-receiver-turn-runtime-turn runtime) *new-turn*))
      (assert (eq (fnn-owner-service-connection-pool service) *new-pool*))
      (assert (not (fnn-owner-service-stopping service)))
      (assert (= *calls* 1)))))

(dolist (absent '(:runtime :node :callback))
  (scenario
    (case absent
      (:runtime (setf (fnn-owner-service-receiver-runtime service) nil))
      (:node (setf node nil))
      (:callback (setf (fnn-owner-receiver-turn-runtime-parser runtime) nil)))
    (assert (handler-case (progn (invoke service node) nil) (error () t)))
    (assert (zerop *calls*))
    (assert (fnn-owner-service-stopping service))
    (assert (= (fnn-owner-service-exit-code service) +fnn-exit-fault+))
    (assert (eq (fnn-owner-service-connection-pool service) *old-pool*))))

(dolist (escape '(:raw-escape :condition))
  (scenario
    (setf *mode* escape)
    (assert (handler-case (progn (invoke service node) nil) (error () t)))
    (assert (= *calls* 1))
    (assert (fnn-owner-service-stopping service))
    (assert (= (fnn-owner-service-exit-code service) +fnn-exit-fault+))
    (assert (eq (fnn-owner-receiver-turn-runtime-turn runtime) *old-turn*))
    (assert (eq (gethash :phase *old-turn*) :parser-installing))
    (assert (eq (gethash :rc *old-turn*) *step*))
    (assert (null (gethash :capacity *old-provider*)))
    (assert (eq (fnn-owner-service-connection-pool service) *old-pool*))))

(scenario
  (let ((old-call (fnn-owner-receiver-turn-runtime-make
                   :capacity :actual-current :start :next :ack :fence :limits)))
    (assert (null (fnn-owner-receiver-turn-runtime-parser old-call)))
    (assert (eq (fnn-owner-receiver-turn-runtime-current old-call) :actual-current))
    (assert (eq (fnn-owner-receiver-turn-runtime-limits old-call) :limits))))

(scenario
  (setf (fnn-owner-service-receiver-runtime service) nil)
  (let ((created 0))
    (sb-thread:with-mutex (*owner-lock*)
      (multiple-value-bind (word installed pool)
          (fnn-owner-receiver-current-startup
           service :demand :limits :actual-current
           (lambda () (incf created) *old-provider*)
           (lambda () (incf created) *old-turn*)
           (lambda (demand current pool)
             (assert (eq demand :demand)) (values :admitted :capacity current pool))
           (lambda (token current pool)
             (assert (eq token :capacity)) (values :allocate current pool))
           (lambda (token provider turn current pool)
             (assert (eq token :capacity)) (values :installed provider turn current pool))
           :start :next :ack :fence :current-fence *old-pool* #'recording-parser)
        (assert (eq word :installed)) (assert (eq pool *old-pool*))
        (assert (eq installed (fnn-owner-service-receiver-runtime service)))
        (assert (eq (fnn-owner-receiver-turn-runtime-parser installed) #'recording-parser))
        (assert (eq (fnn-owner-receiver-turn-runtime-provider installed) *old-provider*))
        (assert (eq (fnn-owner-receiver-turn-runtime-turn installed) *old-turn*))
        (assert (= created 2)))))
  (assert (eq (invoke service node) :response-recorded)))

(scenario
  (setf (fnn-owner-service-receiver-runtime service) nil)
  (sb-thread:with-mutex (*owner-lock*)
    (multiple-value-bind (word runtime pool)
        (fnn-owner-receiver-current-startup
         service :demand :limits :actual-current
         (lambda () (error "creator called after refused reserve"))
         (lambda () (error "turn creator called after refused reserve"))
         (lambda (demand current pool)
           (declare (ignore demand)) (values :unavailable nil current pool))
         nil nil :start :next :ack :fence :current-fence *old-pool* #'recording-parser)
      (assert (eq word :unavailable)) (assert (null runtime))
      (assert (eq pool *old-pool*))
      (assert (eq (fnn-owner-service-receiver-runtime service) :actual-current)))))

(format t "PASS native parser turn: ~d scenarios~%" *scenarios*)
