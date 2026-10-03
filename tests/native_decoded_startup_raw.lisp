;;; Actual startup roster/thread and terminal scratch consumer. Typed methods
;;; are recording boundaries; this is not a pool accounting proof.
(load "tests/native_decoded_worker_raw.lisp")
(in-package "ACL2")
(load-deployed-forms "host/native/io.lisp"
 '((defvar *fnn-native-observer*) (defvar *fnn-native-actor-identity*) (defvar *fnn-native-wait-release*)
   (defmacro fnn-with-observed-mutex) (defun fnn-observed-condition-wait)))
(load-deployed-forms "host/native/extent.lisp"
 '((defvar *fnn-cold-workers*) (defvar *fnn-cold-free*) (defvar *fnn-cold-stopping*)
   (defun fnn-extent-executor-loop) (defun fnn-extent-executor-start) (defun fnn-extent-executor-stop)
   (defun fnn-extent-executor-observe-returned)
   (defun fnn-extent-window-release) (defun fnn-extent-window-settle-cancelled)))
(defun fnn-native-observed-thread-thunk (body) body)
(defun fn-pwx-tokenp (token) (declare (ignore token)) nil)
(defun fnn-err (&rest args) (declare (ignore args)) nil)
(defvar *startup-word* :ready)
(defvar *startup-events* nil)
(defvar *startup-cut* nil)
(defvar *startup-retained* nil)
(defvar *release-cut* nil)
(defun fnn-core (subject &rest args)
 (push subject *startup-events*)
 (case subject
  (fn-prstartup-planp (equal args '(:admitted-plan)))
  (fn-prstartup-decoded-workers 2)
  (fn-pxe-new (list :row (first args)))
  (create-fn-decoded-job
   (setq *startup-retained* (first *fnn-cold-workers*))
   (when (eq *startup-cut* :creator) (error "constructor cut"))
   *decoded-job*)
  (fn-dwj-reserve
   (assert (eq (first args) *decoded-job*))
   (when (eq *startup-cut* :reserve) (error "reserve cut"))
   *decoded-job*)
  (otherwise (error "unexpected startup core ~s" subject))))
(defun fnn-cold-call (subject &rest args)
 (declare (ignore args))
 (push subject *startup-events*)
 (case subject
  (fn-owner-page-read-default-worker-reservedp (list (not (eq *startup-cut* :reservation))))
  (fn-owner-page-read-default-worker-ready
   (assert (fnn-cold-worker-thread (first *fnn-cold-workers*)))
   (assert (not (eq *fnn-cold-free* (first *fnn-cold-workers*))))
   (list *startup-word* :same-pool))
  ((fn-owner-page-window-executor-release fn-owner-page-window-executor-settle-cancelled)
   (when *release-cut* (error "torn settlement"))
   (list :released :idle-row :same-pool))
  (otherwise (error "unexpected startup cold ~s" subject))))
;; The free stack is populated only after constructed/reserved scratch and
;; the actual private thread both exist. Failed readiness still joins it.
(let ((*decoded-job* (vector :scratch)) (*startup-events* nil))
 (unwind-protect
  (progn
   (fnn-extent-executor-start 2 :admitted-plan)
   (assert (= 2 (length *fnn-cold-workers*)))
   (assert *fnn-cold-free*)
   (dolist (worker *fnn-cold-workers*)
    (assert (eq :idle (fnn-cold-worker-phase worker)))
    (assert (sb-thread:thread-alive-p (fnn-cold-worker-thread worker)))
    (assert (eq :idle (fnn-decoded-activation-stage (fnn-cold-worker-decoded-storage worker)))))
   (assert (= 2 (count 'create-fn-decoded-job *startup-events*)))
   (assert (= 2 (count 'fn-dwj-reserve *startup-events*))))
  (fnn-extent-executor-stop)))
(dolist (cut '(:creator :reserve :ready))
 (let ((*decoded-job* (vector :scratch)) (*startup-cut* cut)
       (*startup-word* (if (eq cut :ready) :default-worker-not-reserved :ready))
       (*startup-retained* nil) (*startup-events* nil))
  (assert (handler-case (progn (fnn-extent-executor-start 2 :admitted-plan) nil) (error () t)))
  (assert (null *fnn-cold-free*))
  (assert (null *fnn-cold-workers*))
  (assert *startup-retained*)
  (when (fnn-cold-worker-thread *startup-retained*)
   (assert (not (sb-thread:thread-alive-p (fnn-cold-worker-thread *startup-retained*)))))))
;; Legacy direct startup creates no decoder and does not acknowledge readiness.
(let ((*startup-events* nil))
 (unwind-protect
  (progn (fnn-extent-executor-start 1)
   (assert (null (fnn-cold-worker-decoded-storage (first *fnn-cold-workers*))))
   (assert (not (member 'create-fn-decoded-job *startup-events*))))
  (fnn-extent-executor-stop)))
;; Use the actual release consumer after an affirmative return. The semantic
;; retirement runs before settlement. A torn settlement refuses repeat entry.
(defun fnn-core-cold-single (subject &rest args)
 (declare (ignore args))
 (case subject (fn-pwx-boundp t) (fn-owner-page-read-ledger :ledger)
  (otherwise (error "unexpected terminal single ~s" subject))))
(defvar *terminal-order* nil)
(defun fnn-call (subject &rest args)
 (push subject *terminal-order*)
 (case subject
  (fn-owner-page-decoded-job-retire
   (assert (eq (fourth args) :same-pool))
   (list :reusable (third args) :same-pool))
  (otherwise (error "unexpected terminal subject ~s" subject))))
(let* ((*decoded-job* (vector :scratch))
       (activation (make-fnn-decoded-activation :job *decoded-job* :stage :idle))
       (thread (sb-thread:make-thread (lambda () nil)))
       (worker (%make-fnn-cold-worker :row :row :token :token :phase :returned :thread thread
                                     :decoded activation :decoded-storage activation :result activation)))
 (sb-thread:join-thread thread)
 (let ((*release-cut* t))
  (assert (handler-case (progn (fnn-extent-window-release worker :token) nil) (error () t))))
 (assert (eq :releasing (fnn-cold-worker-phase worker)))
 (assert (eq activation (fnn-cold-worker-decoded-storage worker)))
 (let ((before (length *terminal-order*)))
  (assert (handler-case (progn (fnn-extent-window-release worker :token) nil) (error () t)))
  (assert (= before (length *terminal-order*)))))
(format t "native_decoded_startup_raw: PASS real startup/ready refusal/legacy/no retry after torn settlement~%")

;; A plan alone is insufficient: a refused installed slot allocates no backing.
(let ((*startup-cut* :reservation) (*startup-events* nil))
 (assert (handler-case (progn (fnn-extent-executor-start 2 :admitted-plan) nil) (error () t)))
 (assert (not (member 'create-fn-decoded-job *startup-events*)))
 (assert (null *fnn-cold-workers*)))
