(require :sb-bsd-sockets)
(defpackage "ACL2" (:use "COMMON-LISP"))
(in-package "ACL2")
(defconstant +fnn-exit-ok+ 0)
(defconstant +fnn-exit-uncertain+ 3)
(defconstant +fnn-exit-fault+ 4)
(defvar *fnn-extent-lock* (sb-thread:make-mutex))
(defvar *the-live-state* :state)
(defvar *service* nil)
(defvar *pool* (vector :same-pool))
(defvar *mio* (vector :same-mio))
(defvar *token* nil)
(defvar *mode* :opened)
(defvar *close-word* :closed-held)
(defvar *settle-word* :held)
(defvar *start-mode* :reserved)
(defvar *calls* nil)
(defvar *debits* 0)
(defvar *refunds* 0)
(defvar *cases* 0)
(defvar *condition-reports* 0)
(defvar *seen-fault* nil)
(define-condition custody-print-trap (error) ()
  (:report (lambda (condition stream)
             (declare (ignore condition stream))
             (incf *condition-reports*)
             (error "custody condition must not be rendered"))))
(defvar *opaque-cause* (make-condition 'custody-print-trap))
(defun fnn-developer-selector (name) (declare (ignore name)) nil)
(defun fnn-owner-stop-service-locked (service code)
  (assert (sb-thread:holding-mutex-p (fnn-owner-service-lock service)))
  (setf (fnn-owner-service-stopping service) t
        (fnn-owner-service-exit-code service) code))
 ;; Scheduler is a recording macro; selected production SERIALIZED/SHARED
;; bodies provide actual stopping/refusal/fencing under this real mutex.
(defmacro fnn-owner-gated ((service class) &body body)
  (declare (ignore class))
  `(sb-thread:with-mutex ((fnn-owner-service-lock ,service)) ,@body))
(defun fnn-owner-action (name &rest args)
  (unless (eq name 'fn-owner-exposure-release)
    (error "legacy action forbidden: ~a ~a" name args)))
(defmacro fnn-with-roster ((service) &body body)
  `(sb-thread:with-mutex ((fnn-owner-service-roster ,service)) ,@body))
(defun fnn-socket-shut (socket) (declare (ignore socket)))
(defun fnn-mux-start-waiting-handshake (loop) (declare (ignore loop)))
(defun fnn-live-arena () :arena)
(defun fnn-owner-sasl-seed () :seed)
(defun fnn-owner-sasl-context (&rest args) (declare (ignore args)))
(defun fnn-owner-advance-clock ())
(defun fnn-owner-log ())
(defun fnn-owner-octets-global (name) (declare (ignore name)) #())
(defun fnn-owner-response-unpin (&rest args) (declare (ignore args)))
(defun fnn-owner-socket-address (&rest args) (declare (ignore args)) (values :inet '(127 0 0 1)))
(defun fnn-owner-core (name &rest args)
  (declare (ignore args))
  (case name
    (fn-owner-peer-for-socket-address nil)
    (otherwise (error "legacy core forbidden: ~a" name))))
(defun fnn-core (name &rest args)
  (case name
    (fn-ores-config-word (first args))
    (fn-ores-config-reason :recorded-refusal)
    (otherwise (error "unrecorded core call: ~a" name))))
(defun fnn-mux-after (&rest args) (declare (ignore args)))
(defun fnn-mux-queue (&rest args) (declare (ignore args)))
(load __SOURCE_FILE__)
(defun check-locks (mio pool)
  (assert (eq mio *mio*)) (assert (eq pool *pool*))
  (assert (sb-thread:holding-mutex-p *fnn-extent-lock*))
  (assert (sb-thread:holding-mutex-p (fnn-owner-service-lock *service*))))
(defun start (kind family address peer mio pool state)
  (declare (ignore family address peer))
  (check-locks mio pool)
  (push kind *calls*)
  (incf *debits*)
  ;; Token is deliberately unrelated to CID 41. Native treats this object
  ;; as opaque; the recorders retain identity with EQ only for the fixture.
  (setf *token* (vector :issued-independent-of-cid *debits*))
  (values (case *start-mode* (:error t) (:cause *opaque-cause*))
          (if (eq *start-mode* :cause) :reserved *start-mode*) *token* 91 mio pool state))
(defun open-callback (kind family address peer token fuel mio pool state)
  (declare (ignore kind family address peer))
  (check-locks mio pool)
  (assert (eq token *token*)) (assert (= fuel 91))
  (let ((node (fnn-owner-service-connection-head *service*)))
    (assert node) (assert (eq token (fnn-connection-custody-token node)))
    (assert (null (fnn-owner-service-connection-raw-token *service*))))
  (case *mode*
    (:escape (throw 'raw-ev-fncall :escaped))
    (:error (error "recorded core error"))
    (:condition (error *opaque-cause*))
    (:erp (values *opaque-cause* (list :recovery-required 41 token) mio pool state))
    (:unexpected (values nil (list *opaque-cause* 41 token) mio pool state))
    (:refused (incf *refunds*) (values nil (list :refused nil nil) mio pool state))
    (otherwise (values nil (list *mode* 41 token) mio pool state))))
(defun close-callback (id token faultp fuel mio pool arena state)
  (declare (ignore faultp))
  (check-locks mio pool)
  (assert (= id 41)) (assert token) (assert (= fuel 91)) (assert (eq arena :arena))
  ;; The node must still be rooted at the exact refund observation.
  (assert (fnn-owner-service-connection-head *service*))
  (when (eq *close-word* :escape) (throw 'raw-ev-fncall :escaped))
  (when (eq *close-word* :closed) (incf *refunds*))
  (values nil (list *close-word* id (unless (eq *close-word* :closed) token)) mio pool state))
(defun settle (token fuel mio pool state)
  (check-locks mio pool) (assert token)
  (assert (fnn-owner-service-connection-head *service*))
  (when (eq *settle-word* :released) (incf *refunds*))
  (values nil *settle-word* fuel mio pool state))
(defun fresh ()
  (setf *calls* nil *debits* 0 *refunds* 0 *mode* :opened *close-word* :closed-held
        *settle-word* :held *start-mode* :reserved
        *service* (%make-fnn-owner-service
                   :lock (sb-thread:make-mutex) :connection-start #'start
                   :connection-open #'open-callback :connection-close #'close-callback
                   :connection-abort #'settle :connection-settle #'settle
                   :connection-mio *mio* :connection-pool *pool*))
  (incf *cases*))
(defun opened ()
  (fnn-owner-serialized *service* nil
    (lambda () (fnn-owner-connection-open-locked *service* :reader nil nil nil))))
(defun expect-fault (thunk)
  (assert (handler-case (progn (funcall thunk) nil)
            (serious-condition (cause) (setf *seen-fault* cause) t)))
  (assert (fnn-owner-service-stopping *service*))
  (let ((before *debits*))
    (assert (handler-case (progn (opened) nil) (fnn-store-error () t)))
    (assert (= before *debits*))))

;; Acquired token precedes constructor allocation; a constructor escape keeps
;; the exact raw token in the service, and no admission proceeds after fence.
(fresh)
(let ((original (symbol-function 'fnn-connection-custody-make)))
  (unwind-protect
       (progn
         (setf (symbol-function 'fnn-connection-custody-make)
               (lambda (token)
                 (assert (= *debits* 1))
                 (assert (eq token (fnn-owner-service-connection-raw-token *service*)))
                 (error "constructor escaped")))
         (expect-fault #'opened)
         (assert (eq *token* (fnn-owner-service-connection-raw-token *service*)))
         (assert (null (fnn-owner-service-connection-head *service*)))
         (assert (= *refunds* 0)))
    (setf (symbol-function 'fnn-connection-custody-make) original)))

;; Even ERP+token must be rooted before any word/error inspection.
(fresh) (setf *start-mode* :error)
(expect-fault #'opened)
(assert (eq *token* (fnn-owner-service-connection-raw-token *service*)))
(assert (= *refunds* 0))

(dolist (mode '(:escape :error :recovery-required))
  (fresh) (setf *mode* mode)
  (expect-fault #'opened)
  (assert (eq *token* (fnn-connection-custody-token (fnn-owner-service-connection-head *service*))))
  (assert (= *refunds* 0)))

(fresh) (setf *mode* :refused)
(assert (null (opened)))
(assert (null (fnn-owner-service-connection-head *service*)))
(assert (= *refunds* 1))

 ;; Actual retained paths preserve the same opaque cause without invoking
;; its unbounded/arbitrary condition report, including returned error values.
(fresh) (setf *start-mode* :cause)
(expect-fault #'opened)
(assert (eq *opaque-cause* (fnn-fixed-fault-cause *seen-fault*)))
(assert (eq :issuer-error (fnn-fixed-fault-tag *seen-fault*)))
(assert (eq *token* (fnn-owner-service-connection-raw-token *service*)))
(dolist (mode '(:condition :erp :unexpected))
  (fresh) (setf *mode* mode)
  (expect-fault #'opened)
  (assert (typep *seen-fault* 'fnn-fixed-callback-fault))
  (assert (eq *opaque-cause*
              (if (eq mode :unexpected) (first (fnn-fixed-fault-cause *seen-fault*))
                (fnn-fixed-fault-cause *seen-fault*))))
  (assert (fnn-owner-service-connection-head *service*)))
(assert (zerop *condition-reports*))

;; Logical close holds aliases; only the core's later release unlinks.
(fresh)
(multiple-value-bind (id node) (opened)
  (fnn-owner-serialized *service* id
    (lambda () (fnn-owner-connection-close-locked *service* id node nil)))
  (assert (eq (fnn-connection-custody-phase node) :retiring))
  (assert (eq node (fnn-owner-service-connection-head *service*)))
  (assert (= *refunds* 0))
  (setf *settle-word* :released)
  (fnn-owner-serialized *service* id
    (lambda () (fnn-owner-connection-settle-locked *service* node 91 nil)))
  (assert (= *refunds* 1))
  (assert (null (fnn-owner-service-connection-head *service*)))
  (assert (null (fnn-connection-custody-token node))))

;; Core release and native unlink occur within the same exclusion. Physical
;; endpoint cleanup never independently refunds; direct close is idempotent.
(fresh) (setf *close-word* :closed)
(multiple-value-bind (id node) (opened)
  (dotimes (i 2)
    (declare (ignore i))
    (fnn-owner-serialized *service* id
      (lambda () (fnn-owner-connection-close-locked *service* id node nil))))
  (assert (= *refunds* 1))
  (assert (null (fnn-owner-service-connection-head *service*))))

 ;; An escape after core refund but before physical unlink fences within
;; the SAME owner exclusion. Cleanup overlap stays funded by the baseline.
(fresh) (setf *close-word* :closed)
(multiple-value-bind (id node) (opened)
  (let ((original (symbol-function 'fnn-connection-custody-released)))
    (unwind-protect
         (progn
           (setf (symbol-function 'fnn-connection-custody-released)
                 (lambda (service held)
                   (check-locks *mio* *pool*)
                   (assert (= *refunds* 1))
                   (assert (eq held (fnn-owner-service-connection-head service)))
                   (error "unlink interrupted")))
           (expect-fault (lambda () (fnn-owner-serialized *service* id
                                     (lambda () (fnn-owner-connection-close-locked *service* id node nil)))))
           (assert (eq node (fnn-owner-service-connection-head *service*))))
      (setf (symbol-function 'fnn-connection-custody-released) original))))

(fresh) (setf *close-word* :yield)
(multiple-value-bind (id node) (opened)
  (fnn-owner-serialized *service* id
    (lambda () (fnn-owner-connection-close-locked *service* id node nil)))
  (assert (eq :close-pending (fnn-connection-custody-phase node)))
  (assert (= *refunds* 0))
  (setf *close-word* :escape)
  (expect-fault (lambda () (fnn-owner-serialized *service* id
                            (lambda () (fnn-owner-connection-close-locked *service* id node nil)))))
  (assert (eq node (fnn-owner-service-connection-head *service*))))

;; Repin uses the explicit completion disposition; old/new remain separately
;; rooted for held, refusal and uncertainty. New token never replaces old in place.
(dolist (word '(:committed-repin-held :committed-repin-released :committed :uncertain))
  (fresh)
  (multiple-value-bind (id old) (opened)
    (let* ((new-token (vector :replacement 999))
           (new (fnn-owner-serialized *service* id
                  (lambda () (fnn-connection-custody-retain *service* new-token)))))
      (if (eq word :uncertain)
          (expect-fault (lambda () (fnn-owner-serialized *service* id
                                    (lambda () (fnn-owner-connection-repin-joined-locked *service* old new word)))))
        (assert (eq (if (eq word :committed) old new)
                    (fnn-owner-serialized *service* id
                      (lambda () (fnn-owner-connection-repin-joined-locked *service* old new word))))))
      (assert (eq new (fnn-owner-service-connection-head *service*)))
      (assert (eq (fnn-connection-custody-next new)
                  (unless (eq word :committed-repin-released) old)))
      (assert (eq new-token (fnn-connection-custody-token new))))))

(fresh)
(multiple-value-bind (id old) (opened)
  (let ((new (fnn-owner-serialized *service* id
               (lambda () (fnn-connection-custody-retain *service* (vector :aborted-new))))))
    (assert (eq old (fnn-owner-serialized *service* id
                     (lambda () (fnn-owner-connection-repin-joined-locked
                                 *service* old new :committed-repin-aborted)))))
    (assert (eq old (fnn-owner-service-connection-head *service*)))
    (assert (eq :live (fnn-connection-custody-phase old)))
    (assert (eq :released (fnn-connection-custody-phase new)))
    (assert (null (fnn-connection-custody-token new)))))

;; Removing selected wiring cannot silently return to legacy lookup/open.
(fresh)
(opened)
(setf (fnn-owner-service-connection-start *service*) nil)
(expect-fault #'opened)
(assert (fnn-owner-service-connection-head *service*))

;; Actual endpoint opening bodies route kinds and retain direct node identity.
(fresh)
(let* ((loop (%make-fnn-mux-loop :service *service*))
       (conn (%make-fnn-mux-conn :socket :recorded-socket)))
  (fnn-mux-admit loop conn nil)
  (assert (= (fnn-mux-conn-cid conn) 41))
  (assert (eq (fnn-mux-conn-custody conn) (fnn-owner-service-connection-head *service*)))
  (assert (equal *calls* '(:exposure)))
  ;; Actual physical finish must settle the holder even after a logical close
  ;; has cleared CID. The core may still report aliases held.
  (setf (fnn-mux-conn-cid conn) nil)
  (fnn-mux-finish loop conn)
  (assert (eq :done (fnn-mux-conn-phase conn)))
  (assert (eq :retiring (fnn-connection-custody-phase (fnn-mux-conn-custody conn))))
  (assert (fnn-owner-service-connection-head *service*)))
(fresh)
(multiple-value-bind (id node) (fnn-web-open *service* :inet '(127 0 0 1) nil)
  (assert (= id 41)) (assert (eq node (fnn-owner-service-connection-head *service*)))
  (assert (equal *calls* '(:exposure)))
  (fnn-web-close *service* id node)
  (assert (eq (fnn-connection-custody-phase node) :retiring)))
(fresh)
(multiple-value-bind (id greeting node) (fnn-pull-local-open *service* '(112 101 101 114))
  (declare (ignore greeting))
  (assert (= id 41)) (assert (eq node (fnn-owner-service-connection-head *service*)))
  (assert (equal *calls* '(:peer))))
(fresh)
(assert (eq :refused
  (fnn-owner-serialized *service* nil
    (lambda () (fnn-owner-live-reconfigure-locked *service*
                 (lambda (id) (assert (= id 41)) :refused))))))
(assert (equal *calls* '(:reader)))
(assert (eq :retiring (fnn-connection-custody-phase (fnn-owner-service-connection-head *service*))))
(format t "PASS native connection custody: ~d scenarios~%" *cases*)
