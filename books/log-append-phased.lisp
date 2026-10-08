; The captured log append's physical registration, member binding and write.
; fnn-log-append-capture has already advanced the kernel into flight. Rotation
; is refused until that batch settles. Registration is process-local: deaths
; before :write stutter to the preceding disk cut; :write retains log-written.
; Pending host integration: every append origin must have an off-O window.
; Labels are ((O K) . EFFECT): :off forbids that lock, :held requires it,
; :neither makes no locking decision. Thus a register/write effect is off
; BOTH O and K; a K-only split cannot execute this program. Bind only owns K.
; The host must dispatch from outside O; it may not merely check a label
; inside an O quantum. This book alone does not prove a caller releases O.
(in-package "ACL2")
(include-book "defkeystone")

(defun fn-lap-step (phase word)
  (declare (xargs :guard t))
  (cond ((eq phase :done) (mv nil :done))
        ((not (eq word :ok)) (mv '(((:neither :neither) . :fault)) :done))
        ((eq phase :start) (mv '(((:off :off) . :register)) :register))
        ((eq phase :register) (mv '(((:neither :held) . :bind)) :bind))
        ((eq phase :bind) (mv '(((:off :off) . :write)) :write))
        ((eq phase :write) (mv nil :done))
        (t (mv '(((:neither :neither) . :fault)) :done))))

(defun fn-lap-trace (phase words)
  (declare (xargs :guard t))
  (if (atom words) nil
    (mv-let (effects next) (fn-lap-step phase (car words))
      (append effects (fn-lap-trace next (cdr words))))))

; Independent specification, including the prefix that failed. No binding
; follows failed registration; no write follows failed binding.
(defun fn-lap-run (registered bound written)
  (declare (xargs :guard t))
  (cons '((:off :off) . :register)
        (if (not (eq registered :ok)) '(((:neither :neither) . :fault))
          (cons '((:neither :held) . :bind)
                (if (not (eq bound :ok)) '(((:neither :neither) . :fault))
                  (cons '((:off :off) . :write)
                        (if (eq written :ok) nil '(((:neither :neither) . :fault)))))))))

(defun fn-lap-labelsp (effects)
  (declare (xargs :guard t))
  (if (atom effects) (null effects)
    (and (member-equal (car effects)
                      '(((:off :off) . :register) ((:neither :held) . :bind)
                        ((:off :off) . :write) ((:neither :neither) . :fault)))
         (fn-lap-labelsp (cdr effects)))))

(defthm fn-lap-step-runs-the-phased-run
  (equal (fn-lap-trace :start (list :ok registered bound written))
         (fn-lap-run registered bound written)))

(defteeth fn-lap-step-runs-the-phased-run
  :subject fn-lap-step
  :claim (() (equal (fn-lap-trace :start (list :ok registered bound written))
                    (fn-lap-run registered bound written)))
  :witness ((registered :ok) (bound :ok) (written :ok))
  :breaks ()
  :mutations ((write-after-failed-registration
               (:conclusion
                (equal (fn-lap-trace :start (list :ok registered bound written))
                       '(((:off :off) . :register) ((:neither :held) . :bind) ((:off :off) . :write))))
               ((registered :error) (bound :ok) (written :ok))
               :fault "Continuing to bind and write after registration failed")))

(defthm fn-lap-step-keeps-io-off-owner-and-kernel
  (fn-lap-labelsp (mv-nth 0 (fn-lap-step phase word))))

(defteeth fn-lap-step-keeps-io-off-owner-and-kernel
  :subject fn-lap-step
  :claim (() (fn-lap-labelsp (mv-nth 0 (fn-lap-step phase word))))
  :witness ((phase :start) (word :ok))
  :breaks ()
  :mutations ((registration-under-kernel
               (:conclusion
                (fn-lap-labelsp
                 (if (and (eq phase :start) (eq word :ok))
                     '(((:off :held) . :register))
                   (mv-nth 0 (fn-lap-step phase word)))))
               ((phase :start) (word :ok))
               :fault "Running open/fstat while holding the log kernel mutex")
              (registration-under-owner
               (:conclusion
                (fn-lap-labelsp
                 (if (and (eq phase :start) (eq word :ok))
                     '(((:held :off) . :register))
                   (mv-nth 0 (fn-lap-step phase word)))))
               ((phase :start) (word :ok))
               :fault "Running open/fstat inside an owner quantum")))
