; Raw test instrumentation. Load after ACL2 :q, after the selected mutant.
(in-package "ACL2")
(defvar *e1q-hooks* nil)
(defvar *e1q-stack* nil)
(defvar *e1q-stream* nil)
(defvar *e1q-tape* nil)
(defvar *e1q-replay* nil)
(defvar *e1q-tape-used* 0)
(defvar *e1q-randoms* 0)
(defvar *e1q-core* 0)
(defvar *e1q-reference* 0)
(defvar *e1q-turn* 0)
(defvar *e1q-boundary* nil)
(defvar *e1q-start* 0)
(defvar *e1q-seconds* 120)
(defvar *e1q-cap* 500000)

(defun e1q-seconds ()
  (/ (- (get-internal-real-time) *e1q-start*)
     (float internal-time-units-per-second 1d0)))
(defun e1q-record (event)
  (when *e1q-stream*
    (let ((*print-pretty* nil) (*print-length* nil) (*print-level* nil))
      (write event :stream *e1q-stream* :readably t)
      (terpri *e1q-stream*))))
(defun e1q-boundary (kind verdict)
  (unless (or *e1q-boundary* (eq verdict :pass))
    (setf *e1q-boundary*
          (list :kind kind :turn *e1q-turn* :core *e1q-core*
                :reference *e1q-reference* :randoms *e1q-randoms*
                :contract verdict))
    (e1q-record (list :first-failure *e1q-boundary*))
    (finish-output *e1q-stream*)))
(defun e1q-budget ()
  (when (or (>= (+ *e1q-core* *e1q-reference*) *e1q-cap*)
            (>= (e1q-seconds) *e1q-seconds*))
    (throw 'e1q-end (list :censored :qualification-budget))))

; Wrap both executable entry points, preserving each entry point's multiple
; values. *1* may dispatch to the raw function; the dynamic stack suppresses
; duplicate accounting in that case. This changes no semantic return value,
; except deliberate PRNG-tape replay, which retains the original PRNG state
; advancement while substituting the saved word.
(defun e1q-wrap (name wrapper)
  (dolist (symbol (remove-duplicates (list name (*1*-symbol name))))
    (when (fboundp symbol)
      (let ((old (symbol-function symbol)))
        (push (cons symbol old) *e1q-hooks*)
        (setf (symbol-function symbol)
              (lambda (&rest args)
                (if (member name *e1q-stack*) (apply old args)
                  (let ((*e1q-stack* (cons name *e1q-stack*)))
                    (funcall wrapper old args)))))))))
(defun e1q-restore ()
  (dolist (pair *e1q-hooks*) (setf (symbol-function (car pair)) (cdr pair)))
  (setf *e1q-hooks* nil))
(defun e1q-install ()
  (assert (null *e1q-hooks*))
  (e1q-wrap 'fn2-sim-random
    (lambda (old args)
      (when (and *e1q-replay* (null *e1q-tape*))
        (throw 'e1q-end (list :replay-prefix-exhausted)))
      (let ((values (multiple-value-list (apply old args))))
        (when *e1q-replay*
          (setf (car values) (pop *e1q-tape*))
          (incf *e1q-tape-used*))
        (incf *e1q-randoms*)
        (e1q-record (list :random *e1q-randoms* (car values)))
        (values-list values))))
  (e1q-wrap 'fn2-transition
    (lambda (old args) (e1q-budget) (incf *e1q-core*) (apply old args)))
  (e1q-wrap 'fn2-ref-transition
    (lambda (old args) (e1q-budget) (incf *e1q-reference*) (apply old args)))
  (e1q-wrap 'fn2-check-trace-turn
    (lambda (old args)
      (incf *e1q-turn*)
      (multiple-value-prog1 (apply old args)
        (e1q-record (list :turn *e1q-turn* :core *e1q-core*
                         :reference *e1q-reference* :randoms *e1q-randoms*)))))
  (dolist (entry '((fn2-echo-check-turn . :turn-monitors)
                   (fn2-echo-client-round . :client-oracle)
                   (fn2-echo-live-advance . :live-adapter)))
    (let ((kind (cdr entry)))
      (e1q-wrap (car entry)
        (lambda (old args)
          (let ((values (multiple-value-list (apply old args))))
            (e1q-boundary kind (car values))
            (values-list values))))))
  (e1q-wrap 'fn2-sim-record
    (lambda (old args)
      (e1q-record (cons :observation (subseq args 0 10)))
      (apply old args)))
  (e1q-wrap 'fn2-sim-environment
    (lambda (old args)
      (destructuring-bind (slot fault word sim) args
        (e1q-record
          (list :choice :turn *e1q-turn* :op slot
                :generation (fn2-sim-gen slot sim)
                :cell (if (= (fn2-sim-active slot sim) 2) 1 0)
                :active (fn2-sim-active slot sim) :kind (fn2-sim-kind slot sim)
                :capability (list (fn2-sim-cap-index slot sim) (fn2-sim-cap-nonce slot sim))
                :fault fault :word word :now (fn2-sim-now sim))))
      (apply old args)))
  (e1q-wrap 'fn2-sim-delay-flight
    (lambda (old args)
      (destructuring-bind (slot fault word sim) args
        (let* ((now (fn2-sim-now sim))
               (expected (min #xfffffffffffffff
                           (+ now (if (= fault 14)
                                      (nth (mod word 3) '(1000 10000 100000)) 100))))
               (after (apply old args)))
          (when (member fault '(2 14))
            (let ((actual (fn2-sim-due slot after)))
              (e1q-record (list :delay-class :op slot :fault fault :word word
                               :now now :expected expected :actual actual))
              (unless (= expected actual)
                (e1q-boundary :adapter-latency
                  (list :fail :delay-class fault word expected actual))
                (throw 'e1q-end (list :fail :delay-class fault word expected actual)))))
          after)))))
