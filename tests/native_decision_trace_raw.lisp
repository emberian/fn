;;; Decision tracing: the ring and the call interposition, plain SBCL over the
;;; deployed `fnn-call', `fnn-core-mv' and host/native/trace.lisp (lane
;;; obs-decision-trace; keystones DT-1h, DT-4's shape, DT-5).
;;;
;;; ACL2's `fn-dtrace-project' is recorded by a mock that builds the row the
;;; way books/definterface.lisp's generated dispatch does: (POINT INPUTS
;;; OUTCOME), OUTCOME the first value the entry returned.  What is asserted is
;;; the host's half: the values reach the caller unchanged, a traced call's
;;; row holds what it returned, a masked stobj position is nil, counters
;;; balance in every snapshot, a full ring drops and never blocks, a failing
;;; projection is counted and swallowed, drain is an acknowledged cursor.
;;;
;;; FN_DT_RAW_MUTATION=skew arms the labelled mutation of tests/
;;; test_native_decision_trace.py: the ring's row takes the PREVIOUS call's
;;; outcome (the selector FN_NATIVE_TEST_TRACE_SKEW's mechanism), and the
;;; replay assertion below must then fail.
(load "tests/native_section_envelope_raw.lisp")
(in-package "ACL2")

(define-condition fnn-fixed-callback-fault (fnn-store-fault)
  ((subject :initarg :subject) (tag :initarg :tag) (cause :initarg :cause)))
(load-deployed-forms "host/native/io.lisp"
                     '((defun fnn-fixed-callback-fail) (defun fnn-call)
                       (defun fnn-core-mv-traced) (defmacro fnn-core-mv) (defun fnn-core)))

;;; The mock ACL2 world.  Each entry returns what its name says.
(defparameter *mock-entries* (make-hash-table :test 'eq))
(defparameter *mock-calls* 0)
(defun fnn-entry-guard (name args) (declare (ignore name args)) nil)
(defun fnn-raw-dispatch-apply (name args)
  (apply (or (gethash name *mock-entries*) (error "mock: no entry ~a" name)) args))
(defmacro defmock (name args &body body)
  `(setf (gethash ',name *mock-entries*) (lambda ,args ,@body)))

(defmock mock-word (n)
  (incf *mock-calls*)
  (values (case (mod n 3) (0 :ok) (1 :busy) (t :refused)) (list :state n)))
(defmock mock-stobj (n st) (declare (ignore st)) (values n :the-stobj))
(defmock mock-untraced (n) n)
(defvar *project-fails* nil)
(defmock fn-dtrace-project (point args vals)
  (when *project-fails* (error "projection failed"))
  (list point (copy-list args) (first vals)))
(defmock mock-mv () (values :a :b))

(defparameter *table*
  '((mock-word :class :verdict :positions (0) :stobjs-out (nil nil))
    (mock-stobj :class :schedule :positions (0) :stobjs-out (nil t))
    (mock-mv :class :plan :positions () :stobjs-out (nil nil))))

(defparameter *mutation* (sb-ext:posix-getenv "FN_DT_RAW_MUTATION"))
(defun fail (what) (format t "FAIL: ~a~%" what) (finish-output) (sb-ext:exit :code 1 :abort t))
(defmacro check (what form) `(unless ,form (fail ,what)))

(defun rows-of (since limit)
  "The rows (point class inputs outcome seq) and counters a drain returns."
  (multiple-value-bind (rows attempts recorded dropped sampled live next)
      (fnn-dtrace-snapshot *fnn-dtrace* since limit)
    (values (loop for r across rows
                  collect (list (fnn-dtrace-row-point r) (fnn-dtrace-row-class r)
                                (fnn-dtrace-row-inputs r) (fnn-dtrace-row-outcome r)
                                (fnn-dtrace-row-seq r)))
            (list attempts recorded dropped sampled live next))))

;;; ---- OFF: the default.  The values are the callee's, nothing is recorded.
(check "off by default" (null *fnn-dtrace*))
(check "off: values unchanged"
       (equal (fnn-call 'mock-word 4) '(:busy (:state 4))))
(check "off: nothing to note" (null (fnn-dtrace-drain 0 10)))
(check "enabled-p is nil off" (not (fnn-dtrace-enabled-p)))

;;; ---- ON, an untraced name allocates what off allocates (no clock, no row).
(defun calls (name n) (dotimes (i n) (fnn-call name i)))
(calls 'mock-untraced 100)
(sb-ext:gc :full t)
(let* ((b0 (sb-ext:get-bytes-consed)) (ignore (calls 'mock-untraced 100000))
       (off (- (sb-ext:get-bytes-consed) b0)))
  (declare (ignore ignore))
  (fnn-dtrace-start *table* :capacity 16)
  (calls 'mock-untraced 100)
  (sb-ext:gc :full t)
  (let* ((b1 (sb-ext:get-bytes-consed)) (ignore2 (calls 'mock-untraced 100000))
         (on (- (sb-ext:get-bytes-consed) b1)))
    (declare (ignore ignore2))
    (format t "DT_UNTRACED_ALLOC off=~d on=~d~%" off on)
    (check "an untraced name costs no allocation when tracing is on" (<= (abs (- on off)) 65536)))
  (fnn-dtrace-stop))
(check "stop turns it off" (null *fnn-dtrace*))

;;; ---- DT-1h on the mock: the row holds what the call returned.
(fnn-dtrace-start *table* :capacity 64 :skew (equal *mutation* "skew"))
(let ((returned (loop for n from 0 below 6 collect (first (fnn-call 'mock-word n)))))
  (check "values reach the caller" (equal returned '(:ok :busy :refused :ok :busy :refused)))
  (multiple-value-bind (rows counters) (rows-of 0 100)
    (check "six rows" (= (length rows) 6))
    (loop for row in rows for n from 0 for word in returned
          do (check (format nil "DT-1h: row ~d is the outcome returned (~a), got ~a" n word (fourth row))
                    (and (eq (first row) 'mock-word) (eq (second row) :verdict)
                         (equal (third row) (list n)) (eq (fourth row) word))))
    (check "seq runs from 1" (equal (mapcar #'fifth rows) '(1 2 3 4 5 6)))
    (check "counters" (equal counters '(6 6 0 0 6 7)))))

;;; ---- A masked stobj position is nil to ACL2's projection; the caller's values are not.
(fnn-dtrace-stop)
(fnn-dtrace-start *table* :capacity 8)
(check "the caller keeps its stobj" (equal (fnn-call 'mock-stobj 5 :st) '(5 :the-stobj)))
(let ((r (fnn-dtrace-masked-values (gethash 'mock-stobj (fnn-dtrace-ring-points *fnn-dtrace*)) '(5 :the-stobj))))
  (check "stobj position masked" (equal r '(5 nil))))

;;; ---- fnn-core-mv: a fixed callback traced by name, outcome only.
(check "core-mv preserves its values"
       (equal (multiple-value-list (fnn-core-mv 'mock-mv (values :a :b))) '(:a :b)))
(multiple-value-bind (rows) (rows-of 0 10)
  (check "core-mv row" (find 'mock-mv rows :key #'first)))
(check "core-mv fault is still a fault"
       (handler-case (progn (fnn-core-mv 'mock-mv (error "boom")) nil)
         (fnn-fixed-callback-fault () t)))

;;; ---- DT-5.  A ring of capacity 7 under 100 calls: 7 recorded, 93 dropped.
(fnn-dtrace-stop)
(fnn-dtrace-start *table* :capacity 7)
(calls 'mock-word 100)
(multiple-value-bind (rows counters) (rows-of 0 100)
  (check "DT-5: seven rows kept" (= (length rows) 7))
  (destructuring-bind (attempts recorded dropped sampled live next) counters
    (declare (ignore next))
    (check "DT-5: seven recorded, ninety-three dropped"
           (and (= attempts 100) (= recorded 7) (= dropped 93) (= sampled 0) (= live 7)))
    (check "DT-5: attempts = recorded + dropped + sampled-out"
           (= attempts (+ recorded dropped sampled)))))

;;; ---- Sampling: every third.
(fnn-dtrace-stop)
(fnn-dtrace-start *table* :capacity 100 :sample-every 3)
(calls 'mock-word 100)
(multiple-value-bind (rows counters) (rows-of 0 200)
  (declare (ignore rows))
  (destructuring-bind (attempts recorded dropped sampled live next) counters
    (declare (ignore live next))
    (check "sampled every third" (and (= attempts 100) (= recorded 34) (= dropped 0) (= sampled 66)))))

;;; ---- Drain is an acknowledged cursor: a lost reply is repeated, not lost.
(fnn-dtrace-stop)
(fnn-dtrace-start *table* :capacity 4)
(calls 'mock-word 4)
(check "ring full" (equal (nth 1 (nth-value 1 (rows-of 0 10))) 4))
(calls 'mock-word 3)
(check "full ring dropped three" (= (third (nth-value 1 (rows-of 0 10))) 3))
(check "drain without ack repeats" (equal (mapcar #'fifth (rows-of 0 10)) '(1 2 3 4)))
(check "ack frees, rows after remain" (equal (mapcar #'fifth (rows-of 2 10)) '(3 4)))
(calls 'mock-word 2)
(check "freed slots take new rows" (equal (mapcar #'fifth (rows-of 2 10)) '(3 4 5 6)))
(check "limit bounds a drain" (equal (mapcar #'fifth (rows-of 4 1)) '(5)))

;;; ---- The rendering: JSON lines after the lock is free.
(let ((text (fnn-dtrace-drain 4 10)))
  (check "render has the version and type" (search "\"v\":2,\"type\":\"decision\"" text))
  (check "render has the summary" (search "\"type\":\"decision-summary\"" text))
  (write-string text))

;;; ---- A failing projection is counted and swallowed; the call is unharmed.
(fnn-dtrace-stop)
(fnn-dtrace-start *table* :capacity 8)
(let ((*project-fails* t))
  (check "a failing projection leaves the call alone"
         (equal (fnn-call 'mock-word 1) '(:busy (:state 1)))))
(destructuring-bind (attempts recorded dropped sampled live next) (nth-value 1 (rows-of 0 10))
  (declare (ignore live next))
  (check "a failing projection is a drop" (and (= attempts 1) (= recorded 0) (= dropped 1) (= sampled 0))))

;;; ---- Concurrent callers and a drainer: the identity holds in every snapshot.
(fnn-dtrace-stop)
(fnn-dtrace-start *table* :capacity 32)
(let* ((stop nil) (bad nil)
       (workers (loop repeat 4
                      collect (sb-thread:make-thread (lambda () (calls 'mock-word 2500)))))
       (drainer (sb-thread:make-thread
                 (lambda ()
                   (let ((since 0))
                     (loop until stop
                           do (multiple-value-bind (rows counters) (rows-of since 8)
                                (destructuring-bind (a r d s live next) counters
                                  (declare (ignore live next))
                                  (unless (= a (+ r d s)) (setf bad (list a r d s))))
                                (when rows (setf since (fifth (car (last rows)))))))
                     :done)))))
  (dolist (w workers) (sb-thread:join-thread w))
  (setf stop t)
  (sb-thread:join-thread drainer)
  (check (format nil "counters balance in every snapshot ~a" bad) (null bad))
  (destructuring-bind (a r d s live next) (nth-value 1 (rows-of 0 0))
    (declare (ignore live next))
    (check "ten thousand attempts, all accounted" (and (= a 10000) (= a (+ r d s))))))

(format t "NATIVE_DECISION_TRACE_PASS~%")
