; tools/cost-probe.lisp: what each host-called entry costs, and how much of
; that is its guards (lane cost-gate, 2026-10-03).
;
; Loaded into a DEVELOPER image's core BEFORE the node starts (tools/cost_gate.py
; puts `--load tools/cost-probe.lisp' ahead of the launcher's own
; `--eval (acl2::sbcl-restart)'), so it changes no host file and no saved
; image: the node that runs is the image's own, serving through its own
; dispatch, guard checking as fnn-main requires it (t).  It measures; it
; decides nothing.
;
; WHAT IS COUNTED.  Every call the raw host makes into ACL2 goes through
; `fnn-call' (host/native/io.lisp).  This file wraps it (sb-int:encapsulate,
; as FN_NATIVE_COUNT_LOOKUPS wraps its lookups) and keeps, per entry name:
;
;   calls, ns, bytes     the whole call: the entry guard, the executable
;                        counterpart's own guard, the body.  Outermost only: an
;                        fnn-call made while another is running on the same
;                        thread is charged to the outer one.
;   gcalls, gns, gbytes  the part spent in GUARD PREDICATES: every tree
;                        function (FN-...) that occurs in the guard of any
;                        function of the image's world is wrapped, both its
;                        raw definition and its executable counterpart, and
;                        the outermost such call inside an entry is timed.
;
; SCOPE OF THE GUARD COLUMN, stated once: a guard predicate is timed wherever
; it is called inside the entry, so a body that itself calls fn-sn-statep is
; charged as a guard is (it is the same walk, and the same served cost).  A
; guard conjunct that is not a tree function (natp, a comparison) is not
; timed: it is in `ns' but not in `gns'.  The wrappers cost about 0.1
; microsecond per predicate call, which is inside `ns' too: `ns' with the
; predicates wrapped is an UPPER bound of the unprobed call.  FN_COST_PROBE_GUARDS=0
; leaves the predicates unwrapped (then gns is 0 and ns is the plain call).
;
; Per (entry, predicate): calls, ns, bytes (inclusive) and top (the calls that
; were the outermost guard predicate), so the table names what carries the cost.
;
; Bytes are SBCL's `get-bytes-consed', which is per process and advances a
; region at a time: one call's delta is a lower bound and another thread's
; allocation lands in it.  The driver measures serially and reports loop
; averages (bytes / calls over many calls), never one call.
;
; THE REQUEST HOOK.  A thread of this file's own polls FN_COST_PROBE for
; request.lisp (20 times a second; never a signal: SBCL stops the world for a
; collection with SIGUSR2 and a handler there breaks the collector), loads it
; with its output in reply.txt.tmp, removes it and renames the reply to
; reply.txt.  The driver's requests are (cp-dump PATH), (cp-reset) and
; whatever a developer wants evaluated in the live node (the fixture's state
; is this process's).  The developer's own forms only, as `fn acl2 session'
; reads; a form that reads the owner's state takes the owner's lock itself.

(in-package "ACL2")

(defvar *cp-dir* (sb-ext:posix-getenv "FN_COST_PROBE"))
(defvar *cp-guards-p* (not (equal (sb-ext:posix-getenv "FN_COST_PROBE_GUARDS") "0")))
(defvar *cp-lock* (sb-thread:make-mutex :name "cost-probe"))
(defvar *cp-rows* (make-hash-table :test 'eq)
  "entry name -> #(calls ns bytes gcalls gns gbytes max-ns), under *cp-lock*")
(defvar *cp-preds* (make-hash-table :test 'equal)
  "(entry predicate . parent) -> #(calls ns bytes top), under *cp-lock*")
(defvar *cp-entry* nil "the entry this thread is inside, or NIL")
(defvar *cp-in-guard* nil "T while this thread is inside a timed predicate")
(defvar *cp-gacc* nil "this thread's (gcalls gns gbytes) of the entry it is inside")
(defvar *cp-wrapped* 0)
(defvar *cp-active* nil "the predicates this thread is inside, innermost first")

(declaim (inline cp-now))
(defun cp-now ()
  (multiple-value-bind (s ns) (sb-unix:clock-gettime sb-unix:clock-monotonic)
    (+ (* s 1000000000) ns)))

(defun cp-serve-request ()
  (let* ((dir (concatenate 'string *cp-dir* "/"))
         (request (concatenate 'string dir "request.lisp"))
         (tmp (concatenate 'string dir "reply.txt.tmp")))
    (with-open-file (out tmp :direction :output :if-exists :supersede)
      (let ((*standard-output* out) (*package* (find-package "ACL2")))
        (handler-case
            (progn (load request)
                   (format out "~&CP-REQUEST-OK~%"))
          (serious-condition (c) (format out "~&CP-REQUEST-FAILED ~a~%" c)))))
    (delete-file request)
    (rename-file tmp (concatenate 'string dir "reply.txt"))))

(defun cp-request-loop ()
  (let ((request (concatenate 'string *cp-dir* "/request.lisp")))
    (loop
      (when (probe-file request) (cp-serve-request))
      (sleep 0.05))))

(defstruct (cp-acc (:constructor cp-make-acc ()))
  ;; one entry call's guard account, private to its thread
  (calls 0 :type fixnum) (ns 0 :type fixnum) (bytes 0 :type fixnum)
  (hits 0 :type fixnum)   ; every predicate-wrapper invocation, timed or not
  (preds nil :type list)) ; ((pred . #(calls ns bytes)) ...), a few per entry

(defun cp-entry-wrapper (next name &rest args)
  (cond
    (*cp-entry* (apply next name args))
    (t
     (let* ((acc (cp-make-acc))
            (b0 (sb-ext:get-bytes-consed))
            (t0 (cp-now)))
       (unwind-protect
            (let ((*cp-entry* name) (*cp-gacc* acc) (*cp-in-guard* nil) (*cp-active* nil))
              (apply next name args))
         (let ((dt (- (cp-now) t0))
               (db (- (sb-ext:get-bytes-consed) b0)))
           (sb-thread:with-mutex (*cp-lock*)
             (let ((row (or (gethash name *cp-rows*)
                            (setf (gethash name *cp-rows*)
                                  (make-array 8 :initial-element 0)))))
               (incf (svref row 0))
               (incf (svref row 1) dt)
               (incf (svref row 2) db)
               (incf (svref row 3) (cp-acc-calls acc))
               (incf (svref row 4) (cp-acc-ns acc))
               (incf (svref row 5) (cp-acc-bytes acc))
               (when (> dt (svref row 6)) (setf (svref row 6) dt))
               (incf (svref row 7) (cp-acc-hits acc)))
             (dolist (pair (cp-acc-preds acc))
               (let* ((key (cons name (car pair)))
                      (row (or (gethash key *cp-preds*)
                               (setf (gethash key *cp-preds*)
                                     (make-array 4 :initial-element 0)))))
                 (dotimes (i 4) (incf (svref row i) (svref (cdr pair) i))))))))))))

(defun cp-pred-wrapper (pred)
  ;; Each predicate is timed INCLUSIVELY at its outermost activation inside
  ;; an entry (a self-recursive walk once, not per step), so a row names
  ;; every predicate on the path, nested ones included (fn-sn-statep's row
  ;; contains its conjuncts' rows).  The entry's guard total (gcalls gns
  ;; gbytes) adds only the outermost predicate of each nest, so it never
  ;; counts a nanosecond twice.
  (lambda (next &rest args)
    (when *cp-gacc* (incf (cp-acc-hits *cp-gacc*)))
    (if (or (null *cp-gacc*) (member pred *cp-active* :test #'eq))
        (apply next args)
      (let ((top (not *cp-in-guard*))
            (b0 (sb-ext:get-bytes-consed))
            (t0 (cp-now)))
        (unwind-protect
             (let ((*cp-in-guard* t) (*cp-active* (cons pred *cp-active*)))
               (apply next args))
          (let* ((dt (- (cp-now) t0))
                 (db (- (sb-ext:get-bytes-consed) b0))
                 (acc *cp-gacc*)
                 (key (cons pred (car *cp-active*)))
                 (pair (or (assoc key (cp-acc-preds acc) :test #'equal)
                           (car (push (cons key (make-array 4 :initial-element 0))
                                      (cp-acc-preds acc)))))
                 (row (cdr pair)))
            (when top
              (incf (cp-acc-calls acc))
              (incf (cp-acc-ns acc) dt)
              (incf (cp-acc-bytes acc) db)
              (incf (svref row 3)))
            (incf (svref row 0))
            (incf (svref row 1) dt)
            (incf (svref row 2) db)))))))

(defun cp-guard-predicates ()
  "Every FN- function symbol occurring in a guard of the image's world."
  (let ((seen (make-hash-table :test 'eq)) (done (make-hash-table :test 'eq)))
    (do ((w (w *the-live-state*) (cdr w))) ((endp w))
      (let ((triple (car w)))
        (when (and (eq (cadr triple) 'guard) (not (gethash (car triple) done)))
          ;; the first triple for a symbol is its current value
          (setf (gethash (car triple) done) t)
          (let ((term (cddr triple)))
            (when (consp term)
              (dolist (f (all-fnnames term))
                (when (and (symbolp f)
                           (> (length (symbol-name f)) 3)
                           (string= "FN-" (symbol-name f) :end2 3))
                  (setf (gethash f seen) t))))))))
    (let ((out nil))
      (maphash (lambda (k v) (declare (ignore v)) (push k out)) seen)
      out)))

(defun cp-wrap (symbol wrapper)
  (when (and symbol (fboundp symbol) (not (macro-function symbol))
             (not (sb-int:encapsulated-p symbol 'cost-probe)))
    (sb-int:encapsulate symbol 'cost-probe wrapper)
    (incf *cp-wrapped*)))

(defun cp-install ()
  (cp-wrap 'fnn-call #'cp-entry-wrapper)
  (when *cp-guards-p*
    (dolist (pred (cp-guard-predicates))
      (let ((wrapper (cp-pred-wrapper pred)))
        (cp-wrap pred wrapper)
        (cp-wrap (find-symbol (symbol-name pred) "ACL2_*1*_ACL2") wrapper))))
  (when *cp-dir*
    (sb-thread:make-thread #'cp-request-loop :name "cost-probe-requests"))
  (format *error-output* "~&cost-probe: ~d functions wrapped (guards ~a), requests in ~a~%"
          *cp-wrapped* (if *cp-guards-p* "on" "off") *cp-dir*)
  (finish-output *error-output*))

(defun cp-reset ()
  (sb-thread:with-mutex (*cp-lock*)
    (clrhash *cp-rows*)
    (clrhash *cp-preds*))
  (format t "~&CP-RESET~%"))

(defvar *cp-wrapper-ns* 0.0d0
  "the calibrated cost of one TIMED predicate activation (the outermost of
its predicate inside an entry), ns")
(defvar *cp-skip-ns* 0.0d0
  "the calibrated cost of one untimed wrapper pass (the predicate already
active: a recursive step), ns")

(declaim (notinline cp-calibrate-target))
(defun cp-calibrate-target (x) x)

(defun cp-calibrate ()
  "Time 100,000 calls of a function wrapped as the predicates are, inside a
pretend entry, against the same loop unwrapped, once timed (each call
outermost) and once skipped (the predicate already active): the two
per-call differences are what the table subtracts."
  (let ((n 100000))
    (flet ((loop-ns ()
             (let ((t0 (cp-now)))
               (dotimes (i n) (cp-calibrate-target i))
               (- (cp-now) t0))))
      (let ((bare (min (loop-ns) (loop-ns))) (timed 0) (skipped 0))
        (sb-int:encapsulate 'cp-calibrate-target 'cost-probe
                            (cp-pred-wrapper 'cp-calibrate-target))
        (unwind-protect
             (let ((*cp-entry* :calibrate) (*cp-gacc* (cp-make-acc))
                   (*cp-in-guard* nil) (*cp-active* nil))
               (setq timed (min (loop-ns) (loop-ns)))
               (let ((*cp-active* (list 'cp-calibrate-target)))
                 (setq skipped (min (loop-ns) (loop-ns)))))
          (sb-int:unencapsulate 'cp-calibrate-target 'cost-probe))
        (setq *cp-wrapper-ns* (/ (max 0 (- timed bare)) (float n 1d0))
              *cp-skip-ns* (/ (max 0 (- skipped bare)) (float n 1d0)))
        (format t "~&CP-CALIBRATE timed_ns=~,1f skip_ns=~,1f~%" *cp-wrapper-ns* *cp-skip-ns*)))))

(defun cp-set-guard-checking (value)
  "The fixture's build runs with NIL, every measured window with T (see
tools/cost_gate.py THE FIXTURE).  The owner reads the global at each call."
  (f-put-global 'guard-checking-on value *the-live-state*)
  (format t "~&CP-GUARD-CHECKING ~a~%" value))

(defvar *cp-elided* nil)

(defun cp-elide (preds)
  "FIXTURE BUILD ONLY (tools/cost_gate.py THE FIXTURE): answer T for each
whole-state predicate in PREDS, raw and executable counterpart, without
walking.  Every one is an invariant the entries preserve (its preservation
theorems), so on the reachable states the build visits its value IS T and no
computed value changes; the build's end evaluates the real predicates
(cp-fixture-report, after cp-unelide) and a false one fails the run.  No
measured window ever runs with a predicate elided."
  (dolist (pred preds)
    (dolist (sym (list pred (find-symbol (symbol-name pred) "ACL2_*1*_ACL2")))
      (when (and sym (fboundp sym) (not (sb-int:encapsulated-p sym 'cost-probe-elide)))
        (sb-int:encapsulate sym 'cost-probe-elide
                            (lambda (next &rest args) (declare (ignore next args)) t))
        (push sym *cp-elided*))))
  (format t "~&CP-ELIDE~{ ~(~a~)~}~%" *cp-elided*))

(defun cp-unelide ()
  (dolist (sym *cp-elided*)
    (sb-int:unencapsulate sym 'cost-probe-elide))
  (setq *cp-elided* nil)
  (format t "~&CP-UNELIDE~%"))

(defun cp-fixture-report ()
  "The fixture's invariant, asserted in the live node, and its dimensions."
  (let* ((state *the-live-state*)
         (*cp-entry* :report)
         (oc (fn-owner-ocfg state))
         (store (fn-sbud-oc-store oc))
         (files (fn-sn-files store))
         (node (fn-sn-node store))
         (acc (fn-node-acceptance node))
         (ret (fn-node-retention node)))
    (format t "~&FIXTURE sn_statep=~a retain_statep=~a records=~d successes=~d articles=~d ~
pins=~d releases=~d bindings=~d groups=~d phase=~(~a~)~%"
            (if (fn-sn-statep store) "T" "NIL")
            (if (fn-owner-retain-statep state) "T" "NIL")
            (len (fn-sf-records files)) (len (fn-sf-successes files))
            (len (fn-state-articles acc))
            (len (fn-retain-pins ret)) (len (fn-retain-releases ret))
            (len (fn-node-bindings node)) (len (fn-sn-groups store))
            (fn-sf-phase files))))

(defun cp-dump (path)
  "One line per entry and per (entry, predicate); the driver parses them."
  (with-open-file (out path :direction :output :if-exists :supersede)
    (format out "C wrapper_ns ~,2f~%C skip_ns ~,2f~%" *cp-wrapper-ns* *cp-skip-ns*)
    (sb-thread:with-mutex (*cp-lock*)
      (maphash (lambda (name row)
                 (format out "E ~(~a~)~{ ~d~}~%" name (coerce row 'list)))
               *cp-rows*)
      (maphash (lambda (key row)
                 ;; key = (entry pred . parent); parent is the innermost
                 ;; predicate around this activation, or - at the top
                 (format out "P ~(~a~) ~(~a~) ~(~a~)~{ ~d~}~%" (car key) (cadr key)
                         (or (cddr key) "-") (coerce row 'list)))
               *cp-preds*)))
  (format t "~&CP-DUMP ~a~%" path))

(cp-install)
