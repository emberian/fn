; Raw Common Lisp acceptance instrumentation, loaded after ACL2's :q and LD,
; as own-read-hook.lsp is. While installed, every scenario turn's TRACE check
; is the certified per-case TRACE (fn2-check-trace-cases-turn, the same turn
; stepped transition by transition with the G1 square of each Q1 case
; checked); this file only sums its per-turn tallies and, after the driver's
; scenarios passed, writes them as the run's Q1 evidence data. A failing case
; is a failing TRACE verdict, so the scenario that met it fails first.
; Not installed around the turn meter: the meter measures fn2-turn itself.
(in-package "ACL2")
(defvar *fn2-q1-hook-original* nil)
(defvar *fn2-q1-cases* nil)
(defvar *fn2-q1-certified* nil)
(defvar *fn2-q1-turns* 0)

(defun fn2-q1-hook-merge (from into)
  (dolist (entry from into)
    (let ((old (assoc (car entry) into :test #'equal)))
      (if old (incf (cdr old) (cdr entry))
        (setf into (append into (list (cons (car entry) (cdr entry)))))))))
(defun fn2-q1-hook-install ()
  (assert (null *fn2-q1-hook-original*))
  (setf *fn2-q1-hook-original* (symbol-function 'fn2-check-trace-turn)
        *fn2-q1-cases* nil *fn2-q1-certified* nil *fn2-q1-turns* 0)
  (setf (symbol-function 'fn2-check-trace-turn)
        (lambda (profile cursor queues core reference)
          (multiple-value-bind (verdict status obs visits actions cursor queues tallies core reference)
              (fn2-check-trace-cases-turn profile cursor queues core reference)
            (incf *fn2-q1-turns*)
            (setf *fn2-q1-cases* (fn2-q1-hook-merge (car tallies) *fn2-q1-cases*)
                  *fn2-q1-certified* (fn2-q1-hook-merge (cdr tallies) *fn2-q1-certified*))
            (values verdict status obs visits actions cursor queues core reference)))))
;
; For a driver that keeps no reference (D's sim-layer-d, through
; sim-layer-d-evidence.lsp): A4's three instruments around its own fn2-turn.
; Every fn2-init-executor (one per run) also resets the hook's reference
; core from the initialised concrete one (fn2-ref-reset) and reads the
; reference cursor and FIFOs from its scheduler; every fn2-own-init records
; that run's OWN monitor. Every fn2-turn then becomes, as in the A4
; scenarios: the per-case TRACE turn (fn2-check-trace-cases-turn) with the
; reference carried from the previous turn (cursor and FIFOs too), the trace
; child enabled and cleared for it and its flag restored after; the
; own-read hook observing the core's reads and writes during it; then
; fn2-own-observe-issue for every operation the turn queued and
; fn2-check-own. A failing TRACE or OWN verdict is recorded with its turn
; and makes fn2-q1-hook-write fail. Load own-read-hook.lsp first.
(defvar *fn2-q1-hook-turn* nil)
(defvar *fn2-q1-hook-init* nil)
(defvar *fn2-q1-hook-own-init* nil)
; Host calls outside the arms that change a core between turns (fn2-recovery-start: the
; host starts recovery on a fresh core, as fn2-scribe-start inside fn2-init-executor):
; the reference is re-read from the concrete core after each, as after init.
(defvar *fn2-q1-hook-host-calls* nil)
(defvar *fn2-q1-hook-ref* nil)
(defvar *fn2-q1-hook-profile* :none)
(defvar *fn2-q1-hook-cursor* 0)
(defvar *fn2-q1-hook-queues* nil)
(defvar *fn2-q1-hook-monitor* nil)
(defvar *fn2-q1-hook-failures* nil)
(defvar *fn2-q1-hook-own-checks* 0)
(defun fn2-q1-hook-observe-issues (left offset core own)
  (loop for k from offset below (+ offset left)
        do (multiple-value-bind (code slot gen) (fn2-outbox-peek k (fn2-core-ops core))
             (declare (ignore gen))
             (when (eq code :ok) (fn2-own-observe-issue slot core own)))))
(defun fn2-q1-hook-install-turn ()
  (assert (and (null *fn2-q1-hook-original*) (null *fn2-q1-hook-turn*)
               (null *fn2-q1-hook-init*) (null *fn2-q1-hook-own-init*)))
  (setf *fn2-q1-hook-turn* (symbol-function 'fn2-turn)
        *fn2-q1-hook-init* (symbol-function 'fn2-init-executor)
        *fn2-q1-hook-own-init* (symbol-function 'fn2-own-init)
        *fn2-q1-hook-ref* (create-fn2-ref-core) *fn2-q1-hook-profile* :none
        *fn2-q1-hook-monitor* nil *fn2-q1-hook-own-checks* 0
        *fn2-q1-cases* nil *fn2-q1-certified* nil *fn2-q1-turns* 0 *fn2-q1-hook-failures* nil)
  (dolist (name '(fn2-recovery-start))
    (when (fboundp name)
      (let ((original (symbol-function name)))
        (push (cons name original) *fn2-q1-hook-host-calls*)
        (setf (symbol-function name)
              (lambda (&rest args)
                (let* ((results (multiple-value-list (apply original args)))
                       (core (car (last results)))
                       (lists (fn2-ref-lists-of-core (fn2-profile-weights *fn2-q1-hook-profile*) core)))
                  (setf *fn2-q1-hook-ref* (fn2-ref-reset *fn2-q1-hook-profile* core *fn2-q1-hook-ref*)
                        *fn2-q1-hook-cursor* (nth 1 lists) *fn2-q1-hook-queues* (nth 2 lists))
                  (values-list results)))))))
  (let ((init *fn2-q1-hook-init*) (own-init *fn2-q1-hook-own-init*))
    (setf (symbol-function 'fn2-init-executor)
          (lambda (profile mode scribe-p core)
            (let* ((core (funcall init profile mode scribe-p core))
                   (lists (fn2-ref-lists-of-core (fn2-profile-weights profile) core)))
              (setf *fn2-q1-hook-ref* (fn2-ref-reset profile core *fn2-q1-hook-ref*)
                    *fn2-q1-hook-profile* profile
                    *fn2-q1-hook-cursor* (nth 1 lists) *fn2-q1-hook-queues* (nth 2 lists))
              core))
          (symbol-function 'fn2-own-init)
          (lambda (profile own)
            (let ((own (funcall own-init profile own)))
              (setf *fn2-q1-hook-monitor* own)
              own))))
  (setf (symbol-function 'fn2-turn)
        (lambda (core)
          (assert (not (eq *fn2-q1-hook-profile* :none)))
          (let ((enabled (fn2-check-trace-enabled core))
                (queued (fn2-outbox-queued (fn2-core-ops core)))
                (monitor *fn2-q1-hook-monitor*))
            (setf core (fn2-check-trace-set-trace 1 core))
            (multiple-value-bind (verdict status obs visits actions cursor queues tallies core reference)
                (let ((*fn2-own-hook-core* (and monitor core)) (*fn2-own-hook-monitor* monitor))
                  (fn2-check-trace-cases-turn *fn2-q1-hook-profile* *fn2-q1-hook-cursor*
                                              *fn2-q1-hook-queues* core *fn2-q1-hook-ref*))
              (setf core (fn2-check-trace-set-trace enabled core)
                    *fn2-q1-hook-ref* reference *fn2-q1-hook-cursor* cursor *fn2-q1-hook-queues* queues)
              (incf *fn2-q1-turns*)
              (unless (eq verdict :pass) (push (list *fn2-q1-turns* :trace verdict) *fn2-q1-hook-failures*))
              (when monitor
                (fn2-q1-hook-observe-issues actions queued core monitor)
                (let ((own (fn2-check-own core monitor)))
                  (incf *fn2-q1-hook-own-checks*)
                  (unless (eq own :pass) (push (list *fn2-q1-turns* :own own) *fn2-q1-hook-failures*))))
              (setf *fn2-q1-cases* (fn2-q1-hook-merge (car tallies) *fn2-q1-cases*)
                    *fn2-q1-certified* (fn2-q1-hook-merge (cdr tallies) *fn2-q1-certified*))
              (values status obs visits actions core))))))
(defun fn2-q1-hook-restore ()
  (when *fn2-q1-hook-original*
    (setf (symbol-function 'fn2-check-trace-turn) *fn2-q1-hook-original*
          *fn2-q1-hook-original* nil))
  (when *fn2-q1-hook-turn*
    (setf (symbol-function 'fn2-turn) *fn2-q1-hook-turn* *fn2-q1-hook-turn* nil))
  (when *fn2-q1-hook-init*
    (setf (symbol-function 'fn2-init-executor) *fn2-q1-hook-init* *fn2-q1-hook-init* nil))
  (when *fn2-q1-hook-own-init*
    (setf (symbol-function 'fn2-own-init) *fn2-q1-hook-own-init* *fn2-q1-hook-own-init* nil))
  (dolist (entry *fn2-q1-hook-host-calls*)
    (setf (symbol-function (car entry)) (cdr entry)))
  (setf *fn2-q1-hook-host-calls* nil))

; PATH is a book under fn2/tests/evidence/ (outside the tests digest of
; scenario-revision.py). LOCATION names the driver, DOMAIN its segments,
; PREFIX the constants' infix (*fn2-q1-PREFIX-run* and so on).
(defun fn2-q1-hook-write (path location domain profiles &optional (prefix "a4"))
  (let* ((transitions (loop for e in *fn2-q1-cases* sum (cdr e)))
         (catalogue *fn2-q1-catalogue*)
         (exercised (loop for c in catalogue when (assoc c *fn2-q1-cases* :test #'equal) collect c))
         (outside (loop for e in *fn2-q1-cases*
                        unless (member (car e) catalogue :test #'equal) collect e)))
    (assert (plusp *fn2-q1-turns*))
    (when *fn2-q1-hook-failures*
      (format t "Q1 HOOK FAILURES (turn instrument verdict), first 5: ~S~%"
              (subseq (reverse *fn2-q1-hook-failures*) 0 (min 5 (length *fn2-q1-hook-failures*))))
      (error "~D instrumented turns failed" (length *fn2-q1-hook-failures*)))
    (ensure-directories-exist path)
    (with-open-file (out path :direction :output :if-exists :supersede)
      (with-standard-io-syntax
        (let ((*package* (find-package "ACL2")) (*print-case* :downcase) (*print-pretty* nil))
          (format out "; Generated by fn2/tests/q1-case-hook.lsp from ~A. Do not edit.~%" location)
          (format out "(in-package \"ACL2\")~%")
          (format out "(defconst *fn2-q1-~A-run*~% '~S)~%" prefix
                  (list :revision *fn2-scenario-revision* :profile profiles :domain domain
                        :turns *fn2-q1-turns* :transitions transitions :location location))
          (format out "(defconst *fn2-q1-~A-cases*~% '(~{~S~^~%   ~}))~%" prefix *fn2-q1-cases*)
          (format out "(defconst *fn2-q1-~A-certified*~% '(~{~S~^~%   ~}))~%" prefix *fn2-q1-certified*))))
    (format t "Q1 CASES turns=~D transitions=~D exercised=~D/~D outside-catalogue=~S~%"
            *fn2-q1-turns* transitions (length exercised) (length catalogue) outside)
    (format t "Q1 UNEXERCISED ~S~%"
            (loop for c in catalogue unless (member c exercised :test #'equal) collect c))))
