; E2 raw evidence adapter. Algorithms/endpoints are loaded unchanged from E1.
; This file is orchestration, never a proof book or a semantic implementation.
(in-package "ACL2")
(load "fn2/experiments/squares/runner.lsp")
(load "fn2/experiments/squares/fixtures.lsp")

(defvar *sq-q1-g1-original* nil)
(defvar *sq-q1-scope* nil)
(defvar *sq-q1-outside-catalogue* nil)
(defvar *sq-q1-tooth-cases* nil)
(defvar *sq-q1-campaign-results* nil)

(defun sq-q1-copy-core (core referencep)
  (fn2-ref-copy-core
   core (fn2-core-init *e1-profile*
         (if referencep (create-fn2-ref-core) (create-fn2-core)))))
(defun sq-q1-fresh-sample (sample)
  (list (first sample) (second sample) (third sample) (copy-tree (fourth sample))
        (sq-q1-copy-core (fifth sample) nil)
        (sq-q1-copy-core (sixth sample) t)))

; Each reached row gets repeatable, named checking fixtures. Snapshots precede
; the real transition; every evaluation starts fresh mutable cores. Negative
; removes exactly the entry work relation, by changing one reference counter.
; These are G1-checker teeth, not proofs of the full loop invariant statement.
(defun sq-q1-install-teeth (row sample original)
  (let* ((case (getf row :case)) (names (getf row :teeth))
         (positive (getf names :positive)) (negative (getf names :negative)))
    (unless (member case *sq-q1-tooth-cases* :test #'equal)
      (let ((saved (sq-q1-fresh-sample sample)))
        (setf (symbol-function positive)
          (lambda ()
            (let ((fresh (sq-q1-fresh-sample saved)))
              (and (equal case (fn2-e1-label (fourth fresh) (fifth fresh)))
                   (null (nth-value 0 (apply original fresh)))))))
        (setf (symbol-function negative)
          (lambda ()
            (let* ((fresh (sq-q1-fresh-sample saved)) (ref (sixth fresh)))
              (setf (sixth fresh)
                (fn2-exec-set-turn-steps (1+ (fn2-exec-turn-steps ref)) ref))
              (not (null (nth-value 0 (apply original fresh))))))))
      (push case *sq-q1-tooth-cases*))))

; Generic sq-check-row invokes this, and this invokes the actual E1 G1 checker.
; Result values are returned to E1 without a second transition or replay.
(defun sq-q1-check-sample (row sample)
  (let* ((case (fn2-e1-label (fourth sample) (fifth sample)))
         (matches (equal case (getf row :case))))
    (unless matches
      (error "Q1 row routing mismatch: actual ~S row ~S" case (getf row :case)))
    (sq-q1-install-teeth row sample *sq-q1-g1-original*)
    (let ((outcome (catch 'e1-stop
                     (list :returned (multiple-value-list
                                      (apply *sq-q1-g1-original* sample))))))
      (if (eq (first outcome) :returned)
          (let ((values (second outcome)))
            (list :reached 1 :exercised 1
                  :verdict (if (first values) :fail :pass)
                  :error (first values) :values values))
        (list :reached 1 :exercised 0 :verdict :unexercised
              :interrupted outcome)))))

(defun sq-q1-install-attribution ()
  (e1-wrap 'fn2-e1-g1-step
    (lambda (original)
      (lambda (&rest sample)
        (let* ((case (fn2-e1-label (fourth sample) (fifth sample)))
               (row (sq-row-for-case 'sq-q1 case))
               (*sq-q1-g1-original* original))
          (if row
              (let ((answer (sq-check-row row sample *sq-q1-scope*)))
                (when (getf answer :interrupted)
                  (throw 'e1-stop (getf answer :interrupted)))
                (unless (getf answer :values)
                  (error "Q1 adapter did not return transition values: ~S" answer))
                (values-list (getf answer :values)))
            (let ((record (list :case case :scope *sq-q1-scope*
                                :reached 1 :exercised 0)))
              (push record *sq-q1-outside-catalogue*)
              (multiple-value-prog1 (apply original sample)
                (setf (getf record :exercised) 1)))))))))

; Account for incomplete final calls and any labels outside the catalogue.
(defun sq-q1-attribution-counts (scope)
  (let ((reached 0) (exercised 0) (outside-reached 0) (outside-exercised 0))
    (dolist (entry *sq-runtime-rows*)
      (let* ((row (cdr entry))
             (record (find (sq-scope-record row scope) (getf row :checks)
                           :test #'sq-same-scope-p)))
        (when (and (equal (getf row :owner) '(:correspondence sq-q1)) record)
          (incf reached (getf record :reached))
          (incf exercised (getf record :exercised)))))
    (dolist (record *sq-q1-outside-catalogue*)
      (when (equal scope (getf record :scope))
        (incf outside-reached (getf record :reached))
        (incf outside-exercised (getf record :exercised))))
    (list :reached reached :exercised exercised :outside-reached outside-reached
          :outside-exercised outside-exercised)))

(defun sq-q1-restore-hooks ()
  (dolist (entry *e1-hooks*) (setf (symbol-function (car entry)) (cdr entry)))
  (setf *e1-hooks* nil))

; Only the evidence budget changes: E1's random walk (128 choices/trial) and
; depth-first enumeration (horizon 4) retain their original implementations,
; fault/word domain, G2 contract, client oracle, allocator and latency monitors.
(defun sq-q1-run-one-campaign (config descriptor revision)
  (let* ((start (e1-seconds))
         (*e1-stat* nil) (*e1-label-counts* nil) (*e1-trials* 0)
         (*e1-g1-enabled* t) (*e1-baseline-seed* nil)
         (*e1-cap* (getf descriptor :transition-budget))
         (*e1-deadline* (+ start (getf descriptor :wall-seconds)))
         (seed (getf descriptor :seed)) (depth (getf descriptor :enumeration-depth))
         (*e1-boundary* 0) (*e1-schedule* nil) (*e1-draws* nil)
         (*e1-byte-history* nil) (*e1-close-history* nil)
         (*sq-q1-scope*
           (list :revision revision :profile *e1-profile*
                 :domain (list :mutant :original :campaign config :seed seed
                               :faults *fn2-e1-faults* :words *fn2-e1-words*
                               :random-trial-choices 128 :enumeration-depth depth
                               :checked-projection 'fn2-e1-g1-step)
                 :horizon *e1-cap* :unit :transitions
                 :location "fn2/experiments/squares/e2/q1-campaign-evidence.sexp"))
         (answer
           (progn
             (sq-begin-scope 'sq-q1 *sq-q1-scope*)
             (catch 'e1-stop
               (if (eq config :random)
                   (e1-random-campaign seed :different-capability-and-allocator-disjoint)
                 (progn
                   (e1-enumerate nil depth :different-capability-and-allocator-disjoint)
                   '(:completed :domain-exhausted))))))
         (attribution (sq-q1-attribution-counts *sq-q1-scope*))
         (result (list :config config :scope *sq-q1-scope* :result answer
                       :attribution attribution :seconds (- (e1-seconds) start) :trials *e1-trials*
                       :counters *e1-stat* :labels *e1-label-counts*)))
    (assert (= (reduce #'+ *e1-label-counts* :key #'cdr :initial-value 0)
               (+ (getf attribution :reached) (getf attribution :outside-reached))))
    (assert (= (getf *e1-stat* :g1 0)
               (+ (getf attribution :exercised) (getf attribution :outside-exercised))))
    (format t "E2 Q1 ATTRIBUTION ~S ~S~%" config attribution)
    (format t "E2 Q1 ORIGINAL ~S result=~S trials=~D transitions=~D G1=~D labels=~D seconds=~,6F~%"
            config answer *e1-trials* (e1-total) (getf *e1-stat* :g1 0)
            (length *e1-label-counts*) (getf result :seconds))
    result))

(defun sq-q1-run-campaigns (descriptor revision)
  (setf *sq-q1-outside-catalogue* nil *sq-q1-campaign-results* nil)
  (unwind-protect
      (progn
        (e1-install)
        (sq-q1-install-attribution)
        (dolist (config (getf descriptor :campaigns))
          (push (sq-q1-run-one-campaign config descriptor revision) *sq-q1-campaign-results*))
        (setf *sq-q1-campaign-results* (nreverse *sq-q1-campaign-results*))
        (e1-save "fn2/experiments/squares/e2/q1-campaign-evidence.sexp"
                 (list :campaigns *sq-q1-campaign-results*
                       :outside-catalogue *sq-q1-outside-catalogue*))
        (format t "E2 Q1 outside-catalogue=~D named-G1-teeth=~D~%"
                (length *sq-q1-outside-catalogue*) (length *sq-q1-tooth-cases*))
        *sq-q1-campaign-results*)
    (sq-q1-restore-hooks)))
