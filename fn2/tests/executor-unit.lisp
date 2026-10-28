; Executor controls and whole-state refinement witnesses. All allocations in
; this book are test-only snapshots, never part of fn2-turn.
(in-package "ACL2")
(include-book "reference-unit")

; Snapshot the declaration, not a hand-maintained subset of its readers.
; Array lists retain physical index order and include unused capacity. The
; resulting list is exactly the logical defstobj layout, including extras.
(defun fn2-executor-test-array-events (name fields)
  (declare (xargs :verify-guards nil))
  (if (atom fields) nil
    (let* ((field (caar fields))
           (reader (fn2-columns-sym field "I"))
           (snapshot (fn2-columns-sym field "-TEST-COPY")))
      (append
       (if (fn2-columns-arrayp (car fields))
           `((defun ,snapshot (left offset ,name)
               (declare (xargs :stobjs ,name :verify-guards nil :measure (nfix left)))
               (if (zp left) nil
                 (cons (,reader offset ,name)
                       (,snapshot (- left 1) (+ 1 (nfix offset)) ,name))))
             (in-theory (disable ,snapshot))) nil)
       (fn2-executor-test-array-events name (cdr fields))))))
(defun fn2-executor-test-field-calls (name fields)
  (declare (xargs :verify-guards nil))
  (if (atom fields) nil
    (cons (if (fn2-columns-arrayp (car fields))
              `(,(fn2-columns-sym (caar fields) "-TEST-COPY")
                (,(fn2-columns-sym (caar fields) "-LENGTH") ,name) 0 ,name)
            `(,(caar fields) ,name))
          (fn2-executor-test-field-calls name (cdr fields)))))
(defun fn2-executor-test-snapshot-events (names registry)
  (declare (xargs :verify-guards nil))
  (if (atom names) nil
    (let* ((name (car names))
           (schema (cdr (assoc-eq name registry)))
           (columns (cadr (member-eq :columns schema)))
           (extras (cadr (member-eq :extra-fields schema)))
           (fields (append (fn2-columns-fields name columns)
                           `((,(fn2-columns-sym name "-ROWS") :type (unsigned-byte 32)))
                           extras))
           (snapshot (fn2-columns-sym name "-TEST-LOGICAL-SNAPSHOT")))
      (append (fn2-executor-test-array-events name fields)
              `((defun ,snapshot (,name)
                  (declare (xargs :stobjs ,name :verify-guards nil))
                  (list ,@(fn2-executor-test-field-calls name fields)))
                (in-theory (disable ,snapshot)))
              (fn2-executor-test-snapshot-events (cdr names) registry)))))
(assert-event
 (equal (fn2-executor-test-field-calls 'scratch
          '((octets :type (array (unsigned-byte 8) (0)))
            (count :type (unsigned-byte 32))))
        '((octets-test-copy (octets-length scratch) 0 scratch)
          (count scratch))))
(assert-event
 (equal (fn2-executor-test-array-events 'scratch
          '((octets :type (array (unsigned-byte 8) (0)))))
        '((defun octets-test-copy (left offset scratch)
            (declare (xargs :stobjs scratch :verify-guards nil :measure (nfix left)))
            (if (zp left) nil
              (cons (octetsi offset scratch)
                    (octets-test-copy (- left 1) (+ 1 (nfix offset)) scratch))))
          (in-theory (disable octets-test-copy)))))
(make-event
 (value (cons 'progn
   (fn2-executor-test-snapshot-events
    (strip-cars (strip-cdrs *fn2-core-children*))
    (table-alist 'fn2-columns (w state))))))

(defun fn2-executor-test-snapshot-calls (children)
  (if (atom children) nil
    (cons `(,(fn2-columns-sym (cadar children) "-TEST-LOGICAL-SNAPSHOT") ,(cadar children))
          (fn2-executor-test-snapshot-calls (cdr children)))))
(make-event
 (value `(defun fn2-executor-test-snapshot (fn2-core)
           (declare (xargs :stobjs fn2-core :verify-guards nil))
           (stobj-let ,(fn2-core-child-bindings *fn2-core-children*) (answer)
             (list ,@(fn2-executor-test-snapshot-calls *fn2-core-children*)) answer))))
(in-theory (disable fn2-executor-test-snapshot))

(defun fn2-executor-test-post (slot gen fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (stobj-let ((fn2-ops (fn2-core-ops fn2-core)))
    (fn2-ops)
    (mv-let (code fn2-ops) (fn2-outbox-ack 1 fn2-ops)
      (declare (ignore code))
      (fn2-post-result 0 slot gen *fn2-event-accept-result*
        *fn2-outcome-done* *fn2-reason-none* 0 42 77 fn2-ops)) fn2-core))
(defun fn2-executor-test-mailboxes (fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (stobj-let ((fn2-ops (fn2-core-ops fn2-core)))
    (fn2-ops)
    (let* ((fn2-ops (fn2-post-clock 10 20 0 fn2-ops))
           (fn2-ops (fn2-post-signal 1 fn2-ops))) fn2-ops) fn2-core))
(defun fn2-executor-test-op-head (fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (stobj-let ((fn2-ops (fn2-core-ops fn2-core)))
    (code slot gen) (fn2-outbox-peek 0 fn2-ops) (mv code slot gen)))
(defun fn2-executor-test-op-state (slot fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (stobj-let ((fn2-ops (fn2-core-ops fn2-core)))
    (phase gen) (mv (fn2-ops-phase slot fn2-ops) (fn2-ops-gen slot fn2-ops))
    (mv phase gen)))

; The public one-transition entry also honors a zero descriptor remainder:
; a selected listener requeues without issuing an Accept.
(defun fn2-executor-test-zero-run (fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* ((fn2-core (fn2-init-executor *fn2-profile-tiny* :echo nil fn2-core))
       ((mv obs visits actions bytes steps fn2-core) (fn2-transition nil 0 fn2-core)))
    (mv (and (equal (list obs visits actions bytes steps) '(0 1 0 0 1))
             (= (fn2-exec-queued fn2-core) 0)
             (= (fn2-machine-pending 0 fn2-core) 0)
             (eq (fn2-exec-status fn2-core) :more)) fn2-core)))

; One calendar cycle visits all tiny entries, but only the first listener
; runs. The next cycle selects the second listener and then becomes idle.
(defun fn2-executor-test-initial-run (fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* ((fn2-core (fn2-init-executor *fn2-profile-tiny* :echo nil fn2-core))
       ((mv s0 o0 v0 a0 fn2-core) (fn2-turn fn2-core))
       (pending0 (fn2-machine-pending 0 fn2-core))
       (pending1 (fn2-machine-pending 1 fn2-core))
       ((mv s1 o1 v1 a1 fn2-core) (fn2-turn fn2-core))
       ((mv s2 o2 v2 a2 fn2-core) (fn2-turn fn2-core)))
    (mv (and (equal (list s0 o0 v0 a0) '(:more 0 8 1))
             (equal (list pending0 pending1) '(1 0))
             (equal (list s1 o1 v1 a1) '(:idle 0 1 1))
             (equal (list s2 o2 v2 a2) '(:idle 0 0 0))
             (= (fn2-exec-queued fn2-core) 2)
             (= (fn2-machine-pending 1 fn2-core) 1)) fn2-core)))

; Accept's terminal result recycles its OpRef. The row identity must be
; captured before that recycle, or the completion cannot reach listener 0.
(defun fn2-executor-test-harvest-run (fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* ((fn2-core (fn2-init-executor *fn2-profile-tiny* :echo nil fn2-core))
       ((mv ?o ?v ?a ?b ?s fn2-core) (fn2-transition nil 1 fn2-core))
       ((mv code slot gen) (fn2-executor-test-op-head fn2-core))
       (fn2-core (fn2-executor-test-post slot gen fn2-core))
       ((mv found kind id owner-gen principal) (fn2-core-next-owner fn2-core))
       ((mv o v a bytes steps fn2-core) (fn2-exec-harvest fn2-core))
       ((mv phase new-gen) (fn2-executor-test-op-state slot fn2-core)))
    (mv (and (eq code :ok) found
             (equal (list kind id owner-gen principal) '(0 0 1 0))
             (equal (list o v a bytes steps) '(1 0 0 0 24))
             (= phase *fn2-op-phase-free*) (= new-gen (+ 1 gen))
             (= (fn2-machine-pending 0 fn2-core) 0)
             (= (fn2-machine-event-ready 0 fn2-core) 1)
             (= (fn2-machine-cap-index 0 fn2-core) 42)
             (= (fn2-machine-cap-nonce 0 fn2-core) 77)) fn2-core)))

(defun fn2-executor-test-budget-run (profile fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* ((fn2-core (fn2-init-executor profile :echo nil fn2-core))
       ((mv status nobs nvisits nactions fn2-core) (fn2-turn fn2-core)))
    (mv (and (fn2-core-profilep profile)
             (equal (list status nobs nvisits nactions) '(:more 0 1 1))
             (<= nobs (fn2-profile-h profile))
             (<= nvisits (fn2-profile-k profile))
             (<= nactions (fn2-profile-aturn profile))) fn2-core)))

; H=1 leaves the sticky signal behind after harvesting the clock. With no
; runnable rows the first turn must report :more, never allow a host wait.
(defun fn2-executor-test-h-run (runnablep fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* ((profile (put-assoc-equal :h 1 *fn2-profile-tiny*))
       (fn2-core (if runnablep (fn2-init-executor profile :echo nil fn2-core)
                   (fn2-core-init profile fn2-core)))
       (fn2-core (fn2-executor-test-mailboxes fn2-core))
       ((mv s0 o0 v0 a0 fn2-core) (fn2-turn fn2-core))
       (clock (fn2-exec-now fn2-core))
       ((mv s1 o1 v1 a1 fn2-core) (fn2-turn fn2-core))
       ((mv s2 o2 v2 a2 fn2-core) (fn2-turn fn2-core)))
    (mv (and (fn2-core-profilep profile) (= clock 10)
             (equal (list s0 o0 v0 a0) '(:more 1 0 0))
             (equal (list s1 o1 v1 a1) '(:stop 1 0 0))
             (equal (list s2 o2 v2 a2) '(:stop 0 0 0))) fn2-core)))

(defun fn2-executor-test-initial-snapshot ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (copy fn2-core)
      (let ((fn2-core (fn2-init-executor *fn2-profile-tiny* :echo nil fn2-core)))
        (mv (fn2-executor-test-snapshot fn2-core) fn2-core)) copy)))

(defun fn2-executor-unit-tests ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (result fn2-core)
      (b* (((mv initial fn2-core) (fn2-executor-test-initial-run fn2-core))
           ((mv zero fn2-core) (fn2-executor-test-zero-run fn2-core))
           ((mv harvest fn2-core) (fn2-executor-test-harvest-run fn2-core))
           ((mv k fn2-core) (fn2-executor-test-budget-run
                              (put-assoc-equal :k 1 *fn2-profile-tiny*) fn2-core))
           ((mv a fn2-core) (fn2-executor-test-budget-run
                              (put-assoc-equal :aturn 1 *fn2-profile-tiny*) fn2-core))
           ((mv h-empty fn2-core) (fn2-executor-test-h-run nil fn2-core))
           ((mv h-runnable fn2-core) (fn2-executor-test-h-run t fn2-core))
           ((mv positive fn2-core)
            (mv (fn2-ref-test nil) fn2-core))
           ((mv removal fn2-core)
            (mv (fn2-ref-test t) fn2-core)))
        (mv (list (and initial zero) harvest (and h-empty h-runnable) k a positive removal)
            fn2-core)) result)))
(assert-event (equal (fn2-executor-unit-tests) '(t t t t t t t)))

; Remove only the concrete recognizer hypothesis. This is an ordinary
; logical list, never an invalid write into a live specialized array. The
; rectangular shape still holds, but the H cell is not an unsigned integer.
; Its actual logical turn immediately returns nobs=0, violating 0 <= -1.
(defconst *fn2-executor-test-bad-h*
  (let ((copy (fn2-executor-test-initial-snapshot)))
    (update-nth *fn2-core-control*
      (update-nth *fn2-control-h$ai* '(-1) (nth *fn2-core-control* copy)) copy)))
(defun fn2-executor-test-control-logic-names (columns)
  (declare (xargs :verify-guards nil))
  (if (atom columns) nil
    (let* ((reader (fn2-columns-col-name 'fn2-control (caar columns)))
           (raw (fn2-columns-sym reader "$A")))
      (append (list reader (fn2-columns-col-name 'fn2-control
                             (fn2-columns-pre "SET-" (caar columns)))
                    (fn2-columns-sym raw "I") (fn2-columns-sym raw "-LENGTH")
                    (fn2-columns-pre "UPDATE-" (fn2-columns-sym raw "I")))
              (fn2-executor-test-control-logic-names (cdr columns))))))
(defun fn2-executor-test-execution-runes (names)
  (declare (xargs :verify-guards nil))
  (if (atom names) nil
    (cons (list :executable-counterpart (car names))
          (fn2-executor-test-execution-runes (cdr names)))))
(make-event
 (let* ((schema (cdr (assoc-eq 'fn2-control (table-alist 'fn2-columns (w state)))))
        (columns (cadr (member-eq :columns schema)))
        (names (append '(fn2-turn fn2-concrete-turn fn2-concrete-loop
                         fn2-exec-h fn2-exec-k fn2-exec-aturn
                         fn2-exec-set-turn-bytes fn2-exec-set-turn-steps
                         fn2-corep fn2-core-wfp
                         update-fn2-core-control
                         fn2-control-wfp fn2-control-rows)
                       (strip-cars *fn2-core-children*)
                       (fn2-executor-test-control-logic-names columns))))
   (value
    `(defthm fn2-executor-test-bounds-hypothesis-removal
       (let ((bad *fn2-executor-test-bad-h*))
         (and (not (fn2-corep bad))
              (fn2-core-wfp bad)
              (mv-let (status nobs nvisits nactions after) (fn2-turn bad)
                (declare (ignore status after))
                (and (equal nobs 0)
                     (not (and (<= nobs (fn2-exec-h bad))
                               (<= nvisits (fn2-exec-k bad))
                               (<= nactions (fn2-exec-aturn bad))))))))
       :rule-classes nil
       :hints (("Goal" :in-theory
                (e/d ,names ,(fn2-executor-test-execution-runes names))))))))
