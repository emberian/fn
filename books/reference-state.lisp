; Test/reference access generated from the column declarations. No served caller.
(in-package "ACL2")
(include-book "core")

; Two section books expand these (assembly-reference-children, then
; assembly-reference), so the per-child reference stobjs, which grow with every
; core child, and the core-wide reference functions certify separately, each
; under the one-minute rule. A test instance may expand both in one book.
; Array traversal termination depends only on fuel, not the wide stobj
; recognizers. Keep the prover out of their generated column definitions.
(defmacro fn2-ref-countdown-events ()
 ; Once per world: a test instance expands both reference macros in one book.
 '(make-event
   (if (getpropc 'fn2-ref-countdown 'theorem nil (w state))
       '(value-triple :present)
     '(progn
       (local (defthm fn2-ref-countdown
                (implies (not (zp left)) (o< (nfix (- left 1)) (nfix left)))
                :rule-classes nil))
       (local (defthm fn2-ref-count-op (o-p (nfix left)) :rule-classes nil))))))

; The columns declaration owns copy/diff; this stage supplies congruent children.
(defun fn2-ref-state-events (names registry)
  (declare (xargs :verify-guards nil))
  (if (atom names) nil
    (let* ((name (car names)) (ref (fn2-columns-sym name "-REF"))
           (schema (cdr (assoc-eq name registry)))
           (fields (append (fn2-columns-fields name (fn2-decl-get :columns schema))
                      `((,(fn2-columns-sym name "-ROWS") :type
                         (integer 0 ,(- (fn2-decl-get :rows-bound schema) 1)) :initially 0))
                      (fn2-decl-get :extra-fields schema))))
      (append (fn2-columns-reference-events name ref fields)
              (fn2-ref-state-events (cdr names) registry)))))
; The per-child reference stobjs, their copy/diff/snapshot traversals, for
; part PART of PARTS of the registered children (a contiguous run of them, in
; registry order), so the section books form a chain of groups whose sizes do
; not grow with the instance: a new core child adds to one part, and a part
; near the minute becomes two.
(defun fn2-ref-part (names part parts)
  (declare (xargs :verify-guards nil))
  (let* ((n (len names)) (size (ceiling n (max 1 parts))))
    (take (min size (nfix (- n (* part size)))) (nthcdr (* part size) names))))
(defmacro fn2-reference-children-events (&optional (part '0) (parts '1))
 `(progn
(fn2-ref-countdown-events)

(local (deftheory fn2-ref-base-theory (current-theory :here)))
(local (in-theory nil))
(make-event
 (value (cons 'progn (fn2-ref-state-events
                      (fn2-ref-part (fn2-core-child-types (fn2-core-child-registry (w state))) ,part ,parts)
                      (reverse (fn2-decl-rows :columns (w state)))))))
(local (in-theory (theory 'fn2-ref-base-theory)))
))

; The core-wide reference: the congruent fn2-ref-core, the copy chain, the
; boundary import and the difference.
(defmacro fn2-reference-state-events ()
 '(progn
(fn2-ref-countdown-events)

(defun fn2-ref-core-fields (children)
  (if (atom children) nil
    (cons (list (fn2-columns-sym (caar children) "-REF") :type (cadar children))
          (fn2-ref-core-fields (cdr children)))))
(make-event
 (value (fn2-declare '(:operation-set fn2-ref-core) '(:role :reference)
          '((:declaration (:operation-set fn2-core-issue))
            (:function fn2-ref-copy-core :at :reference)
            (:function fn2-ref-core-difference :at :reference))
          `((defstobj fn2-ref-core ,@(fn2-ref-core-fields *fn2-core-children*)
                         :congruent-to fn2-core)))))
(make-event
 (value `(defconst *fn2-core-reference-children*
           ',(fn2-core-registered-pairs
               (fn2-core-reference-entries (fn2-core-child-registry (w state)))))))
(defun fn2-ref-child-bindings (children refp)
  (if (atom children) nil
    (cons (if refp
              `(,(fn2-columns-sym (cadar children) "-REF")
                (,(fn2-columns-sym (caar children) "-REF") fn2-ref-core))
            `(,(cadar children) (,(caar children) fn2-core)))
          (fn2-ref-child-bindings (cdr children) refp))))
(defun fn2-ref-child-diffs (children)
  (if (atom children) nil
    (let ((name (cadar children)))
      (cons `(,(fn2-columns-sym name "-DIFF") ,name ,(fn2-columns-sym name "-REF")
              :skip (fn2-pool-data))
            (fn2-ref-child-diffs (cdr children))))))

; One copy function per child, then the chain (a single stobj-let over every
; child returns them through one MV, at most 32 values).
(defun fn2-ref-copy-name (field) (fn2-columns-pre "FN2-REF-COPY-" field))
(defun fn2-ref-child-copy-events (children)
  (if (atom children) nil
    (let* ((field (caar children)) (name (cadar children)) (ref (fn2-columns-sym name "-REF")))
      (cons `(defun ,(fn2-ref-copy-name field) (fn2-core fn2-ref-core)
               (declare (xargs :stobjs (fn2-core fn2-ref-core) :verify-guards nil))
               (stobj-let ((,name (,field fn2-core))) (fn2-ref-core)
                 (stobj-let ((,ref (,(fn2-columns-sym field "-REF") fn2-ref-core))) (,ref)
                   (,(fn2-columns-sym name "-COPY") ,name ,ref) fn2-ref-core)
                 fn2-ref-core))
            (fn2-ref-child-copy-events (cdr children))))))
(defun fn2-ref-child-copy-chain (children)
  (if (atom children) nil
    (cons `(fn2-ref-core (,(fn2-ref-copy-name (caar children)) fn2-core fn2-ref-core))
          (fn2-ref-child-copy-chain (cdr children)))))
(make-event (value (cons 'progn (fn2-ref-child-copy-events *fn2-core-children*))))
(make-event
 (let* ((children *fn2-core-children*))
   (value `(fn2-defoperation (:operation-set fn2-ref-core) :reference :infer
            (defun fn2-ref-copy-core (fn2-core fn2-ref-core)
             (declare (xargs :stobjs (fn2-core fn2-ref-core) :verify-guards nil))
             (let* ,(fn2-ref-child-copy-chain children) fn2-ref-core))))))
(in-theory (disable fn2-ref-copy-core))

(defun fn2-ref-reset (profile fn2-core fn2-ref-core)
  (declare (xargs :stobjs (fn2-core fn2-ref-core) :verify-guards nil))
  (let ((fn2-ref-core (fn2-core-init profile fn2-ref-core)))
    (fn2-ref-copy-core fn2-core fn2-ref-core)))
(in-theory (disable fn2-ref-reset))

; Host boundary updates only ops (submission acknowledgments, posted results,
; mailboxes) and physical input loans. Never replace reference machine state,
; pool ownership/fills or control state with the concrete turn's results.
(defun fn2-ref-input-bytes (left fn2-pool fn2-pool-ref)
  (declare (xargs :stobjs (fn2-pool fn2-pool-ref) :verify-guards nil :measure (nfix left)
                  :hints (("Goal" :use (fn2-ref-countdown fn2-ref-count-op) :in-theory nil))))
  (if (zp left) fn2-pool-ref
    (let* ((i (- left 1))
           (fn2-pool-ref
            (if (= (fn2-pool-state i fn2-pool) *fn2-pool-state-leased-in*)
                (fn2-pool-data-copy (fn2-pool-lease-len i fn2-pool)
                  (+ (fn2-pool-base i fn2-pool) (fn2-pool-lease-off i fn2-pool)) fn2-pool fn2-pool-ref)
              fn2-pool-ref)))
      (fn2-ref-input-bytes (- left 1) fn2-pool fn2-pool-ref))))
(defun fn2-ref-import-boundary (fn2-core fn2-ref-core)
  (declare (xargs :stobjs (fn2-core fn2-ref-core) :verify-guards nil))
  (stobj-let ((fn2-pool (fn2-core-pool fn2-core)) (fn2-ops (fn2-core-ops fn2-core)))
    (fn2-ref-core)
    (stobj-let ((fn2-pool-ref (fn2-core-pool-ref fn2-ref-core))
                (fn2-ops-ref (fn2-core-ops-ref fn2-ref-core)))
      (fn2-pool-ref fn2-ops-ref)
      (let* ((fn2-pool-ref (fn2-ref-input-bytes (fn2-pool-rows fn2-pool) fn2-pool fn2-pool-ref))
             (fn2-ops-ref (fn2-ops-copy fn2-ops fn2-ops-ref)))
        (mv fn2-pool-ref fn2-ops-ref)) fn2-ref-core)
    fn2-ref-core))
(in-theory (disable fn2-ref-import-boundary fn2-ref-input-bytes))

; Only initialized bytes can affect a run: the readable prefix, plus input
; bytes named by a posted successful/short completion awaiting harvest.
; A fresh loan does not expose the stale bytes under it (rule 6).
(defun fn2-ref-live-bytes-difference (left fn2-pool fn2-pool-ref fn2-ops)
  (declare (xargs :stobjs (fn2-pool fn2-pool-ref fn2-ops) :verify-guards nil :measure (nfix left)
                  :hints (("Goal" :use (fn2-ref-countdown fn2-ref-count-op) :in-theory nil))))
  (if (zp left) nil
    (let* ((i (- left 1)) (op (fn2-pool-lease-op-slot i fn2-pool))
           (end (max (fn2-pool-fill i fn2-pool)
                (if (and (= (fn2-pool-state i fn2-pool) *fn2-pool-state-leased-in*)
                         (< op (fn2-ops-rows fn2-ops))
                         (= (fn2-ops-c0-posted op fn2-ops) 1)
                         (= (fn2-ops-c0-harvested op fn2-ops) 0)
                         (member-equal (fn2-ops-c0-outcome op fn2-ops)
                                       (list *fn2-outcome-done* *fn2-outcome-short*)))
                    (+ (fn2-pool-lease-off i fn2-pool) (fn2-ops-c0-count op fn2-ops)) 0))))
      (or (fn2-pool-data-diff end (fn2-pool-base i fn2-pool) fn2-pool fn2-pool-ref)
          (fn2-ref-live-bytes-difference (- left 1) fn2-pool fn2-pool-ref fn2-ops)))))
(in-theory (disable fn2-ref-live-bytes-difference))

; Complete scalar/column comparison includes ordered outbox ring entries,
; descriptor kind, OpRef, owner and range, reservations, phases and fills.
; Trace diagnostics and the reference's unused intrusive scheduler are absent.
(make-event
 (let ((children *fn2-core-reference-children*))
   (value `(fn2-defoperation (:operation-set fn2-ref-core) :reference :infer
            (defun fn2-ref-core-difference (fn2-core fn2-ref-core)
             (declare (xargs :stobjs (fn2-core fn2-ref-core) :verify-guards nil))
             (stobj-let ,(fn2-ref-child-bindings children nil) (difference)
               (stobj-let ,(fn2-ref-child-bindings children t) (difference)
                 (or ,@(fn2-ref-child-diffs children)
                     (fn2-ref-live-bytes-difference (fn2-pool-rows fn2-pool)
                       fn2-pool fn2-pool-ref fn2-ops)) difference) difference))))))
(in-theory (disable fn2-ref-core-difference))


(fn2-resolve :reference)
))
