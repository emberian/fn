; Test/reference access generated from the column declarations. No served caller.
(in-package "ACL2")
(include-book "executor")

 ; Array traversal termination depends only on fuel, not the wide stobj
; recognizers. Keep the prover out of their generated column definitions.
(local (defthm fn2-ref-countdown
         (implies (not (zp left)) (o< (nfix (- left 1)) (nfix left)))
         :rule-classes nil))
(local (defthm fn2-ref-count-op (o-p (nfix left)) :rule-classes nil))

; Congruent children allow simultaneous access to the two nested cores.
(defun fn2-ref-renamed-fields (fields)
  (if (atom fields) nil
    (cons (cons (fn2-columns-sym (caar fields) "-REF") (cdar fields))
          (fn2-ref-renamed-fields (cdr fields)))))
(defun fn2-ref-field-events (name ref fields)
  (declare (xargs :verify-guards nil))
  (if (atom fields) nil
    (let* ((field (caar fields))
           (arrayp (fn2-columns-arrayp (car fields)))
           (reader (if arrayp (fn2-columns-sym field "I") field))
           (writer (fn2-columns-pre "UPDATE-" reader))
           (copy (fn2-columns-sym field "-REF-COPY"))
           (diff (fn2-columns-sym field "-REF-DIFF")))
      (append
       (if arrayp
           `((defun ,copy (left i ,name ,ref)
               (declare (xargs :stobjs (,name ,ref) :verify-guards nil :measure (nfix left)
                  :hints (("Goal" :use (fn2-ref-countdown fn2-ref-count-op) :in-theory nil))))
               (if (zp left) ,ref
                 (let ((,ref (,writer i (,reader i ,name) ,ref)))
                   (,copy (- left 1) (+ 1 (nfix i)) ,name ,ref))))
             (defun ,diff (left i ,name ,ref)
               (declare (xargs :stobjs (,name ,ref) :verify-guards nil :measure (nfix left)
                  :hints (("Goal" :use (fn2-ref-countdown fn2-ref-count-op) :in-theory nil))))
               (if (zp left) nil
                 (if (equal (,reader i ,name) (,reader i ,ref))
                     (,diff (- left 1) (+ 1 (nfix i)) ,name ,ref)
                   (list ',field i (,reader i ,name) (,reader i ,ref)))))
             (in-theory (disable ,copy ,diff))) nil)
       (fn2-ref-field-events name ref (cdr fields))))))
(defun fn2-ref-copy-bindings (name ref fields)
  (declare (xargs :verify-guards nil))
  (if (atom fields) nil
    (let* ((field (caar fields)) (arrayp (fn2-columns-arrayp (car fields)))
           (length (fn2-columns-sym field "-LENGTH")))
      (append
       (if (and arrayp (cadr (member-eq :resizable (cdar fields))))
           `((,ref (,(fn2-columns-pre "RESIZE-" field) (,length ,name) ,ref))) nil)
       `((,ref ,(if arrayp
                       `(,(fn2-columns-sym field "-REF-COPY") (,length ,name) 0 ,name ,ref)
                     `(,(fn2-columns-pre "UPDATE-" field) (,field ,name) ,ref))))
       (fn2-ref-copy-bindings name ref (cdr fields))))))
(defun fn2-ref-diff-terms (name ref fields)
  (declare (xargs :verify-guards nil))
  (if (atom fields) nil
    (let* ((field (caar fields)) (arrayp (fn2-columns-arrayp (car fields)))
           (length (fn2-columns-sym field "-LENGTH")))
      (cons
       (if arrayp
           `(if (equal (,length ,name) (,length ,ref))
                ,(if (eq field 'fn2-pool-data) nil
                   `(,(fn2-columns-sym field "-REF-DIFF") (,length ,name) 0 ,name ,ref))
              (list ',length))
         `(and (not (equal (,field ,name) (,field ,ref))) (list ',field)))
       (fn2-ref-diff-terms name ref (cdr fields))))))
(defun fn2-ref-state-events (names registry)
  (declare (xargs :verify-guards nil))
  (if (atom names) nil
    (let* ((name (car names)) (ref (fn2-columns-sym name "-REF"))
           (schema (cdr (assoc-eq name registry)))
           (fields (append (fn2-columns-fields name (cadr (member-eq :columns schema)))
                      `((,(fn2-columns-sym name "-ROWS") :type
                         (integer 0 ,(- (cadr (member-eq :rows-bound schema)) 1)) :initially 0))
                      (cadr (member-eq :extra-fields schema))))
           (copy (fn2-columns-sym name "-REF-COPY"))
           (diff (fn2-columns-sym name "-REF-DIFF")))
      (append
       `((defstobj ,ref ,@(fn2-ref-renamed-fields fields) :congruent-to ,name))
       (fn2-ref-field-events name ref fields)
       `((defun ,copy (,name ,ref)
           (declare (xargs :stobjs (,name ,ref) :verify-guards nil))
           (let* ,(fn2-ref-copy-bindings name ref fields) ,ref))
         (defun ,diff (,name ,ref)
           (declare (xargs :stobjs (,name ,ref) :verify-guards nil))
           (or ,@(fn2-ref-diff-terms name ref fields)))
         (in-theory (disable ,copy ,diff)))
       (fn2-ref-state-events (cdr names) registry)))))
(assert-event
 (equal (fn2-ref-copy-bindings 'x 'y '((sample-counter :type (unsigned-byte 32))))
        '((y (update-sample-counter (sample-counter x) y)))))
(assert-event
 (equal (fn2-ref-diff-terms 'x 'y '((sample-counter :type (unsigned-byte 32))))
        '((and (not (equal (sample-counter x) (sample-counter y))) (list 'sample-counter)))))
(local (deftheory fn2-ref-base-theory (current-theory :here)))
(local (in-theory nil))
(make-event
 (value (cons 'progn (fn2-ref-state-events (append '(fn2-pool fn2-ops fn2-machines fn2-control) (fn2-machine-names (w state)))
                       (table-alist 'fn2-columns (w state))))))
(local (in-theory (theory 'fn2-ref-base-theory)))

(defun fn2-ref-core-fields (children)
  (if (atom children) nil
    (cons (list (fn2-columns-sym (caar children) "-REF") :type (cadar children))
          (fn2-ref-core-fields (cdr children)))))
(make-event (value `(defstobj fn2-ref-core ,@(fn2-ref-core-fields *fn2-core-children*)
                     :congruent-to fn2-core)))
(defun fn2-ref-children (children)
  (if (atom children) nil
    (if (member-eq (cadar children) '(fn2-sched fn2-trace))
        (fn2-ref-children (cdr children))
      (cons (car children) (fn2-ref-children (cdr children))))))
(defun fn2-ref-child-bindings (children refp)
  (if (atom children) nil
    (cons (if refp
              `(,(fn2-columns-sym (cadar children) "-REF")
                (,(fn2-columns-sym (caar children) "-REF") fn2-ref-core))
            `(,(cadar children) (,(caar children) fn2-core)))
          (fn2-ref-child-bindings (cdr children) refp))))
(defun fn2-ref-child-copies (children)
  (if (atom children) nil
    (let ((name (cadar children)))
      (cons `(,(fn2-columns-sym name "-REF")
               (,(fn2-columns-sym name "-REF-COPY") ,name ,(fn2-columns-sym name "-REF")))
            (fn2-ref-child-copies (cdr children))))))
(defun fn2-ref-child-diffs (children)
  (if (atom children) nil
    (let ((name (cadar children)))
      (cons `(,(fn2-columns-sym name "-REF-DIFF") ,name ,(fn2-columns-sym name "-REF"))
            (fn2-ref-child-diffs (cdr children))))))

(make-event
 (let* ((children (fn2-ref-children *fn2-core-children*))
        (bindings (fn2-ref-child-bindings children t)) (refs (strip-cars bindings)))
   (value `(defun fn2-ref-copy-core (fn2-core fn2-ref-core)
             (declare (xargs :stobjs (fn2-core fn2-ref-core) :verify-guards nil))
             (stobj-let ,(fn2-ref-child-bindings children nil) (fn2-ref-core)
               (stobj-let ,bindings ,refs
                 (let* ,(fn2-ref-child-copies children) (mv ,@refs)) fn2-ref-core)
               fn2-ref-core)))))
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
                (fn2-pool-data-ref-copy (fn2-pool-lease-len i fn2-pool)
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
             (fn2-ops-ref (fn2-ops-ref-copy fn2-ops fn2-ops-ref)))
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
      (or (fn2-pool-data-ref-diff end (fn2-pool-base i fn2-pool) fn2-pool fn2-pool-ref)
          (fn2-ref-live-bytes-difference (- left 1) fn2-pool fn2-pool-ref fn2-ops)))))
(in-theory (disable fn2-ref-live-bytes-difference))

; Complete scalar/column comparison includes ordered outbox ring entries,
; descriptor kind, OpRef, owner and range, reservations, phases and fills.
; Trace diagnostics and the reference's unused intrusive scheduler are absent.
(make-event
 (let ((children (fn2-ref-children *fn2-core-children*)))
   (value `(defun fn2-ref-core-difference (fn2-core fn2-ref-core)
             (declare (xargs :stobjs (fn2-core fn2-ref-core) :verify-guards nil))
             (stobj-let ,(fn2-ref-child-bindings children nil) (difference)
               (stobj-let ,(fn2-ref-child-bindings children t) (difference)
                 (or ,@(fn2-ref-child-diffs children)
                     (fn2-ref-live-bytes-difference (fn2-pool-rows fn2-pool)
                       fn2-pool fn2-pool-ref fn2-ops)) difference) difference)))))
(in-theory (disable fn2-ref-core-difference))
