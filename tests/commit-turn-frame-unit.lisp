; Teeth of the commit lifting (books/commit-turn-frame.lisp) on a live core:
; the honest scheduler of tests/commit-durable-all-unit.lisp, its :turn
; stepped through fn2-turn's own loop (fn2-concrete-loop-stop-p,
; fn2-transition, fn2-exec-account-work), the commit rows read through
; their generic readers before and after every transition. POSITIVE: each
; transition changes at most one commit row, only in columns some commit
; arm or the route declares, never the row's kind or slot; some transition
; raises a reply count by one (the :notify arm ran). MUTANTS: a transition
; record with a second row changed, or batch-no changed, is refused.
(in-package "ACL2")
(include-book "../books/commit-durable-all")
(include-book "../books/commit-turn-frame")

(defun fn2-ctft-profile (mode)
  (declare (xargs :verify-guards nil))
  (let* ((p *fn2-profile-tiny*)
         (p (put-assoc-equal :sim-sectors (* 5 *fn2-storage-extent-units*) p))
         (p (put-assoc-equal :extent-slots 5 p))
         (p (put-assoc-equal :pool-classes (append (fn2-profile-pool-classes p) '((8 . 4096))) p)))
    (put-assoc-equal :commit-barrier-mode mode p)))

;; A commit row as its generic readers show it: kind, slot, then each
;; table column with a generic reader, in table order.
(defun fn2-ctft-readers (cols world)
  (declare (xargs :mode :program))
  (cond ((atom cols) nil)
        ((function-symbolp (fn2-columns-col-name 'fn2-machine (car cols)) world)
         (cons (list (car cols) (fn2-columns-col-name 'fn2-machine (car cols)))
               (fn2-ctft-readers (cdr cols) world)))
        (t (fn2-ctft-readers (cdr cols) world))))
(make-event
 (let* ((world (w state))
        (rs (fn2-ctft-readers (strip-cars (fn2-machine-property 'fn2-commit :table world)) world))
        (tcols (strip-cars (fn2-machine-property 'fn2-commit :table world))))
   (value
    `(progn
       (defconst *fn2-ctft-columns* ',(loop$ for r in rs collect (position-eq (car r) tcols)))
       (defun fn2-ctft-row (id fn2-core)
         (declare (xargs :stobjs fn2-core :verify-guards nil))
         (list* (fn2-machine-kind id fn2-core) (fn2-machine-slot id fn2-core)
                (list ,@(loop$ for r in rs collect `(,(cadr r) id fn2-core)))))))))
(defun fn2-ctft-rows (ids fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (if (atom ids) nil (cons (fn2-ctft-row (car ids) fn2-core) (fn2-ctft-rows (cdr ids) fn2-core))))
;; The table columns at which two row reads differ.
(defun fn2-ctft-diff (cols a b)
  (declare (xargs :verify-guards nil))
  (cond ((atom cols) nil)
        ((equal (car a) (car b)) (fn2-ctft-diff (cdr cols) (cdr a) (cdr b)))
        (t (cons (car cols) (fn2-ctft-diff (cdr cols) (cdr a) (cdr b))))))
;; One transition's record: for each commit row, (kind-slot-same . changed columns).
(defun fn2-ctft-record (before after)
  (declare (xargs :verify-guards nil))
  (if (atom before) nil
    (cons (cons (and (equal (car (car before)) (car (car after))) (equal (cadr (car before)) (cadr (car after))))
                (fn2-ctft-diff *fn2-ctft-columns* (cddr (car before)) (cddr (car after))))
          (fn2-ctft-record (cdr before) (cdr after)))))

;; fn2-turn's loop, one transition at a time, each recorded.
(defun fn2-ctft-loop (fuel h k a nobs nvisits nactions ids recs fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil :measure (nfix fuel)))
  (if (or (zp fuel) (fn2-concrete-loop-stop-p h k a nobs nvisits nactions fn2-core)) (mv recs fn2-core)
    (let ((before (fn2-ctft-rows ids fn2-core)))
      (mv-let (obs visits actions bytes steps fn2-core) (fn2-transition (< nobs h) (- a nactions) fn2-core)
        (let* ((rec (fn2-ctft-record before (fn2-ctft-rows ids fn2-core)))
               (fn2-core (fn2-exec-account-work bytes steps fn2-core)))
          (fn2-ctft-loop (- fuel 1) h k a (+ nobs (nfix obs)) (+ nvisits (nfix visits)) (+ nactions (nfix actions))
                         ids (cons rec recs) fn2-core))))))
(defun fn2-ctft-turn (ids recs fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (let* ((h (fn2-exec-h fn2-core)) (k (fn2-exec-k fn2-core)) (a (fn2-exec-aturn fn2-core))
         (fn2-core (fn2-exec-set-turn-bytes 0 fn2-core))
         (fn2-core (fn2-exec-set-turn-steps 0 fn2-core)))
    (fn2-ctft-loop (+ h k) h k a 0 0 0 ids recs fn2-core)))

;; The scheduler of commit-durable-all-unit (take, answer the oldest storage
;; operation honestly, else turn), its turns recorded.
(defun fn2-ctft-unanswered (rlog newer)
  (declare (xargs :verify-guards nil))
  (cond ((atom rlog) nil)
        ((and (fn2-dev-takep (car rlog))
              (member-equal (nth 3 (car rlog)) (list *fn2-action-write* *fn2-action-fence* *fn2-action-read*))
              (not (fn2-dev-answer (nth 1 (car rlog)) (nth 2 (car rlog)) newer)))
         (cons (car rlog) (fn2-ctft-unanswered (cdr rlog) (append newer (list (car rlog))))))
        (t (fn2-ctft-unanswered (cdr rlog) (append newer (list (car rlog)))))))
(defun fn2-ctft-answer (e)
  (declare (xargs :verify-guards nil))
  (let* ((kind (nth 3 e)) (len (cond ((equal kind *fn2-action-fence*) 0) (t (len (nth 6 e))))))
    (mv-let (outcome reason count aux0 aux1) (fn2-host-result kind :ok len 0 len nil)
      (list :post-result 0 (nth 1 e) (nth 2 e) (fn2-terminal-event kind) outcome reason count aux0 aux1))))
(defun fn2-ctft-auto (fuel ids rlog recs fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil :measure (nfix fuel)))
  (if (zp fuel) (mv recs fn2-core)
    (let ((pending (fn2-ctft-unanswered rlog nil)))
      (cond ((< 0 (fn2-host-outbox-queued fn2-core))
             (mv-let (entry fn2-core) (fn2-env-step '(:take) nil nil rlog fn2-core)
               (fn2-ctft-auto (- fuel 1) ids (if entry (cons entry rlog) rlog) recs fn2-core)))
            ((consp pending)
             (mv-let (entry fn2-core) (fn2-env-step (fn2-ctft-answer (car (last pending))) nil nil rlog fn2-core)
               (fn2-ctft-auto (- fuel 1) ids (if entry (cons entry rlog) rlog) recs fn2-core)))
            (t (mv-let (recs fn2-core) (fn2-ctft-turn ids recs fn2-core)
                 (fn2-ctft-auto (- fuel 1) ids rlog recs fn2-core)))))))
(defun fn2-ctft-run (mode fuel)
  (declare (xargs :verify-guards nil))
  (let ((profile (fn2-ctft-profile mode)))
    (with-local-stobj fn2-core
      (mv-let (recs fn2-core)
        (b* ((fn2-core (fn2-init-executor profile :echo nil fn2-core))
             ((mv & & fn2-core) (fn2-env-steps (list (list :epoch 1) (list :admit 2 mode) (list :admit 2 mode))
                                               (fn2-env-commit-ids profile) nil nil fn2-core)))
          (fn2-ctft-auto fuel (fn2-env-commit-ids profile) nil nil fn2-core))
        recs))))
(make-event `(defconst *fn2-ctft-records* ',(fn2-ctft-run 0 600)))

;; The statement's shape on a record: kind and slot kept on every row; at
;; most one row changed; its columns among the declared ones.
(defun fn2-ctft-arm-columns (decls)
  (declare (xargs :verify-guards nil))
  (if (atom decls) nil (union-equal (caddr (car decls)) (fn2-ctft-arm-columns (cdr decls)))))
(make-event `(defconst *fn2-ctft-declared*
               ',(union-equal *fn2-commit-route-columns* (fn2-ctft-arm-columns *fn2-commit-arm-decls*))))
(defun fn2-ctft-rows-ok (rec)
  (declare (xargs :verify-guards nil))
  (or (atom rec) (and (car (car rec)) (subsetp-equal (cdr (car rec)) *fn2-ctft-declared*) (fn2-ctft-rows-ok (cdr rec)))))
(defun fn2-ctft-rec-acked (rec)
  (declare (xargs :verify-guards nil))
  (and (consp rec) (or (member-equal 27 (cdr (car rec))) (fn2-ctft-rec-acked (cdr rec)))))
(defun fn2-ctft-changed (rec)
  (declare (xargs :verify-guards nil))
  (cond ((atom rec) 0) ((consp (cdar rec)) (+ 1 (fn2-ctft-changed (cdr rec)))) (t (fn2-ctft-changed (cdr rec)))))
(defun fn2-ctft-rec-ok (rec)
  (declare (xargs :verify-guards nil))
  (and (<= (fn2-ctft-changed rec) 1) (fn2-ctft-rows-ok rec)))
(defun fn2-ctft-all-ok (recs)
  (declare (xargs :verify-guards nil))
  (or (atom recs) (and (fn2-ctft-rec-ok (car recs)) (fn2-ctft-all-ok (cdr recs)))))
(defun fn2-ctft-acked (recs)
  ; some transition changed a reply count (cb-acks)
  (declare (xargs :verify-guards nil))
  (and (consp recs)
       (or (fn2-ctft-rec-acked (car recs)) (fn2-ctft-acked (cdr recs)))))
(assert-event (equal (position-eq 'cb-acks (strip-cars (fn2-machine-property 'fn2-commit :table (w state)))) 27))
(defun fn2-commit-turn-frame-positive ()
  (declare (xargs :verify-guards nil))
  (and (< 10 (len *fn2-ctft-records*)) (fn2-ctft-all-ok *fn2-ctft-records*)
       (consp (fn2-ctft-acked *fn2-ctft-records*))))
(defun fn2-commit-turn-frame-mutants ()
  (declare (xargs :verify-guards nil))
  (and (not (fn2-ctft-rec-ok '((t 27) (t 0))))          ; two rows changed in one transition
       (not (fn2-ctft-rec-ok '((t 9) (t))))             ; batch-no changed
       (not (fn2-ctft-rec-ok '((nil) (t))))))           ; a row's slot moved
(assert-event (fn2-commit-turn-frame-positive))
(assert-event (fn2-commit-turn-frame-mutants))
