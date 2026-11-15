; Outbox append effects of the common issue primitive. These theorems establish
; the queue delta from actual updates; cancellation queues a request and does
; not dequeue an earlier request. Host acknowledgment is outside this API.
(in-package "ACL2")
(include-book "ops-issued-effects")

(defthm fn2-ops-queued-natural
  (implies (fn2-opsp fn2-ops)
           (natp (nth *fn2-ops-queued* fn2-ops)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable fn2-opsp))))

(defun fn2-issue-queue-frame-events (entries world)
 (declare (xargs :verify-guards nil))
 (if (atom entries) nil
  (let* ((name (caar entries)) (pos (cadar entries))
         (call (cons name (getpropc name 'formals nil world))))
   (cons `(defthm ,(fn2-columns-sym name "-KEEPS-QUEUED")
           (equal (nth *fn2-ops-queued* ,(if (eq pos :self) call `(mv-nth ,pos ,call)))
                  (nth *fn2-ops-queued* fn2-ops))
           :hints (("Goal" :in-theory (enable ,name fn2-ops-queued))))
    (fn2-issue-queue-frame-events (cdr entries) world)))))
(make-event (value (cons 'progn (fn2-issue-queue-frame-events
 '((fn2-ops-clear-row :self) (fn2-op-reserve 3) (fn2-op-unreserve 1)
   (fn2-op-set-range 1) (fn2-op-set-capability 1) (fn2-op-set-storage 1)
   (fn2-op-set-cancel-target 1)) (w state)))))
(defthm fn2-op-enqueue-queued-effect
 (implies (fn2-opsp fn2-ops)
  (equal (nth *fn2-ops-queued* (mv-nth 1 (fn2-op-enqueue slot gen fn2-ops)))
   (+ (nth *fn2-ops-queued* fn2-ops)
      (if (eq (car (fn2-op-enqueue slot gen fn2-ops)) :ok) 1 0))))
 :hints (("Goal" :in-theory (enable fn2-op-enqueue fn2-ops-queued))))
(defthm fn2-issue-children-queued-effect
 (implies (and (fn2-opsp fn2-ops) (fn2-ops-wfp fn2-ops))
  (equal
   (nth *fn2-ops-queued* (mv-nth 4 (fn2-issue-children kind cap-index cap-nonce offset fua slot gen off len may-release target-slot target-gen okind oslot ogen principal fn2-pool fn2-ops fn2-control)))
   (+ (nth *fn2-ops-queued* fn2-ops)
      (if (eq (car (fn2-issue-children kind cap-index cap-nonce offset fua slot gen off len may-release target-slot target-gen okind oslot ogen principal fn2-pool fn2-ops fn2-control)) :ok) 1 0))))
 :hints (("Goal" :in-theory (e/d (fn2-issue-children) (fn2-op-enqueue fn2-ops-queued)))))

(defun fn2-issue-wrapper-effect-events (names world)
 (declare (xargs :verify-guards nil))
 (if (atom names) nil
  (let* ((name (car names))
         (call (cons name (getpropc name 'formals nil world)))
         (pos (fn2-issued-wrapper-ops-position name world)))
   (if (not pos)
       `((make-event (er soft 'fn2-issue-wrapper-effect-events
            "Unsupported issue result ABI for ~x0." ',name)))
   (cons `(defthm ,(fn2-columns-sym name "-QUEUED-EFFECT")
     (implies (and (fn2-opsp fn2-ops) (fn2-ops-wfp fn2-ops))
      (equal (nth *fn2-ops-queued* (mv-nth ,pos ,call))
       (+ (nth *fn2-ops-queued* fn2-ops) (if (eq (car ,call) :ok) 1 0))))
     :hints (("Goal" :in-theory (enable ,name))))
    (fn2-issue-wrapper-effect-events (cdr names) world))))))
(make-event
 (value (cons 'progn (fn2-issue-wrapper-effect-events
  (strip-cars (table-alist 'fn2-issue-child-wrappers (w state)))
  (w state)))))

; The core face uses the same append relation, through the generated child
; read/write matrix. This constructor is also used by focused core fixtures.
(defun fn2-issue-core-effect-event (name formals)
  (declare (xargs :verify-guards nil))
  (let ((call (cons name formals)))
    `(defthm ,(fn2-columns-sym name "-QUEUED-EFFECT")
       (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core))
         (equal (nth *fn2-ops-queued* (fn2-core-ops (mv-nth 3 ,call)))
                (+ (nth *fn2-ops-queued* (fn2-core-ops fn2-core))
                   (if (eq (car ,call) :ok) 1 0))))
       :hints (("Goal" :use (:instance fn2-ops-queued-natural (fn2-ops (fn2-core-ops fn2-core)))
                       :in-theory (e/d (,name) (fn2-core-ops fn2-corep fn2-core-wfp nfix nth)))))))

; A preceding frame can normalize ROWS(input) before rewriting the nested
; issue call. Match the history index independently, then discharge its row
; equality from the same frame. This is a corollary of the existing law.
(defun fn2-issue-core-issued-index-event (name formals)
 (declare (xargs :verify-guards nil))
 (let ((call (cons name formals)))
  `(defthm ,(fn2-columns-sym name "-ISSUED-COUNT-AT-ROWS")
    (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
                  (equal n (fn2-ops-rows (fn2-core-ops fn2-core))))
     (equal (fn2-ops-issued-count n (fn2-core-ops (mv-nth 3 ,call)))
            (+ (fn2-ops-issued-count n (fn2-core-ops fn2-core))
               (if (eq (car ,call) :ok) 1 0))))
    :hints (("Goal" :use ,(fn2-columns-sym name "-ISSUED-TOTAL")
      :in-theory (disable ,name ,(fn2-columns-sym name "-ISSUED-TOTAL")
        fn2-corep fn2-core-wfp fn2-core-ops fn2-ops-issued-count fn2-ops-rows))))))

(defun fn2-issue-core-issued-event (name formals)
 (declare (xargs :verify-guards nil))
 (let* ((call (cons name formals)) (out `(fn2-core-ops (mv-nth 3 ,call))))
  `(progn
     (defthm ,(fn2-columns-sym name "-ISSUED-TOTAL")
    (implies (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core))
     ,(fn2-run-issued-claim `(if (eq (car ,call) :ok) 1 0) '(fn2-core-ops fn2-core) out))
    :hints (("Goal" :in-theory (e/d (,name)
     (fn2-core-ops fn2-corep fn2-core-wfp fn2-ops-issued-count fn2-op-issued-weight fn2-ops-rows nfix nth)))))
     ,(fn2-issue-core-issued-index-event name formals))))
