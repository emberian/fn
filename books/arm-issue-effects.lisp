; Outbox append effects of the common issue primitive. These theorems establish
; the queue delta from actual updates; cancellation queues a request and does
; not dequeue an earlier request. Host acknowledgment is outside this API.
(in-package "ACL2")
(include-book "arm-children")

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
         (call (cons name (getpropc name 'formals nil world))))
   (cons `(defthm ,(fn2-columns-sym name "-QUEUED-EFFECT")
     (implies (and (fn2-opsp fn2-ops) (fn2-ops-wfp fn2-ops))
      (equal (nth *fn2-ops-queued* (mv-nth 4 ,call))
       (+ (nth *fn2-ops-queued* fn2-ops) (if (eq (car ,call) :ok) 1 0))))
     :hints (("Goal" :in-theory (enable ,name))))
    (fn2-issue-wrapper-effect-events (cdr names) world)))))
(make-event
 (value (cons 'progn (fn2-issue-wrapper-effect-events
  '(fn2-issue-receive-children fn2-issue-send-children fn2-issue-read-children
    fn2-issue-write-children fn2-issue-fence-children fn2-issue-accept-children
    fn2-issue-close-children fn2-issue-cancel-children fn2-issue-entropy-children)
  (w state)))))
