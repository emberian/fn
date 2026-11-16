; Independent literal FIFO operations shared by scheduler/reference contracts.
; Extracted unchanged from reference; no production handler is called.
(in-package "ACL2")
(include-book "operations")

(defun fn2-ref-list-member (x xs)
  (declare (xargs :guard t))
  (and (consp xs)
       (or (equal x (car xs)) (fn2-ref-list-member x (cdr xs)))))
(defun fn2-ref-queue (principal queues)
  (declare (xargs :guard t))
  (if (atom queues) nil
    (if (and (consp (car queues)) (equal principal (caar queues)))
        (cdar queues)
      (fn2-ref-queue principal (cdr queues)))))
(defun fn2-ref-set-queue (principal queue queues)
  (declare (xargs :guard t))
  (if (atom queues) (list (cons principal queue))
    (if (and (consp (car queues)) (equal principal (caar queues)))
        (cons (cons principal queue) (cdr queues))
      (cons (car queues) (fn2-ref-set-queue principal queue (cdr queues))))))
(defun fn2-ref-queued-anywhere (machine queues)
  (declare (xargs :guard t))
  (and (consp queues)
       (or (and (consp (car queues))
                (fn2-ref-list-member machine (cdar queues)))
           (fn2-ref-queued-anywhere machine (cdr queues)))))
(defun fn2-ref-enqueue (machine principal queues)
  (declare (xargs :guard t))
  (if (or (equal machine *fn2-none*)
          (fn2-ref-queued-anywhere machine queues)) queues
    (fn2-ref-set-queue
     principal (append (true-list-fix (fn2-ref-queue principal queues))
                       (list machine)) queues)))

(defun fn2-ref-queue-count (queues)
  (declare (xargs :verify-guards nil))
  (if (atom queues) 0 (+ (len (cdar queues)) (fn2-ref-queue-count (cdr queues)))))
