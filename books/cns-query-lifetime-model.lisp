; Independent CNS source-owner wake and alias-query completion frames.
; The exact lookup scratch carriers are explicit; owned pool/query rows,
; all machine state and every other core child have prescribed effects.
(in-package "ACL2")
(include-book "cns-draining-model")
(include-book "queue-model")

(defun fn2-cns-query-owner-livep (kind owner generation before)
  (let* ((dir (fn2-cns-drain-child 'fn2-machines before))
         (own (fn2-cns-drain-child 'fn2-cns before))
         (slot (fn2-cns-drain-cell 'fn2-machines-slot owner dir)))
    (and (equal kind *fn2-cns-kind*)
         (natp owner) (< owner (fn2-cns-drain-get 'fn2-machines-rows dir))
         (equal (fn2-cns-drain-cell 'fn2-machines-kind owner dir) kind)
         (natp slot) (< slot (fn2-cns-drain-get 'fn2-cns-rows own))
         (equal (fn2-cns-drain-cell 'fn2-cns-generation slot own) generation)
         (not (member-equal (fn2-cns-drain-cell 'fn2-cns-phase slot own)
                            (list *fn2-cns-state-free* *fn2-cns-state-retired*)))
         (equal (fn2-cns-drain-cell 'fn2-cns-stopped slot own) 0))))

(defun fn2-cns-query-carry-children (names after before)
  (if (atom names) before
    (fn2-cns-query-carry-children (cdr names) after
      (fn2-cns-drain-put-child (car names)
        (fn2-cns-drain-child (car names) after) before))))


; Projection into literal FIFOs is bounded by the concrete row population;
; malformed/cyclic links yield an explicit marker, never a truncated queue.
(defun fn2-cns-query-fifo (left id sched)
  (declare (xargs :measure (nfix left)))
  (cond ((equal id *fn2-none*) nil)
        ((or (zp left) (not (natp id))
             (>= id (fn2-cns-drain-get 'fn2-sched-rows sched))) '(:bad-chain))
        (t (cons id (fn2-cns-query-fifo (- left 1)
                      (fn2-cns-drain-cell 'fn2-sched-next id sched) sched)))))
(defun fn2-cns-query-queues (left principal sched)
  (declare (xargs :measure (nfix left)))
  (if (zp left) nil
    (cons (cons principal
            (fn2-cns-query-fifo (fn2-cns-drain-get 'fn2-sched-rows sched)
              (fn2-cns-drain-cell 'fn2-sched-heads principal sched) sched))
          (fn2-cns-query-queues (- left 1) (+ 1 (nfix principal)) sched))))
(defun fn2-cns-query-fifo-validp (queue principal prev sched)
  (if (atom queue) (null queue)
    (let ((id (car queue)))
      (and (natp id) (< id (fn2-cns-drain-get 'fn2-sched-rows sched))
           (equal (fn2-cns-drain-cell 'fn2-sched-principal id sched) principal)
           (equal (fn2-cns-drain-cell 'fn2-sched-in-queue id sched) 1)
           (equal (fn2-cns-drain-cell 'fn2-sched-prev id sched) prev)
           (equal (fn2-cns-drain-cell 'fn2-sched-next id sched)
                  (if (consp (cdr queue)) (cadr queue) *fn2-none*))
           (fn2-cns-query-fifo-validp (cdr queue) principal id sched)))))
(defun fn2-cns-query-queue-ids (queues)
  (if (atom queues) nil
    (append (cdar queues) (fn2-cns-query-queue-ids (cdr queues)))))
(defun fn2-cns-query-queues-validp (queues sched)
  (if (atom queues) (null queues)
    (let ((p (caar queues)) (q (cdar queues)))
      (and (fn2-cns-query-fifo-validp q p *fn2-none* sched)
           (equal (fn2-cns-drain-cell 'fn2-sched-counts p sched) (len q))
           (equal (fn2-cns-drain-cell 'fn2-sched-tails p sched)
                  (if (consp q) (car (last q)) *fn2-none*))
           (fn2-cns-query-queues-validp (cdr queues) sched)))))
(defun fn2-cns-query-enqueue-contextp (owner principal sched)
  (let* ((np (fn2-cns-drain-get 'fn2-sched-nprincipals sched))
         (queues (fn2-cns-query-queues np 0 sched)))
    (and (natp owner) (< owner (fn2-cns-drain-get 'fn2-sched-rows sched))
         (natp principal) (< principal np)
         (fn2-cns-query-queues-validp queues sched)
         (no-duplicatesp-equal (fn2-cns-query-queue-ids queues))
         (equal (fn2-cns-drain-get 'fn2-sched-queued sched) (fn2-ref-queue-count queues))
         (< (fn2-ref-queue-count queues) *fn2-none*)
         (equal (fn2-cns-drain-cell 'fn2-sched-in-queue owner sched)
                (if (fn2-ref-queued-anywhere owner queues) 1 0)))))

; Encode the single literal FIFO append; preserve all fields outside its
; exact target/tail links and principal counters. Decisions use list FIFO
; membership/append, not the runtime in-queue flag or insertion function.
(defun fn2-cns-query-sched-enqueue-expected (owner principal sched)
  (let* ((queues (fn2-cns-query-queues
                   (fn2-cns-drain-get 'fn2-sched-nprincipals sched) 0 sched))
         (after (fn2-ref-enqueue owner principal queues))
         (oldq (fn2-ref-queue principal queues))
         (newq (fn2-ref-queue principal after)))
    (if (equal queues after) sched
      (let* ((tail (if (consp oldq) (car (last oldq)) *fn2-none*))
             (sched (fn2-cns-drain-put-cells
                      (list (list 'fn2-sched-principal principal) (list 'fn2-sched-in-queue 1)
                            (list 'fn2-sched-prev tail) (list 'fn2-sched-next *fn2-none*)) owner sched))
             (sched (if (consp oldq)
                        (fn2-cns-drain-put-cell 'fn2-sched-next tail owner sched) sched))
             (sched (fn2-cns-drain-put-cell 'fn2-sched-heads principal (car newq) sched))
             (sched (fn2-cns-drain-put-cell 'fn2-sched-tails principal (car (last newq)) sched))
             (sched (fn2-cns-drain-put-cell 'fn2-sched-counts principal (len newq) sched)))
        (fn2-cns-drain-put 'fn2-sched-queued (fn2-ref-queue-count after) sched)))))

; Complete diagnostic ring effect of one enqueue attempt, including :already.
; Trace loss/disable never decides scheduler membership or FIFO order.
(defun fn2-cns-query-trace-enqueue-expected (owner principal trace)
  (let ((head (fn2-cns-drain-get 'fn2-trace-head trace))
        (rows (fn2-cns-drain-get 'fn2-trace-rows trace))
        (count (fn2-cns-drain-get 'fn2-trace-count trace))
        (lost (fn2-cns-drain-get 'fn2-trace-lost trace)))
    (if (equal (fn2-cns-drain-get 'fn2-trace-enabled trace) 0) trace
      (if (not (and (natp head) (< head rows)))
          (fn2-cns-drain-put 'fn2-trace-lost (min *fn2-u60-max* (+ 1 lost)) trace)
        (let* ((trace (fn2-cns-drain-put-cells
                        (list (list 'fn2-trace-kind *fn2-trace-kind-enqueue*)
                              (list 'fn2-trace-machine owner) (list 'fn2-trace-principal principal)
                              (list 'fn2-trace-position 0) (list 'fn2-trace-bytes 0)
                              (list 'fn2-trace-steps 0) (list 'fn2-trace-actions 0)
                              (list 'fn2-trace-runnable 0) (list 'fn2-trace-wake-id *fn2-none*)
                              (list 'fn2-trace-wake-principal 0) (list 'fn2-trace-action-start 0)
                              (list 'fn2-trace-action-0-slot 0) (list 'fn2-trace-action-0-gen 0)
                              (list 'fn2-trace-action-1-slot 0) (list 'fn2-trace-action-1-gen 0)
                              (list 'fn2-trace-action-2-slot 0) (list 'fn2-trace-action-2-gen 0)
                              (list 'fn2-trace-action-3-slot 0) (list 'fn2-trace-action-3-gen 0)) head trace))
               (trace (fn2-cns-drain-put 'fn2-trace-head (mod (+ head 1) rows) trace))
               (trace (fn2-cns-drain-put 'fn2-trace-count
                        (if (< count rows) (+ count 1) count) trace)))
          (fn2-cns-drain-put 'fn2-trace-lost
            (if (>= count rows) (min *fn2-u60-max* (+ lost 1)) lost) trace))))))
(defun fn2-cns-query-enqueue-core-expected (owner before)
  (let* ((dir (fn2-cns-drain-child 'fn2-machines before))
         (own (fn2-cns-drain-child 'fn2-cns before))
         (slot (fn2-cns-drain-cell 'fn2-machines-slot owner dir))
         (principal (fn2-cns-drain-cell 'fn2-cns-principal-slot slot own)))
    (fn2-cns-drain-put-child 'fn2-sched
      (fn2-cns-query-sched-enqueue-expected owner principal
        (fn2-cns-drain-child 'fn2-sched before))
      (fn2-cns-drain-put-child 'fn2-trace
        (fn2-cns-query-trace-enqueue-expected owner principal
          (fn2-cns-drain-child 'fn2-trace before)) before))))

; Concrete empty-index query slice: both descriptors reference SOURCE.
; Closing one query removes exactly two refs and stores its scalar DONE
; result. Other queries, all bytes, ownership and I/O borrows are framed.
; Lookup may change only its named scratch carriers; this is not a claim
; that these carriers' lookup semantics have been independently specified.
(defun fn2-cns-query-alias-done-framep (tx source before after)
  (let* ((queries (fn2-cns-drain-child 'fn2-id-decides before))
         (pool (fn2-cns-drain-child 'fn2-pool before))
         (dir (fn2-cns-drain-child 'fn2-machines before))
         (count (fn2-cns-drain-cell 'fn2-pool-query-ref-count source pool))
         (owner (fn2-cns-drain-cell 'fn2-id-decides-qs tx queries))
         (last (equal count 2))
         (live (fn2-cns-query-owner-livep
                 (fn2-cns-drain-cell 'fn2-id-decides-qk tx queries) owner
                 (fn2-cns-drain-cell 'fn2-id-decides-qg tx queries) before))
         (queries (fn2-cns-drain-put-cells
                    (list (list 'fn2-id-decides-phase *fn2-id-decide-phase-done*)
                          (list 'fn2-id-decides-qmask 0) (list 'fn2-id-decides-qwake 0)) tx queries))
         (pool (fn2-cns-drain-put-cell 'fn2-pool-query-ref-count source (- count 2) pool))
         (slot (fn2-cns-drain-cell 'fn2-machines-slot owner dir))
         (principal (fn2-cns-drain-cell 'fn2-cns-principal-slot slot
                      (fn2-cns-drain-child 'fn2-cns before)))
         (enqueue-context (or (not (and last live))
                              (fn2-cns-query-enqueue-contextp owner principal
                                (fn2-cns-drain-child 'fn2-sched before))))
         (expected (fn2-cns-query-carry-children
                     '(fn2-succ-txns fn2-run-cursors fn2-run-paths fn2-fields) after before))
         (expected (if (and last live)
                       (fn2-cns-query-enqueue-core-expected owner expected) expected))
         (expected (fn2-cns-drain-put-child 'fn2-pool pool
                     (fn2-cns-drain-put-child 'fn2-id-decides queries expected))))
    (and (natp count) (<= 2 count) enqueue-context (equal after expected))))
