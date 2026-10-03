; SCN-1082: executable schedules using the actual direct host-called read
; entries and their holder effects. These are reachable schedule witnesses,
; not the owed all-schedules/HM-to-native realization theorem (PRF-1254).
(in-package "ACL2")
(include-book "../../books/host-model-machine")

(defun hmct-prefixes-okp (st sched)
  (declare (xargs :guard t :measure (acl2-count sched)))
  (and (fn-hmc-invp st)
       (if (consp sched)
           (hmct-prefixes-okp (fn-hmc-next-state st (car sched)) (cdr sched))
         t)))

(defconst *hmct-token-a* '(0 7 1 0 10 7))
(defconst *hmct-token-b* '(1 7 2 0 10 8))
(defconst *hmct-issued-schedule*
  '((:fd-open 2 1 9) (:acquire 2 :owner) (:acquire 2 :extent)
    (:issue 2 7 1 0 10 7)))
(defconst *hmct-issued* (fn-hmc-run (fn-hmc-init) *hmct-issued-schedule*))

(assert-event
 (and (hmct-prefixes-okp (fn-hmc-init) *hmct-issued-schedule*)
      (equal (fn-hmc-holds *hmct-issued*) (list (list 1 *hmct-token-a*)))
      (equal (fn-hmc-next *hmct-issued*) 1)
      (equal (fn-hmc-worker-token (fn-hmc-worker-of *hmct-token-a*
                                  (fn-hmc-workers *hmct-issued*))) *hmct-token-a*)))

; Complete host-called producer result: model projection agrees with all
; seven actual admit outputs, including the issued and holder effects.
(assert-event
 (let* ((before (fn-hmc-run (fn-hmc-init)
                          '((:fd-open 2 1 9) (:acquire 2 :owner) (:acquire 2 :extent))))
        (r (mv-list 7 (fn-pio-direct-admit 0 7 1 0 10 7
                       (fn-hmc-idle-worker (fn-hmc-workers before)) nil nil))))
   (and (equal (fn-hmc-answer before '(:issue 2 7 1 0 10 7))
               (list (nth 0 r) (nth 2 r)))
        (equal (fn-hmc-next *hmct-issued*) (nth 1 r))
        (equal (fn-hmc-rows *hmct-issued*) (fn-pio-issued-rows (nth 5 r)))
        (equal (fn-hmc-holds *hmct-issued*) (nth 6 r))
        (equal (fn-hmc-worker-of *hmct-token-a* (fn-hmc-workers *hmct-issued*))
               (nth 4 r)))))

; A cancelled operation, already physically reading, survives retirement.
; Logical generation release does not close the descriptor the read holds.
(defconst *hmct-cancel-schedule*
  '((:io-begin 8 (0 7 1 0 10 7)) (:cancel 2 (0 7 1 0 10 7))
    (:acquire 2 :pins) (:retire 2 (1)) (:release-retired 2)))
(defconst *hmct-cancelled* (fn-hmc-run *hmct-issued* *hmct-cancel-schedule*))
(assert-event
 (and (hmct-prefixes-okp *hmct-issued* *hmct-cancel-schedule*)
      (equal (fn-hmc-row-phase (fn-hmc-row-of *hmct-token-a*
                                (fn-hmc-rows *hmct-cancelled*))) :cancelled)
      (equal (fn-hmc-holds *hmct-cancelled*) (fn-hmc-holds *hmct-issued*))
      (equal (fn-hmc-released *hmct-cancelled*) '(1))
      (equal (fn-hmc-answer *hmct-cancelled* '(:close 2 1)) :refused)
      (equal (fn-hmc-next-state *hmct-cancelled* '(:close 2 1)) *hmct-cancelled*)
      (equal (fn-hmc-answer *hmct-cancelled* '(:fd-open 3 2 9)) :refused)
      (equal (fn-hmc-answer *hmct-cancelled* '(:settle 2 (0 7 1 0 10 7))) :refused)
      (equal (fn-hmc-fd-inc 9 (fn-hmc-fds *hmct-cancelled*)) 1)))

; Physical return alone does not erase the ownership row. The owner's
; returned-worker settlement consumes the same token and removes its hold.
(defconst *hmct-return-schedule*
  '((:io-complete (0 7 1 0 10 7) :ok) (:return 2 (0 7 1 0 10 7))))
(defconst *hmct-returned* (fn-hmc-run *hmct-cancelled* *hmct-return-schedule*))
(assert-event
 (and (hmct-prefixes-okp *hmct-cancelled* *hmct-return-schedule*)
      (equal (fn-hmc-answer *hmct-returned* '(:close 2 1)) :refused)
      (equal (fn-hmc-answer *hmct-returned* '(:settle 2 (0 7 1 0 10 7))) :cancelled)))
(defconst *hmct-settled* (fn-hmc-next-state *hmct-returned*
                           '(:settle 2 (0 7 1 0 10 7))))
(assert-event
 (let ((r (mv-list 5
           (fn-pio-direct-settle *hmct-token-a*
             (fn-hmc-worker-of *hmct-token-a* (fn-hmc-workers *hmct-returned*)) :ok
             (fn-hmc-issued (fn-hmc-rows *hmct-returned*)) (fn-hmc-holds *hmct-returned*)))))
   (and (fn-hmc-invp *hmct-settled*)
        (equal (nth 0 r) :cancelled)
        (equal (fn-hmc-rows *hmct-settled*) (fn-pio-issued-rows (nth 3 r)))
        (equal (fn-hmc-holds *hmct-settled*) (nth 4 r))
        (member-equal (nth 2 r) (fn-hmc-workers *hmct-settled*))
        (null (fn-hmc-rows *hmct-settled*)) (null (fn-hmc-holds *hmct-settled*))
        (equal (fn-hmc-answer *hmct-settled* '(:settle 2 (0 7 1 0 10 7))) :refused)
        (equal (fn-hmc-next-state *hmct-settled* '(:settle 2 (0 7 1 0 10 7))) *hmct-settled*))))

; Only now can fd9 be closed and rebound to incarnation2. CID7 and the
; worker are reused, but replaying the old token cannot settle the new draw.
(defconst *hmct-reuse-schedule*
  '((:close 2 1) (:fd-open 3 2 9) (:issue 2 7 2 0 10 8)
    (:io-begin 8 (1 7 2 0 10 8))))
(defconst *hmct-reused* (fn-hmc-run *hmct-settled* *hmct-reuse-schedule*))
(assert-event
 (and (hmct-prefixes-okp *hmct-settled* *hmct-reuse-schedule*)
      (equal (fn-hmc-fd-inc 9 (fn-hmc-fds *hmct-reused*)) 2)
      (equal (fn-hmc-req-inc (fn-hmc-req-of *hmct-token-b* (fn-hmc-reqs *hmct-reused*))) 2)
      (equal (fn-hmc-answer *hmct-reused* '(:io-complete (0 7 1 0 10 7) :ok)) :stale)
      (equal (fn-hmc-next-state *hmct-reused* '(:settle 2 (0 7 1 0 10 7))) *hmct-reused*)
      (equal (fn-hmc-holds *hmct-reused*) (list (list 2 *hmct-token-b*)))))

; An error arriving after cancellation remains a fault, not a cancelled
; success. It nevertheless settles exactly its own physical custody.
(defconst *hmct-error*
  (fn-hmc-run *hmct-cancelled*
              '((:io-complete (0 7 1 0 10 7) :error) (:return 2 (0 7 1 0 10 7)))))
(assert-event
 (and (equal (fn-hmc-answer *hmct-error* '(:settle 2 (0 7 1 0 10 7))) '(:fault :error))
      (fn-hmc-invp (fn-hmc-next-state *hmct-error* '(:settle 2 (0 7 1 0 10 7))))
      (null (fn-hmc-holds (fn-hmc-next-state *hmct-error* '(:settle 2 (0 7 1 0 10 7)))))))

; Unfunded direct labels do not pretend to cover the typed funded pool.
(assert-event
 (equal (fn-hmc-answer *hmct-issued* '(:funded-issue 2 7 1 0 10 7)) :refused))

; The actual native short-read producer stores literal :READ. There is no
; host/Python translation to a different model error vocabulary.
(assert-event
 (let* ((returned (fn-hmc-run *hmct-cancelled*
                    '((:io-complete (0 7 1 0 10 7) :read)
                      (:return 2 (0 7 1 0 10 7)))))
        (settled (fn-hmc-next-state returned '(:settle 2 (0 7 1 0 10 7)))))
   (and (equal (fn-hmc-answer returned '(:settle 2 (0 7 1 0 10 7))) '(:fault :read))
        (fn-hmc-invp returned) (fn-hmc-invp settled)
        (null (fn-hmc-holds settled)))))

; PRF-1254 physical-return preservation: a reachable positive witness
; checks the complete invariant antecedent and the literal conclusion,
; including the existing read token and ownership retained after return.
(assert-event
 (let* ((ready (fn-hmc-next-state *hmct-cancelled*
                 '(:io-complete (0 7 1 0 10 7) :ok)))
        (r (mv-list 2 (fn-hmc-do-return ready '(:return 2 (0 7 1 0 10 7))))))
   (and (fn-hmc-invp ready)
        (fn-hmc-invp (car r))
        (equal (cadr r) :returned)
        (equal (fn-hmc-holds (car r)) (fn-hmc-holds ready))
        (equal (fn-hmc-rows (car r)) (fn-hmc-rows ready))
        (equal (fn-hmc-worker-phase
                 (fn-hmc-worker-of *hmct-token-a* (fn-hmc-workers (car r))))
               :returned))))

; Hypothesis removal, deliberately corrupted state: with the invariant
; omitted, a refused physical return cannot repair invalid lock storage.
(assert-event
 (let* ((broken (fn-hmc-set 0 :corrupted-locks (fn-hmc-init)))
        (r (mv-list 2 (fn-hmc-do-return broken '(:return 2 (0 7 1 0 10 7))))))
   (and (not (fn-hmc-invp broken))
        (not (fn-hmc-invp (car r)))
        (equal (cadr r) :refused)
        (equal (car r) broken))))
