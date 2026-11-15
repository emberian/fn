; The native image machine through the same turn and storage adapter as
; recovery-article-unit. The held fence is a negative listener-release control.
(in-package "ACL2")
(include-book "../books/node-profile")
(include-book "../books/owed-conn")

(defun fn2-bu-accept-count (n i fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil :measure (nfix n)))
 (if (zp n) 0
  (+ (stobj-let ((fn2-ops (fn2-core-ops fn2-core))) (yes)
      (if (and (< (nfix i) (fn2-ops-rows fn2-ops))
               (equal (fn2-ops-kind (nfix i) fn2-ops) *fn2-action-accept*)
               (not (equal (fn2-ops-phase (nfix i) fn2-ops) *fn2-op-phase-free*))) 1 0) yes)
     (fn2-bu-accept-count (- n 1) (+ 1 (nfix i)) fn2-core))))

(defun fn2-bu-to-fence (fuel store fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil :measure (nfix fuel)))
 (if (zp fuel) (mv :fuel store fn2-core)
  (b* (((mv & & & & fn2-core) (fn2-turn fn2-core))
       (fence (stobj-let ((fn2-ops (fn2-core-ops fn2-core))) (yes)
               (mv-let (code op gen) (fn2-outbox-peek 0 fn2-ops)
                (declare (ignore gen))
                (and (eq code :ok) (equal (fn2-ops-kind op fn2-ops) *fn2-action-fence*))) yes))
       ((when fence) (mv :held store fn2-core))
       ((when (not (equal (fn2-core-stop-reason fn2-core) 0))) (mv :failed store fn2-core))
       ((mv & & & store fn2-core) (fn2-cw-adapter-one 0 nil store fn2-core)))
   (fn2-bu-to-fence (- fuel 1) store fn2-core))))

(defun fn2-bu-start (create store)
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-core
  (mv-let (result fn2-core)
   (b* ((fn2-core (fn2-init-executor (fn2-image-profile *fn2-node-profile*) :echo nil fn2-core))
        ((mv start fn2-core) (fn2-boot-start create 33554432 fn2-core))
        ((mv held store fn2-core) (fn2-bu-to-fence 100000 store fn2-core))
        (pre (list start held (fn2-boot-status fn2-core) (fn2-bu-accept-count 32 0 fn2-core)))
        ((mv & & & store fn2-core) (if (eq held :held) (fn2-cw-adapter-one 0 nil store fn2-core)
                                   (mv nil 0 nil store fn2-core)))
        ((mv quiet & store fn2-core) (fn2-cw-loop 100000 0 0 nil store fn2-core))
        (epoch (stobj-let ((fn2-extents (fn2-core-extents fn2-core))) (e)
                 (fn2-alloc-current-epoch fn2-extents) e)))
    (mv (list pre quiet (fn2-boot-status fn2-core) epoch store (fn2-core-stop-reason fn2-core) (fn2-bu-accept-count 32 0 fn2-core)) fn2-core))
   result)))

(assert-event (eq (fn2-image-create-request 1 *fn2-node-profile*) :geometry))
(assert-event (eq (fn2-image-create-request 33554432 *fn2-node-profile*) :ok))

; Attachments are executable observations, not logical DEFCONST values.
(assert-event
 (let* ((created (fn2-bu-start t nil))
        (opened (fn2-bu-start nil (nth 4 created)))
        (reopened (fn2-bu-start nil (nth 4 opened)))
        (empty (fn2-bu-start nil nil))
        (bad-anchor (fn2-bu-start nil (cons (cons (- 33554432 8192) :corrupt) (nth 4 created)))))
  (or (and (equal (take 4 created) '((:ok :held :booting 0) :quiet :ready 1))
           (equal (take 4 opened) '((:ok :held :booting 0) :quiet :ready 2))
           (equal (take 4 reopened) '((:ok :held :booting 0) :quiet :ready 3))
           (posp (nth 6 created)) (posp (nth 6 opened)) (posp (nth 6 reopened))
           (equal (nth 2 empty) :failed) (equal (nth 3 (car empty)) 0)
           (equal (nth 2 bad-anchor) :failed) (equal (nth 3 (car bad-anchor)) 0))
      (cw "boot-unit created/opened/reopened/empty/bad-anchor ~x0~%"
          (list (append (take 4 created) (nthcdr 5 created))
                (append (take 4 opened) (nthcdr 5 opened))
                (append (take 4 reopened) (nthcdr 5 reopened))
                (append (take 4 empty) (nthcdr 5 empty))
                (append (take 4 bad-anchor) (nthcdr 5 bad-anchor)))))))

; Process-death cut on a previously READY image: its next epoch Write has
; completed through the real adapter, while the actual epoch Fence remains
; queued and unacknowledged. The two stores model loss/survival of that Write;
; this adapter does not itself claim power-failure persistence semantics.
(defun fn2-bu-epoch-op-p (kind fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (let* ((id (fn2-machine-kind-base *fn2-boot-kind* fn2-core))
        (ogen (fn2-machine-generation id fn2-core)))
  (and (eq (fn2-boot-snapshot-read-code id fn2-core) :ok)
       (= (fn2-machine-stage id fn2-core) 3)
       (= (fn2-machine-pending id fn2-core) 1)
       (= (fn2-machine-phase id fn2-core)
          (if (= kind *fn2-action-write*) *fn2-boot-state-write-result* *fn2-boot-state-epoch-result*))
       (stobj-let ((fn2-ops (fn2-core-ops fn2-core))) (yes)
        (mv-let (code op gen) (fn2-outbox-peek 0 fn2-ops)
         (declare (ignore gen))
         (and (eq code :ok) (= (fn2-ops-kind op fn2-ops) kind)
              (= (fn2-ops-owner-kind op fn2-ops) *fn2-boot-kind*)
              (= (fn2-ops-owner-slot op fn2-ops) id)
              (= (fn2-ops-owner-gen op fn2-ops) ogen))) yes))))
(defun fn2-bu-to-epoch-op (fuel kind store fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil :measure (nfix fuel)))
 (if (zp fuel) (mv :fuel store fn2-core)
  (b* (((mv & & & & fn2-core) (fn2-turn fn2-core))
       ((when (> (fn2-bu-accept-count 32 0 fn2-core) 0)) (mv :early-accept store fn2-core))
       ((when (fn2-bu-epoch-op-p kind fn2-core)) (mv :held store fn2-core))
       ((when (not (= (fn2-core-stop-reason fn2-core) 0))) (mv :failed store fn2-core))
       ((mv & & & store fn2-core) (fn2-cw-adapter-one 0 nil store fn2-core)))
   (fn2-bu-to-epoch-op (- fuel 1) kind store fn2-core))))
(defun fn2-bu-held-fence-turns (fuel fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil :measure (nfix fuel)))
 (if (zp fuel) (mv t fn2-core)
  (b* (((mv & & & & fn2-core) (fn2-turn fn2-core))
       (id (fn2-machine-kind-base *fn2-boot-kind* fn2-core))
       (closed (and (fn2-bu-epoch-op-p *fn2-action-fence* fn2-core)
                    (= (fn2-machine-event-ready id fn2-core) 0)
                    (= (fn2-bu-accept-count 32 0 fn2-core) 0)
                    (= (fn2-core-stop-reason fn2-core) 0)
                    (eq (fn2-boot-status fn2-core) :booting)
                    (stobj-let ((fn2-extents (fn2-core-extents fn2-core))) (closed)
                     (= (fn2-alloc-epoch-begun fn2-extents) 0) closed))))
   (if closed (fn2-bu-held-fence-turns (- fuel 1) fn2-core) (mv nil fn2-core)))))
(defun fn2-bu-epoch-write-cut (store)
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-core
  (mv-let (answer fn2-core)
   (b* ((fn2-core (fn2-init-executor (fn2-image-profile *fn2-node-profile*) :echo nil fn2-core))
        ((mv start fn2-core) (fn2-boot-start nil 33554432 fn2-core))
        ((mv write-held before fn2-core) (fn2-bu-to-epoch-op 100000 *fn2-action-write* store fn2-core))
        (id (fn2-machine-kind-base *fn2-boot-kind* fn2-core))
        (next (fn2-machine-next-epoch id fn2-core))
        (pre (and (eq start :ok) (eq write-held :held)
                  (fn2-bu-epoch-op-p *fn2-action-write* fn2-core)
                  (= (fn2-bu-accept-count 32 0 fn2-core) 0)))
        ; This is the actual queued Write's sole adapter completion, not an
        ; invented result or caller-provided epoch/ACK.
        ((mv wrote & & survived fn2-core) (if pre (fn2-cw-adapter-one 0 nil before fn2-core)
                                         (mv nil 0 nil before fn2-core)))
        ((mv held survived fn2-core) (fn2-bu-to-epoch-op 100000 *fn2-action-fence* survived fn2-core))
        ((mv closed fn2-core) (fn2-bu-held-fence-turns 8 fn2-core)))
    (mv (list (and pre wrote (eq held :held) closed
                   (fn2-bu-epoch-op-p *fn2-action-fence* fn2-core)
                   (equal (cdr survived) before)) next before survived) fn2-core))
   answer)))
; The local cut core dies with its Fence still pending. Both reopen branches
; instantiate fresh cores and drive actual anchor reads/epoch Write/Fence.
(assert-event
 (let* ((created (fn2-bu-start t nil))
        (cut (fn2-bu-epoch-write-cut (nth 4 created)))
        (lost (fn2-bu-start nil (nth 2 cut)))
        (survived (fn2-bu-start nil (nth 3 cut)))
        (lost-again (fn2-bu-start nil (nth 4 lost)))
        (survived-again (fn2-bu-start nil (nth 4 survived))))
  (or (and (equal (take 4 created) '((:ok :held :booting 0) :quiet :ready 1))
           (car cut) (= (nth 1 cut) 2)
           (equal (take 4 lost) '((:ok :held :booting 0) :quiet :ready 2))
           (equal (take 4 survived) '((:ok :held :booting 0) :quiet :ready 3))
           (equal (take 4 lost-again) '((:ok :held :booting 0) :quiet :ready 3))
           (equal (take 4 survived-again) '((:ok :held :booting 0) :quiet :ready 4))
           (posp (nth 6 lost)) (posp (nth 6 survived))
           (posp (nth 6 lost-again)) (posp (nth 6 survived-again)))
      (cw "boot epoch Write/Fence cut ~x0~%"
          (list (take 2 cut) (take 4 lost) (take 4 survived)
                (take 4 lost-again) (take 4 survived-again))))))

; Proof boundary: this exercises the actual image boot/adapter ordering and
; both Write survival alternatives. It is not a theorem that arbitrary WFP
; cores or arbitrary authenticated disk histories were produced by that
; protocol. The outstanding connected invariant must relate persisted epoch
; anchors after their successful Fence to every issued allocation epoch and
; then to the maximum accepted by recovery. Generic logical test environments
; can call fn2-env-begin-epoch directly, so their WFP alone is insufficient.
