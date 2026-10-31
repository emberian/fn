; The arm vocabulary over the core children it touches (MACHINE-FORM 6.5 P2).
; Each operation here takes only the children it reads or writes, never
; fn2-core: the core's faces (core.lisp, machines-a-access.lisp) are one
; stobj-let around these, and an arm in child form calls them directly, so
; a kind's arms can be defined and proved before any core exists. Nothing
; here depends on the assembled core.
(in-package "ACL2")
(include-book "pool-ranges")
(include-book "vocab")
(include-book "exec-state")
(include-book "machines-directory")
(include-book "std/util/bstar" :dir :system)

; ----------------------------------------------------------------------
; The core's first stop reason (fn2-core-stop is its face).
(defun fn2-control-record-stop (reason fn2-control)
  (declare (xargs :stobjs fn2-control
                  :guard (and (fn2-control-wfp fn2-control) (unsigned-byte-p 8 reason))))
  (if (= (fn2-control-stop fn2-control) 1) fn2-control
    (let* ((fn2-control (update-fn2-control-stop 1 fn2-control))
           (fn2-control (update-fn2-control-stop-reason reason fn2-control)))
      fn2-control)))
(fn2-control-preserves fn2-control-record-stop (reason fn2-control) :rows nil
  :hyps ((fn2-controlp fn2-control) (fn2-control-wfp fn2-control) (unsigned-byte-p 8 reason)))

; A kind's own stop reason (defmachine :stops): the generic reason :kind,
; with the kind and the reason's index; an out-of-width pair is a :kind stop
; with neither recorded.
(defun fn2-control-record-kind-stop (kind detail fn2-control)
  (declare (xargs :stobjs fn2-control :guard (fn2-control-wfp fn2-control)))
  (if (= (fn2-control-stop fn2-control) 1) fn2-control
    (let ((fn2-control (fn2-control-record-stop *fn2-stop-reason-kind* fn2-control)))
      (if (and (unsigned-byte-p 8 kind) (unsigned-byte-p 8 detail))
          (let* ((fn2-control (update-fn2-control-stop-kind kind fn2-control))
                 (fn2-control (update-fn2-control-stop-detail detail fn2-control)))
            fn2-control)
        fn2-control))))
(fn2-control-preserves fn2-control-record-kind-stop (kind detail fn2-control) :rows nil)

; ----------------------------------------------------------------------
; Issue: validate the scalar widths before any mutation, reserve a
; descriptor, lease the range, fill and enqueue it. The only
; post-reservation refusal is the pool lease, and unreserve restores its
; row; a refusal after the reservation records its stop reason in control.
(defun fn2-core-outbox-ready (fn2-ops)
  (declare (xargs :stobjs fn2-ops :guard (fn2-ops-wfp fn2-ops)))
  (let ((capacity (fn2-ops-out-slot-length fn2-ops)))
    (and (< (fn2-ops-out-tail fn2-ops) capacity)
         (< (fn2-ops-out-tail fn2-ops) (fn2-ops-out-gen-length fn2-ops))
         (< capacity 4294967296))))

(defun fn2-core-lease (kind slot gen off len opslot opgen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (fn2-pool-wfp fn2-pool)))
  (cond ((or (equal kind *fn2-action-receive*) (equal kind *fn2-action-read*)
             (equal kind *fn2-action-entropy*))
         (fn2-pool-lease-in slot gen len opslot opgen okind oslot ogen fn2-pool))
        ((or (equal kind *fn2-action-send*) (equal kind *fn2-action-write*))
         (mv-let (code fn2-pool)
           (fn2-pool-lease-out slot gen off len okind oslot ogen fn2-pool)
           (mv code off fn2-pool)))
        (t (mv :ok 0 fn2-pool))))
(fn2-pool-preserves fn2-core-lease (kind slot gen off len opslot opgen okind oslot ogen fn2-pool) :position 2 :disable nil)
(in-theory (disable fn2-core-lease))

(defun fn2-issue-children (kind cap-index cap-nonce offset fua slot gen off len
                                may-release target-slot target-gen
                                okind oslot ogen principal fn2-pool fn2-ops fn2-control)
  (declare (xargs :stobjs (fn2-pool fn2-ops fn2-control)
                  :guard (and (fn2-pool-wfp fn2-pool) (fn2-ops-wfp fn2-ops) (fn2-control-wfp fn2-control))))
  (mv-let (stop-reason code opslot opgen fn2-pool fn2-ops)
    (b* (((unless (and (unsigned-byte-p 32 cap-index) (unsigned-byte-p 32 cap-nonce)
                       (unsigned-byte-p 60 offset) (unsigned-byte-p 1 fua)
                       (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen)
                       (unsigned-byte-p 32 off) (unsigned-byte-p 32 len)
                       (unsigned-byte-p 32 target-slot) (unsigned-byte-p 60 target-gen)))
          (mv *fn2-stop-reason-none* :bounds 0 0 fn2-pool fn2-ops))
         ((unless (fn2-core-outbox-ready fn2-ops))
          (mv *fn2-stop-reason-none* :state 0 0 fn2-pool fn2-ops))
         ((mv code opslot opgen fn2-ops)
          (fn2-op-reserve kind okind oslot ogen principal may-release fn2-ops))
         ((unless (eq code :ok)) (mv *fn2-stop-reason-none* code 0 0 fn2-pool fn2-ops))
         ((mv code actual-off fn2-pool)
          (fn2-core-lease kind slot gen off len opslot opgen okind oslot ogen fn2-pool))
         ((unless (eq code :ok))
          (mv-let (undo fn2-ops) (fn2-op-unreserve opslot opgen fn2-ops)
            (mv (if (eq undo :ok) *fn2-stop-reason-none* *fn2-stop-reason-issue-unreserve*)
                code 0 0 fn2-pool fn2-ops)))
         ((mv code fn2-ops) (fn2-op-set-range opslot opgen slot gen actual-off len fn2-ops))
         ((unless (eq code :ok))
          (mv *fn2-stop-reason-issue-range* code opslot opgen fn2-pool fn2-ops))
         ((mv code fn2-ops) (fn2-op-set-capability opslot opgen cap-index cap-nonce fn2-ops))
         ((unless (eq code :ok))
          (mv *fn2-stop-reason-issue-capability* code opslot opgen fn2-pool fn2-ops))
         ((mv code fn2-ops) (fn2-op-set-storage opslot opgen offset fua fn2-ops))
         ((unless (eq code :ok))
          (mv *fn2-stop-reason-issue-storage* code opslot opgen fn2-pool fn2-ops))
         ((mv code fn2-ops) (fn2-op-set-cancel-target opslot opgen target-slot target-gen fn2-ops))
         ((unless (eq code :ok))
          (mv *fn2-stop-reason-issue-cancel-target* code opslot opgen fn2-pool fn2-ops))
         ((mv code fn2-ops) (fn2-op-enqueue opslot opgen fn2-ops)))
      (mv (if (eq code :ok) *fn2-stop-reason-none* *fn2-stop-reason-issue-enqueue*)
          code opslot opgen fn2-pool fn2-ops))
    (let ((fn2-control (if (= stop-reason *fn2-stop-reason-none*) fn2-control
                         (fn2-control-record-stop stop-reason fn2-control))))
      (mv code opslot opgen fn2-pool fn2-ops fn2-control))))
(fn2-pool-preserves fn2-issue-children (kind cap-index cap-nonce offset fua slot gen off len
        may-release target-slot target-gen okind oslot ogen principal fn2-pool fn2-ops fn2-control)
  :carriers ((fn2-pool 3 :prefix "-POOL") (fn2-ops 4 :prefix "-OPS") (fn2-control 5 :prefix "-CONTROL")))

; One per action, with the action's own descriptor fields (core.lisp's
; fn2-core-issue-wrapper makes each one's core face).
(defmacro fn2-issue-children-wrapper (name args kind cap-index cap-nonce offset fua
                                           slot gen off len may-release target-slot target-gen)
  `(progn
     (defun ,name (,@args okind oslot ogen principal fn2-pool fn2-ops fn2-control)
       (declare (xargs :stobjs (fn2-pool fn2-ops fn2-control)
                       :guard (and (fn2-pool-wfp fn2-pool) (fn2-ops-wfp fn2-ops) (fn2-control-wfp fn2-control))))
       (fn2-issue-children ,kind ,cap-index ,cap-nonce ,offset ,fua ,slot ,gen ,off ,len
                           ,may-release ,target-slot ,target-gen okind oslot ogen principal
                           fn2-pool fn2-ops fn2-control))
     (fn2-pool-preserves ,name (,@args okind oslot ogen principal fn2-pool fn2-ops fn2-control)
       :carriers ((fn2-pool 3 :prefix "-POOL") (fn2-ops 4 :prefix "-OPS") (fn2-control 5 :prefix "-CONTROL")))))
(fn2-issue-children-wrapper fn2-issue-receive-children (cap-index cap-nonce slot gen len)
  *fn2-action-receive* cap-index cap-nonce 0 0 slot gen 0 len 0 0 0)
(fn2-issue-children-wrapper fn2-issue-send-children (cap-index cap-nonce slot gen off len may-release)
  *fn2-action-send* cap-index cap-nonce 0 0 slot gen off len may-release 0 0)
(fn2-issue-children-wrapper fn2-issue-read-children (offset slot gen len)
  *fn2-action-read* 0 0 offset 0 slot gen 0 len 0 0 0)
(fn2-issue-children-wrapper fn2-issue-write-children (offset slot gen off len fua)
  *fn2-action-write* 0 0 offset fua slot gen off len 0 0 0)
(fn2-issue-children-wrapper fn2-issue-fence-children ()
  *fn2-action-fence* 0 0 0 0 0 0 0 0 0 0 0)
(fn2-issue-children-wrapper fn2-issue-accept-children (cap-index cap-nonce)
  *fn2-action-accept* cap-index cap-nonce 0 0 0 0 0 0 0 0 0)
(fn2-issue-children-wrapper fn2-issue-close-children (cap-index cap-nonce)
  *fn2-action-close* cap-index cap-nonce 0 0 0 0 0 0 0 0 0)
(fn2-issue-children-wrapper fn2-issue-cancel-children (target-slot target-gen)
  *fn2-action-cancel* 0 0 0 0 0 0 0 0 0 target-slot target-gen)
(fn2-issue-children-wrapper fn2-issue-entropy-children (slot gen len)
  *fn2-action-entropy* 0 0 0 0 slot gen 0 len 0 0 0)

; ----------------------------------------------------------------------
; Pool range release: a release that is neither done nor retired stops the core.
(defun fn2-core-release-children (slot gen okind oslot ogen fn2-pool fn2-control)
  (declare (xargs :stobjs (fn2-pool fn2-control)
                  :guard (and (fn2-pool-wfp fn2-pool) (fn2-control-wfp fn2-control))))
  (mv-let (code fn2-pool)
    (if (fn2-pool-release-countp slot fn2-pool)
        (fn2-pool-release slot gen okind oslot ogen fn2-pool)
      (mv :corrupt fn2-pool))
    (let ((fn2-control (if (or (eq code :ok) (eq code :retired)) fn2-control
                         (fn2-control-record-stop *fn2-stop-reason-pool-release* fn2-control))))
      (mv code fn2-pool fn2-control))))
(fn2-pool-preserves fn2-core-release-children (slot gen okind oslot ogen fn2-pool fn2-control)
  :carriers ((fn2-pool 1 :prefix "-POOL") (fn2-control 2 :prefix "-CONTROL")))

; A pool slot's capacity and outstanding borrows, read by slot.
(defun fn2-pool-slot-read-code (slot fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (fn2-pool-wfp fn2-pool)))
  (if (and (natp slot) (< slot (fn2-pool-rows fn2-pool))) :ok :bounds))
(defun fn2-pool-slot-capacity (slot fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (fn2-pool-wfp fn2-pool)))
  (if (and (natp slot) (< slot (fn2-pool-rows fn2-pool))) (fn2-pool-cap slot fn2-pool) 0))
(defun fn2-pool-slot-borrows (slot fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (fn2-pool-wfp fn2-pool)))
  (if (and (natp slot) (< slot (fn2-pool-rows fn2-pool))) (fn2-pool-out-count slot fn2-pool) 0))

; A range handed between rows (D F9): the holder hands its workspace to a
; target row (fn2-pool-hand), which takes it as its own; the accept is the
; row's own, so its owner triple is the accepting row's.
(defun fn2-pool-accept-own (slot gen okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :guard (fn2-pool-wfp fn2-pool)))
  (fn2-pool-accept-hand slot gen okind oslot ogen fn2-pool))
(fn2-pool-preserves fn2-pool-accept-own (slot gen okind oslot ogen fn2-pool) :position 1)

; ----------------------------------------------------------------------
; The directory's checked writes: a write the directory cannot take (an id
; outside it, a value wider than its column) stops the core, as the core's
; dispatchers do (fn2-machine-write-F, fn2-machine-set-F of a scalar).
(defun fn2-machines-stop-write (fn2-machines fn2-control)
  (declare (xargs :stobjs (fn2-machines fn2-control) :guard (fn2-control-wfp fn2-control)))
  (let ((fn2-control (fn2-control-record-stop *fn2-stop-reason-machine-write* fn2-control)))
    (mv fn2-machines fn2-control)))
(defmacro fn2-machines-checked (ok write)
  `(if ,ok (let ((fn2-machines ,write)) (mv fn2-machines fn2-control))
     (fn2-machines-stop-write fn2-machines fn2-control)))
(defmacro fn2-machines-row-ok (id)
  `(and (natp ,id) (< ,id (fn2-machines-rows fn2-machines))))

; The resource FIFOs: a row parks at the tail through its own ready links,
; and a grant takes the head (fn2-machine-wait-queue makes the core faces).
; ORD: the queue is one per admitted kind, indexed by its ordinal.
(defmacro fn2-machines-wait-queue (park grant head tail reason &optional ords)
  (let* ((arr (and ords t))
         (get-head (if arr `(,(fn2-columns-sym 'fn2-machines- (concatenate 'string (symbol-name head) "I")) ord fn2-machines)
                     `(,(fn2-columns-sym 'fn2-machines- (symbol-name head)) fn2-machines)))
         (get-tail (if arr `(,(fn2-columns-sym 'fn2-machines- (concatenate 'string (symbol-name tail) "I")) ord fn2-machines)
                     `(,(fn2-columns-sym 'fn2-machines- (symbol-name tail)) fn2-machines)))
         (set-head (if arr (fn2-columns-sym 'update-fn2-machines- (concatenate 'string (symbol-name head) "I"))
                     (fn2-columns-sym 'update-fn2-machines- (symbol-name head))))
         (set-tail (if arr (fn2-columns-sym 'update-fn2-machines- (concatenate 'string (symbol-name tail) "I"))
                     (fn2-columns-sym 'update-fn2-machines- (symbol-name tail))))
         (ord-ok (if arr '((natp ord) (< ord *fn2-machine-admitted-max*)) nil)))
    `(progn
       (defun ,park (id ,@ords fn2-machines fn2-control)
         (declare (xargs :stobjs (fn2-machines fn2-control)
                         :guard (and (fn2-machines-wfp fn2-machines) (fn2-control-wfp fn2-control))))
         (if (not (and (fn2-machines-row-ok id) ,@ord-ok (unsigned-byte-p 32 ,get-tail)))
             (fn2-machines-stop-write fn2-machines fn2-control)
           (if (equal (fn2-machines-wait-reason id fn2-machines) ,reason) (mv fn2-machines fn2-control)
             (let* ((tail ,get-tail)
                    (fn2-machines (fn2-machines-set-wait-reason id ,reason fn2-machines))
                    (fn2-machines (fn2-machines-set-ready-prev id tail fn2-machines))
                    (fn2-machines (fn2-machines-set-ready-next id *fn2-none* fn2-machines)))
               (mv-let (fn2-machines fn2-control)
                 (if (equal tail *fn2-none*)
                     (fn2-machines-checked (unsigned-byte-p 32 id) (,set-head ,@ords id fn2-machines))
                   (fn2-machines-checked (and (unsigned-byte-p 32 id) (fn2-machines-row-ok tail))
                                         (fn2-machines-set-ready-next tail id fn2-machines)))
                 (fn2-machines-checked (unsigned-byte-p 32 id) (,set-tail ,@ords id fn2-machines)))))))
       (fn2-machines-preserves ,park (id ,@ords fn2-machines fn2-control)
         :carriers ((fn2-machines 0 :prefix "-MACHINES") (fn2-control 1 :prefix "-CONTROL")))
       (defthm ,(fn2-columns-sym park "-ROWS")
         (equal (fn2-machines-rows (car (,park id ,@ords fn2-machines fn2-control)))
                (fn2-machines-rows fn2-machines))
         :hints (("Goal" :in-theory (enable ,park))))
       (defthm ,(fn2-columns-sym park "-RAW-ROWS")
         (equal (nth *fn2-machines-rows* (car (,park id ,@ords fn2-machines fn2-control)))
                (nth *fn2-machines-rows* fn2-machines))
         :hints (("Goal" :in-theory (enable ,park))))
       (defun ,grant (,@ords fn2-machines fn2-control)
         (declare (xargs :stobjs (fn2-machines fn2-control)
                         :guard (and (fn2-machines-wfp fn2-machines) (fn2-control-wfp fn2-control))))
         (if (not (and ,@ord-ok))
             (mv-let (fn2-machines fn2-control) (fn2-machines-stop-write fn2-machines fn2-control)
               (mv *fn2-none* fn2-machines fn2-control))
           (let ((id ,get-head))
             (if (equal id *fn2-none*) (mv id fn2-machines fn2-control)
               (if (not (fn2-machines-row-ok id))
                   (mv-let (fn2-machines fn2-control) (fn2-machines-stop-write fn2-machines fn2-control)
                     (mv *fn2-none* fn2-machines fn2-control))
                 (let ((next (fn2-machines-ready-next id fn2-machines)))
                   (mv-let (fn2-machines fn2-control)
                     (fn2-machines-checked (unsigned-byte-p 32 next) (,set-head ,@ords next fn2-machines))
                     (mv-let (fn2-machines fn2-control)
                       (if (equal next *fn2-none*)
                           (fn2-machines-checked t (,set-tail ,@ords *fn2-none* fn2-machines))
                         (fn2-machines-checked (fn2-machines-row-ok next)
                                               (fn2-machines-set-ready-prev next *fn2-none* fn2-machines)))
                       (let* ((fn2-machines (fn2-machines-set-wait-reason id *fn2-wait-none* fn2-machines))
                              (fn2-machines (fn2-machines-set-ready-prev id *fn2-none* fn2-machines))
                              (fn2-machines (fn2-machines-set-ready-next id *fn2-none* fn2-machines)))
                         (mv id fn2-machines fn2-control))))))))))
       (fn2-machines-preserves ,grant (,@ords fn2-machines fn2-control)
         :carriers ((fn2-machines 1 :prefix "-MACHINES") (fn2-control 2 :prefix "-CONTROL"))))))
(fn2-machines-wait-queue fn2-machines-park fn2-machines-grant-op wait-head wait-tail *fn2-wait-operation*)
(fn2-machines-wait-queue fn2-machines-park-admission fn2-machines-grant-admission
                         admission-head admission-tail *fn2-wait-connection-row* (ord))

; The singleton pool waiter: the row parks on :storage-window (its class in
; its own cursor field, written by its kind's checked write).
(defun fn2-machines-park-pool (id fn2-machines fn2-control)
  (declare (xargs :stobjs (fn2-machines fn2-control)
                  :guard (and (fn2-machines-wfp fn2-machines) (fn2-control-wfp fn2-control))))
  (if (not (fn2-machines-row-ok id)) (mv fn2-machines fn2-control)
    (let ((fn2-machines (fn2-machines-set-wait-reason id *fn2-wait-storage-window* fn2-machines)))
      (fn2-machines-checked (unsigned-byte-p 32 id) (update-fn2-machines-pool-wait-id id fn2-machines)))))
(fn2-machines-preserves fn2-machines-park-pool (id fn2-machines fn2-control)
  :carriers ((fn2-machines 0 :prefix "-MACHINES") (fn2-control 1 :prefix "-CONTROL")))
(defthm fn2-machines-park-pool-rows
  (equal (fn2-machines-rows (car (fn2-machines-park-pool id fn2-machines fn2-control)))
         (fn2-machines-rows fn2-machines))
  :hints (("Goal" :in-theory (enable fn2-machines-park-pool))))
(defthm fn2-machines-park-pool-raw-rows
  (equal (nth *fn2-machines-rows* (car (fn2-machines-park-pool id fn2-machines fn2-control)))
         (nth *fn2-machines-rows* fn2-machines))
  :hints (("Goal" :in-theory (enable fn2-machines-park-pool))))

; An admitted kind's partition (D 4.5), by its ordinal ORD.
(defun fn2-machines-free-head-of (ord fn2-machines)
  (declare (xargs :stobjs fn2-machines :guard (fn2-machines-wfp fn2-machines)))
  (if (and (natp ord) (< ord *fn2-machine-admitted-max*)) (fn2-machines-free-headi ord fn2-machines) *fn2-none*))
; A drained row returns to its partition's free chain with its credit,
; unless it retires; a reclaim with no active row of the partition is a
; caller's bug and stops the core before any partition field changes.
(defun fn2-machines-reclaim (id ord retire fn2-machines fn2-control)
  (declare (xargs :stobjs (fn2-machines fn2-control)
                  :guard (and (fn2-machines-wfp fn2-machines) (fn2-control-wfp fn2-control))))
  (if (not (and (natp ord) (< ord *fn2-machine-admitted-max*)))
      (fn2-machines-stop-write fn2-machines fn2-control)
    (let ((active (fn2-machines-active-counti ord fn2-machines)))
      (if (zp active) (fn2-machines-stop-write fn2-machines fn2-control)
        (mv-let (fn2-machines fn2-control)
          (if retire (mv fn2-machines fn2-control)
            (fn2-machines-checked (unsigned-byte-p 32 id) (update-fn2-machines-free-headi ord id fn2-machines)))
          (mv-let (fn2-machines fn2-control)
            (if retire (mv fn2-machines fn2-control)
              (let ((credits (+ 1 (fn2-machines-admission-creditsi ord fn2-machines))))
                (fn2-machines-checked (unsigned-byte-p 32 credits)
                                      (update-fn2-machines-admission-creditsi ord credits fn2-machines))))
            (fn2-machines-checked (unsigned-byte-p 32 (- active 1))
                                  (update-fn2-machines-active-counti ord (- active 1) fn2-machines))))))))
(fn2-machines-preserves fn2-machines-reclaim (id ord retire fn2-machines fn2-control)
  :carriers ((fn2-machines 0 :prefix "-MACHINES") (fn2-control 1 :prefix "-CONTROL")))
(defthm fn2-machines-reclaim-rows
  (equal (fn2-machines-rows (car (fn2-machines-reclaim id ord retire fn2-machines fn2-control)))
         (fn2-machines-rows fn2-machines))
  :hints (("Goal" :in-theory (enable fn2-machines-reclaim))))
(defthm fn2-machines-reclaim-raw-rows
  (equal (nth *fn2-machines-rows* (car (fn2-machines-reclaim id ord retire fn2-machines fn2-control)))
         (nth *fn2-machines-rows* fn2-machines))
  :hints (("Goal" :in-theory (enable fn2-machines-reclaim))))

; Wake another row (the arm language's :wake-row): the directory's single
; wake slot takes the row if it is one; anything else is no wake.
(defun fn2-machines-wake-row (id fn2-machines fn2-control)
  (declare (xargs :stobjs (fn2-machines fn2-control)
                  :guard (and (fn2-machines-wfp fn2-machines) (fn2-control-wfp fn2-control))))
  (if (not (fn2-machines-row-ok id)) (mv fn2-machines fn2-control)
    (fn2-machines-checked (unsigned-byte-p 32 id) (update-fn2-machines-wake-id id fn2-machines))))
(fn2-machines-preserves fn2-machines-wake-row (id fn2-machines fn2-control)
  :carriers ((fn2-machines 0 :prefix "-MACHINES") (fn2-control 1 :prefix "-CONTROL")))
(defthm fn2-machines-wake-row-rows
  (equal (fn2-machines-rows (car (fn2-machines-wake-row id fn2-machines fn2-control)))
         (fn2-machines-rows fn2-machines))
  :hints (("Goal" :in-theory (enable fn2-machines-wake-row))))
(defthm fn2-machines-wake-row-raw-rows
  (equal (nth *fn2-machines-rows* (car (fn2-machines-wake-row id fn2-machines fn2-control)))
         (nth *fn2-machines-rows* fn2-machines))
  :hints (("Goal" :in-theory (enable fn2-machines-wake-row))))

(assert-event
 (fn2-assert-compliant-p
  '(fn2-machines-free-head-of fn2-machines-reclaim fn2-machines-wake-row) (w state)))
(assert-event
 (fn2-assert-compliant-p
  '(fn2-control-record-stop fn2-issue-children fn2-core-release-children
    fn2-pool-slot-read-code fn2-pool-slot-capacity fn2-pool-slot-borrows
    fn2-machines-park fn2-machines-grant-op fn2-machines-park-admission
    fn2-machines-grant-admission fn2-machines-park-pool) (w state)))
