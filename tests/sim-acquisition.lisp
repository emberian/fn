; D0's exhaustion and cancellation scenarios, one per bundle that exists in
; layer A today (resources.lisp, *fn2-resource-bundles* :status :exists).
; Each scenario runs the real assembled core through the adapter boundary
; the simulator drives (fn2-outbox-ack, fn2-post-result, harvest and
; observation routing, fn2-machine-run, the grant service), in tiny
; profiles, exhausting one kind of the bundle at a time by profile capacity
; or by pre-occupying its units through the real exports. A check is
; (bundle name pass); a bundle passes when every check passes. Bundles
; marked :owed-by :r6b are expected to fail; the driver
; (tests/sim-acquisition-driver.lsp) fails when one passes, or when an
; un-owed bundle fails, and so does this book's final assertion.
(in-package "ACL2")
(include-book "../books/resources-owed")

; ------------------------------------------------------------------------
; Census: every free count of a kind A tracks in the core. Accept credits
; are rows (static); the fence slot is adapter-side (no core count).
(defun fn2-acq-census (fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (let ((credits (fn2-machine-admission-credits *fn2-echo-admission-ordinal* fn2-core)))
    (stobj-let ((fn2-pool (fn2-core-pool fn2-core))
                (fn2-ops (fn2-core-ops fn2-core)))
      (c0 c1 free out)
      (mv (fn2-pool-class-countsi 0 fn2-pool) (fn2-pool-class-countsi 1 fn2-pool)
          (fn2-ops-free-count fn2-ops) (fn2-ops-outbox-credits fn2-ops))
      (list (cons :connection-row credits) (cons :class0 c0) (cons :class1 c1)
            (cons :operation free) (cons :outbox out)))))

; The census difference after - before, by named count.
(defun fn2-acq-delta (before after)
  (declare (xargs :verify-guards nil))
  (if (atom before) nil
    (cons (cons (caar before) (- (nfix (cdr (assoc-equal (caar before) after))) (nfix (cdar before))))
          (fn2-acq-delta (cdr before) after))))
(defun fn2-acq-zero-delta (names)
  (declare (xargs :verify-guards nil))
  (if (atom names) nil (cons (cons (car names) 0) (fn2-acq-zero-delta (cdr names)))))
(defconst *fn2-acq-counts* '(:connection-row :class0 :class1 :operation :outbox))
; The expected delta of acquiring KINDS (each one unit), for the counts named.
(defun fn2-acq-expect (changes)
  (declare (xargs :verify-guards nil))
  (if (atom changes) (fn2-acq-zero-delta *fn2-acq-counts*)
    (put-assoc-equal (caar changes) (cdar changes) (fn2-acq-expect (cdr changes)))))
(defun fn2-acq-same-delta (delta expect)
  (declare (xargs :verify-guards nil))
  (if (atom expect) t
    (and (equal (cdr (assoc-equal (caar expect) delta)) (cdar expect))
         (fn2-acq-same-delta delta (cdr expect)))))

; ------------------------------------------------------------------------
; The adapter boundary. Take the outbox head (the adapter acknowledges it),
; post a completion into its reserved cell, deliver one posted result the
; way fn2-exec-harvest does.
(defun fn2-acq-take (fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (stobj-let ((fn2-ops (fn2-core-ops fn2-core)))
    (code slot gen fn2-ops)
    (mv-let (code slot gen) (fn2-outbox-peek 0 fn2-ops)
      (if (not (eq code :ok)) (mv code 0 0 fn2-ops)
        (mv-let (code fn2-ops) (fn2-outbox-ack 1 fn2-ops) (mv code slot gen fn2-ops))))
    (mv code slot gen fn2-core)))
(defun fn2-acq-post (cell op opgen event outcome reason count aux0 fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (stobj-let ((fn2-ops (fn2-core-ops fn2-core)))
    (fn2-ops) (fn2-post-result cell op opgen event outcome reason count aux0 0 fn2-ops)
    fn2-core))
(defun fn2-acq-deliver (fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* (((mv ownerp kind id gen &) (fn2-core-next-owner fn2-core))
       ((unless ownerp) (mv nil fn2-core))
       ((mv delivered & & & event outcome reason count aux0 aux1 fn2-core) (fn2-harvest-one fn2-core))
       ((unless delivered) (mv nil fn2-core))
       ((mv & fn2-core) (fn2-machine-observe kind id gen event outcome reason count aux0 aux1 fn2-core)))
    (mv t fn2-core)))
(defun fn2-acq-run (id fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (mv-let (bytes steps actions runnable fn2-core) (fn2-machine-run id 4 fn2-core)
    (declare (ignore bytes steps runnable))
    (mv actions fn2-core)))
; Fill two bytes of a pending receive's range, as the adapter does.
(defun fn2-acq-fill (slot gen opgen fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (stobj-let ((fn2-pool (fn2-core-pool fn2-core)))
    (fn2-pool)
    (b* (((mv & fn2-pool) (fn2-pool-adapter-write slot gen 0 opgen 0 7 fn2-pool))
         ((mv & fn2-pool) (fn2-pool-adapter-write slot gen 0 opgen 1 8 fn2-pool)))
      fn2-pool)
    fn2-core))
(defun fn2-acq-wait (id fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (fn2-machine-wait-reason id fn2-core))
(defun fn2-acq-init (profile fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (let ((fn2-core (fn2-core-init profile fn2-core)))
    (fn2-listener-set-mode-all 1 fn2-core)))

(defun fn2-acq-profile (changes)
  (declare (xargs :verify-guards nil))
  (if (atom changes) *fn2-profile-tiny*
    (put-assoc-equal (caar changes) (cdar changes) (fn2-acq-profile (cdr changes)))))

; A refusal acquired nothing: every count is unchanged and the holder waits
; with the reason that names the exhausted kind.
(defun fn2-acq-refused (before after reason actions id fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (and (equal before after) (equal actions 0) (equal (fn2-acq-wait id fn2-core) reason)))

; ------------------------------------------------------------------------
; (fn2-listener :accept) and (fn2-listener :close). Bundle (:connection-row
; :rx-range :operation) from listener 0, holding its own row.

; Exhaust the connection row: C = 1, two listeners, the first holds it.
(defun fn2-acq-accept-row (fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* ((fn2-core (fn2-acq-init (fn2-acq-profile '((:c . 1) (:accept-credits . 2))) fn2-core))
       ((mv & fn2-core) (fn2-acq-run 0 fn2-core))
       ((mv & op gen fn2-core) (fn2-acq-take fn2-core))
       (c0 (fn2-acq-census fn2-core))
       ((mv a1 fn2-core) (fn2-acq-run 1 fn2-core))
       (refused (fn2-acq-refused c0 (fn2-acq-census fn2-core) *fn2-wait-connection-row* a1 1 fn2-core))
       ; Lift: the first Accept fails, its reservation comes back, the grant
       ; wakes listener 1, which acquires the bundle whole.
       (fn2-core (fn2-acq-post 0 op gen *fn2-event-accept-result* *fn2-outcome-failed*
                   *fn2-reason-exhausted* 0 0 fn2-core))
       ((mv & fn2-core) (fn2-acq-deliver fn2-core))
       (c1 (fn2-acq-census fn2-core))
       ((mv granted fn2-core) (fn2-machine-grant-one fn2-core))
       ((mv a2 fn2-core) (fn2-acq-run 1 fn2-core))
       (whole (and (equal granted 1) (equal a2 1)
                   (fn2-acq-same-delta (fn2-acq-delta c1 (fn2-acq-census fn2-core))
                     (fn2-acq-expect '((:connection-row . -1) (:class0 . -1)
                                       (:operation . -1) (:outbox . -1))))))
       ; Failed result after acquisition returns every count.
       ((mv & op gen fn2-core) (fn2-acq-take fn2-core))
       (fn2-core (fn2-acq-post 0 op gen *fn2-event-accept-result* *fn2-outcome-failed*
                   *fn2-reason-exhausted* 0 0 fn2-core))
       ((mv & fn2-core) (fn2-acq-deliver fn2-core))
       (released (equal (fn2-acq-census fn2-core) c1)))
    (mv (list (list :exhaust-connection-row refused) (list :lift-acquires-whole whole)
              (list :failed-result-returns released))
        fn2-core)))

; Exhaust the operation: O = 1, the first listener's Accept holds it.
(defun fn2-acq-accept-op (fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* ((fn2-core (fn2-acq-init (fn2-acq-profile '((:o . 1) (:accept-credits . 2))) fn2-core))
       ((mv & fn2-core) (fn2-acq-run 0 fn2-core))
       ((mv & op gen fn2-core) (fn2-acq-take fn2-core))
       (c0 (fn2-acq-census fn2-core))
       ((mv a1 fn2-core) (fn2-acq-run 1 fn2-core))
       (refused (fn2-acq-refused c0 (fn2-acq-census fn2-core) *fn2-wait-operation* a1 1 fn2-core))
       (fn2-core (fn2-acq-post 0 op gen *fn2-event-accept-result* *fn2-outcome-failed*
                   *fn2-reason-exhausted* 0 0 fn2-core))
       ((mv & fn2-core) (fn2-acq-deliver fn2-core))
       ((mv granted fn2-core) (fn2-machine-grant-one fn2-core))
       ((mv a2 fn2-core) (fn2-acq-run 1 fn2-core)))
    (mv (list (list :exhaust-operation refused)
              (list :lift-issues (and (equal granted 1) (equal a2 1))))
        fn2-core)))

; Exhaust the RX range: every class-0 slot is pre-occupied through the
; pool's own reserve export. The atomic bundle refuses at Accept issue; A
; issues the Accept, then closes the accepted capability at admission.
; The same run exhausts the operation while the refused listener closes:
; the Close must still issue, from the close reserve.
(defun fn2-acq-occupy (left class fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil :measure (nfix left)))
  (if (zp left) fn2-core
    (mv-let (code slot gen fn2-core) (fn2-core-reserve class *fn2-listener-kind* 1 1 fn2-core)
      (declare (ignore code slot gen))
      (fn2-acq-occupy (- left 1) class fn2-core))))
(defun fn2-acq-accept-rx (fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* ((fn2-core (fn2-acq-init (fn2-acq-profile '((:o . 1) (:accept-credits . 2))) fn2-core))
       (fn2-core (fn2-acq-occupy 8 0 fn2-core))
       (c0 (fn2-acq-census fn2-core))
       ((mv a0 fn2-core) (fn2-acq-run 0 fn2-core))
       (refused (fn2-acq-refused c0 (fn2-acq-census fn2-core) *fn2-wait-storage-window* a0 0 fn2-core))
       ; Today: the Accept was issued. Complete it and admit.
       ((mv & op gen fn2-core) (fn2-acq-take fn2-core))
       (fn2-core (fn2-acq-post 0 op gen *fn2-event-accept-result* *fn2-outcome-done* 0 0 4 fn2-core))
       ((mv & fn2-core) (fn2-acq-deliver fn2-core))
       ((mv & fn2-core) (fn2-acq-run 0 fn2-core))
       (closing (equal (fn2-machine-phase 0 fn2-core) *fn2-listener-state-closing*))
       ; Listener 1 takes the only operation; listener 0's Close must still issue.
       ((mv & fn2-core) (fn2-acq-run 1 fn2-core))
       ((mv ac fn2-core) (fn2-acq-run 0 fn2-core))
       (close-reserved (equal ac 1)))
    (mv (list (list :exhaust-rx-range refused) (list :refused-admission-closes closing)
              (list :close-from-reserve close-reserved))
        fn2-core)))

; ------------------------------------------------------------------------
; Echo: Receive, Send, Close draw one operation while the connection holds
; its row and RX slot. O = 1; the listener's next Accept holds the op.
(defun fn2-acq-echo-open (fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* ((fn2-core (fn2-acq-init (fn2-acq-profile '((:o . 1) (:accept-credits . 1))) fn2-core))
       (base (fn2-acq-census fn2-core))
       ((mv & fn2-core) (fn2-acq-run 0 fn2-core))
       ((mv & op gen fn2-core) (fn2-acq-take fn2-core))
       (fn2-core (fn2-acq-post 0 op gen *fn2-event-accept-result* *fn2-outcome-done* 0 0 4 fn2-core))
       ((mv & fn2-core) (fn2-acq-deliver fn2-core))
       ((mv & fn2-core) (fn2-acq-run 0 fn2-core))
       ((mv id fn2-core) (fn2-machine-take-wake fn2-core)))
    (mv id base fn2-core)))
; The listener takes the only operation (a pending Accept), returning its ref.
(defun fn2-acq-hold-op (fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* (((mv & fn2-core) (fn2-acq-run 0 fn2-core))
       ((mv & op gen fn2-core) (fn2-acq-take fn2-core)))
    (mv op gen fn2-core)))
(defun fn2-acq-free-op (op gen fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* ((fn2-core (fn2-acq-post 0 op gen *fn2-event-accept-result* *fn2-outcome-failed*
                   *fn2-reason-exhausted* 0 0 fn2-core))
       ((mv & fn2-core) (fn2-acq-deliver fn2-core)))
    fn2-core))
; One exhaustion boundary on the operation for connection ID: refused with
; nothing acquired, then granted and issued once the op comes back.
(defun fn2-acq-echo-boundary (id fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* (((mv op gen fn2-core) (fn2-acq-hold-op fn2-core))
       (c0 (fn2-acq-census fn2-core))
       ((mv a fn2-core) (fn2-acq-run id fn2-core))
       (refused (fn2-acq-refused c0 (fn2-acq-census fn2-core) *fn2-wait-operation* a id fn2-core))
       (fn2-core (fn2-acq-free-op op gen fn2-core))
       (c1 (fn2-acq-census fn2-core))
       ((mv granted fn2-core) (fn2-machine-grant-one fn2-core))
       ((mv a2 fn2-core) (fn2-acq-run id fn2-core))
       (whole (and (equal granted id) (equal a2 1)
                   (fn2-acq-same-delta (fn2-acq-delta c1 (fn2-acq-census fn2-core))
                     (fn2-acq-expect '((:operation . -1) (:outbox . -1)))))))
    (mv refused whole c1 fn2-core)))

(defun fn2-acq-echo (fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* (((mv id base fn2-core) (fn2-acq-echo-open fn2-core))
       (slot (fn2-machine-pool-slot id fn2-core))
       (pgen (fn2-machine-pool-gen id fn2-core))
       ; Receive.
       ((mv r-refused r-whole r-c1 fn2-core) (fn2-acq-echo-boundary id fn2-core))
       ((mv & op gen fn2-core) (fn2-acq-take fn2-core))
       (fn2-core (fn2-acq-fill slot pgen gen fn2-core))
       (fn2-core (fn2-acq-post 0 op gen *fn2-event-receive-result* *fn2-outcome-done* 0 2 0 fn2-core))
       ((mv & fn2-core) (fn2-acq-deliver fn2-core))
       (r-returns (equal (fn2-acq-census fn2-core) r-c1))
       ; Send (from the RX slot; the borrow comes back with the terminal).
       ((mv s-refused s-whole s-c1 fn2-core) (fn2-acq-echo-boundary id fn2-core))
       ((mv & op gen fn2-core) (fn2-acq-take fn2-core))
       (fn2-core (fn2-acq-post 0 op gen *fn2-event-send-result* *fn2-outcome-done* 0 2 0 fn2-core))
       ((mv & fn2-core) (fn2-acq-deliver fn2-core))
       (s-returns (equal (fn2-acq-census fn2-core) s-c1))
       ; Reset to command, the next Receive ends with EOF: the connection closes.
       ((mv & fn2-core) (fn2-acq-run id fn2-core))
       ((mv & fn2-core) (fn2-acq-run id fn2-core))
       ((mv & op gen fn2-core) (fn2-acq-take fn2-core))
       (fn2-core (fn2-acq-post 0 op gen *fn2-event-receive-result* *fn2-outcome-done* 0 0 0 fn2-core))
       ((mv & fn2-core) (fn2-acq-deliver fn2-core))
       (closing (equal (fn2-machine-phase id fn2-core) *fn2-echo-state-closing*))
       ; Close with the only operation held elsewhere: it must still issue.
       ((mv op2 gen2 fn2-core) (fn2-acq-hold-op fn2-core))
       ((mv ac fn2-core) (fn2-acq-run id fn2-core))
       (close-reserved (equal ac 1))
       (fn2-core (fn2-acq-free-op op2 gen2 fn2-core))
       ((mv & fn2-core) (fn2-machine-grant-one fn2-core))
       ((mv & fn2-core) (if close-reserved (mv 0 fn2-core) (fn2-acq-run id fn2-core)))
       ((mv & op gen fn2-core) (fn2-acq-take fn2-core))
       (fn2-core (fn2-acq-post 0 op gen *fn2-event-close-result* *fn2-outcome-done* 0 0 0 fn2-core))
       ((mv & fn2-core) (fn2-acq-deliver fn2-core))
       ((mv & fn2-core) (fn2-acq-run id fn2-core))
       ; Close releases the RX slot and the row credit: back to the base census.
       (c-returns (equal (fn2-acq-census fn2-core) base)))
    (mv (list (list '(fn2-echo :receive) :exhaust-operation r-refused)
              (list '(fn2-echo :receive) :lift-acquires-whole r-whole)
              (list '(fn2-echo :receive) :result-returns r-returns)
              (list '(fn2-echo :send) :exhaust-operation s-refused)
              (list '(fn2-echo :send) :lift-acquires-whole s-whole)
              (list '(fn2-echo :send) :result-returns s-returns)
              (list '(fn2-echo :close) :eof-closes closing)
              (list '(fn2-echo :close) :close-from-reserve close-reserved)
              (list '(fn2-echo :close) :close-returns-every-count c-returns))
        fn2-core)))

; ------------------------------------------------------------------------
; Scribe: the window, then Write, Fence and Read on the operation.
(defconst *fn2-acq-scribe-profile*
  (fn2-acq-profile '((:o . 1) (:accept-credits . 1) (:pool-classes . ((8 . 64) (1 . 4096))))))
(defun fn2-acq-scribe-until (left phase id fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil :measure (nfix left)))
  (if (or (zp left) (equal (fn2-machine-phase id fn2-core) phase)) fn2-core
    (mv-let (a fn2-core) (fn2-acq-run id fn2-core)
      (declare (ignore a))
      (fn2-acq-scribe-until (- left 1) phase id fn2-core))))
(defun fn2-acq-scribe-boundary (id fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* (((mv op gen fn2-core) (fn2-acq-hold-op fn2-core))
       (c0 (fn2-acq-census fn2-core))
       ((mv a fn2-core) (fn2-acq-run id fn2-core))
       (refused (fn2-acq-refused c0 (fn2-acq-census fn2-core) *fn2-wait-operation* a id fn2-core))
       (fn2-core (fn2-acq-free-op op gen fn2-core))
       (c1 (fn2-acq-census fn2-core))
       ((mv granted fn2-core) (fn2-machine-grant-one fn2-core))
       ((mv a2 fn2-core) (fn2-acq-run id fn2-core))
       (whole (and (equal granted id) (equal a2 1)
                   (fn2-acq-same-delta (fn2-acq-delta c1 (fn2-acq-census fn2-core))
                     (fn2-acq-expect '((:operation . -1) (:outbox . -1)))))))
    (mv a refused whole c1 fn2-core)))

(defun fn2-acq-scribe (fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* ((fn2-core (fn2-acq-init *fn2-acq-scribe-profile* fn2-core))
       (fn2-core (fn2-scribe-start fn2-core))
       ((mv id fn2-core) (fn2-machine-take-wake fn2-core))
       ; Window: the only 4 KiB slot is pre-occupied.
       ((mv & tslot tgen fn2-core) (fn2-core-reserve 1 *fn2-listener-kind* 1 1 fn2-core))
       (c0 (fn2-acq-census fn2-core))
       ((mv a fn2-core) (fn2-acq-run id fn2-core))
       (w-refused (fn2-acq-refused c0 (fn2-acq-census fn2-core) *fn2-wait-storage-window* a id fn2-core))
       ((mv & fn2-core) (fn2-core-release tslot tgen *fn2-listener-kind* 1 1 fn2-core))
       (c1 (fn2-acq-census fn2-core))
       ((mv granted fn2-core) (fn2-machine-grant-one fn2-core))
       ((mv & fn2-core) (fn2-acq-run id fn2-core))
       (w-whole (and (equal granted id)
                     (fn2-acq-same-delta (fn2-acq-delta c1 (fn2-acq-census fn2-core))
                       (fn2-acq-expect '((:class1 . -1))))))
       ; Write.
       (fn2-core (fn2-acq-scribe-until 4200 *fn2-scribe-state-write* id fn2-core))
       ((mv & wr-refused wr-whole wr-c1 fn2-core) (fn2-acq-scribe-boundary id fn2-core))
       ((mv & op gen fn2-core) (fn2-acq-take fn2-core))
       (fn2-core (fn2-acq-post 0 op gen *fn2-event-write-result* *fn2-outcome-done* 0 4096 0 fn2-core))
       ((mv & fn2-core) (fn2-acq-deliver fn2-core))
       (wr-returns (equal (fn2-acq-census fn2-core) wr-c1))
       ; Fence: with the operation held elsewhere it must still issue.
       (fn2-core (fn2-acq-scribe-until 16 *fn2-scribe-state-fence* id fn2-core))
       ((mv fa ?f-refused f-whole f-c1 fn2-core) (fn2-acq-scribe-boundary id fn2-core))
       ((mv & op gen fn2-core) (fn2-acq-take fn2-core))
       (fn2-core (fn2-acq-post 0 op gen *fn2-event-fence-result* *fn2-outcome-done* 0 0 0 fn2-core))
       ((mv & fn2-core) (fn2-acq-deliver fn2-core))
       (f-returns (equal (fn2-acq-census fn2-core) f-c1))
       ; Read.
       (fn2-core (fn2-acq-scribe-until 16 *fn2-scribe-state-read* id fn2-core))
       ((mv & rd-refused rd-whole rd-c1 fn2-core) (fn2-acq-scribe-boundary id fn2-core))
       ((mv & op gen fn2-core) (fn2-acq-take fn2-core))
       (fn2-core (fn2-acq-post 0 op gen *fn2-event-read-result* *fn2-outcome-done* 0 4096 0 fn2-core))
       ((mv & fn2-core) (fn2-acq-deliver fn2-core))
       (rd-returns (equal (fn2-acq-census fn2-core) rd-c1)))
    (mv (list (list '(fn2-scribe :reserve) :exhaust-storage-window w-refused)
              (list '(fn2-scribe :reserve) :lift-acquires-whole w-whole)
              (list '(fn2-scribe :write) :exhaust-operation wr-refused)
              (list '(fn2-scribe :write) :lift-acquires-whole wr-whole)
              (list '(fn2-scribe :write) :result-returns wr-returns)
              (list '(fn2-scribe :fence) :fence-from-reserve (equal fa 1))
              (list '(fn2-scribe :fence) :lift-acquires-whole f-whole)
              (list '(fn2-scribe :fence) :result-returns f-returns)
              (list '(fn2-scribe :read) :exhaust-operation rd-refused)
              (list '(fn2-scribe :read) :lift-acquires-whole rd-whole)
              (list '(fn2-scribe :read) :result-returns rd-returns))
        fn2-core)))

; ------------------------------------------------------------------------
; ArmWake: with the operation held, the timer service must still arm.
(defun fn2-acq-arm-wake (fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* ((fn2-core (fn2-acq-init (fn2-acq-profile '((:o . 1) (:accept-credits . 1))) fn2-core))
       ((mv op gen fn2-core) (fn2-acq-hold-op fn2-core))
       (c0 (fn2-acq-census fn2-core))
       (fn2-core (fn2-request-wake 100 fn2-core))
       ((mv armed fn2-core) (fn2-exec-arm fn2-core))
       (unchanged (or (equal armed 1) (equal c0 (fn2-acq-census fn2-core))))
       (fn2-core (fn2-acq-free-op op gen fn2-core))
       ((mv armed2 fn2-core) (if (equal armed 1) (mv 1 fn2-core) (fn2-exec-arm fn2-core))))
    (mv (list (list :refused-acquires-nothing unchanged) (list :arm-from-reserve (equal armed 1))
              (list :lift-arms (equal armed2 1)))
        fn2-core)))

; ------------------------------------------------------------------------
(defun fn2-acq-tag (bundle checks)
  (declare (xargs :verify-guards nil))
  (if (atom checks) nil (cons (cons bundle (car checks)) (fn2-acq-tag bundle (cdr checks)))))

(defun fn2-acq-all-checks ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (checks fn2-core)
      (b* (((mv a fn2-core) (fn2-acq-accept-row fn2-core))
           ((mv b fn2-core) (fn2-acq-accept-op fn2-core))
           ((mv c fn2-core) (fn2-acq-accept-rx fn2-core))
           ((mv e fn2-core) (fn2-acq-echo fn2-core))
           ((mv s fn2-core) (fn2-acq-scribe fn2-core))
           ((mv w fn2-core) (fn2-acq-arm-wake fn2-core)))
        (mv (append (fn2-acq-tag '(fn2-listener :accept) (append a b (take 1 c)))
                    (fn2-acq-tag '(fn2-listener :close) (cdr c))
                    e s (fn2-acq-tag '(:timer :arm-wake) w))
            fn2-core))
      checks)))

; Per bundle: :pass when every check passes, :fail otherwise, :no-scenario
; when an :exists bundle has none (always a red).
(defun fn2-acq-bundle-checks (bundle checks)
  (declare (xargs :verify-guards nil))
  (if (atom checks) nil
    (if (equal (caar checks) bundle) (cons (cdar checks) (fn2-acq-bundle-checks bundle (cdr checks)))
      (fn2-acq-bundle-checks bundle (cdr checks)))))
(defun fn2-acq-all-pass (checks)
  (declare (xargs :verify-guards nil))
  (if (atom checks) t (and (cadar checks) (fn2-acq-all-pass (cdr checks)))))
(defun fn2-acq-verdicts (bundles checks)
  (declare (xargs :verify-guards nil))
  (if (atom bundles) nil
    (let* ((row (car bundles)) (id (car row)) (p (cdr row))
           (status (fn2-resource-get :status p)) (owed (fn2-resource-get :owed-by p))
           (mine (fn2-acq-bundle-checks id checks))
           (verdict (cond ((not (eq status :exists)) :pending)
                          ((atom mine) :no-scenario)
                          ((fn2-acq-all-pass mine) :pass) (t :fail)))
           (ok (case verdict (:pending t) (:no-scenario nil)
                 (:pass (not owed)) (t (and owed t)))))
      (cons (list id verdict owed ok (if (eq verdict :pending) (cadr status) mine))
            (fn2-acq-verdicts (cdr bundles) checks)))))
(defun fn2-acq-verdicts-ok (verdicts)
  (declare (xargs :verify-guards nil))
  (if (atom verdicts) t (and (nth 3 (car verdicts)) (fn2-acq-verdicts-ok (cdr verdicts)))))

;; Teeth of fn2-resource-no-deadlock. Positive: real reached cores with a
;; listener parked on admission and a scribe parked on its window; the
;; projection is nonempty and ranked, and stays ranked after a real turn.
;; Negative: a connection holding its row and RX slot made to wait for a
;; connection row, which the ranked check refuses.
(defun fn2-resource-test-no-deadlock-run (fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* ((fn2-core (fn2-acq-init (fn2-acq-profile '((:c . 1) (:accept-credits . 2))) fn2-core))
       ((mv & fn2-core) (fn2-acq-run 0 fn2-core))
       ((mv & & & fn2-core) (fn2-acq-take fn2-core))
       ((mv & fn2-core) (fn2-acq-run 1 fn2-core))
       (w1 (fn2-resource-waiters fn2-core))
       (r1 (fn2-resource-core-ranked-p fn2-core))
       ((mv & & & & fn2-core) (fn2-turn fn2-core))
       (t1 (fn2-resource-core-ranked-p fn2-core))
       (fn2-core (fn2-acq-init *fn2-acq-scribe-profile* fn2-core))
       (fn2-core (fn2-scribe-start fn2-core))
       ((mv id fn2-core) (fn2-machine-take-wake fn2-core))
       ((mv & & & fn2-core) (fn2-core-reserve 1 *fn2-listener-kind* 1 1 fn2-core))
       ((mv & fn2-core) (fn2-acq-run id fn2-core))
       (w2 (fn2-resource-waiters fn2-core))
       (r2 (fn2-resource-core-ranked-p fn2-core))
       ((mv & & & & fn2-core) (fn2-turn fn2-core))
       (t2 (fn2-resource-core-ranked-p fn2-core)))
    (mv (and (equal w1 '(((:accept-credit) . :connection-row))) r1 t1
             (equal w2 '(((:storage-job) . :storage-window))) r2 t2)
        fn2-core)))
(defun fn2-resource-test-no-deadlock ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (ok fn2-core) (fn2-resource-test-no-deadlock-run fn2-core) ok)))
(defun fn2-resource-test-no-deadlock-negative-run (fn2-core)
  (declare (xargs :stobjs fn2-core :verify-guards nil))
  (b* (((mv id & fn2-core) (fn2-acq-echo-open fn2-core))
       (fn2-core (fn2-machine-put id (wait-reason *fn2-wait-connection-row*)))
       (w (fn2-resource-waiters fn2-core)))
    (mv (and (equal w '(((:connection-row :rx-range) . :connection-row)))
             (not (fn2-resource-core-ranked-p fn2-core)))
        fn2-core)))
(defun fn2-resource-test-no-deadlock-negative ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (ok fn2-core) (fn2-resource-test-no-deadlock-negative-run fn2-core) ok)))
(fn2-assert-owed-teeth fn2-resource-no-deadlock)

(defconst *fn2-acq-checks* (fn2-acq-all-checks))
(defconst *fn2-acq-verdicts* (fn2-acq-verdicts *fn2-resource-bundles* *fn2-acq-checks*))

; Controls on the verdict rule itself, over the same recorded checks: an owed
; bundle that passes is a red (its marking must go), an un-owed bundle that
; fails is a red, and an :exists bundle with no scenario is a red.
(defun fn2-acq-remark (bundle owed rows)
  (declare (xargs :verify-guards nil))
  (if (atom rows) nil
    (cons (if (equal (caar rows) bundle)
              (cons bundle (fn2-decl-set :owed-by owed (cdar rows))) (car rows))
          (fn2-acq-remark bundle owed (cdr rows)))))
(assert-event (not (fn2-acq-verdicts-ok
                    (fn2-acq-verdicts (fn2-acq-remark '(fn2-echo :receive) :r6b *fn2-resource-bundles*)
                                      *fn2-acq-checks*))))
(assert-event (not (fn2-acq-verdicts-ok
                    (fn2-acq-verdicts (fn2-acq-remark '(fn2-echo :close) nil *fn2-resource-bundles*)
                                      *fn2-acq-checks*))))
(assert-event (not (fn2-acq-verdicts-ok
                    (fn2-acq-verdicts (cons '((fn2-echo :unscenarioed) :acquires (:operation) :status :exists)
                                            *fn2-resource-bundles*)
                                      *fn2-acq-checks*))))
(assert-event (fn2-acq-verdicts-ok *fn2-acq-verdicts*)
              :msg (msg "Acquisition verdicts: ~x0" *fn2-acq-verdicts*))
