; fn: the runtime contract (RUNTIME-MODEL-DRAFT-20261009 section 1).
;
; One executor runs many machine instances.  Every effect an instance wants is
; an ACTION (kind id incarnation op args) handed to an I/O worker; the worker's
; answer is a COMPLETION (kind id incarnation op outcome), the only kind of
; event this layer consumes.  ID is the instance's slot, INCARNATION the slot's
; incarnation, OP the operation number the layer assigned at submission (one
; process-monotonic counter, never reused).  Outcomes are (:done n),
; (:short n), (:failed reason) and (:cancelled).  An instance learns that an
; effect happened only from its completion; submission establishes nothing.
;
; This book is that layer, written once over a constrained instance machine
; (`fn-rtc-m-step'), so its theorems hold for every machine that meets the
; constraint; an executable instance obtains them by `:functional-instance'
; (books/def-loop.lisp's manner).  What the layer owns:
;
;   SLOTS  one per instance: (incarnation status resource), status :free,
;          :live, :closing (close submitted) or :draining (close completed,
;          actions still outstanding).  Slot 0 is the listener.  A slot is
;          retired to :free only when its incarnation has no outstanding
;          action, and an :accept reuses it under incarnation + 1.
;   POOL   buffers (generation owner bytes), owner (:free), (:workspace id inc)
;          (mutable, one instance) or (:leased id inc dir) (immutable to every
;          instance; the pair is where the buffer returns when the lease ends,
;          DIR is :in when a worker writes it, :out when workers read it).  At
;          an action boundary a buffer is named by a handle (h g off len).
;   USES   the outstanding-action table: (kind id inc handle op), one per
;          submitted action until its completion arrives.  At most one use per
;          (kind id inc) (v1, below); ops distinct.  A buffered action holds a
;          lease on its handle's buffer: an :in lease has exactly one holder, an
;          :out lease any number of :out holders.
;
; BORROWED, the third ownership state, exists only inside one call: the
; instance machine receives `fn-rtc-borrow' of the pool, which it cannot write
; and in which the bytes of every :in-leased buffer are hidden, so no machine
; observes bytes a worker may be writing.  The executable pool's read export
; refuses an :in-leased buffer, which is what this view models.
;
; A completion that matches no outstanding use -- a duplicate, a forgery, a late
; completion of an earlier operation with the same kind on the same instance,
; one naming a retired incarnation -- changes nothing and emits nothing (T6).
; The layer checks the host's discipline; it does not assume it.
;
; Cancellation: an instance may request (:cancel kind) for its own outstanding
; action; the layer emits (:cancel id inc op (kind)) naming that operation and
; keeps the use.  The use, and any lease it holds, ends only on the action's
; own completion.  A completion, (:cancelled) included, means the worker has
; let go of the operation and its buffer; the host never synthesizes one on a
; timeout (books/page-read-ownership.lisp: cancellation revokes publication,
; not worker ownership).  A-HOST-COMPLETES (statement below): the host
; delivers exactly one completion for every submitted action.  Under it a
; deadline (a :timer) followed by a cancel bounds how long any action pins its
; slot and its buffer.
;
; v1 limitation: one outstanding action per (kind id inc), so an instance cannot
; keep two :pread in flight (no double-buffered reads).  Revisit when a
; measured served path needs it: cold ARTICLE of a multi-extent article whose
; per-read latency, serialized, misses the ARTICLE 3 MiB bar in PRODUCT-DRAFT.
; Operation numbers already identify operations; the change is to drop the
; per-kind check and bound uses per instance by configuration.
;
; The ownership invariant OutstandingUse(h,g) => BytesStable(h,g) and
; not Recyclable(h,g) is `fn-rtc-invp''s lease clause plus the two-state
; theorem `fn-rtc-outstanding-use-is-stable'.  A lease is released only by the
; completion of its last use; a deadline, a close or any other event retains
; it.  Data an :in action reads (:recv, :pread) is part of its completion in
; this model and lands in the buffer exactly when the lease ends; in the
; executable pool the bytes are already in the array (A-HOST), hidden by the
; borrow view until then.
;
; The work budget: the instance machine is charged its quantum q plus a
; constant; the layer adds work bounded by the configuration (completion bytes
; included), so one step costs at most q + (fn-rtc-step-c config).  Retained
; output per step is bounded: actions carry handles and at most two bounded
; naturals, never bytes; an instance's retained state is bounded by the
; constrained `fn-rtc-m-max-state'.  Work an instance cannot finish within q
; stays in its own state and resumes on the completion of a zero-delay :timer
; it submits; there is no other continuation mechanism (that an instance with
; pending work has such a timer outstanding is the instance's obligation).
;
; The commit point: :commit is not an action kind.  An instance's commit
; observer (`fn-rtc-m-committedp') may turn true only on the delivery of a
; (:fsync (:done n)) completion of the instance's own outstanding :fsync (T11,
; the layer's half); which barrier that may be is the instance's keystone.

(in-package "ACL2")
(include-book "cbor")

; -----------------------------------------------------------------------------
; Vocabulary

(defconst *fn-rtc-kinds*
  '(:recv :send :pread :pwrite :fsync :close :accept :timer :bp-send))

; The worker writes the buffer (:in) or reads it (:out); the rest carry none.
(defconst *fn-rtc-in-kinds* '(:recv :pread))
(defconst *fn-rtc-out-kinds* '(:send :pwrite :bp-send))

; What an instance may submit; :close has its own request and :accept is the
; layer's.
(defconst *fn-rtc-machine-kinds*
  '(:recv :send :pread :pwrite :fsync :timer :bp-send))

; Actions are the completion kinds plus :cancel, which has no completion of its
; own: it asks the host to finish the named action early.
(defconst *fn-rtc-action-kinds* (cons :cancel *fn-rtc-kinds*))

; The failure reasons a completion may carry; any other is delivered as
; :other, so a host cannot hand an instance an unbounded object.
(defconst *fn-rtc-failure-reasons*
  '(:eio :enospc :epipe :econnreset :etimedout :ebadf :eagain :malformed-completion :other))

; Extra action arguments: at most two naturals below 2^64 (a file reference
; and a position, or a timer delay).
(defun fn-rtc-extrap (x)
  (declare (xargs :guard t))
  (and (true-listp x) (<= (len x) 2)
       (or (atom x) (and (natp (car x)) (< (car x) (expt 2 64))))
       (or (atom (cdr x)) (and (natp (cadr x)) (< (cadr x) (expt 2 64))))))

(defun fn-rtc-get (i l)
  (declare (xargs :guard t))
  (if (consp l)
      (if (zp (nfix i)) (car l) (fn-rtc-get (- (nfix i) 1) (cdr l)))
    nil))

(defun fn-rtc-set (i v l)
  (declare (xargs :guard t))
  (if (consp l)
      (if (zp (nfix i)) (cons v (cdr l)) (cons (car l) (fn-rtc-set (- (nfix i) 1) v (cdr l))))
    nil))

; -----------------------------------------------------------------------------
; Configuration (nslots nbufs cap): instance slots including the listener,
; buffers, and the capacity of each buffer in octets.

(defun fn-rtc-configp (c)
  (declare (xargs :guard t))
  (and (true-listp c) (equal (len c) 3)
       (natp (fn-rtc-get 0 c)) (<= 2 (fn-rtc-get 0 c))
       (natp (fn-rtc-get 1 c))
       (natp (fn-rtc-get 2 c))))

(defun fn-rtc-nslots (c) (declare (xargs :guard t)) (nfix (fn-rtc-get 0 c)))
(defun fn-rtc-nbufs (c) (declare (xargs :guard t)) (nfix (fn-rtc-get 1 c)))
(defun fn-rtc-cap (c) (declare (xargs :guard t)) (nfix (fn-rtc-get 2 c)))

; -----------------------------------------------------------------------------
; Handles, actions, completions

(defun fn-rtc-handlep (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 4)
       (natp (fn-rtc-get 0 x)) (natp (fn-rtc-get 1 x))
       (natp (fn-rtc-get 2 x)) (natp (fn-rtc-get 3 x))))

(defun fn-rtc-h-buf (hd) (declare (xargs :guard t)) (nfix (fn-rtc-get 0 hd)))
(defun fn-rtc-h-gen (hd) (declare (xargs :guard t)) (nfix (fn-rtc-get 1 hd)))
(defun fn-rtc-h-off (hd) (declare (xargs :guard t)) (nfix (fn-rtc-get 2 hd)))
(defun fn-rtc-h-len (hd) (declare (xargs :guard t)) (nfix (fn-rtc-get 3 hd)))

(defun fn-rtc-outcomep (o)
  (declare (xargs :guard t))
  (and (true-listp o)
       (case (fn-rtc-get 0 o)
         ((:done :short) (and (equal (len o) 2) (natp (fn-rtc-get 1 o))))
         (:failed (equal (len o) 2))
         (:cancelled (equal (len o) 1))
         (otherwise nil))))

; (kind id inc op outcome) or, for an :in kind, (kind id inc op outcome data).
(defun fn-rtc-completionp (e)
  (declare (xargs :guard t))
  (and (true-listp e)
       (or (equal (len e) 5) (equal (len e) 6))
       (member-eq (fn-rtc-get 0 e) *fn-rtc-kinds*)
       (natp (fn-rtc-get 1 e))
       (natp (fn-rtc-get 2 e))
       (natp (fn-rtc-get 3 e))
       (fn-rtc-outcomep (fn-rtc-get 4 e))))

(defun fn-rtc-e-kind (e) (declare (xargs :guard t)) (fn-rtc-get 0 e))
(defun fn-rtc-e-id (e) (declare (xargs :guard t)) (nfix (fn-rtc-get 1 e)))
(defun fn-rtc-e-inc (e) (declare (xargs :guard t)) (nfix (fn-rtc-get 2 e)))
(defun fn-rtc-e-op (e) (declare (xargs :guard t)) (nfix (fn-rtc-get 3 e)))
(defun fn-rtc-e-outcome (e) (declare (xargs :guard t)) (fn-rtc-get 4 e))
(defun fn-rtc-e-data (e) (declare (xargs :guard t)) (fn-rtc-get 5 e))

; An action's arguments: at most four, each a handle, a natural below 2^64, nil
; or a kind -- a bounded object whatever the instance asked for.
(defun fn-rtc-action-argp (x)
  (declare (xargs :guard t))
  (or (null x)
      (and (natp x) (< x (expt 2 64)))
      (and (member-eq x *fn-rtc-kinds*) t)
      (fn-rtc-handlep x)))

(defun fn-rtc-action-argsp (args)
  (declare (xargs :guard t))
  (and (true-listp args) (<= (len args) 4)
       (or (atom args)
           (and (fn-rtc-action-argp (car args))
                (fn-rtc-action-argsp (cdr args))))))

(defun fn-rtc-actionp (a)
  (declare (xargs :guard t))
  (and (true-listp a) (equal (len a) 5)
       (member-eq (fn-rtc-get 0 a) *fn-rtc-action-kinds*)
       (natp (fn-rtc-get 1 a)) (natp (fn-rtc-get 2 a)) (natp (fn-rtc-get 3 a))
       (fn-rtc-action-argsp (fn-rtc-get 4 a))))

; -----------------------------------------------------------------------------
; Slots, buffers, uses

(defun fn-rtc-slotp (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 3)
       (natp (fn-rtc-get 0 x))
       (member-eq (fn-rtc-get 1 x) '(:free :live :closing :draining))
       (or (null (fn-rtc-get 2 x))
           (and (natp (fn-rtc-get 2 x)) (< (fn-rtc-get 2 x) (expt 2 64))))))

(defun fn-rtc-s-inc (x) (declare (xargs :guard t)) (nfix (fn-rtc-get 0 x)))
(defun fn-rtc-s-status (x) (declare (xargs :guard t)) (fn-rtc-get 1 x))
(defun fn-rtc-s-res (x) (declare (xargs :guard t)) (fn-rtc-get 2 x))

(defconst *fn-rtc-listener* '(0 :live nil))

(defun fn-rtc-ownerp (o)
  (declare (xargs :guard t))
  (and (true-listp o)
       (case (fn-rtc-get 0 o)
         (:free (equal (len o) 1))
         (:workspace
          (and (equal (len o) 3) (natp (fn-rtc-get 1 o)) (natp (fn-rtc-get 2 o))))
         (:leased
          (and (equal (len o) 4) (natp (fn-rtc-get 1 o)) (natp (fn-rtc-get 2 o))
               (member-eq (fn-rtc-get 3 o) '(:in :out))))
         (otherwise nil))))

(defun fn-rtc-bufferp (b cap)
  (declare (xargs :guard (natp cap)))
  (and (true-listp b) (equal (len b) 3)
       (natp (fn-rtc-get 0 b))
       (fn-rtc-ownerp (fn-rtc-get 1 b))
       (fn-cbor-octet-listp (fn-rtc-get 2 b))
       (<= (len (fn-rtc-get 2 b)) cap)))

(defun fn-rtc-b-gen (b) (declare (xargs :guard t)) (nfix (fn-rtc-get 0 b)))
(defun fn-rtc-b-owner (b) (declare (xargs :guard t)) (fn-rtc-get 1 b))
(defun fn-rtc-b-bytes (b) (declare (xargs :guard t)) (fn-rtc-get 2 b))

(defun fn-rtc-usep (u)
  (declare (xargs :guard t))
  (and (true-listp u) (equal (len u) 5)
       (member-eq (fn-rtc-get 0 u) *fn-rtc-kinds*)
       (natp (fn-rtc-get 1 u)) (natp (fn-rtc-get 2 u)) (natp (fn-rtc-get 3 u))
       (if (or (member-eq (fn-rtc-get 0 u) *fn-rtc-in-kinds*)
               (member-eq (fn-rtc-get 0 u) *fn-rtc-out-kinds*))
           (fn-rtc-handlep (fn-rtc-get 4 u))
         (null (fn-rtc-get 4 u)))))

; A use's handle (nil for an unbuffered kind).
(defun fn-rtc-u-hd (u) (declare (xargs :guard t)) (fn-rtc-get 4 u))

; The key of a use, an action or a completion: (kind id inc op).
(defun fn-rtc-key (x)
  (declare (xargs :guard t))
  (list (fn-rtc-get 0 x) (fn-rtc-get 1 x) (fn-rtc-get 2 x) (fn-rtc-get 3 x)))

; Is some use of KIND outstanding for instance (ID INC)?  (The v1 one-per-kind
; rule.)
(defun fn-rtc-kind-out-p (kind id inc uses)
  (declare (xargs :guard t))
  (if (consp uses)
      (or (and (equal (fn-rtc-get 0 (car uses)) kind)
               (equal (fn-rtc-get 1 (car uses)) id)
               (equal (fn-rtc-get 2 (car uses)) inc))
          (fn-rtc-kind-out-p kind id inc (cdr uses)))
    nil))

; The op of instance (ID INC)'s outstanding KIND use.
(defun fn-rtc-kind-op (kind id inc uses)
  (declare (xargs :guard t))
  (if (consp uses)
      (if (and (equal (fn-rtc-get 0 (car uses)) kind)
               (equal (fn-rtc-get 1 (car uses)) id)
               (equal (fn-rtc-get 2 (car uses)) inc))
          (nfix (fn-rtc-get 3 (car uses)))
        (fn-rtc-kind-op kind id inc (cdr uses)))
    0))

(defun fn-rtc-find-use (key uses)
  (declare (xargs :guard t))
  (if (consp uses)
      (if (equal (fn-rtc-key (car uses)) key)
          (car uses)
        (fn-rtc-find-use key (cdr uses)))
    nil))

(defun fn-rtc-remove-use (key uses)
  (declare (xargs :guard t))
  (if (consp uses)
      (if (equal (fn-rtc-key (car uses)) key)
          (cdr uses)
        (cons (car uses) (fn-rtc-remove-use key (cdr uses))))
    nil))

; Does some use hold buffer H at generation G?
(defun fn-rtc-holds-p (h g uses)
  (declare (xargs :guard t))
  (if (consp uses)
      (or (let ((hd (fn-rtc-u-hd (car uses))))
            (and (fn-rtc-handlep hd)
                 (equal (fn-rtc-h-buf hd) h)
                 (equal (fn-rtc-h-gen hd) g)))
          (fn-rtc-holds-p h g (cdr uses)))
    nil))

(defun fn-rtc-uses-of-slot-p (id inc uses)
  (declare (xargs :guard t))
  (if (consp uses)
      (or (and (equal (fn-rtc-get 1 (car uses)) id)
               (equal (fn-rtc-get 2 (car uses)) inc))
          (fn-rtc-uses-of-slot-p id inc (cdr uses)))
    nil))

; -----------------------------------------------------------------------------
; The layer state (config slots pool uses mstates next-op)

(defun fn-rtc-config (s) (declare (xargs :guard t)) (fn-rtc-get 0 s))
(defun fn-rtc-slots (s) (declare (xargs :guard t)) (fn-rtc-get 1 s))
(defun fn-rtc-pool (s) (declare (xargs :guard t)) (fn-rtc-get 2 s))
(defun fn-rtc-uses (s) (declare (xargs :guard t)) (fn-rtc-get 3 s))
(defun fn-rtc-mstates (s) (declare (xargs :guard t)) (fn-rtc-get 4 s))
(defun fn-rtc-next-op (s) (declare (xargs :guard t)) (nfix (fn-rtc-get 5 s)))

(defun fn-rtc-make (config slots pool uses mstates next-op)
  (declare (xargs :guard t))
  (list config slots pool uses mstates next-op))

(defun fn-rtc-slot (id s) (declare (xargs :guard t)) (fn-rtc-get id (fn-rtc-slots s)))
(defun fn-rtc-buffer (h s) (declare (xargs :guard t)) (fn-rtc-get h (fn-rtc-pool s)))
(defun fn-rtc-mstate (id s) (declare (xargs :guard t)) (fn-rtc-get id (fn-rtc-mstates s)))

; The bytes and generation of buffer H, the observables of BytesStable.
(defun fn-rtc-bytes (h s) (declare (xargs :guard t)) (fn-rtc-b-bytes (fn-rtc-buffer h s)))
(defun fn-rtc-gen (h s) (declare (xargs :guard t)) (fn-rtc-b-gen (fn-rtc-buffer h s)))

; Recyclable: the pool may hand the buffer to a new owner.
(defun fn-rtc-recyclablep (h s)
  (declare (xargs :guard t))
  (equal (fn-rtc-b-owner (fn-rtc-buffer h s)) '(:free)))

; The current incarnation of slot ID is INC and the slot is not retired.
(defun fn-rtc-current-p (id inc s)
  (declare (xargs :guard t))
  (let ((slot (fn-rtc-slot id s)))
    (and (equal (fn-rtc-s-inc slot) inc)
         (not (eq (fn-rtc-s-status slot) :free)))))

(defun fn-rtc-live-p (id inc s)
  (declare (xargs :guard t))
  (let ((slot (fn-rtc-slot id s)))
    (and (equal (fn-rtc-s-inc slot) inc)
         (eq (fn-rtc-s-status slot) :live))))

; -----------------------------------------------------------------------------
; The instance machine, constrained.
;
; (fn-rtc-m-step m ev pool q) => (mv m2 requests cost).  EV is the delivered
; completion without its identity, (kind outcome); POOL is the borrow view
; (read only; :in-leased bytes hidden).  Requests, processed in order by `fn-rtc-requests':
;   (:acquire h)               a :free buffer becomes this instance's workspace,
;                              generation + 1, bytes empty
;   (:write h g off octets)    into its own workspace, within capacity
;   (:release h g)             its own workspace back to :free
;   (:submit kind hd extra)    an action; hd a handle for a buffered kind
;   (:close)                   close this instance
;   (:cancel kind)             ask the host to finish its outstanding KIND action
; A request the layer cannot honour is refused (returned, nothing changes).

(defun fn-rtc-reqs-octets (reqs)
  (declare (xargs :guard t))
  (if (consp reqs)
      (+ (if (eq (fn-rtc-get 0 (car reqs)) :write)
             (len (fn-rtc-get 4 (car reqs)))
           0)
         (fn-rtc-reqs-octets (cdr reqs)))
    0))

; Retained size in words: one per cons and one per atom.  Every number the layer
; and its instances hold is a handle field, a resource below 2^64, or a counter
; (generation, incarnation, op) that grows by one per event, so below 2^62 --
; one word -- for any run of fewer than 2^62 events.
(defun fn-rtc-size (x)
  (declare (xargs :guard t))
  (if (consp x)
      (+ 1 (fn-rtc-size (car x)) (fn-rtc-size (cdr x)))
    1))

(defun fn-rtc-fsync-done-p (ev)
  (declare (xargs :guard t))
  (and (eq (fn-rtc-get 0 ev) :fsync)
       (eq (fn-rtc-get 0 (fn-rtc-get 1 ev)) :done)))

(encapsulate
  (((fn-rtc-m-init) => *)
   ((fn-rtc-m-step * * * *) => (mv * * *))
   ((fn-rtc-m-committedp *) => *)
   ((fn-rtc-m-c) => *)
   ((fn-rtc-m-max-reqs) => *)
   ((fn-rtc-m-max-state) => *))

  (local (defun fn-rtc-m-init () nil))
  (local (defun fn-rtc-m-step (m ev pool q)
           (declare (ignore m ev pool q))
           (mv nil nil 0)))
  (local (defun fn-rtc-m-committedp (m) (declare (ignore m)) nil))
  (local (defun fn-rtc-m-c () 0))
  (local (defun fn-rtc-m-max-reqs () 0))
  (local (defun fn-rtc-m-max-state () 1))

  (defthm fn-rtc-m-c-natp
    (natp (fn-rtc-m-c))
    :rule-classes :type-prescription)

  (defthm fn-rtc-m-max-reqs-natp
    (natp (fn-rtc-m-max-reqs))
    :rule-classes :type-prescription)

  ; The budget: the machine's own work plus the octets it asks the layer to
  ; write is within its quantum plus a constant.
  (defthm fn-rtc-m-step-is-charged
    (implies (natp q)
             (and (natp (mv-nth 2 (fn-rtc-m-step m ev pool q)))
                  (<= (+ (mv-nth 2 (fn-rtc-m-step m ev pool q))
                         (fn-rtc-reqs-octets (mv-nth 1 (fn-rtc-m-step m ev pool q))))
                      (+ q (fn-rtc-m-c))))))

  (defthm fn-rtc-m-step-requests-are-bounded
    (<= (len (mv-nth 1 (fn-rtc-m-step m ev pool q))) (fn-rtc-m-max-reqs)))

  (defthm fn-rtc-m-max-state-natp
    (natp (fn-rtc-m-max-state))
    :rule-classes :type-prescription)

  ; Retained state: an instance's state is never larger than a constant.
  (defthm fn-rtc-m-init-is-bounded
    (<= (fn-rtc-size (fn-rtc-m-init)) (fn-rtc-m-max-state)))

  (defthm fn-rtc-m-step-state-is-bounded
    (<= (fn-rtc-size (mv-nth 0 (fn-rtc-m-step m ev pool q))) (fn-rtc-m-max-state)))

  (defthm fn-rtc-m-init-is-uncommitted
    (not (fn-rtc-m-committedp (fn-rtc-m-init))))

  ; The commit point is the completion of a barrier, never a submission.
  (defthm fn-rtc-m-commits-only-on-fsync-done
    (implies (and (not (fn-rtc-m-committedp m))
                  (fn-rtc-m-committedp (mv-nth 0 (fn-rtc-m-step m ev pool q))))
             (fn-rtc-fsync-done-p ev))))

; -----------------------------------------------------------------------------
; The invariant

(defun fn-rtc-slots-okp (i slots)
  (declare (xargs :guard (natp i) :measure (len slots)))
  (if (consp slots)
      (and (fn-rtc-slotp (car slots))
           (if (zp i)
               (equal (car slots) *fn-rtc-listener*)
             (iff (null (fn-rtc-s-res (car slots)))
                  (eq (fn-rtc-s-status (car slots)) :free)))
           (fn-rtc-slots-okp (+ 1 i) (cdr slots)))
    (null slots)))

; A workspace belongs to an instance whose slot is live or closing at that
; incarnation; a lease's return pair names an instance slot (never the
; listener); a lease is held by some use at the buffer's generation.
(defun fn-rtc-pool-okp (h pool s)
  (declare (xargs :guard (natp h) :measure (len pool)))
  (if (consp pool)
      (let* ((b (car pool)) (o (fn-rtc-b-owner b)))
        (and (fn-rtc-bufferp b (fn-rtc-cap (fn-rtc-config s)))
             (case (fn-rtc-get 0 o)
               (:workspace
                (let ((slot (fn-rtc-slot (fn-rtc-get 1 o) s)))
                  (and (<= 1 (nfix (fn-rtc-get 1 o)))
                       (equal (fn-rtc-s-inc slot) (fn-rtc-get 2 o))
                       (member-eq (fn-rtc-s-status slot) '(:live :closing)))))
               (:leased
                (and (<= 1 (nfix (fn-rtc-get 1 o)))
                     (< (nfix (fn-rtc-get 1 o)) (fn-rtc-nslots (fn-rtc-config s)))
                     (fn-rtc-holds-p h (fn-rtc-b-gen b) (fn-rtc-uses s))))
               (otherwise t))
             (fn-rtc-pool-okp (+ 1 h) (cdr pool) s)))
    (null pool)))

; Count of uses holding buffer H at generation G (an :in lease has exactly one).
(defun fn-rtc-holders (h g uses)
  (declare (xargs :guard t))
  (if (consp uses)
      (+ (let ((hd (fn-rtc-u-hd (car uses))))
           (if (and (fn-rtc-handlep hd)
                    (equal (fn-rtc-h-buf hd) h)
                    (equal (fn-rtc-h-gen hd) g))
               1 0))
         (fn-rtc-holders h g (cdr uses)))
    0))

; One outstanding use against the state: it belongs to its slot's current
; incarnation and its op was issued (below next-op); a buffered use's handle
; names a buffer leased in the use's direction at its current generation,
; within the bytes (:out) or within capacity starting inside the bytes (:in),
; and an :in lease is exclusive; :accept is the listener's and :close is a
; closing slot's.
(defun fn-rtc-use-okp (u s)
  (declare (xargs :guard t))
  (let* ((kind (fn-rtc-get 0 u)) (id (nfix (fn-rtc-get 1 u))) (inc (fn-rtc-get 2 u))
         (hd (fn-rtc-u-hd u)) (cfg (fn-rtc-config s)))
    (and (fn-rtc-usep u)
         (< id (fn-rtc-nslots cfg))
         (< (nfix (fn-rtc-get 3 u)) (fn-rtc-next-op s))
         (fn-rtc-current-p id inc s)
         (iff (eq kind :accept) (equal id 0))
         (implies (eq kind :close)
                  (eq (fn-rtc-s-status (fn-rtc-slot id s)) :closing))
         (implies (and (not (eq kind :accept)) (not (eq kind :close)))
                  (member-eq (fn-rtc-get 0 u) *fn-rtc-machine-kinds*))
         (implies (fn-rtc-handlep hd)
                  (let* ((h (fn-rtc-h-buf hd)) (b (fn-rtc-buffer h s)))
                    (and (< h (fn-rtc-nbufs cfg))
                         (equal (fn-rtc-b-gen b) (fn-rtc-h-gen hd))
                         (eq (fn-rtc-get 0 (fn-rtc-b-owner b)) :leased)
                         (eq (fn-rtc-get 3 (fn-rtc-b-owner b))
                             (if (member-eq kind *fn-rtc-in-kinds*) :in :out))
                         (if (member-eq kind *fn-rtc-in-kinds*)
                             (and (<= (fn-rtc-h-off hd) (len (fn-rtc-b-bytes b)))
                                  (<= (+ (fn-rtc-h-off hd) (fn-rtc-h-len hd))
                                      (fn-rtc-cap cfg))
                                  (equal (fn-rtc-holders h (fn-rtc-h-gen hd)
                                                         (fn-rtc-uses s))
                                         1))
                           (<= (+ (fn-rtc-h-off hd) (fn-rtc-h-len hd))
                               (len (fn-rtc-b-bytes b))))))))))

; Uses are distinct per (kind id inc) (v1), hence per key, and their ops are
; distinct.
(defun fn-rtc-op-used-p (op uses)
  (declare (xargs :guard t))
  (if (consp uses)
      (or (equal (fn-rtc-get 3 (car uses)) op)
          (fn-rtc-op-used-p op (cdr uses)))
    nil))

(defun fn-rtc-uses-okp (uses s)
  (declare (xargs :guard t))
  (if (consp uses)
      (and (fn-rtc-use-okp (car uses) s)
           (not (fn-rtc-kind-out-p (fn-rtc-get 0 (car uses)) (fn-rtc-get 1 (car uses))
                                   (fn-rtc-get 2 (car uses)) (cdr uses)))
           (not (fn-rtc-op-used-p (fn-rtc-get 3 (car uses)) (cdr uses)))
           (fn-rtc-uses-okp (cdr uses) s))
    (null uses)))

; Every instance's retained state is within the machine's bound.
(defun fn-rtc-mstates-okp (ms)
  (declare (xargs :guard t))
  (if (consp ms)
      (and (<= (fn-rtc-size (car ms)) (fn-rtc-m-max-state))
           (fn-rtc-mstates-okp (cdr ms)))
    t))

; Some slot other than the listener is free.
(defun fn-rtc-free-slot (i slots)
  (declare (xargs :guard (natp i) :measure (len slots)))
  (if (consp slots)
      (if (and (not (zp i)) (eq (fn-rtc-s-status (car slots)) :free))
          i
        (fn-rtc-free-slot (+ 1 i) (cdr slots)))
    nil))

; A :draining slot still has an outstanding use (else it is retired to :free).
(defun fn-rtc-draining-okp (i slots uses)
  (declare (xargs :guard (natp i) :measure (len slots)))
  (if (consp slots)
      (and (implies (eq (fn-rtc-s-status (car slots)) :draining)
                    (fn-rtc-uses-of-slot-p i (fn-rtc-s-inc (car slots)) uses))
           (fn-rtc-draining-okp (+ 1 i) (cdr slots) uses))
    t))

(defun fn-rtc-invp (s)
  (declare (xargs :guard t))
  (let ((cfg (fn-rtc-config s)))
    (and (true-listp s) (equal (len s) 6)
         (natp (fn-rtc-get 5 s))
         (fn-rtc-configp cfg)
         (equal (len (fn-rtc-slots s)) (fn-rtc-nslots cfg))
         (fn-rtc-slots-okp 0 (fn-rtc-slots s))
         (equal (len (fn-rtc-pool s)) (fn-rtc-nbufs cfg))
         (fn-rtc-pool-okp 0 (fn-rtc-pool s) s)
         (fn-rtc-uses-okp (fn-rtc-uses s) s)
         (true-listp (fn-rtc-mstates s))
         (equal (len (fn-rtc-mstates s)) (fn-rtc-nslots cfg))
         (fn-rtc-mstates-okp (fn-rtc-mstates s))
         (fn-rtc-draining-okp 0 (fn-rtc-slots s) (fn-rtc-uses s))
         ;; the listener's :accept is armed exactly while a slot is free
         (iff (fn-rtc-free-slot 0 (fn-rtc-slots s))
              (fn-rtc-kind-out-p :accept 0 0 (fn-rtc-uses s))))))

; -----------------------------------------------------------------------------
; Ending a use

(defun fn-rtc-splice (bytes off data)
  (declare (xargs :guard t))
  (append (take (min (nfix off) (len bytes)) (true-list-fix bytes))
          (true-list-fix data)
          (nthcdr (+ (nfix off) (len data)) (true-list-fix bytes))))

; DATA is exactly N octets; walks at most N + 1 cells, so a completion's data is
; never scanned beyond the handle it is checked against.
(defun fn-rtc-octets-n-p (data n)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      (null data)
    (and (consp data)
         (fn-cbor-octetp (car data))
         (fn-rtc-octets-n-p (cdr data) (- n 1)))))

; What the instance is told: a completion that is malformed for its use (an
; :in completion whose data is not N octets within the handle, an :out count
; beyond the handle) is reported as (:failed :malformed-completion), and a
; failure reason outside the closed set as (:failed :other); the use ends
; either way, because the worker has let go of the buffer.  N is checked
; against the handle before the data is walked.
(defun fn-rtc-delivered-outcome (u e)
  (declare (xargs :guard t))
  (let* ((kind (fn-rtc-get 0 u)) (hd (fn-rtc-u-hd u)) (o (fn-rtc-e-outcome e))
         (tag (fn-rtc-get 0 o)) (n (fn-rtc-get 1 o)))
    (cond ((eq tag :failed)
           (if (member-eq n *fn-rtc-failure-reasons*) o '(:failed :other)))
          ((not (member-eq tag '(:done :short))) o)
          ((member-eq kind *fn-rtc-in-kinds*)
           (if (and (natp n)
                    (<= n (fn-rtc-h-len hd))
                    (fn-rtc-octets-n-p (fn-rtc-e-data e) n))
               o
             '(:failed :malformed-completion)))
          ((member-eq kind *fn-rtc-out-kinds*)
           (if (<= (nfix n) (fn-rtc-h-len hd)) o '(:failed :malformed-completion)))
          (t o))))

; The completion E ends use U (and only U: keys are distinct).
(defun fn-rtc-ends-use-p (e u)
  (declare (xargs :guard t))
  (and (fn-rtc-completionp e)
       (equal (fn-rtc-key e) (fn-rtc-key u))))

(defun fn-rtc-with-slot (id slot s)
  (declare (xargs :guard t))
  (fn-rtc-make (fn-rtc-config s) (fn-rtc-set id slot (fn-rtc-slots s))
               (fn-rtc-pool s) (fn-rtc-uses s) (fn-rtc-mstates s) (fn-rtc-next-op s)))

(defun fn-rtc-with-buffer (h b s)
  (declare (xargs :guard t))
  (fn-rtc-make (fn-rtc-config s) (fn-rtc-slots s) (fn-rtc-set h b (fn-rtc-pool s))
               (fn-rtc-uses s) (fn-rtc-mstates s) (fn-rtc-next-op s)))

(defun fn-rtc-with-uses (uses s)
  (declare (xargs :guard t))
  (fn-rtc-make (fn-rtc-config s) (fn-rtc-slots s) (fn-rtc-pool s)
               uses (fn-rtc-mstates s) (fn-rtc-next-op s)))

(defun fn-rtc-with-mstate (id m s)
  (declare (xargs :guard t))
  (fn-rtc-make (fn-rtc-config s) (fn-rtc-slots s) (fn-rtc-pool s)
               (fn-rtc-uses s) (fn-rtc-set id m (fn-rtc-mstates s)) (fn-rtc-next-op s)))

; Record a newly issued use (op = next-op) and advance the counter.
(defun fn-rtc-issue (use s)
  (declare (xargs :guard t))
  (fn-rtc-make (fn-rtc-config s) (fn-rtc-slots s) (fn-rtc-pool s)
               (cons use (fn-rtc-uses s)) (fn-rtc-mstates s) (+ 1 (fn-rtc-next-op s))))

; The buffer a lease returns to when its last use U ends by completion E: the
; return pair's workspace when that instance is live or closing, else :free;
; generation + 1; an :in completion's data spliced in only when it is live.
(defun fn-rtc-lease-return (u e b s)
  (declare (xargs :guard t))
  (let* ((hd (fn-rtc-u-hd u)) (o (fn-rtc-b-owner b))
         (rid (nfix (fn-rtc-get 1 o))) (rinc (fn-rtc-get 2 o))
         (back (and (fn-rtc-current-p rid rinc s)
                    (member-eq (fn-rtc-s-status (fn-rtc-slot rid s)) '(:live :closing))))
         (out (fn-rtc-delivered-outcome u e))
         (bytes (if (and back
                         (eq (fn-rtc-s-status (fn-rtc-slot rid s)) :live)
                         (member-eq (fn-rtc-get 0 u) *fn-rtc-in-kinds*)
                         (member-eq (fn-rtc-get 0 out) '(:done :short)))
                    (fn-rtc-splice (fn-rtc-b-bytes b) (fn-rtc-h-off hd) (fn-rtc-e-data e))
                  (fn-rtc-b-bytes b))))
    (list (+ 1 (fn-rtc-b-gen b)) (if back (list :workspace rid rinc) '(:free)) bytes)))

; U has been removed from S's uses.  If no use still holds its buffer at its
; generation, the lease ends.
(defun fn-rtc-end-lease (u e s)
  (declare (xargs :guard t))
  (let ((hd (fn-rtc-u-hd u)))
    (if (or (not (fn-rtc-handlep hd))
            (fn-rtc-holds-p (fn-rtc-h-buf hd) (fn-rtc-h-gen hd) (fn-rtc-uses s)))
        s
      (fn-rtc-with-buffer (fn-rtc-h-buf hd)
                          (fn-rtc-lease-return u e (fn-rtc-buffer (fn-rtc-h-buf hd) s) s)
                          s))))

; A :draining slot with no use left is retired to :free.
(defun fn-rtc-retire-drained (id s)
  (declare (xargs :guard t))
  (let ((slot (fn-rtc-slot id s)))
    (if (and (eq (fn-rtc-s-status slot) :draining)
             (not (fn-rtc-uses-of-slot-p id (fn-rtc-s-inc slot) (fn-rtc-uses s))))
        (fn-rtc-with-slot id (list (fn-rtc-s-inc slot) :free nil) s)
      s)))

; Remove the use E completes, end its lease if it was the last, retire a
; drained slot.
(defun fn-rtc-end-use (s e)
  (declare (xargs :guard t))
  (let* ((key (fn-rtc-key e))
         (u (fn-rtc-find-use key (fn-rtc-uses s))))
    (if (not (and (fn-rtc-completionp e) u))
        s
      (fn-rtc-retire-drained
       (fn-rtc-e-id e)
       (fn-rtc-end-lease u e (fn-rtc-with-uses (fn-rtc-remove-use key (fn-rtc-uses s)) s))))))

; -----------------------------------------------------------------------------
; Requests from one instance (ID INC)

; The cost model: one table probe or update is 1, one octet written is 1, and
; a scan of the outstanding-use table is charged at its bound, one use per
; (slot, kind) (`fn-rtc-uses-okp' keeps keys distinct and current).
(defun fn-rtc-use-bound (cfg)
  (declare (xargs :guard t))
  (* (fn-rtc-nslots cfg) (len *fn-rtc-kinds*)))

(defun fn-rtc-buffered-kind-p (kind)
  (declare (xargs :guard t))
  (or (member-eq kind *fn-rtc-in-kinds*) (member-eq kind *fn-rtc-out-kinds*)))

; Each request returns (mv s actions refused cost); a refusal changes nothing.

(defun fn-rtc-req-acquire (r id inc s)
  (declare (xargs :guard t))
  (let* ((h (fn-rtc-get 1 r)) (b (fn-rtc-buffer h s)))
    (if (and (natp h) (< h (fn-rtc-nbufs (fn-rtc-config s)))
             (equal (fn-rtc-b-owner b) '(:free)))
        (mv (fn-rtc-with-buffer h (list (+ 1 (fn-rtc-b-gen b)) (list :workspace id inc) nil) s)
            nil nil 1)
      (mv s nil (list r) 1))))

(defun fn-rtc-req-write (r id inc s)
  (declare (xargs :guard t))
  (let* ((h (fn-rtc-get 1 r)) (g (fn-rtc-get 2 r)) (off (fn-rtc-get 3 r))
         (data (fn-rtc-get 4 r)) (b (fn-rtc-buffer h s)))
    (if (and (natp h) (< h (fn-rtc-nbufs (fn-rtc-config s)))
             (equal (fn-rtc-b-owner b) (list :workspace id inc))
             (equal (fn-rtc-b-gen b) g)
             (natp off) (<= off (len (fn-rtc-b-bytes b)))
             (fn-cbor-octet-listp data)
             (<= (+ off (len data)) (fn-rtc-cap (fn-rtc-config s))))
        (mv (fn-rtc-with-buffer h (list g (list :workspace id inc)
                                        (fn-rtc-splice (fn-rtc-b-bytes b) off data))
                                s)
            nil nil (+ 1 (len data)))
      (mv s nil (list r) 1))))

(defun fn-rtc-req-release (r id inc s)
  (declare (xargs :guard t))
  (let* ((h (fn-rtc-get 1 r)) (g (fn-rtc-get 2 r)) (b (fn-rtc-buffer h s)))
    (if (and (natp h) (< h (fn-rtc-nbufs (fn-rtc-config s)))
             (equal (fn-rtc-b-owner b) (list :workspace id inc))
             (equal (fn-rtc-b-gen b) g))
        (mv (fn-rtc-with-buffer h (list g '(:free) (fn-rtc-b-bytes b)) s) nil nil 1)
      (mv s nil (list r) 1))))

(defun fn-rtc-req-close (r id inc s)
  (declare (xargs :guard t))
  (let ((slot (fn-rtc-slot id s)))
    (if (fn-rtc-live-p id inc s)
        (mv (fn-rtc-issue
             (list :close id inc (fn-rtc-next-op s) nil)
             (fn-rtc-with-slot id (list inc :closing (fn-rtc-s-res slot)) s))
            (list (list :close id inc (fn-rtc-next-op s) (list (fn-rtc-s-res slot))))
            nil
            (+ 1 (fn-rtc-use-bound (fn-rtc-config s))))
      (mv s nil (list r) 1))))

; May instance (ID INC) submit KIND on handle HD?  An :in kind needs its own
; workspace (the worker will write it); an :out kind its own workspace or a
; buffer already leased :out at the handle's generation (shared, immutable).
; An :in lease is never shared.
(defun fn-rtc-submit-okp (kind hd id inc s)
  (declare (xargs :guard t))
  (let* ((h (fn-rtc-h-buf hd)) (b (fn-rtc-buffer h s)) (o (fn-rtc-b-owner b))
         (own (equal o (list :workspace id inc))))
    (and (fn-rtc-handlep hd)
         (< h (fn-rtc-nbufs (fn-rtc-config s)))
         (equal (fn-rtc-b-gen b) (fn-rtc-h-gen hd))
         (if (member-eq kind *fn-rtc-in-kinds*)
             (and own
                  (<= (fn-rtc-h-off hd) (len (fn-rtc-b-bytes b)))
                  (<= (+ (fn-rtc-h-off hd) (fn-rtc-h-len hd))
                      (fn-rtc-cap (fn-rtc-config s))))
           (and (or own (and (eq (fn-rtc-get 0 o) :leased) (eq (fn-rtc-get 3 o) :out)))
                (<= (+ (fn-rtc-h-off hd) (fn-rtc-h-len hd))
                    (len (fn-rtc-b-bytes b))))))))

(defun fn-rtc-req-submit (r id inc s)
  (declare (xargs :guard t))
  (let* ((kind (fn-rtc-get 1 r)) (hd (fn-rtc-get 2 r)) (extra (fn-rtc-get 3 r))
         (res (fn-rtc-s-res (fn-rtc-slot id s)))
         (cost (+ 1 (fn-rtc-use-bound (fn-rtc-config s)))))
    (cond
     ((not (and (member-eq kind *fn-rtc-machine-kinds*)
                (fn-rtc-live-p id inc s)
                (fn-rtc-extrap extra)
                (not (fn-rtc-kind-out-p kind id inc (fn-rtc-uses s)))))
      (mv s nil (list r) cost))
     ((not (fn-rtc-buffered-kind-p kind))
      (if (null hd)
          (mv (fn-rtc-issue (list kind id inc (fn-rtc-next-op s) nil) s)
              (list (list kind id inc (fn-rtc-next-op s) (cons res extra)))
              nil cost)
        (mv s nil (list r) cost)))
     ((not (fn-rtc-submit-okp kind hd id inc s))
      (mv s nil (list r) cost))
     (t
      (let* ((h (fn-rtc-h-buf hd)) (b (fn-rtc-buffer h s))
             (dir (if (member-eq kind *fn-rtc-in-kinds*) :in :out))
             (s1 (if (equal (fn-rtc-b-owner b) (list :workspace id inc))
                     (fn-rtc-with-buffer
                      h (list (fn-rtc-b-gen b) (list :leased id inc dir) (fn-rtc-b-bytes b)) s)
                   s)))
        (mv (fn-rtc-issue (list kind id inc (fn-rtc-next-op s1) hd) s1)
            (list (list kind id inc (fn-rtc-next-op s1) (list* hd res extra)))
            nil cost))))))

(defthm fn-rtc-req-acquire-lists
  (and (true-listp (mv-nth 1 (fn-rtc-req-acquire r id inc s)))
       (true-listp (mv-nth 2 (fn-rtc-req-acquire r id inc s)))))

(defthm fn-rtc-req-write-lists
  (and (true-listp (mv-nth 1 (fn-rtc-req-write r id inc s)))
       (true-listp (mv-nth 2 (fn-rtc-req-write r id inc s)))))

(defthm fn-rtc-req-release-lists
  (and (true-listp (mv-nth 1 (fn-rtc-req-release r id inc s)))
       (true-listp (mv-nth 2 (fn-rtc-req-release r id inc s)))))

(defthm fn-rtc-req-close-lists
  (and (true-listp (mv-nth 1 (fn-rtc-req-close r id inc s)))
       (true-listp (mv-nth 2 (fn-rtc-req-close r id inc s)))))

(defthm fn-rtc-req-submit-lists
  (and (true-listp (mv-nth 1 (fn-rtc-req-submit r id inc s)))
       (true-listp (mv-nth 2 (fn-rtc-req-submit r id inc s))))
  :hints (("Goal" :in-theory (disable fn-rtc-submit-okp fn-rtc-issue fn-rtc-with-buffer
                                      fn-rtc-kind-out-p fn-rtc-live-p fn-rtc-buffered-kind-p
                                      fn-rtc-extrap))))

; Ask the host to finish this instance's outstanding KIND action early: the
; :cancel action names that action's op.  The use stays; nothing in the pool
; changes.  Refused when no such use exists.
(defun fn-rtc-req-cancel (r id inc s)
  (declare (xargs :guard t))
  (let ((kind (fn-rtc-get 1 r)))
    (if (and (member-eq kind *fn-rtc-machine-kinds*)
             (fn-rtc-current-p id inc s)
             (fn-rtc-kind-out-p kind id inc (fn-rtc-uses s)))
        (mv s (list (list :cancel id inc (fn-rtc-kind-op kind id inc (fn-rtc-uses s)) (list kind)))
            nil
            (+ 1 (fn-rtc-use-bound (fn-rtc-config s))))
      (mv s nil (list r) (+ 1 (fn-rtc-use-bound (fn-rtc-config s)))))))

(defthm fn-rtc-req-cancel-lists
  (and (true-listp (mv-nth 1 (fn-rtc-req-cancel r id inc s)))
       (true-listp (mv-nth 2 (fn-rtc-req-cancel r id inc s)))))

(defun fn-rtc-request (r id inc s)
  (declare (xargs :guard t))
  (case (fn-rtc-get 0 r)
    (:acquire (fn-rtc-req-acquire r id inc s))
    (:write (fn-rtc-req-write r id inc s))
    (:release (fn-rtc-req-release r id inc s))
    (:close (fn-rtc-req-close r id inc s))
    (:submit (fn-rtc-req-submit r id inc s))
    (:cancel (fn-rtc-req-cancel r id inc s))
    (otherwise (mv s nil (list r) 1))))

(defthm fn-rtc-request-lists
  (and (true-listp (mv-nth 1 (fn-rtc-request r id inc s)))
       (true-listp (mv-nth 2 (fn-rtc-request r id inc s))))
  :hints (("Goal" :in-theory (disable fn-rtc-req-acquire fn-rtc-req-write fn-rtc-req-release
                                      fn-rtc-req-close fn-rtc-req-submit fn-rtc-req-cancel))))

(in-theory (disable fn-rtc-request))

(defun fn-rtc-requests (reqs id inc s)
  (declare (xargs :guard t))
  (if (consp reqs)
      (mv-let (s1 acts1 ref1 c1)
        (fn-rtc-request (car reqs) id inc s)
        (mv-let (s2 acts2 ref2 c2)
          (fn-rtc-requests (cdr reqs) id inc s1)
          (mv s2 (append acts1 acts2) (append ref1 ref2) (+ (nfix c1) (nfix c2)))))
    (mv s nil nil 0)))

(defthm fn-rtc-requests-lists
  (true-listp (mv-nth 1 (fn-rtc-requests reqs id inc s))))

; -----------------------------------------------------------------------------
; Admission: arm the listener's :accept whenever a slot is free and none is
; outstanding.

(defun fn-rtc-rearm (s)
  (declare (xargs :guard t))
  (if (and (fn-rtc-free-slot 0 (fn-rtc-slots s))
           (not (fn-rtc-kind-out-p :accept 0 0 (fn-rtc-uses s))))
      (mv (fn-rtc-issue (list :accept 0 0 (fn-rtc-next-op s) nil) s)
          (list (list :accept 0 0 (fn-rtc-next-op s) (list nil))))
    (mv s nil)))

(defthm fn-rtc-rearm-lists
  (true-listp (mv-nth 1 (fn-rtc-rearm s))))

; Release every workspace of (ID INC) to :free.
(defun fn-rtc-release-all (pool id inc)
  (declare (xargs :guard t))
  (if (consp pool)
      (cons (if (equal (fn-rtc-b-owner (car pool)) (list :workspace id inc))
                (list (fn-rtc-b-gen (car pool)) '(:free) (fn-rtc-b-bytes (car pool)))
              (car pool))
            (fn-rtc-release-all (cdr pool) id inc))
    nil))

; -----------------------------------------------------------------------------
; Which completions act on an instance: a use is outstanding under its key,
; the slot is at that incarnation, and the slot is live (or closing, for its
; own :close).  Everything else only ends its use.

(defun fn-rtc-acts-on-p (s e)
  (declare (xargs :guard t))
  (and (fn-rtc-completionp e)
       (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s))
       (let ((slot (fn-rtc-slot (fn-rtc-e-id e) s)))
         (and (equal (fn-rtc-s-inc slot) (fn-rtc-e-inc e))
              (if (eq (fn-rtc-e-kind e) :close)
                  (eq (fn-rtc-s-status slot) :closing)
                (eq (fn-rtc-s-status slot) :live))))))

; The instance an event is for: the new slot for an :accept, else its id.
(defun fn-rtc-target (s e)
  (declare (xargs :guard t))
  (if (and (eq (fn-rtc-e-kind e) :accept)
           (fn-rtc-acts-on-p s e)
           (eq (fn-rtc-get 0 (fn-rtc-e-outcome e)) :done))
      (nfix (fn-rtc-free-slot 0 (fn-rtc-slots s)))
    (fn-rtc-e-id e)))

; The borrow view: the pool with every :in-leased buffer's bytes hidden.
(defun fn-rtc-borrow (pool)
  (declare (xargs :guard t))
  (if (consp pool)
      (cons (if (and (eq (fn-rtc-get 0 (fn-rtc-b-owner (car pool))) :leased)
                     (eq (fn-rtc-get 3 (fn-rtc-b-owner (car pool))) :in))
                (list (fn-rtc-b-gen (car pool)) (fn-rtc-b-owner (car pool)) nil)
              (car pool))
            (fn-rtc-borrow (cdr pool)))
    nil))

; Two pools agree except in the bytes of :in-leased buffers (T14).
(defun fn-rtc-pools-agree-off-in-leases-p (p1 p2)
  (declare (xargs :guard t))
  (if (consp p1)
      (and (consp p2)
           (let ((b1 (car p1)) (b2 (car p2)))
             (if (and (eq (fn-rtc-get 0 (fn-rtc-b-owner b1)) :leased)
                      (eq (fn-rtc-get 3 (fn-rtc-b-owner b1)) :in))
                 (and (equal (fn-rtc-b-gen b1) (fn-rtc-b-gen b2))
                      (equal (fn-rtc-b-owner b1) (fn-rtc-b-owner b2)))
               (equal b1 b2)))
           (fn-rtc-pools-agree-off-in-leases-p (cdr p1) (cdr p2)))
    (atom p2)))

; Deliver EV to instance (ID INC) and process its requests.
(defun fn-rtc-deliver (s id inc ev q)
  (declare (xargs :guard t))
  (mv-let (m2 reqs cm)
    (fn-rtc-m-step (fn-rtc-mstate id s) ev (fn-rtc-borrow (fn-rtc-pool s)) (nfix q))
    (mv-let (s2 acts refused cr)
      (fn-rtc-requests reqs id inc (fn-rtc-with-mstate id m2 s))
      (mv s2 acts refused (+ (nfix cm) (nfix cr))))))

(defthm fn-rtc-deliver-types
  (and (true-listp (mv-nth 1 (fn-rtc-deliver s id inc ev q)))
       (natp (mv-nth 3 (fn-rtc-deliver s id inc ev q))))
  :hints (("Goal" :in-theory (disable fn-rtc-requests fn-rtc-with-mstate))))

(in-theory (disable fn-rtc-deliver fn-rtc-rearm fn-rtc-end-use fn-rtc-requests))

; -----------------------------------------------------------------------------
; The step: (mv s2 actions refused cost).

; The listener's :accept completed with outcome OUT, its use already ended
; (S1): bind the least free slot at its next incarnation, start its machine
; with the delivery (:accept OUT), re-arm.  (mv s actions refused cost).
(defun fn-rtc-accept-branch (s1 out q)
  (declare (xargs :guard t))
  (let ((j (fn-rtc-free-slot 0 (fn-rtc-slots s1)))
        (r (fn-rtc-get 1 out)))
    (if (and (eq (fn-rtc-get 0 out) :done) j (natp r) (< r (expt 2 64)))
        (let* ((jinc (+ 1 (fn-rtc-s-inc (fn-rtc-slot j s1))))
               (s2 (fn-rtc-with-mstate
                    j (fn-rtc-m-init)
                    (fn-rtc-with-slot j (list jinc :live r) s1))))
          (mv-let (s3 acts refused c)
            (fn-rtc-deliver s2 j jinc (list :accept out) q)
            (mv-let (s4 acts2) (fn-rtc-rearm s3)
              (mv s4 (append acts acts2) refused c))))
      (mv-let (s2 acts2) (fn-rtc-rearm s1)
        (mv s2 acts2 nil 0)))))

; Slot ID's :close completed, its use already ended (S1): release its
; workspaces, mark it :draining (actions outstanding) or :free, reset its
; machine, re-arm.  (mv s actions).
(defun fn-rtc-close-branch (s1 id inc)
  (declare (xargs :guard t))
  (let* ((s2 (fn-rtc-make (fn-rtc-config s1) (fn-rtc-slots s1)
                          (fn-rtc-release-all (fn-rtc-pool s1) id inc)
                          (fn-rtc-uses s1) (fn-rtc-mstates s1) (fn-rtc-next-op s1)))
         (status (if (fn-rtc-uses-of-slot-p id inc (fn-rtc-uses s2)) :draining :free))
         (s3 (fn-rtc-with-mstate
              id (fn-rtc-m-init)
              (fn-rtc-with-slot id (list inc status (if (eq status :free) nil
                                                      (fn-rtc-s-res (fn-rtc-slot id s2))))
                                s2))))
    (fn-rtc-rearm s3)))

(defun fn-rtc-step* (s e q)
  (declare (xargs :guard t))
  (let* ((cfg (fn-rtc-config s))
         (base (+ 4 (* 6 (fn-rtc-use-bound cfg)) (* 2 (fn-rtc-nslots cfg)))))
    (if (not (fn-rtc-acts-on-p s e))
        (mv-let (s2 acts) (fn-rtc-rearm (fn-rtc-end-use s e))
          (mv s2 acts nil base))
      (let* ((s1 (fn-rtc-end-use s e))
             (kind (fn-rtc-e-kind e)) (id (fn-rtc-e-id e)) (inc (fn-rtc-e-inc e))
             (u (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))
             (out (fn-rtc-delivered-outcome u e))
             ;; checking and landing an :in completion's data: at most the
             ;; handle's length, itself within the buffer capacity
             (base (+ base (if (member-eq kind *fn-rtc-in-kinds*)
                               (fn-rtc-h-len (fn-rtc-u-hd u))
                             0))))
        (cond
         ((eq kind :accept)
          (mv-let (s2 acts refused c) (fn-rtc-accept-branch s1 out q)
            (mv s2 acts refused (+ base (nfix c)))))
         ((eq kind :close)
          (mv-let (s2 acts) (fn-rtc-close-branch s1 id inc)
            (mv s2 acts nil (+ base (fn-rtc-nbufs cfg)))))
         (t
          (mv-let (s2 acts refused c)
            (fn-rtc-deliver s1 id inc (list kind out) q)
            (mv s2 acts refused (+ base c)))))))))

(defun fn-rtc-step (s e q)
  (declare (xargs :guard t))
  (mv-let (s2 acts refused cost) (fn-rtc-step* s e q)
    (declare (ignore refused cost))
    (mv s2 acts)))

(defun fn-rtc-step-cost (s e q)
  (declare (xargs :guard t))
  (mv-let (s2 acts refused cost) (fn-rtc-step* s e q)
    (declare (ignore s2 acts refused))
    cost))

; Retained output of a step: the octets the emitted actions name.  An action
; carries a handle, never bytes; the handle's len is within the configured
; buffer capacity (`fn-rtc-use-okp'), so this is the measure section 1 bounds.
(defun fn-rtc-actions-octets (acts)
  (declare (xargs :guard t))
  (if (consp acts)
      (+ (let ((hd (fn-rtc-get 0 (fn-rtc-get 4 (car acts)))))
           (if (fn-rtc-handlep hd) (fn-rtc-h-len hd) 0))
         (fn-rtc-actions-octets (cdr acts)))
    0))

(defun fn-rtc-step-c (cfg)
  (declare (xargs :guard t))
  (+ 4 (fn-rtc-m-c) (* 2 (fn-rtc-nslots cfg)) (fn-rtc-nbufs cfg) (fn-rtc-cap cfg)
     (* 6 (fn-rtc-use-bound cfg))
     (* (fn-rtc-m-max-reqs) (+ 1 (fn-rtc-use-bound cfg)))))

; -----------------------------------------------------------------------------
; The initial state: every instance slot free, every buffer free, the
; listener's :accept armed.

(defun fn-rtc-free-slots (n)
  (declare (xargs :guard (natp n)))
  (if (zp n) nil (cons '(0 :free nil) (fn-rtc-free-slots (- n 1)))))

(defun fn-rtc-free-pool (n)
  (declare (xargs :guard (natp n)))
  (if (zp n) nil (cons '(0 (:free) nil) (fn-rtc-free-pool (- n 1)))))

(defun fn-rtc-init (cfg)
  (declare (xargs :guard t))
  (fn-rtc-rearm
   (fn-rtc-make cfg
                (cons *fn-rtc-listener* (fn-rtc-free-slots (nfix (- (fn-rtc-nslots cfg) 1))))
                (fn-rtc-free-pool (fn-rtc-nbufs cfg))
                nil
                (make-list (fn-rtc-nslots cfg) :initial-element nil)
                0)))

; =============================================================================
; PROOFS
;
; The state record's accessors are disabled; every operation has frame lemmas
; for the components it leaves alone; keystones are stated in the words of the
; statements section and proved from the frames.

(defthm fn-rtc-get-of-set
  (equal (fn-rtc-get i (fn-rtc-set j v l))
         (if (and (equal (nfix i) (nfix j)) (< (nfix j) (len l)))
             v
           (fn-rtc-get i l))))
(defthm fn-rtc-len-of-set
  (equal (len (fn-rtc-set j v l)) (len l)))
(defthm fn-rtc-set-true-listp
  (implies (true-listp l) (true-listp (fn-rtc-set j v l))))
(defthm fn-rtc-make-accessors
  (and (equal (fn-rtc-config (fn-rtc-make c sl p u m n)) c)
       (equal (fn-rtc-slots (fn-rtc-make c sl p u m n)) sl)
       (equal (fn-rtc-pool (fn-rtc-make c sl p u m n)) p)
       (equal (fn-rtc-uses (fn-rtc-make c sl p u m n)) u)
       (equal (fn-rtc-mstates (fn-rtc-make c sl p u m n)) m)
       (equal (fn-rtc-next-op (fn-rtc-make c sl p u m n)) (nfix n))))

(in-theory (disable fn-rtc-config fn-rtc-slots fn-rtc-pool fn-rtc-uses fn-rtc-mstates fn-rtc-make
                    fn-rtc-with-slot fn-rtc-with-buffer fn-rtc-with-uses fn-rtc-with-mstate
                    fn-rtc-slot fn-rtc-buffer fn-rtc-mstate))
(defthm fn-rtc-with-accessors
  (and (equal (fn-rtc-uses (fn-rtc-with-uses u s)) u)
       (equal (fn-rtc-uses (fn-rtc-with-slot i x s)) (fn-rtc-uses s))
       (equal (fn-rtc-uses (fn-rtc-with-buffer i x s)) (fn-rtc-uses s))
       (equal (fn-rtc-uses (fn-rtc-with-mstate i x s)) (fn-rtc-uses s))
       (equal (fn-rtc-slots (fn-rtc-with-uses u s)) (fn-rtc-slots s))
       (equal (fn-rtc-slots (fn-rtc-with-slot i x s)) (fn-rtc-set i x (fn-rtc-slots s)))
       (equal (fn-rtc-slots (fn-rtc-with-buffer i x s)) (fn-rtc-slots s))
       (equal (fn-rtc-slots (fn-rtc-with-mstate i x s)) (fn-rtc-slots s))
       (equal (fn-rtc-pool (fn-rtc-with-uses u s)) (fn-rtc-pool s))
       (equal (fn-rtc-pool (fn-rtc-with-slot i x s)) (fn-rtc-pool s))
       (equal (fn-rtc-pool (fn-rtc-with-buffer i x s)) (fn-rtc-set i x (fn-rtc-pool s)))
       (equal (fn-rtc-pool (fn-rtc-with-mstate i x s)) (fn-rtc-pool s))
       (equal (fn-rtc-mstates (fn-rtc-with-uses u s)) (fn-rtc-mstates s))
       (equal (fn-rtc-mstates (fn-rtc-with-slot i x s)) (fn-rtc-mstates s))
       (equal (fn-rtc-mstates (fn-rtc-with-buffer i x s)) (fn-rtc-mstates s))
       (equal (fn-rtc-mstates (fn-rtc-with-mstate i x s)) (fn-rtc-set i x (fn-rtc-mstates s)))
       (equal (fn-rtc-config (fn-rtc-with-uses u s)) (fn-rtc-config s))
       (equal (fn-rtc-config (fn-rtc-with-slot i x s)) (fn-rtc-config s))
       (equal (fn-rtc-config (fn-rtc-with-buffer i x s)) (fn-rtc-config s))
       (equal (fn-rtc-config (fn-rtc-with-mstate i x s)) (fn-rtc-config s)))
  :hints (("Goal" :in-theory (enable fn-rtc-with-slot fn-rtc-with-buffer fn-rtc-with-uses fn-rtc-with-mstate))))
(defthm fn-rtc-uses-okp-member
  (implies (and (fn-rtc-uses-okp uses s) (member-equal u uses))
           (fn-rtc-use-okp u s))
  :hints (("Goal" :in-theory (disable fn-rtc-use-okp fn-rtc-find-use fn-rtc-key))))
(defthm fn-rtc-completion-kind-nonnil
  (implies (fn-rtc-completionp e) (fn-rtc-get 0 e))
  :rule-classes :forward-chaining)

(defthm fn-rtc-key-equal-kind
  (implies (equal (fn-rtc-key e) (fn-rtc-key u))
           (equal (fn-rtc-get 0 u) (fn-rtc-get 0 e)))
  :rule-classes :forward-chaining)

(defthm fn-rtc-invp-uses-okp
  (implies (fn-rtc-invp s) (fn-rtc-uses-okp (fn-rtc-uses s) s))
  :hints (("Goal" :in-theory (disable fn-rtc-uses-okp fn-rtc-slots-okp fn-rtc-pool-okp fn-rtc-draining-okp fn-rtc-free-slot fn-rtc-find-use)))
  :rule-classes :forward-chaining)

(defthm fn-rtc-find-use-implies-op-used
  (implies (not (fn-rtc-op-used-p (fn-rtc-get 3 x) l))
           (not (fn-rtc-find-use (fn-rtc-key x) l))))

(defthm fn-rtc-remove-use-removes-distinct-key
  (implies (fn-rtc-uses-okp uses s)
           (not (fn-rtc-find-use key (fn-rtc-remove-use key uses))))
  :hints (("Goal" :in-theory (disable fn-rtc-use-okp fn-rtc-key))))

(defthm fn-rtc-find-use-key-of-member
  (implies (and (member-equal u uses) (equal (fn-rtc-key e) (fn-rtc-key u))
                (fn-rtc-get 0 u))
           (fn-rtc-find-use (fn-rtc-key e) uses)))


(defun fn-rtc-leasedp (h s)
  (declare (xargs :guard t))
  (eq (fn-rtc-get 0 (fn-rtc-b-owner (fn-rtc-buffer h s))) :leased))

(defthm fn-rtc-buffer-of-with
  (and (equal (fn-rtc-buffer h (fn-rtc-with-buffer k b s))
              (if (and (equal (nfix h) (nfix k)) (< (nfix k) (len (fn-rtc-pool s))))
                  b
                (fn-rtc-buffer h s)))
       (equal (fn-rtc-buffer h (fn-rtc-with-slot k x s)) (fn-rtc-buffer h s))
       (equal (fn-rtc-buffer h (fn-rtc-with-uses u s)) (fn-rtc-buffer h s))
       (equal (fn-rtc-buffer h (fn-rtc-with-mstate k x s)) (fn-rtc-buffer h s)))
  :hints (("Goal" :in-theory (enable fn-rtc-buffer))))

(defthm fn-rtc-slot-of-with
  (and (equal (fn-rtc-slot i (fn-rtc-with-slot k x s))
              (if (and (equal (nfix i) (nfix k)) (< (nfix k) (len (fn-rtc-slots s))))
                  x
                (fn-rtc-slot i s)))
       (equal (fn-rtc-slot i (fn-rtc-with-buffer k b s)) (fn-rtc-slot i s))
       (equal (fn-rtc-slot i (fn-rtc-with-uses u s)) (fn-rtc-slot i s))
       (equal (fn-rtc-slot i (fn-rtc-with-mstate k m s)) (fn-rtc-slot i s)))
  :hints (("Goal" :in-theory (enable fn-rtc-slot))))

(defthm fn-rtc-mstate-of-with
  (and (equal (fn-rtc-mstate i (fn-rtc-with-mstate k m s))
              (if (and (equal (nfix i) (nfix k)) (< (nfix k) (len (fn-rtc-mstates s))))
                  m
                (fn-rtc-mstate i s)))
       (equal (fn-rtc-mstate i (fn-rtc-with-buffer k b s)) (fn-rtc-mstate i s))
       (equal (fn-rtc-mstate i (fn-rtc-with-uses u s)) (fn-rtc-mstate i s))
       (equal (fn-rtc-mstate i (fn-rtc-with-slot k x s)) (fn-rtc-mstate i s)))
  :hints (("Goal" :in-theory (enable fn-rtc-mstate))))

(defthm fn-rtc-issue-frame
  (and (equal (fn-rtc-uses (fn-rtc-issue x s)) (cons x (fn-rtc-uses s)))
       (equal (fn-rtc-next-op (fn-rtc-issue x s)) (+ 1 (fn-rtc-next-op s)))
       (equal (fn-rtc-config (fn-rtc-issue x s)) (fn-rtc-config s))
       (equal (fn-rtc-slots (fn-rtc-issue x s)) (fn-rtc-slots s))
       (equal (fn-rtc-pool (fn-rtc-issue x s)) (fn-rtc-pool s))
       (equal (fn-rtc-mstates (fn-rtc-issue x s)) (fn-rtc-mstates s))
       (equal (fn-rtc-buffer h (fn-rtc-issue x s)) (fn-rtc-buffer h s))
       (equal (fn-rtc-slot h (fn-rtc-issue x s)) (fn-rtc-slot h s))
       (equal (fn-rtc-mstate h (fn-rtc-issue x s)) (fn-rtc-mstate h s)))
  :hints (("Goal" :in-theory (e/d (fn-rtc-issue fn-rtc-buffer fn-rtc-slot fn-rtc-mstate) (fn-rtc-next-op)))))

(in-theory (disable fn-rtc-issue fn-rtc-next-op))

(defthm fn-rtc-get-of-non-natp
  (implies (not (natp i)) (equal (fn-rtc-get i l) (fn-rtc-get 0 l))))
(defthm fn-rtc-buffer-of-non-natp
  (implies (not (natp h)) (equal (fn-rtc-buffer h s) (fn-rtc-buffer 0 s)))
  :hints (("Goal" :in-theory (enable fn-rtc-buffer))))
(defthm fn-rtc-slot-of-non-natp
  (implies (not (natp h)) (equal (fn-rtc-slot h s) (fn-rtc-slot 0 s)))
  :hints (("Goal" :in-theory (enable fn-rtc-slot))))
(defthm fn-rtc-mstate-of-non-natp
  (implies (not (natp h)) (equal (fn-rtc-mstate h s) (fn-rtc-mstate 0 s)))
  :hints (("Goal" :in-theory (enable fn-rtc-mstate))))
(defthm fn-rtc-req-acquire-keeps-leased
  (implies (fn-rtc-leasedp h s)
           (equal (fn-rtc-buffer h (mv-nth 0 (fn-rtc-req-acquire r id inc s))) (fn-rtc-buffer h s))))
(defthm fn-rtc-req-write-keeps-leased
  (implies (fn-rtc-leasedp h s)
           (equal (fn-rtc-buffer h (mv-nth 0 (fn-rtc-req-write r id inc s))) (fn-rtc-buffer h s))))
(defthm fn-rtc-req-release-keeps-leased
  (implies (fn-rtc-leasedp h s)
           (equal (fn-rtc-buffer h (mv-nth 0 (fn-rtc-req-release r id inc s))) (fn-rtc-buffer h s))))
(defthm fn-rtc-req-close-keeps-buffers
  (equal (fn-rtc-buffer h (mv-nth 0 (fn-rtc-req-close r id inc s))) (fn-rtc-buffer h s)))
(defthm fn-rtc-req-cancel-keeps-state
  (equal (mv-nth 0 (fn-rtc-req-cancel r id inc s)) s))
(defthm fn-rtc-req-submit-keeps-leased
  (implies (fn-rtc-leasedp h s)
           (equal (fn-rtc-buffer h (mv-nth 0 (fn-rtc-req-submit r id inc s))) (fn-rtc-buffer h s)))
  :hints (("Goal" :in-theory (disable fn-rtc-submit-okp fn-rtc-find-use fn-rtc-live-p))))
(defthm fn-rtc-request-keeps-leased
  (implies (fn-rtc-leasedp h s)
           (equal (fn-rtc-buffer h (mv-nth 0 (fn-rtc-request r id inc s))) (fn-rtc-buffer h s)))
  :hints (("Goal" :in-theory (e/d (fn-rtc-request)
                                  (mv-nth fn-rtc-leasedp fn-rtc-req-acquire fn-rtc-req-write fn-rtc-req-release
                                   fn-rtc-req-close fn-rtc-req-cancel fn-rtc-req-submit)))))
(defthm fn-rtc-requests-keeps-leased
  (implies (fn-rtc-leasedp h s)
           (equal (fn-rtc-buffer h (mv-nth 0 (fn-rtc-requests reqs id inc s))) (fn-rtc-buffer h s)))
  :hints (("Goal" :in-theory (e/d (fn-rtc-requests) (mv-nth fn-rtc-request))
           :induct (fn-rtc-requests reqs id inc s))))
(defthm fn-rtc-holds-p-of-member
  (implies (and (member-equal u uses) (fn-rtc-handlep (fn-rtc-u-hd u)))
           (fn-rtc-holds-p (fn-rtc-h-buf (fn-rtc-u-hd u)) (fn-rtc-h-gen (fn-rtc-u-hd u)) uses))
  :hints (("Goal" :in-theory (disable fn-rtc-handlep fn-rtc-h-buf fn-rtc-h-gen))))

(defthm fn-rtc-member-of-remove-use
  (implies (and (member-equal u uses) (not (equal (fn-rtc-key u) k)))
           (member-equal u (fn-rtc-remove-use k uses)))
  :hints (("Goal" :in-theory (disable fn-rtc-key))))

(defthm fn-rtc-find-use-is-member
  (implies (fn-rtc-find-use k uses)
           (member-equal (fn-rtc-find-use k uses) uses))
  :hints (("Goal" :in-theory (disable fn-rtc-key) :induct (fn-rtc-find-use k uses))))

(defthm fn-rtc-key-of-find-use
  (implies (fn-rtc-find-use k uses)
           (equal (fn-rtc-key (fn-rtc-find-use k uses)) k))
  :hints (("Goal" :in-theory (disable fn-rtc-key) :induct (fn-rtc-find-use k uses))))

(defthm fn-rtc-use-okp-lease
  (implies (and (fn-rtc-use-okp u s) (fn-rtc-handlep (fn-rtc-u-hd u)))
           (and (equal (fn-rtc-b-gen (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd u)) s))
                       (fn-rtc-h-gen (fn-rtc-u-hd u)))
                (fn-rtc-leasedp (fn-rtc-h-buf (fn-rtc-u-hd u)) s)))
  :hints (("Goal" :in-theory (disable fn-rtc-handlep fn-rtc-h-buf fn-rtc-h-gen fn-rtc-holders
                                      fn-rtc-current-p fn-rtc-usep))))


; Ending a use, piece by piece.
(defthm fn-rtc-retire-drained-frame
  (and (equal (fn-rtc-uses (fn-rtc-retire-drained id s)) (fn-rtc-uses s))
       (equal (fn-rtc-buffer h (fn-rtc-retire-drained id s)) (fn-rtc-buffer h s))
       (equal (fn-rtc-mstate j (fn-rtc-retire-drained id s)) (fn-rtc-mstate j s))
       (equal (fn-rtc-config (fn-rtc-retire-drained id s)) (fn-rtc-config s)))
  :hints (("Goal" :in-theory (disable fn-rtc-uses-of-slot-p))))

(defthm fn-rtc-end-lease-frame
  (and (equal (fn-rtc-uses (fn-rtc-end-lease u e s)) (fn-rtc-uses s))
       (equal (fn-rtc-slot j (fn-rtc-end-lease u e s)) (fn-rtc-slot j s))
       (equal (fn-rtc-mstate j (fn-rtc-end-lease u e s)) (fn-rtc-mstate j s))
       (equal (fn-rtc-config (fn-rtc-end-lease u e s)) (fn-rtc-config s)))
  :hints (("Goal" :in-theory (disable fn-rtc-lease-return fn-rtc-holds-p fn-rtc-handlep))))

(defthm fn-rtc-end-lease-buffer-unchanged
  (implies (or (not (fn-rtc-handlep (fn-rtc-u-hd u)))
               (not (equal (nfix h) (fn-rtc-h-buf (fn-rtc-u-hd u))))
               (fn-rtc-holds-p (fn-rtc-h-buf (fn-rtc-u-hd u)) (fn-rtc-h-gen (fn-rtc-u-hd u))
                               (fn-rtc-uses s)))
           (equal (fn-rtc-buffer h (fn-rtc-end-lease u e s)) (fn-rtc-buffer h s)))
  :hints (("Goal" :in-theory (disable fn-rtc-lease-return fn-rtc-holds-p fn-rtc-handlep fn-rtc-h-buf fn-rtc-h-gen))))

(in-theory (disable fn-rtc-retire-drained fn-rtc-end-lease fn-rtc-lease-return))

(defthm fn-rtc-uses-of-end-use
  (equal (fn-rtc-uses (fn-rtc-end-use s e))
         (if (and (fn-rtc-completionp e) (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))
             (fn-rtc-remove-use (fn-rtc-key e) (fn-rtc-uses s))
           (fn-rtc-uses s)))
  :hints (("Goal" :in-theory (enable fn-rtc-end-use))))

(defthm fn-rtc-end-use-keeps-other-leases
  (implies (and (fn-rtc-invp s)
                (member-equal u (fn-rtc-uses s))
                (fn-rtc-handlep (fn-rtc-u-hd u))
                (not (fn-rtc-ends-use-p e u)))
           (equal (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd u)) (fn-rtc-end-use s e))
                  (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd u)) s)))
  :hints (("Goal" :in-theory (e/d (fn-rtc-ends-use-p fn-rtc-end-use)
                                  (fn-rtc-invp fn-rtc-use-okp fn-rtc-completionp fn-rtc-find-use
                                   fn-rtc-remove-use fn-rtc-holds-p fn-rtc-handlep fn-rtc-key
                                   fn-rtc-h-buf fn-rtc-h-gen fn-rtc-leasedp
                                   fn-rtc-holds-p-of-member fn-rtc-use-okp-lease fn-rtc-uses-okp-member
                                   fn-rtc-member-of-remove-use))
           :do-not-induct t
           :use ((:instance fn-rtc-invp-uses-okp)
                 (:instance fn-rtc-uses-okp-member (uses (fn-rtc-uses s)))
                 (:instance fn-rtc-uses-okp-member (uses (fn-rtc-uses s))
                            (u (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s))))
                 (:instance fn-rtc-use-okp-lease)
                 (:instance fn-rtc-use-okp-lease (u (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s))))
                 (:instance fn-rtc-find-use-is-member (k (fn-rtc-key e)) (uses (fn-rtc-uses s)))
                 (:instance fn-rtc-member-of-remove-use (uses (fn-rtc-uses s)) (k (fn-rtc-key e)))
                 (:instance fn-rtc-holds-p-of-member (uses (fn-rtc-remove-use (fn-rtc-key e) (fn-rtc-uses s))))
                 (:instance fn-rtc-end-lease-buffer-unchanged (h (fn-rtc-h-buf (fn-rtc-u-hd u)))
                            (u (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))
                            (s (fn-rtc-with-uses (fn-rtc-remove-use (fn-rtc-key e) (fn-rtc-uses s)) s)))))))

; ---- keystones ----
(defthm fn-rtc-end-use-when-unmatched
  (implies (not (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))
           (equal (fn-rtc-end-use s e) s))
  :hints (("Goal" :in-theory (enable fn-rtc-end-use))))

(defthm fn-rtc-invp-admission
  (implies (fn-rtc-invp s)
           (iff (fn-rtc-free-slot 0 (fn-rtc-slots s))
                (fn-rtc-kind-out-p :accept 0 0 (fn-rtc-uses s))))
  :hints (("Goal" :in-theory (disable fn-rtc-uses-okp fn-rtc-slots-okp fn-rtc-pool-okp fn-rtc-draining-okp
                                      fn-rtc-free-slot fn-rtc-kind-out-p fn-rtc-mstates-okp)))
  :rule-classes nil)

(defthm fn-rtc-rearm-under-invp
  (implies (fn-rtc-invp s)
           (and (equal (mv-nth 0 (fn-rtc-rearm s)) s)
                (equal (mv-nth 1 (fn-rtc-rearm s)) nil)))
  :hints (("Goal" :use fn-rtc-invp-admission
                  :in-theory (e/d (fn-rtc-rearm) (fn-rtc-invp fn-rtc-free-slot fn-rtc-kind-out-p)))))

; T6
(defthm fn-rtc-unmatched-completion-is-discarded
  (implies (and (fn-rtc-invp s)
                (not (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s))))
           (and (equal (mv-nth 0 (fn-rtc-step s e q)) s)
                (equal (mv-nth 1 (fn-rtc-step s e q)) nil)))
  :hints (("Goal" :in-theory (e/d (fn-rtc-step fn-rtc-step* fn-rtc-acts-on-p)
                                  (fn-rtc-invp fn-rtc-find-use fn-rtc-key)))))

; T3
(defthm fn-rtc-outstanding-use-is-leased
  (implies (and (fn-rtc-invp s)
                (member-equal u (fn-rtc-uses s))
                (fn-rtc-handlep (fn-rtc-u-hd u)))
           (let ((h (fn-rtc-h-buf (fn-rtc-u-hd u))))
             (and (not (fn-rtc-recyclablep h s))
                  (equal (fn-rtc-gen h s) (fn-rtc-h-gen (fn-rtc-u-hd u))))))
  :hints (("Goal" :use ((:instance fn-rtc-uses-okp-member (uses (fn-rtc-uses s))))
                  :in-theory (e/d (fn-rtc-use-okp fn-rtc-recyclablep fn-rtc-gen)
                                  (fn-rtc-uses-okp-member fn-rtc-uses-okp fn-rtc-invp
                                   fn-rtc-holders fn-rtc-usep fn-rtc-current-p)))))

; T5
(defthm fn-rtc-completion-ends-its-use
  (implies (and (fn-rtc-invp s)
                (member-equal u (fn-rtc-uses s))
                (fn-rtc-ends-use-p e u))
           (not (fn-rtc-find-use (fn-rtc-key u)
                                 (fn-rtc-uses (fn-rtc-end-use s e)))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-ends-use-p)
                                  (fn-rtc-invp fn-rtc-completionp fn-rtc-find-use fn-rtc-remove-use fn-rtc-key))
           :do-not-induct t
           :use ((:instance fn-rtc-remove-use-removes-distinct-key (key (fn-rtc-key u)) (uses (fn-rtc-uses s)))
                 (:instance fn-rtc-find-use-key-of-member (uses (fn-rtc-uses s)))
                 (:instance fn-rtc-invp-uses-okp)))))


(defthm fn-rtc-request-keeps-uses
  (implies (member-equal u (fn-rtc-uses s))
           (member-equal u (fn-rtc-uses (mv-nth 0 (fn-rtc-request r id inc s)))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-request fn-rtc-req-acquire fn-rtc-req-write fn-rtc-req-release
                                   fn-rtc-req-close fn-rtc-req-cancel fn-rtc-req-submit)
                                  (fn-rtc-submit-okp fn-rtc-find-use fn-rtc-live-p fn-rtc-current-p)))))

(defthm fn-rtc-requests-keeps-uses
  (implies (member-equal u (fn-rtc-uses s))
           (member-equal u (fn-rtc-uses (mv-nth 0 (fn-rtc-requests reqs id inc s)))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-requests) (mv-nth fn-rtc-request))
           :induct (fn-rtc-requests reqs id inc s))))

(defthm fn-rtc-deliver-frame
  (and (implies (fn-rtc-leasedp h s)
                (equal (fn-rtc-buffer h (mv-nth 0 (fn-rtc-deliver s id inc ev q))) (fn-rtc-buffer h s)))
       (implies (member-equal u (fn-rtc-uses s))
                (member-equal u (fn-rtc-uses (mv-nth 0 (fn-rtc-deliver s id inc ev q))))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-deliver fn-rtc-leasedp) (fn-rtc-requests mv-nth)))))

(defthm fn-rtc-rearm-frame
  (and (equal (fn-rtc-buffer h (mv-nth 0 (fn-rtc-rearm s))) (fn-rtc-buffer h s))
       (equal (fn-rtc-mstate j (mv-nth 0 (fn-rtc-rearm s))) (fn-rtc-mstate j s))
       (equal (fn-rtc-slots (mv-nth 0 (fn-rtc-rearm s))) (fn-rtc-slots s))
       (equal (fn-rtc-config (mv-nth 0 (fn-rtc-rearm s))) (fn-rtc-config s))
       (implies (member-equal u (fn-rtc-uses s))
                (member-equal u (fn-rtc-uses (mv-nth 0 (fn-rtc-rearm s))))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-rearm) (fn-rtc-free-slot fn-rtc-find-use)))))


(defthm fn-rtc-get-of-release-all
  (equal (fn-rtc-get k (fn-rtc-release-all pool id inc))
         (if (< (nfix k) (len pool))
             (if (equal (fn-rtc-b-owner (fn-rtc-get k pool)) (list :workspace id inc))
                 (list (fn-rtc-b-gen (fn-rtc-get k pool)) '(:free) (fn-rtc-b-bytes (fn-rtc-get k pool)))
               (fn-rtc-get k pool))
           nil))
  :hints (("Goal" :induct (fn-rtc-get k pool)
                  :in-theory (disable fn-rtc-b-owner fn-rtc-b-gen fn-rtc-b-bytes))))
(defthm fn-rtc-len-of-release-all
  (equal (len (fn-rtc-release-all pool id inc)) (len pool)))
(defthm fn-rtc-buffer-of-make
  (and (equal (fn-rtc-buffer h (fn-rtc-make c sl p u m n)) (fn-rtc-get h p))
       (equal (fn-rtc-slot h (fn-rtc-make c sl p u m n)) (fn-rtc-get h sl))
       (equal (fn-rtc-mstate h (fn-rtc-make c sl p u m n)) (fn-rtc-get h m)))
  :hints (("Goal" :in-theory (enable fn-rtc-buffer fn-rtc-slot fn-rtc-mstate))))

(defthm fn-rtc-pool-is-buffers
  (equal (fn-rtc-get h (fn-rtc-pool s)) (fn-rtc-buffer h s))
  :hints (("Goal" :in-theory (enable fn-rtc-buffer))))

(defthm fn-rtc-member-uses-of-end-use
  (implies (and (member-equal u (fn-rtc-uses s)) (not (fn-rtc-ends-use-p e u)))
           (member-equal u (fn-rtc-uses (fn-rtc-end-use s e))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-ends-use-p) (fn-rtc-key fn-rtc-completionp fn-rtc-find-use fn-rtc-remove-use)))))

(defthm fn-rtc-leasedp-of-use
  (implies (and (fn-rtc-invp s) (member-equal u (fn-rtc-uses s)) (fn-rtc-handlep (fn-rtc-u-hd u)))
           (fn-rtc-leasedp (fn-rtc-h-buf (fn-rtc-u-hd u)) s))
  :hints (("Goal" :in-theory (disable fn-rtc-invp fn-rtc-use-okp fn-rtc-leasedp fn-rtc-handlep fn-rtc-h-buf)
                  :use (fn-rtc-invp-uses-okp
                        (:instance fn-rtc-uses-okp-member (uses (fn-rtc-uses s)))
                        fn-rtc-use-okp-lease))))


(defthm fn-rtc-get-out-of-range
  (implies (<= (len l) (nfix i)) (equal (fn-rtc-get i l) nil)))
(defthm fn-rtc-buffer-out-of-range
  (implies (<= (len (fn-rtc-pool s)) (nfix h)) (equal (fn-rtc-buffer h s) nil))
  :hints (("Goal" :in-theory (e/d (fn-rtc-buffer) (fn-rtc-pool-is-buffers)))))
(defthm fn-rtc-accept-branch-frame
  (and (implies (fn-rtc-leasedp h s1)
                (equal (fn-rtc-buffer h (mv-nth 0 (fn-rtc-accept-branch s1 out q))) (fn-rtc-buffer h s1)))
       (implies (member-equal u (fn-rtc-uses s1))
                (member-equal u (fn-rtc-uses (mv-nth 0 (fn-rtc-accept-branch s1 out q))))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-accept-branch fn-rtc-leasedp)
                                  (mv-nth fn-rtc-free-slot fn-rtc-s-inc)))))

(defthm fn-rtc-close-branch-frame
  (and (implies (fn-rtc-leasedp h s1)
                (equal (fn-rtc-buffer h (mv-nth 0 (fn-rtc-close-branch s1 id inc))) (fn-rtc-buffer h s1)))
       (implies (member-equal u (fn-rtc-uses s1))
                (member-equal u (fn-rtc-uses (mv-nth 0 (fn-rtc-close-branch s1 id inc))))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-close-branch fn-rtc-leasedp)
                                  (mv-nth fn-rtc-uses-of-slot-p fn-rtc-s-res)))))

(in-theory (disable fn-rtc-accept-branch fn-rtc-close-branch))

; T4
(defthm fn-rtc-outstanding-use-is-stable
  (implies (and (fn-rtc-invp s)
                (member-equal u (fn-rtc-uses s))
                (not (fn-rtc-ends-use-p e u)))
           (let ((s2 (mv-nth 0 (fn-rtc-step s e q))))
             (and (member-equal u (fn-rtc-uses s2))
                  (implies (fn-rtc-handlep (fn-rtc-u-hd u))
                           (let ((h (fn-rtc-h-buf (fn-rtc-u-hd u))))
                             (equal (fn-rtc-buffer h s2) (fn-rtc-buffer h s)))))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-step fn-rtc-step* fn-rtc-leasedp)
                                  (fn-rtc-invp fn-rtc-ends-use-p fn-rtc-acts-on-p fn-rtc-handlep fn-rtc-h-buf
                                   fn-rtc-leasedp-of-use fn-rtc-end-use-keeps-other-leases mv-nth
                                   fn-rtc-uses-of-end-use fn-rtc-delivered-outcome fn-rtc-e-id fn-rtc-e-inc
                                   fn-rtc-e-kind fn-rtc-find-use fn-rtc-key))
           :do-not-induct t
           :use (fn-rtc-leasedp-of-use fn-rtc-end-use-keeps-other-leases))))


; Generations never decrease.
; Generations: every operation leaves each buffer's generation equal or larger.
(defun fn-rtc-gen-le (h s1 s2)
  (declare (xargs :guard t))
  (<= (fn-rtc-gen h s1) (fn-rtc-gen h s2)))

(defthm fn-rtc-gen-le-trans
  (implies (and (fn-rtc-gen-le h s1 s2) (fn-rtc-gen-le h s2 s3))
           (fn-rtc-gen-le h s1 s3)))

(defthm fn-rtc-gen-le-refl (fn-rtc-gen-le h s s))

(defthm fn-rtc-gen-le-of-req-acquire (fn-rtc-gen-le h s (mv-nth 0 (fn-rtc-req-acquire r id inc s)))
  :hints (("Goal" :in-theory (enable fn-rtc-gen))))
(defthm fn-rtc-gen-le-of-req-write (fn-rtc-gen-le h s (mv-nth 0 (fn-rtc-req-write r id inc s)))
  :hints (("Goal" :in-theory (e/d (fn-rtc-gen) (fn-rtc-splice)))))
(defthm fn-rtc-gen-le-of-req-release (fn-rtc-gen-le h s (mv-nth 0 (fn-rtc-req-release r id inc s)))
  :hints (("Goal" :in-theory (enable fn-rtc-gen))))
(defthm fn-rtc-gen-le-of-req-close (fn-rtc-gen-le h s (mv-nth 0 (fn-rtc-req-close r id inc s)))
  :hints (("Goal" :in-theory (enable fn-rtc-gen))))
(defthm fn-rtc-gen-le-of-req-submit (fn-rtc-gen-le h s (mv-nth 0 (fn-rtc-req-submit r id inc s)))
  :hints (("Goal" :in-theory (e/d (fn-rtc-gen) (fn-rtc-submit-okp fn-rtc-kind-out-p fn-rtc-live-p fn-rtc-extrap)))))
(defthm fn-rtc-gen-le-of-request (fn-rtc-gen-le h s (mv-nth 0 (fn-rtc-request r id inc s)))
  :hints (("Goal" :in-theory (e/d (fn-rtc-request)
                                  (fn-rtc-gen-le fn-rtc-req-acquire fn-rtc-req-write fn-rtc-req-release
                                   fn-rtc-req-close fn-rtc-req-cancel fn-rtc-req-submit mv-nth)))))
(defthm fn-rtc-gen-le-of-requests
  (fn-rtc-gen-le h s (mv-nth 0 (fn-rtc-requests reqs id inc s)))
  :hints (("Goal" :in-theory (e/d (fn-rtc-requests) (fn-rtc-gen-le fn-rtc-request mv-nth))
           :induct (fn-rtc-requests reqs id inc s))
          ("Subgoal *1/1'" :use ((:instance fn-rtc-gen-le-trans
                                 (s1 s) (s2 (mv-nth 0 (fn-rtc-request (car reqs) id inc s)))
                                 (s3 (mv-nth 0 (fn-rtc-requests (cdr reqs) id inc
                                                                (mv-nth 0 (fn-rtc-request (car reqs) id inc s))))))))))
(defthm fn-rtc-gen-le-of-deliver
  (fn-rtc-gen-le h s (mv-nth 0 (fn-rtc-deliver s id inc ev q)))
  :hints (("Goal" :in-theory (e/d (fn-rtc-deliver) (fn-rtc-gen-le-of-requests fn-rtc-requests mv-nth))
           :use ((:instance fn-rtc-gen-le-of-requests
                  (reqs (mv-nth 1 (fn-rtc-m-step (fn-rtc-mstate id s) ev (fn-rtc-borrow (fn-rtc-pool s)) (nfix q))))
                  (s (fn-rtc-with-mstate id (mv-nth 0 (fn-rtc-m-step (fn-rtc-mstate id s) ev
                                                                      (fn-rtc-borrow (fn-rtc-pool s)) (nfix q)))
                                         s)))))))
(defthm fn-rtc-gen-le-of-rearm
  (fn-rtc-gen-le h s (mv-nth 0 (fn-rtc-rearm s)))
  :hints (("Goal" :in-theory (enable fn-rtc-gen))))
(defthm fn-rtc-lease-return-gen
  (equal (fn-rtc-b-gen (fn-rtc-lease-return u e b s)) (+ 1 (fn-rtc-b-gen b)))
  :hints (("Goal" :in-theory (e/d (fn-rtc-lease-return) (fn-rtc-delivered-outcome fn-rtc-splice fn-rtc-current-p)))))
(defthm fn-rtc-gen-le-of-end-lease
  (fn-rtc-gen-le h s (fn-rtc-end-lease u e s))
  :hints (("Goal" :in-theory (e/d (fn-rtc-end-lease fn-rtc-gen) (fn-rtc-holds-p fn-rtc-handlep fn-rtc-b-gen fn-rtc-u-hd fn-rtc-h-buf fn-rtc-h-gen)))))
(defthm fn-rtc-gen-frames
  (and (equal (fn-rtc-gen h (fn-rtc-with-uses u s)) (fn-rtc-gen h s))
       (equal (fn-rtc-gen h (fn-rtc-with-slot k x s)) (fn-rtc-gen h s))
       (equal (fn-rtc-gen h (fn-rtc-with-mstate k m s)) (fn-rtc-gen h s))
       (equal (fn-rtc-gen h (fn-rtc-retire-drained id s)) (fn-rtc-gen h s))
       (equal (fn-rtc-gen h (fn-rtc-issue x s)) (fn-rtc-gen h s)))
  :hints (("Goal" :in-theory (enable fn-rtc-gen))))
(defthm fn-rtc-gen-le-of-end-use
  (fn-rtc-gen-le h s (fn-rtc-end-use s e))
  :hints (("Goal" :in-theory (e/d (fn-rtc-end-use) (fn-rtc-gen fn-rtc-gen-le-of-end-lease))
           :use ((:instance fn-rtc-gen-le-of-end-lease
                  (u (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))
                  (s (fn-rtc-with-uses (fn-rtc-remove-use (fn-rtc-key e) (fn-rtc-uses s)) s)))))))
(defthm fn-rtc-gen-le-of-accept-branch
  (fn-rtc-gen-le h s1 (mv-nth 0 (fn-rtc-accept-branch s1 out q)))
  :hints (("Goal" :in-theory (e/d (fn-rtc-accept-branch)
                                  (fn-rtc-gen mv-nth fn-rtc-free-slot fn-rtc-gen-le-of-deliver fn-rtc-gen-le-of-rearm
                                   fn-rtc-deliver fn-rtc-rearm))
           :use ((:instance fn-rtc-gen-le-of-rearm (s s1))
                 (:instance fn-rtc-gen-le-of-deliver
                            (s (fn-rtc-with-mstate (fn-rtc-free-slot 0 (fn-rtc-slots s1)) (fn-rtc-m-init)
                                 (fn-rtc-with-slot (fn-rtc-free-slot 0 (fn-rtc-slots s1))
                                                   (list (+ 1 (fn-rtc-s-inc (fn-rtc-slot (fn-rtc-free-slot 0 (fn-rtc-slots s1)) s1)))
                                                         :live (fn-rtc-get 1 out))
                                                   s1)))
                            (id (fn-rtc-free-slot 0 (fn-rtc-slots s1)))
                            (inc (+ 1 (fn-rtc-s-inc (fn-rtc-slot (fn-rtc-free-slot 0 (fn-rtc-slots s1)) s1))))
                            (ev (list :accept out)))
                 (:instance fn-rtc-gen-le-of-rearm
                            (s (mv-nth 0 (fn-rtc-deliver
                                          (fn-rtc-with-mstate (fn-rtc-free-slot 0 (fn-rtc-slots s1)) (fn-rtc-m-init)
                                            (fn-rtc-with-slot (fn-rtc-free-slot 0 (fn-rtc-slots s1))
                                                              (list (+ 1 (fn-rtc-s-inc (fn-rtc-slot (fn-rtc-free-slot 0 (fn-rtc-slots s1)) s1)))
                                                                    :live (fn-rtc-get 1 out))
                                                              s1))
                                          (fn-rtc-free-slot 0 (fn-rtc-slots s1))
                                          (+ 1 (fn-rtc-s-inc (fn-rtc-slot (fn-rtc-free-slot 0 (fn-rtc-slots s1)) s1)))
                                          (list :accept out) q))))))))
(defthm fn-rtc-gen-le-of-close-branch
  (fn-rtc-gen-le h s1 (mv-nth 0 (fn-rtc-close-branch s1 id inc)))
  :hints (("Goal" :in-theory (e/d (fn-rtc-close-branch fn-rtc-gen)
                                  (mv-nth fn-rtc-uses-of-slot-p fn-rtc-rearm fn-rtc-gen-le-of-rearm))
           :use ((:instance fn-rtc-gen-le-of-rearm
                  (s (let* ((s2 (fn-rtc-make (fn-rtc-config s1) (fn-rtc-slots s1)
                                             (fn-rtc-release-all (fn-rtc-pool s1) id inc)
                                             (fn-rtc-uses s1) (fn-rtc-mstates s1) (fn-rtc-next-op s1)))
                            (status (if (fn-rtc-uses-of-slot-p id inc (fn-rtc-uses s2)) :draining :free)))
                       (fn-rtc-with-mstate
                        id (fn-rtc-m-init)
                        (fn-rtc-with-slot id (list inc status (if (eq status :free) nil
                                                                (fn-rtc-s-res (fn-rtc-slot id s2))))
                                          s2)))))))))

(in-theory (disable fn-rtc-gen-le))

(defthm fn-rtc-gen-le-chain-end-use
  (implies (fn-rtc-gen-le h s0 s) (fn-rtc-gen-le h s0 (fn-rtc-end-use s e)))
  :hints (("Goal" :in-theory (disable fn-rtc-gen-le-of-end-use)
           :use ((:instance fn-rtc-gen-le-of-end-use) (:instance fn-rtc-gen-le-trans (s1 s0) (s2 s) (s3 (fn-rtc-end-use s e)))))))
(defthm fn-rtc-gen-le-chain-rearm
  (implies (fn-rtc-gen-le h s0 s) (fn-rtc-gen-le h s0 (mv-nth 0 (fn-rtc-rearm s))))
  :hints (("Goal" :in-theory (disable fn-rtc-gen-le-of-rearm)
           :use ((:instance fn-rtc-gen-le-of-rearm) (:instance fn-rtc-gen-le-trans (s1 s0) (s2 s) (s3 (mv-nth 0 (fn-rtc-rearm s))))))))
(defthm fn-rtc-gen-le-chain-deliver
  (implies (fn-rtc-gen-le h s0 s) (fn-rtc-gen-le h s0 (mv-nth 0 (fn-rtc-deliver s id inc ev q))))
  :hints (("Goal" :in-theory (disable fn-rtc-gen-le-of-deliver)
           :use ((:instance fn-rtc-gen-le-of-deliver) (:instance fn-rtc-gen-le-trans (s1 s0) (s2 s) (s3 (mv-nth 0 (fn-rtc-deliver s id inc ev q))))))))
(defthm fn-rtc-gen-le-chain-accept-branch
  (implies (fn-rtc-gen-le h s0 s) (fn-rtc-gen-le h s0 (mv-nth 0 (fn-rtc-accept-branch s out q))))
  :hints (("Goal" :in-theory (disable fn-rtc-gen-le-of-accept-branch)
           :use ((:instance fn-rtc-gen-le-of-accept-branch (s1 s)) (:instance fn-rtc-gen-le-trans (s1 s0) (s2 s) (s3 (mv-nth 0 (fn-rtc-accept-branch s out q))))))))
(defthm fn-rtc-gen-le-chain-close-branch
  (implies (fn-rtc-gen-le h s0 s) (fn-rtc-gen-le h s0 (mv-nth 0 (fn-rtc-close-branch s id inc))))
  :hints (("Goal" :in-theory (disable fn-rtc-gen-le-of-close-branch)
           :use ((:instance fn-rtc-gen-le-of-close-branch (s1 s)) (:instance fn-rtc-gen-le-trans (s1 s0) (s2 s) (s3 (mv-nth 0 (fn-rtc-close-branch s id inc))))))))


; The state half of a step, one function of its four branches.
(defun fn-rtc-step-state (s e q)
  (declare (xargs :guard t))
  (if (not (fn-rtc-acts-on-p s e))
      (mv-let (s2 a) (fn-rtc-rearm (fn-rtc-end-use s e)) (declare (ignore a)) s2)
    (let ((s1 (fn-rtc-end-use s e))
          (kind (fn-rtc-e-kind e))
          (out (fn-rtc-delivered-outcome (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)) e)))
      (cond ((eq kind :accept)
             (mv-let (s2 a r c) (fn-rtc-accept-branch s1 out q) (declare (ignore a r c)) s2))
            ((eq kind :close)
             (mv-let (s2 a) (fn-rtc-close-branch s1 (fn-rtc-e-id e) (fn-rtc-e-inc e)) (declare (ignore a)) s2))
            (t (mv-let (s2 a r c) (fn-rtc-deliver s1 (fn-rtc-e-id e) (fn-rtc-e-inc e) (list kind out) q)
                 (declare (ignore a r c)) s2))))))

(defthm fn-rtc-step-is-step-state
  (equal (mv-nth 0 (fn-rtc-step s e q)) (fn-rtc-step-state s e q))
  :hints (("Goal" :in-theory (e/d (fn-rtc-step fn-rtc-step*)
                                  (fn-rtc-acts-on-p fn-rtc-e-kind fn-rtc-e-id fn-rtc-e-inc
                                   fn-rtc-delivered-outcome fn-rtc-find-use fn-rtc-key fn-rtc-end-use
                                   fn-rtc-rearm fn-rtc-deliver fn-rtc-accept-branch fn-rtc-close-branch
                                   fn-rtc-use-bound fn-rtc-nslots fn-rtc-nbufs fn-rtc-h-len fn-rtc-u-hd)))))
(defthm fn-rtc-gen-le-of-step-state
  (fn-rtc-gen-le h s (fn-rtc-step-state s e q))
  :hints (("Goal" :in-theory (e/d (fn-rtc-step-state)
                                  (mv-nth fn-rtc-acts-on-p fn-rtc-e-kind fn-rtc-e-id fn-rtc-e-inc
                                   fn-rtc-delivered-outcome fn-rtc-find-use fn-rtc-key fn-rtc-end-use
                                   fn-rtc-rearm fn-rtc-deliver fn-rtc-accept-branch fn-rtc-close-branch)))))

(in-theory (disable fn-rtc-step-state fn-rtc-step fn-rtc-step*))

; T9
(defthm fn-rtc-generation-is-monotone
  (implies (fn-rtc-invp s)
           (<= (fn-rtc-gen h s) (fn-rtc-gen h (mv-nth 0 (fn-rtc-step s e q)))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-gen-le) (fn-rtc-invp fn-rtc-gen-le-of-step-state fn-rtc-gen))
           :use fn-rtc-gen-le-of-step-state)))

; T14
(defthm fn-rtc-borrow-hides-in-leased-bytes
  (implies (fn-rtc-pools-agree-off-in-leases-p p1 p2)
           (equal (fn-rtc-borrow p1) (fn-rtc-borrow p2)))
  :hints (("Goal" :induct (fn-rtc-pools-agree-off-in-leases-p p1 p2))))

(defthm fn-rtc-mstates-okp-get
  (implies (and (fn-rtc-mstates-okp ms) (< (nfix j) (len ms)))
           (<= (fn-rtc-size (fn-rtc-get j ms)) (fn-rtc-m-max-state))))

(defthm fn-rtc-m-max-state-positive
  (<= 1 (fn-rtc-m-max-state))
  :rule-classes :linear
  :hints (("Goal" :use fn-rtc-m-init-is-bounded :in-theory (disable fn-rtc-m-init-is-bounded))))

; T15
(defthm fn-rtc-machine-states-are-bounded
  (implies (and (fn-rtc-invp s) (natp j))
           (<= (fn-rtc-size (fn-rtc-mstate j s)) (fn-rtc-m-max-state)))
  :hints (("Goal" :in-theory (e/d (fn-rtc-mstate) (fn-rtc-mstates-okp-get))
           :cases ((< j (len (fn-rtc-mstates s))))
           :use ((:instance fn-rtc-mstates-okp-get (ms (fn-rtc-mstates s)))))))


; Machine states, operation by operation.
(defthm fn-rtc-request-keeps-mstates
  (equal (fn-rtc-mstate j (mv-nth 0 (fn-rtc-request r id inc s))) (fn-rtc-mstate j s))
  :hints (("Goal" :in-theory (e/d (fn-rtc-request fn-rtc-req-acquire fn-rtc-req-write fn-rtc-req-release
                                   fn-rtc-req-close fn-rtc-req-cancel fn-rtc-req-submit)
                                  (fn-rtc-submit-okp fn-rtc-kind-out-p fn-rtc-live-p fn-rtc-current-p
                                   fn-rtc-extrap fn-rtc-kind-op fn-rtc-splice)))))
(defthm fn-rtc-requests-keeps-mstates
  (equal (fn-rtc-mstate j (mv-nth 0 (fn-rtc-requests reqs id inc s))) (fn-rtc-mstate j s))
  :hints (("Goal" :in-theory (e/d (fn-rtc-requests) (mv-nth fn-rtc-request))
           :induct (fn-rtc-requests reqs id inc s))))
(defthm fn-rtc-mstate-of-deliver
  (equal (fn-rtc-mstate j (mv-nth 0 (fn-rtc-deliver s id inc ev q)))
         (if (and (equal (nfix j) (nfix id)) (< (nfix id) (len (fn-rtc-mstates s))))
             (mv-nth 0 (fn-rtc-m-step (fn-rtc-mstate id s) ev (fn-rtc-borrow (fn-rtc-pool s)) (nfix q)))
           (fn-rtc-mstate j s)))
  :hints (("Goal" :in-theory (e/d (fn-rtc-deliver) (fn-rtc-requests mv-nth)))))
(defthm fn-rtc-mstate-of-end-use
  (equal (fn-rtc-mstate j (fn-rtc-end-use s e)) (fn-rtc-mstate j s))
  :hints (("Goal" :in-theory (enable fn-rtc-end-use))))
(defthm fn-rtc-mstate-of-accept-branch
  (implies (not (equal (nfix j) (nfix (fn-rtc-free-slot 0 (fn-rtc-slots s1)))))
           (equal (fn-rtc-mstate j (mv-nth 0 (fn-rtc-accept-branch s1 out q))) (fn-rtc-mstate j s1)))
  :hints (("Goal" :in-theory (e/d (fn-rtc-accept-branch) (mv-nth fn-rtc-free-slot fn-rtc-deliver fn-rtc-rearm)))))
(defthm fn-rtc-mstates-is-mstate
  (equal (fn-rtc-get j (fn-rtc-mstates s)) (fn-rtc-mstate j s))
  :hints (("Goal" :in-theory (enable fn-rtc-mstate))))
(defthm fn-rtc-slots-is-slot
  (equal (fn-rtc-get j (fn-rtc-slots s)) (fn-rtc-slot j s))
  :hints (("Goal" :in-theory (enable fn-rtc-slot))))
(defthm fn-rtc-mstate-of-close-branch
  (implies (not (equal (nfix j) (nfix id)))
           (equal (fn-rtc-mstate j (mv-nth 0 (fn-rtc-close-branch s1 id inc))) (fn-rtc-mstate j s1)))
  :hints (("Goal" :in-theory (e/d (fn-rtc-close-branch) (mv-nth fn-rtc-uses-of-slot-p fn-rtc-rearm)))))
(defthm fn-rtc-mstate-of-accept-branch-not-done
  (implies (not (eq (fn-rtc-get 0 out) :done))
           (equal (fn-rtc-mstate j (mv-nth 0 (fn-rtc-accept-branch s1 out q))) (fn-rtc-mstate j s1)))
  :hints (("Goal" :in-theory (e/d (fn-rtc-accept-branch) (mv-nth fn-rtc-free-slot fn-rtc-deliver fn-rtc-rearm)))))

(defthm fn-rtc-invp-listener
  (implies (fn-rtc-invp s) (equal (fn-rtc-slot 0 s) '(0 :live nil)))
  :hints (("Goal" :in-theory (e/d (fn-rtc-slot) (fn-rtc-uses-okp fn-rtc-pool-okp fn-rtc-draining-okp fn-rtc-free-slot
                                                fn-rtc-kind-out-p fn-rtc-mstates-okp fn-rtc-slots-is-slot))
                  :expand ((fn-rtc-slots-okp 0 (fn-rtc-slots s))))))

(defthm fn-rtc-slots-of-end-lease
  (equal (fn-rtc-slots (fn-rtc-end-lease u e s)) (fn-rtc-slots s))
  :hints (("Goal" :in-theory (e/d (fn-rtc-end-lease) (fn-rtc-lease-return fn-rtc-holds-p fn-rtc-handlep)))))

(defthm fn-rtc-slots-of-end-use-at-live-slot
  (implies (not (eq (fn-rtc-s-status (fn-rtc-slot (fn-rtc-e-id e) s)) :draining))
           (equal (fn-rtc-slots (fn-rtc-end-use s e)) (fn-rtc-slots s)))
  :hints (("Goal" :in-theory (enable fn-rtc-end-use fn-rtc-retire-drained))))

(defthm fn-rtc-delivered-outcome-done
  (implies (eq (fn-rtc-get 0 (fn-rtc-delivered-outcome u e)) :done)
           (eq (fn-rtc-get 0 (fn-rtc-e-outcome e)) :done))
  :hints (("Goal" :in-theory (enable fn-rtc-delivered-outcome))))

(defthm fn-rtc-use-okp-accept-is-listener
  (implies (and (fn-rtc-use-okp u s) (equal (fn-rtc-get 0 u) :accept))
           (equal (fn-rtc-get 1 u) 0))
  :hints (("Goal" :in-theory (e/d (fn-rtc-use-okp) (fn-rtc-usep fn-rtc-current-p fn-rtc-holders fn-rtc-handlep
                                                   fn-rtc-buffer fn-rtc-slot fn-rtc-u-hd))
                  :expand ((fn-rtc-usep u)))))

(defthm fn-rtc-acts-on-accept-id
  (implies (and (fn-rtc-invp s) (fn-rtc-acts-on-p s e) (eq (fn-rtc-e-kind e) :accept))
           (equal (fn-rtc-e-id e) 0))
  :hints (("Goal" :in-theory (e/d (fn-rtc-acts-on-p fn-rtc-e-kind fn-rtc-e-id)
                                  (fn-rtc-invp fn-rtc-uses-okp-member fn-rtc-find-use fn-rtc-use-okp
                                   fn-rtc-use-okp-accept-is-listener fn-rtc-completionp fn-rtc-slot))
           :use (fn-rtc-invp-uses-okp
                 (:instance fn-rtc-uses-okp-member (uses (fn-rtc-uses s))
                            (u (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s))))
                 (:instance fn-rtc-use-okp-accept-is-listener (u (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s))))
                 (:instance fn-rtc-find-use-is-member (k (fn-rtc-key e)) (uses (fn-rtc-uses s)))
                 (:instance fn-rtc-key-of-find-use (k (fn-rtc-key e)) (uses (fn-rtc-uses s)))))))
; T7
(defthm fn-rtc-machine-changes-only-on-its-own-completion
  (implies (and (fn-rtc-invp s)
                (not (equal (fn-rtc-mstate j (mv-nth 0 (fn-rtc-step s e q)))
                            (fn-rtc-mstate j s))))
           (and (fn-rtc-acts-on-p s e)
                (equal (nfix j) (fn-rtc-target s e))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-step-state fn-rtc-target)
                                  (fn-rtc-invp mv-nth fn-rtc-acts-on-p fn-rtc-e-id fn-rtc-e-inc
                                   fn-rtc-delivered-outcome fn-rtc-find-use fn-rtc-key fn-rtc-end-use
                                   fn-rtc-rearm fn-rtc-deliver fn-rtc-accept-branch fn-rtc-close-branch
                                   fn-rtc-free-slot fn-rtc-e-outcome fn-rtc-delivered-outcome-done
                                   fn-rtc-mstate-of-accept-branch-not-done))
           :use (fn-rtc-invp-listener fn-rtc-acts-on-accept-id
                 (:instance fn-rtc-delivered-outcome-done (u (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s))))
                 (:instance fn-rtc-mstate-of-accept-branch-not-done
                            (s1 (fn-rtc-end-use s e))
                            (out (fn-rtc-delivered-outcome (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)) e)))))))

(defthm fn-rtc-accept-branch-commits-nothing
  (implies (not (fn-rtc-m-committedp (fn-rtc-mstate j s1)))
           (not (fn-rtc-m-committedp (fn-rtc-mstate j (mv-nth 0 (fn-rtc-accept-branch s1 out q))))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-accept-branch fn-rtc-fsync-done-p)
                                  (mv-nth fn-rtc-free-slot fn-rtc-deliver fn-rtc-rearm fn-rtc-m-commits-only-on-fsync-done))
           :use ((:instance fn-rtc-m-commits-only-on-fsync-done
                  (m (fn-rtc-m-init)) (ev (list :accept out))
                  (pool (fn-rtc-borrow (fn-rtc-pool s1))) (q (nfix q)))))))

(defthm fn-rtc-close-branch-commits-nothing
  (implies (not (fn-rtc-m-committedp (fn-rtc-mstate j s1)))
           (not (fn-rtc-m-committedp (fn-rtc-mstate j (mv-nth 0 (fn-rtc-close-branch s1 id inc))))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-close-branch) (mv-nth fn-rtc-uses-of-slot-p fn-rtc-rearm)))))

(defthm fn-rtc-deliver-commits-only-on-fsync-done
  (implies (and (not (fn-rtc-m-committedp (fn-rtc-mstate j s)))
                (fn-rtc-m-committedp (fn-rtc-mstate j (mv-nth 0 (fn-rtc-deliver s id inc ev q)))))
           (fn-rtc-fsync-done-p ev))
  :hints (("Goal" :in-theory (disable fn-rtc-m-commits-only-on-fsync-done fn-rtc-fsync-done-p mv-nth)
           :use ((:instance fn-rtc-m-commits-only-on-fsync-done
                  (m (fn-rtc-mstate id s)) (pool (fn-rtc-borrow (fn-rtc-pool s))) (q (nfix q)))))))

; T11
(defthm fn-rtc-commit-only-on-own-barrier-completion
  (implies (and (fn-rtc-invp s)
                (not (fn-rtc-m-committedp (fn-rtc-mstate j s)))
                (fn-rtc-m-committedp (fn-rtc-mstate j (mv-nth 0 (fn-rtc-step s e q)))))
           (and (fn-rtc-acts-on-p s e)
                (equal (fn-rtc-e-kind e) :fsync)
                (equal (nfix j) (fn-rtc-e-id e))
                (equal (fn-rtc-get 0 (fn-rtc-e-outcome e)) :done)))
  :hints (("Goal" :in-theory (e/d (fn-rtc-step-state fn-rtc-target fn-rtc-fsync-done-p)
                                  (fn-rtc-invp mv-nth fn-rtc-acts-on-p fn-rtc-e-id fn-rtc-e-inc fn-rtc-e-kind
                                   fn-rtc-delivered-outcome fn-rtc-find-use fn-rtc-key fn-rtc-end-use
                                   fn-rtc-rearm fn-rtc-deliver fn-rtc-accept-branch fn-rtc-close-branch
                                   fn-rtc-free-slot fn-rtc-e-outcome fn-rtc-delivered-outcome-done
                                   fn-rtc-machine-changes-only-on-its-own-completion
                                   fn-rtc-deliver-commits-only-on-fsync-done))
           :use (fn-rtc-machine-changes-only-on-its-own-completion
                 (:instance fn-rtc-delivered-outcome-done (u (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s))))
                 (:instance fn-rtc-deliver-commits-only-on-fsync-done
                            (s (fn-rtc-end-use s e)) (id (fn-rtc-e-id e)) (inc (fn-rtc-e-inc e))
                            (ev (list (fn-rtc-e-kind e)
                                      (fn-rtc-delivered-outcome (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)) e))))))))

; =============================================================================
; STATEMENTS NOT YET PROVED (each moves above, unchanged, when proved)
;
;; ; =============================================================================
;; ; STATEMENTS (for review; no proof attempted yet)
;;
;; ; T1. The initial state satisfies the invariant.
;; (defthm fn-rtc-init-establishes-invp
;;   (implies (fn-rtc-configp cfg)
;;            (fn-rtc-invp (mv-nth 0 (fn-rtc-init cfg)))))
;;
;; ; T2. Every step preserves it, for every event and every quantum.
;; (defthm fn-rtc-step-preserves-invp
;;   (implies (fn-rtc-invp s)
;;            (fn-rtc-invp (mv-nth 0 (fn-rtc-step s e q)))))
;;
;; ; T8. Workspace isolation: a step leaves every workspace of an instance
;; ; other than the one the event is for exactly as it was (owner and bytes).
;; (defthm fn-rtc-other-workspaces-are-untouched
;;   (implies (and (fn-rtc-invp s)
;;                 (equal (fn-rtc-get 0 (fn-rtc-b-owner (fn-rtc-buffer h s))) :workspace)
;;                 (not (equal (fn-rtc-get 1 (fn-rtc-b-owner (fn-rtc-buffer h s)))
;;                             (fn-rtc-target s e))))
;;            (equal (fn-rtc-buffer h (mv-nth 0 (fn-rtc-step s e q)))
;;                   (fn-rtc-buffer h s))))
;;
;; ; T10. Every emitted action is well formed; every action but :cancel is
;; ; recorded in the outstanding-use table of the resulting state under its key,
;; ; and a :cancel names a use that is still outstanding there (cancel does not
;; ; end a use).
;; (defthm fn-rtc-every-action-is-outstanding
;;   (implies (and (fn-rtc-invp s)
;;                 (member-equal a (mv-nth 1 (fn-rtc-step s e q))))
;;            (and (fn-rtc-actionp a)
;;                 (if (equal (fn-rtc-get 0 a) :cancel)
;;                     (fn-rtc-find-use (list (fn-rtc-get 0 (fn-rtc-get 4 a))
;;                                            (fn-rtc-get 1 a) (fn-rtc-get 2 a) (fn-rtc-get 3 a))
;;                                      (fn-rtc-uses (mv-nth 0 (fn-rtc-step s e q))))
;;                   (fn-rtc-find-use (fn-rtc-key a)
;;                                    (fn-rtc-uses (mv-nth 0 (fn-rtc-step s e q))))))))
;;
;; ; T12. The work budget: one step costs at most the quantum plus a term of the
;; ; configuration, emits a bounded number of actions, and the octets those
;; ; actions name (its retained output) are bounded by the configuration.
;; (defthm fn-rtc-step-is-charged
;;   (implies (and (fn-rtc-invp s) (natp q))
;;            (and (<= (fn-rtc-step-cost s e q)
;;                     (+ q (fn-rtc-step-c (fn-rtc-config s))))
;;                 (<= (len (mv-nth 1 (fn-rtc-step s e q)))
;;                     (+ 1 (fn-rtc-m-max-reqs)))
;;                 (<= (fn-rtc-actions-octets (mv-nth 1 (fn-rtc-step s e q)))
;;                     (* (fn-rtc-m-max-reqs) (fn-rtc-cap (fn-rtc-config s)))))))
;;
;; ; T13. Drain progresses: a :draining slot whose last outstanding use is ended
;; ; by this event is retired to :free, and the listener's :accept is armed.
;; (defthm fn-rtc-last-completion-retires-a-draining-slot
;;   (implies (and (fn-rtc-invp s)
;;                 (equal (fn-rtc-s-status (fn-rtc-slot j s)) :draining)
;;                 (member-equal u (fn-rtc-uses s))
;;                 (equal (fn-rtc-get 1 u) j)
;;                 (fn-rtc-ends-use-p e u)
;;                 (not (fn-rtc-uses-of-slot-p j (fn-rtc-s-inc (fn-rtc-slot j s))
;;                                             (fn-rtc-remove-use (fn-rtc-key u) (fn-rtc-uses s)))))
;;            (let ((s2 (mv-nth 0 (fn-rtc-step s e q))))
;;              (and (equal (fn-rtc-s-status (fn-rtc-slot j s2)) :free)
;;                   (fn-rtc-kind-out-p :accept 0 0 (fn-rtc-uses s2))))))
;;
;; ; A-HOST-COMPLETES, the named assumption (an encapsulate in
;; ; books/assumptions-runtime.lisp, statement here): the host delivers exactly
;; ; one completion for every submitted action.  Over a host trace -- the actions
;; ; the layer emitted and the events the host returned after them, in order --
;; ; every non-:cancel action's key is the key of exactly one later completion.
;; ;
;; ;   (encapsulate (((fn-assume-host-completions *) => *))
;; ;     (local (defun fn-assume-host-completions (actions)  ; witness: cancel all
;; ;              (fn-rtc-cancel-all actions)))
;; ;     (defthm fn-assume-host-completes-every-action
;; ;       (implies (and (member-equal a actions) (not (equal (fn-rtc-get 0 a) :cancel)))
;; ;                (equal (fn-rtc-count-key (fn-rtc-key a)
;; ;                                         (fn-assume-host-completions actions))
;; ;                       1)))
;; ;     (defthm fn-assume-host-completions-are-completions
;; ;       (fn-rtc-completion-listp (fn-assume-host-completions actions))))
;; ;
;; ; With T4 (only its own completion ends a use), T13 and A-HOST-COMPLETES, every
;; ; draining slot is eventually retired: the pin a stuck action holds is bounded by
;; ; the instance's deadline plus the host's completion of the cancel.
