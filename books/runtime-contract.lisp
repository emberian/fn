; fn: the runtime contract (RUNTIME-MODEL-DRAFT-20261009 section 1).
;
; One executor runs many machine instances.  Every effect an instance wants is
; an ACTION (kind id incarnation args) handed to an I/O worker; the worker's
; answer is a COMPLETION (kind id incarnation outcome), the only kind of event
; this layer consumes.  Outcomes are (:done n), (:short n), (:failed reason)
; and (:cancelled).  An instance learns that an effect happened only from its
; completion; submission establishes nothing.
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
;          action, and an :accept reuses it under incarnation + 1, so every
;          outstanding action belongs to its slot's current incarnation and a
;          completion naming any other incarnation is discarded whole.
;   POOL   buffers (generation owner bytes), owner (:free), (:workspace id inc)
;          (mutable, one instance) or (:leased id inc) (immutable; the pair is
;          where the buffer returns when the lease ends).  At an action boundary
;          a buffer is named by a handle (h g off len).  The third state,
;          BORROWED, exists only inside one call: the instance machine reads the
;          pool and cannot write it; it changes buffers only by requests.
;   USES   the outstanding-action table: (kind id inc handle), one per
;          submitted action until its completion arrives, keys (kind id inc)
;          distinct.  A buffered action holds a lease on its handle's buffer.
;
; A completion that matches no outstanding use -- a duplicate, a forgery, one
; already ended, one naming a retired incarnation -- changes nothing and emits
; nothing (T6).  The layer checks the host's discipline; it does not assume it.
;
; Cancellation: an instance may request (:cancel kind) for its own outstanding
; action; the layer emits (:cancel id inc (kind)) to the host and keeps the use.
; The use, and any lease it holds, ends only on the action's own completion,
; which after a cancel is (:cancelled) or whatever the worker actually did.
; A-HOST-COMPLETES (statement below): the host delivers exactly one completion
; for every submitted action.  Under it a deadline (a :timer) followed by a
; cancel bounds how long any action can pin its slot and its buffer.
;
; v1 limitation: the key (kind id inc) allows one outstanding action per kind
; per instance, so an instance cannot keep two :pread in flight (no double-
; buffered reads).  Revisit when a measured served path needs it: cold ARTICLE
; of a multi-extent article whose per-read latency, serialized, misses the
; ARTICLE 3 MiB bar in PRODUCT-DRAFT; the change is an operation number in the
; key, not a new mechanism.
;
; The ownership invariant OutstandingUse(h,g) => BytesStable(h,g) and
; not Recyclable(h,g) is `fn-rtc-invp''s lease clause plus the two-state
; theorem `fn-rtc-outstanding-use-is-stable' (statements below).  A lease is
; released only by the completion of its last use; a deadline, a close or any
; other event retains it (the uncertainty rule of books/page-read-ownership.lisp,
; kept).  Data an :in action reads (:recv, :pread) is part of its completion in
; this model and lands in the buffer exactly when the lease ends; in the
; executable pool the bytes are already in the array (A-HOST).
;
; The work budget: the instance machine is charged its quantum q plus a
; constant; the layer adds work bounded by the configuration, so one step costs
; at most q + (fn-rtc-step-c config).  Work an instance cannot finish within q
; stays in its own state and resumes on the completion of a zero-delay :timer
; it submits; there is no other continuation mechanism.
;
; The commit point: :commit is not an action kind.  An instance's commit
; observer (`fn-rtc-m-committedp') may turn true only on the delivery of a
; (:fsync (:done n)) completion of the instance's own outstanding :fsync; the
; landing that writes the transaction machine says which record that barrier
; makes durable.

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

; (kind id inc outcome) or, for an :in kind, (kind id inc outcome data).
(defun fn-rtc-completionp (e)
  (declare (xargs :guard t))
  (and (true-listp e)
       (or (equal (len e) 4) (equal (len e) 5))
       (member-eq (fn-rtc-get 0 e) *fn-rtc-kinds*)
       (natp (fn-rtc-get 1 e))
       (natp (fn-rtc-get 2 e))
       (fn-rtc-outcomep (fn-rtc-get 3 e))))

(defun fn-rtc-e-kind (e) (declare (xargs :guard t)) (fn-rtc-get 0 e))
(defun fn-rtc-e-id (e) (declare (xargs :guard t)) (nfix (fn-rtc-get 1 e)))
(defun fn-rtc-e-inc (e) (declare (xargs :guard t)) (nfix (fn-rtc-get 2 e)))
(defun fn-rtc-e-outcome (e) (declare (xargs :guard t)) (fn-rtc-get 3 e))
(defun fn-rtc-e-data (e) (declare (xargs :guard t)) (fn-rtc-get 4 e))

(defun fn-rtc-actionp (a)
  (declare (xargs :guard t))
  (and (true-listp a) (equal (len a) 4)
       (member-eq (fn-rtc-get 0 a) *fn-rtc-action-kinds*)
       (natp (fn-rtc-get 1 a)) (natp (fn-rtc-get 2 a))
       (true-listp (fn-rtc-get 3 a))))

; -----------------------------------------------------------------------------
; Slots, buffers, uses

(defun fn-rtc-slotp (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 3)
       (natp (fn-rtc-get 0 x))
       (member-eq (fn-rtc-get 1 x) '(:free :live :closing :draining))
       (or (null (fn-rtc-get 2 x)) (natp (fn-rtc-get 2 x)))))

(defun fn-rtc-s-inc (x) (declare (xargs :guard t)) (nfix (fn-rtc-get 0 x)))
(defun fn-rtc-s-status (x) (declare (xargs :guard t)) (fn-rtc-get 1 x))
(defun fn-rtc-s-res (x) (declare (xargs :guard t)) (fn-rtc-get 2 x))

(defconst *fn-rtc-listener* '(0 :live nil))

(defun fn-rtc-ownerp (o)
  (declare (xargs :guard t))
  (and (true-listp o)
       (case (fn-rtc-get 0 o)
         (:free (equal (len o) 1))
         ((:workspace :leased)
          (and (equal (len o) 3) (natp (fn-rtc-get 1 o)) (natp (fn-rtc-get 2 o))))
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
  (and (true-listp u) (equal (len u) 4)
       (member-eq (fn-rtc-get 0 u) *fn-rtc-kinds*)
       (natp (fn-rtc-get 1 u)) (natp (fn-rtc-get 2 u))
       (if (or (member-eq (fn-rtc-get 0 u) *fn-rtc-in-kinds*)
               (member-eq (fn-rtc-get 0 u) *fn-rtc-out-kinds*))
           (fn-rtc-handlep (fn-rtc-get 3 u))
         (null (fn-rtc-get 3 u)))))

; The key of a use, an action or a completion: (kind id inc).
(defun fn-rtc-key (x)
  (declare (xargs :guard t))
  (list (fn-rtc-get 0 x) (fn-rtc-get 1 x) (fn-rtc-get 2 x)))

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
      (or (let ((hd (fn-rtc-get 3 (car uses))))
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
; The layer state (config slots pool uses mstates)

(defun fn-rtc-config (s) (declare (xargs :guard t)) (fn-rtc-get 0 s))
(defun fn-rtc-slots (s) (declare (xargs :guard t)) (fn-rtc-get 1 s))
(defun fn-rtc-pool (s) (declare (xargs :guard t)) (fn-rtc-get 2 s))
(defun fn-rtc-uses (s) (declare (xargs :guard t)) (fn-rtc-get 3 s))
(defun fn-rtc-mstates (s) (declare (xargs :guard t)) (fn-rtc-get 4 s))

(defun fn-rtc-make (config slots pool uses mstates)
  (declare (xargs :guard t))
  (list config slots pool uses mstates))

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
; incarnation; a lease's return pair names a slot; a lease is held by some use
; at the buffer's generation.
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
                (fn-rtc-holds-p h (fn-rtc-b-gen b) (fn-rtc-uses s)))
               (otherwise t))
             (fn-rtc-pool-okp (+ 1 h) (cdr pool) s)))
    (null pool)))

; Count of uses holding buffer H at generation G (an :in lease has exactly one).
(defun fn-rtc-holders (h g uses)
  (declare (xargs :guard t))
  (if (consp uses)
      (+ (let ((hd (fn-rtc-get 3 (car uses))))
           (if (and (fn-rtc-handlep hd)
                    (equal (fn-rtc-h-buf hd) h)
                    (equal (fn-rtc-h-gen hd) g))
               1 0))
         (fn-rtc-holders h g (cdr uses)))
    0))

; One outstanding use against the state: it belongs to its slot's current
; incarnation; a buffered use's handle names a leased buffer at its current
; generation, within the bytes (:out) or within capacity starting inside the
; bytes (:in), and an :in lease is exclusive; :accept is the listener's and
; :close is a closing slot's.
(defun fn-rtc-use-okp (u s)
  (declare (xargs :guard t))
  (let* ((kind (fn-rtc-get 0 u)) (id (nfix (fn-rtc-get 1 u))) (inc (fn-rtc-get 2 u))
         (hd (fn-rtc-get 3 u)) (cfg (fn-rtc-config s)))
    (and (fn-rtc-usep u)
         (< id (fn-rtc-nslots cfg))
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
                         (if (member-eq kind *fn-rtc-in-kinds*)
                             (and (<= (fn-rtc-h-off hd) (len (fn-rtc-b-bytes b)))
                                  (<= (+ (fn-rtc-h-off hd) (fn-rtc-h-len hd))
                                      (fn-rtc-cap cfg))
                                  (equal (fn-rtc-holders h (fn-rtc-h-gen hd)
                                                         (fn-rtc-uses s))
                                         1))
                           (<= (+ (fn-rtc-h-off hd) (fn-rtc-h-len hd))
                               (len (fn-rtc-b-bytes b))))))))))

(defun fn-rtc-uses-okp (uses s)
  (declare (xargs :guard t))
  (if (consp uses)
      (and (fn-rtc-use-okp (car uses) s)
           (not (fn-rtc-find-use (fn-rtc-key (car uses)) (cdr uses)))
           (fn-rtc-uses-okp (cdr uses) s))
    (null uses)))

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
    (and (true-listp s) (equal (len s) 5)
         (fn-rtc-configp cfg)
         (equal (len (fn-rtc-slots s)) (fn-rtc-nslots cfg))
         (fn-rtc-slots-okp 0 (fn-rtc-slots s))
         (equal (len (fn-rtc-pool s)) (fn-rtc-nbufs cfg))
         (fn-rtc-pool-okp 0 (fn-rtc-pool s) s)
         (fn-rtc-uses-okp (fn-rtc-uses s) s)
         (true-listp (fn-rtc-mstates s))
         (equal (len (fn-rtc-mstates s)) (fn-rtc-nslots cfg))
         (fn-rtc-draining-okp 0 (fn-rtc-slots s) (fn-rtc-uses s))
         ;; the listener's :accept is armed exactly while a slot is free
         (iff (fn-rtc-free-slot 0 (fn-rtc-slots s))
              (fn-rtc-find-use '(:accept 0 0) (fn-rtc-uses s))))))

; -----------------------------------------------------------------------------
; The instance machine, constrained.
;
; (fn-rtc-m-step m ev pool q) => (mv m2 requests cost).  EV is the delivered
; completion without its identity, (kind outcome); POOL is borrowed (read
; only).  Requests, processed in order by `fn-rtc-requests':
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
      (+ (if (and (true-listp (car reqs)) (eq (fn-rtc-get 0 (car reqs)) :write))
             (len (fn-rtc-get 4 (car reqs)))
           0)
         (fn-rtc-reqs-octets (cdr reqs)))
    0))

(defun fn-rtc-fsync-done-p (ev)
  (declare (xargs :guard t))
  (and (eq (fn-rtc-get 0 ev) :fsync)
       (eq (fn-rtc-get 0 (fn-rtc-get 1 ev)) :done)))

(encapsulate
  (((fn-rtc-m-init) => *)
   ((fn-rtc-m-step * * * *) => (mv * * *))
   ((fn-rtc-m-committedp *) => *)
   ((fn-rtc-m-c) => *)
   ((fn-rtc-m-max-reqs) => *))

  (local (defun fn-rtc-m-init () nil))
  (local (defun fn-rtc-m-step (m ev pool q)
           (declare (ignore ev pool q))
           (mv m nil 0)))
  (local (defun fn-rtc-m-committedp (m) (declare (ignore m)) nil))
  (local (defun fn-rtc-m-c () 0))
  (local (defun fn-rtc-m-max-reqs () 0))

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

  (defthm fn-rtc-m-init-is-uncommitted
    (not (fn-rtc-m-committedp (fn-rtc-m-init))))

  ; The commit point is the completion of a barrier, never a submission.
  (defthm fn-rtc-m-commits-only-on-fsync-done
    (implies (and (not (fn-rtc-m-committedp m))
                  (fn-rtc-m-committedp (mv-nth 0 (fn-rtc-m-step m ev pool q))))
             (fn-rtc-fsync-done-p ev))))

; -----------------------------------------------------------------------------
; Ending a use

(defun fn-rtc-splice (bytes off data)
  (declare (xargs :guard t))
  (append (take (min (nfix off) (len bytes)) (true-list-fix bytes))
          (true-list-fix data)
          (nthcdr (+ (nfix off) (len data)) (true-list-fix bytes))))

; What the instance is told: a completion that is malformed for its use (an
; :in completion whose data is not N octets within the handle, an :out count
; beyond the handle) is reported as (:failed :malformed-completion); the use
; ends either way, because the worker has let go of the buffer.
(defun fn-rtc-delivered-outcome (u e)
  (declare (xargs :guard t))
  (let* ((kind (fn-rtc-get 0 u)) (hd (fn-rtc-get 3 u)) (o (fn-rtc-e-outcome e))
         (tag (fn-rtc-get 0 o)) (n (fn-rtc-get 1 o)))
    (cond ((not (member-eq tag '(:done :short))) o)
          ((member-eq kind *fn-rtc-in-kinds*)
           (if (and (fn-cbor-octet-listp (fn-rtc-e-data e))
                    (equal (len (fn-rtc-e-data e)) n)
                    (<= (nfix n) (fn-rtc-h-len hd)))
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
               (fn-rtc-pool s) (fn-rtc-uses s) (fn-rtc-mstates s)))

(defun fn-rtc-with-buffer (h b s)
  (declare (xargs :guard t))
  (fn-rtc-make (fn-rtc-config s) (fn-rtc-slots s) (fn-rtc-set h b (fn-rtc-pool s))
               (fn-rtc-uses s) (fn-rtc-mstates s)))

(defun fn-rtc-with-uses (uses s)
  (declare (xargs :guard t))
  (fn-rtc-make (fn-rtc-config s) (fn-rtc-slots s) (fn-rtc-pool s)
               uses (fn-rtc-mstates s)))

(defun fn-rtc-with-mstate (id m s)
  (declare (xargs :guard t))
  (fn-rtc-make (fn-rtc-config s) (fn-rtc-slots s) (fn-rtc-pool s)
               (fn-rtc-uses s) (fn-rtc-set id m (fn-rtc-mstates s))))

; Remove the use E completes.  If it held the last use of its buffer the
; lease ends: generation + 1, back to the return pair's workspace when that
; instance is live or closing (an :in completion's data spliced in only when it
; is live: a closing instance reads nothing more), else :free.  A :draining slot with no use left is retired to :free.
(defun fn-rtc-end-use (s e)
  (declare (xargs :guard t))
  (let* ((key (fn-rtc-key e))
         (u (fn-rtc-find-use key (fn-rtc-uses s))))
    (if (not (and (fn-rtc-completionp e) u))
        s
      (let* ((uses2 (fn-rtc-remove-use key (fn-rtc-uses s)))
             (s1 (fn-rtc-with-uses uses2 s))
             (hd (fn-rtc-get 3 u))
             (s2 (if (not (fn-rtc-handlep hd))
                     s1
                   (let* ((h (fn-rtc-h-buf hd)) (g (fn-rtc-h-gen hd))
                          (b (fn-rtc-buffer h s1)) (o (fn-rtc-b-owner b)))
                     (if (fn-rtc-holds-p h g uses2)
                         s1
                       (let* ((rid (nfix (fn-rtc-get 1 o))) (rinc (fn-rtc-get 2 o))
                              (back (and (fn-rtc-current-p rid rinc s1)
                                         (member-eq (fn-rtc-s-status (fn-rtc-slot rid s1))
                                                    '(:live :closing))))
                              (out (fn-rtc-delivered-outcome u e))
                              (bytes (if (and back
                                              (eq (fn-rtc-s-status (fn-rtc-slot rid s1)) :live)
                                              (member-eq (fn-rtc-get 0 u) *fn-rtc-in-kinds*)
                                              (member-eq (fn-rtc-get 0 out) '(:done :short)))
                                         (fn-rtc-splice (fn-rtc-b-bytes b) (fn-rtc-h-off hd)
                                                        (fn-rtc-e-data e))
                                       (fn-rtc-b-bytes b))))
                         (fn-rtc-with-buffer
                          h (list (+ 1 g) (if back (list :workspace rid rinc) '(:free)) bytes)
                          s1))))))
             (id (fn-rtc-e-id e))
             (slot (fn-rtc-slot id s2)))
        (if (and (eq (fn-rtc-s-status slot) :draining)
                 (not (fn-rtc-uses-of-slot-p id (fn-rtc-s-inc slot) (fn-rtc-uses s2))))
            (fn-rtc-with-slot id (list (fn-rtc-s-inc slot) :free nil) s2)
          s2)))))

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
        (mv (fn-rtc-with-uses
             (cons (list :close id inc nil) (fn-rtc-uses s))
             (fn-rtc-with-slot id (list inc :closing (fn-rtc-s-res slot)) s))
            (list (list :close id inc (list (fn-rtc-s-res slot))))
            nil
            (+ 1 (fn-rtc-use-bound (fn-rtc-config s))))
      (mv s nil (list r) 1))))

; May instance (ID INC) submit KIND on handle HD?  An :in kind needs its own
; workspace (the worker will write it); an :out kind its own workspace or a
; buffer already leased at the handle's generation (shared, immutable).
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
           (and (or own (eq (fn-rtc-get 0 o) :leased))
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
                (true-listp extra)
                (not (fn-rtc-find-use (list kind id inc) (fn-rtc-uses s)))))
      (mv s nil (list r) cost))
     ((not (fn-rtc-buffered-kind-p kind))
      (if (null hd)
          (mv (fn-rtc-with-uses (cons (list kind id inc nil) (fn-rtc-uses s)) s)
              (list (list kind id inc (cons res extra)))
              nil cost)
        (mv s nil (list r) cost)))
     ((not (fn-rtc-submit-okp kind hd id inc s))
      (mv s nil (list r) cost))
     (t
      (let* ((h (fn-rtc-h-buf hd)) (b (fn-rtc-buffer h s))
             (s1 (if (equal (fn-rtc-b-owner b) (list :workspace id inc))
                     (fn-rtc-with-buffer
                      h (list (fn-rtc-b-gen b) (list :leased id inc) (fn-rtc-b-bytes b)) s)
                   s)))
        (mv (fn-rtc-with-uses (cons (list kind id inc hd) (fn-rtc-uses s1)) s1)
            (list (list kind id inc (list* hd res extra)))
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
  :hints (("Goal" :in-theory (disable fn-rtc-submit-okp fn-rtc-with-uses fn-rtc-with-buffer
                                      fn-rtc-find-use fn-rtc-live-p fn-rtc-buffered-kind-p))))

; Ask the host to finish this instance's outstanding KIND action early.  The
; use stays; nothing in the pool changes.  Refused when no such use exists.
(defun fn-rtc-req-cancel (r id inc s)
  (declare (xargs :guard t))
  (let ((kind (fn-rtc-get 1 r)))
    (if (and (member-eq kind *fn-rtc-machine-kinds*)
             (fn-rtc-current-p id inc s)
             (fn-rtc-find-use (list kind id inc) (fn-rtc-uses s)))
        (mv s (list (list :cancel id inc (list kind))) nil
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
           (not (fn-rtc-find-use '(:accept 0 0) (fn-rtc-uses s))))
      (mv (fn-rtc-with-uses (cons (list :accept 0 0 nil) (fn-rtc-uses s)) s)
          (list (list :accept 0 0 (list nil))))
    (mv s nil)))

(defthm fn-rtc-rearm-lists
  (true-listp (mv-nth 1 (fn-rtc-rearm s))))

; Release every workspace of (ID INC) to :free.
(defun fn-rtc-release-all (h pool id inc)
  (declare (xargs :guard (natp h) :measure (len pool)))
  (if (consp pool)
      (cons (if (equal (fn-rtc-b-owner (car pool)) (list :workspace id inc))
                (list (fn-rtc-b-gen (car pool)) '(:free) (fn-rtc-b-bytes (car pool)))
              (car pool))
            (fn-rtc-release-all (+ 1 h) (cdr pool) id inc))
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

; Deliver EV to instance (ID INC) and process its requests.
(defun fn-rtc-deliver (s id inc ev q)
  (declare (xargs :guard t))
  (mv-let (m2 reqs cm)
    (fn-rtc-m-step (fn-rtc-mstate id s) ev (fn-rtc-pool s) (nfix q))
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
             (out (fn-rtc-delivered-outcome u e)))
        (cond
         ((eq kind :accept)
          (let ((j (fn-rtc-free-slot 0 (fn-rtc-slots s1)))
                (r (fn-rtc-get 1 out)))
            (if (and (eq (fn-rtc-get 0 out) :done) j)
                (let* ((jinc (+ 1 (fn-rtc-s-inc (fn-rtc-slot j s1))))
                       (s2 (fn-rtc-with-mstate
                            j (fn-rtc-m-init)
                            (fn-rtc-with-slot j (list jinc :live (nfix r)) s1))))
                  (mv-let (s3 acts refused c)
                    (fn-rtc-deliver s2 j jinc (list :accept out) q)
                    (mv-let (s4 acts2) (fn-rtc-rearm s3)
                      (mv s4 (append acts acts2) refused (+ base c)))))
              (mv-let (s2 acts2) (fn-rtc-rearm s1)
                (mv s2 acts2 nil base)))))
         ((eq kind :close)
          (let* ((s2 (fn-rtc-make (fn-rtc-config s1) (fn-rtc-slots s1)
                                  (fn-rtc-release-all 0 (fn-rtc-pool s1) id inc)
                                  (fn-rtc-uses s1) (fn-rtc-mstates s1)))
                 (status (if (fn-rtc-uses-of-slot-p id inc (fn-rtc-uses s2)) :draining :free))
                 (s3 (fn-rtc-with-mstate
                      id (fn-rtc-m-init)
                      (fn-rtc-with-slot id (list inc status (if (eq status :free) nil
                                                              (fn-rtc-s-res (fn-rtc-slot id s2))))
                                        s2))))
            (mv-let (s4 acts2) (fn-rtc-rearm s3)
              (mv s4 acts2 nil (+ base (fn-rtc-nbufs cfg))))))
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
      (+ (let ((hd (fn-rtc-get 0 (fn-rtc-get 3 (car acts)))))
           (if (fn-rtc-handlep hd) (fn-rtc-h-len hd) 0))
         (fn-rtc-actions-octets (cdr acts)))
    0))

(defun fn-rtc-step-c (cfg)
  (declare (xargs :guard t))
  (+ 4 (fn-rtc-m-c) (* 2 (fn-rtc-nslots cfg)) (fn-rtc-nbufs cfg)
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
                (make-list (fn-rtc-nslots cfg) :initial-element nil))))

#|
; =============================================================================
; STATEMENTS (for review; no proof attempted yet)

; T1. The initial state satisfies the invariant.
(defthm fn-rtc-init-establishes-invp
  (implies (fn-rtc-configp cfg)
           (fn-rtc-invp (mv-nth 0 (fn-rtc-init cfg)))))

; T2. Every step preserves it, for every event and every quantum.
(defthm fn-rtc-step-preserves-invp
  (implies (fn-rtc-invp s)
           (fn-rtc-invp (mv-nth 0 (fn-rtc-step s e q)))))

; T3. OutstandingUse(h,g) => not Recyclable(h,g), and the handle is current.
(defthm fn-rtc-outstanding-use-is-leased
  (implies (and (fn-rtc-invp s)
                (member-equal u (fn-rtc-uses s))
                (fn-rtc-handlep (fn-rtc-get 3 u)))
           (let ((h (fn-rtc-h-buf (fn-rtc-get 3 u))))
             (and (not (fn-rtc-recyclablep h s))
                  (equal (fn-rtc-gen h s) (fn-rtc-h-gen (fn-rtc-get 3 u)))))))

; T4. OutstandingUse(h,g) => BytesStable(h,g), across a step: whatever the
; event -- a deadline, a close, another instance's completion, a forged or
; duplicate completion -- a use survives, and its buffer's bytes, generation
; and lease are unchanged, unless the event is that use's own completion.
; This is also the lease-retained-on-uncertainty rule.
(defthm fn-rtc-outstanding-use-is-stable
  (implies (and (fn-rtc-invp s)
                (member-equal u (fn-rtc-uses s))
                (not (fn-rtc-ends-use-p e u)))
           (let ((s2 (mv-nth 0 (fn-rtc-step s e q))))
             (and (member-equal u (fn-rtc-uses s2))
                  (implies (fn-rtc-handlep (fn-rtc-get 3 u))
                           (let ((h (fn-rtc-h-buf (fn-rtc-get 3 u))))
                             (equal (fn-rtc-buffer h s2) (fn-rtc-buffer h s))))))))

; T5. A use's own completion ends it, and nothing else does (with T4).
(defthm fn-rtc-completion-ends-its-use
  (implies (and (fn-rtc-invp s)
                (member-equal u (fn-rtc-uses s))
                (fn-rtc-ends-use-p e u))
           (not (fn-rtc-find-use (fn-rtc-key u)
                                 (fn-rtc-uses (fn-rtc-end-use s e))))))

; T6. A completion that matches no outstanding use -- a duplicate, a forgery, one
; already ended, or one naming an incarnation other than its slot's current one
; (every outstanding use is at its slot's current incarnation) -- changes
; nothing and emits nothing.  The layer checks the host; it does not trust it.
(defthm fn-rtc-unmatched-completion-is-discarded
  (implies (and (fn-rtc-invp s)
                (not (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s))))
           (and (equal (mv-nth 0 (fn-rtc-step s e q)) s)
                (equal (mv-nth 1 (fn-rtc-step s e q)) nil))))

; T7. An instance's machine state changes only by an event that acts on it
; (its own outstanding action's completion at its live incarnation, or the
; :accept that creates it).
(defthm fn-rtc-machine-changes-only-on-its-own-completion
  (implies (and (fn-rtc-invp s)
                (not (equal (fn-rtc-mstate j (mv-nth 0 (fn-rtc-step s e q)))
                            (fn-rtc-mstate j s))))
           (and (fn-rtc-acts-on-p s e)
                (equal (nfix j) (fn-rtc-target s e)))))

; T8. Workspace isolation: a step leaves every workspace of an instance
; other than the one the event is for exactly as it was (owner and bytes).
(defthm fn-rtc-other-workspaces-are-untouched
  (implies (and (fn-rtc-invp s)
                (equal (fn-rtc-get 0 (fn-rtc-b-owner (fn-rtc-buffer h s))) :workspace)
                (not (equal (fn-rtc-get 1 (fn-rtc-b-owner (fn-rtc-buffer h s)))
                            (fn-rtc-target s e))))
           (equal (fn-rtc-buffer h (mv-nth 0 (fn-rtc-step s e q)))
                  (fn-rtc-buffer h s))))

; T9. Generations never decrease: a handle that stopped being current never
; becomes current again, so a recycled buffer is never reached by a stale
; handle.
(defthm fn-rtc-generation-is-monotone
  (implies (fn-rtc-invp s)
           (<= (fn-rtc-gen h s) (fn-rtc-gen h (mv-nth 0 (fn-rtc-step s e q))))))

; T10. Every emitted action is well formed; every action but :cancel is
; recorded in the outstanding-use table of the resulting state under its key,
; and a :cancel names a use that is still outstanding there (cancel does not
; end a use).
(defthm fn-rtc-every-action-is-outstanding
  (implies (and (fn-rtc-invp s)
                (member-equal a (mv-nth 1 (fn-rtc-step s e q))))
           (and (fn-rtc-actionp a)
                (if (equal (fn-rtc-get 0 a) :cancel)
                    (fn-rtc-find-use (list (fn-rtc-get 0 (fn-rtc-get 3 a))
                                           (fn-rtc-get 1 a) (fn-rtc-get 2 a))
                                     (fn-rtc-uses (mv-nth 0 (fn-rtc-step s e q))))
                  (fn-rtc-find-use (fn-rtc-key a)
                                   (fn-rtc-uses (mv-nth 0 (fn-rtc-step s e q))))))))

; T11. The commit point: an instance's commit observer turns true only on
; the delivery of a (:fsync (:done n)) completion of its own outstanding
; :fsync at its live incarnation.  This is the layer's half.  Which barrier an
; instance may commit on (for POST: the barrier after its log record, not the
; payload barrier) is the instance's own keystone, the first of landing 2.
(defthm fn-rtc-commit-only-on-own-barrier-completion
  (implies (and (fn-rtc-invp s)
                (not (fn-rtc-m-committedp (fn-rtc-mstate j s)))
                (fn-rtc-m-committedp (fn-rtc-mstate j (mv-nth 0 (fn-rtc-step s e q)))))
           (and (fn-rtc-acts-on-p s e)
                (equal (fn-rtc-e-kind e) :fsync)
                (equal (nfix j) (fn-rtc-e-id e))
                (equal (fn-rtc-get 0 (fn-rtc-e-outcome e)) :done))))

; T12. The work budget: one step costs at most the quantum plus a term of the
; configuration, emits a bounded number of actions, and the octets those
; actions name (its retained output) are bounded by the configuration.
(defthm fn-rtc-step-is-charged
  (implies (and (fn-rtc-invp s) (natp q))
           (and (<= (fn-rtc-step-cost s e q)
                    (+ q (fn-rtc-step-c (fn-rtc-config s))))
                (<= (len (mv-nth 1 (fn-rtc-step s e q)))
                    (+ 1 (fn-rtc-m-max-reqs)))
                (<= (fn-rtc-actions-octets (mv-nth 1 (fn-rtc-step s e q)))
                    (* (fn-rtc-m-max-reqs) (fn-rtc-cap (fn-rtc-config s)))))))

; T13. Drain progresses: a :draining slot whose last outstanding use is ended
; by this event is retired to :free, and the listener's :accept is armed.
(defthm fn-rtc-last-completion-retires-a-draining-slot
  (implies (and (fn-rtc-invp s)
                (equal (fn-rtc-s-status (fn-rtc-slot j s)) :draining)
                (member-equal u (fn-rtc-uses s))
                (equal (fn-rtc-get 1 u) j)
                (fn-rtc-ends-use-p e u)
                (not (fn-rtc-uses-of-slot-p j (fn-rtc-s-inc (fn-rtc-slot j s))
                                            (fn-rtc-remove-use (fn-rtc-key u) (fn-rtc-uses s)))))
           (let ((s2 (mv-nth 0 (fn-rtc-step s e q))))
             (and (equal (fn-rtc-s-status (fn-rtc-slot j s2)) :free)
                  (fn-rtc-find-use '(:accept 0 0) (fn-rtc-uses s2))))))

; A-HOST-COMPLETES, the named assumption (an encapsulate in
; books/assumptions-runtime.lisp, statement here): the host delivers exactly
; one completion for every submitted action.  Over a host trace -- the actions
; the layer emitted and the events the host returned after them, in order --
; every non-:cancel action's key is the key of exactly one later completion.
;
;   (encapsulate (((fn-assume-host-completions *) => *))
;     (local (defun fn-assume-host-completions (actions)  ; witness: cancel all
;              (fn-rtc-cancel-all actions)))
;     (defthm fn-assume-host-completes-every-action
;       (implies (and (member-equal a actions) (not (equal (fn-rtc-get 0 a) :cancel)))
;                (equal (fn-rtc-count-key (fn-rtc-key a)
;                                         (fn-assume-host-completions actions))
;                       1)))
;     (defthm fn-assume-host-completions-are-completions
;       (fn-rtc-completion-listp (fn-assume-host-completions actions))))
;
; With T4 (only its own completion ends a use), T13 and A-HOST-COMPLETES, every
; draining slot is eventually retired: the pin a stuck action holds is bounded by
; the instance's deadline plus the host's completion of the cancel.
|#|#
