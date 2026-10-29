; Declared costs and resource effects of the outside calls layer A's arms
; make (R7 defcost). Each names a function the :callbacks section resolves.
; Bytes of an I/O range are charged by the arm that sizes it, not here.
(in-package "ACL2")
(include-book "machines-a-access")

; Reads of the directory and the pool: no work beyond the arm's own step.
(defcost fn2-machine-admission-credits :doc "The directory's free admission credits.")
(defcost fn2-machine-free-head :doc "The directory's free connection-row head.")
(defcost fn2-machine-gen-limit :doc "The profile's generation limit.")
(defcost fn2-machine-pool-capacity-read-code :doc "Whether a pool slot's capacity is readable.")
(defcost fn2-machine-pool-capacity :doc "A pool slot's capacity in bytes.")
(defcost fn2-machine-pool-borrows-read-code :doc "Whether a pool slot's borrow count is readable.")
(defcost fn2-machine-pool-borrows :doc "A pool slot's outstanding borrows.")
(defcost fn2-scribe-window-class :doc "The pool class of a 4 KiB window.")

; Issues: one descriptor and one transient op reservation (D0's :operation).
(defcost fn2-issue-accept :descriptors 1 :tables (fn2-core-ops) :effects ((:acquire (:operation)))
  :doc "Accept: one outbox descriptor.")
(defcost fn2-issue-close :descriptors 1 :tables (fn2-core-ops) :effects ((:acquire (:operation)))
  :doc "Close: one outbox descriptor.")
(defcost fn2-issue-receive :descriptors 1 :tables (fn2-core-ops fn2-core-pool) :effects ((:acquire (:operation)))
  :doc "Receive into the row's RX range.")
(defcost fn2-issue-send :descriptors 1 :tables (fn2-core-ops fn2-core-pool) :effects ((:acquire (:operation)))
  :doc "Send by loan from the row's range.")
(defcost fn2-issue-write :descriptors 1 :tables (fn2-core-ops fn2-core-pool) :effects ((:acquire (:operation)))
  :doc "Write from the scribe's window.")
(defcost fn2-issue-fence :descriptors 1 :tables (fn2-core-ops) :effects ((:acquire (:operation)))
  :doc "Fence the scribe's writes.")
(defcost fn2-issue-read :descriptors 1 :tables (fn2-core-ops fn2-core-pool) :effects ((:acquire (:operation)))
  :doc "Read into the scribe's window.")

; Generic row helpers: they write the acting row's wait links and status.
(defcost fn2-machine-issue-result :steps *fn2-work-mailbox*
  :own-writes (pending wait-reason stopped ready-prev ready-next)
  :tables (fn2-core-machines fn2-core-machine-tables)
  :doc "Record an issue's outcome: pending, park on exhaustion, or stop.")
(defcost fn2-machine-park :own-writes (wait-reason ready-prev ready-next)
  :tables (fn2-core-machines fn2-core-machine-tables) :doc "Park on the operation-credit FIFO.")
(defcost fn2-machine-park-admission :own-writes (wait-reason ready-prev ready-next)
  :tables (fn2-core-machines fn2-core-machine-tables) :doc "Park on the admission FIFO.")
(defcost fn2-machine-park-pool :own-writes (wait-reason cursor) :tables (fn2-core-machines)
  :doc "Park as the pool waiter, recording the class.")
(defcost fn2-machine-idle :steps *fn2-work-empty* :doc "An idle row's empty run.")
(defcost fn2-machine-yield :steps *fn2-work-empty* :doc "Yield with the continuation kept.")
(defcost fn2-machine-refuse-phase :steps *fn2-work-empty* :tables (fn2-core-control)
  :doc "Stop on an inconsistent row.")
(defcost fn2-machine-refuse-observation :tables (fn2-core-control) :doc "Stop on an undeliverable observation.")
(defcost fn2-core-stop :tables (fn2-core-control) :doc "Record the first stop reason.")

; The admission bundle's moves (D0's effect rows, declared here as their source).
(defcost fn2-listener-take-credit :tables (fn2-core-machines) :effects ((:acquire (:connection-row)))
  :doc "Reserve one connection row at Accept issue.")
(defcost fn2-listener-return-credit :tables (fn2-core-machines) :effects ((:release (:connection-row)))
  :doc "Return a reserved row: failed Accept, refused admission.")
(defcost fn2-machine-admit-connection
  :tables (fn2-core-machines fn2-core-pool fn2-echo-table)
  :effects ((:transfer (:connection-row) :to fn2-echo) (:acquire (:rx-range) :for fn2-echo))
  :target (fn2-echo :free :command)
  :doc "Install an accepted connection: the reserved row moves to it with a fresh RX range.")
(defcost fn2-machine-reclaim-connection :tables (fn2-core-machines)
  :effects ((:release (:connection-row)))
  :doc "Return a drained connection row to the free list and its credit (unless it retires).")

; Pool range operations: the resource kind is the caller's (:rx-range for a
; connection, :storage-window for the scribe), given in its :uses entry.
(defcost fn2-core-reserve :tables (fn2-core-pool) :effects :per-use :doc "Reserve a pool range.")
(defcost fn2-core-release :tables (fn2-core-pool) :effects :per-use :doc "Release a pool range.")
(defcost fn2-core-reset :tables (fn2-core-pool) :doc "Reset a held range to empty.")
(defcost fn2-scribe-fill :bytes *fn2-scribe-chunk-bytes* :tables (fn2-core-pool)
  :doc "Write one chunk of the probe sector.")
(defcost fn2-scribe-patch-loop :bytes *fn2-format-word-bytes* :tables (fn2-core-pool)
  :doc "Patch the sector's checksum word.")
(defcost fn2-scribe-verify :bytes *fn2-scribe-chunk-bytes* :doc "Verify one chunk read back.")
