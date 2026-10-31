; Layer E (D8's rows, E's book; fn2/docs/e-surface.md 7, lanes/e-continuation
; E.P1): the subscription edges a parked consumer wait holds. An edge names
; a stream and a waiter row (with its generation) and the first position it
; waits for. An edge for stream S sits in one of the *fn2-cns-probes* slots
; from S mod rows (open addressing), so a publish touches at most that many
; slots, never the table. A publish of position P on S marks each matching
; edge pending (fn2-cns-wake-stream, B's stream-wake hook); the wait kind's
; grant service wakes one pending waiter per grant through the directory's
; wake slot (fn2-cns-grant-one), popping a stack threaded through PNEXT. A
; pending edge stays on the stack until popped, so an unlink never breaks it
; and a stale pop wakes nothing. A wrong wake is harmless (the woken row
; reads again and re-parks); a missed one is what this table excludes (K4b).
; Registered as a core child at P4 (the assembly as a registry).
(in-package "ACL2")
(include-book "columns")
(include-book "arm-children")
(fn2-book-layer :e)

(defconst *fn2-cns-none* 4294967295)
(defconst *fn2-cns-probes* 8)
(defcolumns fn2-cns-edges
  ((used :bool) (stream :u60) (waiter :u32) (gen :u60) (from :u60) (pending :bool) (pnext :u32))
  :extra-fields
  ((fn2-cns-pending-head :type (unsigned-byte 32) :initially 4294967295
    :why "Head of the pending-wake stack threaded through PNEXT; the grant service pops it.")
   (fn2-cns-used-count :type (unsigned-byte 32) :initially 0
    :why "Edges in use, the :subscription-edge holding the ledger checks against.")))

(defun fn2-cns-slot (stream k n)
  ; the K-th probe slot of STREAM in a table of N rows
  (declare (xargs :guard (and (natp stream) (natp k) (posp n))))
  (mod (+ (mod stream n) k) n))
(defthm fn2-cns-slot-natp
  (implies (and (natp stream) (natp k) (posp n)) (natp (fn2-cns-slot stream k n)))
  :rule-classes :type-prescription)
(defthm fn2-cns-slot-bound
  (implies (and (natp stream) (natp k) (posp n)) (< (fn2-cns-slot stream k n) n))
  :rule-classes :linear)
(in-theory (disable fn2-cns-slot))

(defun fn2-cns-edge-free (stream k fn2-cns-edges)
  ; the first unused probe slot of STREAM at or after probe K, or nil
  (declare (xargs :stobjs fn2-cns-edges :guard (and (fn2-cns-edges-wfp fn2-cns-edges) (natp stream) (natp k))
                  :measure (nfix (- *fn2-cns-probes* (nfix k)))))
  (cond ((or (not (natp k)) (>= k *fn2-cns-probes*) (zp (fn2-cns-edges-rows fn2-cns-edges))) nil)
        ((equal (fn2-cns-edges-used (fn2-cns-slot stream k (fn2-cns-edges-rows fn2-cns-edges)) fn2-cns-edges) 0)
         (fn2-cns-slot stream k (fn2-cns-edges-rows fn2-cns-edges)))
        (t (fn2-cns-edge-free stream (+ 1 k) fn2-cns-edges))))
(defthm fn2-cns-edge-free-natp
  (implies (natp stream)
           (or (null (fn2-cns-edge-free stream k fn2-cns-edges)) (natp (fn2-cns-edge-free stream k fn2-cns-edges))))
  :hints (("Goal" :induct (fn2-cns-edge-free stream k fn2-cns-edges)))
  :rule-classes :type-prescription)
(defthm fn2-cns-edge-free-bound
  (implies (and (natp stream) (fn2-cns-edge-free stream k fn2-cns-edges))
           (< (fn2-cns-edge-free stream k fn2-cns-edges) (fn2-cns-edges-rows fn2-cns-edges)))
  :hints (("Goal" :induct (fn2-cns-edge-free stream k fn2-cns-edges)))
  :rule-classes :linear)
(in-theory (disable fn2-cns-edge-free))

(defun fn2-cns-edge-link (stream waiter gen from fn2-cns-edges)
  ; (mv code e fn2-cns-edges): :ok with the edge, or :exhausted (no free probe
  ; slot, or every edge in use: the :subscription-edge holding refused).
  (declare (xargs :stobjs fn2-cns-edges
                  :guard (and (fn2-cns-edges-wfp fn2-cns-edges) (unsigned-byte-p 60 stream) (unsigned-byte-p 32 waiter)
                              (unsigned-byte-p 60 gen) (unsigned-byte-p 60 from))
                              ))
  (let ((e (and (natp stream) (fn2-cns-edge-free stream 0 fn2-cns-edges))))
    (if (or (null e) (not (unsigned-byte-p 32 (+ 1 (fn2-cns-used-count fn2-cns-edges))))
            (not (and (unsigned-byte-p 60 stream) (unsigned-byte-p 32 waiter) (unsigned-byte-p 60 gen)
                      (unsigned-byte-p 60 from))))
        (mv :exhausted *fn2-cns-none* fn2-cns-edges)
      (let* ((count (+ 1 (fn2-cns-used-count fn2-cns-edges)))
             (fn2-cns-edges (fn2-cns-edges-put e (used 1) (stream stream) (waiter waiter) (gen gen) (from from)))
             (fn2-cns-edges (update-fn2-cns-used-count count fn2-cns-edges)))
        (mv :ok e fn2-cns-edges)))))

(fn2-cns-edges-preserves fn2-cns-edge-link (stream waiter gen from fn2-cns-edges) :position 2 :rows t :raw-rows t)
(defun fn2-cns-edge-unlink (e fn2-cns-edges)
  ; free edge E (a pending edge stays on the stack; its pop wakes nothing)
  (declare (xargs :stobjs fn2-cns-edges :guard (fn2-cns-edges-wfp fn2-cns-edges)))
  (if (not (and (natp e) (< e (fn2-cns-edges-rows fn2-cns-edges)) (equal (fn2-cns-edges-used e fn2-cns-edges) 1)))
      fn2-cns-edges
    (let ((fn2-cns-edges (fn2-cns-edges-set-used e 0 fn2-cns-edges)))
      (update-fn2-cns-used-count (nfix (- (fn2-cns-used-count fn2-cns-edges) 1)) fn2-cns-edges))))

(fn2-cns-edges-preserves fn2-cns-edge-unlink (e fn2-cns-edges) :position nil :rows t :raw-rows t)
(defun fn2-cns-mark (e fn2-cns-edges)
  ; push E on the pending stack unless it is already there
  (declare (xargs :stobjs fn2-cns-edges :guard (fn2-cns-edges-wfp fn2-cns-edges)))
  (if (or (not (and (natp e) (< e (fn2-cns-edges-rows fn2-cns-edges)) (unsigned-byte-p 32 e)
                    (unsigned-byte-p 32 (fn2-cns-pending-head fn2-cns-edges))))
          (equal (fn2-cns-edges-pending e fn2-cns-edges) 1))
      fn2-cns-edges
    (let* ((head (fn2-cns-pending-head fn2-cns-edges))
           (fn2-cns-edges (fn2-cns-edges-put e (pending 1) (pnext head))))
      (update-fn2-cns-pending-head e fn2-cns-edges))))

(fn2-cns-edges-preserves fn2-cns-mark (e fn2-cns-edges) :position nil :rows t :raw-rows t)
(defun fn2-cns-wake-probes (stream position k fn2-cns-edges)
  (declare (xargs :stobjs fn2-cns-edges :guard (and (fn2-cns-edges-wfp fn2-cns-edges) (natp stream) (natp position) (natp k))
                  :measure (nfix (- *fn2-cns-probes* (nfix k)))))
  (if (or (not (natp k)) (>= k *fn2-cns-probes*) (zp (fn2-cns-edges-rows fn2-cns-edges))) fn2-cns-edges
    (let* ((e (fn2-cns-slot stream k (fn2-cns-edges-rows fn2-cns-edges)))
           (fn2-cns-edges (if (and (equal (fn2-cns-edges-used e fn2-cns-edges) 1)
                                   (equal (fn2-cns-edges-stream e fn2-cns-edges) stream)
                                   (<= (fn2-cns-edges-from e fn2-cns-edges) position))
                              (fn2-cns-mark e fn2-cns-edges)
                            fn2-cns-edges)))
      (fn2-cns-wake-probes stream position (+ 1 k) fn2-cns-edges))))
(fn2-cns-edges-preserves fn2-cns-wake-probes (stream position k fn2-cns-edges) :position nil :rows t :raw-rows t
  :hints (("Goal" :induct (fn2-cns-wake-probes stream position k fn2-cns-edges))))
(defun fn2-cns-wake-stream (stream position fn2-cns-edges)
  ; a publish of POSITION on STREAM: mark every matching edge pending
  (declare (xargs :stobjs fn2-cns-edges :guard (and (fn2-cns-edges-wfp fn2-cns-edges) (natp stream) (natp position))))
  (fn2-cns-wake-probes stream position 0 fn2-cns-edges))

(fn2-cns-edges-preserves fn2-cns-wake-stream (stream position fn2-cns-edges) :position nil :rows t :raw-rows t)
(defun fn2-cns-ready-p (fn2-cns-edges)
  (declare (xargs :stobjs fn2-cns-edges :guard (fn2-cns-edges-wfp fn2-cns-edges)))
  (not (equal (fn2-cns-pending-head fn2-cns-edges) *fn2-cns-none*)))
(defun fn2-cns-pop (fn2-cns-edges)
  ; (mv waiter fn2-cns-edges): pop one pending edge; its waiter if still in use, else none
  (declare (xargs :stobjs fn2-cns-edges :guard (fn2-cns-edges-wfp fn2-cns-edges)))
  (let ((e (fn2-cns-pending-head fn2-cns-edges)))
    (if (not (and (natp e) (< e (fn2-cns-edges-rows fn2-cns-edges)) (equal (fn2-cns-edges-pending e fn2-cns-edges) 1)))
        (let ((fn2-cns-edges (update-fn2-cns-pending-head *fn2-cns-none* fn2-cns-edges)))
          (mv *fn2-cns-none* fn2-cns-edges))
      (let* ((waiter (if (equal (fn2-cns-edges-used e fn2-cns-edges) 1) (fn2-cns-edges-waiter e fn2-cns-edges) *fn2-cns-none*))
             (next (fn2-cns-edges-pnext e fn2-cns-edges))
             (fn2-cns-edges (fn2-cns-edges-put e (pending 0) (pnext *fn2-cns-none*))))
        (let ((fn2-cns-edges (update-fn2-cns-pending-head next fn2-cns-edges)))
          (mv waiter fn2-cns-edges))))))
(fn2-cns-edges-preserves fn2-cns-pop (fn2-cns-edges) :position 1 :rows t :raw-rows t)
(defun fn2-cns-grant-one (fn2-cns-edges fn2-machines fn2-control)
  ; the :wait-row grant source: pop one pending edge and wake its waiter
  (declare (xargs :stobjs (fn2-cns-edges fn2-machines fn2-control)
                  :guard (and (fn2-cns-edges-wfp fn2-cns-edges) (fn2-machines-wfp fn2-machines) (fn2-control-wfp fn2-control))))
  (mv-let (waiter fn2-cns-edges) (fn2-cns-pop fn2-cns-edges)
    (if (equal waiter *fn2-cns-none*) (mv waiter fn2-cns-edges fn2-machines fn2-control)
      (mv-let (fn2-machines fn2-control) (fn2-machines-wake-row waiter fn2-machines fn2-control)
        (mv waiter fn2-cns-edges fn2-machines fn2-control)))))
(fn2-cns-edges-preserves fn2-cns-grant-one (fn2-cns-edges fn2-machines fn2-control)
  :carriers ((fn2-cns-edges 1) (fn2-machines 2 :prefix "-MACHINES") (fn2-control 3 :prefix "-CONTROL")))
