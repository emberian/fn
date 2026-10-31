; Layer E (D8's rows, E's book; fn2/docs/e-surface.md 7, lanes/e-continuation
; E.P1): the subscription edges a parked consumer wait holds. An edge names a
; stream, a waiter row with its generation, and FROM, the first position the
; waiter has not read. Row I of the table is both edge I and bucket I; the
; edges of stream S are chained (doubly linked, appended at the tail) from
; bucket S mod rows.
;
; Allocation (D's review 2): an edge comes from the free list, else from the
; never-used rows above FRESH, so a link succeeds while fewer than rows edges
; are in use. With rows at least the profile's :esub, every link the
; ledger's :subscription-edge holding admits succeeds; the ledger is the
; admission authority and USED-COUNT is the table's capacity, never a second
; one.
;
; Wake (B's stream-wake hook): a publish of POSITION on S raises the bucket's
; BPOS and, if the bucket has edges and is not pending, pushes it on the
; pending-bucket stack (doubly linked) with its cursor at the chain's head:
; O(1) per published member. The :wait-row grant source wakes the cursor's
; waiter (clearing its :wait-row wait) and advances the cursor; a bucket
; whose cursor runs off its chain leaves the stack. Every edge of a pending
; bucket is woken once per pass: an edge of a colliding stream, or one a
; waiter will find already read, is a harmless wake (the row reads again and
; re-parks); an edge linked during a pass is appended ahead of the cursor.
;
; Liveness (D's review 1): READY-P holds exactly when the top bucket's cursor
; is an edge in use with a waiter, which is what GRANT-ONE returns; an unlink
; moves a cursor past its edge and takes a bucket whose cursor runs out off
; the stack at once, so no bucket below the top is ever stuck.
;
; The link race (D's review 3, K4b): LINK answers :behind, linking nothing,
; when the bucket's BPOS is at or above FROM: a publish touching the bucket
; since the waiter's read (whose frontier is FROM - 1) has already run its
; hook, and the waiter reads again instead of parking. A publish after the
; link finds the edge. So no publish between the read and the park is lost.
(in-package "ACL2")
(include-book "columns")
(include-book "arm-children")
(fn2-book-layer :e)

(defconst *fn2-cns-none* 4294967295)
(defcolumns fn2-cns-edges
  (;; the edge
   (used :bool) (stream :u60) (waiter :u32) (gen :u60) (from :u60)
   (enext :link) (eprev :link)
   ;; the bucket (every link column starts at none)
   (bhead :link) (btail :link) (bcur :link) (bpos :u60) (bpend :bool) (bpnext :link) (bpprev :link))
  :extra-fields
  ((fn2-cns-free-head :type (unsigned-byte 32) :initially 4294967295
    :why "The free list of released edges, threaded through ENEXT.")
   (fn2-cns-fresh :type (unsigned-byte 32) :initially 0
    :why "The first never-used row: rows at or above it are free without being on the list.")
   (fn2-cns-pending-head :type (unsigned-byte 32) :initially 4294967295
    :why "The top of the pending-bucket stack, threaded through BPNEXT and BPPREV.")
   (fn2-cns-used-count :type (unsigned-byte 32) :initially 0
    :why "Edges in use: the table's capacity beside the ledger's :subscription-edge holding.")))

(defmacro fn2-cns-ix (x) `(and (natp ,x) (< ,x (fn2-cns-edges-rows fn2-cns-edges)) (unsigned-byte-p 32 ,x)))
(defun fn2-cns-bucket (stream fn2-cns-edges)
  (declare (xargs :stobjs fn2-cns-edges :guard (fn2-cns-edges-wfp fn2-cns-edges)))
  (if (and (natp stream) (posp (fn2-cns-edges-rows fn2-cns-edges)))
      (mod stream (fn2-cns-edges-rows fn2-cns-edges))
    *fn2-cns-none*))

;; ---- the pending-bucket stack -------------------------------------------
(defun fn2-cns-push-bucket (b fn2-cns-edges)
  ; B pending, its cursor at its head (B has edges and is not pending)
  (declare (xargs :stobjs fn2-cns-edges :guard (fn2-cns-edges-wfp fn2-cns-edges)))
  (let ((top (fn2-cns-pending-head fn2-cns-edges)))
    (if (not (and (fn2-cns-ix b) (unsigned-byte-p 32 top))) fn2-cns-edges
      (let* ((fn2-cns-edges (fn2-cns-edges-put b (bpend 1) (bpnext top) (bpprev *fn2-cns-none*)
                                               (bcur (fn2-cns-edges-bhead b fn2-cns-edges))))
             (fn2-cns-edges (if (fn2-cns-ix top) (fn2-cns-edges-set-bpprev top b fn2-cns-edges) fn2-cns-edges)))
        (update-fn2-cns-pending-head b fn2-cns-edges)))))
(fn2-cns-edges-preserves fn2-cns-push-bucket (b fn2-cns-edges) :position nil :rows t :raw-rows t)
(defun fn2-cns-remove-bucket (b fn2-cns-edges)
  ; take pending bucket B off the stack, wherever it is
  (declare (xargs :stobjs fn2-cns-edges :guard (fn2-cns-edges-wfp fn2-cns-edges)))
  (if (not (and (fn2-cns-ix b) (equal (fn2-cns-edges-bpend b fn2-cns-edges) 1))) fn2-cns-edges
    (let* ((next (fn2-cns-edges-bpnext b fn2-cns-edges)) (prev (fn2-cns-edges-bpprev b fn2-cns-edges))
           (fn2-cns-edges (if (fn2-cns-ix next) (fn2-cns-edges-set-bpprev next prev fn2-cns-edges) fn2-cns-edges))
           (fn2-cns-edges (if (fn2-cns-ix prev) (fn2-cns-edges-set-bpnext prev next fn2-cns-edges)
                            (update-fn2-cns-pending-head next fn2-cns-edges))))
      (fn2-cns-edges-put b (bpend 0) (bpnext *fn2-cns-none*) (bpprev *fn2-cns-none*) (bcur *fn2-cns-none*)))))
(fn2-cns-edges-preserves fn2-cns-remove-bucket (b fn2-cns-edges) :position nil :rows t :raw-rows t)

;; ---- link and unlink ----------------------------------------------------
(defun fn2-cns-alloc-row (fn2-cns-edges)
  ; a free edge (the free list's head, else the first never-used row), or none
  (declare (xargs :stobjs fn2-cns-edges :guard (fn2-cns-edges-wfp fn2-cns-edges)))
  (let ((f (fn2-cns-free-head fn2-cns-edges)) (fresh (fn2-cns-fresh fn2-cns-edges)))
    (cond ((fn2-cns-ix f) f)
          ((and (fn2-cns-ix fresh) (unsigned-byte-p 32 (+ 1 fresh))) fresh)
          (t *fn2-cns-none*))))
(defun fn2-cns-take-row (e fn2-cns-edges)
  ; take E, just chosen by fn2-cns-alloc-row, off the free list or the fresh rows
  (declare (xargs :stobjs fn2-cns-edges :guard (fn2-cns-edges-wfp fn2-cns-edges)))
  (cond ((not (fn2-cns-ix e)) fn2-cns-edges)
        ((equal e (fn2-cns-free-head fn2-cns-edges))
         (update-fn2-cns-free-head (fn2-cns-edges-enext e fn2-cns-edges) fn2-cns-edges))
        ((and (equal e (fn2-cns-fresh fn2-cns-edges)) (unsigned-byte-p 32 (+ 1 e)))
         (update-fn2-cns-fresh (+ 1 e) fn2-cns-edges))
        (t fn2-cns-edges)))
(fn2-cns-edges-preserves fn2-cns-take-row (e fn2-cns-edges) :position nil :rows t :raw-rows t)
(defun fn2-cns-edge-link (stream waiter gen from fn2-cns-edges)
  ; (mv code e fn2-cns-edges): :ok with the edge; :behind (a publish touching
  ; the bucket since the read: read again); :exhausted (every row in use)
  (declare (xargs :stobjs fn2-cns-edges :guard (fn2-cns-edges-wfp fn2-cns-edges)))
  (let ((b (fn2-cns-bucket stream fn2-cns-edges)))
    (cond ((not (and (fn2-cns-ix b) (unsigned-byte-p 60 stream) (unsigned-byte-p 32 waiter)
                     (not (equal waiter *fn2-cns-none*)) (unsigned-byte-p 60 gen) (unsigned-byte-p 60 from)
                     (unsigned-byte-p 32 (+ 1 (fn2-cns-used-count fn2-cns-edges)))))
           (mv :exhausted *fn2-cns-none* fn2-cns-edges))
          ((<= from (fn2-cns-edges-bpos b fn2-cns-edges)) (mv :behind *fn2-cns-none* fn2-cns-edges))
          (t
           (let ((e (fn2-cns-alloc-row fn2-cns-edges)) (tail (fn2-cns-edges-btail b fn2-cns-edges))
                 (count (+ 1 (fn2-cns-used-count fn2-cns-edges))))
             (if (not (fn2-cns-ix e)) (mv :exhausted *fn2-cns-none* fn2-cns-edges)
               (let* ((fn2-cns-edges (fn2-cns-take-row e fn2-cns-edges))
                      (fn2-cns-edges (fn2-cns-edges-put e (used 1) (stream stream) (waiter waiter) (gen gen) (from from)
                                                        (enext *fn2-cns-none*) (eprev tail)))
                      (fn2-cns-edges (if (fn2-cns-ix tail) (fn2-cns-edges-set-enext tail e fn2-cns-edges)
                                       (fn2-cns-edges-set-bhead b e fn2-cns-edges)))
                      (fn2-cns-edges (fn2-cns-edges-set-btail b e fn2-cns-edges))
                      (fn2-cns-edges (update-fn2-cns-used-count count fn2-cns-edges)))
                 (mv :ok e fn2-cns-edges))))))))
(fn2-cns-edges-preserves fn2-cns-edge-link (stream waiter gen from fn2-cns-edges) :position 2 :rows t :raw-rows t)
(defun fn2-cns-edge-unlink (e fn2-cns-edges)
  ; release edge E: out of its bucket's chain (its cursor moved past it, the
  ; bucket off the stack if the cursor runs out), onto the free list
  (declare (xargs :stobjs fn2-cns-edges :guard (fn2-cns-edges-wfp fn2-cns-edges)))
  (if (not (and (fn2-cns-ix e) (equal (fn2-cns-edges-used e fn2-cns-edges) 1)
                (unsigned-byte-p 32 (fn2-cns-free-head fn2-cns-edges))))
      fn2-cns-edges
    (let* ((b (fn2-cns-bucket (fn2-cns-edges-stream e fn2-cns-edges) fn2-cns-edges))
           (next (fn2-cns-edges-enext e fn2-cns-edges)) (prev (fn2-cns-edges-eprev e fn2-cns-edges))
           (free (fn2-cns-free-head fn2-cns-edges)) (count (nfix (- (fn2-cns-used-count fn2-cns-edges) 1)))
           (cur (fn2-cns-edges-bcur (fn2-cns-bucket (fn2-cns-edges-stream e fn2-cns-edges) fn2-cns-edges) fn2-cns-edges)))
      (if (not (and (fn2-cns-ix b) (unsigned-byte-p 32 count))) fn2-cns-edges
        (let* ((fn2-cns-edges (if (fn2-cns-ix next) (fn2-cns-edges-set-eprev next prev fn2-cns-edges)
                                (fn2-cns-edges-set-btail b prev fn2-cns-edges)))
               (fn2-cns-edges (if (fn2-cns-ix prev) (fn2-cns-edges-set-enext prev next fn2-cns-edges)
                                (fn2-cns-edges-set-bhead b next fn2-cns-edges)))
               (fn2-cns-edges (if (equal cur e)
                                  (if (fn2-cns-ix next) (fn2-cns-edges-set-bcur b next fn2-cns-edges)
                                    (fn2-cns-remove-bucket b fn2-cns-edges))
                                fn2-cns-edges))
               (fn2-cns-edges (fn2-cns-edges-put e (used 0) (enext free)
                                                 (eprev *fn2-cns-none*)))
               (fn2-cns-edges (update-fn2-cns-free-head e fn2-cns-edges)))
          (update-fn2-cns-used-count count fn2-cns-edges))))))
(fn2-cns-edges-preserves fn2-cns-edge-unlink (e fn2-cns-edges) :position nil :rows t :raw-rows t)

;; ---- the publish hook and the grant source -----------------------------
(defun fn2-cns-wake-stream (stream position fn2-cns-edges)
  ; a publish of POSITION on STREAM (B's stream-wake hook): O(1)
  (declare (xargs :stobjs fn2-cns-edges :guard (fn2-cns-edges-wfp fn2-cns-edges)))
  (let ((b (fn2-cns-bucket stream fn2-cns-edges)))
    (if (not (and (fn2-cns-ix b) (unsigned-byte-p 60 position))) fn2-cns-edges
      (let ((fn2-cns-edges (if (< (fn2-cns-edges-bpos b fn2-cns-edges) position)
                               (fn2-cns-edges-set-bpos b position fn2-cns-edges) fn2-cns-edges)))
        (if (or (equal (fn2-cns-edges-bpend b fn2-cns-edges) 1)
                (not (fn2-cns-ix (fn2-cns-edges-bhead b fn2-cns-edges))))
            fn2-cns-edges
          (fn2-cns-push-bucket b fn2-cns-edges))))))
(fn2-cns-edges-preserves fn2-cns-wake-stream (stream position fn2-cns-edges) :position nil :rows t :raw-rows t)
(defun fn2-cns-ready-p (fn2-cns-edges)
  ; the top bucket's cursor is an edge in use with a waiter
  (declare (xargs :stobjs fn2-cns-edges :guard (fn2-cns-edges-wfp fn2-cns-edges)))
  (let ((b (fn2-cns-pending-head fn2-cns-edges)))
    (and (fn2-cns-ix b)
         (let ((c (fn2-cns-edges-bcur b fn2-cns-edges)))
           (and (fn2-cns-ix c) (equal (fn2-cns-edges-used c fn2-cns-edges) 1)
                (not (equal (fn2-cns-edges-waiter c fn2-cns-edges) *fn2-cns-none*)))))))
(defun fn2-cns-take-next (fn2-cns-edges)
  ; (mv waiter fn2-cns-edges): the top bucket's cursor's waiter; the cursor
  ; advanced, the bucket off the stack at its chain's end. The edge stays
  ; linked: its row unlinks it when it runs.
  (declare (xargs :stobjs fn2-cns-edges :guard (fn2-cns-edges-wfp fn2-cns-edges)))
  (if (not (fn2-cns-ready-p fn2-cns-edges)) (mv *fn2-none* fn2-cns-edges)
    (let* ((b (fn2-cns-pending-head fn2-cns-edges)) (c (fn2-cns-edges-bcur b fn2-cns-edges))
           (w (fn2-cns-edges-waiter c fn2-cns-edges)) (next (fn2-cns-edges-enext c fn2-cns-edges))
           (fn2-cns-edges (if (fn2-cns-ix next) (fn2-cns-edges-set-bcur b next fn2-cns-edges)
                            (fn2-cns-remove-bucket b fn2-cns-edges))))
      (mv w fn2-cns-edges))))
(fn2-cns-edges-preserves fn2-cns-take-next (fn2-cns-edges) :position 1 :rows t :raw-rows t)
(defthm fn2-cns-take-next-live
  (implies (fn2-cns-ready-p fn2-cns-edges)
           (not (equal (mv-nth 0 (fn2-cns-take-next fn2-cns-edges)) *fn2-none*)))
  :hints (("Goal" :in-theory (enable fn2-cns-take-next))))
(defun fn2-cns-grant-one (fn2-cns-edges fn2-machines fn2-control)
  ; the :wait-row grant source: the next waiter, its :wait-row wait cleared
  ; (the grant service makes it runnable; D's review 4)
  (declare (xargs :stobjs (fn2-cns-edges fn2-machines fn2-control)
                  :guard (and (fn2-cns-edges-wfp fn2-cns-edges) (fn2-machines-wfp fn2-machines) (fn2-control-wfp fn2-control))))
  (mv-let (w fn2-cns-edges) (fn2-cns-take-next fn2-cns-edges)
    (let ((fn2-machines (if (and (fn2-machines-row-ok w)
                                 (equal (fn2-machines-wait-reason w fn2-machines) *fn2-wait-wait-row*))
                            (fn2-machines-set-wait-reason w *fn2-wait-none* fn2-machines)
                          fn2-machines)))
      (mv w fn2-cns-edges fn2-machines fn2-control))))
(fn2-cns-edges-preserves fn2-cns-grant-one (fn2-cns-edges fn2-machines fn2-control)
  :carriers ((fn2-cns-edges 1) (fn2-machines 2 :prefix "-MACHINES") (fn2-control 3 :prefix "-CONTROL")))
;; The defwait pair's G-LIVE at the child level: a ready source grants a row.
(defthm fn2-cns-grant-one-live
  (implies (fn2-cns-ready-p fn2-cns-edges)
           (not (equal (mv-nth 0 (fn2-cns-grant-one fn2-cns-edges fn2-machines fn2-control)) *fn2-none*)))
  :hints (("Goal" :in-theory (e/d (fn2-cns-grant-one) (fn2-cns-take-next fn2-cns-ready-p))
                  :use fn2-cns-take-next-live)))
