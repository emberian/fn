; Witnesses for books/store-log-kernel-concrete (the log kernel the host
; holds: the committed records' count in place of their list).
;
; Every refinement theorem there is an unconditional equality, so there is no
; hypothesis to remove; the witnesses are (1) reachable: a real segment (the
; codec's workload records chained from genesis, zero padded) opened by
; fn-lgc-open, a host run of prepare / append / fence / finish-one / take /
; consume-to over it, both sides of the keystone evaluated and equal, the
; concrete kernel holding no record; (2) CORRUPTED STATE (labelled): a
; concrete kernel whose count is not the logical committed length is not the
; abstraction of it, and the acknowledgement then diverges -- the count is
; what the correspondence carries.
(in-package "ACL2")
(include-book "../../books/store-log-kernel-concrete")
; The record codec seam's attachment: the log's txid reads the record through
; fn-record-decode-exact (books/store-log-txid.lisp).
(include-book "../../books/codec-attach")

(defun slc-unit () (declare (xargs :guard t)) 4)
(defun slc-max () (declare (xargs :guard t)) 4096)
(defun slc-extent () (declare (xargs :guard t)) 2048)
(defun slc-rec (i) (declare (xargs :guard t :verify-guards nil)) (fn-lg-workload-record i 8))

(defun slc-chars (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (cons (code-char (if (and (natp (car xs)) (< (car xs) 256)) (car xs) 0))
            (slc-chars (cdr xs)))
    nil))

; The segment holding records 1 .. 2, chained from genesis, then zeros to
; the extent.
(defun slc-segment ()
  (declare (xargs :guard t :verify-guards nil))
  (let ((log (fn-lg-log (list (slc-rec 1) (slc-rec 2)) *fn-lg-genesis* (slc-unit))))
    (coerce (slc-chars (append log (fn-bs-zeros (- (slc-extent) (len log))))) 'string)))

(defun slc-open () (declare (xargs :guard t :verify-guards nil))
  (fn-lgc-open (slc-segment) *fn-lg-genesis* (slc-unit) (slc-max) 1))

; The host's run: record 3 prepared, appended, fenced, acknowledged three
; times (the third past nothing: the count bounds it); then record 4 taken,
; a consume-to past it, and a failed fence.
(defun slc-ops ()
  (declare (xargs :guard t :verify-guards nil))
  (list (list :prepare (slc-rec 3))
        (list :append (slc-unit) (slc-extent))
        (list :fence (slc-unit))
        (list :finish-one) (list :finish-one) (list :finish-one) (list :finish-one)
        (list :take (slc-rec 4) 4 0 0 64 1000000 (slc-unit))
        (list :consume-to 9)
        (list :fence-failed)))

; (1) The open: the decode's two records, and the concrete kernel counting them.
(assert-event
 (mv-let (records c) (slc-open)
   (and (equal records (list (slc-rec 1) (slc-rec 2)))
        (equal records (fn-lgk-committed (fn-lg-open-kernel (slc-segment) *fn-lg-genesis*
                                                            (slc-unit) (slc-max) 1)))
        (equal c (fn-lgc-of (fn-lg-open-kernel (slc-segment) *fn-lg-genesis*
                                               (slc-unit) (slc-max) 1)))
        (equal (fn-lgc-count c) 2)
        (equal (fn-lgc-acked c) 2)
        (equal (fn-lgc-next-txid c) 3)
        (< 0 (fn-lgc-frontier c)))))

; (1) The keystone's two sides on the run, equal; the logical kernel commits
; record 3, the concrete one counts it and holds no record at all.
(assert-event
 (let* ((c (fn-lgc-host-run (mv-let (records c0) (slc-open) (declare (ignore records)) c0)
                            (slc-ops)))
        (ks (fn-lgk-host-run (fn-lgt-recover (fn-lgd-octets (slc-segment)) *fn-lg-genesis*
                                             (slc-unit) (slc-max) 1)
                             (slc-ops))))
   (and (equal c (fn-lgc-of ks))
        (equal (fn-lgk-committed ks) (list (slc-rec 1) (slc-rec 2) (slc-rec 3)))
        (equal (fn-lgc-count c) 3)
        (equal (fn-lgc-acked c) 3)
        (equal (fn-lgc-batch c) (list (slc-rec 4)))
        (equal (fn-lgc-next-txid c) 9)
        (equal (fn-lgc-phase c) :fault)
        (not (member-equal (slc-rec 1) c))
        (not (member-equal (slc-rec 3) c)))))

; (1) The fence's step alone, after the append: count grows by the batch in
; flight and the frontier by its entries, as the logical fence commits them.
(assert-event
 (let* ((ks0 (fn-lg-open-kernel (slc-segment) *fn-lg-genesis* (slc-unit) (slc-max) 1))
        (ks1 (fn-lgk-append (fn-lgt-prepare ks0 (slc-rec 3)) (slc-unit) (slc-extent)))
        (c1 (fn-lgc-append (fn-lgc-t-prepare (fn-lgc-of ks0) (slc-rec 3)) (slc-unit) (slc-extent))))
   (and (equal c1 (fn-lgc-of ks1))
        (equal (fn-lgc-inflight c1) (list (slc-rec 3)))
        (equal (fn-lgc-fence c1 (slc-unit)) (fn-lgc-of (fn-lgk-fence ks1 (slc-unit))))
        (equal (fn-lgc-count (fn-lgc-fence c1 (slc-unit))) 3)
        (equal (fn-lgc-frontier (fn-lgc-fence c1 (slc-unit)))
               (+ (fn-lgc-frontier c1) (len (fn-lgc-append-octets (fn-lgc-t-prepare (fn-lgc-of ks0) (slc-rec 3)) (slc-unit))))))))

; (1) The refused prepare: a record whose txid is not the next leaves both
; kernels unchanged.
(assert-event
 (let ((ks0 (fn-lg-open-kernel (slc-segment) *fn-lg-genesis* (slc-unit) (slc-max) 1)))
   (and (equal (fn-lgc-t-prepare (fn-lgc-of ks0) (slc-rec 7)) (fn-lgc-of ks0))
        (equal (fn-lgt-prepare ks0 (slc-rec 7)) ks0))))

; (2) CORRUPTED STATE: a concrete kernel counting one record more than the
; logical kernel commits is not its abstraction, and acknowledging from it
; passes the committed records (acked 3 over 2 committed).
(assert-event
 (let* ((ks0 (fn-lg-open-kernel (slc-segment) *fn-lg-genesis* (slc-unit) (slc-max) 1))
        (bad (fn-lgc-make 3 (fn-lgk-last ks0) (fn-lgk-frontier ks0) (fn-lgk-next-txid ks0)
                          nil nil 2 :ready)))
   (and (not (equal bad (fn-lgc-of ks0)))
        (equal (fn-lgc-acked (fn-lgc-finish-one bad)) 3)
        (equal (fn-lgk-acked (fn-lgk-finish-one ks0)) 2)
        (not (equal (fn-lgc-finish-one bad) (fn-lgc-of (fn-lgk-finish-one ks0)))))))

; (1) The rotation (host fnn-log-rotate): after the fence and the
; acknowledgements it is admitted and needed, the new segment's kernel counts
; nothing and keeps the chain head and the txid, on both sides of the
; keystone; with a record prepared and not appended it is refused and the
; kernel is unchanged.
(assert-event
 (let* ((ops (list (list :prepare (slc-rec 3)) (list :append (slc-unit) (slc-extent))
                   (list :fence (slc-unit)) (list :finish-one) (list :rotate)))
        (before (fn-lgc-host-run (mv-let (records c0) (slc-open) (declare (ignore records)) c0)
                                 (butlast ops 1)))
        (c (fn-lgc-host-run (mv-let (records c0) (slc-open) (declare (ignore records)) c0) ops))
        (ks (fn-lgk-host-run (fn-lgt-recover (fn-lgd-octets (slc-segment)) *fn-lg-genesis*
                                             (slc-unit) (slc-max) 1)
                             ops)))
   (and (fn-lgc-rotate-admitsp before)
        (fn-lgc-rotate-needed-p before)
        (equal c (fn-lgc-of ks))
        (equal (fn-lgc-count c) 0)
        (equal (fn-lgc-frontier c) 0)
        (equal (fn-lgc-last c) (fn-lgc-last before))
        (equal (fn-lgc-next-txid c) 4)
        (equal (fn-lgk-committed ks) nil))))

(assert-event
 (let* ((c0 (mv-let (records c0) (slc-open) (declare (ignore records)) c0))
        (c1 (fn-lgc-t-prepare c0 (slc-rec 3))))
   (and (not (fn-lgc-rotate-admitsp c1))
        (equal (fn-lgc-host-step c1 (list :rotate)) c1))))

; -----------------------------------------------------------------------------
; Lane kernel-concrete-2 (PRF-282): the pipelined commit's operations, the
; extension, and the executable framing.

; (1) Every function the host calls on the served path runs as guard-verified
; code (no *1* recursion per octet): the fit, the append's length and octets,
; the append, the fence, the extension's decision and target, the take.
(defun slc-verifiedp (fns wrld)
  (declare (xargs :mode :program))
  (or (atom fns)
      (and (eq (symbol-class (car fns) wrld) :common-lisp-compliant)
           (slc-verifiedp (cdr fns) wrld))))

(assert-event
 (slc-verifiedp '(fn-lgc-log-len fn-lgc-log-octets fn-lgc-last-trailer fn-lgx-log
                  fn-lgx-last-trailer fn-lgc-append-len fn-lgc-fitsp fn-lgc-append-admitsp
                  fn-lgc-append-octets fn-lgc-append fn-lgc-fence fn-lgc-fence-failed
                  fn-lgc-finish-one fn-lgc-t-prepare fn-lgc-take fn-lgc-consume-to
                  fn-lgc-extension-needed-p fn-lgc-extension-target fn-lgc-sealed-extent
                  fn-lgc-rotate fn-lgc-rotate-admitsp fn-lgc-rotate-needed-p fn-lgc-phase
                  fn-lgc-batch)
                (w state)))

; (1) The arithmetic length is the octets' length on a batch that is one
; packed chunk (two records) and on one record, from genesis and from a
; chain head of another length (no hypothesis on the head).
(assert-event
 (let ((b (list (slc-rec 5) (slc-rec 6))))
   (and (equal (fn-lgc-log-len b 32 (slc-unit)) (len (fn-lg-log b *fn-lg-genesis* (slc-unit))))
        (equal (fn-lgc-log-len (list (slc-rec 5)) 32 7)
               (len (fn-lg-log (list (slc-rec 5)) *fn-lg-genesis* 7)))
        (equal (fn-lgc-log-len b 3 (slc-unit)) (len (fn-lg-log b '(1 2 3) (slc-unit))))
        (equal (fn-lgc-log-octets b *fn-lg-genesis* (slc-unit))
               (fn-lg-log b *fn-lg-genesis* (slc-unit)))
        (equal (fn-lgc-last-trailer b *fn-lg-genesis*) (fn-lg-last-trailer b *fn-lg-genesis*))
        ; the fallback branch (a head that is not a digest) answers the logical value
        (equal (fn-lgc-log-octets b '(1 2 3) (slc-unit)) (fn-lg-log b '(1 2 3) (slc-unit))))))

; (1) A 3 MiB record (the article size that exhausted the owner's control
; stack, input-loop-2 section 6): its append's length, fit and octets are
; computed; the octets' length is the arithmetic one.
(assert-event
 (let* ((b (list (make-list 3145728 :initial-element 65)))
        (c (fn-lgc-make 0 *fn-lg-genesis* 0 1 b nil 0 :ready))
        (n (fn-lgc-append-len c 4096)))
   (and (< 3145728 n)
        (equal (mod n 4096) 0)
        (fn-lgc-fitsp c 4096 n)
        (not (fn-lgc-fitsp c 4096 (- n 4096)))
        (equal (len (fn-lgc-append-octets c 4096)) n)
        (equal (fn-lgc-frontier (fn-lgc-fence (fn-lgc-append c 4096 n) 4096)) n))))

; (1) The pipelined commit (lane log-2), both sides of the keystone: record 3
; taken and SEALED (the extension needed from a one-unit extent, then the
; append into the target), record 4 taken BEHIND the batch in flight (a take
; between the seal and its fence), the syncer's fence, COMPLETE's
; acknowledgement; then record 4's seal and fence.  The concrete kernel holds
; no record; the counts and frontiers agree with the logical run.
(defun slc-pipelined-ops (extent)
  (declare (xargs :guard t :verify-guards nil))
  (list (list :take (slc-rec 3) 3 0 0 64 1000000 (slc-unit))
        (list :seal (slc-unit) extent)
        (list :take (slc-rec 4) 4 0 0 64 1000000 (slc-unit))
        (list :fence (slc-unit))
        (list :finish-one)
        (list :seal (slc-unit) extent)
        (list :fence (slc-unit))
        (list :finish-one)))

(assert-event
 (let* ((c0 (mv-let (records c0) (slc-open) (declare (ignore records)) c0))
        (ks0 (fn-lgt-recover (fn-lgd-octets (slc-segment)) *fn-lg-genesis* (slc-unit) (slc-max) 1))
        (extent (+ (fn-lgc-frontier c0) (slc-unit)))
        (c (fn-lgc-host-run c0 (slc-pipelined-ops extent)))
        (ks (fn-lgk-host-run ks0 (slc-pipelined-ops extent)))
        (after-take (fn-lgc-host-run c0 (take 1 (slc-pipelined-ops extent))))
        (behind (fn-lgc-host-run c0 (take 3 (slc-pipelined-ops extent)))))
   (and (fn-lgc-extension-needed-p after-take extent (slc-unit))
        (< extent (fn-lgc-sealed-extent after-take extent (slc-unit)))
        (equal (fn-lgc-inflight behind) (list (slc-rec 3)))
        (equal (fn-lgc-batch behind) (list (slc-rec 4)))
        (equal (fn-lgc-phase behind) :appended)
        (equal c (fn-lgc-of ks))
        (equal (fn-lgk-committed ks) (list (slc-rec 1) (slc-rec 2) (slc-rec 3) (slc-rec 4)))
        (equal (fn-lgc-count c) 4)
        (equal (fn-lgc-acked c) 4)
        ; two entries past the open's frontier: record 3's, then record 4's
        ; chained from it
        (equal (fn-lgc-frontier c)
               (+ (fn-lgc-frontier c0)
                  (len (fn-lg-log (list (slc-rec 3)) (fn-lgc-last c0) (slc-unit)))
                  (len (fn-lg-log (list (slc-rec 4))
                                  (fn-lg-last-trailer (list (slc-rec 3)) (fn-lgc-last c0))
                                  (slc-unit)))))
        (not (member-equal (slc-rec 3) c)))))

; (1) Without the extension the seal's append is refused: the same take,
; appended into the one-unit extent, leaves the kernel unchanged.
(assert-event
 (let* ((c0 (mv-let (records c0) (slc-open) (declare (ignore records)) c0))
        (extent (+ (fn-lgc-frontier c0) (slc-unit)))
        (c1 (cadr (fn-lgc-take c0 (slc-rec 3) 3 0 0 64 1000000 (slc-unit)))))
   (and (not (fn-lgc-fitsp c1 (slc-unit) extent))
        (equal (fn-lgc-append c1 (slc-unit) extent) c1)
        (fn-lgc-fitsp c1 (slc-unit) (fn-lgc-sealed-extent c1 extent (slc-unit))))))

; (2) CORRUPTED STATE: a concrete kernel whose chain head is not the
; logical one's frames the batch differently -- the append's octets are
; not the logical kernel's, though their length is.
(assert-event
 (let* ((ks0 (fn-lg-open-kernel (slc-segment) *fn-lg-genesis* (slc-unit) (slc-max) 1))
        (ks1 (fn-lgt-prepare ks0 (slc-rec 3)))
        (bad (fn-lgc-make 2 *fn-lg-genesis* (fn-lgk-frontier ks1) (fn-lgk-next-txid ks1)
                          (fn-lgk-batch ks1) nil 2 :ready)))
   (and (not (equal bad (fn-lgc-of ks1)))
        (not (equal (fn-lgc-append-octets bad (slc-unit)) (fn-lgk-append-octets ks1 (slc-unit))))
        (equal (fn-lgc-append-len bad (slc-unit)) (len (fn-lgk-append-octets ks1 (slc-unit)))))))
