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
