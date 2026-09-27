; fn: the record log's kernel as the host holds it: COMMITTED as its length
; (lane per-record-state, 2026-09-27; D27).
;
; The logical kernel (books/store-log-kernel.lisp) is
;   (:lgk COMMITTED LAST FRONTIER NEXT-TXID BATCH INFLIGHT ACKED PHASE)
; and its relation R, the crash theorems and the programs speak of COMMITTED,
; the list of every record the durable segment scans to.  No transition the
; served path runs reads COMMITTED's elements: the fence appends to it, the
; acknowledgement compares ACKED with its length, and the open hands it to the
; replay once.  Held for the life of the process it cost 16 octets of conses
; per history octet (measured: 38.8 MB for 1,000 POSTs of 2 KiB, section 1 of
; planning/evidence/per-record-state-2026-09-27.md), and each fence copied it
; (an O(N) append per batch).
;
; The concrete kernel keeps the COUNT in COMMITTED's place:
;   (:lgc COUNT LAST FRONTIER NEXT-TXID BATCH INFLIGHT ACKED PHASE)
; `fn-lgc-of' is the abstraction (the logical kernel's COMMITTED replaced by
; its length, every other position copied), and every transition the host
; calls commutes with it, with no hypothesis:
;
;   (fn-lgc-T (fn-lgc-of ks) args) = (fn-lgc-of (fn-lgk-T ks args))
;
; for T in prepare (txid-checked), take, consume-to, append, fence,
; fence-failed, finish-one; the observers (frontier, next txid, last, acked,
; phase, append octets, fits, admits) answer what the logical ones answer.
; KEYSTONE `fn-lgc-run-refines-the-kernel': over ANY sequence of host
; operations, the concrete kernel reached from the open is fn-lgc-of the
; logical kernel reached from the recovered kernel, so every theorem over the
; logical run (R preserved by append and fence, the crash image a prefix) is a
; theorem about the kernel the host holds.  `fn-lgc-open' answers the scan's
; records (the replay's input, dropped by the host after the replay) and the
; concrete kernel of fn-lg-open-kernel.
;
; Host: host/native/io.lisp fnn-log-open-kernel calls fn-lgc-open; fnn-log-
; prepare fn-lgc-prepare; fnn-log-append fn-lgc-append-admitsp, fn-lgc-append-
; octets, fn-lgc-append; fnn-log-fence fn-lgc-fence / fn-lgc-fence-failed;
; fnn-log-finish fn-lgc-finish-one; fnn-log-take fn-lgc-take; the open's catch
; up fn-lgc-consume-to.  No skip-proofs.

(in-package "ACL2")
(include-book "store-log-route")
(include-book "store-log-segments")

; -----------------------------------------------------------------------------
; The concrete state.

(defun fn-lgc-make (count last frontier next-txid batch inflight acked phase)
  (declare (xargs :guard t))
  (list :lgc count last frontier next-txid batch inflight acked phase))

(defun fn-lgc-count (c) (declare (xargs :guard (true-listp c))) (nfix (nth 1 c)))
(defun fn-lgc-last (c) (declare (xargs :guard (true-listp c))) (nth 2 c))
(defun fn-lgc-frontier (c) (declare (xargs :guard (true-listp c))) (nfix (nth 3 c)))
(defun fn-lgc-next-txid (c) (declare (xargs :guard (true-listp c))) (nfix (nth 4 c)))
(defun fn-lgc-batch (c) (declare (xargs :guard (true-listp c))) (nth 5 c))
(defun fn-lgc-inflight (c) (declare (xargs :guard (true-listp c))) (nth 6 c))
(defun fn-lgc-acked (c) (declare (xargs :guard (true-listp c))) (nfix (nth 7 c)))
(defun fn-lgc-phase (c) (declare (xargs :guard (true-listp c))) (nth 8 c))

; The abstraction: COMMITTED replaced by its length.
(defun fn-lgc-of (ks)
  (declare (xargs :guard (true-listp ks)))
  (fn-lgc-make (len (fn-lgk-committed ks)) (fn-lgk-last ks) (fn-lgk-frontier ks)
               (fn-lgk-next-txid ks) (fn-lgk-batch ks) (fn-lgk-inflight ks)
               (fn-lgk-acked ks) (fn-lgk-phase ks)))

; -----------------------------------------------------------------------------
; The transitions, each the logical one with COMMITTED's length in its place.

(defun fn-lgc-prepare (c record)
  (declare (xargs :guard (true-listp c)))
  (if (equal (fn-lgc-phase c) :fault)
      c
    (fn-lgc-make (fn-lgc-count c) (fn-lgc-last c) (fn-lgc-frontier c)
                 (1+ (fn-lgc-next-txid c))
                 (append (true-list-fix (fn-lgc-batch c)) (list record))
                 (fn-lgc-inflight c) (fn-lgc-acked c) (fn-lgc-phase c))))

; fn-lgt-prepare's txid check (the host's prepare).
(defun fn-lgc-t-prepare (c record)
  (declare (xargs :guard (true-listp c)))
  (if (equal (fn-lgt-txid record) (fn-lgc-next-txid c))
      (fn-lgc-prepare c record)
    c))

(defun fn-lgc-append-octets (c unit)
  (declare (xargs :guard t :verify-guards nil))
  (fn-lg-log (fn-lgc-batch c) (fn-lgc-last c) unit))

(defun fn-lgc-fitsp (c unit extent)
  (declare (xargs :guard t :verify-guards nil))
  (<= (+ (fn-lgc-frontier c) (len (fn-lgc-append-octets c unit))) (nfix extent)))

(defun fn-lgc-append-admitsp (c unit extent)
  (declare (xargs :guard t :verify-guards nil))
  (and (not (consp (fn-lgc-inflight c)))
       (not (equal (fn-lgc-phase c) :fault))
       (fn-lgc-fitsp c unit extent)))

(defun fn-lgc-append (c unit extent)
  (declare (xargs :guard t :verify-guards nil))
  (if (or (consp (fn-lgc-inflight c)) (equal (fn-lgc-phase c) :fault)
          (not (fn-lgc-fitsp c unit extent)))
      c
    (fn-lgc-make (fn-lgc-count c) (fn-lgc-last c) (fn-lgc-frontier c)
                 (fn-lgc-next-txid c) nil (true-list-fix (fn-lgc-batch c))
                 (fn-lgc-acked c) :appended)))

; The barrier returned :ok: the count grows by the batch in flight; nothing
; is copied.
(defun fn-lgc-fence (c unit)
  (declare (xargs :guard t :verify-guards nil))
  (let ((w (fn-lg-log (fn-lgc-inflight c) (fn-lgc-last c) unit)))
    (fn-lgc-make (+ (fn-lgc-count c) (len (fn-lgc-inflight c)))
                 (fn-lg-last-trailer (fn-lgc-inflight c) (fn-lgc-last c))
                 (+ (fn-lgc-frontier c) (len w))
                 (fn-lgc-next-txid c) (fn-lgc-batch c) nil
                 (fn-lgc-acked c) :fenced)))

(defun fn-lgc-fence-failed (c)
  (declare (xargs :guard (true-listp c)))
  (fn-lgc-make (fn-lgc-count c) (fn-lgc-last c) (fn-lgc-frontier c)
               (fn-lgc-next-txid c) (fn-lgc-batch c) (fn-lgc-inflight c)
               (fn-lgc-acked c) :fault))

(defun fn-lgc-finish-one (c)
  (declare (xargs :guard (true-listp c)))
  (if (< (fn-lgc-acked c) (fn-lgc-count c))
      (fn-lgc-make (fn-lgc-count c) (fn-lgc-last c) (fn-lgc-frontier c)
                   (fn-lgc-next-txid c) (fn-lgc-batch c) (fn-lgc-inflight c)
                   (1+ (fn-lgc-acked c)) (fn-lgc-phase c))
    c))

(defun fn-lgc-consume-to (c txid)
  (declare (xargs :guard (true-listp c)))
  (if (and (natp txid) (< (fn-lgc-next-txid c) txid))
      (fn-lgc-make (fn-lgc-count c) (fn-lgc-last c) (fn-lgc-frontier c)
                   txid (fn-lgc-batch c) (fn-lgc-inflight c)
                   (fn-lgc-acked c) (fn-lgc-phase c))
    c))

(defun fn-lgc-take (c record txid count octets bmax omax unit)
  (declare (xargs :guard (true-listp c)))
  (let ((entry (fn-olr-entry-octets (len record) unit)))
    (cond ((and (posp count)
                (or (<= (nfix bmax) count)
                    (< (nfix omax) (+ (nfix octets) entry))))
           (list :full c entry))
          ((and (natp txid) (equal txid (fn-lgc-next-txid c))
                (not (equal (fn-lgc-phase c) :fault)))
           (list :taken (fn-lgc-prepare c record) entry))
          (t (list :refused c entry)))))

; The segment rotation (books/store-log-segments.lisp; host fnn-log-rotate):
; admitted when nothing is open, in flight or unacknowledged; needed when the
; active segment holds a record; the new segment's kernel keeps the chain head
; and the txid.
(defun fn-lgc-rotate-admitsp (c)
  (declare (xargs :guard (true-listp c)))
  (and (atom (fn-lgc-batch c))
       (atom (fn-lgc-inflight c))
       (equal (fn-lgc-acked c) (fn-lgc-count c))
       (not (equal (fn-lgc-phase c) :fault))))

(defun fn-lgc-rotate-needed-p (c)
  (declare (xargs :guard (true-listp c)))
  (< 0 (fn-lgc-count c)))

(defun fn-lgc-rotate (c)
  (declare (xargs :guard (true-listp c)))
  (fn-lgc-make 0 (fn-lgc-last c) 0 (fn-lgc-next-txid c) nil nil 0 :ready))

; The open: the scan's records (the replay's input) and the concrete kernel.
(defun fn-lgc-open (s genesis unit max floor)
  (declare (xargs :guard (stringp s) :verify-guards nil))
  (mv-let (records consumed last) (fn-lg-decode s genesis unit max)
    (mv records
        (fn-lgc-make (len records) last (nfix consumed) (fn-lgt-next-after records floor)
                     nil nil (len records) :ready))))

; -----------------------------------------------------------------------------
; Refinement: each transition commutes with the abstraction.

(local (in-theory (disable fn-lg-log fn-lg-last-trailer fn-lg-decode
                            fn-lg-open-kernel-is-the-recovered-kernel)))

(local
 (defthm fn-lgc-len-true-list-fix
   (equal (len (true-list-fix x)) (len x))))

(local
 (defthm fn-lgc-len-append
   (equal (len (append a b)) (+ (len a) (len b)))))

(defthm fn-lgc-observers-of-abstraction
  (and (equal (fn-lgc-count (fn-lgc-of ks)) (len (fn-lgk-committed ks)))
       (equal (fn-lgc-last (fn-lgc-of ks)) (fn-lgk-last ks))
       (equal (fn-lgc-frontier (fn-lgc-of ks)) (fn-lgk-frontier ks))
       (equal (fn-lgc-next-txid (fn-lgc-of ks)) (fn-lgk-next-txid ks))
       (equal (fn-lgc-batch (fn-lgc-of ks)) (fn-lgk-batch ks))
       (equal (fn-lgc-inflight (fn-lgc-of ks)) (fn-lgk-inflight ks))
       (equal (fn-lgc-acked (fn-lgc-of ks)) (fn-lgk-acked ks))
       (equal (fn-lgc-phase (fn-lgc-of ks)) (fn-lgk-phase ks))))

(defthm fn-lgc-append-octets-of-abstraction
  (equal (fn-lgc-append-octets (fn-lgc-of ks) unit) (fn-lgk-append-octets ks unit)))

(defthm fn-lgc-fitsp-of-abstraction
  (equal (fn-lgc-fitsp (fn-lgc-of ks) unit extent) (fn-lgk-fitsp ks unit extent)))

(defthm fn-lgc-append-admitsp-of-abstraction
  (equal (fn-lgc-append-admitsp (fn-lgc-of ks) unit extent)
         (fn-lg-append-admitsp ks unit extent)))

(defthm fn-lgc-of-make
  (equal (fn-lgc-of (fn-lgk-make cm l f n b i a p))
         (fn-lgc-make (len cm) l (nfix f) (nfix n) b i (nfix a) p)))

(local
 (defthm fn-lgc-committed-of-lgk-make
   (equal (nth 1 (fn-lgk-make cm l f n b i a p)) cm)))

; The transitions below are proved at the field level: the abstraction and
; the constructors closed, the observers and fn-lgc-of-make rewriting.
(local (in-theory (disable fn-lgc-of fn-lgc-make fn-lgk-make fn-lgc-fitsp fn-lgk-fitsp
                           fn-lgc-append-admitsp fn-lg-append-admitsp)))

(defthm fn-lgc-prepare-refines
  (equal (fn-lgc-prepare (fn-lgc-of ks) record) (fn-lgc-of (fn-lgk-prepare ks record))))

(defthm fn-lgc-t-prepare-refines
  (equal (fn-lgc-t-prepare (fn-lgc-of ks) record) (fn-lgc-of (fn-lgt-prepare ks record)))
  :hints (("Goal" :in-theory (disable fn-lgc-prepare fn-lgk-prepare fn-lgc-of))))

(defthm fn-lgc-append-refines
  (equal (fn-lgc-append (fn-lgc-of ks) unit extent) (fn-lgc-of (fn-lgk-append ks unit extent))))

(defthm fn-lgc-fence-refines
  (equal (fn-lgc-fence (fn-lgc-of ks) unit) (fn-lgc-of (fn-lgk-fence ks unit))))

(defthm fn-lgc-fence-failed-refines
  (equal (fn-lgc-fence-failed (fn-lgc-of ks)) (fn-lgc-of (fn-lgk-fence-failed ks))))

(defthm fn-lgc-finish-one-refines
  (equal (fn-lgc-finish-one (fn-lgc-of ks)) (fn-lgc-of (fn-lgk-finish-one ks))))

(defthm fn-lgc-consume-to-refines
  (equal (fn-lgc-consume-to (fn-lgc-of ks) txid) (fn-lgc-of (fn-olr-consume-to ks txid))))

(defthm fn-lgc-take-refines
  (let ((a (fn-lgc-take (fn-lgc-of ks) record txid count octets bmax omax unit))
        (b (fn-olr-take ks record txid count octets bmax omax unit)))
    (and (equal (car a) (car b))
         (equal (cadr a) (fn-lgc-of (cadr b)))
         (equal (caddr a) (caddr b))))
  :hints (("Goal" :in-theory (disable fn-lgc-prepare fn-lgk-prepare fn-lgc-of fn-olr-entry-octets))))

(defthm fn-lgc-rotate-admitsp-of-abstraction
  (equal (fn-lgc-rotate-admitsp (fn-lgc-of ks)) (fn-lgs-rotate-admitsp ks)))

(local
 (defthm fn-lgc-positive-len-is-consp
   (equal (< 0 (len x)) (consp x))))

(defthm fn-lgc-rotate-needed-p-of-abstraction
  (equal (fn-lgc-rotate-needed-p (fn-lgc-of ks)) (fn-lgs-rotate-needed-p ks)))

(defthm fn-lgc-rotate-refines
  (equal (fn-lgc-rotate (fn-lgc-of ks)) (fn-lgc-of (fn-lgs-rotate ks))))

; Recovery's zeroing range read from the concrete kernel (host fnn-log-recover).
(defthm fn-lg-recover-tail-of-abstraction
  (equal (fn-lg-recover-tail (fn-lgc-of ks) extent) (fn-lg-recover-tail ks extent))
  :hints (("Goal" :in-theory (enable fn-lgc-of fn-lgc-make))))

(defthm fn-lgc-open-refines
  (mv-let (records c) (fn-lgc-open s genesis unit max floor)
    (and (equal records (fn-lgk-committed (fn-lg-open-kernel s genesis unit max floor)))
         (equal c (fn-lgc-of (fn-lg-open-kernel s genesis unit max floor))))))

(in-theory (disable fn-lgc-of fn-lgc-make fn-lgc-prepare fn-lgc-t-prepare fn-lgc-append
                    fn-lgc-fence fn-lgc-fence-failed fn-lgc-finish-one fn-lgc-consume-to
                    fn-lgc-take fn-lgc-open fn-lgc-append-octets fn-lgc-fitsp
                    fn-lgc-append-admitsp fn-lgc-rotate-admitsp fn-lgc-rotate-needed-p
                    fn-lgc-rotate))

; -----------------------------------------------------------------------------
; The keystone over any host run.  An operation is one of the host's calls:
;   (:prepare record) (:take record txid count octets bmax omax unit)
;   (:consume-to txid) (:append unit extent) (:fence unit) (:fence-failed)
;   (:finish-one) (:rotate)   -- the rotation only when admitted, as fnn-log-rotate

(defun fn-lgk-host-step (ks op)
  (declare (xargs :guard t :verify-guards nil))
  (case (car op)
      (:prepare (fn-lgt-prepare ks (nth 1 op)))
      (:take (cadr (fn-olr-take ks (nth 1 op) (nth 2 op) (nth 3 op) (nth 4 op)
                                (nth 5 op) (nth 6 op) (nth 7 op))))
      (:consume-to (fn-olr-consume-to ks (nth 1 op)))
      (:append (fn-lgk-append ks (nth 1 op) (nth 2 op)))
      (:fence (fn-lgk-fence ks (nth 1 op)))
      (:fence-failed (fn-lgk-fence-failed ks))
      (:finish-one (fn-lgk-finish-one ks))
      (:rotate (if (fn-lgs-rotate-admitsp ks) (fn-lgs-rotate ks) ks))
      (otherwise ks)))

(defun fn-lgc-host-step (c op)
  (declare (xargs :guard t :verify-guards nil))
  (case (car op)
      (:prepare (fn-lgc-t-prepare c (nth 1 op)))
      (:take (cadr (fn-lgc-take c (nth 1 op) (nth 2 op) (nth 3 op) (nth 4 op)
                                (nth 5 op) (nth 6 op) (nth 7 op))))
      (:consume-to (fn-lgc-consume-to c (nth 1 op)))
      (:append (fn-lgc-append c (nth 1 op) (nth 2 op)))
      (:fence (fn-lgc-fence c (nth 1 op)))
      (:fence-failed (fn-lgc-fence-failed c))
      (:finish-one (fn-lgc-finish-one c))
      (:rotate (if (fn-lgc-rotate-admitsp c) (fn-lgc-rotate c) c))
      (otherwise c)))

(defun fn-lgk-host-run (ks ops)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp ops) (fn-lgk-host-run (fn-lgk-host-step ks (car ops)) (cdr ops)) ks))

(defun fn-lgc-host-run (c ops)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp ops) (fn-lgc-host-run (fn-lgc-host-step c (car ops)) (cdr ops)) c))

(local
 (defthm fn-lgc-of-is-true-listp
   (true-listp (fn-lgc-of ks))
   :hints (("Goal" :in-theory (enable fn-lgc-of fn-lgc-make)))))

(local
 (defthm fn-lgc-host-step-refines
   (equal (fn-lgc-host-step (fn-lgc-of ks) op) (fn-lgc-of (fn-lgk-host-step ks op)))
   :hints (("Goal" :in-theory (disable fn-lgc-take-refines fn-lgk-prepare fn-lgt-prepare fn-olr-take
                                       fn-olr-consume-to fn-lgk-append fn-lgk-fence
                                       fn-lgk-fence-failed fn-lgk-finish-one
                                       fn-lgs-rotate fn-lgs-rotate-admitsp)
                   :use ((:instance fn-lgc-take-refines
                                    (record (nth 1 op)) (txid (nth 2 op)) (count (nth 3 op))
                                    (octets (nth 4 op)) (bmax (nth 5 op)) (omax (nth 6 op))
                                    (unit (nth 7 op))))))))

(defthm fn-lgc-host-run-refines
  (equal (fn-lgc-host-run (fn-lgc-of ks) ops) (fn-lgc-of (fn-lgk-host-run ks ops)))
  :hints (("Goal" :induct (fn-lgk-host-run ks ops)
                  :in-theory (disable fn-lgc-host-step fn-lgk-host-step))))

; KEYSTONE: from the open, the host's concrete kernel after any run of its
; operations is the abstraction of the logical kernel after the same run from
; the kernel the recovery program's theorem names.
(defthm fn-lgc-run-refines-the-kernel
  (equal (fn-lgc-host-run (mv-nth 1 (fn-lgc-open s genesis unit max floor)) ops)
         (fn-lgc-of (fn-lgk-host-run (fn-lgt-recover (fn-lgd-octets s) genesis unit max floor)
                                     ops)))
  :hints (("Goal" :in-theory (disable fn-lgc-host-run fn-lgk-host-run fn-lgc-open-refines
                                      fn-lg-open-kernel-is-the-recovered-kernel fn-lgt-recover
                                      fn-lg-open-kernel)
                  :use ((:instance fn-lgc-open-refines)
                        (:instance fn-lg-open-kernel-is-the-recovered-kernel)))))
