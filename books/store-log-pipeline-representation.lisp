; Shared logical/concrete primitives for the ONE pipeline dispatcher.
; No committed record list is installed by the native host. A logical kernel
; has a true-list COMMITTED; its existing fn-lgc-of projection has a count.
(in-package "ACL2")
(include-book "store-log-durable")
(local (in-theory (disable (tau-system))))

(defun fn-lgk-pipe-countedp (ks)
  (declare (xargs :guard (true-listp ks)))
  (natp (nth 1 ks)))
(defun fn-lgk-pipe-kernel-view (ks)
  (declare (xargs :guard (true-listp ks)))
  (if (fn-lgk-pipe-countedp ks) ks (fn-lgc-of ks)))
(defun fn-lgk-pipe-kernel-append (ks unit extent)
  (declare (xargs :guard (true-listp ks)))
  (if (fn-lgk-pipe-countedp ks)
      (fn-lgc-append ks unit extent) (ec-call (fn-lgk-append ks unit extent))))
(defun fn-lgk-pipe-kernel-fence (ks unit)
  (declare (xargs :guard (true-listp ks)))
  (if (fn-lgk-pipe-countedp ks)
      (fn-lgc-fence ks unit) (ec-call (fn-lgk-fence ks unit))))
(defun fn-lgk-pipe-kernel-fail (ks)
  (declare (xargs :guard (true-listp ks)))
  (if (fn-lgk-pipe-countedp ks)
      (fn-lgc-fence-failed ks) (fn-lgk-fence-failed ks)))
(defun fn-lgk-pipe-kernel-ack (ks n)
  (declare (xargs :guard (true-listp ks)))
  (if (fn-lgk-pipe-countedp ks)
      (fn-lgu-acknowledge ks (nfix n))
    (ec-call (fn-lgk-host-run ks (fn-lgu-finishes (nfix n))))))
(defun fn-lgk-pipe-kernel-take (ks record txid count octets bmax omax unit)
  (declare (xargs :guard (true-listp ks)))
  (if (fn-lgk-pipe-countedp ks)
      (fn-lgc-take ks record txid count octets bmax omax unit)
    (fn-olr-take ks record txid count octets bmax omax unit)))
(defun fn-lgk-pipe-kernel-consume (ks txid)
  (declare (xargs :guard (true-listp ks)))
  (if (fn-lgk-pipe-countedp ks)
      (fn-lgc-consume-to ks txid) (fn-olr-consume-to ks txid)))
(defun fn-lgk-pipe-kernel-octets (ks unit)
  (declare (xargs :guard (true-listp ks)))
  (fn-lgc-append-octets (fn-lgk-pipe-kernel-view ks) unit))
(defun fn-lgk-pipe-kernel-fitsp (ks unit extent)
  (declare (xargs :guard (true-listp ks)))
  (fn-lgc-fitsp (fn-lgk-pipe-kernel-view ks) unit extent))
(defun fn-lgk-pipe-kernel-count (ks)
  (declare (xargs :guard (true-listp ks)))
  (fn-lgc-count (fn-lgk-pipe-kernel-view ks)))
(defun fn-ocp-gc-history-extend (h records)
  (declare (xargs :guard (and (or (natp h) (true-listp h)) (true-listp records))))
  (if (natp h) (+ h (len records)) (append h records)))

(defthm fn-lgk-pipe-countedp-of-abstraction
  (fn-lgk-pipe-countedp (fn-lgc-of ks))
  :hints (("Goal" :in-theory (enable fn-lgc-of fn-lgc-make nth))))
(defthm fn-lgk-pipe-logical-is-not-counted
  (implies (true-listp (fn-lgk-committed ks))
           (not (fn-lgk-pipe-countedp ks)))
  :hints (("Goal" :in-theory (enable fn-lgk-committed true-listp))))
(defthm fn-lgk-pipe-kernel-view-of-abstraction
  (equal (fn-lgk-pipe-kernel-view (fn-lgc-of ks)) (fn-lgc-of ks)))
(defthm fn-lgk-pipe-kernel-view-of-logical
  (implies (true-listp (fn-lgk-committed ks))
           (equal (fn-lgk-pipe-kernel-view ks) (fn-lgc-of ks))))
(defthm fn-lgk-pipe-kernel-append-of-logical
  (implies (true-listp (fn-lgk-committed ks))
           (equal (fn-lgk-pipe-kernel-append ks unit extent) (fn-lgk-append ks unit extent)))
  :hints (("Goal" :in-theory (disable fn-lgk-append fn-lgc-append))))
(defthm fn-lgk-pipe-kernel-append-refines
  (implies (true-listp (fn-lgk-committed ks))
    (equal (fn-lgk-pipe-kernel-append (fn-lgc-of ks) unit extent)
           (fn-lgc-of (fn-lgk-pipe-kernel-append ks unit extent))))
  :hints (("Goal" :in-theory (disable fn-lgk-append fn-lgc-append fn-lgc-of))))
(defthm fn-lgk-pipe-kernel-fence-of-logical
  (implies (true-listp (fn-lgk-committed ks))
           (equal (fn-lgk-pipe-kernel-fence ks unit) (fn-lgk-fence ks unit)))
  :hints (("Goal" :in-theory (disable fn-lgk-fence fn-lgc-fence))))
(defthm fn-lgk-pipe-kernel-fence-refines
  (implies (true-listp (fn-lgk-committed ks))
    (equal (fn-lgk-pipe-kernel-fence (fn-lgc-of ks) unit)
           (fn-lgc-of (fn-lgk-pipe-kernel-fence ks unit))))
  :hints (("Goal" :in-theory (disable fn-lgk-fence fn-lgc-fence fn-lgc-of))))
(defthm fn-lgk-pipe-kernel-fail-of-logical
  (implies (true-listp (fn-lgk-committed ks))
           (equal (fn-lgk-pipe-kernel-fail ks) (fn-lgk-fence-failed ks)))
  :hints (("Goal" :in-theory (disable fn-lgk-fence-failed fn-lgc-fence-failed))))
(defthm fn-lgk-pipe-kernel-fail-refines
  (implies (true-listp (fn-lgk-committed ks))
    (equal (fn-lgk-pipe-kernel-fail (fn-lgc-of ks))
           (fn-lgc-of (fn-lgk-pipe-kernel-fail ks))))
  :hints (("Goal" :in-theory (disable fn-lgk-fence-failed fn-lgc-fence-failed fn-lgc-of))))
(defthm fn-lgk-pipe-kernel-ack-refines
  (implies (true-listp (fn-lgk-committed ks))
    (equal (fn-lgk-pipe-kernel-ack (fn-lgc-of ks) n)
           (fn-lgc-of (fn-lgk-pipe-kernel-ack ks n))))
  :hints (("Goal" :in-theory (e/d (fn-lgu-acknowledge)
                            (fn-lgk-host-run fn-lgc-host-run fn-lgu-finishes fn-lgc-of)))))
(defthm fn-lgk-pipe-kernel-ack-of-logical
  (implies (true-listp (fn-lgk-committed ks))
    (equal (fn-lgk-pipe-kernel-ack ks n)
           (fn-lgk-host-run ks (fn-lgu-finishes (nfix n)))))
  :hints (("Goal" :in-theory (disable fn-lgk-host-run fn-lgu-finishes fn-lgu-acknowledge))))
(defthm fn-lgk-pipe-kernel-take-of-logical
  (implies (true-listp (fn-lgk-committed ks))
    (equal (fn-lgk-pipe-kernel-take ks record txid count octets bmax omax unit)
           (fn-olr-take ks record txid count octets bmax omax unit)))
  :hints (("Goal" :in-theory (disable fn-olr-take fn-lgc-take))))
(defthm fn-lgk-pipe-kernel-take-refines
  (implies (true-listp (fn-lgk-committed ks))
    (let ((a (fn-lgk-pipe-kernel-take (fn-lgc-of ks) record txid count octets bmax omax unit))
          (b (fn-lgk-pipe-kernel-take ks record txid count octets bmax omax unit)))
      (and (equal (car a) (car b))
           (equal (cadr a) (fn-lgc-of (cadr b)))
           (equal (caddr a) (caddr b)))))
  :hints (("Goal" :use fn-lgc-take-refines
           :in-theory (disable fn-lgc-of fn-lgc-take fn-olr-take))))
(defthm fn-lgk-pipe-kernel-octets-of-logical
  (implies (true-listp (fn-lgk-committed ks))
    (equal (fn-lgk-pipe-kernel-octets ks unit) (fn-lgk-append-octets ks unit)))
  :hints (("Goal" :in-theory (disable fn-lgc-append-octets fn-lgk-append-octets fn-lgc-of))))
(defthm fn-lgk-pipe-kernel-fitsp-of-logical
  (implies (true-listp (fn-lgk-committed ks))
    (equal (fn-lgk-pipe-kernel-fitsp ks unit extent) (fn-lgk-fitsp ks unit extent)))
  :hints (("Goal" :in-theory (disable fn-lgc-fitsp fn-lgk-fitsp fn-lgc-of))))
(defthm fn-lgk-pipe-kernel-count-of-logical
  (implies (true-listp (fn-lgk-committed ks))
    (equal (fn-lgk-pipe-kernel-count ks) (len (fn-lgk-committed ks))))
  :hints (("Goal" :in-theory (disable fn-lgc-of fn-lgc-count))))
(defthm fn-ocp-gc-history-extend-refines
  (implies (true-listp h)
    (equal (fn-ocp-gc-history-extend (len h) records)
           (len (fn-ocp-gc-history-extend h records)))))

(defthm fn-lgk-pipe-kernel-fail-fields
  (let ((q (fn-lgk-pipe-kernel-fail ks)))
    (and (equal (fn-lgk-pipe-kernel-count q) (fn-lgk-pipe-kernel-count ks))
         (equal (fn-lgk-acked q) (fn-lgk-acked ks))
         (equal (fn-lgk-batch q) (fn-lgk-batch ks))
         (equal (fn-lgk-inflight q) (fn-lgk-inflight ks))
         (equal (fn-lgk-phase q) :fault)))
  :hints (("Goal" :in-theory
           (enable fn-lgk-pipe-kernel-fail fn-lgk-pipe-kernel-count
                   fn-lgk-pipe-kernel-view fn-lgk-pipe-countedp
                   fn-lgc-fence-failed fn-lgk-fence-failed fn-lgc-of
                   fn-lgc-make fn-lgk-make fn-lgc-count fn-lgk-committed
                   fn-lgk-acked fn-lgk-batch fn-lgk-inflight fn-lgk-phase nth))))

(local
 (defun fn-lgk-pipe-finish-shape-ind (ks n)
   (if (zp n) ks (fn-lgk-pipe-finish-shape-ind (fn-lgk-finish-one ks) (1- n)))))
(local
 (defthm fn-lgk-pipe-finishes-keep-committed
   (equal (fn-lgk-committed (fn-lgk-host-run ks (fn-lgu-finishes n)))
          (fn-lgk-committed ks))
   :hints (("Goal" :induct (fn-lgk-pipe-finish-shape-ind ks n)
            :in-theory (enable fn-lgk-host-run fn-lgk-host-step fn-lgu-finishes
                               fn-lgk-finish-one fn-lgk-committed fn-lgk-make nth)))))
(local
 (defthm fn-lgk-pipe-concrete-finishes-keep-countedp
   (implies (fn-lgk-pipe-countedp ks)
     (fn-lgk-pipe-countedp (fn-lgc-host-run ks (fn-lgu-finishes n))))
   :hints (("Goal" :induct (fn-lgu-acknowledge-loop ks n)
            :in-theory (e/d (fn-lgc-host-run fn-lgc-host-step fn-lgu-finishes
                              fn-lgc-finish-one fn-lgc-make fn-lgc-count
                              fn-lgk-pipe-countedp nth)
                             (fn-lgu-acknowledge-loop-is-the-run))))))
(local
 (defthm fn-lgk-pipe-logical-finishes-keep-countedp
   (equal (fn-lgk-pipe-countedp (fn-lgk-host-run ks (fn-lgu-finishes n)))
          (fn-lgk-pipe-countedp ks))
   :hints (("Goal" :use fn-lgk-pipe-finishes-keep-committed
            :in-theory (e/d (fn-lgk-pipe-countedp fn-lgk-committed)
                             (fn-lgk-host-run fn-lgu-finishes
                              fn-lgk-pipe-finishes-keep-committed))))))
(defthm fn-lgk-pipe-kernel-ack-view
  (equal (fn-lgk-pipe-kernel-view (fn-lgk-pipe-kernel-ack ks n))
         (fn-lgu-acknowledge (fn-lgk-pipe-kernel-view ks) (nfix n)))
  :hints (("Goal" :cases ((fn-lgk-pipe-countedp ks))
           :in-theory (e/d (fn-lgk-pipe-kernel-view fn-lgk-pipe-kernel-ack
                             fn-lgu-acknowledge)
                            (fn-lgk-pipe-countedp fn-lgk-host-run fn-lgc-host-run
                             fn-lgu-finishes fn-lgc-of (:executable-counterpart fn-lgu-finishes))))))

(defthm fn-lgk-pipe-kernel-octets-is-the-kernel-plan
  (equal (fn-lgk-pipe-kernel-octets ks unit) (fn-lgk-append-octets ks unit))
  :hints (("Goal" :in-theory
           (e/d (fn-lgk-pipe-kernel-octets fn-lgk-pipe-kernel-view
                  fn-lgc-append-octets fn-lgk-append-octets fn-lgc-batch
                  fn-lgc-last fn-lgk-batch fn-lgk-last)
                (fn-lgc-of fn-lg-log fn-lgc-log-octets)))))
