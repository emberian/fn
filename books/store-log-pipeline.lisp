; One frozen append behind the outstanding barrier; extends the existing kernel.
(in-package "ACL2")
(include-book "store-log-pipeline-representation")
(local (in-theory
 (disable fn-lgk-pipe-countedp fn-lgk-pipe-kernel-view fn-lgk-pipe-kernel-count
          fn-lgk-pipe-kernel-append fn-lgk-pipe-kernel-fence fn-lgk-pipe-kernel-fail
          fn-lgk-pipe-kernel-ack fn-lgk-pipe-kernel-take fn-lgk-pipe-kernel-octets
          fn-lgk-pipe-kernel-fitsp)))

(defun fn-lgk-pipe-shapedp (p)
  (declare (xargs :guard t))
  (and (true-listp p) (true-listp (car p))))

; Extend the EXISTING kernel with one bit: BATCH has been appended behind
; INFLIGHT and is frozen. Do not duplicate its history, counters or codec.
; After the first fence BATCH stays pending; promotion uses fn-lgk-append
; as a logical move, with no second physical write if BEHIND was true.
(defun fn-lgk-pipe-make (ks behind)
  (declare (xargs :guard t :verify-guards nil)) (list ks (if behind t nil)))
(defun fn-lgk-pipe-ks (p)
  (declare (xargs :guard (true-listp p) :verify-guards nil)) (nth 0 p))
(defun fn-lgk-pipe-behind (p)
  (declare (xargs :guard (true-listp p) :verify-guards nil)) (nth 1 p))
(defun fn-lgk-pipe-d (p)
  (declare (xargs :guard (fn-lgk-pipe-shapedp p) :verify-guards nil)) (fn-lgk-pipe-kernel-count (fn-lgk-pipe-ks p)))
(defun fn-lgk-pipe-acked (p)
  (declare (xargs :guard (fn-lgk-pipe-shapedp p) :verify-guards nil)) (fn-lgk-acked (fn-lgk-pipe-ks p)))
(defun fn-lgk-pipe-okp (p h)
  (let ((ks (fn-lgk-pipe-ks p)))
    (and (true-listp p) (equal (len p) 2) (booleanp (fn-lgk-pipe-behind p))
         (true-listp ks) (true-listp h)
         (true-listp (fn-lgk-committed ks)) (true-listp (fn-lgk-inflight ks))
         (true-listp (fn-lgk-batch ks)) (fn-olr-linkp h ks)
         (fn-frame-digestp (fn-lgk-last ks))
         (<= (fn-lgk-acked ks) (len (fn-lgk-committed ks)))
         (implies (fn-lgk-pipe-behind p) (consp (fn-lgk-batch ks))))))

(defun fn-lgk-pipe-fence (p unit)
  (declare (xargs :guard (fn-lgk-pipe-shapedp p) :verify-guards nil))
  (let ((ks (fn-lgk-pipe-ks p)))
    (if (equal (fn-lgk-phase ks) :appended)
        (fn-lgk-pipe-make (fn-lgk-pipe-kernel-fence ks unit) (fn-lgk-pipe-behind p)) p)))

; The virtual fence computes the following offset/chain head using the
; existing codec. It does NOT install a durable kernel or acknowledge A.
; The returned write plan is for successful append receipt modeling; physical
; writing and its uncertain cuts need the new multi-write byte-store relation.
(defun fn-lgk-behind-write (p unit)
  (declare (xargs :guard (fn-lgk-pipe-shapedp p) :verify-guards nil))
  (let ((tail (fn-lgk-pipe-ks (fn-lgk-pipe-fence p unit))))
    (list :write (fn-lgk-frontier tail) (fn-lgk-pipe-kernel-octets tail unit))))
(defun fn-lgk-behind-admitsp (p unit extent)
  (declare (xargs :guard (fn-lgk-pipe-shapedp p) :verify-guards nil))
  (let ((ks (fn-lgk-pipe-ks p)))
    (and (not (fn-lgk-pipe-behind p)) (member-eq (fn-lgk-phase ks) '(:appended :fenced))
         (consp (fn-lgk-batch ks))
         (posp unit) (fn-lgk-pipe-kernel-fitsp
                      (fn-lgk-pipe-ks (fn-lgk-pipe-fence p unit)) unit extent))))
(defthm fn-lgk-behind-admitsp-positive-batch
  (implies (fn-lgk-behind-admitsp p unit extent)
           (posp (len (fn-lgk-batch (fn-lgk-pipe-ks p)))))
  :hints (("Goal" :in-theory (enable fn-lgk-behind-admitsp len))))
(defun fn-lgk-append-behind (p unit extent)
  (declare (xargs :guard (fn-lgk-pipe-shapedp p) :verify-guards nil))
  (if (fn-lgk-behind-admitsp p unit extent)
      (mv :appended (fn-lgk-pipe-make (fn-lgk-pipe-ks p) t)
          (fn-lgk-behind-write p unit))
    (mv :refused p nil)))
(defun fn-lgk-pipe-fail (p)
  (declare (xargs :guard (fn-lgk-pipe-shapedp p) :verify-guards nil))
  (fn-lgk-pipe-make (fn-lgk-pipe-kernel-fail (fn-lgk-pipe-ks p)) (fn-lgk-pipe-behind p)))
(defun fn-lgk-pipe-ack (p n)
  (declare (xargs :guard (fn-lgk-pipe-shapedp p) :verify-guards nil))
  (fn-lgk-pipe-make
   (fn-lgk-pipe-kernel-ack (fn-lgk-pipe-ks p) n)
   (fn-lgk-pipe-behind p)))
(defun fn-lgk-pipe-consume (p txid)
  (declare (xargs :guard (fn-lgk-pipe-shapedp p) :verify-guards nil))
  (fn-lgk-pipe-make (fn-lgk-pipe-kernel-consume (fn-lgk-pipe-ks p) txid)
                    (fn-lgk-pipe-behind p)))

; Proposed profile preflight counts ENCODED, padded log octets. The native
; profile must accommodate one maximal legal record. No arbitrary data cap.
(defun fn-olr-gc-profile-fitp (ks record bmax omax unit)
  (declare (xargs :guard (true-listp ks) :verify-guards nil))
  (and (posp bmax) (natp omax) (posp unit)
       (<= (fn-lgc-append-len
            (fn-lgc-prepare (fn-lgk-pipe-kernel-view ks) record) unit) omax)))
(defun fn-lgk-pipe-take (p record txid count octets bmax omax unit)
  (declare (xargs :guard (fn-lgk-pipe-shapedp p) :verify-guards nil))
  (let ((ks (fn-lgk-pipe-ks p)))
    (if (or (fn-lgk-pipe-behind p)
            (not (fn-olr-gc-profile-fitp ks record bmax omax unit)))
        (list :full p (fn-olr-entry-octets (len record) unit))
      (let ((a (fn-lgk-pipe-kernel-take ks record txid count octets bmax omax unit)))
        (list (car a) (fn-lgk-pipe-make (cadr a) nil) (caddr a))))))
; Pure bounded START/START-NEXT plan: all records must fit before the owner
; consumes this selected quantum. Work still left remains in its input queue.
(defun fn-olr-gc-prepare (p records bmax omax unit)
  (declare (xargs :guard (and (fn-lgk-pipe-shapedp p) (true-listp records)) :verify-guards nil :measure (len records)))
  (if (atom records) (mv t p)
    (let* ((ks (fn-lgk-pipe-ks p))
           (a (fn-lgk-pipe-take p (car records) (fn-lgk-next-txid ks)
                 (len (fn-lgk-batch ks)) (fn-lg-pack-len (fn-lgk-batch ks)) bmax omax unit)))
      (if (equal (car a) :taken)
          (fn-olr-gc-prepare (cadr a) (cdr records) bmax omax unit)
        (mv nil p)))))


(defun fn-lgk-behind-state (p unit extent)
  (declare (xargs :guard (fn-lgk-pipe-shapedp p) :verify-guards nil))
  (mv-let (word after effect) (fn-lgk-append-behind p unit extent)
    (declare (ignore word effect)) after))

(defun fn-lgk-behind-effect (p unit extent)
  (declare (xargs :guard (fn-lgk-pipe-shapedp p) :verify-guards nil))
  (mv-let (word after effect) (fn-lgk-append-behind p unit extent)
    (declare (ignore word after)) effect))

(local
 (defthm fn-lgk-pipe-shape-make
  (implies (true-listp ks) (fn-lgk-pipe-shapedp (fn-lgk-pipe-make ks b)))
  :hints (("Goal" :in-theory (enable fn-lgk-pipe-shapedp fn-lgk-pipe-make)))))
(local
 (defthm fn-lgk-pipe-shape-fields
  (implies (fn-lgk-pipe-shapedp p)
    (and (true-listp p) (true-listp (fn-lgk-pipe-ks p))))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-lgk-pipe-shapedp fn-lgk-pipe-ks)))))
(local
 (defthm fn-lgk-pipe-kernel-view-listp
  (implies (true-listp ks) (true-listp (fn-lgk-pipe-kernel-view ks)))
  :hints (("Goal" :in-theory (enable fn-lgk-pipe-kernel-view)))))
(local
 (defthm fn-lgk-pipe-kernel-steps-listp
  (implies (true-listp ks)
    (and (true-listp (fn-lgk-pipe-kernel-append ks unit extent))
         (true-listp (fn-lgk-pipe-kernel-fence ks unit))
         (true-listp (fn-lgk-pipe-kernel-consume ks txid))
         (true-listp (fn-lgk-pipe-kernel-fail ks))))
  :hints (("Goal" :in-theory
           (enable fn-lgk-pipe-kernel-append fn-lgk-pipe-kernel-fence
                   fn-lgk-pipe-kernel-consume fn-lgk-pipe-kernel-fail
                   fn-lgk-append fn-lgc-append fn-lgk-fence fn-lgc-fence
                   fn-lgk-fence-failed fn-lgc-fence-failed fn-olr-consume-to
                   fn-lgc-consume-to)))))
(local
 (defthm fn-lgk-pipe-fence-shapedp
  (implies (fn-lgk-pipe-shapedp p)
           (fn-lgk-pipe-shapedp (fn-lgk-pipe-fence p unit)))
  :hints (("Goal" :in-theory (enable fn-lgk-pipe-fence)))))

(verify-guards fn-lgk-pipe-make)
(verify-guards fn-lgk-pipe-ks)
(verify-guards fn-lgk-pipe-behind)
(verify-guards fn-lgk-pipe-d)
(verify-guards fn-lgk-pipe-acked)
(verify-guards fn-lgk-pipe-fence)
(verify-guards fn-lgk-behind-write)
(verify-guards fn-lgk-behind-admitsp)
(verify-guards fn-lgk-append-behind)
(verify-guards fn-lgk-behind-state)
(verify-guards fn-lgk-behind-effect)
(verify-guards fn-lgk-pipe-fail)
(verify-guards fn-lgk-pipe-ack)
(verify-guards fn-lgk-pipe-consume)
(verify-guards fn-olr-gc-profile-fitp)
(verify-guards fn-lgk-pipe-take)

(defthm fn-lgk-pipe-take-shapedp
  (implies (fn-lgk-pipe-shapedp p)
    (fn-lgk-pipe-shapedp (cadr (fn-lgk-pipe-take p record txid count octets bmax omax unit))))
  :hints (("Goal" :in-theory
           (e/d (fn-lgk-pipe-take fn-lgk-pipe-shapedp fn-lgk-pipe-kernel-take
                  fn-lgc-take fn-olr-take fn-lgk-prepare fn-lgc-prepare)
                (fn-olr-gc-profile-fitp fn-lgk-next-txid fn-lgc-next-txid
                 fn-lgk-phase fn-lgc-phase fn-olr-entry-octets nfix natp posp)))))
(defthm fn-olr-gc-prepare-shapedp
  (implies (fn-lgk-pipe-shapedp p)
           (fn-lgk-pipe-shapedp (mv-nth 1 (fn-olr-gc-prepare p records bmax omax unit))))
  :hints (("Goal" :induct (fn-olr-gc-prepare p records bmax omax unit)
           :in-theory (disable fn-lgk-pipe-take fn-lgk-pipe-shapedp))))
(verify-guards fn-olr-gc-prepare
  :hints (("Goal" :in-theory (disable fn-lgk-pipe-take fn-lgk-pipe-shapedp fn-lgk-pipe-ks))))

(defthm fn-lgk-append-behind-safe
  (implies (fn-lgk-pipe-okp p h)
    (let ((q (fn-lgk-behind-state p unit extent)))
      (and (fn-lgk-pipe-okp q h) (equal (fn-lgk-pipe-d q) (fn-lgk-pipe-d p))
           (<= (fn-lgk-pipe-acked q) (fn-lgk-pipe-d q)))))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (disable fn-lgk-fence fn-lgk-fitsp fn-lgk-behind-write fn-olr-linkp
                    fn-frame-digestp fn-lgk-committed fn-lgk-inflight fn-lgk-batch
                    fn-lgk-last fn-lgk-acked fn-lgk-phase))))

(local
 (defthm fn-lgk-pipe-nthcdr-at-append
   (equal (nthcdr (len a) (append a b)) b)
   :hints (("Goal" :induct (len a)
            :in-theory (disable fn-lgc-nthcdr-of-append-shorter)))))
(local
 (defthm fn-lgk-pipe-trailer-of-frame-digestp
   (fn-frame-digestp (fn-lg-trailer (fn-lg-frame prev chunk)))
   :hints (("Goal" :do-not-induct t
            :in-theory
            (e/d (fn-lg-trailer fn-lg-frame fn-frame-seal fn-frame-encode fn-frame-digestp)
                 (fn-frame-protected fn-lg-frame-body fn-lg-frame-kind fn-frame-digest
                  fn-lg-frame-len fn-lgc-nthcdr-of-append-shorter))))))
(local
 (defthm fn-lgk-pipe-last-trailer-digestp
   (implies (fn-frame-digestp prev)
            (fn-frame-digestp (fn-lg-last-trailer records prev)))
   :hints (("Goal" :induct (fn-lg-last-trailer records prev)
            :in-theory (disable fn-lg-frame fn-lg-trailer fn-lg-chunk-len fn-frame-digestp)))))
(local
 (defthm fn-lgk-pipe-fence-fields
   (and (equal (fn-lgk-committed (fn-lgk-fence ks unit))
               (append (true-list-fix (fn-lgk-committed ks))
                       (true-list-fix (fn-lgk-inflight ks))))
        (equal (fn-lgk-last (fn-lgk-fence ks unit))
               (fn-lg-last-trailer (fn-lgk-inflight ks) (fn-lgk-last ks)))
        (equal (fn-lgk-batch (fn-lgk-fence ks unit)) (fn-lgk-batch ks))
        (equal (fn-lgk-acked (fn-lgk-fence ks unit)) (fn-lgk-acked ks))
        (true-listp (fn-lgk-fence ks unit)))
   :hints (("Goal" :in-theory (disable fn-lg-log fn-lg-last-trailer)))))
(defthm fn-lgk-pipe-fence-safe
  (implies (fn-lgk-pipe-okp p h)
    (let ((q (fn-lgk-pipe-fence p unit)))
      (and (fn-lgk-pipe-okp q h) (<= (fn-lgk-pipe-d p) (fn-lgk-pipe-d q))
           (<= (fn-lgk-pipe-acked q) (fn-lgk-pipe-d q)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory
           (disable fn-lgk-fence fn-lgk-committed fn-lgk-inflight fn-lgk-last
                    fn-lgk-batch fn-lgk-acked fn-lgk-phase fn-lg-log
                    fn-lg-last-trailer fn-olr-linkp fn-frame-digestp))))

; Field lemmas used by the owner composition.
(local (in-theory (disable (tau-system) nth len true-listp update-nth
 fn-lgk-pipe-okp fn-lgk-pipe-ks fn-lgk-pipe-behind fn-lgk-pipe-d fn-lgk-pipe-acked
 fn-lgk-pipe-fence fn-lgk-pipe-fail fn-lgk-pipe-ack fn-lgk-behind-state
 fn-lgk-behind-effect fn-lgk-behind-admitsp fn-lgk-phase fn-lgk-batch fn-lgk-inflight
 fn-lgk-committed fn-lgk-acked fn-lgk-last fn-lgk-append fn-lgc-append-admitsp
 fn-olr-gc-prepare)))
(local
 (defthm fn-ocp-gc-list-constructors
  (and (equal (len (cons a b)) (+ 1 (len b)))
       (equal (true-listp (cons a b)) (true-listp b)))
  :hints (("Goal" :in-theory (enable len true-listp)))))

(defthm fn-lgk-pipe-fail-fields
  (let ((q (fn-lgk-pipe-fail p)))
    (and (equal (fn-lgk-pipe-d q) (fn-lgk-pipe-d p))
         (equal (fn-lgk-pipe-acked q) (fn-lgk-pipe-acked p))
         (equal (fn-lgk-pipe-behind q) (if (fn-lgk-pipe-behind p) t nil))
         (equal (fn-lgk-phase (fn-lgk-pipe-ks q)) :fault)
         (equal (fn-lgk-batch (fn-lgk-pipe-ks q)) (fn-lgk-batch (fn-lgk-pipe-ks p)))
         (equal (fn-lgk-inflight (fn-lgk-pipe-ks q)) (fn-lgk-inflight (fn-lgk-pipe-ks p)))))
  :hints (("Goal" :in-theory
           (enable fn-lgk-pipe-fail fn-lgk-pipe-d fn-lgk-pipe-acked
                   fn-lgk-pipe-behind fn-lgk-pipe-ks))))

(defthm fn-lgk-pipe-fail-preserves-okp
  (implies (fn-lgk-pipe-okp p h) (fn-lgk-pipe-okp (fn-lgk-pipe-fail p) h))
  :hints (("Goal" :in-theory
           (enable fn-lgk-pipe-okp fn-lgk-pipe-fail fn-lgk-pipe-ks fn-lgk-pipe-behind
                   fn-lgk-committed fn-lgk-inflight fn-lgk-batch fn-lgk-last
                   fn-lgk-acked fn-olr-linkp))))

(defthm fn-lgk-behind-state-fields
  (and (equal (fn-lgk-pipe-ks (fn-lgk-behind-state p unit extent)) (fn-lgk-pipe-ks p))
       (equal (fn-lgk-pipe-behind (fn-lgk-behind-state p unit extent))
              (if (fn-lgk-behind-admitsp p unit extent) t (fn-lgk-pipe-behind p))))
  :hints (("Goal" :in-theory
           (enable fn-lgk-behind-state fn-lgk-pipe-ks fn-lgk-pipe-behind))))

(local
 (defthm fn-lgk-pipe-fence-phase
  (equal (fn-lgk-phase (fn-lgk-fence ks unit)) :fenced)
  :hints (("Goal" :in-theory (enable fn-lgk-phase fn-lgk-fence)))))

(defthm fn-lgk-pipe-fence-linked-fields
  (implies (and (fn-lgk-pipe-okp p h)
                (equal (fn-lgk-phase (fn-lgk-pipe-ks p)) :appended))
    (let ((q (fn-lgk-pipe-fence p unit)))
      (and (fn-lgk-pipe-okp q h)
           (equal (fn-lgk-pipe-d q)
                  (+ (fn-lgk-pipe-d p) (len (fn-lgk-inflight (fn-lgk-pipe-ks p)))))
           (equal (fn-lgk-pipe-behind q) (fn-lgk-pipe-behind p))
           (equal (fn-lgk-phase (fn-lgk-pipe-ks q)) :fenced)
           (equal (fn-lgk-inflight (fn-lgk-pipe-ks q)) nil)
           (equal (fn-lgk-batch (fn-lgk-pipe-ks q)) (fn-lgk-batch (fn-lgk-pipe-ks p))))))
  :hints (("Goal" :use fn-lgk-pipe-fence-safe
           :in-theory (e/d (fn-lgk-pipe-fence fn-lgk-pipe-d fn-lgk-pipe-ks
                            fn-lgk-pipe-behind fn-lgk-pipe-okp)
                           (fn-lgk-fence fn-olr-linkp fn-frame-digestp)))))

(local
 (defun fn-lgk-pipe-ack-ind (n ks)
  (if (zp n) ks (fn-lgk-pipe-ack-ind (1- n) (fn-lgk-finish-one ks)))))

(local
 (defthm fn-lgk-pipe-finishes-fields
  (implies (and (true-listp ks)
                (<= (fn-lgk-acked ks) (len (fn-lgk-committed ks))))
    (let ((q (fn-lgk-host-run ks (fn-lgu-finishes n))))
      (and (true-listp q)
           (equal (fn-lgk-committed q) (fn-lgk-committed ks))
           (equal (fn-lgk-frontier q) (fn-lgk-frontier ks))
           (equal (fn-lgk-last q) (fn-lgk-last ks))
           (equal (fn-lgk-inflight q) (fn-lgk-inflight ks))
           (equal (fn-lgk-batch q) (fn-lgk-batch ks))
           (equal (fn-lgk-phase q) (fn-lgk-phase ks))
           (<= (fn-lgk-acked q) (len (fn-lgk-committed q))))))
  :hints (("Goal" :induct (fn-lgk-pipe-ack-ind n ks)
           :expand ((fn-lgu-finishes n) (fn-lgk-host-run ks nil)
                    (:free (op rest) (fn-lgk-host-run ks (cons op rest))))
           :in-theory (e/d (fn-lgk-host-step fn-lgk-finish-one fn-lgk-fields-of-make)
                           (fn-lgk-make fn-lgk-frontier fn-lgk-host-run fn-lgu-finishes))))))

(defthm fn-lgk-pipe-ack-linked-fields
  (implies (fn-lgk-pipe-okp p h)
    (let ((q (fn-lgk-pipe-ack p n)))
      (and (fn-lgk-pipe-okp q h)
           (equal (fn-lgk-pipe-d q) (fn-lgk-pipe-d p))
           (equal (fn-lgk-pipe-behind q) (fn-lgk-pipe-behind p))
           (equal (fn-lgk-committed (fn-lgk-pipe-ks q)) (fn-lgk-committed (fn-lgk-pipe-ks p)))
           (equal (fn-lgk-frontier (fn-lgk-pipe-ks q)) (fn-lgk-frontier (fn-lgk-pipe-ks p)))
           (equal (fn-lgk-phase (fn-lgk-pipe-ks q)) (fn-lgk-phase (fn-lgk-pipe-ks p)))
           (equal (fn-lgk-batch (fn-lgk-pipe-ks q)) (fn-lgk-batch (fn-lgk-pipe-ks p)))
           (equal (fn-lgk-inflight (fn-lgk-pipe-ks q)) (fn-lgk-inflight (fn-lgk-pipe-ks p))))))
  :hints (("Goal" :use ((:instance fn-lgk-pipe-finishes-fields
                                  (ks (fn-lgk-pipe-ks p)) (n (nfix n))))
           :expand ((:free (ks) (fn-lgk-host-run ks nil))) :in-theory
           (e/d (fn-lgk-pipe-okp fn-lgk-pipe-ack fn-lgk-pipe-ks
                  fn-lgk-pipe-behind fn-lgk-pipe-d fn-olr-linkp)
                (fn-lgk-host-run fn-lgu-finishes)))))

(defthm fn-lgk-pipe-consume-linked-fields
  (implies (fn-lgk-pipe-okp p h)
    (let ((q (fn-lgk-pipe-consume p txid)))
      (and (fn-lgk-pipe-okp q h)
           (equal (fn-lgk-pipe-d q) (fn-lgk-pipe-d p))
           (equal (fn-lgk-pipe-behind q) (fn-lgk-pipe-behind p))
           (equal (fn-lgk-phase (fn-lgk-pipe-ks q)) (fn-lgk-phase (fn-lgk-pipe-ks p)))
           (equal (fn-lgk-batch (fn-lgk-pipe-ks q)) (fn-lgk-batch (fn-lgk-pipe-ks p)))
           (equal (fn-lgk-inflight (fn-lgk-pipe-ks q)) (fn-lgk-inflight (fn-lgk-pipe-ks p))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-lgk-pipe-okp fn-lgk-pipe-consume
                              fn-lgk-pipe-kernel-consume fn-lgk-pipe-countedp
                              fn-olr-consume-to fn-lgk-pipe-ks fn-lgk-pipe-behind
                              fn-lgk-pipe-d fn-lgk-fields-of-make fn-olr-linkp)
                            (fn-lgk-make)))))

(defthm fn-lgk-pipe-promote-linked-fields
  (implies (and (fn-lgk-pipe-okp p h)
                (fn-lgc-append-admitsp (fn-lgc-of (fn-lgk-pipe-ks p)) unit extent))
    (let ((q (fn-lgk-pipe-make (fn-lgk-append (fn-lgk-pipe-ks p) unit extent) nil)))
      (and (fn-lgk-pipe-okp q h)
           (equal (fn-lgk-pipe-d q) (fn-lgk-pipe-d p))
           (equal (fn-lgk-phase (fn-lgk-pipe-ks q)) :appended)
           (equal (fn-lgk-inflight (fn-lgk-pipe-ks q)) (fn-lgk-batch (fn-lgk-pipe-ks p)))
           (equal (fn-lgk-batch (fn-lgk-pipe-ks q)) nil)
           (equal (fn-lgk-pipe-behind q) nil))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-olr-linkp-of-append (history h) (ks (fn-lgk-pipe-ks p))))
           :in-theory
           (e/d (fn-lgk-pipe-okp fn-lgk-pipe-d fn-lgk-pipe-ks fn-lgk-pipe-behind
                  fn-lgk-append fn-lg-append-admitsp fn-lgk-fields-of-make)
                (fn-lgk-make fn-lgk-fitsp fn-lgc-of fn-olr-linkp)))))

(defthm fn-lgk-pipe-take-linked-fields
  (implies (and (fn-lgk-pipe-okp p h)
                (equal (car (fn-lgk-pipe-take p record txid count octets bmax omax unit)) :taken))
    (let ((q (cadr (fn-lgk-pipe-take p record txid count octets bmax omax unit))))
      (and (fn-lgk-pipe-okp q (append h (list record)))
           (equal (fn-lgk-pipe-d q) (fn-lgk-pipe-d p))
           (equal (fn-lgk-pipe-behind q) (fn-lgk-pipe-behind p))
           (equal (fn-lgk-phase (fn-lgk-pipe-ks q)) (fn-lgk-phase (fn-lgk-pipe-ks p)))
           (equal (fn-lgk-inflight (fn-lgk-pipe-ks q)) (fn-lgk-inflight (fn-lgk-pipe-ks p)))
           (equal (fn-lgk-batch (fn-lgk-pipe-ks q))
                  (append (fn-lgk-batch (fn-lgk-pipe-ks p)) (list record))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-olr-linkp-of-take (history h) (ks (fn-lgk-pipe-ks p))))
           :in-theory
           (e/d (fn-lgk-pipe-take fn-lgk-pipe-okp fn-lgk-pipe-ks fn-lgk-pipe-d
                  fn-lgk-pipe-behind fn-olr-take fn-lgk-prepare fn-lgk-fields-of-make)
                (fn-lgk-make fn-olr-gc-profile-fitp fn-olr-linkp)))))

(local
 (defun fn-olr-gc-prepare-induct (p records h bmax omax unit)
  (declare (xargs :measure (acl2-count records)
                  :hints (("Goal" :in-theory (disable fn-lgk-pipe-take)))))
  (if (atom records) (list p h)
    (let* ((ks (fn-lgk-pipe-ks p))
           (a (fn-lgk-pipe-take p (car records) (fn-lgk-next-txid ks)
                 (len (fn-lgk-batch ks)) (fn-lg-pack-len (fn-lgk-batch ks)) bmax omax unit)))
      (if (equal (car a) :taken)
          (fn-olr-gc-prepare-induct (cadr a) (cdr records) (append h (list (car records))) bmax omax unit)
        (list p h))))))

(defthm fn-lgk-pipe-okp-forward
  (implies (fn-lgk-pipe-okp p h)
    (and (true-listp h) (true-listp (fn-lgk-pipe-ks p))
         (true-listp (fn-lgk-committed (fn-lgk-pipe-ks p)))
         (true-listp (fn-lgk-inflight (fn-lgk-pipe-ks p)))
         (true-listp (fn-lgk-batch (fn-lgk-pipe-ks p)))))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-lgk-pipe-okp))))

(defthm fn-olr-gc-prepare-linked-fields
  (implies (and (fn-lgk-pipe-okp p h) (true-listp records)
                (mv-nth 0 (fn-olr-gc-prepare p records bmax omax unit)))
    (let ((q (mv-nth 1 (fn-olr-gc-prepare p records bmax omax unit))))
      (and (fn-lgk-pipe-okp q (append h records))
           (equal (fn-lgk-pipe-d q) (fn-lgk-pipe-d p))
           (equal (fn-lgk-pipe-behind q) (fn-lgk-pipe-behind p))
           (equal (fn-lgk-phase (fn-lgk-pipe-ks q)) (fn-lgk-phase (fn-lgk-pipe-ks p)))
           (equal (fn-lgk-inflight (fn-lgk-pipe-ks q)) (fn-lgk-inflight (fn-lgk-pipe-ks p)))
           (equal (fn-lgk-batch (fn-lgk-pipe-ks q))
                  (append (fn-lgk-batch (fn-lgk-pipe-ks p)) records)))))
  :hints (("Goal" :induct (fn-olr-gc-prepare-induct p records h bmax omax unit)
           :expand ((fn-olr-gc-prepare p records bmax omax unit)
                    (fn-olr-gc-prepare p nil bmax omax unit))
           :in-theory (e/d (true-listp) (fn-lgk-pipe-take fn-lgk-next-txid fn-lg-pack-len)))))

(defthm fn-lgk-pipe-acked-bound
  (implies (fn-lgk-pipe-okp p h) (<= (fn-lgk-pipe-acked p) (fn-lgk-pipe-d p)))
  :hints (("Goal" :in-theory (enable fn-lgk-pipe-okp fn-lgk-pipe-acked fn-lgk-pipe-d))))
(local
 (defthm fn-olr-gc-empty-batch
   (implies (true-listp a) (equal (equal (len a) 0) (equal a nil)))
   :hints (("Goal" :in-theory (enable len true-listp)))))
(defun fn-olr-gc-membership-hyp (h p record txid count octets bmax omax unit)
  (let ((ks (fn-lgk-pipe-ks p)))
    (and (fn-lgk-pipe-okp p h)
         (equal count (len (fn-lgk-batch ks)))
         (equal octets (fn-lg-pack-len (fn-lgk-batch ks)))
         (equal (car (fn-lgk-pipe-take p record txid count octets bmax omax unit)) :taken))))

(defun fn-olr-gc-membership-okp (h p record txid count octets bmax omax unit)
  (let* ((ks (fn-lgk-pipe-ks p))
         (after (fn-lgk-pipe-ks (cadr (fn-lgk-pipe-take p record txid count octets bmax omax unit))))
         (d (len (fn-lgk-committed ks))) (seal (+ d (len (fn-lgk-inflight ks))))
         (h2 (append h (list record))))
    (and (equal (fn-lgk-inflight after) (fn-lgk-inflight ks))
         (equal (fn-lgk-batch after) (nthcdr seal h2))
         (equal (append (fn-lgk-inflight after) (fn-lgk-batch after)) (nthcdr d h2))
         (<= (len (fn-lgk-batch after)) bmax)
         (<= (fn-lgc-append-len (fn-lgc-of after) unit) omax))))

(defthm fn-olr-gc-membership-and-profile-bounds
  (implies (fn-olr-gc-membership-hyp h p record txid count octets bmax omax unit)
           (fn-olr-gc-membership-okp h p record txid count octets bmax omax unit))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory
           (e/d (fn-olr-gc-membership-hyp fn-olr-gc-membership-okp fn-lgk-pipe-take
                  fn-olr-take fn-olr-gc-profile-fitp fn-lgk-pipe-ks fn-lgk-pipe-make
                  fn-lgk-prepare fn-lgk-fields-of-make fn-lgk-pipe-okp fn-olr-linkp
                  fn-lgc-append-len fn-lgc-batch fn-lgc-last fn-lgc-make)
                (fn-lgc-of fn-lgk-make)))))

(defthm fn-lgk-pipe-ack-refines-host-call
  (equal (fn-lgk-pipe-kernel-view (fn-lgk-pipe-ks (fn-lgk-pipe-ack p n)))
         (fn-lgu-acknowledge (fn-lgk-pipe-kernel-view (fn-lgk-pipe-ks p)) (nfix n)))
  :hints (("Goal" :in-theory
           (e/d (fn-lgk-pipe-ack fn-lgk-pipe-ks fn-lgu-acknowledge)
                (fn-lgk-pipe-kernel-view fn-lgk-host-run fn-lgc-host-run fn-lgu-finishes)))))

(defthm fn-lgk-behind-promotion-keeps-write-plan
  (implies (fn-lgk-behind-admitsp p unit extent)
    (equal (fn-lgk-behind-effect p unit extent)
           (let ((ks (fn-lgk-pipe-ks (fn-lgk-pipe-fence p unit))))
             (list :write (fn-lgk-frontier ks) (fn-lgk-append-octets ks unit)))))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (e/d (fn-lgk-behind-effect fn-lgk-append-behind fn-lgk-pipe-fence
                  fn-lgk-behind-admitsp fn-lgk-behind-write fn-lgk-pipe-ks)
                (fn-lgk-fence fn-lgk-fitsp fn-lgk-append-octets)))))
