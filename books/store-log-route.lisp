; fn: the store's commit through the record log, store level (lane
; commit-onto-log, 2026-09-27; planning/design-2026-09-27-storage-log.md
; sections 3.3 and 9; w6-log-owner's PKT-698).  The owner level is
; books/owner-log-route.lisp; this book is what every image (the developer
; store, the DTN node and the owner) needs: the file kernel's two composite
; transitions over the store node, the log's layout, the take and the
; allocation catch-up.  See books/owner-log-route.lisp for the argument.
(in-package "ACL2")
(include-book "records-concrete")
(include-book "store-log-programs")

; -----------------------------------------------------------------------------
; The store node (the developer store bridge: host/store-node-host.lisp
; fn-store-sn-io's :log-reserve and :log-order arms).

(defun fn-olr-sn-reserve (s)
  (declare (xargs :guard (fn-sn-statep s) :verify-guards nil))
  (fn-rcon-sn-io
   (fn-rcon-sn-io
    (fn-rcon-sn-io (fn-rcon-sn-io s :start-frontier nil) :frontier-file :ok)
    :frontier-replace :ok)
   :frontier-directory :ok))

(defun fn-olr-sn-order (s)
  (declare (xargs :guard (fn-sn-statep s) :verify-guards nil))
  (fn-rcon-sn-io
   (fn-rcon-sn-io (fn-rcon-sn-io s :record-file :ok) :record-link :ok)
   :record-directory :ok))

(defthm fn-olr-sn-reserve-is-the-file-route-by-definition
  (equal (fn-olr-sn-reserve s)
         (fn-sn-io
          (fn-sn-io (fn-sn-io (fn-sn-io s :start-frontier nil) :frontier-file :ok)
                    :frontier-replace :ok)
          :frontier-directory :ok)))

(defthm fn-olr-sn-order-is-the-file-route-by-definition
  (equal (fn-olr-sn-order s)
         (fn-sn-io (fn-sn-io (fn-sn-io s :record-file :ok) :record-link :ok)
                   :record-directory :ok)))

; -----------------------------------------------------------------------------
; The log's layout and the batch's close rule, as the host reads them
; (host/store-host.lisp fn-store-log-*; host/native/io.lisp fnn-log-*).

; The one segment of a format-9 store (journal/NAME); rotation is lane
; w6-log-recovery's (PKT-750).
(defun fn-olr-segment-name ()
  (declare (xargs :guard t))
  "000001.log")

; The write unit: every batch starts on a unit boundary, so an append never
; shares a unit with committed octets (A-WRITE-ISOLATION at the layout,
; design 3.2).  4096 is a multiple of every sector size the qualification
; profile admits (512 and 4096).
(defconst *fn-olr-unit* 4096)
(defun fn-olr-unit ()
  (declare (xargs :guard t))
  *fn-olr-unit*)

; A new segment's extent (init): 256 units.
(defun fn-olr-initial-extent ()
  (declare (xargs :guard t))
  (* 256 *fn-olr-unit*))

; An entry's octets for a record of N octets: the FNLG frame (header, the
; 32-octet chain, the record, the 32-octet trailer) padded to the unit.  No
; digest is computed to know it (`fn-olr-entry-octets-is-the-entry-length').
(defun fn-olr-entry-octets (n unit)
  (declare (xargs :guard t))
  (let ((f (+ *fn-frame-overhead-octets* *fn-frame-trailer-octets* (nfix n))))
    (+ f (fn-lg-pad-len f unit))))

; The next extent when the open batch does not fit: at least twice the
; current one and at least NEED rounded up to the unit.  Growth is by
; doubling, so the number of extensions is logarithmic in the log's size.
(defun fn-olr-next-extent (extent need unit)
  (declare (xargs :guard t))
  (let* ((unit (if (posp unit) unit 1))
         (need (nfix need))
         (rounded (* unit (ceiling need unit))))
    (max (max (* 2 (nfix extent)) rounded) unit)))

; Every txid the owner consumed since the kernel's last record (a refused
; reservation or a known abort consumes one in the file kernel,
; fn-sf-refuse-reservation / fn-sn-known-abort) is consumed by the log
; kernel before the next reservation: NEXT-TXID rises to TXID, never falls.
(defun fn-olr-consume-to (ks txid)
  (declare (xargs :guard (true-listp ks)))
  (if (and (natp txid) (< (fn-lgk-next-txid ks) txid))
      (fn-lgk-make (fn-lgk-committed ks) (fn-lgk-last ks) (fn-lgk-frontier ks)
                   txid (fn-lgk-batch ks) (fn-lgk-inflight ks)
                   (fn-lgk-acked ks) (fn-lgk-phase ks))
    ks))

; The take of one prepared record into the open batch: :full when the batch
; already holds BMAX records or the entry would pass OMAX octets (the host
; commits the open batch, then takes again); :taken when the log kernel
; admits the record at its next txid (fn-lgt-prepare: T5's allocation rule);
; :refused otherwise (a core fault: the owner stamped another txid).  COUNT
; and OCTETS are the open batch's, which the host accumulates from the
; answers of this function (the octets are fn-olr-entry-octets').
(defun fn-olr-take (ks record count octets bmax omax unit)
  (declare (xargs :guard (true-listp ks)))
  (let ((entry (fn-olr-entry-octets (len record) unit)))
    (cond ((and (posp count)
                (or (<= (nfix bmax) count)
                    (< (nfix omax) (+ (nfix octets) entry))))
           (list :full ks entry))
          (t (let ((next (fn-lgt-prepare ks record)))
               (if (equal next ks)
                   (list :refused ks entry)
                 (list :taken next entry)))))))

; =============================================================================
; What the host's take, catch-up and extension keep.

; The octets the host accumulates for the open batch are the entries' own:
; an entry's length is fn-olr-entry-octets of its record's length.
(defthm fn-olr-entry-octets-is-the-entry-length
  (implies (and (fn-frame-digestp prev) (fn-cbor-octet-listp record))
           (equal (len (fn-lg-entry prev record unit))
                  (fn-olr-entry-octets (len record) unit)))
  :hints (("Goal" :in-theory (disable fn-lg-entry fn-lg-frame fn-lg-pad-len))))

; The take: :taken is the log kernel's checked prepare (T5's allocation rule,
; fn-lgt-prepare), and anything else leaves the kernel as it was.
(defthm fn-olr-take-is-the-checked-prepare
  (let ((answer (fn-olr-take ks record count octets bmax omax unit)))
    (and (equal (cadr answer)
                (if (equal (car answer) :taken) (fn-lgt-prepare ks record) ks))
         (equal (caddr answer) (fn-olr-entry-octets (len record) unit))))
  :hints (("Goal" :in-theory (disable fn-lgt-prepare fn-olr-entry-octets))))

; The close rule: a record joins a non-empty batch only below BMAX members
; and within OMAX octets of entries.
(defthm fn-olr-take-keeps-the-bounds
  (implies (and (equal (car (fn-olr-take ks record count octets bmax omax unit)) :taken)
                (posp count))
           (and (< count (nfix bmax))
                (<= (+ (nfix octets) (fn-olr-entry-octets (len record) unit))
                    (nfix omax))))
  :hints (("Goal" :in-theory (disable fn-lgt-prepare fn-olr-entry-octets))))

; T5's invariant and the log's relation R are kept by the take and by the
; catch-up to the owner's allocation.
(defthm fn-olr-take-preserves-okp
  (implies (fn-lgt-okp ks)
           (fn-lgt-okp (cadr (fn-olr-take ks record count octets bmax omax unit))))
  :hints (("Goal" :in-theory (disable fn-lgt-prepare fn-lgt-okp fn-olr-entry-octets))))

(defthm fn-olr-take-preserves-relation
  (implies (and (fn-lgk-relp bs ks ino genesis max) (fn-lg-recordp record max))
           (fn-lgk-relp bs (cadr (fn-olr-take ks record count octets bmax omax unit))
                        ino genesis max))
  :hints (("Goal" :in-theory (disable fn-lgt-prepare fn-lgk-relp fn-lg-recordp
                                      fn-olr-entry-octets))))

(defthm fn-olr-consume-to-preserves-okp
  (implies (fn-lgt-okp ks) (fn-lgt-okp (fn-olr-consume-to ks txid)))
  :hints (("Goal" :in-theory (enable fn-lgt-okp))))

(defthm fn-olr-consume-to-preserves-relation
  (implies (fn-lgk-relp bs ks ino genesis max)
           (fn-lgk-relp bs (fn-olr-consume-to ks txid) ino genesis max))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-lgk-relp-when-fields-agree
                            (k2 (fn-olr-consume-to ks txid)))
                 (:instance fn-lgk-relp-forward))
           :in-theory (e/d (fn-olr-consume-to)
                           (fn-lgk-relp fn-lg-recordsp)))))

; The consumed txids are never handed out again by the log: after the
; catch-up the kernel's next txid is at least TXID.
(defthm fn-olr-consume-to-reaches-the-owner
  (implies (natp txid)
           (<= txid (fn-lgk-next-txid (fn-olr-consume-to ks txid))))
  :rule-classes :linear)

; =============================================================================
; The refinement: a crash of the log reads a prefix of the sequential history.
;
; On the log route the store node's history (the records the file kernel
; holds, in order, as the host hands them to the log: fn-owner-pending-octets
; of each staged record, taken just before its :log-order step,
; host/native/io.lisp fnn-log-publish) runs AHEAD of the log's durable content
; inside a commit quantum.  The link: the log kernel's committed ++ in flight
; ++ open batch IS that history.  Recovery establishes it (the history is the
; scan's committed records, nothing in flight), the member step, the append,
; the barrier, the acknowledgement and the catch-up keep it; and under it
; every crash image of the segment reads a prefix of the history that
; extends the committed records: the state of the sequential machine after
; some member of the batch (T2 through fn-lgk-crash-of-related-state-is-a-
; prefix; the forgery disjunct is A-CRYPTO-TRAILER's, as there).  A member is
; answered only after the barrier (fn-lgk-finish-one, and the host releases
; its reply after log-fenced), so an acknowledged member is below every such
; prefix (T1).

(defun fn-olr-linkp (history ks)
  (declare (xargs :guard (true-listp ks)))
  (equal (append (true-list-fix (fn-lgk-committed ks))
                 (true-list-fix (fn-lgk-inflight ks))
                 (true-list-fix (fn-lgk-batch ks)))
         history))

(local
 (defthm fn-olr-append-assoc
   (equal (append (append a b) c) (append a (append b c)))))

(local
 (defthm fn-olr-true-list-fix-append
   (equal (true-list-fix (append a b)) (append a (true-list-fix b)))))

(local
 (defthm fn-olr-append-nil
   (equal (append a nil) (true-list-fix a))))

(defthm fn-olr-linkp-of-recovery
  (fn-olr-linkp (true-list-fix (car (fn-lg-scan c genesis unit max)))
                (fn-lgk-recover c genesis unit max next-txid))
  :hints (("Goal" :in-theory (enable fn-lgk-recover))))

(defthm fn-olr-linkp-of-take
  (implies (and (fn-olr-linkp history ks)
                (equal (car (fn-olr-take ks record count octets bmax omax unit)) :taken))
           (fn-olr-linkp (append history (list record))
                         (cadr (fn-olr-take ks record count octets bmax omax unit))))
  :hints (("Goal" :in-theory (enable fn-lgt-prepare fn-lgk-prepare))))

(defthm fn-olr-linkp-of-append
  (implies (and (fn-olr-linkp history ks) (not (consp (fn-lgk-inflight ks))))
           (fn-olr-linkp history (fn-lgk-append ks unit extent)))
  :hints (("Goal" :in-theory (e/d (fn-lgk-append) (fn-lgk-fitsp)))))

(defthm fn-olr-linkp-of-fence
  (implies (fn-olr-linkp history ks)
           (fn-olr-linkp history (fn-lgk-fence ks unit)))
  :hints (("Goal" :in-theory (enable fn-lgk-fence))))

(defthm fn-olr-linkp-of-finish-one
  (implies (fn-olr-linkp history ks)
           (fn-olr-linkp history (fn-lgk-finish-one ks)))
  :hints (("Goal" :in-theory (enable fn-lgk-finish-one))))

(defthm fn-olr-linkp-of-consume-to
  (implies (fn-olr-linkp history ks)
           (fn-olr-linkp history (fn-olr-consume-to ks txid))))

(local
 (defthm fn-olr-prefixp-of-append-prefix
   (implies (fn-lg-prefixp p b)
            (fn-lg-prefixp (append a p) (append a b c)))
   :hints (("Goal" :induct (append a p)))))

(local
 (defthm fn-olr-prefixp-of-self-append
   (fn-lg-prefixp a (append a b))
   :hints (("Goal" :induct (append a b)))))

(local
 (defthm fn-olr-prefixp-true-list-fix
   (equal (fn-lg-prefixp p (true-list-fix b)) (fn-lg-prefixp p b))))

; KEYSTONE.  The subjects are the log kernel's transitions the host calls
; (host/native/io.lisp fnn-log-take -> fn-olr-take, fnn-log-append ->
; fn-lgk-append, fnn-log-fence -> fn-lgk-fence) over the state the link
; relates to the store node's history.  At any cut with a batch in flight,
; every admissible crash image's scan is a prefix of the history, and it
; extends the committed records; or the damaged entry is a forgery (the
; A-CRYPTO-TRAILER case of T2).
(defthm fn-olr-crash-reads-a-prefix-of-the-history
  (implies (and (fn-lgk-relp bs ks ino genesis max)
                (consp (fn-lgk-inflight ks))
                (fn-bs-crash-imagep bs image)
                (fn-olr-linkp history ks))
           (let* ((content (fn-bs-durable-content image ino))
                  (scan (fn-lg-scan content genesis (fn-bs-unit bs) max)))
             (or (and (fn-lg-prefixp (car scan) history)
                      (fn-lg-prefixp (fn-lgk-committed ks) (car scan)))
                 (fn-lg-forgery-in (nthcdr (fn-lgk-frontier ks) content)
                                   (fn-lgk-inflight ks) (fn-lgk-last ks)
                                   (fn-bs-unit bs) max))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-lgk-crash-of-related-state-is-a-prefix)
                 (:instance fn-lgk-relp-forward))
           :in-theory (e/d (fn-lg-crash-verdictp)
                           (fn-lgk-relp fn-lg-scan fn-lg-forgery-in
                            fn-bs-durable-content fn-lg-log)))))
