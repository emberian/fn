; fn: the store node's commit through the record log (lane commit-onto-log,
; 2026-09-27; planning/design-2026-09-27-storage-log.md sections 3.3 and 9;
; w6-log-owner's PKT-698).
;
; A format-9 store (books/byte-store-frame.lisp `fn-bs-profile-logp') has no
; allocation-frontier file, no transactions/ directory and no marker: its
; commit is one entry in the record log (books/store-log*.lisp), made durable
; by the log's one barrier per batch.  The store node's file kernel
; (books/store-files.lisp) keeps its phases; on this route two of its phase
; sequences are single transitions whose durability the LOG carries:
;
;   RESERVE  :ready -> :reserved.  The file route reaches it by the frontier
;            program's three observations (stage fenced, replaced, root
;            fenced).  The log route has no frontier object: the allocation
;            is derived (the next txid is one past the log's largest, design
;            3.3), so the reservation is the kernel's step with every
;            observation of that program a success.
;   ORDER    :record-staged -> :completing.  The file route reaches it by the
;            record program's three observations (stage fenced, linked,
;            transactions/ fenced).  On the log route the record has taken its
;            place in the log's order (the log kernel's batch, fn-owb-take);
;            the ENTRY's durability is the batch's barrier (fn-lgk-fence), and
;            no reply, feed resolution or read leaves the owner before it
;            (host/native/owner.lisp: the batch runs in one owner quantum and
;            its replies are released after `log-fenced').
;
; Each is DEFINED as the file route's success sequence, so every invariant
; the file kernel's transitions carry is carried here by composition, and the
; outcome of every operation is the one the sequential file route gives
; (`fn-olr-*-is-the-file-route-by-definition').  What the file route's crash
; model (fn-sf-crash-imagep, the K0 books) said about the frontier and record
; files does not describe a format-9 store's bytes; the log's does
; (books/store-log-crash.lisp T2, books/owner-batch.lisp T1/T7).
(in-package "ACL2")
(include-book "store-log-route")
(include-book "records-concrete-owner")
(include-book "config")

; -----------------------------------------------------------------------------
; The owner (host/owner-host.lisp fn-owner-io's :log-reserve and :log-order
; arms): the same sequences as owner events.

; The routes below chain concrete io steps on the owner's store: each step
; wants (and keeps) the store a store-node state, which is what the host
; carries for the owner (fn-rcon-ocfg-io's guard).
(defthm fn-rcon-ocfg-io-keeps-the-store-a-state
  (implies (fn-sn-statep (fn-own-store (fn-ocfg-owner oc)))
           (fn-sn-statep (fn-own-store (fn-ocfg-owner (fn-rcon-ocfg-io oc operation result)))))
  :hints (("Goal" :in-theory (enable fn-rcon-ocfg-io fn-rcon-own-store-io))))

(defun fn-olr-ocfg-reserve (oc)
  (declare (xargs :guard (fn-sn-statep (fn-own-store (fn-ocfg-owner oc)))))
  (fn-rcon-ocfg-io
   (fn-rcon-ocfg-io
    (fn-rcon-ocfg-io (fn-rcon-ocfg-io oc :start-frontier nil) :frontier-file :ok)
    :frontier-replace :ok)
   :frontier-directory :ok))

(defun fn-olr-ocfg-order (oc)
  (declare (xargs :guard (fn-sn-statep (fn-own-store (fn-ocfg-owner oc)))))
  (fn-rcon-ocfg-io
   (fn-rcon-ocfg-io (fn-rcon-ocfg-io oc :record-file :ok) :record-link :ok)
   :record-directory :ok))

(defthm fn-olr-ocfg-reserve-is-the-file-route-by-definition
  (equal (fn-olr-ocfg-reserve oc)
         (fn-ocfg-step
          (fn-ocfg-step
           (fn-ocfg-step
            (fn-ocfg-step oc '(:store (:io :start-frontier nil)) fn-arena)
            '(:store (:io :frontier-file :ok)) fn-arena)
           '(:store (:io :frontier-replace :ok)) fn-arena)
          '(:store (:io :frontier-directory :ok)) fn-arena)))

(defthm fn-olr-ocfg-order-is-the-file-route-by-definition
  (equal (fn-olr-ocfg-order oc)
         (fn-ocfg-step
          (fn-ocfg-step
           (fn-ocfg-step oc '(:store (:io :record-file :ok)) fn-arena)
           '(:store (:io :record-link :ok)) fn-arena)
          '(:store (:io :record-directory :ok)) fn-arena)))


; -----------------------------------------------------------------------------
; The operator's bounds on one batch: the live configuration's limits at the
; slots "log-batch-records" and "log-batch-octets" (the EXISTING delta kind
; :set-limit, books/config.lisp fn-cfg-limit; D27: work per step, never a
; data cap).  These are books/owner-batch.lisp's fn-owb-bmax / fn-owb-omax
; with the octet bound's default fixed at 16 MiB of entries; owner-batch is
; not included here because its catalog's abstract stobj and the digest's
; attachment (books/crypto-attach, which the record codec needs) cannot be in
; one world (ACL2's stobj-attachment restriction).
(defconst *fn-olr-batch-records-default* 64)
(defconst *fn-olr-batch-octets-default* 16777216)
(defun fn-olr-bmax (v)
  (declare (xargs :guard t))
  (let ((n (fn-cfg-limit v "log-batch-records")))
    (if (posp n) n *fn-olr-batch-records-default*)))
(defun fn-olr-omax (v)
  (declare (xargs :guard t))
  (let ((n (fn-cfg-limit v "log-batch-octets")))
    (if (and (posp n) (< n *fn-olr-batch-octets-default*)) n
      *fn-olr-batch-octets-default*)))

; The host's call (host/owner-host.lisp fn-owner-log-bounds): the bounds of
; the live configuration RECORD (fn-owner-config: a generation and its
; value, books/config.lisp fn-cfg-make), read at its VALUE.  Lane
; scheduler-2-rebase (PKT-828 trace, 2026-09-27): the host called fn-olr-bmax
; on the record itself, whose limits are not at fn-cfg-limit's place, so
; `policy set log-batch-records 2' was read as the default 64 (a START of 7
; members at bound 2; tests/acl2/owner-log-route-tests.lisp has the witness).
(defun fn-olr-bounds (cfg)
  (declare (xargs :guard t))
  (list (fn-olr-bmax (fn-cfg-value cfg)) (fn-olr-omax (fn-cfg-value cfg))))
