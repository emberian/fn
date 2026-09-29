; store-finalize-published.lisp -- the composed boundary of the Store open
; from a checkpoint (row A9, PRF-992; lane incremental-finalize-3).
;
; The open (host/store-node-host.lisp fn-store-sn-recover-from-checkpoint)
; calls fn-sfi-extend-open with the F row's NEXT, and its KEYSTONE
; fn-sfi-extend-open-is-rii-extend-open (PRF-946) equates it to the twin
; under two facts about the checkpoint: it finalized :ok at some frontier,
; and NEXT is its records' transaction bound.  Neither is checked at the
; open (the first IS the whole-history finalize the open no longer runs).
; This book proves both of every PUBLICATION: the owner publishes
; fn-ock-next-checkpoint of a history that opens :ok at the publication
; frontier (books/owner-checkpoint-open.lisp: the capture of the whole
; history), through fn-sct-tables-of-capture (the F row's S, frontier and
; NEXT).  The composed statement fn-sfp-open-from-publication-is-the-twin:
; the open from the tables of such a publication, with the F row's NEXT,
; is the twin's open, for every later suffix and frontier.
;
; What connects the tables of a publication to the bytes the open verified
; is not a theorem: books/store-checkpoint-arena-load.lisp
; fn-scka-load-of-written-file says the writer's file loads to its tables,
; and that a file whose trailer chain verifies IS the writer's file is the
; trust row A-CHECKPOINT-PUBLICATION (books/assumptions-publication.lisp),
; the 2^-128 of one trailer.  Every process-death cut of the publication is
; a crash point of fn-bs-scp-program (books/byte-store-state-checkpoint-
; program.lisp fn-bs-scp-program-crash-is-old-or-new): the open sees the
; old checkpoint or the new one, never a torn one, and a torn new one fails
; its chain (fn-scc-open-segment) before any table is read.

(in-package "ACL2")

(include-book "store-finalize-incremental")
(include-book "owner-checkpoint-open")
(include-book "store-checkpoint-tables")

; -----------------------------------------------------------------------------
; 1. Of an observed history the transaction bound is a natural: every record's
; transaction is at or above the running bound, which starts at a natural.

(defthm fn-sfp-next-lower-natp
  (implies (and (fn-sf-record-listp p sequence lower frontier)
                (natp lower))
           (natp (fn-sf-next-lower p lower)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :induct (fn-sf-record-listp p sequence lower frontier)
           :in-theory (enable fn-sf-next-lower fn-sf-record-listp))))

(defthm fn-sfp-observed-history-is-a-true-list
  (implies (fn-sn-observed-historyp frontier records)
           (true-listp records))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-sn-observed-historyp fn-sf-record-listp))))

; -----------------------------------------------------------------------------
; 2. The published capture finalizes :ok at the publication frontier.
; fn-ock-next-checkpoint of a history that opens :ok is the capture of the
; whole history (fn-ock-next-checkpoint-is-the-capture), and the finalize of
; a capture at its frontier is the full open (fn-ock-finalize-of-extended-
; capture with the empty suffix).

(defthm fn-sfp-published-capture-finalizes-ok
  (implies (equal (fn-sn-open-kind (fn-cpo-open-observed configs frontier records)) :ok)
           (equal (fn-sn-open-kind
                   (fn-sco-finalize (fn-ock-next-checkpoint base configs records)
                                    configs frontier))
                  :ok))
  :hints (("Goal" :do-not-induct t
           :use (fn-ock-open-ok-has-history
                 fn-ock-next-checkpoint-is-the-capture
                 (:instance fn-ock-finalize-of-extended-capture
                            (prefix records) (suffix nil))
                 (:instance fn-sco-extend-of-capture-when-history
                            (prefix records) (suffix nil)))
           :in-theory (e/d (fn-sfp-observed-history-is-a-true-list)
                           (fn-ock-next-checkpoint fn-ock-next-checkpoint-is-the-capture
                            fn-ock-finalize-of-extended-capture
                            fn-sco-extend-of-capture-when-history
                            fn-sco-finalize fn-cpo-open-observed fn-sco-extend
                            fn-sco-capture fn-sn-open-kind fn-sn-observed-historyp)))))

; -----------------------------------------------------------------------------
; 3. The F row's NEXT of the publication is the bound the keystone asks for.

(defthm fn-sfp-published-next-is-the-bound
  (implies (equal (fn-sn-open-kind (fn-cpo-open-observed configs frontier records)) :ok)
           (equal (fn-sct-tables-next
                   (fn-sct-tables-of-capture (fn-ock-next-checkpoint base configs records)
                                             frontier revision log))
                  (fn-sf-next-lower records 0)))
  :hints (("Goal" :do-not-induct t
           :use (fn-ock-open-ok-has-history
                 fn-ock-next-checkpoint-is-the-capture
                 (:instance fn-sfp-next-lower-natp
                            (p records) (sequence 0) (lower 0)))
           :in-theory (e/d (fn-sct-next-of-tables-of-capture fn-sn-observed-historyp
                            fn-sfp-observed-history-is-a-true-list)
                           (fn-ock-next-checkpoint fn-ock-next-checkpoint-is-the-capture
                            fn-sfp-next-lower-natp fn-sf-record-listp
                            fn-cpo-open-observed fn-sn-open-kind fn-sco-capture
                            fn-sf-next-lower)))))

; -----------------------------------------------------------------------------
; 4. THE COMPOSED BOUNDARY (KEYSTONE, PRF-992).  The tables of a publication
; of a history that opens :ok at the publication frontier, loaded
; (fn-sct-capture-of-tables) and opened with the F row's NEXT over any
; suffix at any frontier, open as the twin fn-rii-sco-extend-open does.
; CONFIGS is the configuration history on both sides: the one the
; publication captured and the one the open passes.

(defthm fn-sfp-open-from-publication-is-the-twin
  (implies (equal (fn-sn-open-kind (fn-cpo-open-observed configs frontier records)) :ok)
           (let* ((tables (fn-sct-tables-of-capture
                           (fn-ock-next-checkpoint base configs records)
                           frontier revision log))
                  (c (fn-sct-capture-of-tables tables)))
             (equal (fn-sfi-extend-open c configs suffix f (fn-sct-tables-next tables))
                    (fn-rii-sco-extend-open c configs suffix f))))
  :hints (("Goal" :do-not-induct t
           :use (fn-ock-open-ok-has-history
                 fn-ock-next-checkpoint-is-the-capture
                 fn-sfp-published-capture-finalizes-ok
                 fn-sfp-published-next-is-the-bound
                 (:instance fn-sfi-extend-open-is-rii-extend-open
                            (c (fn-sco-capture configs records))
                            (frontier f) (f0 frontier)
                            (next (fn-sf-next-lower records 0))))
           :in-theory (e/d (fn-sct-capture-of-tables-of-capture)
                           (fn-ock-next-checkpoint fn-ock-next-checkpoint-is-the-capture
                            fn-sfp-published-capture-finalizes-ok
                            fn-sfp-published-next-is-the-bound
                            fn-sfi-extend-open-is-rii-extend-open
                            fn-sfi-extend-open fn-rii-sco-extend-open
                            fn-sct-tables-of-capture fn-sct-capture-of-tables
                            fn-sct-tables-next fn-sco-finalize fn-cpo-open-observed
                            fn-sn-open-kind fn-sco-capture fn-sf-next-lower
                            fn-sn-observed-historyp)))))
