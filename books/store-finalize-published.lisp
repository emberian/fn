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
; A-CRYPTO-TRAILER's 2^-128 per chosen pair.  Every process-death cut of
; the publication is a crash point of fn-bs-scp-program (books/byte-store-
; state-checkpoint-program.lisp fn-bs-scp-program-crash-is-old-or-new): the
; open sees the old checkpoint or the new one, never a torn one, and a torn
; new one fails its chain (fn-scc-open-segment) before any table is read.
;
; The base of a publication is a capture (fn-sco-capture configs prefix), as
; the owner's always is: the first publication's base is the capture of the
; empty prefix (host/owner-host.lisp fn-owner-sco-next) and every later one
; is the previous publication.

(in-package "ACL2")

(include-book "store-finalize-incremental")
(include-book "owner-checkpoint-open")
(include-book "store-checkpoint-tables")

; -----------------------------------------------------------------------------
; 1. Facts of an observed history: a true list whose transaction bound is a
; natural (every record's transaction is at or above the running bound,
; which starts at a natural).

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
  :rule-classes (:rewrite :forward-chaining)
  :hints (("Goal" :in-theory (enable fn-sn-observed-historyp fn-sf-record-listp))))

(defthm fn-sfp-observed-history-bound-natp
  (implies (fn-sn-observed-historyp frontier records)
           (natp (fn-sf-next-lower records 0)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :use ((:instance fn-sfp-next-lower-natp
                                   (p records) (sequence 0) (lower 0)))
           :in-theory (e/d (fn-sn-observed-historyp)
                           (fn-sfp-next-lower-natp fn-sf-record-listp fn-sf-next-lower)))))

(local
 (defthm fn-sfp-append-nil
   (implies (true-listp x) (equal (append x nil) x))))

(local
 (defthm fn-sfp-true-list-fix-of-true-list
   (implies (true-listp x) (equal (true-list-fix x) x))))

; -----------------------------------------------------------------------------
; 2. Of a capture: its records, its extension by nothing, its finalize at
; the frontier of an observed history (the full open,
; fn-ock-finalize-of-extended-capture over the empty suffix).

(local
 (defthm fn-sfp-records-of-capture
   (equal (fn-sco-records (fn-sco-capture configs records))
          (true-list-fix records))
   :hints (("Goal" :in-theory (e/d (fn-sco-capture fn-sco-make fn-sco-records fn-sco-at)
                                   (fn-sco-cpr-prefix fn-replay-identity-loop
                                    fn-cpe-projection-replay fn-th-prefix-loop
                                    fn-cei-build-aux))))))

(defthm fn-sfp-extend-capture-by-nothing
  (implies (fn-sn-observed-historyp frontier records)
           (equal (fn-sco-extend (fn-sco-capture configs records) configs nil)
                  (fn-sco-capture configs records)))
  :hints (("Goal" :use ((:instance fn-sco-extend-of-capture-when-history
                                   (prefix records) (suffix nil))
                        (:instance fn-sfp-observed-history-is-a-true-list))
           :in-theory (union-theories (theory 'minimal-theory)
                                      '(fn-sfp-append-nil)))))

(defthm fn-sfp-finalize-of-capture-is-the-open
  (implies (fn-sn-observed-historyp frontier records)
           (equal (fn-sco-finalize (fn-sco-capture configs records) configs frontier)
                  (fn-cpo-open-observed configs frontier records)))
  :hints (("Goal" :use ((:instance fn-ock-finalize-of-extended-capture
                                   (prefix records) (suffix nil))
                        (:instance fn-sfp-observed-history-is-a-true-list))
           :in-theory (union-theories (theory 'minimal-theory)
                                      '(fn-sfp-append-nil
                                        fn-sfp-extend-capture-by-nothing)))))

; -----------------------------------------------------------------------------
; 3. The published capture finalizes :ok at the publication frontier.

(defthm fn-sfp-published-capture-finalizes-ok
  (implies (equal (fn-sn-open-kind (fn-cpo-open-observed configs frontier records)) :ok)
           (equal (fn-sn-open-kind
                   (fn-sco-finalize (fn-ock-next-checkpoint (fn-sco-capture configs prefix)
                                                            configs records)
                                    configs frontier))
                  :ok))
  :hints (("Goal" :use ((:instance fn-ock-open-ok-has-history (events records)))
           :in-theory (union-theories (theory 'minimal-theory)
                                      '(fn-ock-next-checkpoint-is-the-capture
                                        fn-sfp-finalize-of-capture-is-the-open)))))

; -----------------------------------------------------------------------------
; 4. The F row's NEXT of the publication is the bound the keystone asks for.

(defthm fn-sfp-next-of-capture-tables
  (implies (fn-sn-observed-historyp frontier records)
           (equal (fn-sct-tables-next
                   (fn-sct-tables-of-capture (fn-sco-capture configs records)
                                             frontier2 revision log))
                  (fn-sf-next-lower records 0)))
  :hints (("Goal" :use ((:instance fn-sfp-observed-history-is-a-true-list)
                        (:instance fn-sfp-observed-history-bound-natp))
           :in-theory (union-theories (theory 'minimal-theory)
                                      '(fn-sct-next-of-tables-of-capture
                                        fn-sfp-records-of-capture
                                        fn-sfp-true-list-fix-of-true-list
                                        nfix natp)))))

(defthm fn-sfp-published-next-is-the-bound
  (implies (equal (fn-sn-open-kind (fn-cpo-open-observed configs frontier records)) :ok)
           (equal (fn-sct-tables-next
                   (fn-sct-tables-of-capture
                    (fn-ock-next-checkpoint (fn-sco-capture configs prefix) configs records)
                    frontier revision log))
                  (fn-sf-next-lower records 0)))
  :hints (("Goal" :use ((:instance fn-ock-open-ok-has-history (events records)))
           :in-theory (union-theories (theory 'minimal-theory)
                                      '(fn-ock-next-checkpoint-is-the-capture
                                        fn-sfp-next-of-capture-tables)))))

; -----------------------------------------------------------------------------
; 5. THE COMPOSED BOUNDARY (KEYSTONE, PRF-992).  The tables of a publication
; of a history that opens :ok at the publication frontier, loaded
; (fn-sct-capture-of-tables) and opened with the F row's NEXT over any
; suffix at any frontier, open as the twin fn-rii-sco-extend-open does.
; CONFIGS is the configuration history on both sides: the one the
; publication captured and the one the open passes; PREFIX the records of
; the base the publication extended (the previous publication's).

(defthm fn-sfp-open-from-publication-is-the-twin
  (implies (equal (fn-sn-open-kind (fn-cpo-open-observed configs frontier records)) :ok)
           (let* ((tables (fn-sct-tables-of-capture
                           (fn-ock-next-checkpoint (fn-sco-capture configs prefix)
                                                   configs records)
                           frontier revision log))
                  (c (fn-sct-capture-of-tables tables)))
             (equal (fn-sfi-extend-open c configs suffix f (fn-sct-tables-next tables))
                    (fn-rii-sco-extend-open c configs suffix f))))
  :hints (("Goal" :use ((:instance fn-ock-open-ok-has-history (events records))
                        (:instance fn-sfi-extend-open-is-rii-extend-open
                                   (c (fn-sco-capture configs records))
                                   (frontier f) (f0 frontier)
                                   (next (fn-sf-next-lower records 0))))
           :in-theory (union-theories (theory 'minimal-theory)
                                      '(fn-ock-next-checkpoint-is-the-capture
                                        fn-sct-capture-of-tables-of-capture
                                        fn-sfp-next-of-capture-tables
                                        fn-sfp-finalize-of-capture-is-the-open
                                        fn-sfp-records-of-capture
                                        fn-sfp-true-list-fix-of-true-list
                                        fn-sfp-observed-history-is-a-true-list)))))
