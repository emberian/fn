; assumptions-publication.lisp -- A-CHECKPOINT-PUBLICATION, the trust row of
; the Store open from a checkpoint (row A9, PRF-992; lane incremental-
; finalize-3).  A named assumption is an encapsulate with a local witness
; (books/assumptions.lisp says why); this book is included from nothing on
; a served path -- it states what the host RELIES on at one boundary, so
; that the reliance is mechanically listable (`grep fn-assume-`), and it
; carries the theorem the open has under it.
;
; THE BOUNDARY.  host/store-node-host.lisp fn-store-sco-decode-finish loads
; a checkpoint file whose segment chain verified (every segment's trailer
; over its header and chunk, chained from the genesis: books/store-
; checkpoint-codec.lisp fn-scc-open-segment) to its tables, and
; fn-store-sn-recover-from-checkpoint opens from the capture the tables mean
; with the F row's NEXT, by fn-sfi-extend-open (books/store-finalize-
; incremental.lisp, PRF-946): the prefix is never walked again.  The twin
; equality holds of every PUBLICATION (books/store-finalize-published.lisp
; fn-sfp-open-from-publication-is-the-twin) and the writer's file loads to
; its tables (books/store-checkpoint-arena-load.lisp
; fn-scka-load-of-written-file).  What is assumed is the step between: a
; file whose chain verifies is the writer's file of a publication of a
; history that opened :ok under the configuration the open passes, at the
; frontier the F row carries.  The pessimistic number, with its scope: each
; segment's trailer is one 256-bit digest (fn-frame-trailer), and the figure
; for a file that is not the writer's and still verifies is A-CRYPTO-
; TRAILER's collision bound, about 2^-128 per chosen pair of frames (not the
; 2^-256 second-preimage figure) -- but the row is not only cryptographic:
; an operator who copies a foreign store's
; checkpoint over this one produces a verifying file that is a publication
; of ANOTHER history (row A10, store-lineage: the lineage check refuses it
; by name before this open runs).
;
; Under the assumption the open is the twin: the theorem below.  The
; assumption's witness is the empty predicate (no tables are assumed
; published), so nothing in the tree depends on the assumption without
; naming fn-assume-checkpoint-publishedp in its hypothesis.
;
; Registered: planning/proofs.json PRF-992; specs/failures.md names it.

(in-package "ACL2")

(include-book "store-finalize-published")

; A-CHECKPOINT-PUBLICATION.  (fn-assume-checkpoint-publishedp tables configs)
; holds of the tables a verified checkpoint file loaded to, under the
; configuration history CONFIGS the open passes; fn-assume-checkpoint-
; publication names the publication: (list BASE RECORDS FRONTIER REVISION
; LOG), the owner's next-checkpoint base, the records of the history it
; captured, its frontier, its revision and its log position.
(encapsulate
  (((fn-assume-checkpoint-publishedp * *) => *)
   ((fn-assume-checkpoint-publication * *) => *))
  (local (defun fn-assume-checkpoint-publishedp (tables configs)
           (declare (ignore tables configs))
           nil))
  (local (defun fn-assume-checkpoint-publication (tables configs)
           (declare (ignore tables configs))
           nil))
  (defthm fn-assume-checkpoint-publication-is-a-publication
    (implies (fn-assume-checkpoint-publishedp tables configs)
             (let* ((p (fn-assume-checkpoint-publication tables configs))
                    (base (nth 0 p)) (records (nth 1 p)) (frontier (nth 2 p))
                    (revision (nth 3 p)) (log (nth 4 p)))
               (and (equal tables
                           (fn-sct-tables-of-capture
                            (fn-ock-next-checkpoint base configs records)
                            frontier revision log))
                    (equal (fn-sn-open-kind
                            (fn-cpo-open-observed configs frontier records))
                           :ok))))
    :rule-classes nil))

; The open under A-CHECKPOINT-PUBLICATION: from the tables a verified file
; loaded to, with the F row's NEXT, over any suffix at any frontier, the
; open the host runs is the twin's.
(defthm fn-sfp-open-under-checkpoint-publication
  (implies (fn-assume-checkpoint-publishedp tables configs)
           (equal (fn-sfi-extend-open (fn-sct-capture-of-tables tables)
                                      configs suffix f (fn-sct-tables-next tables))
                  (fn-rii-sco-extend-open (fn-sct-capture-of-tables tables)
                                          configs suffix f)))
  :hints (("Goal" :do-not-induct t
           :use (fn-assume-checkpoint-publication-is-a-publication
                 (:instance fn-sfp-open-from-publication-is-the-twin
                            (base (nth 0 (fn-assume-checkpoint-publication tables configs)))
                            (records (nth 1 (fn-assume-checkpoint-publication tables configs)))
                            (frontier (nth 2 (fn-assume-checkpoint-publication tables configs)))
                            (revision (nth 3 (fn-assume-checkpoint-publication tables configs)))
                            (log (nth 4 (fn-assume-checkpoint-publication tables configs)))))
           :in-theory (disable fn-sfp-open-from-publication-is-the-twin
                               fn-sfi-extend-open fn-rii-sco-extend-open
                               fn-sct-capture-of-tables fn-sct-tables-next
                               fn-sct-tables-of-capture fn-ock-next-checkpoint
                               fn-cpo-open-observed fn-sn-open-kind))))
