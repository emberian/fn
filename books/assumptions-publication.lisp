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
(include-book "store-finalize-carried-check")

; A-CHECKPOINT-PUBLICATION.  (fn-assume-checkpoint-publishedp tables configs)
; holds of the tables a verified checkpoint file loaded to, under the
; configuration history CONFIGS the open passes; fn-assume-checkpoint-
; publication names the publication: (list PREFIX RECORDS FRONTIER REVISION
; LOG), the records of the base it extended (the previous publication's
; capture, (fn-sco-capture configs prefix)), the records of the history it
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
                    (prefix (nth 0 p)) (records (nth 1 p)) (frontier (nth 2 p))
                    (revision (nth 3 p)) (log (nth 4 p)))
               (and (equal tables
                           (fn-sct-tables-of-capture
                            (fn-ock-next-checkpoint (fn-sco-capture configs prefix)
                                                    configs records)
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
                            (prefix (nth 0 (fn-assume-checkpoint-publication tables configs)))
                            (records (nth 1 (fn-assume-checkpoint-publication tables configs)))
                            (frontier (nth 2 (fn-assume-checkpoint-publication tables configs)))
                            (revision (nth 3 (fn-assume-checkpoint-publication tables configs)))
                            (log (nth 4 (fn-assume-checkpoint-publication tables configs)))))
           :in-theory (theory 'minimal-theory))))

; -----------------------------------------------------------------------------
; A-CARRIED-PAIR (PRF-1005).  The carried entries (books/store-finalize-
; incremental.lisp fn-sfi-cpr-resume-carried, fn-sfi-extend-open-carried;
; PRF-968) take the pair (R . IX) under fn-sfi-cpr-carriedp, a guard the
; evaluator cannot run (fn-rii-known-okp is a defun-sk) and ACL2 will not
; hold in a stobj (fn-cnode-statep reaches the attached fn-digest).  A host
; that carries the pair across extensions (the online-reclaim swap; the
; owner's later publications) relies on this: the pair it passes is the one
; fn-sfi-carry produced at the open, or the one the previous carried entry
; answered -- the preservation theorems (fn-sfi-carry-is-carried,
; fn-sfi-extend-open-carried-keeps-carried, fn-sfi-cpr-resume-carried-keeps-
; carried) keep it carried along exactly that sequence.  At a boundary that
; can afford one node pass, fn-sfk-carried-check decides it (:ok establishes
; the invariant; every other answer but :uncertain-id-trie refutes it).
; Nothing on a served path calls the carried entries at this revision
; (the open calls fn-sfi-extend-open); the row is the contract of the
; wiring that will.
(encapsulate
  (((fn-assume-carried-pairp * *) => *))
  (local (defun fn-assume-carried-pairp (r ix) (declare (ignore r ix)) nil))
  (defthm fn-assume-carried-pair-is-carried
    (implies (fn-assume-carried-pairp r ix)
             (fn-sfi-cpr-carriedp r ix))
    :rule-classes nil))

; The carried open under A-CARRIED-PAIR (with PRF-968's other hypotheses).
(defthm fn-sfp-carried-open-under-carried-pair
  (implies (and (fn-assume-carried-pairp (fn-sco-cpr c) ix)
                (equal (fn-sn-open-kind (fn-sco-finalize c configs f0)) :ok)
                (equal count (len (fn-sco-records c)))
                (equal next (fn-sf-next-lower (fn-sco-records c) 0)))
           (equal (fn-sfi-extend-open-carried c ix configs suffix frontier count next)
                  (list (fn-sco-extend c configs suffix)
                        (cdr (fn-sfi-cpr-resume-carried (fn-sco-cpr c) configs suffix ix))
                        (fn-rii-classified-open (fn-sco-extend c configs suffix)
                                                configs frontier))))
  :hints (("Goal" :use ((:instance fn-assume-carried-pair-is-carried (r (fn-sco-cpr c)))
                        (:instance fn-sfi-extend-open-carried-is-rii-extend-open))
           :in-theory (theory 'minimal-theory))))
