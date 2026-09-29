; fn: a state checkpoint's VERIFIABLE digest (PKT-854, lane
; correctness-remainder-4; planning/evidence/proto-determinism-2026-09-27.md
; N1).  A checkpoint file's bytes carry two non-log fields in its F row
; (books/store-checkpoint-tables.lisp fn-sct-f-row): REVISION, the writer
; image's source revision, and LOG, the rotation's (K GENESIS).  Two nodes
; holding the same log write different checkpoint bytes when their images or
; their rotation histories differ.  What a peer compares is this digest: the
; F row's schema, sequence S and txid frontier, the P, E and R tables, and
; the arena's payloads (books/state-digest.lisp, the LOGICAL value), never
; REVISION or LOG.  REVISION stays in the file as provenance.
;
; KEYSTONE `fn-sckd-digest-of-written-file': the file the writer produced
; for a prefix (CONFIGS, RECORDS), a frontier and the payloads PS, loaded
; by fn-scka-load (the three calls host/store-node-host.lisp makes;
; KEYSTONE fn-scka-load-of-written-file), digests to
; fn-sckd-digest-of-prefix: a function of those alone, whatever REVISION
; and LOG the writer put in the F row.
; What the host calls: host/store-node-host.lisp fn-store-sco-decode-finish
; calls fn-sckd-tables-digest on the loaded tables and
; fn-store-sco-note-checkpoint-digest calls fn-sckd-combine with the arena's
; fn-sdg-arena-pool right after the load, which is fn-sckd-digest by
; definition; `store ROOT digest' prints it as `checkpoint-digest'.
(in-package "ACL2")
(include-book "store-checkpoint-arena-load")
(include-book "state-digest")

; The tables without the F row's provenance: (schema S frontier P E R).
(defun fn-sckd-verifiable (tables)
  (declare (xargs :guard t))
  (let ((f (fn-sct-tables-f tables)))
    (list (fn-sco-at 0 f) (fn-sco-at 1 f) (fn-sco-at 2 f)
          (fn-sct-tables-p tables) (fn-sct-tables-e tables)
          (fn-sct-tables-r tables))))

(defun fn-sckd-tables-digest (tables)
  (declare (xargs :guard t))
  (fn-sdg-digest (fn-sckd-verifiable tables)))

; POOL is the arena's digest (fn-sdg-arena-pool).
(defun fn-sckd-combine (tables-digest pool)
  (declare (xargs :guard (and (true-listp tables-digest) (true-listp pool))))
  (fn-digest (append tables-digest pool)))

(defun fn-sckd-digest (tables pool)
  (declare (xargs :guard (true-listp pool)))
  (fn-sckd-combine (fn-sckd-tables-digest tables) pool))

; The provenance fields are not read.
(defthm fn-sckd-verifiable-of-tables-of-capture
  (equal (fn-sckd-verifiable (fn-sct-tables-of-capture c frontier revision log))
         (fn-sckd-verifiable (fn-sct-tables-of-capture c frontier nil nil)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-sct-tables-of-capture fn-sct-f-row
                                     fn-sct-tables-f fn-sct-tables-p
                                     fn-sct-tables-e fn-sct-tables-r fn-sco-at))))

(defthm fn-sckd-digest-ignores-revision-and-log-by-definition
  (equal (fn-sckd-digest (fn-sct-tables-of-capture c frontier revision log) pool)
         (fn-sckd-digest (fn-sct-tables-of-capture c frontier nil nil) pool))
  :rule-classes nil
  :hints (("Goal" :use fn-sckd-verifiable-of-tables-of-capture
           :in-theory (disable fn-sckd-verifiable fn-sct-tables-of-capture
                               fn-sckd-combine))))

; The digest a prefix's checkpoint has: its capture's tables with no
; provenance, and the payloads PS the arena holds.
(defun-nx fn-sckd-digest-of-prefix (configs records frontier ps)
  (fn-sckd-digest (fn-sct-tables-of-capture (fn-sco-capture configs records)
                                            frontier nil nil)
                  (fn-sdg-arena-pool ps)))

; KEYSTONE (PKT-854).  Under fn-scka-load-of-written-file's hypotheses the
; loaded checkpoint's digest is the prefix's, for every REVISION and LOG the
; writer recorded: two nodes holding the same prefix and payloads compute
; the same checkpoint digest whatever image wrote the file and whenever the
; log rotated.  Teeth: tests/acl2/store-checkpoint-digest-tests.lisp.
(defthm fn-sckd-digest-of-written-file
  (let* ((c (fn-sco-capture configs records))
         (tables (fn-sct-tables-of-capture c frontier revision log))
         (progs (fn-sct-table-programs tables (fn-sco-event-index c)))
         (s (len records)))
    (implies (and (fn-octets-p fn-octets)
                  (fn-sccr-planp plan (if (consp plan) (fn-sccr-at 1 (car plan)) 0) fn-octets)
                  (equal (fn-sccr-plan-segments plan fn-octets)
                         (append (fn-scka-run-segments ps ks s)
                                 (fn-sct-file-segments progs seg s)))
                  (true-list-listp ps) (equal (fn-scka-sum ks) (len ps))
                  (fn-scc-chunk-listp (fn-scka-run-chunks ps ks))
                  (< (+ 1 (len ks)) *fn-scc-u64-bound*) (< s *fn-scc-u64-bound*)
                  (fn-sct-tables-treep tables)
                  (fn-sct-log-positionp log)
                  (<= (len records) (1+ *fn-cbor-max-uint*))
                  (fn-sct-programs-widthp progs))
             (equal (fn-sckd-digest
                     (cadr (mv-nth 0 (fn-scka-load plan fn-octets fn-arena)))
                     (fn-sdg-arena-pool (mv-nth 1 (fn-scka-load plan fn-octets fn-arena))))
                    (fn-sckd-digest-of-prefix configs records frontier ps))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-scka-load-of-written-file)
                 (:instance fn-sckd-digest-ignores-revision-and-log-by-definition
                            (c (fn-sco-capture configs records))
                            (pool (fn-sdg-arena-pool ps))))
           :in-theory (e/d ()
                           (fn-scka-load-of-written-file fn-scka-load fn-sckd-digest
                            fn-sct-tables-of-capture fn-sco-capture
                            fn-sct-table-programs fn-sct-tables-treep
                            fn-sct-programs-widthp fn-sccr-planp fn-sco-event-index
                            fn-sct-log-positionp fn-sdg-arena-pool
                            fn-sct-file-segments fn-sccr-plan-segments)))))
