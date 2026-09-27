; fn: which of the format-9 open's recovery barriers the byte model needs
; (lane log-recovery-2, item 3, 2026-09-27).
;
; host/native/io.lisp fnn-recover-log runs P-LOG-RECOVER (the tail zeroed,
; the segment fenced: books/store-log-programs.lisp fn-lg-recover-program)
; and then the five recovery barriers of fnn-store-recovery-barriers
; (config.json, the segment, journal/, the root, its parent), counted by
; books/store-files.lisp *fn-sf-recovery-barrier-count*.  The design
; (planning/design-2026-09-27-storage-log.md section 3.5) names ONE recovery
; barrier: the segment's fence after the truncation.  This book settles which
; of the six fences the byte model (books/byte-store.lisp) needs.
;
;   fn-lgob-duplicate-segment-fence-is-identity   the second barrier (the
;       segment again) is the identity on a related state with nothing in
;       flight: after P-LOG-RECOVER nothing is pending, so it fences nothing.
;   fn-lgob-recovered-segment-fence-is-identity   the same at the state the
;       host holds after fnn-log-recover (log-recovered), for any store
;       whose segment inode exists: no obligation, no relation needed.
;   fn-lgob-file-fence-keeps-entry-operations      a file fence never drains a
;       pending directory entry: a create in journal/ (P-ROTATE's
;       rotate-created, init's init-segment-created), a rename into the root
;       (a checkpoint install before its root fence) or into the parent (an
;       import at import-published) is still droppable by a crash after the
;       segment's fence.  So ONE barrier is not sufficient:
;   fn-lgob-one-barrier-loses-a-rotated-segment    a ground witness: a death
;       at rotate-created, an open fencing only the segment, a batch written
;       and fenced (acknowledged), then a crash: the batch's octets are
;       durable in an inode no durable name reaches.
;   fn-lgob-journal-fence-keeps-the-rotated-segment   with journal/ fenced
;       at the open, every crash image names it.
;
; What the model needs at the open, then: the segment (P-LOG-RECOVER's own
; fence), journal/ (a create or unlink in flight at a death in P-ROTATE,
; P-DROP or init), the parent (an import at import-published, init before
; init-parent-fenced), and the root before the open's drop of covered
; segments (a checkpoint renamed but not fenced).  The second barrier (the
; segment) is redundant (the theorems here); config.json is written only by
; init's publication and the import's staging, each of which fences its data
; before it is named (books/byte-store-initializer.lisp fn-bsi-publish-steps,
; books/store-import-publication.lisp fn-bs-imp-file-steps), so its barrier
; fences nothing on a reachable state (argued, not proved here).
(in-package "ACL2")
(include-book "store-log-programs")

(local
 (defthm fn-lgob-make-of-own-fields
   (implies (and (fn-bs-shapep bs) (null (fn-bs-pending bs)))
            (equal (fn-bs-make (fn-bs-unit bs) (fn-bs-inodes bs) (fn-bs-dirs bs)
                               nil (fn-bs-next-ino bs))
                   bs))
   :hints (("Goal" :in-theory (enable fn-bs-make fn-bs-shapep fn-bs-unit fn-bs-inodes
                                      fn-bs-dirs fn-bs-pending fn-bs-next-ino)
            :expand ((len bs) (len (cdr bs)) (len (cddr bs)) (len (cdddr bs))
                     (len (cddddr bs)) (len (cdr (cddddr bs))))))))

; R with nothing in flight holds nothing pending.
(local
 (defthm fn-lgob-relp-idle-has-nothing-pending
   (implies (and (fn-lgk-relp bs ks ino genesis max)
                 (not (consp (fn-lgk-inflight ks))))
            (equal (fn-bs-pending bs) nil))
   :hints (("Goal" :in-theory (e/d (fn-lgk-relp) (fn-lgk-content-okp))))))

; KEYSTONE.  The open's second recovery barrier fences the segment again:
; on a related state with no batch in flight the step changes neither the
; byte store nor the kernel.
(defthm fn-lgob-duplicate-segment-fence-is-identity
  (implies (and (fn-bs-shapep bs)
                (fn-lgk-relp bs ks ino genesis max)
                (not (consp (fn-lgk-inflight ks))))
           (equal (fn-lg-step bs ks '(:fence :segment :tail) :ok ino)
                  (mv :ok bs ks)))
  :hints (("Goal" :in-theory (e/d (fn-lg-step fn-bs-fsync-file fn-bs-fence-file)
                                  (fn-lgk-relp fn-bs-durable-content fn-bs-make)))))

; The state the host holds after fnn-log-recover (fn-lg-recover-program run
; to log-recovered) is such a state: the recovered kernel has nothing in
; flight, the run's store is a byte store, and R holds there
; (fn-lg-recover-program-establishes-the-relation).
(defthm fn-lgob-recovered-kernel-has-nothing-in-flight
  (not (consp (fn-lgk-inflight (fn-lg-recovered-kernel bs ino genesis max floor))))
  :hints (("Goal" :in-theory (enable fn-lg-recovered-kernel fn-lgt-recover fn-lgk-recover
                                     fn-lgk-inflight fn-lgk-make))))

(defthm fn-lgob-recover-run-keeps-the-kernel
  (implies (assoc-equal ino (fn-bs-inodes bs))
           (let ((final (car (last (fn-lg-run bs ks (fn-lg-recover-program) nil ino)))))
             (and (equal (cdr final) ks)
                  (fn-bs-shapep (car final)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-lg-step fn-bs-write fn-bs-fsync-file fn-bs-fence-file)
                           (fn-bs-durable-content fn-bs-zeros fn-bs-apply-ops)))))

; The recovery program ends with the segment's fence, which leaves nothing of
; the segment pending, so fencing it again changes nothing: the only premise
; is that the segment's inode exists (otherwise the program's first write is
; refused with :ebadf and the run stops before its fence).  The statement
; once carried six more hypotheses -- a positive unit, a unit-aligned true
; content, a digest genesis, the owner's sole-pending-writer obligation and
; no pending write of the segment -- which R needed and the conclusion does
; not (lane audit-fixes, keystone-audit G4-7: this weakened theorem was
; proved, so they were removed).

(local
 (defthm fn-lgob-ops-for-ino-of-not-for-ino
   (equal (fn-bs-ops-for-ino (fn-bs-ops-not-for-ino ops ino) ino) nil)))

(local
 (defthm fn-lgob-ops-not-for-ino-idempotent
   (equal (fn-bs-ops-not-for-ino (fn-bs-ops-not-for-ino ops ino) ino)
          (fn-bs-ops-not-for-ino ops ino))))

(local
 (defthm fn-lgob-fence-file-idempotent
   (equal (fn-bs-fence-file (fn-bs-fence-file s ino) ino)
          (fn-bs-fence-file s ino))
   :hints (("Goal" :in-theory (enable fn-bs-fence-file)))))

(defthm fn-lgob-recovered-segment-fence-is-identity
  (let* ((ks (fn-lg-recovered-kernel bs ino genesis max floor))
         (final (car (last (fn-lg-run bs ks (fn-lg-recover-program) nil ino)))))
    (implies (assoc-equal ino (fn-bs-inodes bs))
             (equal (fn-lg-step (car final) (cdr final) '(:fence :segment :tail) :ok ino)
                    (mv :ok (car final) (cdr final)))))
  :hints (("Goal" :do-not-induct t
           :expand ((:free (bs ks steps outcomes) (fn-lg-run bs ks steps outcomes ino)))
           :in-theory (e/d (fn-lg-step fn-bs-fsync-file fn-bs-write fn-lg-recover-program)
                           (fn-bs-fence-file fn-lg-recovered-kernel fn-bs-durable-content
                            fn-bs-zeros fn-bs-take)))))

; -----------------------------------------------------------------------------
; Why one barrier is not enough.

(local
 (defthm fn-lgob-ops-not-for-ino-keeps-entry-operations
   (implies (and (member-equal op ops) (not (equal (car op) :write)))
            (member-equal op (fn-bs-ops-not-for-ino ops ino)))))

; A file fence drains that inode's writes only: every pending directory entry
; operation (a create's or link's :set-entry, an unlink's :del-entry, a
; rename's pair) is still pending after it, so a crash may drop it
; (fn-bs-crash-choicep: :drop is a choice for every non-write).
(defthm fn-lgob-file-fence-keeps-entry-operations
  (implies (and (member-equal op (fn-bs-pending s))
                (not (equal (car op) :write)))
           (member-equal op (fn-bs-pending (fn-bs-fence-file s ino))))
  :hints (("Goal" :in-theory (enable fn-bs-fence-file))))

; The ground witness.  Segment 1 durable in journal/; the process died at
; rotate-created (000002.log created, its name pending in journal/).  The
; next open recovers 000002.log (the highest index) with ONE barrier, the
; segment's fence; a batch is written and fenced (P-BATCH: acknowledged).
(defun fn-lgob-rotated-store ()
  (declare (xargs :guard t :verify-guards nil))
  (mv-let (r s)
    (fn-bs-create (fn-bs-make 4 '((1 . (0 0 0 0))) '((:journal ("000001.log" . 1))) nil 2)
                  :journal "000002.log" :ok)
    (declare (ignore r))
    s))

(defun fn-lgob-write (s ino octets)
  (declare (xargs :guard t :verify-guards nil))
  (mv-let (r s1) (fn-bs-write s ino 0 octets :ok) (declare (ignore r)) s1))
(defun fn-lgob-fsync-file (s ino)
  (declare (xargs :guard t :verify-guards nil))
  (mv-let (r s1) (fn-bs-fsync-file s ino :ok) (declare (ignore r)) s1))
(defun fn-lgob-fsync-dir (s dir)
  (declare (xargs :guard t :verify-guards nil))
  (mv-let (r s1) (fn-bs-fsync-dir s dir :ok) (declare (ignore r)) s1))

(defun fn-lgob-acked-batch (journal-fence)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((s (fn-lgob-rotated-store))
         ;; P-LOG-RECOVER: the tail zeroed and fenced (the one barrier).
         (s (fn-lgob-fsync-file (fn-lgob-write s 2 '(0 0 0 0)) 2))
         (s (if journal-fence (fn-lgob-fsync-dir s :journal) s))
         ;; P-BATCH: the entry written and fenced; the member acknowledged.
         (s (fn-lgob-write s 2 '(7 7 7 7))))
    (fn-lgob-fsync-file s 2)))

(defthm fn-lgob-one-barrier-loses-a-rotated-segment
  (let* ((s (fn-lgob-acked-batch nil))
         (image (fn-bs-crash s '(:drop))))
    (and (equal (fn-bs-pending s) '((:set-entry :journal "000002.log" 2)))
         (fn-bs-crash-choicesp '(:drop) (fn-bs-pending s) (fn-bs-unit s))
         (fn-bs-crash-imagep s image)
         (equal (fn-bs-durable-content image 2) '(7 7 7 7))
         (null (fn-bs-durable-entry image :journal "000002.log"))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-bs-crash-imagep-suff
                                   (s (fn-lgob-acked-batch nil))
                                   (choices '(:drop))
                                   (image (fn-bs-crash (fn-lgob-acked-batch nil) '(:drop))))))))

(defthm fn-lgob-journal-fence-keeps-the-rotated-segment
  (let ((s (fn-lgob-acked-batch t)))
    (and (null (fn-bs-pending s))
         (implies (fn-bs-crash-imagep s image)
                  (and (equal (fn-bs-durable-entry image :journal "000002.log") 2)
                       (equal (fn-bs-durable-content image 2) '(7 7 7 7))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-bs-crash-imagep fn-bs-crash fn-bs-crash-select))))
