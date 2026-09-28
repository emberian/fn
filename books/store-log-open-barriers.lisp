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
(include-book "store-log-route-programs")
(include-book "store-import-publication")

;; Rules withdrawn at their source that this book's proofs use
;; (lane rule-hygiene, tools/rule_cost.py).
(local (in-theory (enable (:rewrite fn-lgc-take-all))))

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

; -----------------------------------------------------------------------------
; Three barriers, not five (lane open-barriers, 2026-09-27).
;
; fn-lg-open-program (books/store-log-route-programs.lisp) now runs, after
; P-LOG-RECOVER, three recovery barriers: journal/, the root, the root's
; parent (host/native/io.lisp fnn-store-recovery-barriers;
; *fn-sf-recovery-barrier-count* 3 in books/store-files.lisp).  The five it
; replaces are kept here as a constant, the "before".  Read over the byte
; store (fn-lg-step holds only the segment), a barrier is a file fence of its
; inode (the config file, the segment) or a directory fence (journal/, the
; root, its parent); a cut is no step.
;
;   fn-lgob-three-barrier-open-is-the-five-at-every-cut   KEYSTONE.  From any
;       byte state in which the segment and the config file have no pending
;       write, the byte state at each process-death cut of the five-barrier
;       open is the state at a cut of the three-barrier open, and conversely:
;       the five's cut states are the three's with the recovered state
;       repeated twice in front (the two dropped fences change nothing).  So
;       a process death or a power cut at any cut of either open leaves the
;       same set of states and crash images.
;   fn-lgob-recovered-state-meets-the-segment-hypothesis   P-LOG-RECOVER's own
;       fence leaves the segment with no pending write and a config file with
;       none still with none: at log-recovered, the segment half of the
;       keystone's hypotheses holds for every store whose segment exists.
;       (Two hypotheses the first statement carried, a true-list pending
;       list and a config inode other than the segment, were redundant: the
;       weakened statement was proved and they are gone.)
;   fn-lgob-only-a-write-unfences-a-file   the config half: of every byte
;       syscall, only a write of the inode adds a pending write of it.  The
;       config file's only writes are its publication's (init: host/native/
;       io.lisp fnn-publish-initial-file, books/byte-store-initializer.lisp
;       fn-bsi-publish-steps; the in-stage writes of the staged init and the
;       import, books/store-import-publication.lisp fn-bs-imp-file-steps), each
;       followed by that inode's fsync before its name is published; no
;       other host code writes config.json (fnn-config-path's only writers;
;       a profile change is a configuration record in the log).  So at every
;       process-death cut a later open can start from, the config file has
;       no pending write (argued from the host source, not proved here).
;   fn-lgob-three-barrier-open-after-recovery-is-the-five   the keystone
;       composed with P-LOG-RECOVER: the open as the host runs it, from any
;       store whose segment exists and whose config file has no pending
;       write.
;
; Teeth: tests/acl2/store-log-open-barriers-tests.lisp: a reachable witness
; (the rotated store after P-LOG-RECOVER), and per hypothesis a state that
; fails it where the two opens differ.  And none of the three can go: one
; ground counterexample per omitted barrier, each a two-barrier open losing an
; acknowledged or published state to a power cut:
;
;   fn-lgob-one-barrier-loses-a-rotated-segment (above) and
;   fn-lgob-two-barriers-without-journal-lose-a-rotated-segment
;       the root and the parent fenced, not journal/: a death at
;       rotate-created, a batch fenced (acknowledged), its segment unnamed.
;   fn-lgob-two-barriers-without-root-lose-a-checkpointed-history
;       journal/ and the parent fenced, not the root: a death after a state
;       checkpoint's rename and before its root fence; the open's drop of the
;       segments it covers (unlinked, journal/ fenced) lands, the checkpoint's
;       name does not: neither the checkpoint nor the history it covers.
;   fn-lgob-two-barriers-without-parent-lose-an-imported-store
;       journal/ and the root fenced, not the parent: a death at
;       import-published (the stage renamed to the store's name, the parent
;       not fenced); a batch fenced (acknowledged); the store's name is lost.
; with a control for each (the three barriers: every crash image keeps it).

(defconst *fn-lgob-five-barrier-suffix*
  '((:cut "recover-replayed")
    (:fence :config) (:cut "recover-barrier")
    (:fence :segment :tail) (:cut "recover-barrier")
    (:fence :journal) (:cut "recover-barrier")
    (:fence :root) (:cut "recover-barrier")
    (:fence :parent) (:cut "recover-barrier")))

(defun fn-lgob-bytes-step (s step seg cfg)
  (declare (xargs :guard t :verify-guards nil))
  (cond ((equal step '(:fence :segment :tail)) (fn-bs-fence-file s seg))
        ((equal step '(:fence :config)) (fn-bs-fence-file s cfg))
        ((and (consp step) (equal (car step) :fence) (consp (cdr step))
              (member-equal (cadr step) '(:journal :root :parent)))
         (fn-bs-fence-dir s (cadr step)))
        (t s)))

; The byte state at each process-death cut of STEPS, in order.
(defun fn-lgob-cut-states (s steps seg cfg)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp steps)
      (let ((s1 (fn-lgob-bytes-step s (car steps) seg cfg)))
        (if (and (consp (car steps)) (equal (car (car steps)) :cut))
            (cons s1 (fn-lgob-cut-states s1 (cdr steps) seg cfg))
          (fn-lgob-cut-states s1 (cdr steps) seg cfg)))
    nil))

(local
 (defthm fn-lgob-make-of-own-fields-any-pending
   (implies (fn-bs-shapep bs)
            (equal (fn-bs-make (fn-bs-unit bs) (fn-bs-inodes bs) (fn-bs-dirs bs)
                               (fn-bs-pending bs) (fn-bs-next-ino bs))
                   bs))
   :hints (("Goal" :in-theory (enable fn-bs-make fn-bs-shapep fn-bs-unit fn-bs-inodes
                                      fn-bs-dirs fn-bs-pending fn-bs-next-ino)
            :expand ((len bs) (len (cdr bs)) (len (cddr bs)) (len (cdddr bs))
                     (len (cddddr bs)) (len (cdr (cddddr bs))))))))

(local
 (defthm fn-lgob-ops-not-for-ino-when-none-for-ino
   (implies (and (true-listp ops) (not (fn-bs-ops-for-ino ops ino)))
            (equal (fn-bs-ops-not-for-ino ops ino) ops))))

; A file fence of an inode with no pending write is the identity.
(defthm fn-lgob-fence-of-a-fenced-file-is-identity
  (implies (and (fn-bs-shapep s) (true-listp (fn-bs-pending s)) (fn-bs-fencedp s ino))
           (equal (fn-bs-fence-file s ino) s))
  :hints (("Goal" :in-theory (enable fn-bs-fence-file fn-bs-fencedp))))

(defthm fn-lgob-three-barrier-open-is-the-five-at-every-cut
  (implies (and (fn-bs-shapep s) (true-listp (fn-bs-pending s))
                (fn-bs-fencedp s seg) (fn-bs-fencedp s cfg))
           (equal (fn-lgob-cut-states s *fn-lgob-five-barrier-suffix* seg cfg)
                  (list* s s (fn-lgob-cut-states s (fn-lg-open-suffix) seg cfg))))
  :hints (("Goal" :in-theory (disable fn-bs-fence-dir fn-bs-fence-file fn-bs-fencedp))))

; The same, as sets: a state is a cut state of the five-barrier open exactly
; when it is one of the three-barrier open.
(defthm fn-lgob-three-and-five-barrier-opens-have-the-same-cut-states
  (implies (and (fn-bs-shapep s) (true-listp (fn-bs-pending s))
                (fn-bs-fencedp s seg) (fn-bs-fencedp s cfg))
           (iff (member-equal x (fn-lgob-cut-states s *fn-lgob-five-barrier-suffix* seg cfg))
                (member-equal x (fn-lgob-cut-states s (fn-lg-open-suffix) seg cfg))))
  :hints (("Goal" :use fn-lgob-three-barrier-open-is-the-five-at-every-cut
           :in-theory (disable fn-lgob-three-barrier-open-is-the-five-at-every-cut
                               fn-bs-fence-dir fn-bs-fence-file fn-bs-fencedp))))

(local
 (defthm fn-lgob-ops-for-ino-of-append
   (equal (fn-bs-ops-for-ino (append a b) ino)
          (append (fn-bs-ops-for-ino a ino) (fn-bs-ops-for-ino b ino)))))

(local
 (defthm fn-lgob-ops-for-ino-of-not-for-other
   (equal (fn-bs-ops-for-ino (fn-bs-ops-not-for-ino ops other) ino)
          (if (equal ino other) nil (fn-bs-ops-for-ino ops ino)))))

(local
 (defthm fn-lgob-ops-for-ino-of-dir-ops
   (and (implies (not (fn-bs-ops-for-ino ops ino))
                 (not (fn-bs-ops-for-ino (fn-bs-ops-not-for-dir ops dir) ino))))))

(local
 (defthm fn-lgob-true-listp-of-not-for-ino
   (true-listp (fn-bs-ops-not-for-ino ops ino))))

; Of every byte syscall, only a write of INO adds a pending write of it:
; a create, link, rename, unlink or mkdir adds entry operations, a file or
; directory fence (any outcome) removes operations, and a write of another
; inode adds that inode's write.
(defthm fn-lgob-only-a-write-unfences-a-file
  (implies (fn-bs-fencedp s ino)
           (and (fn-bs-fencedp (mv-nth 1 (fn-bs-create s dir name outcome)) ino)
                (fn-bs-fencedp (mv-nth 1 (fn-bs-link s sdir sname ddir dname outcome)) ino)
                (fn-bs-fencedp (mv-nth 1 (fn-bs-rename s sdir sname ddir dname outcome)) ino)
                (fn-bs-fencedp (mv-nth 1 (fn-bs-unlink s dir name outcome)) ino)
                (fn-bs-fencedp (mv-nth 1 (fn-bs-mkdir s parent name id outcome)) ino)
                (fn-bs-fencedp (mv-nth 1 (fn-bs-fsync-file s other outcome)) ino)
                (fn-bs-fencedp (mv-nth 1 (fn-bs-fsync-dir s dir outcome)) ino)
                (implies (not (equal other ino))
                         (fn-bs-fencedp (mv-nth 1 (fn-bs-write s other offset octets outcome))
                                        ino))))
  :hints (("Goal" :in-theory (enable fn-bs-fencedp fn-bs-create fn-bs-link fn-bs-rename
                                     fn-bs-unlink fn-bs-mkdir fn-bs-fsync-file fn-bs-fsync-dir
                                     fn-bs-write fn-bs-fence-file fn-bs-fence-dir))))

(defthm fn-lgob-recovered-state-meets-the-segment-hypothesis
  (let* ((ks (fn-lg-recovered-kernel bs ino genesis max floor))
         (final (car (car (last (fn-lg-run bs ks (fn-lg-recover-program) nil ino))))))
    (implies (and (assoc-equal ino (fn-bs-inodes bs))
                  (fn-bs-fencedp bs cfg))
             (and (fn-bs-shapep final)
                  (true-listp (fn-bs-pending final))
                  (fn-bs-fencedp final ino)
                  (fn-bs-fencedp final cfg))))
  :hints (("Goal" :do-not-induct t
           :expand ((:free (bs ks steps outcomes) (fn-lg-run bs ks steps outcomes ino)))
           :in-theory (e/d (fn-lg-step fn-bs-fsync-file fn-bs-write fn-lg-recover-program
                            fn-bs-fence-file fn-bs-fencedp)
                           (fn-lg-recovered-kernel fn-bs-durable-content
                            fn-bs-zeros fn-bs-take)))))

; KEYSTONE, composed: the open as the host runs it.  From any store whose
; segment exists and whose config file has no pending write, P-LOG-RECOVER to
; log-recovered and then the five barriers leave, at every process-death cut,
; the states the three barriers leave.
(defthm fn-lgob-three-barrier-open-after-recovery-is-the-five
  (let* ((ks (fn-lg-recovered-kernel bs ino genesis max floor))
         (final (car (car (last (fn-lg-run bs ks (fn-lg-recover-program) nil ino))))))
    (implies (and (assoc-equal ino (fn-bs-inodes bs))
                  (fn-bs-fencedp bs cfg))
             (equal (fn-lgob-cut-states final *fn-lgob-five-barrier-suffix* ino cfg)
                    (list* final final
                           (fn-lgob-cut-states final (fn-lg-open-suffix) ino cfg)))))
  :hints (("Goal" :use (fn-lgob-recovered-state-meets-the-segment-hypothesis
                        (:instance fn-lgob-three-barrier-open-is-the-five-at-every-cut
                                   (s (car (car (last (fn-lg-run bs (fn-lg-recovered-kernel bs ino genesis max floor)
                                                                 (fn-lg-recover-program) nil ino)))))
                                   (seg ino)))
           :in-theory (disable fn-lgob-recovered-state-meets-the-segment-hypothesis
                               fn-lgob-three-barrier-open-is-the-five-at-every-cut
                               fn-lg-run fn-lg-recovered-kernel fn-lgob-cut-states
                               fn-lg-open-suffix fn-bs-fencedp))))

; -----------------------------------------------------------------------------
; Why none of the three can go: one ground counterexample per omitted barrier.

(defun fn-lgob-rename (s sdir sname ddir dname)
  (declare (xargs :guard t :verify-guards nil))
  (mv-let (r s1) (fn-bs-rename s sdir sname ddir dname :ok) (declare (ignore r)) s1))
(defun fn-lgob-unlink (s dir name)
  (declare (xargs :guard t :verify-guards nil))
  (mv-let (r s1) (fn-bs-unlink s dir name :ok) (declare (ignore r)) s1))

; The open's recovery barriers DIRS, each fsync(dir) answering :ok.
(defun fn-lgob-open-fences (s dirs)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp dirs)
      (fn-lgob-open-fences (fn-lgob-fsync-dir s (car dirs)) (cdr dirs))
    s))

; P-LOG-RECOVER of segment SEG (the tail zeroed and fenced), the open's
; barriers DIRS, then P-BATCH: a batch written and fenced, acknowledged.
(defun fn-lgob-open-then-batch (s seg dirs)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((s (fn-lgob-fsync-file (fn-lgob-write s seg '(0 0 0 0)) seg))
         (s (fn-lgob-open-fences s dirs))
         (s (fn-lgob-write s seg '(7 7 7 7))))
    (fn-lgob-fsync-file s seg)))

; journal/ omitted: a death at rotate-created (fn-lgob-rotated-store); the
; open fences the root and the parent.
(defthm fn-lgob-two-barriers-without-journal-lose-a-rotated-segment
  (let* ((s (fn-lgob-open-then-batch (fn-lgob-rotated-store) 2 '(:root :parent)))
         (image (fn-bs-crash s '(:drop))))
    (and (equal (fn-bs-pending s) '((:set-entry :journal "000002.log" 2)))
         (fn-bs-crash-choicesp '(:drop) (fn-bs-pending s) (fn-bs-unit s))
         (fn-bs-crash-imagep s image)
         (equal (fn-bs-durable-content image 2) '(7 7 7 7))
         (null (fn-bs-durable-entry image :journal "000002.log"))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-bs-crash-imagep-suff
                                   (s (fn-lgob-open-then-batch (fn-lgob-rotated-store) 2
                                                               '(:root :parent)))
                                   (choices '(:drop))
                                   (image (fn-bs-crash (fn-lgob-open-then-batch
                                                        (fn-lgob-rotated-store) 2 '(:root :parent))
                                                       '(:drop))))))))

(defthm fn-lgob-three-barriers-keep-the-rotated-segment
  (let ((s (fn-lgob-open-then-batch (fn-lgob-rotated-store) 2 '(:journal :root :parent))))
    (and (null (fn-bs-pending s))
         (implies (fn-bs-crash-imagep s image)
                  (and (equal (fn-bs-durable-entry image :journal "000002.log") 2)
                       (equal (fn-bs-durable-content image 2) '(7 7 7 7))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-bs-crash-imagep fn-bs-crash fn-bs-crash-select))))

; The root omitted.  Segment 1 holds the history (octets 1 1 1 1) and a state
; checkpoint covering it (inode 5) was staged, fenced and renamed into the
; root (its name there fn-store-sco-file-name's; "checkpoint" here) when the
; process died, before the root's fence.  The next open fences journal/ and
; the parent, not the root, and drops the covered segment (P-DROP: unlink,
; journal/ fenced).  A power cut then keeps the drop and loses the rename:
; neither the checkpoint nor the segment it covers has a durable name.
(defun fn-lgob-checkpointed-store ()
  (declare (xargs :guard t :verify-guards nil))
  (fn-lgob-rename (fn-bs-make 4 '((5 . (9 9 9 9)) (1 . (1 1 1 1)))
                              '((:staging (".checkpoint-stage" . 5))
                                (:root ("journal" . :journal) ("staging" . :staging))
                                (:journal ("000001.log" . 1)))
                              nil 6)
                  :staging ".checkpoint-stage" :root "checkpoint"))

(defun fn-lgob-open-then-drop (dirs)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((s (fn-lgob-open-fences (fn-lgob-checkpointed-store) dirs))
         (s (fn-lgob-unlink s :journal "000001.log")))
    (fn-lgob-fsync-dir s :journal)))

(defthm fn-lgob-two-barriers-without-root-lose-a-checkpointed-history
  (let* ((s (fn-lgob-open-then-drop '(:journal :parent)))
         (image (fn-bs-crash s '(:drop :drop))))
    (and (equal (fn-bs-pending s) '((:set-entry :root "checkpoint" 5)
                                    (:del-entry :staging ".checkpoint-stage")))
         (fn-bs-crash-choicesp '(:drop :drop) (fn-bs-pending s) (fn-bs-unit s))
         (fn-bs-crash-imagep s image)
         (null (fn-bs-durable-entry image :root "checkpoint"))
         (null (fn-bs-durable-entry image :journal "000001.log"))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-bs-crash-imagep-suff
                                   (s (fn-lgob-open-then-drop '(:journal :parent)))
                                   (choices '(:drop :drop))
                                   (image (fn-bs-crash (fn-lgob-open-then-drop '(:journal :parent))
                                                       '(:drop :drop))))))))

(defthm fn-lgob-three-barriers-keep-the-checkpoint
  (let ((s (fn-lgob-open-then-drop '(:journal :root :parent))))
    (and (equal (fn-bs-pending s) '((:del-entry :staging ".checkpoint-stage")))
         (implies (fn-bs-crash-imagep s image)
                  (and (equal (fn-bs-durable-entry image :root "checkpoint") 5)
                       (equal (fn-bs-durable-content image 5) '(9 9 9 9))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-bs-crash-imagep fn-bs-crash fn-bs-crash-select))))

; The parent omitted.  An import died at import-published: its stage (a
; complete store, segment 1 zeroed) renamed to the store's name in the
; parent (books/store-import-publication.lisp fn-bs-rename-dir-noreplace), the
; parent not fenced.  The next open fences journal/ and the root,
; not the parent; a batch is written and fenced (acknowledged).  A power cut
; keeps the stage name's removal and loses the rename: the acknowledged
; batch is durable in a store no durable name reaches.
(defun fn-lgob-imported-store ()
  (declare (xargs :guard t :verify-guards nil))
  (mv-let (r s)
    (fn-bs-rename-dir-noreplace (fn-bs-make 4 '((1 . (0 0 0 0)))
                                            '((:parent (".import-stage" . :root))
                                              (:root ("journal" . :journal))
                                              (:journal ("000001.log" . 1)))
                                            nil 2)
                                :parent ".import-stage" :parent "store" :ok)
    (declare (ignore r))
    s))

(defthm fn-lgob-two-barriers-without-parent-lose-an-imported-store
  (let* ((s (fn-lgob-open-then-batch (fn-lgob-imported-store) 1 '(:journal :root)))
         (image (fn-bs-crash s '(:drop :apply))))
    (and (equal (fn-bs-pending s) '((:set-entry :parent "store" :root)
                                    (:del-entry :parent ".import-stage")))
         (fn-bs-crash-choicesp '(:drop :apply) (fn-bs-pending s) (fn-bs-unit s))
         (fn-bs-crash-imagep s image)
         (equal (fn-bs-durable-content image 1) '(7 7 7 7))
         (null (fn-bs-durable-entry image :parent "store"))
         (null (fn-bs-durable-entry image :parent ".import-stage"))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-bs-crash-imagep-suff
                                   (s (fn-lgob-open-then-batch (fn-lgob-imported-store) 1
                                                               '(:journal :root)))
                                   (choices '(:drop :apply))
                                   (image (fn-bs-crash (fn-lgob-open-then-batch
                                                        (fn-lgob-imported-store) 1 '(:journal :root))
                                                       '(:drop :apply))))))))

(defthm fn-lgob-three-barriers-keep-the-imported-store
  (let ((s (fn-lgob-open-then-batch (fn-lgob-imported-store) 1 '(:journal :root :parent))))
    (and (null (fn-bs-pending s))
         (implies (fn-bs-crash-imagep s image)
                  (and (equal (fn-bs-durable-entry image :parent "store") :root)
                       (equal (fn-bs-durable-content image 1) '(7 7 7 7))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-bs-crash-imagep fn-bs-crash fn-bs-crash-select))))
