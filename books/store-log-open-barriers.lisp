; fn: which of the format-9 open's recovery barriers the byte model needs
; (lane log-recovery-2, item 3, 2026-09-27).
;
; host/native/io.lisp fnn-recover-log runs the open's recovery
; (P-LOG-RECOVER-COPY since RL-01 A2: books/store-log-recover-copy.lisp; it
; leaves nothing pending, fn-lgrc-attempt-makes-the-read-prefix-durable) and
; then the five recovery barriers of fnn-store-recovery-barriers
; (config.json, the segment, journal/, the root, its parent), counted by
; books/store-files.lisp *fn-sf-recovery-barrier-count*.  The design
; (planning/design-2026-09-27-storage-log.md section 3.5) names ONE recovery
; barrier: the segment's fence after the truncation.  This book settles which
; of the six fences the byte model (books/byte-store.lisp) needs.
;
;   fn-lgob-duplicate-segment-fence-is-identity   the second barrier (the
;       segment again) is the identity on a related state with nothing in
;       flight: after P-LOG-RECOVER nothing is pending, so it fences nothing.
;   fn-lgob-three-barrier-open-after-the-copy-is-the-five   at the state
;       the host holds after fnn-log-recover (nothing pending), the three
;       barriers' cut states are the five's.
;   fn-lgob-file-fence-keeps-entry-operations      a file fence never drains a
;       pending directory entry: a create or rename into journal/ (P-ROTATE's
;       rotate-renamed, init's init-segment-created), a rename into the root
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
; What the model needs at the open, then: the segment (the copy's own
; fence), journal/ (a create or unlink in flight at a death in P-ROTATE,
; P-DROP or init) and the parent (an import at import-published, init before
; init-parent-fenced).  The root's barrier was for the open's drop of covered
; segments after a checkpoint renamed but not fenced; the open no longer
; drops (RL-01-CHECKPOINT-NAME-BEFORE-DROP, books/store-log-recover-copy.lisp
; fn-lgrc-open-unlinks-no-segment), so no counterexample here needs the root
; barrier; it stays in the host's program until its removal is stated and
; proved.  The second barrier (the
; segment) is redundant (the theorems here); config.json is written only by
; init's publication and the import's staging, each of which fences its data
; before it is named (books/byte-store-initializer.lisp fn-bsi-publish-steps,
; books/store-import-publication.lisp fn-bs-imp-file-steps), so its barrier
; fences nothing on a reachable state (argued, not proved here).
(in-package "ACL2")
(include-book "store-log-programs")
(include-book "store-log-route-programs")
(include-book "store-import-publication")

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

; The kernel the open recovers has nothing in flight.
(defthm fn-lgob-recovered-kernel-has-nothing-in-flight
  (not (consp (fn-lgk-inflight (fn-lg-recovered-kernel bs ino genesis max floor))))
  :hints (("Goal" :in-theory (enable fn-lg-recovered-kernel fn-lgt-recover fn-lgk-recover
                                     fn-lgk-inflight fn-lgk-make))))

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
; P-LOG-RECOVER-COPY, three recovery barriers: journal/, the root, the root's
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
;   the segment half of the keystone's hypotheses: P-LOG-RECOVER-COPY leaves
;       nothing pending at log-recovered (books/store-log-recover-copy.lisp
;       fn-lgrc-attempt-makes-the-read-prefix-durable).
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
;   fn-lgob-three-barrier-open-after-the-copy-is-the-five   the keystone
;       at the state the copy leaves (nothing pending): the open as the host
;       runs it.
;
; Teeth: tests/acl2/store-log-open-barriers-tests.lisp: a reachable witness
; (the rotated store after the open's copy), and per hypothesis a state that
; fails it where the two opens differ.  And journal/'s and the parent's
; barriers cannot go: one ground counterexample per omitted barrier, each a
; two-barrier open losing an acknowledged or published state to a power cut
; (the root's had one while the open dropped covered segments; see above):
;
;   fn-lgob-one-barrier-loses-a-rotated-segment (above) and
;   fn-lgob-two-barriers-without-journal-lose-a-rotated-segment
;       the root and the parent fenced, not journal/: a death at
;       rotate-created, a batch fenced (acknowledged), its segment unnamed.
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
                  (list* s s (fn-lgob-cut-states s (fn-lg-open-program) seg cfg))))
  :hints (("Goal" :in-theory (disable fn-bs-fence-dir fn-bs-fence-file fn-bs-fencedp))))

; The same, as sets: a state is a cut state of the five-barrier open exactly
; when it is one of the three-barrier open.
(defthm fn-lgob-three-and-five-barrier-opens-have-the-same-cut-states
  (implies (and (fn-bs-shapep s) (true-listp (fn-bs-pending s))
                (fn-bs-fencedp s seg) (fn-bs-fencedp s cfg))
           (iff (member-equal x (fn-lgob-cut-states s *fn-lgob-five-barrier-suffix* seg cfg))
                (member-equal x (fn-lgob-cut-states s (fn-lg-open-program) seg cfg))))
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

; KEYSTONE, composed: the open as the host runs it.  The copy leaves nothing
; pending (books/store-log-recover-copy.lisp fn-lgrc-attempt-makes-the-read-
; prefix-durable); from such a store the five barriers leave, at every
; process-death cut, the states the three barriers leave.
(defthm fn-lgob-three-barrier-open-after-the-copy-is-the-five
  (implies (and (fn-bs-shapep s) (null (fn-bs-pending s)))
           (equal (fn-lgob-cut-states s *fn-lgob-five-barrier-suffix* seg cfg)
                  (list* s s (fn-lgob-cut-states s (fn-lg-open-program) seg cfg))))
  :hints (("Goal" :use ((:instance fn-lgob-three-barrier-open-is-the-five-at-every-cut))
           :in-theory (e/d (fn-bs-fencedp)
                           (fn-lgob-three-barrier-open-is-the-five-at-every-cut
                            fn-lgob-cut-states fn-bs-fence-dir fn-bs-fence-file)))))

; -----------------------------------------------------------------------------
; Why journal/'s and the parent's barriers cannot go: one ground
; counterexample per omitted barrier.

(defun fn-lgob-rename (s sdir sname ddir dname)
  (declare (xargs :guard t :verify-guards nil))
  (mv-let (r s1) (fn-bs-rename s sdir sname ddir dname :ok) (declare (ignore r)) s1))

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
