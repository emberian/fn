; fn: `store export' durability over the byte model (lane
; obligations-paged-archive, 2026-09-28; PRF-370).  Prefix `fn-sxd-'.
;
; The export fsynced every archive entry as it wrote it: on hbox's ZFS about
; 40 files a second, so a 1,000,000-record archive took hours (lane
; scale-reads-export).  COORDINATOR DECISION (2026-09-28): the archive's data
; files share ONE sync at the end, provided the MANIFEST is written and
; synced LAST -- an archive counts as complete only once its MANIFEST is
; durable, and a crash before that leaves an archive the import refuses by
; name as incomplete.
;
; The program, in the host's order (host/native/io.lisp
; fnn-command-store-export), inside the archive directory DIR (the model's
; :arch; DIR itself is the export's own fresh directory):
;   1. mkdir config/ and records/; create MANIFEST.partial;
;   2. for every entry (profile, frontier, config/NAME, records/NAME): create
;      it and write its octets, no fsync (cut export-entry-written); the
;      MANIFEST's lines are written into MANIFEST.partial;
;   3. ONE sync of the filesystem (Linux syncfs(2); the step :sync-all drains
;      every pending operation, and a failure lands any torn selection and
;      discards the rest, as a failed fsync does);
;   4. fsync MANIFEST.partial, records/ and config/ (redundant after 3, and
;      the whole barrier where 3 is not available), rename MANIFEST.partial
;      onto MANIFEST, fsync DIR.
; The host writes the MANIFEST's lines as the chunks go; the model writes
; them in one write before the sync.  Nothing written before the sync is
; durable in the model until the sync, so the two agree on every crash image
; the claims below read.
;
; KEYSTONE fn-sxd-crash-is-incomplete-or-complete: a crash at ANY point of
; ANY run of the program, with ANY outcome of any syscall and any selection
; of what landed, leaves either no MANIFEST (the import refuses the archive by
; name, archive-incomplete: fn-sxd-archive-verdict) or the MANIFEST bound to
; the file the export wrote its lines into, holding exactly those lines, with
; every entry bound to a file holding exactly its octets.
;
; KEYSTONE fn-sxd-import-verdict-is-incomplete-or-complete: the verdict the
; import takes on the MANIFEST's presence (host/native/io.lisp
; fnn-import-pass calls fn-sxd-archive-verdict) over every such crash image
; is :archive-incomplete, or :read over the complete archive.

(in-package "ACL2")
(include-book "byte-store-invariants")

(defconst *fn-sxd-partial* "MANIFEST.partial")
(defconst *fn-sxd-manifest* "MANIFEST")

; The import's verdict on the archive's MANIFEST entry: absent is an
; incomplete archive, refused by that name before anything is read.
(defun fn-sxd-archive-verdict (manifest-present)
  (declare (xargs :guard t))
  (if manifest-present :read :archive-incomplete))

; -----------------------------------------------------------------------------
; The steps: the byte model's syscalls, and the filesystem sync.

; syncfs(2): every pending operation drains.  A failure (ERRNO . CHOICES)
; lands the torn selection CHOICES and discards the rest (the dirty pages are
; marked clean, as a failed fsync's are).
(defun fn-sxd-sync-all (s outcome)
  (declare (xargs :guard t :verify-guards nil))
  (mv-let (inodes dirs)
    (fn-bs-apply-ops (fn-bs-inodes s) (fn-bs-dirs s)
                     (if (equal outcome :ok)
                         (fn-bs-pending s)
                       (fn-bs-crash-select (fn-bs-pending s)
                                           (if (consp outcome) (cdr outcome) nil)
                                           (fn-bs-unit s))))
    (mv (if (equal outcome :ok) :ok (if (consp outcome) (car outcome) outcome))
        (fn-bs-make (fn-bs-unit s) inodes dirs nil (fn-bs-next-ino s)))))

(defun fn-sxd-step (s step outcome)
  (declare (xargs :guard t :verify-guards nil))
  (case (car step)
    (:mkdir (fn-bs-mkdir s (nth 1 step) (nth 2 step) (nth 3 step) outcome))
    (:create (fn-bs-create s (nth 1 step) (nth 2 step) outcome))
    (:write-all (fn-bs-write s (fn-bs-lookup s (nth 1 step) (nth 2 step)) 0
                             (nth 3 step) outcome))
    (:fsync-file (fn-bs-fsync-file s (fn-bs-lookup s (nth 1 step) (nth 2 step)) outcome))
    (:fsync-dir (fn-bs-fsync-dir s (nth 1 step) outcome))
    (:rename (fn-bs-rename s (nth 1 step) (nth 2 step) (nth 3 step) (nth 4 step) outcome))
    (:sync-all (fn-sxd-sync-all s outcome))
    (otherwise (mv :ok s))))

; To the first error, as the host runs: the state after every step.
(defun fn-sxd-run (s steps outcomes)
  (declare (xargs :guard t :verify-guards nil :measure (len steps)))
  (if (consp steps)
      (mv-let (r s1) (fn-sxd-step s (car steps) (if (consp outcomes) (car outcomes) :ok))
        (cons s1 (if (equal r :ok) (fn-sxd-run s1 (cdr steps) (cdr outcomes)) nil)))
    nil))

(defun fn-sxd-okp (s steps outcomes)
  (declare (xargs :guard t :verify-guards nil :measure (len steps)))
  (if (consp steps)
      (mv-let (r s1) (fn-sxd-step s (car steps) (if (consp outcomes) (car outcomes) :ok))
        (and (equal r :ok) (fn-sxd-okp s1 (cdr steps) (cdr outcomes))))
    t))

(defun fn-sxd-final (s steps outcomes)
  (declare (xargs :guard t :verify-guards nil :measure (len steps)))
  (if (consp steps)
      (mv-let (r s1) (fn-sxd-step s (car steps) (if (consp outcomes) (car outcomes) :ok))
        (declare (ignore r))
        (fn-sxd-final s1 (cdr steps) (cdr outcomes)))
    s))

; -----------------------------------------------------------------------------
; The program.  ENTRIES: (DIR NAME . OCTETS), DIR one of :arch (profile,
; frontier), :cfg (config/) and :rec (records/).

(defun fn-sxd-head-steps ()
  (declare (xargs :guard t :verify-guards nil))
  (list (list :mkdir :arch "config" :cfg)
        (list :mkdir :arch "records" :rec)
        (list :create :arch *fn-sxd-partial*)))

(defun fn-sxd-entry-steps (entries)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp entries)
      (let ((e (car entries)))
        (list* (list :create (car e) (cadr e))
               (list :write-all (car e) (cadr e) (cddr e))
               (list :cut "export-entry-written")
               (fn-sxd-entry-steps (cdr entries))))
    nil))

(defun fn-sxd-tail-steps (manifest)
  (declare (xargs :guard t :verify-guards nil))
  (list (list :write-all :arch *fn-sxd-partial* manifest)
        (list :cut "export-data-written")))

(defun fn-sxd-write-program (entries manifest)
  (declare (xargs :guard t :verify-guards nil))
  (append (fn-sxd-head-steps)
          (append (fn-sxd-entry-steps entries)
                  (fn-sxd-tail-steps manifest))))

(defun fn-sxd-publish-program ()
  (declare (xargs :guard t :verify-guards nil))
  (list (list :cut "export-data-durable")
        (list :fsync-file :arch *fn-sxd-partial*)
        (list :fsync-dir :rec)
        (list :fsync-dir :cfg)
        (list :cut "export-manifest-staged")
        (list :rename :arch *fn-sxd-partial* :arch *fn-sxd-manifest*)
        (list :cut "export-manifest-renamed")
        (list :fsync-dir :arch)
        (list :cut "export-durable")))

(defun fn-sxd-program (entries manifest)
  (declare (xargs :guard t :verify-guards nil))
  (append (fn-sxd-write-program entries manifest)
          (cons (list :sync-all) (fn-sxd-publish-program))))

; The environment's answer to one syscall: :ok, or a failure (ERRNO . X)
; whose errno is not :ok (store-import-publication's fn-bs-imp-outcomep).
(defun fn-sxd-outcomep (x)
  (declare (xargs :guard t))
  (or (equal x :ok) (and (consp x) (not (equal (car x) :ok)))))

(defun fn-sxd-outcomesp (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (fn-sxd-outcomep (car xs)) (fn-sxd-outcomesp (cdr xs)))
    t))

; The export's entries: in DIR, config/ or records/, named by strings, never
; DIR's MANIFEST, octets for contents.
(defun fn-sxd-keysp (entries)
  (declare (xargs :guard t))
  (if (consp entries)
      (and (consp (car entries)) (consp (cdar entries))
           (member-equal (caar entries) '(:arch :cfg :rec))
           (stringp (cadar entries))
           (not (and (equal (caar entries) :arch)
                     (equal (cadar entries) *fn-sxd-manifest*)))
           (fn-cbor-octet-listp (cddar entries))
           (fn-sxd-keysp (cdr entries)))
    (null entries)))


; -----------------------------------------------------------------------------
; The proof.

(local (in-theory (enable fn-bs-invariants-vocabulary fn-bs-entry-after)))

(defun fn-sxd-quietp (s)
  (declare (xargs :guard t :verify-guards nil))
  (and (null (fn-bs-ops-for-name (fn-bs-pending s) :arch *fn-sxd-manifest*))
       (null (fn-bs-durable-entry s :arch *fn-sxd-manifest*))))

(defun fn-sxd-step-avoidsp (step)
  (declare (xargs :guard t :verify-guards nil))
  (and (consp step)
       (case (car step)
         ((:cut :write-all :fsync-file :fsync-dir :sync-all) t)
         ((:create :mkdir) (not (and (equal (nth 1 step) :arch)
                                     (equal (nth 2 step) *fn-sxd-manifest*))))
         (otherwise nil))))

(defun fn-sxd-steps-avoidp (steps)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp steps)
      (and (fn-sxd-step-avoidsp (car steps)) (fn-sxd-steps-avoidp (cdr steps)))
    t))

(local
 (defthm fn-sxd-ops-for-name-of-append
   (equal (fn-bs-ops-for-name (append a b) dir name)
          (append (fn-bs-ops-for-name a dir name) (fn-bs-ops-for-name b dir name)))))

(local
 (defthm fn-sxd-ops-for-name-of-selections
   (and (equal (fn-bs-ops-for-name (fn-bs-ops-for-ino ops ino) d n) nil)
        (equal (fn-bs-ops-for-name (fn-bs-ops-not-for-ino ops ino) d n)
               (fn-bs-ops-for-name ops d n))
        (equal (fn-bs-ops-for-name (fn-bs-ops-for-dir ops x) d n)
               (if (equal x d) (fn-bs-ops-for-name ops d n) nil))
        (equal (fn-bs-ops-for-name (fn-bs-ops-not-for-dir ops x) d n)
               (if (equal x d) nil (fn-bs-ops-for-name ops d n))))))

(local
 (defthm fn-sxd-entry-after-of-quiet-name
   (implies (not (fn-bs-ops-for-name ops dir name))
            (equal (fn-bs-entry-after ops old dir name) old))))

(local
 (defthm fn-sxd-ops-for-name-within-dir
   (implies (not (fn-bs-ops-for-dir ops dir))
            (not (fn-bs-ops-for-name ops dir name)))))

(local
 (defthm fn-sxd-ops-for-name-of-tear-write
   (not (fn-bs-ops-for-name (fn-bs-tear-write op sels i unit) dir name))))

(local
 (defthm fn-sxd-ops-for-name-of-crash-select
   (implies (not (fn-bs-ops-for-name ops dir name))
            (not (fn-bs-ops-for-name (fn-bs-crash-select ops choices unit) dir name)))
   :hints (("Goal" :induct (fn-bs-crash-select ops choices unit)
            :in-theory (union-theories '(fn-bs-crash-select fn-bs-ops-for-name
                                         fn-sxd-ops-for-name-of-append
                                         fn-sxd-ops-for-name-of-tear-write
                                         member-equal car-cons cdr-cons (:e equal)
                                         (:e member-equal) (:e binary-append)
                                         (:induction fn-bs-crash-select))
                                       (theory 'minimal-theory))))))

(local
 (defthm fn-sxd-quiet-by-parts
   (equal (fn-sxd-quietp s)
          (and (not (fn-bs-ops-for-name (fn-bs-pending s) :arch *fn-sxd-manifest*))
               (not (cdr (assoc-equal *fn-sxd-manifest*
                                      (cdr (assoc-equal :arch (fn-bs-dirs s))))))))
   :hints (("Goal" :in-theory (enable fn-bs-durable-entry)))))

(local
 (defthm fn-sxd-mkdir-keeps-quiet
   (implies (and (fn-sxd-quietp s)
                 (not (and (equal p :arch) (equal nm *fn-sxd-manifest*))))
            (fn-sxd-quietp (mv-nth 1 (fn-bs-mkdir s p nm id o))))
   :hints (("Goal" :in-theory (union-theories
                               '(fn-sxd-quiet-by-parts fn-bs-mkdir fn-sxd-ops-for-name-of-append
                                 fn-bs-ops-for-name fn-bs-pending-of-fn-bs-make
                                 fn-bs-dirs-of-fn-bs-make assoc-equal member-equal mv-nth
                                 car-cons cdr-cons nth (:e equal) (:e member-equal) (:e nth)
                                 (:e zp) (:e car) (:e cdr) (:e consp)
                                 append-to-nil)
                               (theory 'minimal-theory))))))

(local
 (defthm fn-sxd-create-keeps-quiet
   (implies (and (fn-sxd-quietp s)
                 (not (and (equal d :arch) (equal nm *fn-sxd-manifest*))))
            (fn-sxd-quietp (mv-nth 1 (fn-bs-create s d nm o))))
   :hints (("Goal" :in-theory (union-theories
                               '(fn-sxd-quiet-by-parts fn-bs-create fn-sxd-ops-for-name-of-append
                                 fn-bs-ops-for-name fn-bs-pending-of-fn-bs-make
                                 fn-bs-dirs-of-fn-bs-make member-equal mv-nth
                                 car-cons cdr-cons nth (:e equal) (:e member-equal) (:e nth)
                                 (:e zp) (:e car) (:e cdr) (:e consp) append-to-nil)
                               (theory 'minimal-theory))))))

(local
 (defthm fn-sxd-write-keeps-quiet
   (implies (fn-sxd-quietp s)
            (fn-sxd-quietp (mv-nth 1 (fn-bs-write s ino off oct o))))
   :hints (("Goal" :in-theory (union-theories
                               '(fn-sxd-quiet-by-parts fn-bs-write fn-sxd-ops-for-name-of-append
                                 fn-bs-ops-for-name fn-bs-pending-of-fn-bs-make
                                 fn-bs-dirs-of-fn-bs-make member-equal mv-nth
                                 car-cons cdr-cons nth (:e equal) (:e member-equal) (:e nth)
                                 (:e zp) (:e car) (:e cdr) (:e consp) append-to-nil)
                               (theory 'minimal-theory))))))

(local
 (defthm fn-sxd-quiet-ops-keep-entry
   (implies (and (not (fn-bs-ops-for-name ops :arch *fn-sxd-manifest*))
                 (not (cdr (assoc-equal *fn-sxd-manifest*
                                        (cdr (assoc-equal :arch dirs))))))
            (not (cdr (assoc-equal *fn-sxd-manifest*
                                   (cdr (assoc-equal :arch (fn-bs-apply-entries dirs ops)))))))
   :hints (("Goal" :use ((:instance fn-bs-apply-entries-entry-is-entry-after
                                    (dir :arch) (name *fn-sxd-manifest*)))
            :in-theory (union-theories '(fn-sxd-entry-after-of-quiet-name)
                                       (theory 'minimal-theory))))))

(local
 (defthm fn-sxd-fsync-file-keeps-quiet
   (implies (fn-sxd-quietp s)
            (fn-sxd-quietp (mv-nth 1 (fn-bs-fsync-file s ino o))))
   :hints (("Goal" :in-theory (union-theories
                               '(fn-sxd-quiet-by-parts fn-bs-fsync-file fn-bs-fence-file
                                 fn-bs-pending-of-fn-bs-make fn-bs-dirs-of-fn-bs-make
                                 fn-bs-apply-ops-dirs-are-apply-entries
                                 fn-sxd-ops-for-name-of-selections fn-sxd-quiet-ops-keep-entry
                                 fn-sxd-ops-for-name-of-crash-select mv-nth car-cons cdr-cons
                                 (:e zp) (:e equal))
                               (theory 'minimal-theory))))))

(local
 (defthm fn-sxd-fsync-dir-keeps-quiet
   (implies (fn-sxd-quietp s)
            (fn-sxd-quietp (mv-nth 1 (fn-bs-fsync-dir s d o))))
   :hints (("Goal" :in-theory (union-theories
                               '(fn-sxd-quiet-by-parts fn-bs-fsync-dir fn-bs-fence-dir
                                 fn-bs-pending-of-fn-bs-make fn-bs-dirs-of-fn-bs-make
                                 fn-bs-apply-ops-dirs-are-apply-entries
                                 fn-sxd-ops-for-name-of-selections fn-sxd-quiet-ops-keep-entry
                                 fn-sxd-ops-for-name-of-crash-select mv-nth car-cons cdr-cons
                                 (:e zp) (:e equal))
                               (theory 'minimal-theory))))))

(local
 (defthm fn-sxd-sync-all-keeps-quiet
   (implies (fn-sxd-quietp s)
            (fn-sxd-quietp (mv-nth 1 (fn-sxd-sync-all s o))))
   :hints (("Goal" :in-theory (union-theories
                               '(fn-sxd-quiet-by-parts fn-sxd-sync-all
                                 fn-bs-pending-of-fn-bs-make fn-bs-dirs-of-fn-bs-make
                                 fn-bs-apply-ops-dirs-are-apply-entries fn-sxd-quiet-ops-keep-entry
                                 fn-sxd-ops-for-name-of-crash-select mv-nth car-cons cdr-cons
                                 fn-bs-ops-for-name (:e fn-bs-ops-for-name) (:e zp) (:e equal))
                               (theory 'minimal-theory))))))

(local
 (defthm fn-sxd-step-keeps-quiet
   (implies (and (fn-sxd-quietp s) (fn-sxd-step-avoidsp step))
            (fn-sxd-quietp (mv-nth 1 (fn-sxd-step s step outcome))))
   :hints (("Goal" :in-theory (union-theories
                               '(fn-sxd-step fn-sxd-step-avoidsp fn-sxd-mkdir-keeps-quiet
                                 fn-sxd-create-keeps-quiet fn-sxd-write-keeps-quiet
                                 fn-sxd-fsync-file-keeps-quiet fn-sxd-fsync-dir-keeps-quiet
                                 fn-sxd-sync-all-keeps-quiet mv-nth car-cons cdr-cons
                                 (:e zp) (:e equal) (:e member-equal))
                               (theory 'minimal-theory))))))

(local (in-theory (disable fn-sxd-quiet-by-parts)))

(local
 (defthm fn-sxd-run-keeps-quiet
   (implies (and (fn-sxd-quietp s) (fn-sxd-steps-avoidp steps)
                 (member-equal p (fn-sxd-run s steps outcomes)))
            (fn-sxd-quietp p))
   :hints (("Goal" :induct (fn-sxd-run s steps outcomes)
            :in-theory (disable fn-sxd-step fn-sxd-quietp)))))

(local
 (defthm fn-sxd-final-keeps-quiet
   (implies (and (fn-sxd-quietp s) (fn-sxd-steps-avoidp steps))
            (fn-sxd-quietp (fn-sxd-final s steps outcomes)))
   :hints (("Goal" :induct (fn-sxd-final s steps outcomes)
            :in-theory (disable fn-sxd-step fn-sxd-quietp)))))

(local
 (defthm fn-sxd-quiet-crash-has-no-manifest
   (implies (fn-sxd-quietp s)
            (null (fn-bs-durable-entry (fn-bs-crash s choices) :arch *fn-sxd-manifest*)))
   :hints (("Goal" :in-theory (enable fn-bs-crash fn-bs-durable-entry)))))

(local
 (defthm fn-sxd-run-of-append
   (equal (fn-sxd-run s (append a b) outcomes)
          (if (fn-sxd-okp s a outcomes)
              (append (fn-sxd-run s a outcomes)
                      (fn-sxd-run (fn-sxd-final s a outcomes) b (nthcdr (len a) outcomes)))
            (fn-sxd-run s a outcomes)))
   :hints (("Goal" :induct (fn-sxd-run s a outcomes)
            :in-theory (disable fn-sxd-step)))))

(local
 (defthm fn-sxd-okp-of-append
   (equal (fn-sxd-okp s (append a b) outcomes)
          (and (fn-sxd-okp s a outcomes)
               (fn-sxd-okp (fn-sxd-final s a outcomes) b (nthcdr (len a) outcomes))))
   :hints (("Goal" :induct (fn-sxd-okp s a outcomes)
            :in-theory (disable fn-sxd-step)))))

(local
 (defthm fn-sxd-final-of-append
   (equal (fn-sxd-final s (append a b) outcomes)
          (fn-sxd-final (fn-sxd-final s a outcomes) b (nthcdr (len a) outcomes)))
   :hints (("Goal" :induct (fn-sxd-final s a outcomes)
            :in-theory (disable fn-sxd-step)))))

(defun fn-sxd-content-after (ws old)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp ws)
      (fn-sxd-content-after (cdr ws) (fn-bs-splice old (nth 2 (car ws)) (nth 3 (car ws))))
    old))

(local
 (defthm fn-sxd-apply-writes-content
   (implies i
            (equal (cdr (assoc-equal i (fn-bs-apply-writes tab ops)))
                   (fn-sxd-content-after (fn-bs-ops-for-ino ops i) (cdr (assoc-equal i tab)))))
   :hints (("Goal" :induct (fn-bs-apply-writes tab ops)
            :in-theory (disable fn-bs-splice fn-bs-apply-writes-keeps-quiet-ino)))))

(local
 (defthm fn-sxd-content-after-of-append
   (equal (fn-sxd-content-after (append a b) old)
          (fn-sxd-content-after b (fn-sxd-content-after a old)))))

(local
 (defthm fn-sxd-content-is-content-after
   (implies i
   (equal (fn-bs-content s i)
          (fn-sxd-content-after (fn-bs-ops-for-ino (fn-bs-pending s) i)
                                (cdr (assoc-equal i (fn-bs-inodes s))))))
   :hints (("Goal" :in-theory (enable fn-bs-content fn-bs-view)))))

(local
 (defthm fn-sxd-lookup-is-entry-after
   (implies (and dir name)
            (equal (fn-bs-lookup s dir name)
                   (fn-bs-entry-after (fn-bs-pending s)
                                      (fn-bs-durable-entry s dir name) dir name)))
   :hints (("Goal" :in-theory (enable fn-bs-lookup fn-bs-view fn-bs-durable-entry)))))

(local
 (defthm fn-sxd-no-writes-past-next
   (implies (and (fn-bs-writes-knownp ops inodes)
                 (fn-bs-keys-belowp inodes n)
                 (natp n))
            (not (fn-bs-ops-for-ino ops n)))))

(local
 (defthm fn-sxd-create-ok-outcome
   (implies (equal (mv-nth 0 (fn-bs-create s d n o)) :ok)
            (and (equal o :ok) (not (fn-bs-lookup s d n))))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn-bs-create) (fn-sxd-lookup-is-entry-after))))))

(local
 (defthm fn-sxd-create-ok-effect
   (implies (not (fn-bs-lookup s d n))
            (let ((s1 (mv-nth 1 (fn-bs-create s d n :ok))))
              (and (equal (fn-bs-next-ino s1) (1+ (fn-bs-next-ino s)))
                   (equal (fn-bs-pending s1)
                          (append (fn-bs-pending s)
                                  (list (list :set-entry d n (fn-bs-next-ino s)))))
                   (equal (fn-bs-inodes s1)
                          (cons (cons (fn-bs-next-ino s) nil) (fn-bs-inodes s)))
                   (equal (fn-bs-dirs s1) (fn-bs-dirs s)))))
   :hints (("Goal" :in-theory (e/d (fn-bs-create) (fn-sxd-lookup-is-entry-after))))))

(local
 (defthm fn-sxd-write-ok-outcome
   (implies (and (fn-sxd-outcomep o)
                 (equal (mv-nth 0 (fn-bs-write s ino off oct o)) :ok))
            (and (equal o :ok) (assoc-equal ino (fn-bs-inodes s))))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-bs-write)))))

(local
 (defthm fn-sxd-write-ok-effect
   (implies (assoc-equal ino (fn-bs-inodes s))
            (let ((s1 (mv-nth 1 (fn-bs-write s ino off oct :ok))))
              (and (equal (fn-bs-next-ino s1) (fn-bs-next-ino s))
                   (equal (fn-bs-pending s1)
                          (if (zp (len oct))
                              (fn-bs-pending s)
                            (append (fn-bs-pending s)
                                    (list (list :write ino off (fn-bs-take (len oct) oct))))))
                   (equal (fn-bs-inodes s1) (fn-bs-inodes s))
                   (equal (fn-bs-dirs s1) (fn-bs-dirs s)))))
   :hints (("Goal" :in-theory (enable fn-bs-write)))))

(local
 (defthm fn-sxd-durable-entry-by-dirs
   (equal (fn-bs-durable-entry s d n)
          (cdr (assoc-equal n (cdr (assoc-equal d (fn-bs-dirs s))))))
   :hints (("Goal" :in-theory (enable fn-bs-durable-entry)))))

(local
 (defthm fn-sxd-lookup-after-create
   (implies (and (not (fn-bs-lookup s d n)) d2 n2)
            (equal (fn-bs-lookup (mv-nth 1 (fn-bs-create s d n :ok)) d2 n2)
                   (if (and (equal d2 d) (equal n2 n))
                       (fn-bs-next-ino s)
                     (fn-bs-lookup s d2 n2))))
   :hints (("Goal" :in-theory (disable fn-bs-create)))))

(local
 (defthm fn-sxd-content-after-create
   (implies (and (not (fn-bs-lookup s d n)) i (fn-bs-statep s))
            (equal (fn-bs-content (mv-nth 1 (fn-bs-create s d n :ok)) i)
                   (if (equal i (fn-bs-next-ino s)) nil (fn-bs-content s i))))
   :hints (("Goal" :in-theory (e/d (fn-bs-statep) (fn-bs-create))))))

(local
 (defthm fn-sxd-lookup-after-write
   (implies (and (assoc-equal ino (fn-bs-inodes s)) d2 n2)
            (equal (fn-bs-lookup (mv-nth 1 (fn-bs-write s ino off oct :ok)) d2 n2)
                   (fn-bs-lookup s d2 n2)))
   :hints (("Goal" :in-theory (disable fn-bs-write)))))

(local
 (defthm fn-sxd-content-after-write
   (implies (and (assoc-equal ino (fn-bs-inodes s)) i)
            (equal (fn-bs-content (mv-nth 1 (fn-bs-write s ino 0 oct :ok)) i)
                   (if (equal i ino)
                       (fn-bs-splice (fn-bs-content s ino) 0 (fn-bs-take (len oct) oct))
                     (fn-bs-content s i))))
   :hints (("Goal" :in-theory (disable fn-bs-write)))))

(local
 (defthm fn-sxd-splice-of-nil
   (implies (true-listp x)
            (equal (fn-bs-splice nil 0 x) x))
   :hints (("Goal" :in-theory (enable fn-bs-splice)))))

(local
 (defthm fn-sxd-take-of-own-len
   (implies (true-listp x)
            (equal (fn-bs-take (len x) x) x))))

(defun fn-sxd-landed (s done lo)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp done)
      (let* ((e (car done)) (i (fn-bs-lookup s (car e) (cadr e))))
        (and (natp i) (< (nfix lo) i) (< i (fn-bs-next-ino s))
             (equal (fn-bs-content s i) (cddr e))
             (fn-sxd-landed s (cdr done) lo)))
    t))

(local
 (defthm fn-sxd-landed-of-append
   (equal (fn-sxd-landed s (append a b) lo)
          (and (fn-sxd-landed s a lo) (fn-sxd-landed s b lo)))))

(local (in-theory (disable fn-bs-lookup-types-its-name fn-bs-lookup-types-its-dir)))

(local
 (defthm fn-sxd-landed-after-create
   (implies (and (fn-sxd-landed s done lo) (fn-sxd-keysp done)
                 (not (fn-bs-lookup s d n)) (fn-bs-statep s))
            (fn-sxd-landed (mv-nth 1 (fn-bs-create s d n :ok)) done lo))
   :hints (("Goal" :induct (fn-sxd-landed s done lo)
            :in-theory (disable fn-bs-create fn-bs-write fn-sxd-lookup-is-entry-after
                                fn-sxd-content-is-content-after fn-sxd-durable-entry-by-dirs)))))

(local
 (defthm fn-sxd-landed-after-pair
   (implies (and (fn-sxd-landed s done lo) (fn-sxd-keysp done)
                 (not (fn-bs-lookup s d n)) (fn-bs-statep s) d n)
            (fn-sxd-landed (mv-nth 1 (fn-bs-write (mv-nth 1 (fn-bs-create s d n :ok))
                                                  (fn-bs-next-ino s) 0 oct :ok))
                           done lo))
   :hints (("Goal" :induct (fn-sxd-landed s done lo)
            :in-theory (disable fn-bs-create fn-bs-write fn-sxd-lookup-is-entry-after
                                fn-sxd-content-is-content-after fn-sxd-durable-entry-by-dirs)))))

(defun fn-sxd-writingp (s done ino)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-bs-statep s) (natp ino) (< ino (fn-bs-next-ino s))
       (assoc-equal ino (fn-bs-inodes s))
       (equal (fn-bs-lookup s :arch *fn-sxd-partial*) ino)
       (equal (fn-bs-content s ino) nil)
       (fn-sxd-quietp s)
       (fn-sxd-landed s done ino)))

(local
 (defthm fn-sxd-quiet-after-create
   (implies (and (fn-sxd-quietp s)
                 (not (and (equal d :arch) (equal n *fn-sxd-manifest*))))
            (fn-sxd-quietp (mv-nth 1 (fn-bs-create s d n o))))
   :hints (("Goal" :use ((:instance fn-sxd-step-keeps-quiet (step (list :create d n)) (outcome o)))
            :in-theory (disable fn-sxd-step-keeps-quiet fn-sxd-quietp fn-bs-create)))))

(local
 (defthm fn-sxd-quiet-after-write
   (implies (fn-sxd-quietp s)
            (fn-sxd-quietp (mv-nth 1 (fn-bs-write s ino 0 oct o))))
   :hints (("Goal" :in-theory (e/d (fn-bs-write) (fn-sxd-lookup-is-entry-after))))))

(local
 (defun fn-sxd-entries-ind (es s done outs)
   (declare (xargs :verify-guards nil))
   (if (consp es)
       (let ((e (car es)))
         (mv-let (r1 s1) (fn-bs-create s (car e) (cadr e) :ok)
           (declare (ignore r1))
           (mv-let (r2 s2) (fn-bs-write s1 (fn-bs-next-ino s) 0 (cddr e) :ok)
             (declare (ignore r2))
             (fn-sxd-entries-ind (cdr es) s2 (append done (list e)) (nthcdr 3 outs)))))
     (list s done outs))))

(local
 (defthm fn-sxd-statep-next-natp
   (implies (fn-bs-statep s) (natp (fn-bs-next-ino s)))
   :rule-classes (:rewrite :forward-chaining)
   :hints (("Goal" :in-theory (enable fn-bs-statep)))))

(local
 (defthm fn-sxd-octets-true-listp
   (implies (fn-cbor-octet-listp x) (true-listp x))
   :hints (("Goal" :in-theory (enable fn-cbor-octet-listp)))))

(local
 (defthm fn-sxd-writing-after-pair
   (implies (and (fn-sxd-writingp s done ino) (fn-sxd-keysp done)
                 (member-equal d '(:arch :cfg :rec)) (stringp n)
                 (not (and (equal d :arch) (equal n *fn-sxd-manifest*)))
                 (fn-cbor-octet-listp oct)
                 (not (fn-bs-lookup s d n)))
            (fn-sxd-writingp (mv-nth 1 (fn-bs-write (mv-nth 1 (fn-bs-create s d n :ok))
                                                    (fn-bs-next-ino s) 0 oct :ok))
                             (append done (list (list* d n oct))) ino))
   :hints (("Goal" :in-theory (disable fn-bs-create fn-bs-write fn-sxd-lookup-is-entry-after
                                       fn-sxd-content-is-content-after fn-sxd-durable-entry-by-dirs
                                       fn-sxd-quietp)))))

(local
 (defthm fn-sxd-keysp-of-append
   (implies (and (fn-sxd-keysp a) (fn-sxd-keysp b))
            (fn-sxd-keysp (append a b)))))

(local
 (defthm fn-sxd-okp-of-cons
   (equal (fn-sxd-okp s (cons st rest) outs)
          (and (equal (mv-nth 0 (fn-sxd-step s st (if (consp outs) (car outs) :ok))) :ok)
               (fn-sxd-okp (mv-nth 1 (fn-sxd-step s st (if (consp outs) (car outs) :ok)))
                           rest (cdr outs))))
   :hints (("Goal" :in-theory (disable fn-sxd-step)))))

(local
 (defthm fn-sxd-final-of-cons
   (equal (fn-sxd-final s (cons st rest) outs)
          (fn-sxd-final (mv-nth 1 (fn-sxd-step s st (if (consp outs) (car outs) :ok)))
                        rest (cdr outs)))
   :hints (("Goal" :in-theory (disable fn-sxd-step)))))

(local
 (defthm fn-sxd-three-steps
   (implies (and (consp es) (fn-sxd-keysp es) (fn-sxd-outcomesp outs)
                 (fn-sxd-okp s (fn-sxd-entry-steps es) outs))
            (let* ((e (car es))
                   (s2 (mv-nth 1 (fn-bs-write (mv-nth 1 (fn-bs-create s (car e) (cadr e) :ok))
                                              (fn-bs-next-ino s) 0 (cddr e) :ok))))
              (and (not (fn-bs-lookup s (car e) (cadr e)))
                   (fn-sxd-okp s2 (fn-sxd-entry-steps (cdr es)) (nthcdr 3 outs))
                   (equal (fn-sxd-final s (fn-sxd-entry-steps es) outs)
                          (fn-sxd-final s2 (fn-sxd-entry-steps (cdr es)) (nthcdr 3 outs))))))
   :hints (("Goal" :do-not-induct t
            :expand ((fn-sxd-entry-steps es))
            :use ((:instance fn-sxd-create-ok-outcome (d (caar es)) (n (cadar es))
                             (o (if (consp outs) (car outs) :ok)))
                  (:instance fn-sxd-write-ok-outcome
                             (s (mv-nth 1 (fn-bs-create s (caar es) (cadar es)
                                                        (if (consp outs) (car outs) :ok))))
                             (ino (fn-bs-lookup (mv-nth 1 (fn-bs-create s (caar es) (cadar es)
                                                        (if (consp outs) (car outs) :ok)))
                                                (caar es) (cadar es)))
                             (off 0) (oct (cddar es))
                             (o (if (consp (cdr outs)) (cadr outs) :ok))))
            :in-theory (disable fn-bs-create fn-bs-write fn-sxd-lookup-is-entry-after
                                fn-sxd-content-is-content-after fn-sxd-durable-entry-by-dirs
                                fn-sxd-okp fn-sxd-final fn-sxd-entry-steps)))))

(local
 (defthm fn-sxd-append-assoc (equal (append (append a b) c) (append a (append b c)))))

(local
 (defthm fn-sxd-entry-cons-okp
   (implies (and (consp es) (fn-sxd-keysp es) (fn-sxd-outcomesp outs)
                 (fn-sxd-okp s (fn-sxd-entry-steps es) outs))
            (fn-sxd-okp (mv-nth 1 (fn-bs-write (mv-nth 1 (fn-bs-create s (caar es) (cadar es) :ok))
                                               (fn-bs-next-ino s) 0 (cddar es) :ok))
                        (fn-sxd-entry-steps (cdr es)) (nthcdr 3 outs)))
   :hints (("Goal" :use fn-sxd-three-steps :in-theory (disable fn-sxd-three-steps)))))

(local
 (defthm fn-sxd-entry-cons-final
   (implies (and (consp es) (fn-sxd-keysp es) (fn-sxd-outcomesp outs)
                 (fn-sxd-okp s (fn-sxd-entry-steps es) outs))
            (equal (fn-sxd-final s (fn-sxd-entry-steps es) outs)
                   (fn-sxd-final (mv-nth 1 (fn-bs-write (mv-nth 1 (fn-bs-create s (caar es) (cadar es) :ok))
                                                        (fn-bs-next-ino s) 0 (cddar es) :ok))
                                 (fn-sxd-entry-steps (cdr es)) (nthcdr 3 outs))))
   :hints (("Goal" :use fn-sxd-three-steps :in-theory (disable fn-sxd-three-steps)))))

(local
 (defthm fn-sxd-entry-cons-fresh
   (implies (and (consp es) (fn-sxd-keysp es) (fn-sxd-outcomesp outs)
                 (fn-sxd-okp s (fn-sxd-entry-steps es) outs))
            (not (fn-bs-lookup s (caar es) (cadar es))))
   :hints (("Goal" :use fn-sxd-three-steps :in-theory (disable fn-sxd-three-steps)))))

(local
 (defthm fn-sxd-keysp-cons-facts
   (implies (and (fn-sxd-keysp es) (consp es))
            (and (fn-sxd-keysp (cdr es)) (consp (car es)) (consp (cdar es))
                 (member-equal (caar es) '(:arch :cfg :rec))
                 (stringp (cadar es))
                 (not (and (equal (caar es) :arch) (equal (cadar es) *fn-sxd-manifest*)))
                 (fn-cbor-octet-listp (cddar es))))))

(local
 (defthm fn-sxd-keysp-of-singleton
   (implies (and (fn-sxd-keysp es) (consp es))
            (fn-sxd-keysp (list (car es))))))

(local
 (defthm fn-sxd-outcomesp-of-nthcdr
   (implies (fn-sxd-outcomesp outs) (fn-sxd-outcomesp (nthcdr n outs)))))

(local
 (defthm fn-sxd-final-of-atom
   (implies (atom steps) (equal (fn-sxd-final s steps outs) s))))

(local
 (defthm fn-sxd-entry-steps-land
   (implies (and (fn-sxd-writingp s done ino) (fn-sxd-keysp es) (true-listp es)
                 (fn-sxd-keysp done) (true-listp done)
                 (fn-sxd-outcomesp outs)
                 (fn-sxd-okp s (fn-sxd-entry-steps es) outs))
            (fn-sxd-writingp (fn-sxd-final s (fn-sxd-entry-steps es) outs)
                             (append done es) ino))
   :hints (("Goal" :induct (fn-sxd-entries-ind es s done outs)
            :in-theory (disable fn-bs-create fn-bs-write fn-sxd-lookup-is-entry-after
                                fn-sxd-content-is-content-after fn-sxd-durable-entry-by-dirs
                                fn-sxd-quietp fn-sxd-writingp fn-sxd-okp fn-sxd-final
                                fn-sxd-entry-steps fn-sxd-okp-of-cons fn-sxd-final-of-cons
                                fn-sxd-three-steps fn-sxd-keysp))
           ("Subgoal *1/1"
            :use ((:instance fn-sxd-writing-after-pair (d (caar es)) (n (cadar es))
                             (oct (cddar es))))))))

(defun fn-sxd-pending-okp (ops ino)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp ops)
      (and (or (equal (car ops) (list :set-entry :arch *fn-sxd-manifest* ino))
               (equal (car ops) (list :del-entry :arch *fn-sxd-partial*)))
           (fn-sxd-pending-okp (cdr ops) ino))
    (null ops)))

(defun fn-sxd-durable-landed (s done lo)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp done)
      (let* ((e (car done)) (i (fn-bs-durable-entry s (car e) (cadr e))))
        (and (natp i) (< (nfix lo) i)
             (equal (fn-bs-durable-content s i) (cddr e))
             (not (and (equal (car e) :arch)
                       (member-equal (cadr e) (list *fn-sxd-partial* *fn-sxd-manifest*))))
             (fn-sxd-durable-landed s (cdr done) lo)))
    t))

(defun fn-sxd-publishedp (s entries ino manifest)
  (declare (xargs :guard t :verify-guards nil))
  (and (natp ino)
       (fn-sxd-pending-okp (fn-bs-pending s) ino)
       (fn-sxd-durable-landed s entries ino)
       (equal (fn-bs-durable-content s ino) manifest)
       (member-equal (fn-bs-durable-entry s :arch *fn-sxd-manifest*) (list nil ino))
       (member-equal (fn-bs-durable-entry s :arch *fn-sxd-partial*) (list nil ino))))

(defun fn-sxd-completep (img entries ino manifest)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-sxd-durable-landed img entries ino)
       (equal (fn-bs-durable-entry img :arch *fn-sxd-manifest*) ino)
       (equal (fn-bs-durable-content img ino) manifest)))

(local (defthm fn-sxd-pok-no-writes
  (implies (fn-sxd-pending-okp ops ino) (not (fn-bs-ops-for-ino ops i)))))

(local (defthm fn-sxd-pok-not-for-ino
  (implies (fn-sxd-pending-okp ops ino) (equal (fn-bs-ops-not-for-ino ops i) ops))))

(local (defthm fn-sxd-pok-names
  (implies (and (fn-sxd-pending-okp ops ino)
                (not (and (equal d :arch)
                          (or (equal n *fn-sxd-partial*) (equal n *fn-sxd-manifest*)))))
           (not (fn-bs-ops-for-name ops d n)))
  :hints (("Goal" :induct (fn-sxd-pending-okp ops ino)
           :in-theory (union-theories '(fn-sxd-pending-okp fn-bs-ops-for-name member-equal nth
                                        car-cons cdr-cons (:e equal) (:e zp) (:e nth)
                                        (:e member-equal) (:induction fn-sxd-pending-okp))
                                      (theory 'minimal-theory))))))

(local (defthm fn-sxd-pok-for-dir
  (implies (fn-sxd-pending-okp ops ino) (fn-sxd-pending-okp (fn-bs-ops-for-dir ops x) ino))))

(local (defthm fn-sxd-pok-not-for-dir
  (implies (fn-sxd-pending-okp ops ino) (fn-sxd-pending-okp (fn-bs-ops-not-for-dir ops x) ino))))

(local (defthm fn-sxd-pok-crash-select
  (implies (fn-sxd-pending-okp ops ino)
           (fn-sxd-pending-okp (fn-bs-crash-select ops ch unit) ino))))

(local (defthm fn-sxd-pok-entry-after
  (implies (and (fn-sxd-pending-okp ops ino) (or (null old) (equal old ino))
                (or (equal n *fn-sxd-partial*) (equal n *fn-sxd-manifest*)))
           (or (null (fn-bs-entry-after ops old :arch n))
               (equal (fn-bs-entry-after ops old :arch n) ino)))
  :rule-classes nil
  :hints (("Goal" :induct (fn-bs-entry-after ops old :arch n)
           :in-theory (union-theories '(fn-bs-entry-after fn-sxd-pending-okp nth car-cons cdr-cons
                                        (:e equal) (:e zp) (:e nth) (:e car) (:e cdr))
                                      (theory 'minimal-theory))))))

(local (defthm fn-sxd-pok-apply-writes
  (implies (fn-sxd-pending-okp ops ino)
           (equal (fn-bs-apply-writes tab ops) tab))
  :hints (("Goal" :induct (fn-sxd-pending-okp ops ino) :expand ((fn-bs-apply-writes tab ops))
           :in-theory (union-theories '(fn-sxd-pending-okp fn-bs-apply-writes car-cons cdr-cons
                                        (:e equal) (:induction fn-sxd-pending-okp))
                                      (theory 'minimal-theory))))))

(local
 (defthm fn-sxd-durable-content-by-inodes
   (equal (fn-bs-durable-content s i) (cdr (assoc-equal i (fn-bs-inodes s))))
   :hints (("Goal" :in-theory (enable fn-bs-durable-content)))))

(local
 (defthm fn-sxd-landed-after-quiet-ops
   (implies (and (fn-sxd-durable-landed s done lo) (fn-sxd-keysp done)
                 (fn-sxd-pending-okp ops ino))
            (fn-sxd-durable-landed
             (fn-bs-make u (fn-bs-apply-writes (fn-bs-inodes s) ops)
                         (fn-bs-apply-entries (fn-bs-dirs s) ops) p n)
             done lo))
   :hints (("Goal" :induct (fn-sxd-durable-landed s done lo)
            :in-theory (union-theories
                        '(fn-sxd-durable-landed fn-sxd-keysp fn-sxd-durable-entry-by-dirs
                          fn-sxd-durable-content-by-inodes fn-bs-dirs-of-fn-bs-make
                          fn-bs-inodes-of-fn-bs-make fn-bs-apply-entries-entry-is-entry-after
                          fn-sxd-pok-names fn-sxd-entry-after-of-quiet-name
                          fn-sxd-pok-apply-writes member-equal car-cons cdr-cons
                          (:e equal) (:e member-equal) (:induction fn-sxd-durable-landed))
                        (theory 'minimal-theory))))))

(local
 (defthm fn-sxd-named-entry-after-ops
   (implies (and (fn-sxd-pending-okp ops ino)
                 (or (equal nm *fn-sxd-partial*) (equal nm *fn-sxd-manifest*))
                 (member-equal (fn-bs-durable-entry s :arch nm) (list nil ino)))
            (member-equal (fn-bs-durable-entry
                           (fn-bs-make u i (fn-bs-apply-entries (fn-bs-dirs s) ops) p n)
                           :arch nm)
                          (list nil ino)))
   :hints (("Goal" :use ((:instance fn-sxd-pok-entry-after
                                    (old (fn-bs-durable-entry s :arch nm)) (n nm))
                         (:instance fn-bs-apply-entries-entry-is-entry-after
                                    (dirs (fn-bs-dirs s)) (dir :arch) (name nm)))
            :in-theory (union-theories '(fn-sxd-durable-entry-by-dirs fn-bs-dirs-of-fn-bs-make
                                         member-equal (:e equal) car-cons cdr-cons
                                         (:e member-equal))
                                       (theory 'minimal-theory))))))

(local
 (defthm fn-sxd-published-ops-keep-published
   (implies (and (fn-sxd-publishedp s entries ino manifest) (fn-sxd-keysp entries)
                 (fn-sxd-pending-okp ops ino) (fn-sxd-pending-okp p ino))
            (fn-sxd-publishedp
             (fn-bs-make u (fn-bs-apply-writes (fn-bs-inodes s) ops)
                         (fn-bs-apply-entries (fn-bs-dirs s) ops) p n)
             entries ino manifest))
   :hints (("Goal" :use ((:instance fn-sxd-named-entry-after-ops (nm *fn-sxd-manifest*)
                                    (i (fn-bs-apply-writes (fn-bs-inodes s) ops)))
                         (:instance fn-sxd-named-entry-after-ops (nm *fn-sxd-partial*)
                                    (i (fn-bs-apply-writes (fn-bs-inodes s) ops)))
                         (:instance fn-sxd-landed-after-quiet-ops (done entries) (lo ino)))
            :in-theory (union-theories '(fn-sxd-publishedp fn-bs-pending-of-fn-bs-make
                                         fn-bs-inodes-of-fn-bs-make fn-sxd-pok-apply-writes
                                         fn-sxd-durable-content-by-inodes (:e equal))
                                       (theory 'minimal-theory))))))

(local
 (defthm fn-sxd-publishedp-pok
   (implies (fn-sxd-publishedp s entries ino manifest)
            (fn-sxd-pending-okp (fn-bs-pending s) ino))))

(local
 (defthm fn-sxd-apply-ops-parts
   (and (equal (mv-nth 0 (fn-bs-apply-ops inodes dirs ops)) (fn-bs-apply-writes inodes ops))
        (equal (mv-nth 1 (fn-bs-apply-ops inodes dirs ops)) (fn-bs-apply-entries dirs ops)))))

(local
 (defthm fn-sxd-crash-is-make
   (equal (fn-bs-crash s ch)
          (fn-bs-make (fn-bs-unit s)
                      (fn-bs-apply-writes (fn-bs-inodes s)
                                          (fn-bs-crash-select (fn-bs-pending s) ch (fn-bs-unit s)))
                      (fn-bs-apply-entries (fn-bs-dirs s)
                                           (fn-bs-crash-select (fn-bs-pending s) ch (fn-bs-unit s)))
                      nil (fn-bs-next-ino s)))
   :hints (("Goal" :in-theory (union-theories '(fn-bs-crash fn-sxd-apply-ops-parts)
                                              (theory 'minimal-theory))))))

(local
 (defthm fn-sxd-published-crash
   (implies (and (fn-sxd-publishedp s entries ino manifest) (fn-sxd-keysp entries))
            (fn-sxd-publishedp (fn-bs-crash s ch) entries ino manifest))
   :hints (("Goal" :use ((:instance fn-sxd-published-ops-keep-published
                                    (ops (fn-bs-crash-select (fn-bs-pending s) ch (fn-bs-unit s)))
                                    (p nil) (u (fn-bs-unit s)) (n (fn-bs-next-ino s)))
                         (:instance fn-sxd-pok-crash-select (ops (fn-bs-pending s))
                                    (unit (fn-bs-unit s)))
                         (:instance fn-sxd-publishedp-pok))
            :in-theory (union-theories '(fn-sxd-crash-is-make fn-sxd-pending-okp (:e null))
                                       (theory 'minimal-theory))))))

(local (in-theory (disable fn-sxd-publishedp)))

(local
 (defthm fn-sxd-pok-of-nil (fn-sxd-pending-okp nil ino)))

(local (defthm fn-sxd-pok-no-writes-equal
  (implies (fn-sxd-pending-okp ops ino) (equal (fn-bs-ops-for-ino ops i) nil))))

(local
 (defthm fn-sxd-fsync-file-keeps-published
   (implies (and (fn-sxd-publishedp s entries ino manifest) (fn-sxd-keysp entries))
            (fn-sxd-publishedp (mv-nth 1 (fn-bs-fsync-file s i o)) entries ino manifest))
   :hints (("Goal" :cases ((equal o :ok)) :use fn-sxd-publishedp-pok
            :in-theory (union-theories '(fn-bs-fsync-file fn-bs-fence-file fn-sxd-apply-ops-parts
                                         fn-sxd-pok-no-writes-equal fn-sxd-pok-not-for-ino
                                         fn-bs-crash-select-with-no-choices-is-empty (:e fn-bs-crash-select) fn-bs-crash-select
                                         fn-sxd-pok-of-nil
                                         fn-sxd-published-ops-keep-published
                                         mv-nth car-cons cdr-cons (:e zp))
                                       (theory 'minimal-theory))))))

(local
 (defthm fn-sxd-fsync-dir-keeps-published
   (implies (and (fn-sxd-publishedp s entries ino manifest) (fn-sxd-keysp entries))
            (fn-sxd-publishedp (mv-nth 1 (fn-bs-fsync-dir s d o)) entries ino manifest))
   :hints (("Goal" :cases ((equal o :ok)) :use fn-sxd-publishedp-pok
            :in-theory (union-theories '(fn-bs-fsync-dir fn-bs-fence-dir fn-sxd-apply-ops-parts
                                         fn-sxd-pok-for-dir fn-sxd-pok-not-for-dir
                                         fn-sxd-pok-crash-select
                                         fn-sxd-published-ops-keep-published
                                         mv-nth car-cons cdr-cons (:e zp))
                                       (theory 'minimal-theory))))))

(local
 (defthm fn-sxd-pok-of-append
   (implies (fn-sxd-pending-okp a ino)
            (equal (fn-sxd-pending-okp (append a b) ino)
                   (fn-sxd-pending-okp b ino)))))

(local
 (defthm fn-sxd-partial-lookup-of-published
   (implies (fn-sxd-publishedp s entries ino manifest)
            (or (null (fn-bs-lookup s :arch *fn-sxd-partial*))
                (equal (fn-bs-lookup s :arch *fn-sxd-partial*) ino)))
   :rule-classes nil
   :hints (("Goal" :use (fn-sxd-publishedp-pok
                         (:instance fn-sxd-pok-entry-after (ops (fn-bs-pending s))
                                    (old (fn-bs-durable-entry s :arch *fn-sxd-partial*))
                                    (n *fn-sxd-partial*))
                         (:instance fn-sxd-lookup-is-entry-after (dir :arch)
                                    (name *fn-sxd-partial*)))
            :in-theory (union-theories '(fn-sxd-publishedp member-equal car-cons cdr-cons (:e equal))
                                       (theory 'minimal-theory))))))

(local
 (defthm fn-sxd-rename-keeps-published
   (implies (and (fn-sxd-publishedp s entries ino manifest) (fn-sxd-keysp entries))
            (fn-sxd-publishedp (mv-nth 1 (fn-bs-rename s :arch *fn-sxd-partial*
                                                       :arch *fn-sxd-manifest* o))
                               entries ino manifest))
   :hints (("Goal" :use (fn-sxd-publishedp-pok fn-sxd-partial-lookup-of-published
                         (:instance fn-sxd-published-ops-keep-published
                                    (ops nil) (u (fn-bs-unit s))
                                    (p (append (fn-bs-pending s)
                                               (list (list :set-entry :arch *fn-sxd-manifest* ino)
                                                     (list :del-entry :arch *fn-sxd-partial*))))
                                    (n (fn-bs-next-ino s))))
            :in-theory (union-theories '(fn-bs-rename fn-sxd-pok-of-append fn-sxd-pending-okp
                                         fn-bs-apply-writes fn-bs-apply-entries
                                         mv-nth car-cons cdr-cons (:e zp) (:e fn-bs-inop)
                                         (:e equal) (:e null) (:e consp) (:e car) (:e cdr))
                                       (theory 'minimal-theory))))))

(local
 (defthm fn-sxd-sync-ok-is-the-view
   (and (equal (fn-bs-durable-entry (mv-nth 1 (fn-sxd-sync-all s :ok)) d n)
               (fn-bs-lookup s d n))
        (equal (fn-bs-durable-content (mv-nth 1 (fn-sxd-sync-all s :ok)) i)
               (fn-bs-content s i))
        (equal (fn-bs-pending (mv-nth 1 (fn-sxd-sync-all s :ok))) nil)
        (equal (mv-nth 0 (fn-sxd-sync-all s :ok)) :ok))
   :hints (("Goal" :in-theory (union-theories '(fn-sxd-sync-all fn-bs-lookup fn-bs-content fn-bs-view
                                                fn-bs-durable-entry fn-bs-durable-content
                                                fn-bs-dirs-of-fn-bs-make fn-bs-inodes-of-fn-bs-make
                                                fn-bs-pending-of-fn-bs-make
                                                mv-nth car-cons cdr-cons (:e zp) (:e equal))
                                              (theory 'minimal-theory))))))

(local
 (defthm fn-sxd-landed-is-durable-after-sync
   (implies (and (fn-sxd-landed s done lo) (fn-sxd-keysp done) (natp lo)
                 (equal (fn-bs-lookup s :arch *fn-sxd-partial*) lo))
            (fn-sxd-durable-landed (mv-nth 1 (fn-sxd-sync-all s :ok)) done lo))
   :hints (("Goal" :induct (fn-sxd-landed s done lo)
            :in-theory (e/d (fn-sxd-keysp)
                            (fn-sxd-sync-all fn-sxd-lookup-is-entry-after
                             fn-sxd-content-is-content-after fn-sxd-durable-entry-by-dirs
                             fn-sxd-durable-content-by-inodes))))))

(local
 (defthm fn-sxd-landed-after-write-at-lo
   (implies (and (fn-sxd-landed s done lo) (fn-sxd-keysp done) (natp lo)
                 (assoc-equal lo (fn-bs-inodes s)))
            (fn-sxd-landed (mv-nth 1 (fn-bs-write s lo 0 m :ok)) done lo))
   :hints (("Goal" :induct (fn-sxd-landed s done lo)
            :in-theory (e/d (fn-sxd-keysp)
                            (fn-bs-write fn-sxd-lookup-is-entry-after
                             fn-sxd-content-is-content-after fn-sxd-durable-entry-by-dirs))))))

(defun fn-sxd-writtenp (s entries ino manifest)
  (declare (xargs :guard t :verify-guards nil))
  (and (natp ino)
       (equal (fn-bs-lookup s :arch *fn-sxd-partial*) ino)
       (equal (fn-bs-content s ino) manifest)
       (fn-sxd-quietp s)
       (fn-sxd-landed s entries ino)))

(local
 (defthm fn-sxd-quiet-lookup-manifest
   (implies (fn-sxd-quietp s)
            (equal (fn-bs-lookup s :arch *fn-sxd-manifest*) nil))
   :hints (("Goal" :in-theory (e/d (fn-sxd-quietp) (fn-sxd-durable-entry-by-dirs))))))

(local
 (defthm fn-sxd-written-sync-is-published
   (implies (and (fn-sxd-writtenp s entries ino manifest) (fn-sxd-keysp entries))
            (fn-sxd-publishedp (mv-nth 1 (fn-sxd-sync-all s :ok)) entries ino manifest))
   :hints (("Goal" :in-theory (e/d (fn-sxd-publishedp fn-sxd-writtenp)
                                   (fn-sxd-sync-all fn-sxd-lookup-is-entry-after
                                    fn-sxd-content-is-content-after fn-sxd-durable-entry-by-dirs
                                    fn-sxd-durable-content-by-inodes fn-sxd-quietp))))))

(local
 (defthm fn-sxd-mkdir-next
   (equal (fn-bs-next-ino (mv-nth 1 (fn-bs-mkdir s p nm id o))) (fn-bs-next-ino s))
   :hints (("Goal" :in-theory (enable fn-bs-mkdir)))))

(local
 (defthm fn-sxd-mkdir-ok-outcome
   (implies (and (fn-sxd-outcomep o) (equal (mv-nth 0 (fn-bs-mkdir s p nm id o)) :ok))
            (equal o :ok))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-bs-mkdir)))))

(local
 (defthm fn-sxd-head-okp-facts
   (implies (and (fn-sxd-outcomesp outs) (fn-sxd-okp s (fn-sxd-head-steps) outs))
            (let* ((s1 (mv-nth 1 (fn-bs-mkdir s :arch "config" :cfg :ok)))
                   (s2 (mv-nth 1 (fn-bs-mkdir s1 :arch "records" :rec :ok))))
              (and (not (fn-bs-lookup s2 :arch *fn-sxd-partial*))
                   (equal (fn-sxd-final s (fn-sxd-head-steps) outs)
                          (mv-nth 1 (fn-bs-create s2 :arch *fn-sxd-partial* :ok))))))
   :hints (("Goal" :use ((:instance fn-sxd-mkdir-ok-outcome (p :arch) (nm "config") (id :cfg)
                                    (o (if (consp outs) (car outs) :ok)))
                         (:instance fn-sxd-mkdir-ok-outcome
                                    (s (mv-nth 1 (fn-bs-mkdir s :arch "config" :cfg :ok)))
                                    (p :arch) (nm "records") (id :rec)
                                    (o (if (consp (cdr outs)) (cadr outs) :ok)))
                         (:instance fn-sxd-create-ok-outcome
                                    (s (mv-nth 1 (fn-bs-mkdir (mv-nth 1 (fn-bs-mkdir s :arch "config" :cfg :ok))
                                                              :arch "records" :rec :ok)))
                                    (d :arch) (n *fn-sxd-partial*)
                                    (o (if (consp (cddr outs)) (caddr outs) :ok))))
            :in-theory (e/d (fn-sxd-okp fn-sxd-final fn-sxd-step fn-sxd-outcomesp)
                            (fn-bs-create fn-bs-mkdir fn-sxd-lookup-is-entry-after
                             fn-sxd-content-is-content-after fn-sxd-durable-entry-by-dirs
                             fn-sxd-quietp fn-sxd-okp-of-cons fn-sxd-final-of-cons))))))

(local
 (defthm fn-sxd-quiet-after-mkdir
   (implies (and (fn-sxd-quietp s)
                 (not (and (equal p :arch) (equal nm *fn-sxd-manifest*))))
            (fn-sxd-quietp (mv-nth 1 (fn-bs-mkdir s p nm id o))))
   :hints (("Goal" :use ((:instance fn-sxd-step-keeps-quiet (step (list :mkdir p nm id)) (outcome o)))
            :in-theory (disable fn-sxd-step-keeps-quiet fn-sxd-quietp fn-bs-mkdir)))))

(local
 (defthm fn-sxd-head-writing
   (implies (and (fn-bs-statep s) (fn-sxd-quietp s) (fn-sxd-outcomesp outs)
                 (fn-sxd-okp s (fn-sxd-head-steps) outs))
            (fn-sxd-writingp (fn-sxd-final s (fn-sxd-head-steps) outs) nil
                             (fn-bs-next-ino s)))
   :hints (("Goal" :use fn-sxd-head-okp-facts
            :in-theory (union-theories
                        '(fn-sxd-writingp fn-bs-mkdir-preserves-statep fn-bs-create-preserves-statep
                          fn-sxd-mkdir-next fn-sxd-create-ok-effect fn-sxd-lookup-after-create
                          fn-sxd-content-after-create fn-sxd-quiet-after-mkdir
                          fn-sxd-quiet-after-create fn-sxd-statep-next-natp fn-sxd-landed
                          assoc-equal car-cons cdr-cons natp fn-bs-dir-idp fn-bs-namep
                          (:compound-recognizer natp-compound-recognizer)
                          (:e equal) (:e keywordp) (:e stringp) (:e fn-bs-dir-idp) (:e fn-bs-namep)
                          (:e not))
                        (theory 'minimal-theory))))))

(local
 (defthm fn-sxd-writing-write-is-written
   (implies (and (fn-sxd-writingp s entries ino) (fn-sxd-keysp entries)
                 (fn-cbor-octet-listp m))
            (fn-sxd-writtenp (mv-nth 1 (fn-bs-write s ino 0 m :ok)) entries ino m))
   :hints (("Goal" :in-theory (union-theories
                               '(fn-sxd-writingp fn-sxd-writtenp fn-sxd-lookup-after-write
                                 fn-sxd-content-after-write fn-sxd-quiet-after-write
                                 fn-sxd-landed-after-write-at-lo fn-sxd-splice-of-nil
                                 fn-sxd-take-of-own-len fn-sxd-octets-true-listp natp
                                 (:e equal))
                               (theory 'minimal-theory))))))

(local
 (defthm fn-sxd-writingp-lookup
   (implies (fn-sxd-writingp s entries ino)
            (equal (fn-bs-lookup s :arch *fn-sxd-partial*) ino))))

(local
 (defthm fn-sxd-tail-written
   (implies (and (fn-sxd-writingp s entries ino) (fn-sxd-keysp entries)
                 (fn-cbor-octet-listp manifest)
                 (fn-sxd-outcomesp outs) (fn-sxd-okp s (fn-sxd-tail-steps manifest) outs))
            (fn-sxd-writtenp (fn-sxd-final s (fn-sxd-tail-steps manifest) outs)
                             entries ino manifest))
   :hints (("Goal" :use ((:instance fn-sxd-write-ok-outcome (off 0) (oct manifest)
                                    (o (if (consp outs) (car outs) :ok)))
                         (:instance fn-sxd-writing-write-is-written (m manifest)))
            :in-theory (union-theories
                        '(fn-sxd-tail-steps fn-sxd-okp fn-sxd-final fn-sxd-step fn-sxd-outcomesp
                          fn-sxd-writingp-lookup mv-nth car-cons cdr-cons nth (:e zp) (:e equal)
                          (:e fn-sxd-outcomep) (:e consp) (:e car) (:e cdr) (:e nth))
                        (theory 'minimal-theory))))))

(defun fn-sxd-post-stepp (step)
  (declare (xargs :guard t :verify-guards nil))
  (or (and (consp step) (equal (car step) :cut))
      (equal step (list :fsync-file :arch *fn-sxd-partial*))
      (and (consp step) (equal (car step) :fsync-dir))
      (equal step (list :rename :arch *fn-sxd-partial* :arch *fn-sxd-manifest*))))

(defun fn-sxd-post-stepsp (steps)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp steps)
      (and (fn-sxd-post-stepp (car steps)) (fn-sxd-post-stepsp (cdr steps)))
    t))

(local
 (defthm fn-sxd-post-step-keeps-published
   (implies (and (fn-sxd-publishedp s entries ino manifest) (fn-sxd-keysp entries)
                 (fn-sxd-post-stepp step))
            (fn-sxd-publishedp (mv-nth 1 (fn-sxd-step s step o)) entries ino manifest))
   :hints (("Goal" :in-theory (union-theories
                               '(fn-sxd-post-stepp fn-sxd-step fn-sxd-fsync-file-keeps-published
                                 fn-sxd-fsync-dir-keeps-published fn-sxd-rename-keeps-published
                                 mv-nth car-cons cdr-cons nth (:e zp) (:e equal) (:e car) (:e cdr)
                                 (:e nth) (:e consp))
                               (theory 'minimal-theory))))))

(local
 (defthm fn-sxd-run-keeps-published
   (implies (and (fn-sxd-publishedp s entries ino manifest) (fn-sxd-keysp entries)
                 (fn-sxd-post-stepsp steps)
                 (member-equal p (fn-sxd-run s steps outs)))
            (fn-sxd-publishedp p entries ino manifest))
   :hints (("Goal" :induct (fn-sxd-run s steps outs)
            :in-theory (disable fn-sxd-step fn-sxd-post-stepp)))))

(local
 (defthm fn-sxd-published-crash-is-absent-or-complete
   (implies (and (fn-sxd-publishedp s entries ino manifest) (fn-sxd-keysp entries))
            (let ((img (fn-bs-crash s ch)))
              (or (null (fn-bs-durable-entry img :arch *fn-sxd-manifest*))
                  (fn-sxd-completep img entries ino manifest))))
   :hints (("Goal" :use fn-sxd-published-crash
            :in-theory (union-theories '(fn-sxd-publishedp fn-sxd-completep member-equal
                                         car-cons cdr-cons (:e equal))
                                       (theory 'minimal-theory))))))

(local
 (defthm fn-sxd-entry-steps-avoid
   (implies (fn-sxd-keysp es) (fn-sxd-steps-avoidp (fn-sxd-entry-steps es)))
   :hints (("Goal" :in-theory (enable fn-sxd-keysp)))))

(local
 (defthm fn-sxd-steps-avoidp-of-append
   (equal (fn-sxd-steps-avoidp (append a b))
          (and (fn-sxd-steps-avoidp a) (fn-sxd-steps-avoidp b)))))

(local
 (defthm fn-sxd-write-program-avoids
   (implies (fn-sxd-keysp entries)
            (fn-sxd-steps-avoidp (fn-sxd-write-program entries manifest)))))

(local
 (defthm fn-sxd-keysp-true-listp
   (implies (fn-sxd-keysp entries) (true-listp entries))
   :rule-classes (:rewrite :forward-chaining)))

(local
 (defthm fn-sxd-len-head-steps
   (equal (len (fn-sxd-head-steps)) 3)))

(local
 (defthm fn-sxd-write-program-written
   (implies (and (fn-bs-statep s) (fn-sxd-quietp s) (fn-sxd-keysp entries) (true-listp entries)
                 (fn-cbor-octet-listp manifest) (fn-sxd-outcomesp outs)
                 (fn-sxd-okp s (fn-sxd-write-program entries manifest) outs))
            (fn-sxd-writtenp (fn-sxd-final s (fn-sxd-write-program entries manifest) outs)
                             entries (fn-bs-next-ino s) manifest))
   :hints (("Goal" :use ((:instance fn-sxd-head-writing)
                         (:instance fn-sxd-entry-steps-land
                                    (s (fn-sxd-final s (fn-sxd-head-steps) outs))
                                    (done nil) (es entries) (ino (fn-bs-next-ino s))
                                    (outs (nthcdr 3 outs)))
                         (:instance fn-sxd-tail-written
                                    (s (fn-sxd-final (fn-sxd-final s (fn-sxd-head-steps) outs)
                                                     (fn-sxd-entry-steps entries) (nthcdr 3 outs)))
                                    (ino (fn-bs-next-ino s))
                                    (outs (nthcdr (len (fn-sxd-entry-steps entries))
                                                  (nthcdr 3 outs)))))
            :in-theory (union-theories '(fn-sxd-write-program fn-sxd-okp-of-append
                                         fn-sxd-final-of-append fn-sxd-outcomesp-of-nthcdr
                                         fn-sxd-len-head-steps (:e fn-sxd-keysp)
                                         (:e true-listp) (:e binary-append) append-to-nil binary-append)
                                       (theory 'minimal-theory))))))

(local
 (defthm fn-sxd-sync-ok-outcome
   (implies (and (fn-sxd-outcomep o) (equal (mv-nth 0 (fn-sxd-sync-all s o)) :ok))
            (equal o :ok))
   :rule-classes nil
   :hints (("Goal" :in-theory (union-theories '(fn-sxd-sync-all fn-sxd-outcomep mv-nth
                                                car-cons cdr-cons (:e equal) (:e zp))
                                              (theory 'minimal-theory))))))

(local
 (defthm fn-sxd-publish-program-steps
   (fn-sxd-post-stepsp (fn-sxd-publish-program))))

; The states of the run from the sync on: the sync's own, and the publishing
; steps' (each published when the sync succeeded).
(local
 (defthm fn-sxd-after-sync-crash
   (implies (and (fn-sxd-writtenp f entries ino manifest) (fn-sxd-keysp entries)
                 (fn-sxd-outcomesp outs)
                 (member-equal p (fn-sxd-run f (cons (list :sync-all) (fn-sxd-publish-program))
                                             outs)))
            (let ((img (fn-bs-crash p ch)))
              (or (null (fn-bs-durable-entry img :arch *fn-sxd-manifest*))
                  (fn-sxd-completep img entries ino manifest))))
   :hints (("Goal" :use ((:instance fn-sxd-sync-ok-outcome (s f)
                                    (o (if (consp outs) (car outs) :ok)))
                         (:instance fn-sxd-written-sync-is-published (s f))
                         (:instance fn-sxd-step-keeps-quiet (s f) (step (list :sync-all))
                                    (outcome (if (consp outs) (car outs) :ok)))
                         (:instance fn-sxd-run-keeps-published
                                    (s (mv-nth 1 (fn-sxd-sync-all f :ok)))
                                    (steps (fn-sxd-publish-program)) (outs (cdr outs)))
                         (:instance fn-sxd-published-crash-is-absent-or-complete (s p))
                         (:instance fn-sxd-quiet-crash-has-no-manifest (s p) (choices ch)))
            :in-theory (union-theories '(fn-sxd-run fn-sxd-step fn-sxd-writtenp member-equal
                                         fn-sxd-outcomesp fn-sxd-publish-program-steps
                                         mv-nth car-cons cdr-cons (:e equal) (:e car)
                                         (:e fn-sxd-step-avoidsp) (:e consp))
                                       (theory 'minimal-theory))))))

; KEYSTONE (the subject: the export program host/native/io.lisp
; fnn-command-store-export runs, step for step, with its cuts).  From a
; well-formed byte state whose archive directory has no MANIFEST durable or
; pending, a crash at ANY state of ANY run of the program, under ANY outcome
; of every syscall (fn-sxd-outcomesp) and ANY selection of what landed, leaves
; either no MANIFEST, or the MANIFEST bound to the file the export wrote its
; lines into (the inode created first, fn-bs-next-ino of the start), holding
; exactly MANIFEST, with every entry of ENTRIES bound to a file holding
; exactly its octets.
(defthm fn-sxd-crash-is-incomplete-or-complete
  (implies (and (fn-bs-statep bs) (fn-sxd-quietp bs)
                (fn-sxd-keysp entries) (fn-cbor-octet-listp manifest)
                (fn-sxd-outcomesp outs)
                (member-equal p (fn-sxd-run bs (fn-sxd-program entries manifest) outs)))
           (let ((img (fn-bs-crash p ch)))
             (or (null (fn-bs-durable-entry img :arch *fn-sxd-manifest*))
                 (fn-sxd-completep img entries (fn-bs-next-ino bs) manifest))))
  :hints (("Goal" :use ((:instance fn-sxd-run-of-append (s bs)
                                   (a (fn-sxd-write-program entries manifest))
                                   (b (cons (list :sync-all) (fn-sxd-publish-program)))
                                   (outcomes outs))
                        (:instance fn-sxd-run-keeps-quiet (s bs)
                                   (steps (fn-sxd-write-program entries manifest))
                                   (outcomes outs))
                        (:instance fn-sxd-quiet-crash-has-no-manifest (s p) (choices ch))
                        (:instance fn-sxd-write-program-avoids)
                        (:instance fn-sxd-write-program-written (s bs))
                        (:instance fn-sxd-after-sync-crash
                                   (f (fn-sxd-final bs (fn-sxd-write-program entries manifest) outs))
                                   (ino (fn-bs-next-ino bs))
                                   (outs (nthcdr (len (fn-sxd-write-program entries manifest))
                                                 outs))))
           :in-theory (union-theories '(fn-sxd-program fn-bs-member-of-append
                                        fn-sxd-outcomesp-of-nthcdr fn-sxd-keysp-true-listp)
                                      (theory 'minimal-theory)))))

; The import's verdict on what a crash left (host/native/io.lisp
; fnn-import-pass asks fn-sxd-archive-verdict whether DIR/MANIFEST is there):
; :archive-incomplete, the refusal by name, or :read over the complete
; archive -- never :read over a MANIFEST the crash left without its entries.
(defthm fn-sxd-import-verdict-is-incomplete-or-complete
  (implies (and (fn-bs-statep bs) (fn-sxd-quietp bs)
                (fn-sxd-keysp entries) (fn-cbor-octet-listp manifest)
                (fn-sxd-outcomesp outs)
                (member-equal p (fn-sxd-run bs (fn-sxd-program entries manifest) outs)))
           (let* ((img (fn-bs-crash p ch))
                  (verdict (fn-sxd-archive-verdict
                            (fn-bs-durable-entry img :arch *fn-sxd-manifest*))))
             (or (equal verdict :archive-incomplete)
                 (and (equal verdict :read)
                      (fn-sxd-completep img entries (fn-bs-next-ino bs) manifest)))))
  :hints (("Goal" :use fn-sxd-crash-is-incomplete-or-complete
           :in-theory (union-theories '(fn-sxd-archive-verdict) (theory 'minimal-theory)))))
