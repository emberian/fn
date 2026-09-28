; fn: the publication program of `store import' (D34), P-IMPORT, over the
; byte model (crash model v2).
;
; `store import DIR' builds a new Store beside ROOT and publishes it by one
; directory rename.  The program, in the host's order (host/native/io.lisp
; `fnn-command-store-import'):
;
;   1. staging: mkdir the staged directory STAGE in ROOT's parent, mkdir its
;      subdirectories, and for every file of the import plan create it,
;      write it and fsync it; then fsync every subdirectory and the staged
;      directory itself.  At the end every file's octets and every name in
;      the staged tree are durable (fn-bs-imp-staging-completes).
;   2. validation: the ordinary open admits the staged Store (full replay,
;      marker catch-up).  It is its own modelled program (P-RECOVER) run on
;      the staged directory; here it is the cut `import-validated', and it
;      rewrites no name of the plan (it creates the writer lock and the
;      marker and sweeps the staged Store's own staging/).
;   3. publication: rename STAGE onto ROOT WITHOUT replacing an existing
;      destination (Linux renameat2 RENAME_NOREPLACE; the model's
;      fn-bs-rename-dir-noreplace refuses :eexist when ROOT is bound in the
;      view), then fsync the parent.
;
; The keystone fn-bs-imp-program-crash-is-no-store-or-the-complete-store:
; a crash at any point of any run of the program, with any outcome of any
; syscall, leaves ROOT's entry as it was (no store, when ROOT was absent; an
; unrelated destination is never replaced), or -- only when ROOT was absent
; -- bound to the staged directory with every file of the plan durable with
; exactly its octets.  fn-bs-imp-classify-by-what-is-known is the recovery
; classification of the two names the host can observe (STAGE and ROOT):
; a staged directory beside a present ROOT is `publication uncertain', never
; `no store was created'.
(in-package "ACL2")
(include-book "byte-store-programs")
(include-book "byte-store-invariants")

;; Rules withdrawn at their source that this book's proofs use
;; (lane rule-hygiene, tools/rule_cost.py).
(local (in-theory (enable (:definition fn-bs-dir-idp)
                          (:definition fn-bs-keys-belowp)
                          (:rewrite fn-bs-keys-belowp-excludes-bound))))

; -----------------------------------------------------------------------------
; The directory rename.  byte-store's fn-bs-rename moves a file entry; a
; directory entry (a directory id) moves the same way: ONE :set-entry on the
; destination and a SEPARATE :del-entry of the source, neither assumed to
; land with the other.  The destination is never replaced: a bound
; destination is :eexist and nothing is issued (renameat2 RENAME_NOREPLACE).
(defun fn-bs-rename-dir-noreplace (s sdir sname ddir dname outcome)
  (declare (xargs :guard t :verify-guards nil))
  (let ((id (fn-bs-lookup s sdir sname)))
    (cond ((not (fn-bs-dir-idp id)) (mv :enoent s))
          ((fn-bs-lookup s ddir dname) (mv :eexist s))
          ((or (equal outcome :ok)
               (and (consp outcome) (equal (cdr outcome) :issued)))
           (mv (if (equal outcome :ok) :ok (car outcome))
               (fn-bs-make (fn-bs-unit s) (fn-bs-inodes s) (fn-bs-dirs s)
                           (append (fn-bs-pending s)
                                   (list (list :set-entry ddir dname id)
                                         (list :del-entry sdir sname)))
                           (fn-bs-next-ino s))))
          (t (mv (if (consp outcome) (car outcome) outcome) s)))))

; The step language of byte-store-programs plus
;   (:rename-dir-noreplace sdir sname ddir dname)   renameat2(RENAME_NOREPLACE)
(defun fn-bs-imp-step (bs ks step outcome groups capacity)
  (declare (xargs :guard t :verify-guards nil))
  (if (equal (car step) :rename-dir-noreplace)
      (mv-let (r bs1) (fn-bs-rename-dir-noreplace bs (nth 1 step) (nth 2 step)
                                                  (nth 3 step) (nth 4 step) outcome)
        (mv r bs1 ks))
    (fn-bs-step bs ks step outcome groups capacity)))

; fn-bs-run over that step: to the first error, the (bs . ks) pair after
; every step.
(defun fn-bs-imp-run (bs ks steps outcomes groups capacity)
  (declare (xargs :guard t :verify-guards nil :measure (len steps)))
  (if (consp steps)
      (mv-let (r bs1 ks1)
        (fn-bs-imp-step bs ks (car steps) (if (consp outcomes) (car outcomes) :ok)
                        groups capacity)
        (cons (cons bs1 ks1)
              (if (equal r :ok)
                  (fn-bs-imp-run bs1 ks1 (cdr steps) (cdr outcomes) groups capacity)
                nil)))
    nil))

; Every step of STEPS returned :ok, and the pair after the last.
(defun fn-bs-imp-okp (bs ks steps outcomes groups capacity)
  (declare (xargs :guard t :verify-guards nil :measure (len steps)))
  (if (consp steps)
      (mv-let (r bs1 ks1)
        (fn-bs-imp-step bs ks (car steps) (if (consp outcomes) (car outcomes) :ok)
                        groups capacity)
        (and (equal r :ok)
             (fn-bs-imp-okp bs1 ks1 (cdr steps) (cdr outcomes) groups capacity)))
    t))

(defun fn-bs-imp-final (bs ks steps outcomes groups capacity)
  (declare (xargs :guard t :verify-guards nil :measure (len steps)))
  (if (consp steps)
      (mv-let (r bs1 ks1)
        (fn-bs-imp-step bs ks (car steps) (if (consp outcomes) (car outcomes) :ok)
                        groups capacity)
        (declare (ignore r))
        (fn-bs-imp-final bs1 ks1 (cdr steps) (cdr outcomes) groups capacity))
    (cons bs ks)))

; -----------------------------------------------------------------------------
; The program.  SUBDIRS is a list of (NAME . ID): the staged directory's
; subdirectories.  FILES is a list of (DIR NAME . OCTETS): the plan's files,
; each in the staged directory (:stage) or one of its subdirectories.

(defun fn-bs-imp-subdir-steps (subdirs)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp subdirs)
      (list* (list :mkdir :stage (car (car subdirs)) (cdr (car subdirs)))
             (list :cut "import-subdir-created")
             (fn-bs-imp-subdir-steps (cdr subdirs)))
    nil))

(defun fn-bs-imp-file-steps (file)
  (declare (xargs :guard t :verify-guards nil))
  (let ((dir (car file)) (name (cadr file)) (octets (cddr file)))
    (list (list :create dir name)
          (list :cut "import-file-created")
          (list :write-all dir name octets)
          (list :cut "import-file-written")
          (list :fsync-file dir name)
          (list :cut "import-file-durable"))))

(defun fn-bs-imp-files-steps (files)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp files)
      (append (fn-bs-imp-file-steps (car files))
              (fn-bs-imp-files-steps (cdr files)))
    nil))

(defun fn-bs-imp-fence-steps (subdirs)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp subdirs)
      (list* (list :fsync-dir (cdr (car subdirs)))
             (list :cut "import-subdir-durable")
             (fn-bs-imp-fence-steps (cdr subdirs)))
    nil))

(defun fn-bs-imp-stage-steps (stage)
  (declare (xargs :guard t :verify-guards nil))
  (list (list :mkdir :parent stage :stage)
        (list :cut "import-stage-created")))

(defun fn-bs-imp-seal-steps ()
  (declare (xargs :guard t :verify-guards nil))
  (list (list :fsync-dir :stage)
        (list :cut "import-staged-durable")))

(defun fn-bs-imp-staging-program (stage subdirs files)
  (declare (xargs :guard t :verify-guards nil))
  (append (fn-bs-imp-stage-steps stage)
          (fn-bs-imp-subdir-steps subdirs)
          (fn-bs-imp-files-steps files)
          (fn-bs-imp-fence-steps subdirs)
          (fn-bs-imp-seal-steps)))

(defun fn-bs-imp-publication-program (stage root)
  (declare (xargs :guard t :verify-guards nil))
  (list (list :cut "import-validated")
        (list :rename-dir-noreplace :parent stage :parent root)
        (list :cut "import-published")
        (list :fsync-dir :parent)
        (list :cut "import-durable")))

(defun fn-bs-imp-program (stage root subdirs files)
  (declare (xargs :guard t :verify-guards nil))
  (append (fn-bs-imp-staging-program stage subdirs files)
          (fn-bs-imp-publication-program stage root)))

; -----------------------------------------------------------------------------
; Recovery's classification (host: `fnn-command-store-import', before it
; writes anything and after an error at or after the rename).  What the host
; can observe after a death or an ambiguous rename/barrier outcome is whether
; the staged name and ROOT are present.  The answer is ACL2's:
;   :no-store               neither: no store was published (import again)
;   :not-published          only the staged directory: the import died before
;                           publication; ROOT holds no store (remove the
;                           staged directory by name, import again)
;   :publication-uncertain  both: never "no store was created"; run `store
;                           recover' on ROOT, then remove the staged directory
;   :store-present          only ROOT: the ordinary open decides
; fn-bs-imp-classify-by-what-is-known: at every crash image of every run of
; the program from an absent ROOT, the two answers that say ROOT holds no
; store are given only when it holds none.
(defun fn-bs-imp-classify (stage-present root-present)
  (declare (xargs :guard t))
  (cond ((and stage-present root-present) :publication-uncertain)
        (stage-present :not-published)
        (root-present :store-present)
        (t :no-store)))

; -----------------------------------------------------------------------------
; The precondition and the conclusion.

(defun fn-bs-imp-subdirsp (subdirs)
  (declare (xargs :guard t))
  (if (consp subdirs)
      (and (consp (car subdirs))
           (stringp (car (car subdirs)))
           (keywordp (cdr (car subdirs)))
           (fn-bs-imp-subdirsp (cdr subdirs)))
    (null subdirs)))

; Every file names a staged directory (DIRS), a string name and octets.
(defun fn-bs-imp-filesp (files dirs)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp files)
      (and (consp (car files)) (consp (cdr (car files)))
           (member-equal (car (car files)) dirs)
           (stringp (cadr (car files)))
           (fn-cbor-octet-listp (cddr (car files)))
           (fn-bs-imp-filesp (cdr files) dirs))
    (null files)))

; The import runs in a fresh process: nothing is pending.  The parent
; directory exists, STAGE and ROOT are two names in it, the files are in
; the staged tree, and ROOT's durable entry is OLD (nil: no store).
(defun fn-bs-imp-inputp (bs stage root subdirs files old)
  (declare (xargs :guard t :verify-guards nil))
  (and (null (fn-bs-pending bs))
       (natp (fn-bs-next-ino bs))
       (assoc-equal :parent (fn-bs-dirs bs))
       (stringp stage) (stringp root) (not (equal stage root))
       (fn-bs-imp-subdirsp subdirs)
       (fn-bs-imp-filesp files (cons :stage (strip-cdrs subdirs)))
       (equal (fn-bs-durable-entry bs :parent root) old)))

; The complete imported tree, durably: every subdirectory named in the
; staged directory, every file named with inode INO, INO+1, ... in plan order
; and holding exactly its octets.
(defun fn-bs-imp-subdirs-completep (s subdirs)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp subdirs)
      (and (equal (fn-bs-durable-entry s :stage (car (car subdirs)))
                  (cdr (car subdirs)))
           (fn-bs-imp-subdirs-completep s (cdr subdirs)))
    t))

(defun fn-bs-imp-files-completep (s files ino)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp files)
      (and (equal (fn-bs-durable-entry s (car (car files)) (cadr (car files))) ino)
           (equal (fn-bs-durable-content s ino) (cddr (car files)))
           (fn-bs-imp-files-completep s (cdr files) (+ 1 ino)))
    t))

(defun fn-bs-imp-completep (s subdirs files ino)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-bs-imp-subdirs-completep s subdirs)
       (fn-bs-imp-files-completep s files ino)))

; What a crash image holds at ROOT: its old entry (no store, or the
; unrelated destination untouched), or -- only when ROOT was absent -- the
; staged directory with the complete tree.
(defun fn-bs-imp-no-store-or-completep (img root subdirs files ino old)
  (declare (xargs :guard t :verify-guards nil))
  (let ((entry (fn-bs-durable-entry img :parent root)))
    (or (equal entry old)
        (and (null old)
             (equal entry :stage)
             (fn-bs-imp-completep img subdirs files ino)))))

; -----------------------------------------------------------------------------
; Proof.

(local (in-theory (enable fn-bs-invariants-vocabulary)))
; Proof cost (D26): with the vocabulary enabled the landing and program lemmas
; spent most of their time on rules they never use (22.6 s at two jobs).  The
; slow ones therefore prove in a quoted theory naming exactly the rules each
; proof uses; the statements are unchanged.
(local (in-theory (disable fn-bs-rename-dir-noreplace)))

(local
 (defthm fn-bs-imp-run-of-append
   (implies (true-listp a)
            (equal (fn-bs-imp-run bs ks (append a b) outcomes groups capacity)
                   (if (fn-bs-imp-okp bs ks a outcomes groups capacity)
                       (let ((f (fn-bs-imp-final bs ks a outcomes groups capacity)))
                         (append (fn-bs-imp-run bs ks a outcomes groups capacity)
                                 (fn-bs-imp-run (car f) (cdr f) b
                                                (nthcdr (len a) outcomes)
                                                groups capacity)))
                     (fn-bs-imp-run bs ks a outcomes groups capacity))))
   :hints (("Goal" :induct (fn-bs-imp-run bs ks a outcomes groups capacity)
            :in-theory (disable fn-bs-imp-step)))))

(local
 (defthm fn-bs-imp-okp-of-append
   (equal (fn-bs-imp-okp bs ks (append a b) outcomes groups capacity)
          (and (fn-bs-imp-okp bs ks a outcomes groups capacity)
               (let ((f (fn-bs-imp-final bs ks a outcomes groups capacity)))
                 (fn-bs-imp-okp (car f) (cdr f) b (nthcdr (len a) outcomes)
                                groups capacity))))
   :hints (("Goal" :induct (fn-bs-imp-okp bs ks a outcomes groups capacity)
            :in-theory (disable fn-bs-imp-step)))))

(local
 (defthm fn-bs-imp-final-of-append
   (equal (fn-bs-imp-final bs ks (append a b) outcomes groups capacity)
          (let ((f (fn-bs-imp-final bs ks a outcomes groups capacity)))
            (fn-bs-imp-final (car f) (cdr f) b (nthcdr (len a) outcomes)
                             groups capacity)))
   :hints (("Goal" :induct (fn-bs-imp-final bs ks a outcomes groups capacity)
            :in-theory (disable fn-bs-imp-step)))))

(local (in-theory (disable fn-bs-imp-run-of-append fn-bs-imp-okp-of-append
                           fn-bs-imp-final-of-append)))

; Operation-list vocabulary.

(local
 (defthm fn-bs-imp-keyword-is-not-nil
   (implies (equal (symbol-package-name x) "KEYWORD") x)
   :rule-classes :forward-chaining))

(local (in-theory (enable fn-bs-entry-after)))

(local
 (defthm fn-bs-imp-ops-not-for-ino-of-append
   (equal (fn-bs-ops-not-for-ino (append a b) ino)
          (append (fn-bs-ops-not-for-ino a ino) (fn-bs-ops-not-for-ino b ino)))))

(local
 (defthm fn-bs-imp-ops-not-for-dir-of-append
   (equal (fn-bs-ops-not-for-dir (append a b) dir)
          (append (fn-bs-ops-not-for-dir a dir) (fn-bs-ops-not-for-dir b dir)))))

(local
 (defthm fn-bs-imp-ops-for-name-of-append
   (equal (fn-bs-ops-for-name (append a b) dir name)
          (append (fn-bs-ops-for-name a dir name) (fn-bs-ops-for-name b dir name)))))

; Every operation is a :set-entry (no write is pending).
(defun fn-bs-imp-entry-opsp (ops)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp ops)
      (and (consp (car ops)) (equal (car (car ops)) :set-entry)
           (fn-bs-imp-entry-opsp (cdr ops)))
    (null ops)))

(local
 (defthm fn-bs-imp-entry-opsp-of-append
   (implies (true-listp a)
            (equal (fn-bs-imp-entry-opsp (append a b))
                   (and (fn-bs-imp-entry-opsp a) (fn-bs-imp-entry-opsp b))))))

(local
 (defthm fn-bs-imp-entry-ops-have-no-writes
   (implies (fn-bs-imp-entry-opsp ops)
            (and (equal (fn-bs-ops-for-ino ops ino) nil)
                 (equal (fn-bs-ops-not-for-ino ops ino) ops)))))

(local
 (defthm fn-bs-imp-entry-opsp-true-listp
   (implies (fn-bs-imp-entry-opsp ops) (true-listp ops))
   :rule-classes :forward-chaining))

; The view's entry is the durable entry after the pending operations.
(local
 (defthm fn-bs-imp-lookup-is-entry-after
   (implies (and dir name)
            (equal (fn-bs-lookup s dir name)
                   (fn-bs-entry-after (fn-bs-pending s)
                                      (fn-bs-durable-entry s dir name) dir name)))
   :hints (("Goal" :in-theory (enable fn-bs-lookup fn-bs-view fn-bs-durable-entry)))))

(local
 (defthm fn-bs-imp-entry-after-of-ops-for-other-dir
   (implies (not (equal d x))
            (equal (fn-bs-entry-after (fn-bs-ops-for-dir ops x) old d n) old))
   :hints (("Goal" :induct (fn-bs-ops-for-dir ops x)))))

(local
 (defthm fn-bs-imp-entry-after-of-ops-for-same-dir
   (equal (fn-bs-entry-after (fn-bs-ops-for-dir ops d) old d n)
          (fn-bs-entry-after ops old d n))
   :hints (("Goal" :induct (fn-bs-entry-after ops old d n)))))

(local
 (defthm fn-bs-imp-entry-after-of-ops-not-for-same-dir
   (equal (fn-bs-entry-after (fn-bs-ops-not-for-dir ops d) old d n) old)
   :hints (("Goal" :induct (fn-bs-ops-not-for-dir ops d)))))

(local
 (defthm fn-bs-imp-entry-after-of-ops-not-for-other-dir
   (implies (not (equal d x))
            (equal (fn-bs-entry-after (fn-bs-ops-not-for-dir ops x) old d n)
                   (fn-bs-entry-after ops old d n)))
   :hints (("Goal" :induct (fn-bs-entry-after ops old d n)))))

(local
 (defthm fn-bs-imp-entry-after-of-ops-for-ino
   (equal (fn-bs-entry-after (fn-bs-ops-for-ino ops ino) old d n) old)
   :hints (("Goal" :induct (fn-bs-ops-for-ino ops ino)))))

(local
 (defthm fn-bs-imp-entry-after-of-ops-not-for-ino
   (equal (fn-bs-entry-after (fn-bs-ops-not-for-ino ops ino) old d n)
          (fn-bs-entry-after ops old d n))
   :hints (("Goal" :induct (fn-bs-entry-after ops old d n)))))

(local
 (defthm fn-bs-imp-entry-after-is-an-outcome
   (member-equal (fn-bs-entry-after ops old d n)
                 (fn-bs-entry-outcomes (fn-bs-ops-for-name ops d n) old))
   :hints (("Goal" :induct (fn-bs-entry-after ops old d n)
            :in-theory (enable fn-bs-entry-outcomes fn-bs-ops-for-name)))))

; -----------------------------------------------------------------------------
; Staging, one segment at a time: the effect of a run in which every step
; returned :ok.

(local
 (defthm fn-bs-imp-splice-of-nothing
   (implies (fn-cbor-octet-listp o)
            (equal (fn-bs-splice nil 0 o) o))
   :hints (("Goal" :in-theory (enable fn-bs-splice fn-cbor-octet-listp)))))

(local
 (defthm fn-bs-imp-octets-true-listp
   (implies (fn-cbor-octet-listp o) (true-listp o))
   :hints (("Goal" :in-theory (enable fn-cbor-octet-listp)))
   :rule-classes :forward-chaining))

; The environment's answer to one syscall: :ok, or a failure (ERRNO . X)
; whose errno is not :ok.  A pair (:ok . N) would be a write that accepted
; N octets and reported success; write_all never reports that.
(defun fn-bs-imp-outcomep (x)
  (declare (xargs :guard t))
  (or (equal x :ok) (and (consp x) (not (equal (car x) :ok)))))

(defun fn-bs-imp-outcomesp (xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (and (fn-bs-imp-outcomep (car xs)) (fn-bs-imp-outcomesp (cdr xs)))
    t))

(local
 (defthm fn-bs-imp-outcomesp-parts
   (implies (fn-bs-imp-outcomesp xs)
            (and (fn-bs-imp-outcomep (if (consp xs) (car xs) :ok))
                 (fn-bs-imp-outcomesp (cdr xs))
                 (fn-bs-imp-outcomesp (nthcdr n xs))))))

; One syscall at a time.
(local
 (defthm fn-bs-imp-step-cut
   (equal (fn-bs-imp-step s ks (list :cut name) out groups capacity)
          (mv :ok s ks))
   :hints (("Goal" :in-theory (enable fn-bs-imp-step fn-bs-step)))))

(local
 (defthm fn-bs-imp-step-syscalls
   (and (equal (fn-bs-imp-step s ks (list :create d n) out groups capacity)
               (mv (mv-nth 0 (fn-bs-create s d n out))
                   (mv-nth 1 (fn-bs-create s d n out)) ks))
        (equal (fn-bs-imp-step s ks (list :write-all d n o) out groups capacity)
               (mv (mv-nth 0 (fn-bs-write s (fn-bs-lookup s d n) 0 o out))
                   (mv-nth 1 (fn-bs-write s (fn-bs-lookup s d n) 0 o out)) ks))
        (equal (fn-bs-imp-step s ks (list :fsync-file d n) out groups capacity)
               (mv (mv-nth 0 (fn-bs-fsync-file s (fn-bs-lookup s d n) out))
                   (mv-nth 1 (fn-bs-fsync-file s (fn-bs-lookup s d n) out)) ks))
        (equal (fn-bs-imp-step s ks (list :fsync-dir d) out groups capacity)
               (mv (mv-nth 0 (fn-bs-fsync-dir s d out))
                   (mv-nth 1 (fn-bs-fsync-dir s d out)) ks))
        (equal (fn-bs-imp-step s ks (list :mkdir p n id) out groups capacity)
               (mv (mv-nth 0 (fn-bs-mkdir s p n id out))
                   (mv-nth 1 (fn-bs-mkdir s p n id out)) ks))
        (equal (fn-bs-imp-step s ks (list :rename-dir-noreplace p n q m) out groups capacity)
               (mv (mv-nth 0 (fn-bs-rename-dir-noreplace s p n q m out))
                   (mv-nth 1 (fn-bs-rename-dir-noreplace s p n q m out)) ks)))
   :hints (("Goal" :in-theory (enable fn-bs-imp-step fn-bs-step)))))

(local
 (defthm fn-bs-imp-syscall-results
   (and (equal (mv-nth 0 (fn-bs-create s d n out))
               (cond ((fn-bs-lookup s d n) :eexist) ((equal out :ok) :ok) (t out)))
        (equal (mv-nth 0 (fn-bs-write s ino 0 o out))
               (cond ((not (assoc-equal ino (fn-bs-inodes s))) :ebadf)
                     ((equal out :ok) :ok) (t (car out))))
        (equal (mv-nth 0 (fn-bs-fsync-file s ino out))
               (if (equal out :ok) :ok (car out)))
        (equal (mv-nth 0 (fn-bs-fsync-dir s dir out))
               (if (equal out :ok) :ok (car out)))
        (equal (mv-nth 0 (fn-bs-mkdir s p n id out))
               (cond ((fn-bs-lookup s p n) :eexist)
                     ((assoc-equal id (fn-bs-dirs s)) :eexist)
                     ((equal out :ok) :ok) (t out))))
   :hints (("Goal" :in-theory (enable fn-bs-create fn-bs-write fn-bs-fsync-file
                                      fn-bs-fsync-dir fn-bs-mkdir)))))

(local
 (defthm fn-bs-imp-apply-writes-of-nothing
   (equal (fn-bs-apply-writes i nil) i)))

(local
 (defthm fn-bs-imp-take-of-own-length
   (implies (true-listp x) (equal (fn-bs-take (len x) x) x))))

(local
 (defthm fn-bs-imp-syscall-ok-states
   (and (implies (not (fn-bs-lookup s d n))
                 (equal (mv-nth 1 (fn-bs-create s d n :ok))
                        (fn-bs-make (fn-bs-unit s)
                                    (cons (cons (fn-bs-next-ino s) nil) (fn-bs-inodes s))
                                    (fn-bs-dirs s)
                                    (append (fn-bs-pending s)
                                            (list (list :set-entry d n (fn-bs-next-ino s))))
                                    (+ 1 (fn-bs-next-ino s)))))
        (implies (and (true-listp o) (assoc-equal ino (fn-bs-inodes s)))
                 (equal (mv-nth 1 (fn-bs-write s ino 0 o :ok))
                        (if (consp o)
                            (fn-bs-make (fn-bs-unit s) (fn-bs-inodes s) (fn-bs-dirs s)
                                        (append (fn-bs-pending s)
                                                (list (list :write ino 0 o)))
                                        (fn-bs-next-ino s))
                          s)))
        (equal (mv-nth 1 (fn-bs-fsync-file s ino :ok)) (fn-bs-fence-file s ino))
        (equal (mv-nth 1 (fn-bs-fsync-dir s dir :ok)) (fn-bs-fence-dir s dir))
        (implies (and (not (fn-bs-lookup s p n))
                      (not (assoc-equal id (fn-bs-dirs s))))
                 (equal (mv-nth 1 (fn-bs-mkdir s p n id :ok))
                        (fn-bs-make (fn-bs-unit s) (fn-bs-inodes s)
                                    (cons (cons id nil) (fn-bs-dirs s))
                                    (append (fn-bs-pending s)
                                            (list (list :set-entry p n id)))
                                    (fn-bs-next-ino s)))))
   :hints (("Goal" :in-theory (enable fn-bs-create fn-bs-write fn-bs-fsync-file
                                      fn-bs-fsync-dir fn-bs-mkdir)))))

(local
 (defthm fn-bs-imp-lookup-after-set-entry
   (implies (and d n)
            (equal (fn-bs-lookup (fn-bs-make u i dirs (append p (list (list :set-entry d2 n2 v))) nx)
                                 d n)
                   (if (and (equal d d2) (equal n n2)) v
                     (fn-bs-lookup (fn-bs-make u i dirs p nx) d n))))
   :hints (("Goal" :in-theory (enable fn-bs-durable-entry)))))

(local
 (defthm fn-bs-imp-lookup-after-write
   (implies (and d n)
            (equal (fn-bs-lookup (fn-bs-make u i dirs (append p (list (list :write ino off o))) nx)
                                 d n)
                   (fn-bs-lookup (fn-bs-make u i dirs p nx) d n)))
   :hints (("Goal" :in-theory (enable fn-bs-durable-entry)))))

(local (in-theory (disable fn-bs-imp-lookup-is-entry-after)))

(local
 (defthm fn-bs-imp-fence-file-of-make
   (equal (fn-bs-fence-file (fn-bs-make u i dirs q nx) ino)
          (fn-bs-make u (fn-bs-apply-writes i (fn-bs-ops-for-ino q ino)) dirs
                      (fn-bs-ops-not-for-ino q ino) nx))
   :hints (("Goal" :in-theory (enable fn-bs-fence-file)))))

; The state after one file's six steps, every step :ok.
(defun fn-bs-imp-file-state (s file)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bs-make (fn-bs-unit s)
              (if (consp (cddr file))
                  (fn-bs-apply-writes
                   (cons (cons (fn-bs-next-ino s) nil) (fn-bs-inodes s))
                   (list (list :write (fn-bs-next-ino s) 0 (cddr file))))
                (cons (cons (fn-bs-next-ino s) nil) (fn-bs-inodes s)))
              (fn-bs-dirs s)
              (append (fn-bs-pending s)
                      (list (list :set-entry (car file) (cadr file) (fn-bs-next-ino s))))
              (+ 1 (fn-bs-next-ino s))))

(local
 (defthm fn-bs-imp-one-file
   (implies (and (fn-bs-imp-entry-opsp (fn-bs-pending s))
                 (fn-bs-imp-outcomesp outs)
                 (consp file) (consp (cdr file))
                 (keywordp (car file)) (stringp (cadr file))
                 (fn-cbor-octet-listp (cddr file))
                 (fn-bs-imp-okp s ks (fn-bs-imp-file-steps file) outs groups capacity))
            (and (not (fn-bs-lookup s (car file) (cadr file)))
                 (equal (fn-bs-imp-final s ks (fn-bs-imp-file-steps file) outs groups capacity)
                        (cons (fn-bs-imp-file-state s file) ks))))
   :hints (("Goal" :do-not-induct t
            :expand ((:free (b k s0 o0) (fn-bs-imp-okp b k s0 o0 groups capacity))
                     (:free (b k s0 o0) (fn-bs-imp-final b k s0 o0 groups capacity)))
            :in-theory '((:congruence iff-implies-equal-not) (:definition assoc-equal)
              (:definition binary-append) (:definition fn-bs-durable-entry)
              (:definition fn-bs-entry-after) (:definition fn-bs-imp-entry-opsp)
              (:definition fn-bs-imp-file-state) (:definition fn-bs-imp-file-steps)
              (:definition fn-bs-imp-final) (:definition fn-bs-imp-okp)
              (:definition fn-bs-imp-outcomep) (:definition fn-bs-imp-outcomesp)
              (:definition fn-bs-ops-for-ino) (:definition fn-bs-ops-not-for-ino)
              (:definition fn-cbor-octet-listp) (:definition keywordp) (:definition mv-nth)
              (:definition not) (:executable-counterpart car) (:executable-counterpart cdr)
              (:executable-counterpart consp) (:executable-counterpart equal)
              (:executable-counterpart fn-bs-imp-entry-opsp)
              (:executable-counterpart fn-bs-imp-outcomep) (:executable-counterpart if)
              (:executable-counterpart not) (:executable-counterpart zp)
              (:forward-chaining fn-bs-imp-entry-opsp-true-listp)
              (:forward-chaining fn-bs-imp-keyword-is-not-nil)
              (:forward-chaining fn-bs-imp-octets-true-listp) (:rewrite car-cons)
              (:rewrite cdr-cons) (:rewrite cons-equal) (:rewrite default-cdr)
              (:rewrite fn-bs-dirs-of-fn-bs-make) (:rewrite fn-bs-entry-after-of-append)
              (:rewrite fn-bs-imp-apply-writes-of-nothing)
              (:rewrite fn-bs-imp-entry-ops-have-no-writes)
              (:rewrite fn-bs-imp-entry-opsp-of-append)
              (:rewrite fn-bs-imp-fence-file-of-make)
              (:rewrite fn-bs-imp-lookup-after-set-entry)
              (:rewrite fn-bs-imp-lookup-is-entry-after)
              (:rewrite fn-bs-imp-ops-not-for-ino-of-append) (:rewrite fn-bs-imp-step-cut)
              (:rewrite fn-bs-imp-step-syscalls) (:rewrite fn-bs-imp-syscall-ok-states)
              (:rewrite fn-bs-imp-syscall-results) (:rewrite fn-bs-inodes-of-fn-bs-make)
              (:rewrite fn-bs-next-ino-of-fn-bs-make) (:rewrite fn-bs-ops-for-ino-of-append)
              (:rewrite fn-bs-pending-of-fn-bs-make) (:rewrite fn-bs-unit-of-fn-bs-make)
              (:rewrite fn-cp-append-assoc) (:rewrite fn-cp-append-nil-left)
              (:rewrite nth-0-cons) (:rewrite nth-add1)
              (:type-prescription fn-bs-imp-entry-opsp)
              (:type-prescription fn-cbor-octet-listp))))))

(local
 (defthm fn-bs-imp-len-of-file-steps
   (equal (len (fn-bs-imp-file-steps file)) 6)))

(local (in-theory (disable fn-bs-imp-file-steps)))

(defun fn-bs-imp-files-shapep (files)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp files)
      (and (consp (car files)) (consp (cdr (car files)))
           (keywordp (car (car files)))
           (stringp (cadr (car files)))
           (fn-cbor-octet-listp (cddr (car files)))
           (fn-bs-imp-files-shapep (cdr files)))
    t))

(defun fn-bs-imp-files-state (s files)
  (declare (xargs :guard t :verify-guards nil :measure (len files)))
  (if (consp files)
      (fn-bs-imp-files-state (fn-bs-imp-file-state s (car files)) (cdr files))
    s))

; Each file's name was free in the view when it was created.
(defun fn-bs-imp-files-freshp (s files)
  (declare (xargs :guard t :verify-guards nil :measure (len files)))
  (if (consp files)
      (and (not (fn-bs-lookup s (car (car files)) (cadr (car files))))
           (fn-bs-imp-files-freshp (fn-bs-imp-file-state s (car files)) (cdr files)))
    t))

(defun fn-bs-imp-file-entries (files ino)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp files)
      (cons (list :set-entry (car (car files)) (cadr (car files)) ino)
            (fn-bs-imp-file-entries (cdr files) (+ 1 ino)))
    nil))

(defun fn-bs-imp-contentsp (inodes files ino)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp files)
      (and (equal (cdr (assoc-equal ino inodes)) (cddr (car files)))
           (fn-bs-imp-contentsp inodes (cdr files) (+ 1 ino)))
    t))

(defun fn-bs-imp-view-filesp (s files ino)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp files)
      (and (equal (fn-bs-lookup s (car (car files)) (cadr (car files))) ino)
           (fn-bs-imp-view-filesp s (cdr files) (+ 1 ino)))
    t))

(local
 (defthm fn-bs-imp-entry-opsp-of-file-state
   (implies (fn-bs-imp-entry-opsp (fn-bs-pending s))
            (fn-bs-imp-entry-opsp (fn-bs-pending (fn-bs-imp-file-state s file))))))

(local
 (defun fn-bs-imp-files-induct (s files outs)
   (declare (xargs :verify-guards nil :measure (len files)))
   (if (consp files)
       (fn-bs-imp-files-induct (fn-bs-imp-file-state s (car files)) (cdr files)
                               (nthcdr 6 outs))
     (list s outs))))

(local
 (defthm fn-bs-imp-files-ok
   (implies (and (fn-bs-imp-entry-opsp (fn-bs-pending s))
                 (fn-bs-imp-outcomesp outs)
                 (fn-bs-imp-files-shapep files)
                 (fn-bs-imp-okp s ks (fn-bs-imp-files-steps files) outs groups capacity))
            (and (fn-bs-imp-files-freshp s files)
                 (equal (fn-bs-imp-final s ks (fn-bs-imp-files-steps files) outs
                                         groups capacity)
                        (cons (fn-bs-imp-files-state s files) ks))))
   :hints (("Goal" :induct (fn-bs-imp-files-induct s files outs)
            :in-theory '((:definition fn-bs-imp-files-freshp) (:definition fn-bs-imp-files-shapep)
              (:definition fn-bs-imp-files-state) (:definition fn-bs-imp-files-steps)
              (:definition fn-bs-imp-final) (:definition fn-bs-imp-okp)
              (:definition fn-bs-imp-outcomep) (:definition fn-bs-imp-outcomesp)
              (:definition keywordp) (:definition not) (:definition nthcdr)
              (:executable-counterpart binary-+) (:executable-counterpart consp)
              (:executable-counterpart equal) (:executable-counterpart fn-bs-imp-outcomesp)
              (:executable-counterpart nthcdr) (:executable-counterpart zp)
              (:induction fn-bs-imp-files-induct) (:rewrite car-cons) (:rewrite cdr-cons)
              (:rewrite default-cdr) (:rewrite fn-bs-imp-entry-opsp-of-file-state)
              (:rewrite fn-bs-imp-final-of-append) (:rewrite fn-bs-imp-len-of-file-steps)
              (:rewrite fn-bs-imp-okp-of-append) (:rewrite fn-bs-imp-one-file)
              (:rewrite fn-bs-imp-outcomesp-parts) (:type-prescription fn-bs-imp-entry-opsp)
              (:type-prescription fn-bs-imp-files-freshp) (:type-prescription fn-bs-imp-okp)
              (:type-prescription fn-bs-imp-outcomesp)
              (:type-prescription fn-cbor-octet-listp)))
           ("Subgoal *1/1" :use ((:instance fn-bs-imp-one-file (file (car files))))))))

(local (in-theory (disable fn-bs-imp-file-state)))

(local
 (defthm fn-bs-imp-file-state-parts
   (and (equal (fn-bs-pending (fn-bs-imp-file-state s file))
               (append (fn-bs-pending s)
                       (list (list :set-entry (car file) (cadr file) (fn-bs-next-ino s)))))
        (equal (fn-bs-dirs (fn-bs-imp-file-state s file)) (fn-bs-dirs s))
        (equal (fn-bs-unit (fn-bs-imp-file-state s file)) (fn-bs-unit s))
        (equal (fn-bs-next-ino (fn-bs-imp-file-state s file)) (+ 1 (fn-bs-next-ino s)))
        (implies (fn-cbor-octet-listp (cddr file))
                 (equal (assoc-equal ino (fn-bs-inodes (fn-bs-imp-file-state s file)))
                        (if (equal ino (fn-bs-next-ino s))
                            (cons ino (cddr file))
                          (assoc-equal ino (fn-bs-inodes s))))))
   :hints (("Goal" :in-theory (enable fn-bs-imp-file-state)))))

(local
 (defthm fn-bs-imp-files-state-parts
   (and (implies (true-listp (fn-bs-pending s))
                 (equal (fn-bs-pending (fn-bs-imp-files-state s files))
                        (append (fn-bs-pending s)
                                (fn-bs-imp-file-entries files (fn-bs-next-ino s)))))
        (equal (fn-bs-dirs (fn-bs-imp-files-state s files)) (fn-bs-dirs s))
        (equal (fn-bs-unit (fn-bs-imp-files-state s files)) (fn-bs-unit s))
        (implies (acl2-numberp (fn-bs-next-ino s))
                 (equal (fn-bs-next-ino (fn-bs-imp-files-state s files))
                        (+ (fn-bs-next-ino s) (len files)))))
   :hints (("Goal" :induct (fn-bs-imp-files-state s files)))))

(local
 (defthm fn-bs-imp-files-state-inode-frame
   (implies (and (fn-bs-imp-files-shapep files)
                 (rationalp (fn-bs-next-ino s)) (rationalp ino)
                 (< ino (fn-bs-next-ino s)))
            (equal (assoc-equal ino (fn-bs-inodes (fn-bs-imp-files-state s files)))
                   (assoc-equal ino (fn-bs-inodes s))))
   :hints (("Goal" :induct (fn-bs-imp-files-state s files)))))

(local
 (defthm fn-bs-imp-files-state-contents
   (implies (and (fn-bs-imp-files-shapep files) (natp (fn-bs-next-ino s)))
            (fn-bs-imp-contentsp (fn-bs-inodes (fn-bs-imp-files-state s files))
                                 files (fn-bs-next-ino s)))
   :hints (("Goal" :induct (fn-bs-imp-files-state s files)))))

(local
 (defthm fn-bs-imp-files-state-contents-at
   (implies (and (fn-bs-imp-files-shapep files) (natp (fn-bs-next-ino s))
                 (equal ino (fn-bs-next-ino s)))
            (fn-bs-imp-contentsp (fn-bs-inodes (fn-bs-imp-files-state s files))
                                 files ino))))

(local
 (defthm fn-bs-imp-lookup-of-file-state
   (implies (and x y)
            (equal (fn-bs-lookup (fn-bs-imp-file-state s file) x y)
                   (if (and (equal x (car file)) (equal y (cadr file)))
                       (fn-bs-next-ino s)
                     (fn-bs-lookup s x y))))
   :hints (("Goal" :in-theory (enable fn-bs-imp-file-state fn-bs-durable-entry
                                      fn-bs-imp-lookup-is-entry-after)))))

(local
 (defthm fn-bs-imp-files-state-lookup-frame
   (implies (and x y (fn-bs-lookup s x y) (fn-bs-imp-files-freshp s files))
            (equal (fn-bs-lookup (fn-bs-imp-files-state s files) x y)
                   (fn-bs-lookup s x y)))
   :hints (("Goal" :induct (fn-bs-imp-files-state s files)))))

(local
 (defthm fn-bs-imp-files-state-view
   (implies (and (fn-bs-imp-files-shapep files) (fn-bs-imp-files-freshp s files)
                 (natp (fn-bs-next-ino s)))
            (fn-bs-imp-view-filesp (fn-bs-imp-files-state s files) files (fn-bs-next-ino s)))
   :hints (("Goal" :induct (fn-bs-imp-files-state s files)))))

(local
 (defthm fn-bs-imp-files-state-view-at
   (implies (and (fn-bs-imp-files-shapep files) (fn-bs-imp-files-freshp s files)
                 (natp (fn-bs-next-ino s)) (equal ino (fn-bs-next-ino s)))
            (fn-bs-imp-view-filesp (fn-bs-imp-files-state s files) files ino))))

; The subdirectories.
(defun fn-bs-imp-subdir-state (s sub)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bs-make (fn-bs-unit s) (fn-bs-inodes s)
              (cons (cons (cdr sub) nil) (fn-bs-dirs s))
              (append (fn-bs-pending s) (list (list :set-entry :stage (car sub) (cdr sub))))
              (fn-bs-next-ino s)))

(local (in-theory (disable fn-bs-imp-subdir-state)))

(defun fn-bs-imp-subdirs-state (s subdirs)
  (declare (xargs :guard t :verify-guards nil :measure (len subdirs)))
  (if (consp subdirs)
      (fn-bs-imp-subdirs-state (fn-bs-imp-subdir-state s (car subdirs)) (cdr subdirs))
    s))

(defun fn-bs-imp-subdirs-freshp (s subdirs)
  (declare (xargs :guard t :verify-guards nil :measure (len subdirs)))
  (if (consp subdirs)
      (and (not (fn-bs-lookup s :stage (car (car subdirs))))
           (not (assoc-equal (cdr (car subdirs)) (fn-bs-dirs s)))
           (fn-bs-imp-subdirs-freshp (fn-bs-imp-subdir-state s (car subdirs)) (cdr subdirs)))
    t))

(defun fn-bs-imp-subdir-entries (subdirs)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp subdirs)
      (cons (list :set-entry :stage (car (car subdirs)) (cdr (car subdirs)))
            (fn-bs-imp-subdir-entries (cdr subdirs)))
    nil))

(defun fn-bs-imp-view-subdirsp (s subdirs)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp subdirs)
      (and (equal (fn-bs-lookup s :stage (car (car subdirs))) (cdr (car subdirs)))
           (fn-bs-imp-view-subdirsp s (cdr subdirs)))
    t))

(local
 (defun fn-bs-imp-subdirs-induct (s subdirs outs)
   (declare (xargs :verify-guards nil :measure (len subdirs)))
   (if (consp subdirs)
       (fn-bs-imp-subdirs-induct (fn-bs-imp-subdir-state s (car subdirs)) (cdr subdirs)
                                 (cddr outs))
     (list s outs))))

(local
 (defthm fn-bs-imp-subdirs-ok
   (implies (and (fn-bs-imp-outcomesp outs)
                 (fn-bs-imp-okp s ks (fn-bs-imp-subdir-steps subdirs) outs groups capacity))
            (and (fn-bs-imp-subdirs-freshp s subdirs)
                 (equal (fn-bs-imp-final s ks (fn-bs-imp-subdir-steps subdirs) outs
                                         groups capacity)
                        (cons (fn-bs-imp-subdirs-state s subdirs) ks))))
   :hints (("Goal" :induct (fn-bs-imp-subdirs-induct s subdirs outs)
            :expand ((:free (b k o0) (fn-bs-imp-okp b k (fn-bs-imp-subdir-steps subdirs)
                                                    o0 groups capacity))
                     (:free (b k o0) (fn-bs-imp-final b k (fn-bs-imp-subdir-steps subdirs)
                                                      o0 groups capacity))
                     (:free (b k s0 o0) (fn-bs-imp-okp b k (cons (list :cut "import-subdir-created") s0)
                                                       o0 groups capacity))
                     (:free (b k s0 o0) (fn-bs-imp-final b k (cons (list :cut "import-subdir-created") s0)
                                                         o0 groups capacity)))
            :in-theory '((:definition fn-bs-imp-final) (:definition fn-bs-imp-okp)
              (:definition fn-bs-imp-outcomep) (:definition fn-bs-imp-outcomesp)
              (:definition fn-bs-imp-subdir-state) (:definition fn-bs-imp-subdir-steps)
              (:definition fn-bs-imp-subdirs-freshp) (:definition fn-bs-imp-subdirs-state)
              (:definition mv-nth) (:definition not) (:executable-counterpart cdr)
              (:executable-counterpart consp) (:executable-counterpart equal)
              (:executable-counterpart not) (:executable-counterpart tau-system)
              (:executable-counterpart zp) (:induction fn-bs-imp-subdirs-induct)
              (:rewrite car-cons) (:rewrite cdr-cons) (:rewrite cons-equal)
              (:rewrite default-cdr) (:rewrite fn-bs-imp-outcomesp-parts)
              (:rewrite fn-bs-imp-step-cut) (:rewrite fn-bs-imp-step-syscalls)
              (:rewrite fn-bs-imp-syscall-ok-states) (:rewrite fn-bs-imp-syscall-results)
              (:type-prescription fn-bs-imp-outcomesp)
              (:type-prescription fn-bs-imp-subdir-steps)
              (:type-prescription fn-bs-imp-subdirs-freshp))))))

(local
 (defthm fn-bs-imp-subdirs-state-parts
   (and (implies (true-listp (fn-bs-pending s))
                 (equal (fn-bs-pending (fn-bs-imp-subdirs-state s subdirs))
                        (append (fn-bs-pending s) (fn-bs-imp-subdir-entries subdirs))))
        (equal (fn-bs-inodes (fn-bs-imp-subdirs-state s subdirs)) (fn-bs-inodes s))
        (equal (fn-bs-unit (fn-bs-imp-subdirs-state s subdirs)) (fn-bs-unit s))
        (equal (fn-bs-next-ino (fn-bs-imp-subdirs-state s subdirs)) (fn-bs-next-ino s))
        (implies (and (assoc-equal x (fn-bs-dirs s))
                      (fn-bs-imp-subdirs-freshp s subdirs))
                 (and (equal (assoc-equal x (fn-bs-dirs (fn-bs-imp-subdirs-state s subdirs)))
                             (assoc-equal x (fn-bs-dirs s)))
                      (not (member-equal x (strip-cdrs subdirs))))))
   :hints (("Goal" :induct (fn-bs-imp-subdirs-state s subdirs)
            :in-theory (enable fn-bs-imp-subdir-state)))))

(local
 (defthm fn-bs-imp-lookup-of-subdir-state
   (implies (and x y (not (assoc-equal (cdr sub) (fn-bs-dirs s))))
            (equal (fn-bs-lookup (fn-bs-imp-subdir-state s sub) x y)
                   (if (and (equal x :stage) (equal y (car sub)))
                       (cdr sub)
                     (fn-bs-lookup s x y))))
   :hints (("Goal" :in-theory (enable fn-bs-imp-subdir-state fn-bs-durable-entry
                                      fn-bs-imp-lookup-is-entry-after)))))

(local
 (defthm fn-bs-imp-subdirs-state-lookup-frame
   (implies (and x y (fn-bs-lookup s x y) (fn-bs-imp-subdirs-freshp s subdirs))
            (equal (fn-bs-lookup (fn-bs-imp-subdirs-state s subdirs) x y)
                   (fn-bs-lookup s x y)))
   :hints (("Goal" :induct (fn-bs-imp-subdirs-state s subdirs)))))

(local
 (defthm fn-bs-imp-subdirs-state-view
   (implies (and (fn-bs-imp-subdirsp subdirs) (fn-bs-imp-subdirs-freshp s subdirs))
            (fn-bs-imp-view-subdirsp (fn-bs-imp-subdirs-state s subdirs) subdirs))
   :hints (("Goal" :induct (fn-bs-imp-subdirs-state s subdirs)))))


; The fences.
(defun fn-bs-imp-fences-state (s subdirs)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp subdirs)
      (fn-bs-imp-fences-state (fn-bs-fence-dir s (cdr (car subdirs))) (cdr subdirs))
    s))

(local
 (defun fn-bs-imp-fences-induct (s subdirs outs)
   (declare (xargs :verify-guards nil :measure (len subdirs)))
   (if (consp subdirs)
       (fn-bs-imp-fences-induct (fn-bs-fence-dir s (cdr (car subdirs))) (cdr subdirs)
                                (cddr outs))
     (list s outs))))

(local
 (defthm fn-bs-imp-fences-ok
   (implies (and (fn-bs-imp-outcomesp outs)
                 (fn-bs-imp-okp s ks (fn-bs-imp-fence-steps subdirs) outs groups capacity))
            (equal (fn-bs-imp-final s ks (fn-bs-imp-fence-steps subdirs) outs groups capacity)
                   (cons (fn-bs-imp-fences-state s subdirs) ks)))
   :hints (("Goal" :induct (fn-bs-imp-fences-induct s subdirs outs)
            :expand ((:free (b k o0) (fn-bs-imp-okp b k (fn-bs-imp-fence-steps subdirs)
                                                    o0 groups capacity))
                     (:free (b k o0) (fn-bs-imp-final b k (fn-bs-imp-fence-steps subdirs)
                                                      o0 groups capacity))
                     (:free (b k s0 o0) (fn-bs-imp-okp b k (cons (list :cut "import-subdir-durable") s0)
                                                       o0 groups capacity))
                     (:free (b k s0 o0) (fn-bs-imp-final b k (cons (list :cut "import-subdir-durable") s0)
                                                         o0 groups capacity)))))))

(local
 (defthm fn-bs-imp-fence-dir-parts
   (and (equal (fn-bs-inodes (fn-bs-fence-dir s x)) (fn-bs-inodes s))
        (equal (fn-bs-unit (fn-bs-fence-dir s x)) (fn-bs-unit s))
        (equal (fn-bs-next-ino (fn-bs-fence-dir s x)) (fn-bs-next-ino s))
        (equal (fn-bs-pending (fn-bs-fence-dir s x))
               (fn-bs-ops-not-for-dir (fn-bs-pending s) x))
        (implies (and d n (not (equal d x)))
                 (equal (fn-bs-durable-entry (fn-bs-fence-dir s x) d n)
                        (fn-bs-durable-entry s d n)))
        (implies (and d n)
                 (equal (fn-bs-lookup (fn-bs-fence-dir s x) d n)
                        (fn-bs-lookup s d n))))
   :hints (("Goal" :in-theory (enable fn-bs-fence-dir fn-bs-durable-entry
                                      fn-bs-imp-lookup-is-entry-after)
            :cases ((equal d x))))))

(local
 (defthm fn-bs-imp-fences-state-parts
   (and (equal (fn-bs-inodes (fn-bs-imp-fences-state s subdirs)) (fn-bs-inodes s))
        (equal (fn-bs-unit (fn-bs-imp-fences-state s subdirs)) (fn-bs-unit s))
        (equal (fn-bs-next-ino (fn-bs-imp-fences-state s subdirs)) (fn-bs-next-ino s))
        (implies (and d n (not (member-equal d (strip-cdrs subdirs))))
                 (equal (fn-bs-durable-entry (fn-bs-imp-fences-state s subdirs) d n)
                        (fn-bs-durable-entry s d n)))
        (implies (and d n)
                 (equal (fn-bs-lookup (fn-bs-imp-fences-state s subdirs) d n)
                        (fn-bs-lookup s d n))))
   :hints (("Goal" :induct (fn-bs-imp-fences-state s subdirs)))))

; The operations whose directory is outside DIRS.
(defun fn-bs-imp-ops-outside (ops dirs)
  (declare (xargs :guard t :verify-guards nil))
  (cond ((atom ops) nil)
        ((member-equal (nth 1 (car ops)) dirs) (fn-bs-imp-ops-outside (cdr ops) dirs))
        (t (cons (car ops) (fn-bs-imp-ops-outside (cdr ops) dirs)))))

(local
 (defthm fn-bs-imp-ops-not-for-dir-is-outside
   (implies (fn-bs-imp-entry-opsp ops)
            (equal (fn-bs-ops-not-for-dir ops x)
                   (fn-bs-imp-ops-outside ops (list x))))))

(local
 (defthm fn-bs-imp-outside-of-outside
   (equal (fn-bs-imp-ops-outside (fn-bs-imp-ops-outside ops a) b)
          (fn-bs-imp-ops-outside ops (append a b)))))

(local
 (defthm fn-bs-imp-entry-opsp-of-outside
   (implies (fn-bs-imp-entry-opsp ops)
            (fn-bs-imp-entry-opsp (fn-bs-imp-ops-outside ops dirs)))))

(local
 (defthm fn-bs-imp-fences-state-pending
   (implies (fn-bs-imp-entry-opsp (fn-bs-pending s))
            (equal (fn-bs-pending (fn-bs-imp-fences-state s subdirs))
                   (fn-bs-imp-ops-outside (fn-bs-pending s) (strip-cdrs subdirs))))
   :hints (("Goal" :induct (fn-bs-imp-fences-state s subdirs)
            :in-theory (disable fn-bs-imp-ops-not-for-dir-is-outside))
           ("Subgoal *1/1" :use ((:instance fn-bs-imp-ops-not-for-dir-is-outside
                                            (ops (fn-bs-pending s))
                                            (x (cdr (car subdirs)))))))))

(local
 (defthm fn-bs-imp-outside-of-file-entries
   (implies (fn-bs-imp-filesp files (cons :stage ids))
            (equal (fn-bs-imp-ops-outside (fn-bs-imp-file-entries files ino)
                                          (append ids (list :stage)))
                   nil))))

(local
 (defthm fn-bs-imp-outside-of-subdir-entries
   (equal (fn-bs-imp-ops-outside (fn-bs-imp-subdir-entries subdirs)
                                 (append ids (list :stage)))
          nil)))

(local
 (defthm fn-bs-imp-outside-of-append
   (equal (fn-bs-imp-ops-outside (append a b) dirs)
          (append (fn-bs-imp-ops-outside a dirs) (fn-bs-imp-ops-outside b dirs)))))

; From the view to the durable tree: once only the parent's entry for the
; staged directory is pending, every other entry the process sees is durable.
(defun fn-bs-imp-parent-onlyp (ops)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp ops)
      (and (consp (car ops))
           (member-equal (car (car ops)) '(:set-entry :del-entry))
           (equal (nth 1 (car ops)) :parent)
           (fn-bs-imp-parent-onlyp (cdr ops)))
    (null ops)))

(local
 (defthm fn-bs-imp-entry-after-of-parent-only
   (implies (and (fn-bs-imp-parent-onlyp ops) (not (equal d :parent)))
            (equal (fn-bs-entry-after ops old d n) old))))

(local
 (defthm fn-bs-imp-durable-is-lookup-off-parent
   (implies (and d n (not (equal d :parent))
                 (fn-bs-imp-parent-onlyp (fn-bs-pending s)))
            (equal (fn-bs-durable-entry s d n) (fn-bs-lookup s d n)))
   :hints (("Goal" :in-theory (enable fn-bs-imp-lookup-is-entry-after)))))

(local
 (defthm fn-bs-imp-view-subdirs-is-complete
   (implies (and (fn-bs-imp-view-subdirsp s subdirs) (fn-bs-imp-subdirsp subdirs)
                 (fn-bs-imp-parent-onlyp (fn-bs-pending s)))
            (fn-bs-imp-subdirs-completep s subdirs))))

(defun fn-bs-imp-files-off-parentp (files)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp files)
      (and (not (equal (car (car files)) :parent))
           (fn-bs-imp-files-off-parentp (cdr files)))
    t))

(local
 (defthm fn-bs-imp-filesp-off-parent
   (implies (and (fn-bs-imp-filesp files dirs) (not (member-equal :parent dirs)))
            (fn-bs-imp-files-off-parentp files))))

(local
 (defthm fn-bs-imp-view-files-is-complete
   (implies (and (fn-bs-imp-view-filesp s files ino)
                 (fn-bs-imp-contentsp (fn-bs-inodes s) files ino)
                 (fn-bs-imp-files-off-parentp files)
                 (fn-bs-imp-files-shapep files)
                 (fn-bs-imp-parent-onlyp (fn-bs-pending s)))
            (fn-bs-imp-files-completep s files ino))
   :hints (("Goal" :in-theory (e/d (fn-bs-durable-content)
                                   (fn-bs-imp-lookup-is-entry-after))))))

(local
 (defthm fn-bs-imp-view-subdirs-through-one-file
   (implies (and (fn-bs-imp-view-subdirsp s subdirs) (fn-bs-imp-subdirsp subdirs)
                 (car file) (cadr file)
                 (not (fn-bs-lookup s (car file) (cadr file))))
            (fn-bs-imp-view-subdirsp (fn-bs-imp-file-state s file) subdirs))))

(local
 (defthm fn-bs-imp-view-subdirs-through-files
   (implies (and (fn-bs-imp-view-subdirsp s subdirs) (fn-bs-imp-subdirsp subdirs)
                 (fn-bs-imp-files-shapep files)
                 (fn-bs-imp-files-freshp s files))
            (fn-bs-imp-view-subdirsp (fn-bs-imp-files-state s files) subdirs))
   :hints (("Goal" :induct (fn-bs-imp-files-state s files)))))

(local
 (defthm fn-bs-imp-view-subdirs-through-fence
   (implies (fn-bs-imp-subdirsp subdirs)
            (equal (fn-bs-imp-view-subdirsp (fn-bs-fence-dir s x) subdirs)
                   (fn-bs-imp-view-subdirsp s subdirs)))))

(local
 (defthm fn-bs-imp-view-subdirs-through-fences
   (implies (fn-bs-imp-subdirsp subdirs)
            (equal (fn-bs-imp-view-subdirsp (fn-bs-imp-fences-state s l) subdirs)
                   (fn-bs-imp-view-subdirsp s subdirs)))
   :hints (("Goal" :induct (fn-bs-imp-fences-state s l)))))

(local
 (defthm fn-bs-imp-view-files-through-fence
   (implies (fn-bs-imp-files-shapep files)
            (equal (fn-bs-imp-view-filesp (fn-bs-fence-dir s x) files ino)
                   (fn-bs-imp-view-filesp s files ino)))))

(local
 (defthm fn-bs-imp-view-files-through-fences
   (implies (fn-bs-imp-files-shapep files)
            (equal (fn-bs-imp-view-filesp (fn-bs-imp-fences-state s l) files ino)
                   (fn-bs-imp-view-filesp s files ino)))
   :hints (("Goal" :induct (fn-bs-imp-fences-state s l)))))

(local
 (defthm fn-bs-imp-member-of-keyword-list
   (implies (and (member-equal x l) (keyword-listp l)) (keywordp x))
   :hints (("Goal" :in-theory (disable keywordp)))))

(local
 (defthm fn-bs-imp-filesp-is-shaped
   (implies (and (fn-bs-imp-filesp files dirs) (keyword-listp dirs))
            (fn-bs-imp-files-shapep files))
   :hints (("Goal" :in-theory (disable keywordp)))))

(local
 (defthm fn-bs-imp-subdirsp-ids-are-keywords
   (implies (fn-bs-imp-subdirsp subdirs) (keyword-listp (strip-cdrs subdirs)))))

(local
 (defthm fn-bs-imp-entry-opsp-of-subdir-entries
   (fn-bs-imp-entry-opsp (fn-bs-imp-subdir-entries subdirs))))

(local
 (defthm fn-bs-imp-entry-opsp-of-files-entries
   (fn-bs-imp-entry-opsp (fn-bs-imp-file-entries files ino))))

; The first two steps.
(defun fn-bs-imp-stage-state (bs stage)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bs-make (fn-bs-unit bs) (fn-bs-inodes bs)
              (cons (cons :stage nil) (fn-bs-dirs bs))
              (list (list :set-entry :parent stage :stage))
              (fn-bs-next-ino bs)))

(local
 (defthm fn-bs-imp-stage-ok
   (implies (and (null (fn-bs-pending bs))
                 (stringp stage)
                 (fn-bs-imp-outcomesp outs)
                 (fn-bs-imp-okp bs ks (fn-bs-imp-stage-steps stage) outs groups capacity))
            (and (not (assoc-equal :stage (fn-bs-dirs bs)))
                 (not (fn-bs-durable-entry bs :parent stage))
                 (equal (fn-bs-imp-final bs ks (fn-bs-imp-stage-steps stage) outs groups capacity)
                        (cons (fn-bs-imp-stage-state bs stage) ks))))
   :hints (("Goal" :in-theory (enable fn-bs-imp-stage-steps fn-bs-imp-lookup-is-entry-after)
            :expand ((:free (b k s0 o0) (fn-bs-imp-okp b k s0 o0 groups capacity))
                            (:free (b k s0 o0) (fn-bs-imp-final b k s0 o0 groups capacity)))))))

(local
 (defthm fn-bs-imp-stage-state-parts
   (and (equal (fn-bs-pending (fn-bs-imp-stage-state bs stage))
               (list (list :set-entry :parent stage :stage)))
        (equal (fn-bs-inodes (fn-bs-imp-stage-state bs stage)) (fn-bs-inodes bs))
        (equal (fn-bs-next-ino (fn-bs-imp-stage-state bs stage)) (fn-bs-next-ino bs))
        (equal (assoc-equal :parent (fn-bs-dirs (fn-bs-imp-stage-state bs stage)))
               (assoc-equal :parent (fn-bs-dirs bs)))
        (implies (stringp stage)
                 (equal (fn-bs-lookup (fn-bs-imp-stage-state bs stage) :parent stage) :stage)))
   :hints (("Goal" :in-theory (enable fn-bs-imp-lookup-is-entry-after fn-bs-durable-entry)))))

(local (in-theory (disable fn-bs-imp-stage-state)))

(local
 (defthm fn-bs-imp-seal-ok
   (implies (and (fn-bs-imp-outcomesp outs)
                 (fn-bs-imp-okp s ks (fn-bs-imp-seal-steps) outs groups capacity))
            (equal (fn-bs-imp-final s ks (fn-bs-imp-seal-steps) outs groups capacity)
                   (cons (fn-bs-fence-dir s :stage) ks)))
   :hints (("Goal" :in-theory (enable fn-bs-imp-seal-steps)
            :expand ((:free (b k s0 o0) (fn-bs-imp-okp b k s0 o0 groups capacity))
                     (:free (b k s0 o0) (fn-bs-imp-final b k s0 o0 groups capacity)))))))

(local (in-theory (disable fn-bs-imp-stage-steps fn-bs-imp-seal-steps
                           (:e fn-bs-imp-seal-steps))))

(local
 (defthm fn-bs-imp-durable-entry-by-dirs
   (implies (equal (assoc-equal d (fn-bs-dirs s2)) (assoc-equal d (fn-bs-dirs s)))
            (equal (equal (fn-bs-durable-entry s2 d n) (fn-bs-durable-entry s d n)) t))
   :hints (("Goal" :in-theory (enable fn-bs-durable-entry)))))

(local
 (defthm fn-bs-imp-durable-entry-through-staging
   (and (equal (fn-bs-durable-entry (fn-bs-imp-files-state s files) d n)
               (fn-bs-durable-entry s d n))
        (implies (and (assoc-equal :parent (fn-bs-dirs s))
                      (fn-bs-imp-subdirs-freshp s subdirs))
                 (equal (fn-bs-durable-entry (fn-bs-imp-subdirs-state s subdirs) :parent n)
                        (fn-bs-durable-entry s :parent n)))
        (equal (fn-bs-durable-entry (fn-bs-imp-stage-state bs stage) :parent n)
               (fn-bs-durable-entry bs :parent n)))
   :hints (("Goal" :in-theory (enable fn-bs-durable-entry fn-bs-imp-stage-state)))))

(local
 (defthm fn-bs-imp-staged-pending
   (implies (and (not (member-equal :parent (strip-cdrs subdirs)))
                 (fn-bs-imp-filesp files (cons :stage (strip-cdrs subdirs))))
            (equal (fn-bs-ops-not-for-dir
                    (fn-bs-pending
                     (fn-bs-imp-fences-state
                      (fn-bs-imp-files-state
                       (fn-bs-imp-subdirs-state (fn-bs-imp-stage-state bs stage) subdirs)
                       files)
                      subdirs))
                    :stage)
                   (list (list :set-entry :parent stage :stage))))
   :hints (("Goal" :do-not-induct t))))

(local
 (defthm fn-bs-imp-staging-completes
   (implies (and (fn-bs-imp-inputp bs stage root subdirs files old)
                 (fn-bs-imp-outcomesp outs)
                 (fn-bs-imp-okp bs ks (fn-bs-imp-staging-program stage subdirs files)
                                outs groups capacity))
            (let ((f (fn-bs-imp-final bs ks (fn-bs-imp-staging-program stage subdirs files)
                                      outs groups capacity)))
              (and (equal (cdr f) ks)
                   (not (member-equal :parent (strip-cdrs subdirs)))
                   (equal (fn-bs-pending (car f)) (list (list :set-entry :parent stage :stage)))
                   (fn-bs-imp-completep (car f) subdirs files (fn-bs-next-ino bs))
                   (equal (fn-bs-durable-entry (car f) :parent root) old)
                   (equal (fn-bs-durable-entry (car f) :parent stage) nil)
                   (equal (fn-bs-lookup (car f) :parent stage) :stage))))
   :hints (("Goal" :do-not-induct t
            :in-theory '((:compound-recognizer natp-compound-recognizer) (:definition binary-append)
              (:definition fn-bs-imp-completep) (:definition fn-bs-imp-entry-opsp)
              (:definition fn-bs-imp-inputp) (:definition fn-bs-imp-ops-outside)
              (:definition fn-bs-imp-outcomep) (:definition fn-bs-imp-outcomesp)
              (:definition fn-bs-imp-parent-onlyp) (:definition fn-bs-imp-staging-program)
              (:definition keyword-listp) (:definition member-equal) (:definition natp)
              (:definition not) (:definition null) (:executable-counterpart binary-append)
              (:executable-counterpart cons) (:executable-counterpart equal)
              (:executable-counterpart fn-bs-imp-parent-onlyp)
              (:executable-counterpart keywordp) (:executable-counterpart member-equal)
              (:executable-counterpart not) (:rewrite car-cons) (:rewrite cdr-cons)
              (:rewrite fn-bs-imp-durable-entry-through-staging)
              (:rewrite fn-bs-imp-entry-opsp-of-append)
              (:rewrite fn-bs-imp-entry-opsp-of-files-entries)
              (:rewrite fn-bs-imp-entry-opsp-of-outside)
              (:rewrite fn-bs-imp-entry-opsp-of-subdir-entries)
              (:rewrite fn-bs-imp-fence-dir-parts) (:rewrite fn-bs-imp-fences-state-parts)
              (:rewrite fn-bs-imp-fences-state-pending)
              (:rewrite fn-bs-imp-files-state-contents-at)
              (:rewrite fn-bs-imp-files-state-lookup-frame)
              (:rewrite fn-bs-imp-files-state-parts)
              (:rewrite fn-bs-imp-files-state-view-at) (:rewrite fn-bs-imp-filesp-is-shaped)
              (:rewrite fn-bs-imp-filesp-off-parent) (:rewrite fn-bs-imp-final-of-append)
              (:rewrite fn-bs-imp-okp-of-append)
              (:rewrite fn-bs-imp-ops-not-for-dir-is-outside)
              (:rewrite fn-bs-imp-outcomesp-parts) (:rewrite fn-bs-imp-outside-of-append)
              (:rewrite fn-bs-imp-outside-of-file-entries)
              (:rewrite fn-bs-imp-outside-of-outside)
              (:rewrite fn-bs-imp-outside-of-subdir-entries)
              (:rewrite fn-bs-imp-stage-state-parts)
              (:rewrite fn-bs-imp-subdirs-state-lookup-frame)
              (:rewrite fn-bs-imp-subdirs-state-parts)
              (:rewrite fn-bs-imp-subdirs-state-view)
              (:rewrite fn-bs-imp-subdirsp-ids-are-keywords)
              (:rewrite fn-bs-imp-view-files-is-complete)
              (:rewrite fn-bs-imp-view-files-through-fence)
              (:rewrite fn-bs-imp-view-files-through-fences)
              (:rewrite fn-bs-imp-view-subdirs-is-complete)
              (:rewrite fn-bs-imp-view-subdirs-through-fence)
              (:rewrite fn-bs-imp-view-subdirs-through-fences)
              (:rewrite fn-bs-imp-view-subdirs-through-files)
              (:rewrite fn-cp-append-nil-left) (:rewrite nth-0-cons) (:rewrite nth-add1)
              (:type-prescription fn-bs-imp-completep)
              (:type-prescription fn-bs-imp-file-entries)
              (:type-prescription fn-bs-imp-files-freshp)
              (:type-prescription fn-bs-imp-filesp)
              (:type-prescription fn-bs-imp-ops-outside)
              (:type-prescription fn-bs-imp-outcomesp)
              (:type-prescription fn-bs-imp-subdir-entries)
              (:type-prescription fn-bs-imp-subdirs-freshp)
              (:type-prescription fn-bs-imp-subdirsp) (:type-prescription member-equal)
              (:type-prescription strip-cdrs) (:type-prescription true-listp-append))
            :use ((:instance fn-bs-imp-stage-ok)
                  (:instance fn-bs-imp-subdirs-ok
                             (s (fn-bs-imp-stage-state bs stage))
                             (outs (nthcdr (len (fn-bs-imp-stage-steps stage)) outs)))
                  (:instance fn-bs-imp-files-ok
                             (s (fn-bs-imp-subdirs-state (fn-bs-imp-stage-state bs stage) subdirs))
                             (outs (nthcdr (len (fn-bs-imp-subdir-steps subdirs))
                                           (nthcdr (len (fn-bs-imp-stage-steps stage)) outs))))
                  (:instance fn-bs-imp-fences-ok
                             (s (fn-bs-imp-files-state
                                 (fn-bs-imp-subdirs-state (fn-bs-imp-stage-state bs stage) subdirs)
                                 files))
                             (outs (nthcdr (len (fn-bs-imp-files-steps files))
                                           (nthcdr (len (fn-bs-imp-subdir-steps subdirs))
                                                   (nthcdr (len (fn-bs-imp-stage-steps stage)) outs)))))
                  (:instance fn-bs-imp-seal-ok
                             (s (fn-bs-imp-fences-state
                                 (fn-bs-imp-files-state
                                  (fn-bs-imp-subdirs-state (fn-bs-imp-stage-state bs stage) subdirs)
                                  files)
                                 subdirs))
                             (outs (nthcdr (len (fn-bs-imp-fence-steps subdirs))
                                           (nthcdr (len (fn-bs-imp-files-steps files))
                                                   (nthcdr (len (fn-bs-imp-subdir-steps subdirs))
                                                           (nthcdr (len (fn-bs-imp-stage-steps stage))
                                                                   outs))))))
                  (:instance fn-bs-imp-subdirs-state-parts
                             (s (fn-bs-imp-stage-state bs stage)) (x :parent)))))))

(local
 (defthm fn-bs-imp-parent-onlyp-of-crash-select
   (implies (fn-bs-imp-parent-onlyp ops)
            (fn-bs-imp-parent-onlyp (fn-bs-crash-select ops ch u)))
   :hints (("Goal" :induct (fn-bs-crash-select ops ch u)
            :in-theory (disable fn-bs-tear-write)))))

(local
 (defthm fn-bs-imp-apply-writes-of-parent-only
   (implies (fn-bs-imp-parent-onlyp ops)
            (equal (fn-bs-apply-writes i ops) i))))

(local
 (defthm fn-bs-imp-apply-entries-of-parent-only
   (implies (and (fn-bs-imp-parent-onlyp ops) (not (equal d :parent)))
            (equal (assoc-equal d (fn-bs-apply-entries dirs ops))
                   (assoc-equal d dirs)))
   :hints (("Goal" :induct (fn-bs-apply-entries dirs ops)))))

(defun fn-bs-imp-tree-subdirsp (dirs subdirs)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp subdirs)
      (and (equal (cdr (assoc-equal (car (car subdirs)) (cdr (assoc-equal :stage dirs))))
                  (cdr (car subdirs)))
           (fn-bs-imp-tree-subdirsp dirs (cdr subdirs)))
    t))

(defun fn-bs-imp-tree-filesp (dirs inodes files ino)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp files)
      (and (equal (cdr (assoc-equal (cadr (car files))
                                    (cdr (assoc-equal (car (car files)) dirs))))
                  ino)
           (equal (cdr (assoc-equal ino inodes)) (cddr (car files)))
           (fn-bs-imp-tree-filesp dirs inodes (cdr files) (+ 1 ino)))
    t))

(local
 (defthm fn-bs-imp-completep-is-tree
   (equal (fn-bs-imp-completep s subdirs files ino)
          (and (fn-bs-imp-tree-subdirsp (fn-bs-dirs s) subdirs)
               (fn-bs-imp-tree-filesp (fn-bs-dirs s) (fn-bs-inodes s) files ino)))
   :hints (("Goal" :in-theory (enable fn-bs-durable-entry fn-bs-durable-content)))))

(local
 (defthm fn-bs-imp-tree-subdirs-of-parent-only
   (implies (fn-bs-imp-parent-onlyp ops)
            (equal (fn-bs-imp-tree-subdirsp (fn-bs-apply-entries dirs ops) subdirs)
                   (fn-bs-imp-tree-subdirsp dirs subdirs)))
   :hints (("Goal" :induct (fn-bs-imp-tree-subdirsp dirs subdirs)
            :in-theory (disable fn-bs-apply-entries)))))

(local
 (defthm fn-bs-imp-tree-files-of-parent-only
   (implies (and (fn-bs-imp-parent-onlyp ops) (fn-bs-imp-files-off-parentp files))
            (equal (fn-bs-imp-tree-filesp (fn-bs-apply-entries dirs ops) inodes files ino)
                   (fn-bs-imp-tree-filesp dirs inodes files ino)))
   :hints (("Goal" :induct (fn-bs-imp-tree-filesp dirs inodes files ino)
            :in-theory (disable fn-bs-apply-entries)))))

; Every pending operation on ROOT's name publishes the staged directory.
(defun fn-bs-imp-root-opsp (ops)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp ops)
      (and (equal (car (car ops)) :set-entry)
           (equal (nth 3 (car ops)) :stage)
           (fn-bs-imp-root-opsp (cdr ops)))
    t))

; Every pending operation on STAGE's name binds it to the staged directory
; or removes it.
(defun fn-bs-imp-stage-opsp (ops)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp ops)
      (and (or (equal (car (car ops)) :del-entry)
               (equal (nth 3 (car ops)) :stage))
           (fn-bs-imp-stage-opsp (cdr ops)))
    t))

;; The publication invariant, in four parts.
(defun fn-bs-imp-root-okp (q root old)
  (declare (xargs :guard t :verify-guards nil))
  (let ((rops (fn-bs-ops-for-name (fn-bs-pending q) :parent root))
        (entry (fn-bs-durable-entry q :parent root)))
    (and (fn-bs-imp-root-opsp rops)
         (or (equal entry old) (and (null old) (equal entry :stage)))
         (or (null rops) (null old)))))

(defun fn-bs-imp-stage-okp (q stage)
  (declare (xargs :guard t :verify-guards nil))
  (let ((sentry (fn-bs-durable-entry q :parent stage)))
    (and (fn-bs-imp-stage-opsp (fn-bs-ops-for-name (fn-bs-pending q) :parent stage))
         (or (null sentry) (equal sentry :stage)))))

(defun fn-bs-imp-tree-okp (q subdirs files ino)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-bs-imp-tree-subdirsp (fn-bs-dirs q) subdirs)
       (fn-bs-imp-tree-filesp (fn-bs-dirs q) (fn-bs-inodes q) files ino)))

(defun fn-bs-imp-pubp (q stage root subdirs files ino old)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-bs-imp-parent-onlyp (fn-bs-pending q))
       (fn-bs-imp-tree-okp q subdirs files ino)
       (fn-bs-imp-root-okp q root old)
       (fn-bs-imp-stage-okp q stage)))

(local
 (defthm fn-bs-imp-root-outcomes
   (implies (and (fn-bs-imp-root-opsp ops) (member-equal x (fn-bs-entry-outcomes ops old)))
            (or (equal x old) (equal x :stage)))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-bs-entry-outcomes)))))

(local
 (defthm fn-bs-imp-stage-outcomes
   (implies (and (fn-bs-imp-stage-opsp ops) (member-equal x (fn-bs-entry-outcomes ops old)))
            (or (equal x old) (equal x :stage) (equal x nil)))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-bs-entry-outcomes)))))

(local
 (defthm fn-bs-imp-ops-for-name-of-parent-only-for-dir
   (implies (fn-bs-imp-parent-onlyp ops)
            (and (equal (fn-bs-ops-for-dir ops :parent) ops)
                 (equal (fn-bs-ops-not-for-dir ops :parent) nil)))))

(local
 (defthm fn-bs-imp-crash-root-entry
   (implies (stringp n)
            (member-equal (cdr (assoc-equal n (cdr (assoc-equal :parent
                                                                (fn-bs-apply-entries
                                                                 dirs (fn-bs-crash-select ops ch u))))))
                          (fn-bs-entry-outcomes (fn-bs-ops-for-name ops :parent n)
                                                (cdr (assoc-equal n (cdr (assoc-equal :parent dirs)))))))
   :hints (("Goal" :in-theory '((:congruence iff-implies-equal-not) (:executable-counterpart not)
              (:rewrite fn-bs-apply-entries-entry-is-entry-after)
              (:rewrite fn-bs-crash-select-entry-is-an-outcome)) :use ((:instance fn-bs-crash-select-entry-is-an-outcome
                                    (old (cdr (assoc-equal n (cdr (assoc-equal :parent dirs)))))
                                    (dir :parent) (name n) (choices ch) (unit u)))))))

(local
 (defthm fn-bs-imp-fence-root-entry
   (implies (stringp n)
            (member-equal (cdr (assoc-equal n (cdr (assoc-equal :parent
                                                                (fn-bs-apply-entries dirs ops)))))
                          (fn-bs-entry-outcomes (fn-bs-ops-for-name ops :parent n)
                                                (cdr (assoc-equal n (cdr (assoc-equal :parent dirs)))))))
   :hints (("Goal" :use ((:instance fn-bs-imp-entry-after-is-an-outcome
                                    (old (cdr (assoc-equal n (cdr (assoc-equal :parent dirs)))))
                                    (d :parent)))))))

(local
 (defthm fn-bs-imp-quiet-entry-lands-unchanged
   (implies (and (stringp n) (not (fn-bs-ops-for-name l :parent n)))
            (and (equal (cdr (assoc-equal n (cdr (assoc-equal :parent
                                                               (fn-bs-apply-entries dirs l)))))
                        (cdr (assoc-equal n (cdr (assoc-equal :parent dirs)))))
                 (equal (cdr (assoc-equal n (cdr (assoc-equal :parent
                                                               (fn-bs-apply-entries
                                                                dirs (fn-bs-crash-select l ch u))))))
                        (cdr (assoc-equal n (cdr (assoc-equal :parent dirs)))))))
   :hints (("Goal" :in-theory '((:definition fn-bs-entry-outcomes) (:definition member-equal)
              (:definition not) (:executable-counterpart consp) (:rewrite car-cons)
              (:rewrite cdr-cons) (:rewrite fn-bs-apply-entries-entry-is-entry-after))
            :use ((:instance fn-bs-imp-fence-root-entry (ops l))
                  (:instance fn-bs-imp-crash-root-entry (ops l)))))))

; Landing any subset of the pending operations keeps the invariant.
(local
 (defthm fn-bs-imp-landed-root-entry
   (implies (and (fn-bs-imp-root-opsp (fn-bs-ops-for-name ops :parent n)) (stringp n))
            (member-equal (cdr (assoc-equal n (cdr (assoc-equal :parent
                                                                (fn-bs-apply-entries
                                                                 dirs (fn-bs-crash-select ops ch u))))))
                          (list (cdr (assoc-equal n (cdr (assoc-equal :parent dirs)))) :stage)))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn-bs-imp-crash-root-entry)
                         (:instance fn-bs-imp-root-outcomes
                                    (ops (fn-bs-ops-for-name ops :parent n))
                                    (old (cdr (assoc-equal n (cdr (assoc-equal :parent dirs)))))
                                    (x (cdr (assoc-equal n (cdr (assoc-equal :parent
                                         (fn-bs-apply-entries dirs (fn-bs-crash-select ops ch u)))))))))
            :in-theory '(member-equal car-cons cdr-cons (:e member-equal))))))

(local
 (defthm fn-bs-imp-landed-stage-entry
   (implies (and (fn-bs-imp-stage-opsp (fn-bs-ops-for-name ops :parent n)) (stringp n))
            (member-equal (cdr (assoc-equal n (cdr (assoc-equal :parent
                                                                (fn-bs-apply-entries
                                                                 dirs (fn-bs-crash-select ops ch u))))))
                          (list (cdr (assoc-equal n (cdr (assoc-equal :parent dirs)))) :stage nil)))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn-bs-imp-crash-root-entry)
                         (:instance fn-bs-imp-stage-outcomes
                                    (ops (fn-bs-ops-for-name ops :parent n))
                                    (old (cdr (assoc-equal n (cdr (assoc-equal :parent dirs)))))
                                    (x (cdr (assoc-equal n (cdr (assoc-equal :parent
                                         (fn-bs-apply-entries dirs (fn-bs-crash-select ops ch u)))))))))
            :in-theory '((:definition member-equal) (:definition not) (:executable-counterpart cons)
              (:executable-counterpart member-equal) (:rewrite car-cons) (:rewrite cdr-cons)
              (:rewrite fn-bs-apply-entries-entry-is-entry-after)
              (:rewrite fn-bs-crash-select-entry-is-an-outcome)
              (:type-prescription fn-bs-imp-stage-opsp))))))

(local
 (defthm fn-bs-imp-root-okp-after-crash-select
   (implies (and (fn-bs-imp-root-okp q root old) (stringp root))
            (fn-bs-imp-root-okp (fn-bs-make u i (fn-bs-apply-entries
                                                 (fn-bs-dirs q)
                                                 (fn-bs-crash-select (fn-bs-pending q) ch cu))
                                            nil nx)
                                root old))
   :hints (("Goal" :in-theory '((:congruence iff-implies-equal-not) (:definition fn-bs-durable-entry)
              (:definition fn-bs-imp-root-okp) (:definition fn-bs-ops-for-name)
              (:definition member-equal) (:definition not) (:executable-counterpart car)
              (:executable-counterpart cdr) (:executable-counterpart cons)
              (:executable-counterpart consp) (:executable-counterpart equal)
              (:executable-counterpart fn-bs-imp-root-opsp) (:executable-counterpart not)
              (:rewrite car-cons) (:rewrite cdr-cons)
              (:rewrite fn-bs-apply-entries-entry-is-entry-after)
              (:rewrite fn-bs-dirs-of-fn-bs-make)
              (:rewrite fn-bs-imp-quiet-entry-lands-unchanged)
              (:rewrite fn-bs-pending-of-fn-bs-make) (:type-prescription fn-bs-imp-root-okp)
              (:type-prescription fn-bs-imp-root-opsp)
              (:type-prescription fn-bs-ops-for-name))
            :cases ((fn-bs-ops-for-name (fn-bs-pending q) :parent root))
            :use ((:instance fn-bs-imp-landed-root-entry (ops (fn-bs-pending q)) (n root)
                             (dirs (fn-bs-dirs q)) (u cu))
                  (:instance fn-bs-imp-quiet-entry-lands-unchanged (l (fn-bs-pending q)) (n root)
                             (dirs (fn-bs-dirs q)) (u cu)))))))

(local
 (defthm fn-bs-imp-stage-okp-after-crash-select
   (implies (and (fn-bs-imp-stage-okp q stage) (stringp stage))
            (fn-bs-imp-stage-okp (fn-bs-make u i (fn-bs-apply-entries
                                                  (fn-bs-dirs q)
                                                  (fn-bs-crash-select (fn-bs-pending q) ch cu))
                                             nil nx)
                                 stage))
   :hints (("Goal" :in-theory '((:definition fn-bs-durable-entry) (:definition fn-bs-imp-stage-okp)
              (:definition fn-bs-ops-for-name) (:definition member-equal) (:definition not)
              (:executable-counterpart car) (:executable-counterpart cdr)
              (:executable-counterpart cons) (:executable-counterpart consp)
              (:executable-counterpart equal) (:executable-counterpart fn-bs-imp-stage-opsp)
              (:executable-counterpart not) (:rewrite car-cons) (:rewrite cdr-cons)
              (:rewrite fn-bs-apply-entries-entry-is-entry-after)
              (:rewrite fn-bs-dirs-of-fn-bs-make) (:rewrite fn-bs-pending-of-fn-bs-make)
              (:type-prescription fn-bs-imp-stage-okp)
              (:type-prescription fn-bs-imp-stage-opsp))
            :use ((:instance fn-bs-imp-landed-stage-entry (ops (fn-bs-pending q)) (n stage)
                             (dirs (fn-bs-dirs q)) (u cu)))))))

(local
 (defthm fn-bs-imp-tree-okp-after-crash-select
   (implies (and (fn-bs-imp-tree-okp q subdirs files ino)
                 (fn-bs-imp-parent-onlyp (fn-bs-pending q))
                 (fn-bs-imp-files-off-parentp files))
            (fn-bs-imp-tree-okp (fn-bs-make u (fn-bs-inodes q)
                                            (fn-bs-apply-entries
                                             (fn-bs-dirs q)
                                             (fn-bs-crash-select (fn-bs-pending q) ch cu))
                                            nil nx)
                                subdirs files ino))))

(local
 (defthm fn-bs-imp-pubp-after-crash-select
   (implies (and (fn-bs-imp-pubp q stage root subdirs files ino old)
                 (fn-bs-imp-files-off-parentp files)
                 (stringp stage) (stringp root))
            (fn-bs-imp-pubp (fn-bs-make u (fn-bs-inodes q)
                                        (fn-bs-apply-entries
                                         (fn-bs-dirs q)
                                         (fn-bs-crash-select (fn-bs-pending q) ch cu))
                                        nil nx)
                            stage root subdirs files ino old))
   :hints (("Goal" :in-theory (disable fn-bs-imp-root-okp fn-bs-imp-stage-okp
                                       fn-bs-imp-tree-okp)))))

(local
 (defthm fn-bs-imp-pubp-after-fence
   (implies (and (fn-bs-imp-pubp q stage root subdirs files ino old)
                 (fn-bs-imp-files-off-parentp files)
                 (stringp stage) (stringp root))
            (fn-bs-imp-pubp (fn-bs-make u (fn-bs-inodes q)
                                        (fn-bs-apply-entries (fn-bs-dirs q) (fn-bs-pending q))
                                        nil nx)
                            stage root subdirs files ino old))
   :hints (("Goal" :in-theory '((:definition fn-bs-durable-entry) (:definition fn-bs-imp-pubp)
              (:definition fn-bs-imp-root-okp) (:definition fn-bs-imp-stage-okp)
              (:definition fn-bs-imp-tree-okp) (:definition fn-bs-ops-for-name)
              (:definition not) (:executable-counterpart consp)
              (:executable-counterpart equal)
              (:executable-counterpart fn-bs-imp-parent-onlyp)
              (:executable-counterpart fn-bs-imp-root-opsp)
              (:executable-counterpart fn-bs-imp-stage-opsp)
              (:rewrite fn-bs-apply-entries-entry-is-entry-after)
              (:rewrite fn-bs-dirs-of-fn-bs-make)
              (:rewrite fn-bs-imp-entry-after-is-an-outcome)
              (:rewrite fn-bs-imp-quiet-entry-lands-unchanged)
              (:rewrite fn-bs-imp-tree-files-of-parent-only)
              (:rewrite fn-bs-imp-tree-subdirs-of-parent-only)
              (:rewrite fn-bs-inodes-of-fn-bs-make) (:rewrite fn-bs-pending-of-fn-bs-make)
              (:type-prescription fn-bs-imp-files-off-parentp)
              (:type-prescription fn-bs-imp-parent-onlyp)
              (:type-prescription fn-bs-imp-pubp) (:type-prescription fn-bs-imp-root-opsp)
              (:type-prescription fn-bs-imp-stage-opsp)
              (:type-prescription fn-bs-imp-tree-filesp)
              (:type-prescription fn-bs-imp-tree-subdirsp))
            :use ((:instance fn-bs-imp-root-outcomes
                             (ops (fn-bs-ops-for-name (fn-bs-pending q) :parent root))
                             (old (fn-bs-durable-entry q :parent root))
                             (x (cdr (assoc-equal root (cdr (assoc-equal :parent
                                  (fn-bs-apply-entries (fn-bs-dirs q) (fn-bs-pending q))))))))
                  (:instance fn-bs-imp-stage-outcomes
                             (ops (fn-bs-ops-for-name (fn-bs-pending q) :parent stage))
                             (old (fn-bs-durable-entry q :parent stage))
                             (x (cdr (assoc-equal stage (cdr (assoc-equal :parent
                                  (fn-bs-apply-entries (fn-bs-dirs q) (fn-bs-pending q))))))))
                  (:instance fn-bs-imp-fence-root-entry (n root) (dirs (fn-bs-dirs q))
                             (ops (fn-bs-pending q)))
                  (:instance fn-bs-imp-fence-root-entry (n stage) (dirs (fn-bs-dirs q))
                             (ops (fn-bs-pending q))))))))

(local
 (defthm fn-bs-imp-fsync-dir-state
   (equal (mv-nth 1 (fn-bs-fsync-dir s d out))
          (if (equal out :ok)
              (fn-bs-fence-dir s d)
            (fn-bs-make (fn-bs-unit s)
                        (fn-bs-apply-writes (fn-bs-inodes s)
                                            (fn-bs-crash-select (fn-bs-ops-for-dir (fn-bs-pending s) d)
                                                                (cdr out) (fn-bs-unit s)))
                        (fn-bs-apply-entries (fn-bs-dirs s)
                                             (fn-bs-crash-select (fn-bs-ops-for-dir (fn-bs-pending s) d)
                                                                 (cdr out) (fn-bs-unit s)))
                        (fn-bs-ops-not-for-dir (fn-bs-pending s) d)
                        (fn-bs-next-ino s))))
   :hints (("Goal" :in-theory '((:definition fn-bs-fsync-dir)
              (:rewrite fn-bs-apply-ops-dirs-are-apply-entries)
              (:rewrite fn-bs-apply-ops-inodes-are-apply-writes))))))

(local
 (defthm fn-bs-imp-fence-dir-state
   (equal (fn-bs-fence-dir s d)
          (fn-bs-make (fn-bs-unit s)
                      (fn-bs-apply-writes (fn-bs-inodes s) (fn-bs-ops-for-dir (fn-bs-pending s) d))
                      (fn-bs-apply-entries (fn-bs-dirs s) (fn-bs-ops-for-dir (fn-bs-pending s) d))
                      (fn-bs-ops-not-for-dir (fn-bs-pending s) d)
                      (fn-bs-next-ino s)))
   :hints (("Goal" :in-theory (enable fn-bs-fence-dir)))))

(local
 (defthm fn-bs-imp-crash-state
   (equal (fn-bs-crash s ch)
          (fn-bs-make (fn-bs-unit s)
                      (fn-bs-apply-writes (fn-bs-inodes s)
                                          (fn-bs-crash-select (fn-bs-pending s) ch (fn-bs-unit s)))
                      (fn-bs-apply-entries (fn-bs-dirs s)
                                           (fn-bs-crash-select (fn-bs-pending s) ch (fn-bs-unit s)))
                      nil
                      (fn-bs-next-ino s)))
   :hints (("Goal" :in-theory '((:definition fn-bs-crash) (:rewrite fn-bs-apply-ops-dirs-are-apply-entries)
              (:rewrite fn-bs-apply-ops-inodes-are-apply-writes))))))

(local
 (defthm fn-bs-imp-op-lists-of-append
   (and (implies (fn-bs-imp-parent-onlyp a)
                 (equal (fn-bs-imp-parent-onlyp (append a b)) (fn-bs-imp-parent-onlyp b)))
        (equal (fn-bs-imp-root-opsp (append a b))
               (and (fn-bs-imp-root-opsp a) (fn-bs-imp-root-opsp b)))
        (equal (fn-bs-imp-stage-opsp (append a b))
               (and (fn-bs-imp-stage-opsp a) (fn-bs-imp-stage-opsp b))))))

(local
 (defthm fn-bs-imp-pubp-after-rename
   (implies (and (fn-bs-imp-pubp q stage root subdirs files ino old)
                 (stringp stage) (stringp root) (not (equal stage root)))
            (fn-bs-imp-pubp (mv-nth 1 (fn-bs-rename-dir-noreplace q :parent stage :parent root out))
                            stage root subdirs files ino old))
   :hints (("Goal" :in-theory '((:congruence iff-implies-equal-implies-1) (:congruence iff-implies-equal-not)
              (:definition fn-bs-dir-idp) (:definition fn-bs-durable-entry)
              (:definition fn-bs-imp-parent-onlyp) (:definition fn-bs-imp-pubp)
              (:definition fn-bs-imp-root-okp) (:definition fn-bs-imp-root-opsp)
              (:definition fn-bs-imp-stage-okp) (:definition fn-bs-imp-stage-opsp)
              (:definition fn-bs-imp-tree-okp) (:definition fn-bs-ops-for-name)
              (:definition fn-bs-rename-dir-noreplace) (:definition keywordp)
              (:definition mv-nth) (:definition not) (:executable-counterpart binary-+)
              (:executable-counterpart cons) (:executable-counterpart consp)
              (:executable-counterpart equal) (:executable-counterpart fn-bs-dir-idp)
              (:executable-counterpart fn-bs-imp-parent-onlyp)
              (:executable-counterpart fn-bs-imp-root-opsp)
              (:executable-counterpart fn-bs-imp-stage-opsp)
              (:executable-counterpart member-equal) (:executable-counterpart not)
              (:executable-counterpart nth) (:executable-counterpart symbol-package-name)
              (:executable-counterpart symbolp) (:executable-counterpart zp)
              (:forward-chaining fn-bs-imp-keyword-is-not-nil) (:rewrite car-cons)
              (:rewrite cdr-cons) (:rewrite fn-bs-dirs-of-fn-bs-make)
              (:rewrite fn-bs-imp-entry-after-is-an-outcome)
              (:rewrite fn-bs-imp-lookup-is-entry-after)
              (:rewrite fn-bs-imp-op-lists-of-append)
              (:rewrite fn-bs-imp-ops-for-name-of-append)
              (:rewrite fn-bs-inodes-of-fn-bs-make) (:rewrite fn-bs-pending-of-fn-bs-make)
              (:rewrite fn-cp-append-nil-left) (:rewrite nth-0-cons) (:rewrite nth-add1)
              (:type-prescription binary-append) (:type-prescription fn-bs-imp-parent-onlyp)
              (:type-prescription fn-bs-imp-pubp) (:type-prescription fn-bs-imp-root-opsp)
              (:type-prescription fn-bs-imp-stage-opsp)
              (:type-prescription fn-bs-imp-tree-filesp)
              (:type-prescription fn-bs-imp-tree-subdirsp)
              (:type-prescription true-listp-append))
            :use ((:instance fn-bs-imp-stage-outcomes
                             (ops (fn-bs-ops-for-name (fn-bs-pending q) :parent stage))
                             (old (fn-bs-durable-entry q :parent stage))
                             (x (fn-bs-entry-after (fn-bs-pending q)
                                                   (fn-bs-durable-entry q :parent stage)
                                                   :parent stage)))
                  (:instance fn-bs-imp-root-outcomes
                             (ops (fn-bs-ops-for-name (fn-bs-pending q) :parent root))
                             (old (fn-bs-durable-entry q :parent root))
                             (x (fn-bs-entry-after (fn-bs-pending q)
                                                   (fn-bs-durable-entry q :parent root)
                                                   :parent root)))
                  (:instance fn-bs-imp-entry-after-is-an-outcome
                             (ops (fn-bs-pending q)) (d :parent) (n stage)
                             (old (fn-bs-durable-entry q :parent stage)))
                  (:instance fn-bs-imp-entry-after-is-an-outcome
                             (ops (fn-bs-pending q)) (d :parent) (n root)
                             (old (fn-bs-durable-entry q :parent root))))))))

; The publication program keeps the invariant at every step, any outcome.
(local
 (defthm fn-bs-imp-pubp-is-parent-only
   (implies (fn-bs-imp-pubp q stage root subdirs files ino old)
            (fn-bs-imp-parent-onlyp (fn-bs-pending q)))
   :rule-classes :forward-chaining))
(local
 (defthm fn-bs-imp-pubp-after-fence-dir
   (implies (and (fn-bs-imp-pubp q stage root subdirs files ino old)
                 (fn-bs-imp-files-off-parentp files)
                 (stringp stage) (stringp root))
            (fn-bs-imp-pubp (mv-nth 1 (fn-bs-fsync-dir q :parent out))
                            stage root subdirs files ino old))
   :hints (("Goal" :do-not-induct t :in-theory (disable fn-bs-imp-pubp)))))

(local
 (defthm fn-bs-imp-pubp-after-fence-parent
   (implies (and (fn-bs-imp-pubp q stage root subdirs files ino old)
                 (fn-bs-imp-files-off-parentp files)
                 (stringp stage) (stringp root))
            (fn-bs-imp-pubp (fn-bs-fence-dir q :parent) stage root subdirs files ino old))
   :hints (("Goal" :do-not-induct t :in-theory (disable fn-bs-imp-pubp)))))

(local
 (defthm fn-bs-imp-pubp-after-crash
   (implies (and (fn-bs-imp-pubp q stage root subdirs files ino old)
                 (fn-bs-imp-files-off-parentp files)
                 (stringp stage) (stringp root))
            (fn-bs-imp-pubp (fn-bs-crash q ch) stage root subdirs files ino old))
   :hints (("Goal" :do-not-induct t :in-theory (disable fn-bs-imp-pubp)))))

(local
 (defthm fn-bs-imp-publication-run-keeps-pubp
   (implies (and (member-equal p (fn-bs-imp-run q ks (fn-bs-imp-publication-program stage root)
                                                outs groups capacity))
                 (fn-bs-imp-pubp q stage root subdirs files ino old)
                 (fn-bs-imp-files-off-parentp files)
                 (stringp stage) (stringp root) (not (equal stage root)))
            (fn-bs-imp-pubp (car p) stage root subdirs files ino old))
   :hints (("Goal" :do-not-induct t
            :in-theory (disable fn-bs-imp-pubp fn-bs-imp-fsync-dir-state
                                fn-bs-imp-fence-dir-state)
            :expand ((:free (b k s0 o0) (fn-bs-imp-run b k s0 o0 groups capacity)))))))

; A crash image of a state in the invariant: ROOT is its old entry, or the
; staged directory with the complete tree.
(local
 (defthm fn-bs-imp-pubp-gives-the-conclusion
   (implies (and (fn-bs-imp-pubp img stage root subdirs files ino old))
            (fn-bs-imp-no-store-or-completep img root subdirs files ino old))
   :hints (("Goal" :in-theory (enable fn-bs-durable-entry)))))

; -----------------------------------------------------------------------------
; Staging never touches ROOT's name: at every step, any outcome, nothing is
; pending on it and its durable entry is the old one.

(defun fn-bs-imp-root-quietp (s root old)
  (declare (xargs :guard t :verify-guards nil))
  (and (null (fn-bs-ops-for-name (fn-bs-pending s) :parent root))
       (equal (fn-bs-durable-entry s :parent root) old)))

(defun fn-bs-imp-step-avoidsp (step root)
  (declare (xargs :guard t :verify-guards nil))
  (and (consp step)
       (case (car step)
         ((:cut :write-all :fsync-file :fsync-dir) t)
         ((:create :mkdir) (not (and (equal (nth 1 step) :parent)
                                     (equal (nth 2 step) root))))
         (otherwise nil))))

(defun fn-bs-imp-steps-avoidp (steps root)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp steps)
      (and (fn-bs-imp-step-avoidsp (car steps) root)
           (fn-bs-imp-steps-avoidp (cdr steps) root))
    t))

(local
 (defthm fn-bs-imp-ops-for-name-of-selections
   (and (equal (fn-bs-ops-for-name (fn-bs-ops-for-ino ops ino) d n) nil)
        (equal (fn-bs-ops-for-name (fn-bs-ops-not-for-ino ops ino) d n)
               (fn-bs-ops-for-name ops d n))
        (equal (fn-bs-ops-for-name (fn-bs-ops-for-dir ops x) d n)
               (if (equal x d) (fn-bs-ops-for-name ops d n) nil))
        (equal (fn-bs-ops-for-name (fn-bs-ops-not-for-dir ops x) d n)
               (if (equal x d) nil (fn-bs-ops-for-name ops d n))))
   :hints (("Goal" :in-theory '((:definition atom) (:definition fn-bs-ops-for-dir)
              (:definition fn-bs-ops-for-ino) (:definition fn-bs-ops-for-name)
              (:definition fn-bs-ops-not-for-dir) (:definition fn-bs-ops-not-for-ino)
              (:definition member-equal) (:definition not) (:executable-counterpart car)
              (:executable-counterpart cdr) (:executable-counterpart consp)
              (:executable-counterpart equal) (:executable-counterpart member-equal)
              (:induction fn-bs-ops-for-dir) (:induction fn-bs-ops-for-ino)
              (:induction fn-bs-ops-for-name) (:induction fn-bs-ops-not-for-dir)
              (:induction fn-bs-ops-not-for-ino) (:rewrite car-cons) (:rewrite cdr-cons)
              (:type-prescription fn-bs-ops-for-dir) (:type-prescription fn-bs-ops-for-ino)
              (:type-prescription fn-bs-ops-not-for-dir)
              (:type-prescription fn-bs-ops-not-for-ino))))))

(local
 (defthm fn-bs-imp-step-keeps-root-quiet
   (implies (and (fn-bs-imp-root-quietp s root old)
                 (fn-bs-imp-step-avoidsp step root)
                 (stringp root))
            (fn-bs-imp-root-quietp (mv-nth 1 (fn-bs-imp-step s ks step out groups capacity))
                                   root old))
   :hints (("Goal" :do-not-induct t
            :in-theory '((:definition assoc-equal) (:definition fn-bs-create)
              (:definition fn-bs-durable-entry) (:definition fn-bs-fence-file)
              (:definition fn-bs-fsync-file) (:definition fn-bs-imp-root-quietp)
              (:definition fn-bs-imp-step) (:definition fn-bs-imp-step-avoidsp)
              (:definition fn-bs-keys-belowp) (:definition fn-bs-mkdir)
              (:definition fn-bs-ops-for-name) (:definition fn-bs-step)
              (:definition fn-bs-take) (:definition fn-bs-write) (:definition member-equal)
              (:definition mv-nth) (:definition nfix) (:definition not) (:definition synp)
              (:executable-counterpart <) (:executable-counterpart binary-+)
              (:executable-counterpart binary-append) (:executable-counterpart car)
              (:executable-counterpart cdr) (:executable-counterpart cons)
              (:executable-counterpart consp) (:executable-counterpart equal)
              (:executable-counterpart integerp) (:executable-counterpart member-equal)
              (:executable-counterpart not) (:executable-counterpart zp) (:rewrite car-cons)
              (:rewrite cdr-cons) (:rewrite fn-bs-apply-entries-keeps-quiet-dir)
              (:rewrite fn-bs-apply-entries-of-ops-for-ino)
              (:rewrite fn-bs-apply-ops-dirs-are-apply-entries)
              (:rewrite fn-bs-apply-ops-inodes-are-apply-writes)
              (:rewrite fn-bs-apply-writes-of-ops-for-dir)
              (:rewrite fn-bs-crash-select-keeps-quiet-dir)
              (:rewrite fn-bs-dirs-of-fn-bs-make) (:rewrite fn-bs-imp-fence-dir-state)
              (:rewrite fn-bs-imp-fsync-dir-state)
              (:rewrite fn-bs-imp-ops-for-name-of-append)
              (:rewrite fn-bs-imp-ops-for-name-of-selections)
              (:rewrite fn-bs-imp-quiet-entry-lands-unchanged)
              (:rewrite fn-bs-keys-belowp-excludes-bound)
              (:rewrite fn-bs-ops-for-dir-of-ops-for-ino)
              (:rewrite fn-bs-pending-of-fn-bs-make) (:rewrite nth-0-cons)
              (:rewrite nth-add1) (:rewrite zp-open) (:type-prescription fn-bs-fsync-dir)
              (:type-prescription fn-bs-imp-root-quietp)
              (:type-prescription fn-bs-ops-for-name) (:type-prescription len))))))

(local
 (defthm fn-bs-imp-run-keeps-root-quiet
   (implies (and (member-equal p (fn-bs-imp-run s ks steps outs groups capacity))
                 (fn-bs-imp-root-quietp s root old)
                 (fn-bs-imp-steps-avoidp steps root)
                 (stringp root))
            (fn-bs-imp-root-quietp (car p) root old))
   :hints (("Goal" :induct (fn-bs-imp-run s ks steps outs groups capacity)
            :in-theory '((:definition fn-bs-imp-run) (:definition fn-bs-imp-step-avoidsp)
              (:definition fn-bs-imp-steps-avoidp) (:definition member-equal)
              (:definition mv-nth) (:definition not) (:executable-counterpart car)
              (:executable-counterpart cdr) (:executable-counterpart consp)
              (:executable-counterpart member-equal) (:executable-counterpart zp)
              (:induction fn-bs-imp-run) (:rewrite car-cons) (:rewrite cdr-cons)
              (:rewrite default-cdr) (:rewrite fn-bs-imp-step-keeps-root-quiet)
              (:type-prescription fn-bs-imp-root-quietp) (:type-prescription fn-bs-imp-run)
              (:type-prescription fn-bs-imp-step)
              (:type-prescription fn-bs-imp-steps-avoidp))))))

(local
 (defthm fn-bs-imp-final-keeps-root-quiet
   (implies (and (fn-bs-imp-root-quietp s root old)
                 (fn-bs-imp-steps-avoidp steps root)
                 (stringp root))
            (fn-bs-imp-root-quietp (car (fn-bs-imp-final s ks steps outs groups capacity))
                                   root old))
   :hints (("Goal" :induct (fn-bs-imp-final s ks steps outs groups capacity)
            :in-theory (disable fn-bs-imp-root-quietp fn-bs-imp-step)))))

(local
 (defthm fn-bs-imp-staging-segments-avoid-root
   (and (implies (and (stringp stage) (not (equal stage root)))
                 (fn-bs-imp-steps-avoidp (fn-bs-imp-stage-steps stage) root))
        (fn-bs-imp-steps-avoidp (fn-bs-imp-subdir-steps subdirs) root)
        (implies (fn-bs-imp-files-off-parentp files)
                 (fn-bs-imp-steps-avoidp (fn-bs-imp-files-steps files) root))
        (fn-bs-imp-steps-avoidp (fn-bs-imp-fence-steps subdirs) root)
        (fn-bs-imp-steps-avoidp (fn-bs-imp-seal-steps) root))
   :hints (("Goal" :in-theory (enable fn-bs-imp-stage-steps fn-bs-imp-seal-steps
                                      fn-bs-imp-file-steps)))))

(local
 (defthm fn-bs-imp-steps-avoidp-of-append
   (equal (fn-bs-imp-steps-avoidp (append a b) root)
          (and (fn-bs-imp-steps-avoidp a root) (fn-bs-imp-steps-avoidp b root)))))

(local
 (defthm fn-bs-imp-quiet-crash-is-old
   (implies (and (fn-bs-imp-root-quietp s root old) (stringp root))
            (equal (fn-bs-durable-entry (fn-bs-crash s ch) :parent root) old))
   :hints (("Goal" :in-theory '((:definition fn-bs-durable-entry) (:definition fn-bs-imp-root-quietp)
              (:rewrite fn-bs-dirs-of-fn-bs-make) (:rewrite fn-bs-imp-crash-state)
              (:rewrite fn-bs-imp-quiet-entry-lands-unchanged))))))

(local
 (defthm fn-bs-imp-quiet-at-start
   (implies (null (fn-bs-pending bs))
            (fn-bs-imp-root-quietp bs root (fn-bs-durable-entry bs :parent root)))
   :hints (("Goal" :in-theory (enable fn-bs-ops-for-name)))))

(local
 (defthm fn-bs-imp-staging-run-is-root-quiet
   (implies (and (fn-bs-imp-inputp bs stage root subdirs files old)
                 (fn-bs-imp-outcomesp outs)
                 (member-equal p (fn-bs-imp-run bs ks (fn-bs-imp-staging-program stage subdirs files)
                                                outs groups capacity)))
            (fn-bs-imp-root-quietp (car p) root old))
   :hints (("Goal" :do-not-induct t
            :in-theory '((:definition binary-append) (:definition fn-bs-imp-entry-opsp)
              (:definition fn-bs-imp-inputp) (:definition fn-bs-imp-outcomep)
              (:definition fn-bs-imp-outcomesp) (:definition fn-bs-imp-staging-program)
              (:definition keyword-listp) (:definition member-equal) (:definition natp)
              (:definition not) (:definition null) (:executable-counterpart equal)
              (:executable-counterpart keywordp) (:rewrite car-cons) (:rewrite cdr-cons)
              (:rewrite fn-bs-imp-entry-opsp-of-subdir-entries)
              (:rewrite fn-bs-imp-fences-ok) (:rewrite fn-bs-imp-filesp-is-shaped)
              (:rewrite fn-bs-imp-filesp-off-parent) (:rewrite fn-bs-imp-outcomesp-parts)
              (:rewrite fn-bs-imp-quiet-at-start) (:rewrite fn-bs-imp-run-keeps-root-quiet)
              (:rewrite fn-bs-imp-run-of-append) (:rewrite fn-bs-imp-stage-state-parts)
              (:rewrite fn-bs-imp-staging-segments-avoid-root)
              (:rewrite fn-bs-imp-subdirs-state-parts)
              (:rewrite fn-bs-imp-subdirsp-ids-are-keywords)
              (:rewrite fn-bs-member-of-append) (:rewrite fn-cp-append-nil-left)
              (:type-prescription fn-bs-imp-fence-steps)
              (:type-prescription fn-bs-imp-files-steps)
              (:type-prescription fn-bs-imp-filesp) (:type-prescription fn-bs-imp-okp)
              (:type-prescription fn-bs-imp-outcomesp)
              (:type-prescription fn-bs-imp-root-quietp)
              (:type-prescription fn-bs-imp-stage-steps)
              (:type-prescription fn-bs-imp-steps-avoidp)
              (:type-prescription fn-bs-imp-subdir-entries)
              (:type-prescription fn-bs-imp-subdir-steps)
              (:type-prescription fn-bs-imp-subdirs-freshp)
              (:type-prescription fn-bs-imp-subdirsp) (:type-prescription member-equal)
              (:type-prescription strip-cdrs))
            :use ((:instance fn-bs-imp-stage-ok)
                  (:instance fn-bs-imp-subdirs-ok
                             (s (fn-bs-imp-stage-state bs stage))
                             (outs (nthcdr (len (fn-bs-imp-stage-steps stage)) outs)))
                  (:instance fn-bs-imp-subdirs-state-parts
                             (s (fn-bs-imp-stage-state bs stage)) (x :parent))
                  (:instance fn-bs-imp-files-ok (s (fn-bs-imp-subdirs-state (fn-bs-imp-stage-state bs stage) subdirs)) (outs (nthcdr (len (fn-bs-imp-subdir-steps subdirs)) (nthcdr (len (fn-bs-imp-stage-steps stage)) outs))))
                  (:instance fn-bs-imp-final-keeps-root-quiet
                             (s bs) (steps (fn-bs-imp-stage-steps stage))
                             (old (fn-bs-durable-entry bs :parent root)))
                  (:instance fn-bs-imp-final-keeps-root-quiet
                             (s (fn-bs-imp-stage-state bs stage)) (steps (fn-bs-imp-subdir-steps subdirs)) (outs (nthcdr (len (fn-bs-imp-stage-steps stage)) outs))
                             (old (fn-bs-durable-entry bs :parent root)))
                  (:instance fn-bs-imp-final-keeps-root-quiet
                             (s (fn-bs-imp-subdirs-state (fn-bs-imp-stage-state bs stage) subdirs)) (steps (fn-bs-imp-files-steps files)) (outs (nthcdr (len (fn-bs-imp-subdir-steps subdirs)) (nthcdr (len (fn-bs-imp-stage-steps stage)) outs)))
                             (old (fn-bs-durable-entry bs :parent root)))
                  (:instance fn-bs-imp-final-keeps-root-quiet
                             (s (fn-bs-imp-files-state (fn-bs-imp-subdirs-state (fn-bs-imp-stage-state bs stage) subdirs) files)) (steps (fn-bs-imp-fence-steps subdirs)) (outs (nthcdr (len (fn-bs-imp-files-steps files)) (nthcdr (len (fn-bs-imp-subdir-steps subdirs)) (nthcdr (len (fn-bs-imp-stage-steps stage)) outs))))
                             (old (fn-bs-durable-entry bs :parent root))))))))

(local
 (defthm fn-bs-imp-staged-state-is-in-the-invariant
   (implies (and (equal (fn-bs-pending sr) (list (list :set-entry :parent stage :stage)))
                 (fn-bs-imp-completep sr subdirs files ino)
                 (equal (fn-bs-durable-entry sr :parent root) old)
                 (equal (fn-bs-durable-entry sr :parent stage) nil)
                 (stringp stage) (stringp root) (not (equal stage root)))
            (fn-bs-imp-pubp sr stage root subdirs files ino old))
   :hints (("Goal" :in-theory (e/d (fn-bs-ops-for-name) (fn-bs-imp-completep))))))

; -----------------------------------------------------------------------------
; Keystone

(defthm fn-bs-imp-program-crash-is-no-store-or-the-complete-store
  (implies (and (fn-bs-imp-inputp bs stage root subdirs files old)
                (fn-bs-imp-outcomesp outs)
                (member-equal p (fn-bs-imp-run bs ks (fn-bs-imp-program stage root subdirs files)
                                               outs groups capacity)))
           (fn-bs-imp-no-store-or-completep (fn-bs-crash (car p) choices)
                                            root subdirs files (fn-bs-next-ino bs) old))
  :hints (("Goal" :do-not-induct t
           :in-theory '((:compound-recognizer natp-compound-recognizer) (:definition fn-bs-imp-inputp)
              (:definition fn-bs-imp-no-store-or-completep) (:definition fn-bs-imp-outcomep)
              (:definition fn-bs-imp-outcomesp) (:definition fn-bs-imp-program)
              (:definition member-equal) (:definition natp) (:definition not)
              (:executable-counterpart cons) (:executable-counterpart equal)
              (:executable-counterpart fn-bs-imp-outcomep) (:executable-counterpart not)
              (:rewrite car-cons) (:rewrite cdr-cons) (:rewrite fn-bs-imp-completep-is-tree)
              (:rewrite fn-bs-imp-filesp-off-parent) (:rewrite fn-bs-imp-outcomesp-parts)
              (:rewrite fn-bs-imp-pubp-after-crash) (:rewrite fn-bs-imp-quiet-crash-is-old)
              (:rewrite fn-bs-imp-run-of-append)
              (:rewrite fn-bs-imp-staged-state-is-in-the-invariant)
              (:rewrite fn-bs-member-of-append)
              (:type-prescription fn-bs-imp-files-off-parentp)
              (:type-prescription fn-bs-imp-filesp)
              (:type-prescription fn-bs-imp-no-store-or-completep)
              (:type-prescription fn-bs-imp-outcomesp) (:type-prescription fn-bs-imp-pubp)
              (:type-prescription fn-bs-imp-root-quietp)
              (:type-prescription fn-bs-imp-staging-program)
              (:type-prescription fn-bs-imp-subdirsp)
              (:type-prescription fn-bs-imp-tree-filesp)
              (:type-prescription fn-bs-imp-tree-subdirsp) (:type-prescription member-equal)
              (:type-prescription strip-cdrs))
           :use ((:instance fn-bs-imp-staging-completes)
                 (:instance fn-bs-imp-staging-run-is-root-quiet)
                 (:instance fn-bs-imp-quiet-crash-is-old (s (car p)) (ch choices))
                 (:instance fn-bs-imp-staged-state-is-in-the-invariant
                            (sr (car (fn-bs-imp-final bs ks (fn-bs-imp-staging-program stage subdirs files)
                                                      outs groups capacity)))
                            (ino (fn-bs-next-ino bs)))
                 (:instance fn-bs-imp-filesp-off-parent
                            (dirs (cons :stage (strip-cdrs subdirs))))
                 (:instance fn-bs-imp-publication-run-keeps-pubp
                            (q (car (fn-bs-imp-final bs ks (fn-bs-imp-staging-program stage subdirs files)
                                                     outs groups capacity)))
                            (ks (cdr (fn-bs-imp-final bs ks (fn-bs-imp-staging-program stage subdirs files)
                                                      outs groups capacity)))
                            (outs (nthcdr (len (fn-bs-imp-staging-program stage subdirs files)) outs))
                            (ino (fn-bs-next-ino bs)))
                 (:instance fn-bs-imp-pubp-after-crash (q (car p)) (ch choices)
                            (ino (fn-bs-next-ino bs)))
                 (:instance fn-bs-imp-pubp-gives-the-conclusion
                            (img (fn-bs-crash (car p) choices)) (ino (fn-bs-next-ino bs)))))))

; Recovery's classification of what it can observe, over every crash image
; of every run from an absent ROOT: an answer that says ROOT holds no store
; (:no-store, :not-published) is given only when ROOT is absent, and an
; answer that says ROOT is present (:store-present, :publication-uncertain)
; is given only when ROOT is the staged directory with the complete tree.
; In particular a staged directory beside a present ROOT is never "no store
; was created".
(defthm fn-bs-imp-classify-by-what-is-known
  (implies (and (fn-bs-imp-inputp bs stage root subdirs files nil)
                (fn-bs-imp-outcomesp outs)
                (member-equal p (fn-bs-imp-run bs ks (fn-bs-imp-program stage root subdirs files)
                                               outs groups capacity)))
           (let* ((img (fn-bs-crash (car p) choices))
                  (verdict (fn-bs-imp-classify (fn-bs-durable-entry img :parent stage)
                                               (fn-bs-durable-entry img :parent root))))
             (and (implies (member-equal verdict '(:no-store :not-published))
                           (null (fn-bs-durable-entry img :parent root)))
                  (implies (member-equal verdict '(:store-present :publication-uncertain))
                           (and (equal (fn-bs-durable-entry img :parent root) :stage)
                                (fn-bs-imp-completep img subdirs files
                                                     (fn-bs-next-ino bs)))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-bs-imp-program-crash-is-no-store-or-the-complete-store
                               fn-bs-imp-completep fn-bs-imp-completep-is-tree
                               fn-bs-imp-inputp fn-bs-crash fn-bs-imp-crash-state)
           :use ((:instance fn-bs-imp-program-crash-is-no-store-or-the-complete-store
                            (old nil))))))

(in-theory (disable fn-bs-imp-program fn-bs-imp-staging-program
                    fn-bs-imp-publication-program fn-bs-imp-inputp
                    fn-bs-imp-no-store-or-completep fn-bs-imp-completep))
