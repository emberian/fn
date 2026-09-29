; S7 staged snapshot publication (PRF-1071, HST-040).
; The logical file set is the captured frontier's target encoding, NOT an
; enumeration or allocation on the served capture path.  Host streaming
; refinement and target recovery equivalence remain separate obligations.
; Reuse the arbitrary-subdirectory import byte program: every data file is
; fenced before the last SNAPSHOT file, then names are fenced, the complete
; stage is renamed without replacing TARGET, and its parent is fenced.
; A failure once rename may have been issued is uncertain, even if TARGET
; is presently visible.  The generic theorem covers torn name selections.
(in-package "ACL2")
(include-book "store-import-publication")

(defconst *fn-osd-subdirs*
  '(("staging" . :staging) ("config" . :config)
    ("journal" . :journal) ("keys" . :keys)))

(defun fn-osd-subdir-names ()
  (declare (xargs :guard t))
  (strip-cars *fn-osd-subdirs*))

(defun fn-osd-files (data marker)
  (declare (xargs :guard (true-listp data)))
  (append data (list (list* :stage "SNAPSHOT" marker))))

; The host calls this tail only after every captured data file has been
; durably streamed and closed.  The full program below models that prelude.
(defun fn-osd-seal-program (stage target marker)
  (declare (xargs :guard t))
  (list (list :create :stage "SNAPSHOT")
        (list :cut "import-file-created")
        (list :write-all :stage "SNAPSHOT" marker)
        (list :cut "import-file-written")
        (list :fsync-file :stage "SNAPSHOT")
        (list :cut "import-file-durable")
        (list :fsync-dir :staging) (list :cut "import-subdir-durable")
        (list :fsync-dir :config) (list :cut "import-subdir-durable")
        (list :fsync-dir :journal) (list :cut "import-subdir-durable")
        (list :fsync-dir :keys) (list :cut "import-subdir-durable")
        (list :fsync-dir :stage) (list :cut "import-staged-durable")
        (list :cut "import-validated")
        (list :rename-dir-noreplace :parent stage :parent target)
        (list :cut "import-published")
        (list :fsync-dir :parent) (list :cut "import-durable")))

(defun fn-osd-program (stage target data marker)
  (declare (xargs :guard (true-listp data) :verify-guards nil))
  (fn-bs-imp-program stage target *fn-osd-subdirs*
                    (fn-osd-files data marker)))

; Named program boundary, not a new crash keystone.  The authoritative
; keystone is fn-bs-imp-program-crash-is-no-store-or-the-complete-store.
(defthm fn-osd-program-is-the-import-program-by-definition
  (equal (fn-osd-program stage target data marker)
         (fn-bs-imp-program stage target *fn-osd-subdirs*
                            (fn-osd-files data marker))))

; Expose the actual tail to the host; avoid a second host-coded syscall
; sequence.  This equality is a structural boundary, not crash evidence.
(defthm fn-osd-tail-is-the-last-file-and-publication-by-definition
  (equal (fn-osd-program stage target data marker)
         (append (fn-bs-imp-stage-steps stage)
                 (fn-bs-imp-subdir-steps *fn-osd-subdirs*)
                 (fn-bs-imp-files-steps data)
                 (fn-osd-seal-program stage target marker)))
  :hints (("Goal" :in-theory (enable fn-osd-program fn-osd-files
                                     fn-osd-seal-program fn-bs-imp-program
                                     fn-bs-imp-staging-program
                                     fn-bs-imp-files-steps fn-bs-imp-file-steps
                                     fn-bs-imp-fence-steps fn-bs-imp-seal-steps
                                     fn-bs-imp-publication-program))))
