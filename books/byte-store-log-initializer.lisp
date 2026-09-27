; fn: the developer initializer of a format-9 store over the byte store
; (lane log-2, 2026-09-27; PKT-COL-2 of lane commit-onto-log's record).
;
; `store ROOT init' and `fn init' build the store in place
; (host/native/io.lisp fnn-initialize).  For a format-9 profile (ACL2's
; fn-store-profile-logp) the host now runs this program instead of
; books/byte-store-initializer.lisp's fn-bsi-current-init-program followed
; by an unmodelled segment: no transactions/ and no allocation-frontier.json
; (a format-9 store reads neither), and the record log's segment
; journal/000001.log created, its extent of zeros written (posix_fallocate
; on Linux: its range reads zeros, A-HOST), fenced, and journal/ fenced, each
; syscall followed by its cut.  The fresh path only, as for format 8: an
; existing directory, lock or segment is the host's retry branch (kept, not
; recreated) and is not this program.
;
; fn-bsi-log-init-program-establishes-the-empty-log: from the empty byte
; store, the run of every step ok ends with journal/ named durably in the
; root, the segment named durably in journal/ with exactly EXTENT zeros
; durable, config.json and config/00000001.cfg durable with their octets,
; and nothing named in the root for a frontier file or transactions/.
; With books/store-init-log-publication.lisp fn-bs-init-log-segment-is-the-
; empty-log, the first open's recovery reads the empty log.
(in-package "ACL2")
(include-book "byte-store-initializer")

(defun fn-bsi-log-segment-steps (extent)
  (declare (xargs :guard t :verify-guards nil))
  (list (list :create :journal "000001.log")
        (list :cut "init-segment-created")
        (list :write-all :journal "000001.log" (fn-bs-zeros extent))
        (list :cut "init-segment-written")
        (list :fsync-file :journal "000001.log")
        (list :cut "init-segment-file-fenced")
        (list :fsync-dir :journal)
        (list :cut "init-journal-segment-fenced")))

(defun fn-bsi-log-init-program (config config-record config-stage record-stage extent)
  (declare (xargs :guard t :verify-guards nil))
  (append
   (list (list :mkdir :parent "store" :root)
         (list :cut "init-root-mkdir")
         (list :fsync-dir :parent)
         (list :cut "init-root-parent-fenced")
         (list :create :root *fn-bsi-lock-name*)
         (list :cut "init-lock-created")
         (list :mkdir :root "staging" :staging)
         (list :cut "init-staging-mkdir")
         (list :fsync-dir :root)
         (list :cut "init-staging-parent-fenced")
         (list :mkdir :root "config" :config)
         (list :cut "init-config-dir-mkdir")
         (list :fsync-dir :root)
         (list :cut "init-config-dir-parent-fenced")
         (list :mkdir :root "journal" :journal)
         (list :cut "init-journal-mkdir")
         (list :fsync-dir :root)
         (list :cut "init-journal-parent-fenced"))
   (fn-bsi-publish-steps "init-config-" config-stage :root *fn-bs-config-name* config)
   (fn-bsi-publish-steps "init-history-" record-stage :config *fn-bsi-config-record-name* config-record)
   (list (list :fsync-dir :config)
         (list :cut "init-config-history-fenced"))
   (fn-bsi-log-segment-steps extent)
   (list (list :fsync-file :root *fn-bs-config-name*)
         (list :cut "init-final-config-file-fenced")
         (list :fsync-file :config *fn-bsi-config-record-name*)
         (list :cut "init-final-config-record-file-fenced")
         (list :fsync-dir :root)
         (list :cut "init-root-fenced")
         (list :fsync-dir :parent)
         (list :cut "init-parent-fenced"))))

(local
 (defun fn-bsil-find-run (term)
   (declare (xargs :mode :program))
   (cond ((atom term) nil)
         ((equal (car term) 'fn-bs-run) term)
         ((equal (car term) 'quote) nil)
         (t (or (fn-bsil-find-run (car term))
                (fn-bsil-find-run (cdr term)))))))
(local
 (defun fn-bsil-unroll-hint (clause stable-under-simplificationp)
   (declare (xargs :mode :program))
   (let ((term (and stable-under-simplificationp (fn-bsil-find-run clause))))
     (and term
          (list :computed-hint-replacement
                '((fn-bsil-unroll-hint clause stable-under-simplificationp))
                :expand (list term))))))
(local
 (defthm fn-bsil-take-of-len
   (implies (true-listp xs) (equal (fn-bs-take (len xs) xs) xs))
   :hints (("Goal" :in-theory (enable fn-bs-take)))))
(local (defthm fn-bsil-octets-are-true-lists
   (implies (fn-cbor-octet-listp xs) (true-listp xs))))
(local (defthm fn-bsil-consp-has-positive-len
   (implies (consp xs) (< 0 (len xs)))))
(local (defthm fn-bsil-nthcdr-of-nil (equal (nthcdr n nil) nil)))
(local (defthm fn-bsil-append-nil
   (implies (true-listp xs) (equal (append xs nil) xs))))
(local (defthm fn-bsil-splice-new-file
   (implies (true-listp octets)
            (equal (fn-bs-splice nil 0 octets) octets))
   :hints (("Goal" :in-theory (enable fn-bs-splice)))))
(local (defthm fn-bsil-zeros-true-listp (true-listp (fn-bs-zeros n))))
(local (defthm fn-bsil-zeros-len (equal (len (fn-bs-zeros n)) (nfix n))))
(local (defthm fn-bsil-take-zeros
   (equal (fn-bs-take n (fn-bs-zeros n)) (fn-bs-zeros n))
   :hints (("Goal" :in-theory (enable fn-bs-take fn-bs-zeros)))))

(defun fn-bsi-log-final (config config-record config-stage record-stage extent)
  (declare (xargs :guard t :verify-guards nil))
  (car (car (last (fn-bs-run *fn-bs-empty-store* (fn-sf-initial-state)
                             (fn-bsi-log-init-program config config-record
                                                      config-stage record-stage extent)
                             nil nil nil)))))

; The staging names need not be names (audit packet G4-5, lane audit-fixes):
; the weakened theorem proves, so (fn-bs-namep config-stage) and
; (fn-bs-namep record-stage) were dropped.
(defthm fn-bsi-log-init-program-establishes-the-empty-log
  (implies (and (fn-cbor-octet-listp config) (consp config)
                (fn-cbor-octet-listp config-record) (consp config-record)
                (posp extent))
           (let* ((s (fn-bsi-log-final config config-record config-stage record-stage extent))
                  (seg (fn-bs-durable-entry s :journal "000001.log")))
             (and (equal (fn-bs-durable-entry s :root "journal") :journal)
                  seg
                  (equal (fn-bs-durable-content s seg) (fn-bs-zeros extent))
                  (equal (fn-bs-durable-content s (fn-bs-durable-entry s :root *fn-bs-config-name*))
                         config)
                  (equal (fn-bs-durable-content
                          s (fn-bs-durable-entry s :config *fn-bsi-config-record-name*))
                         config-record)
                  (null (fn-bs-durable-entry s :root *fn-bs-frontier-name*))
                  (null (fn-bs-durable-entry s :root "transactions")))))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d (fn-bsi-log-final fn-bsi-log-init-program fn-bsi-log-segment-steps
                              fn-bsi-publish-steps fn-bs-step fn-bs-mkdir
                              fn-bs-create fn-bs-write fn-bs-fsync-file
                              fn-bs-fsync-dir fn-bs-link fn-bs-unlink
                              fn-bs-fence-file fn-bs-fence-dir fn-bs-lookup
                              fn-bs-content fn-bs-view fn-bs-durable-entry fn-bs-durable-content
                              fn-bs-apply-ops-inodes-are-apply-writes
                              fn-bs-apply-ops-dirs-are-apply-entries
                              fn-bs-splice)
                           (fn-bs-apply-ops fn-bs-run fn-bs-zeros)))
          (fn-bsil-unroll-hint clause stable-under-simplificationp)))
