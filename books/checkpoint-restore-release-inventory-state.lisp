; Authenticated selected-checkpoint source records, not physical ownership.
; Only the decoded inventory factory populates tagged rows. The canonical
; release-evidence table alone owns descriptor/J/self claims after projection.
(in-package "ACL2")
(include-book "release-inventory-format")
(include-book "columns")
(fn2-book-layer :b)
(defcolumns fn2-checkpoint-restore-release-inventory
 ((phase (:enum fn2-checkpoint-restore-release-inventory-phase
    (:idle :captured :pages :complete :installing :installed :uncertain :applying :applied)))
  (candidate :u32) (generation :u60) (checkpoint :u60)
  (cut-commit :u60) (cut-event :u60) (history :u60) (incarnation :u60)
  (owner-kind :u8) (owner-slot :u32) (owner-gen :u60)
  (slot :u32) (gen :u60) (checker-row :u32) (field-base :u32)
  (root-unit :u60) (root-epoch :u60) (root-allocation :u60)
  (unit :u60) (epoch :u60) (allocation :u60)
  (total :u60) (consumed :u60) (materialized :u60)
  (head :u32) (tail :u32) (cursor :u32) (settled :u60))
 :extra-fields
 ((fn2-checkpoint-restore-release-inventory-identities :type (array (unsigned-byte 8) (96)) :initially 0
   :why "Private descriptor, root4 and inventory-root hashes copied from actual authenticated source; no caller hash or scratch alias.")))
(defcolumns fn2-checkpoint-restore-release-entries
 ((generation :u60) (target-generation :u60) (next :u32)
  (journal-history :u60) (journal-incarnation :u60)
  (journal-extent :u32) (journal-writer-epoch :u60) (journal-allocation :u60)
  (commit :u60) (event :u60)
  (extent :u32) (writer-epoch :u60) (allocation :u60) (retirement-commit :u60)
  (checkpoint :u60) (cut-commit :u60) (cut-event :u60) (history :u60) (incarnation :u60)
  (installation-commit :u60) (installation-event :u60)
  (installation-history :u60) (installation-incarnation :u60)
  (installation-extent :u32) (installation-writer-epoch :u60) (installation-allocation :u60)
  (descriptor-storage-domain :u60) (descriptor-physical-unit :u60)
  (descriptor-writer-epoch :u60) (descriptor-allocation :u60)
  (descriptor-page-kind :u60) (descriptor-encoded-length :u60))
 :init-name fn2-checkpoint-restore-release-entries-columns-init
 :extra-fields
 ((fn2-checkpoint-restore-release-entries-hashes :type (array (unsigned-byte 8) (0)) :initially 0 :resizable t
   :why "One authenticated descriptor digest per original journal extent; source bytes, not caller digest or ownership ledger.")))
(defun fn2-checkpoint-restore-release-entries-init (rows fn2-checkpoint-restore-release-entries)
 (declare (xargs :stobjs fn2-checkpoint-restore-release-entries :verify-guards nil
  :guard (and (unsigned-byte-p 32 rows) (unsigned-byte-p 32 (* 32 rows))
   (fn2-checkpoint-restore-release-entriesp fn2-checkpoint-restore-release-entries))))
 (let* ((fn2-checkpoint-restore-release-entries (fn2-checkpoint-restore-release-entries-columns-init rows fn2-checkpoint-restore-release-entries))
        (fn2-checkpoint-restore-release-entries (resize-fn2-checkpoint-restore-release-entries-hashes (* 32 rows) fn2-checkpoint-restore-release-entries)))
  fn2-checkpoint-restore-release-entries))
(defthm fn2-checkpoint-restore-release-entries-init-type
 (implies (and (fn2-checkpoint-restore-release-entriesp fn2-checkpoint-restore-release-entries)
               (unsigned-byte-p 32 rows) (unsigned-byte-p 32 (* 32 rows)))
  (fn2-checkpoint-restore-release-entriesp (fn2-checkpoint-restore-release-entries-init rows fn2-checkpoint-restore-release-entries))))
(defthm fn2-checkpoint-restore-release-entries-init-wfp
 (implies (and (fn2-checkpoint-restore-release-entriesp fn2-checkpoint-restore-release-entries)
               (unsigned-byte-p 32 rows) (unsigned-byte-p 32 (* 32 rows)))
  (fn2-checkpoint-restore-release-entries-wfp (fn2-checkpoint-restore-release-entries-init rows fn2-checkpoint-restore-release-entries))))
(defthm fn2-checkpoint-restore-release-entries-init-rows
 (implies (and (fn2-checkpoint-restore-release-entriesp fn2-checkpoint-restore-release-entries)
               (unsigned-byte-p 32 rows) (unsigned-byte-p 32 (* 32 rows)))
  (equal (fn2-checkpoint-restore-release-entries-rows (fn2-checkpoint-restore-release-entries-init rows fn2-checkpoint-restore-release-entries)) rows)))
(defthm fn2-checkpoint-restore-release-entries-init-hashes
 (implies (and (fn2-checkpoint-restore-release-entriesp fn2-checkpoint-restore-release-entries)
               (unsigned-byte-p 32 rows) (unsigned-byte-p 32 (* 32 rows)))
  (equal (fn2-checkpoint-restore-release-entries-hashes-length (fn2-checkpoint-restore-release-entries-init rows fn2-checkpoint-restore-release-entries)) (* 32 rows))))
