; fn: the publish program of the Store checkpoint (P3), one file in the
; store root, `store-checkpoint.fnsc', whose octets are the segment frames of
; books/store-checkpoint-codec.lisp.  Stage, write, fsync, rename, root fsync:
; the shape of fn-bs-profile-program, with five cuts.  The crash keystone
; `fn-bs-scp-program-crash-is-old-or-new': at every cut, a crash leaves the
; checkpoint name bound to the old file with its old octets (or absent, when
; there was none) or to the new inode with exactly the new octets.  Open
; then reads the old checkpoint, the new one, or none, and each is either
; refused (full replay) or the capture of a committed prefix
; (fn-sn-recover-from-checkpoint-equals-full-recover).
;
; K0: the checkpoint is derived, not authority; no step of this program
; touches the kernel's names.  fn-bs-k0-step-inputp (byte-store-k0-step)
; does not yet admit a :rename from :staging to a non-authority :root name
; nor a :root fsync outside the marker rename, so K0 coverage at these cuts is
; an open item, the same one the profile program has.
(in-package "ACL2")
(include-book "byte-store-programs")
(local (include-book "byte-store-invariants"))

(defconst *fn-bs-state-checkpoint-name* "store-checkpoint.fnsc")

(defun fn-bs-scp-program (stage octets)
  (declare (xargs :guard t :verify-guards nil))
  (list (list :create :staging stage)
        (list :cut "state-checkpoint-created")
        (list :write-all :staging stage octets)
        (list :cut "state-checkpoint-written")
        (list :fsync-file :staging stage)
        (list :cut "state-checkpoint-staged-durable")
        (list :rename :staging stage :root *fn-bs-state-checkpoint-name*)
        (list :cut "state-checkpoint-replaced")
        (list :fsync-dir :root)
        (list :cut "state-checkpoint-durable")))
; On an error before the rename the host reports a known failure (exit 1)
; and config.json is untouched; at or after the rename it reports an
; uncertain outcome (exit 3), and the next open reads whichever frame the
; directory holds.  Both are covered by the crash keystone below only
; through their crash images; the error arms themselves are not modelled
; (the run is the successful one, as for P-FRONTIER's K0 lemmas).

; Program discipline D1 to D3 (byte-store-programs, section 2.4), on a
; ground instance.
(defconst *fn-bs-p-state-checkpoint* (fn-bs-scp-program ".stage-state-checkpoint-1" '(1)))
(assert-event (fn-bs-step-listp *fn-bs-p-state-checkpoint*))
(assert-event (fn-bs-links-only-fencedp *fn-bs-p-state-checkpoint*))
(assert-event (fn-bs-never-overwrites-authorityp *fn-bs-p-state-checkpoint*))
(assert-event (fn-bs-fences-authority-dirsp *fn-bs-p-state-checkpoint*))

; The precondition: a store in which no operation is pending (the verb runs
; in a fresh process, after open's own barriers), config.json durably names
; OLD-INO, an inode below the allocation mark, and the stage name is free.
(defun fn-bs-scp-inputp (bs stage old-ino)
  (declare (xargs :guard t :verify-guards nil))
  (and (null (fn-bs-pending bs))
       (stringp stage)
       (natp (fn-bs-next-ino bs))
       (or (null old-ino)
           (and (natp old-ino) (< old-ino (fn-bs-next-ino bs))))
       (equal (fn-bs-durable-entry bs :root *fn-bs-state-checkpoint-name*) old-ino)
       (not (fn-bs-lookup bs :staging stage))))

; What config.json holds in a byte image: its entry and that inode's content.
(defun fn-bs-scp-old-or-newp (img bs old-ino octets)
  (declare (xargs :guard t :verify-guards nil))
  (let ((ino (fn-bs-durable-entry img :root *fn-bs-state-checkpoint-name*)))
    (or (and (equal ino old-ino)
             (or (null old-ino)
                 (equal (fn-bs-durable-content img ino)
                        (fn-bs-durable-content bs old-ino))))
        (and (equal ino (fn-bs-next-ino bs))
             (equal (fn-bs-durable-content img ino) octets)))))

; -----------------------------------------------------------------------------
; Crash images: the entry is the old one or a pending target
; (fn-bs-crash-with-choices-entry-is-old-or-a-pending-target, byte-store-
; invariants), and an inode with no pending write keeps its durable content.

(local (in-theory (enable fn-bs-invariants-vocabulary)))

(local
 (defthm fn-bs-scp-crash-keeps-quiet-inode
   (implies (not (fn-bs-ops-for-ino (fn-bs-pending s) ino))
            (equal (assoc-equal ino (fn-bs-inodes (fn-bs-crash s choices)))
                   (assoc-equal ino (fn-bs-inodes s))))
   :hints (("Goal" :in-theory (enable fn-bs-crash)))))

(local
 (defthm fn-bs-scp-take-of-own-length
   (implies (true-listp x) (equal (fn-bs-take (len x) x) x))))

(local
 (defthm fn-bs-scp-len-of-consp
   (implies (consp x) (not (equal (len x) 0)))))

(local
 (defthm fn-bs-scp-nthcdr-of-nil
   (equal (nthcdr n nil) nil)))

(local
 (defthm fn-bs-scp-append-nil-of-true-list
   (implies (true-listp x) (equal (append x nil) x))))

(local
 (defthm fn-bs-scp-octets-are-a-true-list
   (implies (fn-cbor-octet-listp x) (true-listp x))
   :hints (("Goal" :in-theory (enable fn-cbor-octet-listp)))))

; -----------------------------------------------------------------------------
; Keystone

(defthm fn-bs-scp-program-crash-is-old-or-new
  (implies (and (fn-bs-scp-inputp bs stage old-ino)
                (fn-cbor-octet-listp octets)
                (consp octets)
                (member-equal p (fn-bs-run bs ks (fn-bs-scp-program stage octets)
                                           nil groups capacity)))
           (fn-bs-scp-old-or-newp (fn-bs-crash (car p) choices)
                                      bs old-ino octets))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-crash-with-choices-entry-is-old-or-a-pending-target
                            (s (car p)) (dir :root) (name *fn-bs-state-checkpoint-name*)))
           :expand ((:free (b k s o) (fn-bs-run b k s o groups capacity)))
           :in-theory (e/d (fn-bs-scp-program fn-bs-step
                            fn-bs-create fn-bs-write fn-bs-fsync-file
                            fn-bs-fsync-dir fn-bs-rename fn-bs-fence-file
                            fn-bs-fence-dir fn-bs-lookup fn-bs-view
                            fn-bs-durable-entry fn-bs-durable-content)
                           (fn-bs-crash-with-choices-entry-is-old-or-a-pending-target
                            fn-bs-crash)))))

(in-theory (disable fn-bs-scp-program fn-bs-scp-inputp
                    fn-bs-scp-old-or-newp))
