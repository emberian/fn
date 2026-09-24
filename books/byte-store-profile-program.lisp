; fn: the offline profile upgrade as a byte program (crash model v2, M5).
;
; P-PROFILE is host/native/io.lisp `fnn-upgrade-profile-write', the one
; durable write of `operator CONFIG store upgrade-profile PROFILE': the new
; FNSM profile frame (books/store-profile-upgrade.lisp
; `fn-profile-upgrade-verdict') is staged in :staging under a `.stage-' name
; (so the recovery sweep owns a stage a death leaves there,
; books/store-sweep.lisp), fenced, renamed onto config.json, and the root
; directory fenced.  It is the frontier program's shape (P-FRONTIER in
; books/byte-store-programs.lisp) without kernel observations: the file
; kernel has no profile, so the program changes no fn-sf state.  A :cut
; follows every durable syscall, and each cut is an `fnn-at' site of the
; developer image (tests/campaign/native_cuts.py PROFILE_CUTS).
;
; The keystone: from a quiet store (a fresh process has issued nothing) in
; which config.json names inode OLD-INO, every crash image of every cut of
; the successful run names, at config.json, either OLD-INO with its old
; content or the new inode with exactly the staged octets.  Never a torn
; frame and never an empty file: the name moves to the new inode only by the
; rename, which is issued after the new inode's data fence.
(in-package "ACL2")
(include-book "byte-store-programs")
(include-book "store-budget")
(local (include-book "byte-store-invariants"))

(defun fn-bs-profile-program (stage octets)
  (declare (xargs :guard t :verify-guards nil))
  (list (list :create :staging stage)
        (list :cut "profile-created")
        (list :write-all :staging stage octets)
        (list :cut "profile-written")
        (list :fsync-file :staging stage)
        (list :cut "profile-staged-durable")
        (list :rename :staging stage :root *fn-bs-config-name*)
        (list :cut "profile-replaced")
        (list :fsync-dir :root)
        (list :cut "profile-durable")))
; On an error before the rename the host reports a known failure (exit 1)
; and config.json is untouched; at or after the rename it reports an
; uncertain outcome (exit 3), and the next open reads whichever frame the
; directory holds.  Both are covered by the crash keystone below only
; through their crash images; the error arms themselves are not modelled
; (the run is the successful one, as for P-FRONTIER's K0 lemmas).

; Program discipline D1 to D3 (byte-store-programs, section 2.4), on a
; ground instance.
(defconst *fn-bs-p-profile* (fn-bs-profile-program ".stage-profile-1" '(1)))
(assert-event (fn-bs-step-listp *fn-bs-p-profile*))
(assert-event (fn-bs-links-only-fencedp *fn-bs-p-profile*))
(assert-event (fn-bs-never-overwrites-authorityp *fn-bs-p-profile*))
(assert-event (fn-bs-fences-authority-dirsp *fn-bs-p-profile*))

; The precondition: a store in which no operation is pending (the verb runs
; in a fresh process, after open's own barriers), config.json durably names
; OLD-INO, an inode below the allocation mark, and the stage name is free.
(defun fn-bs-profile-inputp (bs stage old-ino)
  (declare (xargs :guard t :verify-guards nil))
  (and (null (fn-bs-pending bs))
       (stringp stage)
       (natp (fn-bs-next-ino bs))
       (natp old-ino)
       (< old-ino (fn-bs-next-ino bs))
       (equal (fn-bs-durable-entry bs :root *fn-bs-config-name*) old-ino)
       (not (fn-bs-lookup bs :staging stage))))

; What config.json holds in a byte image: its entry and that inode's content.
(defun fn-bs-profile-old-or-newp (img bs old-ino octets)
  (declare (xargs :guard t :verify-guards nil))
  (let ((ino (fn-bs-durable-entry img :root *fn-bs-config-name*)))
    (or (and (equal ino old-ino)
             (equal (fn-bs-durable-content img ino)
                    (fn-bs-durable-content bs old-ino)))
        (and (equal ino (fn-bs-next-ino bs))
             (equal (fn-bs-durable-content img ino) octets)))))

; -----------------------------------------------------------------------------
; Crash images: the entry is the old one or a pending target
; (fn-bs-crash-with-choices-entry-is-old-or-a-pending-target, byte-store-
; invariants), and an inode with no pending write keeps its durable content.

(local (in-theory (enable fn-bs-invariants-vocabulary)))

(local
 (defthm fn-bs-profile-crash-keeps-quiet-inode
   (implies (not (fn-bs-ops-for-ino (fn-bs-pending s) ino))
            (equal (assoc-equal ino (fn-bs-inodes (fn-bs-crash s choices)))
                   (assoc-equal ino (fn-bs-inodes s))))
   :hints (("Goal" :in-theory (enable fn-bs-crash)))))

(local
 (defthm fn-bs-profile-take-of-own-length
   (implies (true-listp x) (equal (fn-bs-take (len x) x) x))))

(local
 (defthm fn-bs-profile-len-of-consp
   (implies (consp x) (not (equal (len x) 0)))))

(local
 (defthm fn-bs-profile-nthcdr-of-nil
   (equal (nthcdr n nil) nil)))

(local
 (defthm fn-bs-profile-append-nil-of-true-list
   (implies (true-listp x) (equal (append x nil) x))))

(local
 (defthm fn-bs-profile-octets-are-a-true-list
   (implies (fn-cbor-octet-listp x) (true-listp x))
   :hints (("Goal" :in-theory (enable fn-cbor-octet-listp)))))

; -----------------------------------------------------------------------------
; Keystone

(defthm fn-bs-profile-program-crash-is-old-or-new
  (implies (and (fn-bs-profile-inputp bs stage old-ino)
                (fn-cbor-octet-listp octets)
                (consp octets)
                (member-equal p (fn-bs-run bs ks (fn-bs-profile-program stage octets)
                                           nil groups capacity)))
           (fn-bs-profile-old-or-newp (fn-bs-crash (car p) choices)
                                      bs old-ino octets))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-crash-with-choices-entry-is-old-or-a-pending-target
                            (s (car p)) (dir :root) (name *fn-bs-config-name*)))
           :expand ((:free (b k s o) (fn-bs-run b k s o groups capacity)))
           :in-theory (e/d (fn-bs-profile-program fn-bs-step
                            fn-bs-create fn-bs-write fn-bs-fsync-file
                            fn-bs-fsync-dir fn-bs-rename fn-bs-fence-file
                            fn-bs-fence-dir fn-bs-lookup fn-bs-view
                            fn-bs-durable-entry fn-bs-durable-content)
                           (fn-bs-crash-with-choices-entry-is-old-or-a-pending-target
                            fn-bs-crash)))))

; The budget the next open hands the owner, at every cut: the budget of the
; old frame or of the new one.  With OCTETS the frame of an :upgrade verdict,
; the second is `fn-sbud-budget' of the named profile
; (books/store-profile-upgrade.lisp fn-profile-upgrade-budget-after-reopen).
(defthm fn-bs-profile-program-crash-budget-is-old-or-new
  (implies (and (fn-bs-profile-inputp bs stage old-ino)
                (fn-cbor-octet-listp octets)
                (consp octets)
                (member-equal p (fn-bs-run bs ks (fn-bs-profile-program stage octets)
                                           nil groups capacity)))
           (let ((img (fn-bs-crash (car p) choices)))
             (member-equal
              (fn-sbud-budget
               (fn-bs-config-decode
                (fn-bs-durable-content
                 img (fn-bs-durable-entry img :root *fn-bs-config-name*)))
               kind)
              (list (fn-sbud-budget
                     (fn-bs-config-decode (fn-bs-durable-content bs old-ino)) kind)
                    (fn-sbud-budget (fn-bs-config-decode octets) kind)))))
  :hints (("Goal" :use fn-bs-profile-program-crash-is-old-or-new
           :in-theory (e/d (fn-bs-profile-old-or-newp)
                           (fn-bs-profile-program-crash-is-old-or-new
                            fn-bs-run fn-bs-profile-program fn-bs-profile-inputp
                            fn-sbud-budget fn-bs-config-decode fn-bs-crash
                            fn-bs-durable-content fn-bs-durable-entry)))))

(in-theory (disable fn-bs-profile-program fn-bs-profile-inputp
                    fn-bs-profile-old-or-newp))
