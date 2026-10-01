; fn: the publish program of the Store checkpoint (P3), one file in the
; store root, `store-checkpoint.fnsc', whose octets are the segment frames of
; books/store-checkpoint-codec.lisp.  Stage, write, fsync, rename, root fsync:
; the shape of the marker program (P-MARKER), with five cuts.  The crash keystone
; `fn-bs-scp-program-crash-is-old-or-new': at every cut, a crash leaves the
; checkpoint name bound to the old file with its old octets (or absent, when
; there was none) or to the new inode with exactly the new octets.  Open
; then reads the old checkpoint, the new one, or none, and each is either
; refused (full replay) or the capture of a committed prefix
; (fn-sn-recover-from-checkpoint-equals-full-recover).
;
; K0: the checkpoint is derived, not authority; no step of this program
; touches the kernel's names.  K0 at its five cuts, and at every step with
; any outcome, is byte-store-k0-step-bridge-root
; (fn-bs-k0-state-checkpoint-cuts-relation-by-step), by the general step
; theorem whose coverage is generic over the root name.
(in-package "ACL2")
(include-book "byte-store-programs")
(local (include-book "byte-store-invariants"))

;; Rules withdrawn at their source that this book's proofs use
;; (lane rule-hygiene, tools/rule_cost.py).
(local (in-theory (enable (:definition fn-bs-apply-op))))

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

; -----------------------------------------------------------------------------
; The write loop's batches (PRF-1223).  The host writes the staged file as a
; sequence of write(2) calls, one per pipeline step (host/native/io.lisp
; fnn-checkpoint-write-steps: one fnn-plan-write-all per fn-ockp-step; the
; developer fault FN_NATIVE_CHECKPOINT_BATCH_FAULT=K:kill kills the process
; after step K), so a death between two batches is a crash point of its own.
; fn-bs-scp-batched-program is that program: fn-bs-scp-program's one
; :write-all as one :write-at per batch at the running offset, each followed
; by the cut "state-checkpoint-batch"; the five outer cuts are the same, and
; a :write-at at offset 0 is the :write-all step
; (fn-bs-scp-write-at-zero-is-write-all-by-definition), so fn-bs-scp-program
; is the one-batch shape.  The crash keystone below is
; fn-bs-scp-program-crash-is-old-or-new at EVERY state, the batch states
; included: until the rename config.json names the old checkpoint (or none),
; whatever the staged inode holds.

(defun fn-bs-scp-chunksp (chunks)
  ; the batches: each a non-empty octet list
  (declare (xargs :guard t :verify-guards nil))
  (if (consp chunks)
      (and (consp (car chunks)) (fn-cbor-octet-listp (car chunks))
           (fn-bs-scp-chunksp (cdr chunks)))
    (null chunks)))

(defun fn-bs-scp-octets (chunks)
  ; the file: the batches in order
  (declare (xargs :guard t :verify-guards nil))
  (if (consp chunks) (append (car chunks) (fn-bs-scp-octets (cdr chunks))) nil))

(defun fn-bs-scp-write-steps (stage chunks offset)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp chunks)
      (list* (list :write-at :staging stage offset (car chunks))
             (list :cut "state-checkpoint-batch")
             (fn-bs-scp-write-steps stage (cdr chunks)
                                    (+ (nfix offset) (len (car chunks)))))
    nil))

(defun fn-bs-scp-batched-program (stage chunks)
  (declare (xargs :guard t :verify-guards nil))
  (append (list (list :create :staging stage)
                (list :cut "state-checkpoint-created"))
          (fn-bs-scp-write-steps stage chunks 0)
          (list (list :cut "state-checkpoint-written")
                (list :fsync-file :staging stage)
                (list :cut "state-checkpoint-staged-durable")
                (list :rename :staging stage :root *fn-bs-state-checkpoint-name*)
                (list :cut "state-checkpoint-replaced")
                (list :fsync-dir :root)
                (list :cut "state-checkpoint-durable"))))

(defthm fn-bs-scp-write-at-zero-is-write-all-by-definition
  (equal (fn-bs-step bs ks (list :write-at dir name 0 octets) outcome groups capacity)
         (fn-bs-step bs ks (list :write-all dir name octets) outcome groups capacity))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn-bs-step car-cons cdr-cons nth
                               (:executable-counterpart zp)
                               (:executable-counterpart binary-+)
                               (:executable-counterpart unary--)))))

; Program discipline D1 to D3 on a three-batch ground instance; the batches
; are the file.
(defconst *fn-bs-p-state-checkpoint-batched*
  (fn-bs-scp-batched-program ".stage-state-checkpoint-1" '((1 2) (3) (4 5 6))))
(assert-event (fn-bs-step-listp *fn-bs-p-state-checkpoint-batched*))
(assert-event (fn-bs-links-only-fencedp *fn-bs-p-state-checkpoint-batched*))
(assert-event (fn-bs-never-overwrites-authorityp *fn-bs-p-state-checkpoint-batched*))
(assert-event (fn-bs-fences-authority-dirsp *fn-bs-p-state-checkpoint-batched*))
(assert-event (and (fn-bs-scp-chunksp '((1 2) (3) (4 5 6)))
                   (equal (fn-bs-scp-octets '((1 2) (3) (4 5 6))) '(1 2 3 4 5 6))))

(in-theory (disable fn-bs-scp-program fn-bs-scp-inputp
                    fn-bs-scp-old-or-newp))
