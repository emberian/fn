; K0 for the error outcomes of the authority barriers (lane k0-rest, PKT-086).
;
; fsync(2) of :root or :transactions can fail.  fn-bs-fsync-dir then lands a
; selection of that directory's pending entry operations and discards the
; rest (byte-store.lisp).  A related state outside the recovery window has at
; most one pending entry operation on each authority directory (the
; relation's pending shape, fn-bs-pending-shape-okp: the frontier rename on
; :root, the record link on :transactions), and a selection of one entry
; operation keeps it or drops it.  So the error result is the fence's result
; (fn-bs-k0a-error-is-fence-or-drop) or the state with that directory's
; pending operations dropped, fn-bs-k0a-drop-dir.  The fence's result is
; related by fn-bs-k0s-root-fence-preserves-relation (:root, from any related
; state) and fn-bs-k8-pending-link-fence-preserves-relation (:transactions,
; in :record-attempted with the link pending); the dropped state is related
; by fn-bs-k0a-drop-dir-preserves-relation, because dropping pending entry
; operations changes no durable projection and only removes pending entries
; from the relation's shape.  The keystone:
;   fn-bs-k0a-authority-fsync-error-preserves-relation.
(in-package "ACL2")
(include-book "byte-store-k0-step-root-fence")

(defun fn-bs-k0a-drop-dir (b dir)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bs-make (fn-bs-unit b) (fn-bs-inodes b) (fn-bs-dirs b)
              (fn-bs-ops-not-for-dir (fn-bs-pending b) dir) (fn-bs-next-ino b)))

; The selection of a directory's entry operations.
(defun fn-bs-k0a-entry-opsp (ops)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp ops)
      (and (member-equal (car (car ops)) '(:set-entry :del-entry))
           (fn-bs-k0a-entry-opsp (cdr ops)))
    t))
(defthm fn-bs-k0a-entry-opsp-of-ops-for-dir
  (fn-bs-k0a-entry-opsp (fn-bs-ops-for-dir ops dir))
  :hints (("Goal" :in-theory (enable fn-bs-ops-for-dir))))
(defthm fn-bs-k0a-select-nothing
  (implies (fn-bs-k0a-entry-opsp ops)
           (equal (fn-bs-crash-select ops nil unit) nil))
  :hints (("Goal" :in-theory (enable fn-bs-crash-select))))
(defthm fn-bs-k0a-select-one
  (implies (and (consp ops) (not (consp (cdr ops))) (fn-bs-k0a-entry-opsp ops))
           (member-equal (fn-bs-crash-select ops choices unit) (list (list (car ops)) nil)))
  :rule-classes nil
  :hints (("Goal" :expand ((fn-bs-crash-select ops choices unit) (fn-bs-crash-select (cdr ops) (cdr choices) unit))
                  :in-theory (disable fn-bs-crash-select))))
(local (defthm fn-bs-k0a-one-op-list
  (implies (and (consp ops) (not (consp (cdr ops))) (true-listp ops))
           (equal (cons (car ops) nil) ops))))
(defthm fn-bs-k0a-ops-for-dir-true-listp
  (true-listp (fn-bs-ops-for-dir ops dir))
  :hints (("Goal" :in-theory (enable fn-bs-ops-for-dir))))
(defthm fn-bs-k0a-error-is-fence-or-drop
  (implies (and (not (equal outcome :ok))
                (not (consp (cdr (fn-bs-ops-for-dir (fn-bs-pending b) dir)))))
           (member-equal (mv-nth 1 (fn-bs-fsync-dir b dir outcome))
                         (list (fn-bs-fence-dir b dir) (fn-bs-k0a-drop-dir b dir))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :cases ((consp (fn-bs-ops-for-dir (fn-bs-pending b) dir)))
           :use ((:instance fn-bs-k0a-select-one (ops (fn-bs-ops-for-dir (fn-bs-pending b) dir))
                  (choices (cdr outcome)) (unit (fn-bs-unit b)))
)
           :in-theory (e/d (fn-bs-fsync-dir fn-bs-fence-dir fn-bs-k0a-drop-dir)
                           (fn-bs-crash-select fn-bs-apply-ops fn-bs-ops-for-dir fn-bs-ops-not-for-dir)))
          (and stable-under-simplificationp
               '(:expand ((:free (i d) (fn-bs-apply-ops i d nil)) (:free (i) (fn-bs-apply-writes i nil))
                          (:free (c u) (fn-bs-crash-select nil c u)))))))
(defthm fn-bs-k0a-quiet-fence-is-drop
  (implies (not (fn-bs-ops-for-dir (fn-bs-pending b) dir))
           (equal (fn-bs-fence-dir b dir) (fn-bs-k0a-drop-dir b dir)))
  :rule-classes nil
  :hints (("Goal" :expand ((:free (i d) (fn-bs-apply-ops i d nil)))
           :in-theory (e/d (fn-bs-fence-dir fn-bs-k0a-drop-dir) (fn-bs-apply-ops)))))
(defthm fn-bs-k0a-drop-dir-statep
  (implies (fn-bs-statep b) (fn-bs-statep (fn-bs-k0a-drop-dir b dir)))
  :hints (("Goal" :use ((:instance fn-bs-fsync-dir-preserves-statep (s b) (outcome '(:eio))))
           :expand ((:free (i d) (fn-bs-apply-ops i d nil)))
           :in-theory (e/d (fn-bs-fsync-dir fn-bs-k0a-drop-dir) (fn-bs-fsync-dir-preserves-statep fn-bs-statep
                                                                   fn-bs-apply-ops)))))

; The dropped state: the same durable image, fewer pending entries.
(defthm fn-bs-k0a-ops-for-dir-of-not-for-dir
  (equal (fn-bs-ops-for-dir (fn-bs-ops-not-for-dir ops d) d2)
         (if (equal d d2) nil (fn-bs-ops-for-dir ops d2)))
  :hints (("Goal" :in-theory (enable fn-bs-ops-for-dir fn-bs-ops-not-for-dir))))
(defthm fn-bs-k0a-ops-for-ino-of-not-for-dir
  (equal (fn-bs-ops-for-ino (fn-bs-ops-not-for-dir ops d) ino) (fn-bs-ops-for-ino ops ino))
  :hints (("Goal" :in-theory (enable fn-bs-ops-for-ino fn-bs-ops-not-for-dir))))
(defun fn-bs-k0a-sublistp (xs ys)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp xs) (and (member-equal (car xs) ys) (fn-bs-k0a-sublistp (cdr xs) ys)) t))
(defthm fn-bs-k0a-sublistp-cons-right
  (implies (fn-bs-k0a-sublistp xs ys) (fn-bs-k0a-sublistp xs (cons y ys))))
(defthm fn-bs-k0a-sublistp-refl (fn-bs-k0a-sublistp xs xs))
(defthm fn-bs-k0a-targets-sublist
  (fn-bs-k0a-sublistp (fn-bs-pending-entry-targets (fn-bs-ops-not-for-dir ops d))
                      (fn-bs-pending-entry-targets ops))
  :hints (("Goal" :in-theory (enable fn-bs-pending-entry-targets fn-bs-ops-not-for-dir))))
(defthm fn-bs-k0a-all-fencedp-member
  (implies (and (fn-bs-all-fencedp b ys) (member-equal x ys)) (fn-bs-fencedp b x))
  :hints (("Goal" :in-theory (e/d (fn-bs-all-fencedp) (fn-bs-fencedp)))))
(defthm fn-bs-k0a-all-fencedp-sublist
  (implies (and (fn-bs-all-fencedp b ys) (fn-bs-k0a-sublistp xs ys)) (fn-bs-all-fencedp b xs))
  :hints (("Goal" :in-theory (e/d (fn-bs-all-fencedp) (fn-bs-fencedp)))))
(defthm fn-bs-k0a-knownp-member
  (implies (and (fn-bs-inode-list-knownp b ys) (member-equal x ys)) (consp (assoc-equal x (fn-bs-inodes b))))
  :hints (("Goal" :in-theory (enable fn-bs-inode-list-knownp))))
(defthm fn-bs-k0a-knownp-sublist
  (implies (and (fn-bs-inode-list-knownp b ys) (fn-bs-k0a-sublistp xs ys)) (fn-bs-inode-list-knownp b xs))
  :hints (("Goal" :in-theory (enable fn-bs-inode-list-knownp))))
(defthm fn-bs-k0a-drop-dir-projections
  (let ((b1 (fn-bs-k0a-drop-dir b dir)))
    (and (equal (fn-bs-durable b1) (fn-bs-durable b))
         (equal (fn-bs-durable-entry b1 d n) (fn-bs-durable-entry b d n))
         (equal (fn-bs-durable-content b1 x) (fn-bs-durable-content b x))
         (equal (fn-bs-durable-names b1 d) (fn-bs-durable-names b d))
         (equal (fn-bs-durable-frontier b1) (fn-bs-durable-frontier b))
         (equal (fn-bs-durable-records b1) (fn-bs-durable-records b))
         (equal (fn-bs-fencedp b1 x) (fn-bs-fencedp b x))
         (equal (fn-bs-inodes b1) (fn-bs-inodes b))
         (equal (fn-bs-dirs b1) (fn-bs-dirs b))
         (equal (fn-bs-pending b1) (fn-bs-ops-not-for-dir (fn-bs-pending b) dir))))
  :hints (("Goal" :in-theory (e/d (fn-bs-k0a-drop-dir fn-bs-durable fn-bs-durable-entry fn-bs-durable-content
                                   fn-bs-durable-names fn-bs-durable-frontier fn-bs-durable-records fn-bs-fencedp)
                                  (fn-bs-read-records)))))
(defthm fn-bs-k0a-all-fencedp-of-drop
  (equal (fn-bs-all-fencedp (fn-bs-k0a-drop-dir b dir) xs) (fn-bs-all-fencedp b xs))
  :hints (("Goal" :induct (len xs) :in-theory (e/d (fn-bs-all-fencedp) (fn-bs-k0a-drop-dir fn-bs-fencedp)))))
(defthm fn-bs-k0a-knownp-of-drop
  (equal (fn-bs-inode-list-knownp (fn-bs-k0a-drop-dir b dir) xs) (fn-bs-inode-list-knownp b xs))
  :hints (("Goal" :induct (len xs) :in-theory (e/d (fn-bs-inode-list-knownp) (fn-bs-k0a-drop-dir)))))
(defthm fn-bs-k0a-drop-dir-preserves-relation
  (implies (and (fn-bs-store-relation b k) (not (fn-bs-replay-visiblep k)))
           (fn-bs-store-relation (fn-bs-k0a-drop-dir b dir) k))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-store-relation-unfolds (bs b) (ks k))
                 (:instance fn-bs-store-relation-window-unfolds (bs b) (ks k))
                 (:instance fn-bs-k0a-targets-sublist (ops (fn-bs-pending b)) (d dir)))
           :in-theory (e/d (fn-bs-store-relation fn-bs-authority-fencedp fn-bs-authority-knownp
                            fn-bs-pending-matches-phase fn-bs-pending-shape-okp fn-bs-authority-inode-list
                            fn-bs-k8-record-of-durable-is-durable-content)
                           (fn-bs-durable fn-bs-durable-names fn-bs-statep fn-bs-k0a-drop-dir
                            fn-bs-durable-records fn-bs-durable-frontier fn-bs-durable-entry
                            fn-bs-durable-content fn-bs-record-of fn-bs-k0a-targets-sublist
                            fn-bs-replay-matches-scan fn-sf-crash-imagep fn-sf-statep
                            fn-bs-contiguous-namesp fn-bs-replay-visiblep
                            fn-bs-all-fencedp fn-bs-inode-list-knownp fn-bs-fencedp
                            fn-sf-frontier-new-visiblep fn-sf-record-present-visiblep)))))

; KEYSTONE.  The error outcome of either authority barrier, from a related
; state outside the recovery window (for :transactions with a pending link,
; in :record-attempted, the phase the record barrier runs in).
(defthm fn-bs-k0a-shape-one-op
  (implies (fn-bs-pending-shape-okp b)
           (and (not (consp (cdr (fn-bs-ops-for-dir (fn-bs-pending b) :root))))
                (not (consp (cdr (fn-bs-ops-for-dir (fn-bs-pending b) :transactions))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-bs-pending-shape-okp) (fn-bs-fencedp fn-bs-durable-names)))))
(defthm fn-bs-k0a-authority-fsync-error-preserves-relation
  (implies (and (fn-bs-store-relation b k)
                (not (fn-bs-replay-visiblep k))
                (member-equal dir '(:root :transactions))
                (not (equal outcome :ok))
                (or (equal dir :root)
                    (not (fn-bs-ops-for-dir (fn-bs-pending b) :transactions))
                    (equal (fn-sf-phase k) :record-attempted)))
           (fn-bs-store-relation (mv-nth 1 (fn-bs-fsync-dir b dir outcome)) k))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-k0a-error-is-fence-or-drop fn-bs-k0a-drop-dir-preserves-relation
                 fn-bs-k0a-quiet-fence-is-drop
                 (:instance fn-bs-k0a-shape-one-op)
                 (:instance fn-bs-store-relation-window-unfolds (bs b) (ks k))
                 (:instance fn-bs-pending-matches-phase-unfolds (bs b) (ks k))
                 (:instance fn-bs-k0s-root-fence-preserves-relation (bs b) (ks k))
                 (:instance fn-bs-k8-pending-link-fence-preserves-relation (bs b) (ks k)))
           :in-theory (e/d () (fn-bs-store-relation fn-bs-fsync-dir fn-bs-fence-dir fn-bs-k0a-drop-dir
                               fn-bs-pending-shape-okp fn-bs-pending-matches-phase fn-bs-replay-visiblep
                               fn-sf-crash-imagep fn-bs-ops-for-dir)))))
