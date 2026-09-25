;; fn: K0 at the committed-history marker's cuts (P10, lane p10-marker-model).
;;
;; fn-bs-marker-program (books/byte-store-marker-program.lisp) runs between
;; the record program's end and fn-bs-finish-program, in the kernel's
;; completion window.  Under byte-store-k0's hypotheses (an arbitrary related
;; state outside the recovery window) and a quiet root directory:
;;   marker-created, -written, -staged-durable  the pair is related;
;;   marker-replaced   the pair holds one pending root entry the relation's
;;       shape does not name (the marker is not an authority file), so the
;;       claim is on its two resolutions: with the rename's root entry
;;       dropped the state is related, with it landed it is the
;;       marker-durable state, and every crash image of the pair is a crash
;;       image of one of the two;
;;   marker-durable    the pair is related.
;; The marker itself, at every cut and in every crash image, is the history
;; step books/store-history-marker.lisp models (absent or old before the
;; rename, old or new at it, new after the root barrier; never torn), and the
;; open verdict stays admitted: books/byte-store-marker-program.lisp
;; fn-bs-marker-crash-is-a-history-step and
;; fn-bs-marker-crash-open-stays-admitted (by fn-hm-run-keeps-every-open-admitted).
;;
;; marker-replaced is closed by fn-bs-k0-marker-replaced-cut-relation: both
;; resolutions are related to the cut's kernel, and every crash image of the
;; pending-rename state is a crash image of one of them
;; (fn-bs-k0m-marker-rename-crash-is-a-resolution-crash, from the commutation
;; fn-bs-k0m-crash-of-pending-marker-rename).
;;
;; OPEN, named and not claimed: the error arms (every OS error in
;; fnn-mark-committed is uncertain, and the state is the cut pair's).
(in-package "ACL2")
(include-book "byte-store-k0-staging")
(include-book "byte-store-marker-program")

; A fresh stage inode's content is not authority: changing it keeps the relation
; (the stage's data fence, marker-staged-durable).
(encapsulate ()
(local (defthm l-assoc-value-in-strip-cdrs
  (implies (cdr (assoc-equal name al))
           (member-equal (cdr (assoc-equal name al)) (strip-cdrs al)))))
(defthm fn-bs-k0m-content-txn-agreement
  (implies (and (natp x) (not (member-equal x (strip-cdrs (cdr (assoc-equal :transactions dirs))))))
           (fn-bs-txn-prefix-agreesp (fn-bs-make u (fn-bs-put-assoc x c inodes) dirs nil m)
                                     (fn-bs-make u inodes dirs nil m2) i count))
  :rule-classes nil
  :hints (("Goal" :induct (fn-bs-txn-prefix-agreesp (fn-bs-make u (fn-bs-put-assoc x c inodes) dirs nil m)
                                                    (fn-bs-make u inodes dirs nil m2) i count)
           :in-theory (e/d (fn-bs-txn-prefix-agreesp fn-bs-lookup fn-bs-content fn-bs-view fn-bs-apply-ops
                            fn-bs-invariants-vocabulary)
                           ()))
          ("Subgoal *1/3" :use ((:instance l-assoc-value-in-strip-cdrs
                                 (name (fn-bs-txn-name i)) (al (cdr (assoc-equal :transactions dirs))))))))
)
(defun fn-bs-k0m-with-content (b x c)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bs-make (fn-bs-unit b) (fn-bs-put-assoc x c (fn-bs-inodes b)) (fn-bs-dirs b)
              (fn-bs-pending b) (fn-bs-next-ino b)))
(local (defthm fn-bs-k0m-assoc-of-put-assoc-same
  (implies x (equal (cdr (assoc-equal x (fn-bs-put-assoc x c al))) c))
  :hints (("Goal" :in-theory (enable fn-bs-put-assoc)))))
(defthm fn-bs-k0m-with-content-fencedp
  (equal (fn-bs-fencedp (fn-bs-k0m-with-content b x c) y) (fn-bs-fencedp b y))
  :hints (("Goal" :in-theory (enable fn-bs-fencedp))))
(defthm fn-bs-k0m-with-content-all-fencedp
  (equal (fn-bs-all-fencedp (fn-bs-k0m-with-content b x c) ys) (fn-bs-all-fencedp b ys))
  :hints (("Goal" :induct (len ys) :in-theory (e/d (fn-bs-all-fencedp) (fn-bs-k0m-with-content fn-bs-fencedp)))))
(defthm fn-bs-k0m-with-content-projections
  (let ((b1 (fn-bs-k0m-with-content b x c)))
    (implies (natp x) (and (equal (fn-bs-dirs b1) (fn-bs-dirs b))
         (equal (fn-bs-pending b1) (fn-bs-pending b))
         (equal (fn-bs-unit b1) (fn-bs-unit b))
         (equal (fn-bs-next-ino b1) (fn-bs-next-ino b))
         (equal (fn-bs-durable-entry b1 dir name) (fn-bs-durable-entry b dir name))
         (equal (fn-bs-durable-names b1 dir) (fn-bs-durable-names b dir))
         (equal (fn-bs-durable-content b1 y)
                (if (equal y x) c (fn-bs-durable-content b y)))
         (equal (fn-bs-authority-inode-list b1) (fn-bs-authority-inode-list b)))))
  :hints (("Goal" :in-theory (enable fn-bs-durable-entry fn-bs-durable-names fn-bs-durable-content
                                     fn-bs-authority-inode-list
                                     fn-bs-invariants-vocabulary))))
(local (defthm fn-bs-k0m-assoc-put-assoc-keeps-consp
  (implies (consp (assoc-equal y al)) (consp (assoc-equal y (fn-bs-put-assoc x c al))))
  :hints (("Goal" :in-theory (enable fn-bs-put-assoc)))))
(defthm fn-bs-k0m-with-content-knownp
  (implies (fn-bs-inode-list-knownp b ys)
           (fn-bs-inode-list-knownp (fn-bs-k0m-with-content b x c) ys))
  :hints (("Goal" :induct (len ys)
           :in-theory (enable fn-bs-inode-list-knownp))))
(defthm fn-bs-k0m-with-content-durable-records
  (implies (and (fn-bs-statep b) (natp x)
                (not (member-equal x (fn-bs-authority-inode-list b))))
           (equal (fn-bs-durable-records (fn-bs-k0m-with-content b x c))
                  (fn-bs-durable-records b)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-k0m-content-txn-agreement
                  (u (fn-bs-unit b)) (inodes (fn-bs-inodes b))
                  (dirs (fn-bs-dirs b)) (m (fn-bs-next-ino b)) (m2 (fn-bs-next-ino b)) (i 0)
                  (count (len (fn-bs-durable-names b :transactions))))
                 (:instance fn-bs-read-records-under-agreement
                  (a (fn-bs-make (fn-bs-unit b) (fn-bs-put-assoc x c (fn-bs-inodes b))
                                 (fn-bs-dirs b) nil (fn-bs-next-ino b)))
                  (b (fn-bs-make (fn-bs-unit b) (fn-bs-inodes b) (fn-bs-dirs b) nil (fn-bs-next-ino b)))
                  (n 0) (count (len (fn-bs-durable-names b :transactions)))))
           :in-theory (e/d (fn-bs-durable-records fn-bs-durable fn-bs-authority-inode-list fn-bs-member-of-append fn-bs-durable-names)
                           (fn-bs-read-records fn-bs-txn-prefix-agreesp
                            fn-bs-read-records-under-agreement fn-bs-statep)))))
(defthm fn-bs-k0m-first-dir-op-is-entry-target
  (implies (and (member-equal dir '(:root :transactions))
                (consp (fn-bs-ops-for-dir p dir))
                (equal (car (car (fn-bs-ops-for-dir p dir))) :set-entry))
           (member-equal (nth 3 (car (fn-bs-ops-for-dir p dir)))
                         (fn-bs-pending-entry-targets p)))
  :rule-classes nil
  :hints (("Goal" :induct (fn-bs-ops-for-dir p dir)
           :in-theory (enable fn-bs-ops-for-dir fn-bs-pending-entry-targets))))
(defthm fn-bs-k0m-with-content-preserves-relation
  (implies (and (fn-bs-store-relation b k)
                (not (fn-bs-replay-visiblep k))
                (natp x)
                (not (member-equal x (fn-bs-authority-inode-list b)))
                (fn-bs-statep (fn-bs-k0m-with-content b x c)))
           (fn-bs-store-relation (fn-bs-k0m-with-content b x c) k))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-store-relation-unfolds (bs b) (ks k))
                 (:instance fn-bs-store-relation-window-unfolds (bs b) (ks k))
                 (:instance fn-bs-k0m-with-content-knownp (ys (fn-bs-authority-inode-list b)) (x x) (c c))
                 (:instance fn-bs-k0m-first-dir-op-is-entry-target (p (fn-bs-pending b)) (dir :root))
                 (:instance fn-bs-k0m-first-dir-op-is-entry-target (p (fn-bs-pending b)) (dir :transactions)))
           :in-theory (e/d (fn-bs-store-relation fn-bs-authority-fencedp fn-bs-authority-knownp
                            fn-bs-pending-matches-phase fn-bs-pending-shape-okp
                            fn-bs-k8-record-of-durable-is-durable-content
                            fn-bs-durable-frontier fn-bs-member-of-append fn-bs-authority-inode-list)
                           (fn-bs-durable fn-bs-durable-names fn-bs-statep fn-bs-k0m-with-content
                            fn-bs-durable-records fn-bs-durable-entry fn-bs-k0m-with-content-knownp
                            fn-bs-durable-content fn-bs-record-of
                            fn-bs-replay-matches-scan fn-sf-crash-imagep fn-sf-statep
                            fn-bs-contiguous-namesp fn-bs-replay-visiblep
                            fn-bs-all-fencedp fn-bs-inode-list-knownp fn-bs-fencedp
                            fn-sf-frontier-new-visiblep fn-sf-record-present-visiblep)))))

; A root entry under a name that is neither config.json nor the frontier is
; not authority either: adding it keeps the relation (the root barrier,
; marker-durable).
(defun fn-bs-k0m-with-root-entry (b name ino)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bs-make (fn-bs-unit b) (fn-bs-inodes b)
              (fn-bs-put-assoc :root (fn-bs-put-assoc name ino (cdr (assoc-equal :root (fn-bs-dirs b))))
                               (fn-bs-dirs b))
              (fn-bs-pending b) (fn-bs-next-ino b)))
(local (defthm fn-bs-k0m-assoc-put-assoc-other
  (implies (not (equal k1 k2))
           (equal (assoc-equal k1 (fn-bs-put-assoc k2 v al)) (assoc-equal k1 al)))
  :hints (("Goal" :in-theory (enable fn-bs-put-assoc)))))
(defthm fn-bs-k0m-with-root-entry-projections
  (let ((b1 (fn-bs-k0m-with-root-entry b name ino)))
    (and (equal (fn-bs-inodes b1) (fn-bs-inodes b))
         (equal (fn-bs-pending b1) (fn-bs-pending b))
         (equal (fn-bs-unit b1) (fn-bs-unit b))
         (equal (fn-bs-next-ino b1) (fn-bs-next-ino b))
         (equal (assoc-equal :transactions (fn-bs-dirs b1)) (assoc-equal :transactions (fn-bs-dirs b)))
         (equal (fn-bs-durable-names b1 :transactions) (fn-bs-durable-names b :transactions))
         (equal (fn-bs-durable-content b1 y) (fn-bs-durable-content b y))
         (implies (not (equal n2 name))
                  (equal (fn-bs-durable-entry b1 :root n2) (fn-bs-durable-entry b :root n2)))
         (implies (and (not (equal name *fn-bs-scan-config-name*))
                       (not (equal name *fn-bs-scan-frontier-name*)))
                  (and (equal (fn-bs-authority-inode-list b1) (fn-bs-authority-inode-list b))
                       (equal (fn-bs-durable-frontier b1) (fn-bs-durable-frontier b))))
         (equal (fn-bs-fencedp b1 y) (fn-bs-fencedp b y))))
  :hints (("Goal" :in-theory (enable fn-bs-durable-entry fn-bs-durable-names fn-bs-durable-content
                                     fn-bs-authority-inode-list fn-bs-durable-frontier fn-bs-fencedp))))
(defthm fn-bs-k0m-with-root-entry-all-fencedp
  (equal (fn-bs-all-fencedp (fn-bs-k0m-with-root-entry b name ino) ys) (fn-bs-all-fencedp b ys))
  :hints (("Goal" :induct (len ys) :in-theory (e/d (fn-bs-all-fencedp) (fn-bs-k0m-with-root-entry)))))
(defthm fn-bs-k0m-with-root-entry-knownp
  (equal (fn-bs-inode-list-knownp (fn-bs-k0m-with-root-entry b name ino) ys) (fn-bs-inode-list-knownp b ys))
  :hints (("Goal" :induct (len ys) :in-theory (enable fn-bs-inode-list-knownp))))
(defthm fn-bs-k0m-with-root-entry-durable-records
  (equal (fn-bs-durable-records (fn-bs-k0m-with-root-entry b name ino))
         (fn-bs-durable-records b))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-k0m-with-root-entry-projections)
                 (:instance fn-bs-k0-same-transaction-dir-agreement
                  (u (fn-bs-unit b)) (i (fn-bs-inodes b))
                  (d1 (fn-bs-dirs (fn-bs-k0m-with-root-entry b name ino))) (d2 (fn-bs-dirs b))
                  (m (fn-bs-next-ino b)) (m2 (fn-bs-next-ino b))
                  (n 0) (count (len (fn-bs-durable-names b :transactions))))
                 (:instance fn-bs-read-records-under-agreement
                  (a (fn-bs-durable (fn-bs-k0m-with-root-entry b name ino)))
                  (b (fn-bs-make (fn-bs-unit b) (fn-bs-inodes b) (fn-bs-dirs b) nil (fn-bs-next-ino b)))
                  (n 0) (count (len (fn-bs-durable-names b :transactions)))))
           :in-theory (e/d (fn-bs-durable-records fn-bs-durable)
                           (fn-bs-read-records fn-bs-txn-prefix-agreesp fn-bs-durable-names
                            fn-bs-read-records-under-agreement fn-bs-k0m-with-root-entry
                            fn-bs-k0m-with-root-entry-projections)))))
(defthm fn-bs-k0m-with-root-entry-preserves-relation
  (implies (and (fn-bs-store-relation b k)
                (not (fn-bs-replay-visiblep k))
                (not (equal name *fn-bs-scan-config-name*))
                (not (equal name *fn-bs-scan-frontier-name*))
                (fn-bs-statep (fn-bs-k0m-with-root-entry b name ino)))
           (fn-bs-store-relation (fn-bs-k0m-with-root-entry b name ino) k))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-k0m-with-root-entry-projections (n2 *fn-bs-scan-config-name*))
                 (:instance fn-bs-k0m-with-root-entry-projections (n2 *fn-bs-scan-frontier-name*)
                  (y (fn-bs-durable-entry b :root *fn-bs-scan-config-name*)))
                 (:instance fn-bs-store-relation-unfolds (bs b) (ks k))
                 (:instance fn-bs-store-relation-window-unfolds (bs b) (ks k)))
           :in-theory (e/d (fn-bs-store-relation fn-bs-authority-fencedp fn-bs-authority-knownp
                            fn-bs-pending-matches-phase fn-bs-pending-shape-okp
                            fn-bs-k8-record-of-durable-is-durable-content)
                           (fn-bs-durable fn-bs-durable-names fn-bs-statep fn-bs-k0m-with-root-entry
                            fn-bs-durable-records fn-bs-durable-frontier fn-bs-durable-entry
                            fn-bs-durable-content fn-bs-authority-inode-list fn-bs-record-of
                            fn-bs-replay-matches-scan fn-sf-crash-imagep fn-sf-statep
                            fn-bs-contiguous-namesp fn-bs-replay-visiblep
                            fn-bs-all-fencedp fn-bs-inode-list-knownp fn-bs-fencedp
                            fn-sf-frontier-new-visiblep fn-sf-record-present-visiblep)))))

; The run's states, from the syscalls, and the two resolutions of the
; pending rename at marker-replaced.
(defthm fn-bs-k0m-completing-window-facts
  (implies (and (fn-bs-store-relation bs ks) (fn-bs-finish-inputp ks sequence txid))
           (and (not (fn-bs-replay-visiblep ks))
                (not (fn-bs-ops-for-dir (fn-bs-pending bs) :root))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-bs-store-relation-window-unfolds))
           :in-theory (e/d (fn-bs-replay-visiblep fn-bs-finish-inputp fn-bs-pending-matches-phase
                            fn-sf-frontier-new-visiblep)
                           (fn-bs-store-relation fn-bs-pending-shape-okp fn-sf-crash-imagep)))))
(local (defthm fn-bs-k0m-statep-fresh
  (implies (fn-bs-statep bs)
           (and (true-listp (fn-bs-pending bs))
                (natp (fn-bs-next-ino bs))
                (not (fn-bs-ops-for-ino (fn-bs-pending bs) (fn-bs-next-ino bs)))))
  :hints (("Goal" :in-theory (enable fn-bs-statep)
           :use ((:instance fn-bs-marker-fresh-ino-has-no-writes (ops (fn-bs-pending bs))
                  (inodes (fn-bs-inodes bs)) (n (fn-bs-next-ino bs))))))))
(local (defthm fn-bs-k0m-not-for-ino-id
  (implies (not (fn-bs-ops-for-ino ops n)) (equal (fn-bs-ops-not-for-ino ops n) (true-list-fix ops)))
  :hints (("Goal" :in-theory (enable fn-bs-ops-for-ino fn-bs-ops-not-for-ino)))))
(local (defthm fn-bs-k0m-not-for-ino-app
  (equal (fn-bs-ops-not-for-ino (append a b) n) (append (fn-bs-ops-not-for-ino a n) (fn-bs-ops-not-for-ino b n)))
  :hints (("Goal" :in-theory (enable fn-bs-ops-not-for-ino)))))
(local (defthm fn-bs-k0m-nthcdr-nil (equal (nthcdr n nil) nil)))
(local (defthm fn-bs-k0m-app-nil (implies (true-listp x) (equal (append x nil) x))))
(local (defthm fn-bs-k0m-take-own (implies (true-listp x) (equal (fn-bs-take (len x) x) x))))
(local (defthm fn-bs-k0m-len-consp (implies (consp x) (not (equal (len x) 0)))))
(local (defthm fn-bs-k0m-octets-true (implies (fn-cbor-octet-listp x) (true-listp x))
   :hints (("Goal" :in-theory (enable fn-cbor-octet-listp)))))
(defthm fn-bs-k0m-syscall-states
  (implies (and (fn-bs-statep bs) (stringp stage) (not (fn-bs-lookup bs :staging stage))
                (fn-cbor-octet-listp octets) (consp octets))
           (let ((b1 (fn-bs-marker-b1 bs stage)) (n (fn-bs-next-ino bs)))
             (and (equal (mv-nth 1 (fn-bs-create bs :staging stage :ok)) b1)
                  (equal (mv-nth 1 (fn-bs-write b1 n 0 octets :ok)) (fn-bs-marker-b2 bs stage octets))
                  (equal (fn-bs-k0m-with-content b1 n octets) (fn-bs-marker-b3 bs stage octets))
                  (equal (mv-nth 1 (fn-bs-fsync-file (fn-bs-marker-b2 bs stage octets) n :ok))
                         (fn-bs-marker-b3 bs stage octets))
                  (equal (fn-bs-k0m-with-root-entry
                          (mv-nth 1 (fn-bs-unlink (fn-bs-marker-b3 bs stage octets) :staging stage :ok))
                          *fn-bs-history-marker-name* n)
                         (fn-bs-marker-b5 bs stage octets)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-bs-create fn-bs-write fn-bs-fsync-file fn-bs-fence-file fn-bs-unlink
                            fn-bs-marker-b1 fn-bs-marker-b2 fn-bs-marker-b3 fn-bs-marker-b5
                            fn-bs-k0m-with-content fn-bs-k0m-with-root-entry
                            fn-bs-marker-lookup-is-entry-after fn-bs-entry-after fn-bs-durable-entry
                            fn-bs-ops-for-ino fn-bs-splice fn-bs-put-assoc fn-bs-invariants-vocabulary fn-bs-ops-for-ino-of-append fn-bs-apply-ops fn-bs-apply-op)
                           (fn-bs-statep fn-bs-lookup)))))
(defthm fn-bs-k0m-with-root-entry-statep
  (implies (and (fn-bs-statep b) (stringp name) (natp ino))
           (fn-bs-statep (fn-bs-k0m-with-root-entry b name ino)))
  :hints (("Goal" :in-theory (enable fn-bs-statep fn-bs-invariants-vocabulary fn-bs-dir-tablep fn-bs-entriesp))))
(defun fn-bs-k0m-drop-root-marker (ops)
  (declare (xargs :guard t :verify-guards nil))
  (cond ((atom ops) nil)
        ((and (consp (car ops)) (equal (car (car ops)) :set-entry)
              (equal (nth 1 (car ops)) :root)
              (equal (nth 2 (car ops)) *fn-bs-history-marker-name*))
         (fn-bs-k0m-drop-root-marker (cdr ops)))
        (t (cons (car ops) (fn-bs-k0m-drop-root-marker (cdr ops))))))
(defun fn-bs-marker-rename-dropped (b)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bs-make (fn-bs-unit b) (fn-bs-inodes b) (fn-bs-dirs b)
              (fn-bs-k0m-drop-root-marker (fn-bs-pending b)) (fn-bs-next-ino b)))
(defthm fn-bs-k0m-drop-of-root-quiet
  (implies (not (fn-bs-ops-for-dir ops :root))
           (equal (fn-bs-k0m-drop-root-marker ops) (true-list-fix ops)))
  :hints (("Goal" :in-theory (enable fn-bs-ops-for-dir))))
(defthm fn-bs-k0m-drop-of-append
  (equal (fn-bs-k0m-drop-root-marker (append a b))
         (append (fn-bs-k0m-drop-root-marker a) (fn-bs-k0m-drop-root-marker b))))
(local (defthm fn-bs-k0m-not-for-dir-id
  (implies (not (fn-bs-ops-for-dir ops d)) (equal (fn-bs-ops-not-for-dir ops d) (true-list-fix ops)))
  :hints (("Goal" :in-theory (enable fn-bs-ops-for-dir fn-bs-ops-not-for-dir)))))
(local (defthm fn-bs-k0m-not-for-dir-app
  (equal (fn-bs-ops-not-for-dir (append a b) n) (append (fn-bs-ops-not-for-dir a n) (fn-bs-ops-not-for-dir b n)))
  :hints (("Goal" :in-theory (enable fn-bs-ops-not-for-dir)))))
(defthm fn-bs-k0m-resolutions
  (implies (and (fn-bs-statep bs) (stringp stage) (not (fn-bs-lookup bs :staging stage))
                (not (fn-bs-ops-for-dir (fn-bs-pending bs) :root))
                (fn-cbor-octet-listp octets) (consp octets))
           (and (equal (fn-bs-marker-rename-dropped (fn-bs-marker-b4 bs stage octets))
                       (mv-nth 1 (fn-bs-unlink (fn-bs-marker-b3 bs stage octets) :staging stage :ok)))
                (equal (mv-nth 1 (fn-bs-fsync-dir (fn-bs-marker-b4 bs stage octets) :root :ok))
                       (fn-bs-marker-b5 bs stage octets))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-bs-unlink fn-bs-fsync-dir fn-bs-fence-dir
                            fn-bs-marker-b3 fn-bs-marker-b4 fn-bs-marker-b5
                            fn-bs-marker-lookup-is-entry-after fn-bs-entry-after fn-bs-durable-entry
                            fn-bs-ops-for-dir fn-bs-ops-not-for-dir fn-bs-put-assoc fn-bs-invariants-vocabulary
                            fn-bs-ops-for-dir-of-append fn-bs-apply-ops fn-bs-apply-op)
                           (fn-bs-statep fn-bs-lookup)))))

; K0 at the marker's cuts.
(defthm fn-bs-k0-marker-cuts-relation
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-finish-inputp ks sequence txid)
                (stringp stage)
                (not (fn-bs-lookup bs :staging stage))
                (fn-cbor-octet-listp octets) (consp octets))
           (let ((run (fn-bs-run bs ks (fn-bs-marker-program stage octets) nil groups capacity)))
             (and (equal (len run) 10)
                  (fn-bs-store-relation (car (nth 1 run)) (cdr (nth 1 run)))
                  (fn-bs-store-relation (car (nth 3 run)) (cdr (nth 3 run)))
                  (fn-bs-store-relation (car (nth 5 run)) (cdr (nth 5 run)))
                  (fn-bs-store-relation (fn-bs-marker-rename-dropped (car (nth 7 run)))
                                        (cdr (nth 7 run)))
                  (equal (mv-nth 1 (fn-bs-fsync-dir (car (nth 7 run)) :root :ok))
                         (car (nth 9 run)))
                  (fn-bs-store-relation (car (nth 9 run)) (cdr (nth 9 run))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-k0m-completing-window-facts
                 (:instance fn-bs-store-relation-unfolds)
                 (:instance fn-bs-k0m-syscall-states)
                 (:instance fn-bs-k0m-resolutions)
                 (:instance fn-bs-k0-staging-create-preserves-relation (b bs) (k ks))
                 (:instance fn-bs-k0-staging-create-fresh-facts (b bs) (k ks))
                 (:instance fn-bs-k0-staging-write-preserves-relation
                  (b (fn-bs-marker-b1 bs stage)) (k ks) (ino (fn-bs-next-ino bs)))
                 (:instance fn-bs-create-preserves-statep (s bs) (dir :staging) (name stage) (outcome :ok))
                 (:instance fn-bs-write-preserves-statep (s (fn-bs-marker-b1 bs stage))
                  (ino (fn-bs-next-ino bs)) (offset 0) (outcome :ok))
                 (:instance fn-bs-fsync-file-preserves-statep (s (fn-bs-marker-b2 bs stage octets))
                  (ino (fn-bs-next-ino bs)) (outcome :ok))
                 (:instance fn-bs-k0m-with-content-preserves-relation
                  (b (fn-bs-marker-b1 bs stage)) (k ks) (x (fn-bs-next-ino bs)) (c octets))
                 (:instance fn-bs-k0-staging-unlink-preserves-relation
                  (b (fn-bs-marker-b3 bs stage octets)) (k ks) (dir :staging) (name stage))
                 (:instance fn-bs-unlink-preserves-statep (s (fn-bs-marker-b3 bs stage octets))
                  (dir :staging) (name stage) (outcome :ok))
                 (:instance fn-bs-k0m-with-root-entry-statep
                  (b (mv-nth 1 (fn-bs-unlink (fn-bs-marker-b3 bs stage octets) :staging stage :ok)))
                  (name *fn-bs-history-marker-name*) (ino (fn-bs-next-ino bs)))
                 (:instance fn-bs-k0m-with-root-entry-preserves-relation
                  (b (mv-nth 1 (fn-bs-unlink (fn-bs-marker-b3 bs stage octets) :staging stage :ok)))
                  (k ks) (name *fn-bs-history-marker-name*) (ino (fn-bs-next-ino bs))))
           :in-theory (e/d (fn-bs-marker-run-shape)
                           (fn-bs-store-relation fn-bs-statep fn-bs-lookup fn-bs-create fn-bs-write
                            fn-bs-fsync-file fn-bs-fsync-dir fn-bs-unlink fn-bs-marker-program fn-bs-run
                            fn-bs-marker-b1 fn-bs-marker-b2 fn-bs-marker-b3 fn-bs-marker-b4 fn-bs-marker-b5
                            fn-bs-k0m-with-content fn-bs-k0m-with-root-entry fn-bs-marker-rename-dropped
                            fn-bs-authority-inode-list fn-bs-finish-inputp fn-bs-replay-visiblep
                            fn-bs-create-preserves-statep fn-bs-write-preserves-statep
                            fn-bs-fsync-file-preserves-statep fn-bs-unlink-preserves-statep
                            fn-bs-k0m-with-root-entry-statep)))))

;
; marker-replaced: every crash image of the pending rename is a crash image of
; one of its two resolutions.  The rename's root entry commutes with the rest
; of the pending list: a crash that lands it is a crash of the state with the
; entry already durable (the marker-durable state), and a crash that drops it
; is a crash of the state without it, under the same choices for every other
; operation.  The premise is the one the marker program has: every pending
; root entry operation is this rename (the root was quiet before it), and the
; root directory exists (a related state's config.json entry).

(defun fn-bs-k0m-root-marker-onlyp (ops ino)
  (declare (xargs :guard t :verify-guards nil))
  (cond ((atom ops) t)
        ((and (consp (car ops)) (member-equal (car (car ops)) '(:set-entry :del-entry))
              (equal (nth 1 (car ops)) :root))
         (and (equal (car (car ops)) :set-entry)
              (equal (nth 2 (car ops)) *fn-bs-history-marker-name*)
              (equal (nth 3 (car ops)) ino)
              (fn-bs-k0m-root-marker-onlyp (cdr ops) ino)))
        (t (fn-bs-k0m-root-marker-onlyp (cdr ops) ino))))
(defun fn-bs-k0m-has-root-marker (ops)
  (declare (xargs :guard t :verify-guards nil))
  (cond ((atom ops) nil)
        ((and (consp (car ops)) (equal (car (car ops)) :set-entry)
              (equal (nth 1 (car ops)) :root)
              (equal (nth 2 (car ops)) *fn-bs-history-marker-name*))
         t)
        (t (fn-bs-k0m-has-root-marker (cdr ops)))))
(defun fn-bs-k0m-drop-marker-choices (ops choices)
  (declare (xargs :guard t :verify-guards nil))
  (cond ((or (atom ops) (atom choices)) nil)
        ((and (consp (car ops)) (equal (car (car ops)) :set-entry)
              (equal (nth 1 (car ops)) :root)
              (equal (nth 2 (car ops)) *fn-bs-history-marker-name*))
         (fn-bs-k0m-drop-marker-choices (cdr ops) (cdr choices)))
        (t (cons (car choices) (fn-bs-k0m-drop-marker-choices (cdr ops) (cdr choices))))))
(encapsulate ()
(local (defun fn-bs-k0m-all-writesp (ops)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp ops)
      (and (consp (car ops)) (equal (car (car ops)) :write) (fn-bs-k0m-all-writesp (cdr ops)))
    t)))
(local (defthm fn-bs-k0m-tear-write-all-writesp
  (fn-bs-k0m-all-writesp (fn-bs-tear-write op sel i unit))
  :hints (("Goal" :induct (fn-bs-tear-write op sel i unit)
           :in-theory (e/d (fn-bs-tear-write)
                           (fn-bs-unit-count floor min max fn-bs-take fn-bs-zeros nthcdr))))))
(local (defthm fn-bs-k0m-all-writes-facts
  (implies (fn-bs-k0m-all-writesp ops)
           (and (equal (fn-bs-k0m-drop-root-marker ops) (true-list-fix ops))
                (fn-bs-k0m-root-marker-onlyp ops ino)
                (not (fn-bs-k0m-has-root-marker ops))))
  :hints (("Goal" :induct (fn-bs-k0m-all-writesp ops)
           :in-theory (e/d (fn-bs-k0m-drop-root-marker) (fn-bs-k0m-drop-of-root-quiet))))))
(defthm fn-bs-k0m-root-marker-onlyp-of-append
  (equal (fn-bs-k0m-root-marker-onlyp (append a b) ino)
         (and (fn-bs-k0m-root-marker-onlyp a ino) (fn-bs-k0m-root-marker-onlyp b ino))))
(defthm fn-bs-k0m-has-root-marker-of-append
  (equal (fn-bs-k0m-has-root-marker (append a b))
         (or (fn-bs-k0m-has-root-marker a) (fn-bs-k0m-has-root-marker b))))
(defthm fn-bs-k0m-drop-marker-choices-fit
  (implies (fn-bs-crash-choicesp choices ops unit)
           (fn-bs-crash-choicesp (fn-bs-k0m-drop-marker-choices ops choices)
                                 (fn-bs-k0m-drop-root-marker ops) unit))
  :hints (("Goal" :induct (fn-bs-k0m-drop-marker-choices ops choices)
           :in-theory (e/d (fn-bs-k0m-drop-root-marker fn-bs-crash-choicesp)
                           (fn-bs-crash-choicep fn-bs-k0m-drop-of-root-quiet)))))
(local (defthm fn-bs-k0m-crash-select-of-dropped
  (equal (fn-bs-crash-select (fn-bs-k0m-drop-root-marker ops)
                             (fn-bs-k0m-drop-marker-choices ops choices) unit)
         (fn-bs-k0m-drop-root-marker (fn-bs-crash-select ops choices unit)))
  :hints (("Goal" :induct (fn-bs-k0m-drop-marker-choices ops choices)
           :in-theory (e/d (fn-bs-k0m-drop-root-marker fn-bs-crash-select)
                           (fn-bs-tear-write fn-bs-k0m-drop-of-root-quiet))))))
(local (defthm fn-bs-k0m-crash-select-keeps-root-marker-only
  (implies (fn-bs-k0m-root-marker-onlyp ops ino)
           (fn-bs-k0m-root-marker-onlyp (fn-bs-crash-select ops choices unit) ino))
  :hints (("Goal" :induct (fn-bs-crash-select ops choices unit)
           :in-theory (e/d (fn-bs-crash-select) (fn-bs-tear-write))))))
(local (defthm fn-bs-k0m-apply-writes-of-drop
  (equal (fn-bs-apply-writes inodes (fn-bs-k0m-drop-root-marker ops))
         (fn-bs-apply-writes inodes ops))
  :hints (("Goal" :induct (fn-bs-apply-writes inodes ops)
           :in-theory (e/d (fn-bs-k0m-drop-root-marker fn-bs-apply-writes) (fn-bs-k0m-drop-of-root-quiet))))))
(local (defun fn-bs-k0m-set-marker (dirs ino)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bs-put-assoc :root (fn-bs-put-assoc *fn-bs-history-marker-name* ino
                                          (cdr (assoc-equal :root dirs)))
                   dirs)))
(local (defthm fn-bs-k0m-put-assoc-commutes
  (implies (and (not (equal k1 k2)) k2 (consp (assoc-equal k2 al)))
           (equal (fn-bs-put-assoc k1 v1 (fn-bs-put-assoc k2 v2 al))
                  (fn-bs-put-assoc k2 v2 (fn-bs-put-assoc k1 v1 al))))
  :hints (("Goal" :in-theory (enable fn-bs-put-assoc)))))
(local (defthm fn-bs-k0m-put-assoc-twice
  (equal (fn-bs-put-assoc k v2 (fn-bs-put-assoc k v1 al))
         (fn-bs-put-assoc k v2 al))
  :hints (("Goal" :in-theory (enable fn-bs-put-assoc)))))
(local (defthm fn-bs-k0m-assoc-of-put-assoc
  (and (implies (not (equal k k2))
                (equal (assoc-equal k (fn-bs-put-assoc k2 v al)) (assoc-equal k al)))
       (implies k (equal (assoc-equal k (fn-bs-put-assoc k v al)) (cons k v))))
  :hints (("Goal" :in-theory (enable fn-bs-put-assoc)))))
(local (defthm fn-bs-k0m-set-marker-facts
  (implies (consp (assoc-equal :root dirs))
           (and (consp (assoc-equal :root (fn-bs-k0m-set-marker dirs ino)))
                (equal (fn-bs-k0m-set-marker (fn-bs-k0m-set-marker dirs ino) ino)
                       (fn-bs-k0m-set-marker dirs ino))
                (implies (not (equal d :root))
                         (and (equal (assoc-equal d (fn-bs-k0m-set-marker dirs ino)) (assoc-equal d dirs))
                              (consp (assoc-equal :root (fn-bs-put-assoc d v dirs)))
                              (equal (fn-bs-k0m-set-marker (fn-bs-put-assoc d v dirs) ino)
                                     (fn-bs-put-assoc d v (fn-bs-k0m-set-marker dirs ino)))))))
  :hints (("Goal" :in-theory (e/d (fn-bs-k0m-set-marker) (fn-bs-put-assoc fn-bs-k0m-put-assoc-commutes))
                  :use ((:instance fn-bs-k0m-put-assoc-commutes (k1 d) (v1 v) (k2 :root)
                         (v2 (fn-bs-put-assoc *fn-bs-history-marker-name* ino (cdr (assoc-equal :root dirs))))
                         (al dirs)))))))
(local (in-theory (disable fn-bs-k0m-set-marker)))
(local (defthm fn-bs-k0m-set-marker-folds
  (equal (fn-bs-put-assoc :root (fn-bs-put-assoc *fn-bs-history-marker-name* ino
                                                 (cdr (assoc-equal :root dirs)))
                          dirs)
         (fn-bs-k0m-set-marker dirs ino))
  :hints (("Goal" :in-theory (enable fn-bs-k0m-set-marker)))))
(local (defthm fn-bs-k0m-apply-entries-of-marker-rename
  (implies (and (fn-bs-k0m-root-marker-onlyp ops ino)
                (consp (assoc-equal :root dirs)))
           (equal (fn-bs-apply-entries dirs ops)
                  (fn-bs-apply-entries (if (fn-bs-k0m-has-root-marker ops)
                                           (fn-bs-k0m-set-marker dirs ino)
                                         dirs)
                                       (fn-bs-k0m-drop-root-marker ops))))
  :hints (("Goal" :induct (fn-bs-apply-entries dirs ops)
           :in-theory (e/d (fn-bs-apply-entries fn-bs-k0m-drop-root-marker)
                           (fn-bs-k0m-drop-of-root-quiet fn-bs-k0m-set-marker
                            fn-bs-put-assoc fn-bs-del-assoc fn-bs-k0m-put-assoc-commutes))))))
; The crash of the pending state under CHOICES is the crash of a resolution
; under the same choices with the rename's own choice removed.
(defthm fn-bs-k0m-crash-of-pending-marker-rename
  (implies (and (fn-bs-k0m-root-marker-onlyp (fn-bs-pending s) ino)
                (consp (assoc-equal :root (fn-bs-dirs s))))
           (equal (fn-bs-crash s choices)
                  (fn-bs-crash (if (fn-bs-k0m-has-root-marker
                                    (fn-bs-crash-select (fn-bs-pending s) choices (fn-bs-unit s)))
                                   (fn-bs-k0m-with-root-entry (fn-bs-marker-rename-dropped s)
                                                              *fn-bs-history-marker-name* ino)
                                 (fn-bs-marker-rename-dropped s))
                               (fn-bs-k0m-drop-marker-choices (fn-bs-pending s) choices))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-k0m-apply-entries-of-marker-rename
                  (dirs (fn-bs-dirs s))
                  (ops (fn-bs-crash-select (fn-bs-pending s) choices (fn-bs-unit s)))))
           :in-theory (e/d (fn-bs-crash fn-bs-k0m-with-root-entry fn-bs-marker-rename-dropped
                            fn-bs-apply-ops-inodes-are-apply-writes fn-bs-apply-ops-dirs-are-apply-entries)
                           (fn-bs-k0m-apply-entries-of-marker-rename fn-bs-apply-ops fn-bs-apply-entries
                            fn-bs-apply-writes fn-bs-crash-select fn-bs-put-assoc
                            fn-bs-k0m-put-assoc-commutes)))))
)
(defthm fn-bs-k0m-marker-rename-crash-is-a-resolution-crash
  (implies (and (fn-bs-k0m-root-marker-onlyp (fn-bs-pending s) ino)
                (consp (assoc-equal :root (fn-bs-dirs s)))
                (fn-bs-crash-imagep s image))
           (or (fn-bs-crash-imagep (fn-bs-marker-rename-dropped s) image)
               (fn-bs-crash-imagep (fn-bs-k0m-with-root-entry (fn-bs-marker-rename-dropped s)
                                                              *fn-bs-history-marker-name* ino)
                                   image)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-k0m-crash-of-pending-marker-rename
                  (choices (fn-bs-crash-imagep-witness s image)))
                 (:instance fn-bs-k0m-drop-marker-choices-fit
                  (choices (fn-bs-crash-imagep-witness s image)) (ops (fn-bs-pending s))
                  (unit (fn-bs-unit s)))
                 (:instance fn-bs-crash-imagep-suff
                  (s (fn-bs-marker-rename-dropped s))
                  (choices (fn-bs-k0m-drop-marker-choices (fn-bs-pending s) (fn-bs-crash-imagep-witness s image))))
                 (:instance fn-bs-crash-imagep-suff
                  (s (fn-bs-k0m-with-root-entry (fn-bs-marker-rename-dropped s) *fn-bs-history-marker-name* ino))
                  (choices (fn-bs-k0m-drop-marker-choices (fn-bs-pending s) (fn-bs-crash-imagep-witness s image)))))
           :in-theory (e/d (fn-bs-crash-imagep)
                           (fn-bs-crash fn-bs-crash-imagep-suff fn-bs-crash-choicesp
                            fn-bs-k0m-drop-marker-choices-fit fn-bs-crash-select)))
          (and stable-under-simplificationp
               '(:in-theory (e/d (fn-bs-crash-imagep fn-bs-k0m-with-root-entry fn-bs-marker-rename-dropped)
                           (fn-bs-crash fn-bs-crash-imagep-suff fn-bs-crash-choicesp
                            fn-bs-k0m-drop-marker-choices-fit fn-bs-crash-select))))))

; K0 at marker-replaced: both resolutions are related to the cut's kernel, and
; every crash image of the cut's byte state is a crash image of one of them.
(defthm fn-bs-k0m-root-quiet-is-marker-only
  (implies (not (fn-bs-ops-for-dir ops :root))
           (fn-bs-k0m-root-marker-onlyp ops ino))
  :hints (("Goal" :in-theory (enable fn-bs-ops-for-dir))))
(defthm fn-bs-k0m-root-entry-means-root-dir
  (implies (fn-bs-inop (fn-bs-durable-entry b :root name))
           (consp (assoc-equal :root (fn-bs-dirs b))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-bs-durable-entry fn-bs-inop))))
(defthm fn-bs-k0m-b4-marker-only
  (implies (and (not (fn-bs-ops-for-dir (fn-bs-pending bs) :root))
                (fn-bs-inop (fn-bs-durable-entry bs :root *fn-bs-scan-config-name*)))
           (and (fn-bs-k0m-root-marker-onlyp (fn-bs-pending (fn-bs-marker-b4 bs stage octets))
                                             (fn-bs-next-ino bs))
                (consp (assoc-equal :root (fn-bs-dirs (fn-bs-marker-b4 bs stage octets))))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-bs-k0m-root-entry-means-root-dir (b bs) (name *fn-bs-scan-config-name*)))
           :in-theory (e/d (fn-bs-marker-b4) (fn-bs-inop fn-bs-durable-entry)))))
(defthm fn-bs-k0-marker-replaced-cut-relation
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-finish-inputp ks sequence txid)
                (stringp stage)
                (not (fn-bs-lookup bs :staging stage))
                (fn-cbor-octet-listp octets) (consp octets))
           (let* ((run (fn-bs-run bs ks (fn-bs-marker-program stage octets) nil groups capacity))
                  (b (car (nth 7 run))) (k (cdr (nth 7 run)))
                  (landed (mv-nth 1 (fn-bs-fsync-dir b :root :ok))))
             (and (fn-bs-store-relation (fn-bs-marker-rename-dropped b) k)
                  (fn-bs-store-relation landed k)
                  (implies (fn-bs-crash-imagep b image)
                           (or (fn-bs-crash-imagep (fn-bs-marker-rename-dropped b) image)
                               (fn-bs-crash-imagep landed image))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-k0-marker-cuts-relation
                 fn-bs-k0m-completing-window-facts
                 fn-bs-k0m-syscall-states
                 fn-bs-k0m-resolutions
                 (:instance fn-bs-store-relation-unfolds)
                 (:instance fn-bs-k0m-b4-marker-only)
                 (:instance fn-bs-k0m-marker-rename-crash-is-a-resolution-crash
                  (s (fn-bs-marker-b4 bs stage octets)) (ino (fn-bs-next-ino bs))))
           :in-theory (e/d (fn-bs-marker-run-shape)
                           (fn-bs-store-relation fn-bs-statep fn-bs-lookup fn-bs-create fn-bs-write
                            fn-bs-fsync-file fn-bs-fsync-dir fn-bs-unlink fn-bs-marker-program fn-bs-run
                            fn-bs-marker-b1 fn-bs-marker-b2 fn-bs-marker-b3 fn-bs-marker-b4 fn-bs-marker-b5
                            fn-bs-k0m-with-content fn-bs-k0m-with-root-entry fn-bs-marker-rename-dropped
                            fn-bs-crash-imagep fn-bs-finish-inputp fn-bs-replay-visiblep
                            fn-bs-inop fn-bs-durable-entry)))))

(in-theory (disable fn-bs-k0m-with-content fn-bs-k0m-with-root-entry
                    fn-bs-k0m-drop-root-marker fn-bs-marker-rename-dropped
                    fn-bs-k0m-root-marker-onlyp fn-bs-k0m-has-root-marker
                    fn-bs-k0m-drop-marker-choices))
