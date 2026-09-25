; fn: general per-step lemmas for K0 (T16's model side, lane k0-general-step).
;
; Each lemma is one syscall of the byte model, stated over an ARBITRARY
; related state (not a program pair) and every outcome the environment may
; choose, so books/byte-store-k0-step.lisp can prove the relation preserved
; step by step.  The existing single-step lemmas (byte-store-k0-staging,
; -k0-marker, -record-fence, -program-invariants) cover :ok outcomes; this
; book adds the error outcomes (a short write, a failed fsync that lands a
; subset of the file's pending writes) and the fsync of a non-authority file.
(in-package "ACL2")
(include-book "byte-store-k0-marker")
(include-book "byte-store-record-fence")
(include-book "byte-store-invariants")

; A write's error outcome (ERR . N) is the successful write of its first N
; octets (fn-bs-take pads with zero past the end, as the model's short write).
(defthm fn-bs-k0s-len-of-take (equal (len (fn-bs-take n xs)) (nfix n)) :hints (("Goal" :in-theory (enable fn-bs-take))))
(defthm fn-bs-k0s-take-of-take-natp (implies (natp n) (equal (fn-bs-take n (fn-bs-take n xs)) (fn-bs-take n xs))) :hints (("Goal" :in-theory (enable fn-bs-take))))
(defthm fn-bs-k0s-take-of-len (implies (true-listp xs) (equal (fn-bs-take (len xs) xs) xs)) :hints (("Goal" :in-theory (enable fn-bs-take))))
(defthm fn-bs-k0s-take-octets (implies (fn-cbor-octet-listp xs) (fn-cbor-octet-listp (fn-bs-take n xs))) :hints (("Goal" :in-theory (enable fn-bs-take fn-cbor-octet-listp))))
(defthm fn-bs-k0s-octets-are-true-lists (implies (fn-cbor-octet-listp xs) (true-listp xs)) :hints (("Goal" :in-theory (enable fn-cbor-octet-listp))))
(defthm fn-bs-k0s-write-outcome-is-an-ok-write
  (implies (fn-cbor-octet-listp octets)
           (equal (mv-nth 1 (fn-bs-write b ino 0 octets outcome))
                  (mv-nth 1 (fn-bs-write b ino 0 (if (equal outcome :ok) octets
                                                   (fn-bs-take (nfix (cdr outcome)) octets))
                                         :ok))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t :in-theory (e/d (fn-bs-write) (fn-bs-take fn-cbor-octet-listp)))))
(defthm fn-bs-k0s-write-preserves-relation
  (implies (and (fn-bs-store-relation b k)
                (not (fn-bs-replay-visiblep k))
                (fn-cbor-octet-listp octets)
                (not (member-equal ino (fn-bs-authority-inode-list b))))
           (fn-bs-store-relation (mv-nth 1 (fn-bs-write b ino 0 octets outcome)) k))
  :hints (("Goal" :use (fn-bs-k0s-write-outcome-is-an-ok-write
                        (:instance fn-bs-k0-staging-write-preserves-relation
                         (octets (if (equal outcome :ok) octets (fn-bs-take (nfix (cdr outcome)) octets)))))
           :in-theory (disable fn-bs-write fn-bs-store-relation fn-bs-take fn-cbor-octet-listp))))

; An fsync of one file, with any outcome, applies some of that file's
; pending writes (all of them on :ok, a crash selection of them on error)
; and drops the rest: the other inodes, the directories and the other
; pending operations are untouched.
(defun fn-bs-k0s-writes-to (ops ino)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp ops)
      (and (consp (car ops)) (equal (car (car ops)) :write) (equal (nth 1 (car ops)) ino)
           (fn-bs-k0s-writes-to (cdr ops) ino))
    t))
(defthm fn-bs-k0s-writes-to-of-append
  (equal (fn-bs-k0s-writes-to (append a b) ino)
         (and (fn-bs-k0s-writes-to a ino) (fn-bs-k0s-writes-to b ino))))
(defthm fn-bs-k0s-writes-to-ops-for-ino
  (fn-bs-k0s-writes-to (fn-bs-ops-for-ino ops ino) ino)
  :hints (("Goal" :in-theory (enable fn-bs-ops-for-ino))))
(defthm fn-bs-k0s-writes-to-tear-write
  (fn-bs-k0s-writes-to (fn-bs-tear-write op sel i unit) (nth 1 op))
  :hints (("Goal" :induct (fn-bs-tear-write op sel i unit)
           :in-theory (e/d (fn-bs-tear-write) (fn-bs-unit-count floor min max fn-bs-take fn-bs-zeros nthcdr)))))
(defthm fn-bs-k0s-writes-to-crash-select
  (implies (fn-bs-k0s-writes-to ops ino)
           (fn-bs-k0s-writes-to (fn-bs-crash-select ops choices unit) ino))
  :hints (("Goal" :induct (fn-bs-crash-select ops choices unit)
           :in-theory (e/d (fn-bs-crash-select) (fn-bs-tear-write)))))
(defthm fn-bs-k0s-writes-to-keep-entries
  (implies (fn-bs-k0s-writes-to ops ino)
           (equal (fn-bs-apply-entries dirs ops) dirs))
  :hints (("Goal" :in-theory (enable fn-bs-apply-entries))))
(defthm fn-bs-k0s-put-assoc-twice
  (equal (fn-bs-put-assoc k a (fn-bs-put-assoc k b al)) (fn-bs-put-assoc k a al))
  :hints (("Goal" :in-theory (enable fn-bs-put-assoc))))
(defthm fn-bs-k0s-assoc-of-put-assoc-same
  (implies k (equal (assoc-equal k (fn-bs-put-assoc k v a)) (cons k v)))
  :hints (("Goal" :in-theory (enable fn-bs-put-assoc))))
(defthm fn-bs-k0s-writes-to-apply-writes
  (implies (and (fn-bs-k0s-writes-to ops ino) (consp ops) ino)
           (equal (fn-bs-apply-writes inodes ops)
                  (fn-bs-put-assoc ino (cdr (assoc-equal ino (fn-bs-apply-writes inodes ops))) inodes)))
  :rule-classes nil
  :hints (("Goal" :induct (fn-bs-apply-writes inodes ops)
           :in-theory (e/d (fn-bs-apply-writes) (fn-bs-splice)))))
(defun fn-bs-k0s-drop-writes (b x)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bs-make (fn-bs-unit b) (fn-bs-inodes b) (fn-bs-dirs b)
              (fn-bs-ops-not-for-ino (fn-bs-pending b) x) (fn-bs-next-ino b)))
(defthm fn-bs-k0s-ops-for-dir-of-ops-not-for-ino
  (equal (fn-bs-ops-for-dir (fn-bs-ops-not-for-ino ops x) d) (fn-bs-ops-for-dir ops d))
  :hints (("Goal" :in-theory (enable fn-bs-ops-for-dir fn-bs-ops-not-for-ino))))
(defthm fn-bs-k0s-entry-targets-of-ops-not-for-ino
  (equal (fn-bs-pending-entry-targets (fn-bs-ops-not-for-ino ops x)) (fn-bs-pending-entry-targets ops))
  :hints (("Goal" :in-theory (enable fn-bs-pending-entry-targets fn-bs-ops-not-for-ino))))
(defthm fn-bs-k0s-ops-for-ino-of-ops-not-for-ino-other
  (implies (not (equal y x))
           (equal (fn-bs-ops-for-ino (fn-bs-ops-not-for-ino ops x) y) (fn-bs-ops-for-ino ops y)))
  :hints (("Goal" :in-theory (enable fn-bs-ops-for-ino fn-bs-ops-not-for-ino))))
(defthm fn-bs-k0s-drop-writes-knownp
  (equal (fn-bs-inode-list-knownp (fn-bs-k0s-drop-writes b x) ys) (fn-bs-inode-list-knownp b ys))
  :hints (("Goal" :induct (len ys) :in-theory (enable fn-bs-inode-list-knownp))))
(defthm fn-bs-k0s-drop-writes-authority-list
  (equal (fn-bs-authority-inode-list (fn-bs-k0s-drop-writes b x)) (fn-bs-authority-inode-list b))
  :hints (("Goal" :in-theory (enable fn-bs-authority-inode-list fn-bs-durable-entry))))
(defthm fn-bs-k0s-drop-writes-all-fencedp
  (implies (fn-bs-all-fencedp b ys)
           (fn-bs-all-fencedp (fn-bs-k0s-drop-writes b x) ys))
  :hints (("Goal" :induct (len ys) :in-theory (enable fn-bs-all-fencedp fn-bs-fencedp))
          ("Subgoal *1/1" :cases ((equal (car ys) x))
           :use ((:instance fn-bs-ops-for-ino-of-ops-not-for-ino (ops (fn-bs-pending b)) (ino x))))))
(defthm fn-bs-k0s-drop-writes-statep
  (implies (fn-bs-statep b) (fn-bs-statep (fn-bs-k0s-drop-writes b x)))
  :hints (("Goal" :use ((:instance fn-bs-writes-knownp-of-ops-not-for-ino (ops (fn-bs-pending b)) (inodes (fn-bs-inodes b)) (ino x))
                        (:instance fn-bs-writes-nonemptyp-of-ops-not-for-ino (ops (fn-bs-pending b)) (ino x))
                        (:instance fn-bs-op-listp-of-ops-not-for-ino (ops (fn-bs-pending b)) (ino x)))
           :in-theory (enable fn-bs-statep fn-bs-shapep))))
(defthm fn-bs-k0s-drop-writes-projections
  (implies (fn-bs-statep b)
           (let ((d (fn-bs-k0s-drop-writes b x)))
             (and (equal (fn-bs-dirs d) (fn-bs-dirs b))
                  (equal (fn-bs-pending d) (fn-bs-ops-not-for-ino (fn-bs-pending b) x))
                  (equal (fn-bs-durable-entry d dir name) (fn-bs-durable-entry b dir name))
                  (equal (fn-bs-durable-content d ino) (fn-bs-durable-content b ino))
                  (equal (fn-bs-durable-records d) (fn-bs-durable-records b))
                  (equal (fn-bs-durable-frontier d) (fn-bs-durable-frontier b)))))
  :hints (("Goal" :use ((:instance fn-bs-k0-durable-projections-ignore-pending
                         (p (fn-bs-ops-not-for-ino (fn-bs-pending b) x))))
           :in-theory (e/d (fn-bs-k0s-drop-writes) (fn-bs-statep fn-bs-durable-records fn-bs-durable-frontier
                                                    fn-bs-durable-content fn-bs-durable-entry)))))
(defthm fn-bs-k0s-relation-facts
  (implies (fn-bs-store-relation b k)
           (and (fn-bs-statep b) (fn-sf-statep k)
                (fn-bs-authority-knownp b) (fn-bs-authority-fencedp b)))
  :rule-classes nil
  :hints (("Goal" :in-theory '(fn-bs-store-relation))))
(defthm fn-bs-k0s-drop-writes-preserves-relation
  (implies (and (fn-bs-store-relation b k)
                (not (fn-bs-replay-visiblep k))
                (not (fn-bs-ops-for-dir (fn-bs-pending b) :root))
                (not (fn-bs-ops-for-dir (fn-bs-pending b) :transactions)))
           (fn-bs-store-relation (fn-bs-k0s-drop-writes b x) k))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-k0-quiet-projection-transports-relation
                  (bs b) (file (fn-bs-k0s-drop-writes b x)))
                 (:instance fn-bs-store-relation-unfolds (bs b) (ks k)) (:instance fn-bs-k0s-relation-facts))
           :in-theory (e/d (fn-bs-authority-fencedp fn-bs-authority-knownp)
                           (fn-bs-store-relation fn-bs-statep fn-bs-k0s-drop-writes fn-bs-authority-inode-list
                            fn-bs-durable-records fn-bs-durable-frontier fn-bs-durable-content fn-bs-durable-entry)))))
(defun fn-bs-k0s-fsync-file-selection (b x outcome)
  (declare (xargs :guard t :verify-guards nil))
  (if (equal outcome :ok) (fn-bs-ops-for-ino (fn-bs-pending b) x)
    (fn-bs-crash-select (fn-bs-ops-for-ino (fn-bs-pending b) x) (cdr outcome) (fn-bs-unit b))))
(defthm fn-bs-k0s-apply-entries-of-ino-ops
  (equal (fn-bs-apply-entries dirs (fn-bs-ops-for-ino ops x)) dirs)
  :hints (("Goal" :use ((:instance fn-bs-k0s-writes-to-keep-entries (ino x) (ops (fn-bs-ops-for-ino ops x)))))))
(defthm fn-bs-k0s-apply-entries-of-selected-ino-ops
  (equal (fn-bs-apply-entries dirs (fn-bs-crash-select (fn-bs-ops-for-ino ops x) ch u)) dirs)
  :hints (("Goal" :use ((:instance fn-bs-k0s-writes-to-keep-entries (ino x) (ops (fn-bs-crash-select (fn-bs-ops-for-ino ops x) ch u)))
                        (:instance fn-bs-k0s-writes-to-crash-select (ino x) (ops (fn-bs-ops-for-ino ops x)) (choices ch) (unit u)))
           :in-theory (disable fn-bs-crash-select fn-bs-k0s-writes-to-keep-entries fn-bs-k0s-writes-to-crash-select))))
(defthm fn-bs-k0s-fsync-file-shape
  (implies x
           (equal (mv-nth 1 (fn-bs-fsync-file b x outcome))
                  (let ((w (fn-bs-k0s-fsync-file-selection b x outcome)))
                    (if (consp w)
                        (fn-bs-k0m-with-content (fn-bs-k0s-drop-writes b x) x
                                                (cdr (assoc-equal x (fn-bs-apply-writes (fn-bs-inodes b) w))))
                      (fn-bs-k0s-drop-writes b x)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-k0s-writes-to-apply-writes (ino x) (inodes (fn-bs-inodes b))
                  (ops (fn-bs-k0s-fsync-file-selection b x outcome))) (:instance fn-bs-k0s-writes-to-keep-entries (ino x) (dirs (fn-bs-dirs b)) (ops (fn-bs-k0s-fsync-file-selection b x outcome))) (:instance fn-bs-k0s-writes-to-crash-select (ino x) (ops (fn-bs-ops-for-ino (fn-bs-pending b) x)) (choices (cdr outcome)) (unit (fn-bs-unit b))))
           :in-theory (e/d (fn-bs-fsync-file fn-bs-fence-file fn-bs-k0m-with-content fn-bs-k0s-drop-writes
                            fn-bs-k0s-fsync-file-selection
                            fn-bs-apply-ops-inodes-are-apply-writes fn-bs-apply-ops-dirs-are-apply-entries)
                           (fn-bs-apply-ops fn-bs-apply-writes fn-bs-crash-select fn-bs-ops-for-ino)))
          (and stable-under-simplificationp '(:expand ((:free (i) (fn-bs-apply-writes i nil)) (:free (d) (fn-bs-apply-entries d nil)))))))
(defthm fn-bs-k0s-fsync-file-preserves-relation
  (implies (and (fn-bs-store-relation b k)
                (not (fn-bs-replay-visiblep k))
                (natp x)
                (not (member-equal x (fn-bs-authority-inode-list b)))
                (not (fn-bs-ops-for-dir (fn-bs-pending b) :root))
                (not (fn-bs-ops-for-dir (fn-bs-pending b) :transactions))
                (or (equal outcome :ok)
                    (fn-bs-crash-choicesp (cdr outcome) (fn-bs-ops-for-ino (fn-bs-pending b) x) (fn-bs-unit b))))
           (fn-bs-store-relation (mv-nth 1 (fn-bs-fsync-file b x outcome)) k))
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-k0s-fsync-file-shape
                 fn-bs-k0s-relation-facts
                 fn-bs-k0s-drop-writes-preserves-relation
                 (:instance fn-bs-fsync-file-preserves-statep (s b) (ino x))
                 (:instance fn-bs-k0m-with-content-preserves-relation
                  (b (fn-bs-k0s-drop-writes b x))
                  (c (cdr (assoc-equal x (fn-bs-apply-writes (fn-bs-inodes b) (fn-bs-k0s-fsync-file-selection b x outcome)))))))
           :in-theory (disable fn-bs-store-relation fn-bs-fsync-file fn-bs-k0s-drop-writes fn-bs-k0m-with-content
                               fn-bs-statep fn-bs-authority-inode-list fn-bs-k0s-fsync-file-selection
                               fn-bs-fsync-file-preserves-statep fn-bs-k0s-drop-writes-preserves-relation
                               fn-bs-apply-writes fn-bs-crash-choicesp))))

; Create, unlink and rename, every outcome.
(defthm fn-bs-k0s-create-preserves-relation
  (implies (and (fn-bs-store-relation b k)
                (not (fn-bs-replay-visiblep k))
                (fn-bs-namep stage))
           (fn-bs-store-relation (mv-nth 1 (fn-bs-create b :staging stage outcome)) k))
  :hints (("Goal" :cases ((fn-bs-lookup b :staging stage) (equal outcome :ok))
           :use (fn-bs-k0-staging-create-preserves-relation)
           :in-theory (e/d (fn-bs-create) (fn-bs-store-relation fn-bs-lookup)))))
(defthm fn-bs-k0s-unlink-preserves-relation
  (implies (and (fn-bs-store-relation b k)
                (not (fn-bs-replay-visiblep k))
                (not (equal dir :root))
                (not (equal dir :transactions)))
           (fn-bs-store-relation (mv-nth 1 (fn-bs-unlink b dir name outcome)) k))
  :hints (("Goal" :use (fn-bs-k0-staging-unlink-preserves-relation)
           :in-theory (e/d (fn-bs-unlink) (fn-bs-store-relation fn-bs-lookup)))))
; The pending marker rename (a root entry the relation's shape does not name)
; is covered by its two resolutions.
(defun fn-bs-k0s-root-target (bs)
  (declare (xargs :guard t :verify-guards nil))
  (nth 3 (car (fn-bs-ops-for-dir (fn-bs-pending bs) :root))))
(defun fn-bs-k0s-marker-landed (bs)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bs-k0m-with-root-entry (fn-bs-marker-rename-dropped bs) *fn-bs-history-marker-name*
                             (fn-bs-k0s-root-target bs)))
(defun fn-bs-k0s-marker-pendingp (bs ks)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-bs-k0m-has-root-marker (fn-bs-pending bs))
       (fn-bs-k0m-root-marker-onlyp (fn-bs-pending bs) (fn-bs-k0s-root-target bs))
       (consp (assoc-equal :root (fn-bs-dirs bs)))
       (fn-bs-store-relation (fn-bs-marker-rename-dropped bs) ks)
       (fn-bs-store-relation (fn-bs-k0s-marker-landed bs) ks)))
(defun fn-bs-k0-coveredp (bs ks)
  (declare (xargs :guard t :verify-guards nil))
  (or (fn-bs-store-relation bs ks) (fn-bs-k0s-marker-pendingp bs ks)))
(defthm fn-bs-k0-covered-crash-image-is-a-related-image
  (implies (and (fn-bs-k0-coveredp bs ks) (fn-bs-crash-imagep bs image))
           (or (fn-bs-store-relation bs ks)
               (and (fn-bs-store-relation (fn-bs-marker-rename-dropped bs) ks)
                    (fn-bs-crash-imagep (fn-bs-marker-rename-dropped bs) image))
               (and (fn-bs-store-relation (fn-bs-k0s-marker-landed bs) ks)
                    (fn-bs-crash-imagep (fn-bs-k0s-marker-landed bs) image))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-bs-k0m-marker-rename-crash-is-a-resolution-crash
                         (s bs) (ino (fn-bs-k0s-root-target bs))))
           :in-theory (e/d (fn-bs-k0-coveredp fn-bs-k0s-marker-pendingp fn-bs-k0s-marker-landed)
                           (fn-bs-store-relation fn-bs-crash-imagep fn-bs-marker-rename-dropped
                            fn-bs-k0m-with-root-entry fn-bs-k0m-root-marker-onlyp fn-bs-k0s-root-target)))))
(defthm fn-bs-k0s-marker-rename-dropped-is-unlink
  (implies (and (fn-bs-statep b)
                (not (fn-bs-ops-for-dir (fn-bs-pending b) :root))
                (fn-bs-inop (fn-bs-lookup b :staging stage)))
           (equal (fn-bs-marker-rename-dropped
                   (mv-nth 1 (fn-bs-rename b :staging stage :root *fn-bs-history-marker-name* :ok)))
                  (mv-nth 1 (fn-bs-unlink b :staging stage :ok))))
  :hints (("Goal" :use ((:instance fn-bs-op-listp-implies-true-listp (x (fn-bs-pending b))))
           :in-theory (e/d (fn-bs-rename fn-bs-unlink fn-bs-marker-rename-dropped fn-bs-k0m-drop-root-marker fn-bs-statep)
                           (fn-bs-lookup fn-bs-op-listp-implies-true-listp)))))
(defthm fn-bs-k0s-issued-rename-is-ok-rename
  (implies (and (consp outcome) (equal (cdr outcome) :issued))
           (equal (mv-nth 1 (fn-bs-rename b sdir sname ddir dname outcome))
                  (mv-nth 1 (fn-bs-rename b sdir sname ddir dname :ok))))
  :hints (("Goal" :in-theory (e/d (fn-bs-rename) (fn-bs-lookup)))))
(defthm fn-bs-k0s-failed-rename-is-identity
  (implies (not (or (equal outcome :ok) (and (consp outcome) (equal (cdr outcome) :issued))))
           (equal (mv-nth 1 (fn-bs-rename b sdir sname ddir dname outcome)) b))
  :hints (("Goal" :in-theory (e/d (fn-bs-rename) (fn-bs-lookup)))))
(defthm fn-bs-k0s-marker-rename-covered
  (implies (and (fn-bs-store-relation b k)
                (not (fn-bs-replay-visiblep k))
                (not (fn-bs-ops-for-dir (fn-bs-pending b) :root))
                (fn-bs-inop (fn-bs-lookup b :staging stage)))
           (fn-bs-k0-coveredp (mv-nth 1 (fn-bs-rename b :staging stage :root *fn-bs-history-marker-name* outcome)) k))
  :hints (("Goal" :do-not-induct t
           :cases ((or (equal outcome :ok) (and (consp outcome) (equal (cdr outcome) :issued))))
           :use (fn-bs-k0s-marker-rename-dropped-is-unlink
                 fn-bs-k0s-relation-facts
                 (:instance fn-bs-k0-staging-unlink-preserves-relation (dir :staging) (name stage))
                 (:instance fn-bs-store-relation-unfolds (bs b) (ks k))
                 (:instance fn-bs-k0m-root-entry-means-root-dir (name *fn-bs-scan-config-name*))
                 (:instance fn-bs-k0m-with-root-entry-preserves-relation
                  (b (mv-nth 1 (fn-bs-unlink b :staging stage :ok)))
                  (name *fn-bs-history-marker-name*) (ino (fn-bs-lookup b :staging stage)))
                 (:instance fn-bs-k0m-with-root-entry-statep
                  (b (mv-nth 1 (fn-bs-unlink b :staging stage :ok)))
                  (name *fn-bs-history-marker-name*) (ino (fn-bs-lookup b :staging stage))))
           :in-theory (e/d (fn-bs-k0-coveredp fn-bs-k0s-marker-pendingp fn-bs-k0s-marker-landed fn-bs-k0s-root-target
                            fn-bs-k0m-has-root-marker fn-bs-k0m-root-marker-onlyp)
                           (fn-bs-store-relation fn-bs-lookup fn-bs-unlink fn-bs-marker-rename-dropped
                            fn-bs-k0m-with-root-entry fn-bs-statep fn-bs-inop fn-bs-durable-entry)))
          (and stable-under-simplificationp
               '(:in-theory (e/d (fn-bs-rename fn-bs-ops-for-dir-of-append fn-bs-ops-for-dir fn-bs-k0-coveredp fn-bs-k0s-marker-pendingp fn-bs-k0s-marker-landed fn-bs-k0s-root-target
                            fn-bs-k0m-has-root-marker fn-bs-k0m-root-marker-onlyp fn-bs-inop)
                           (fn-bs-store-relation fn-bs-lookup fn-bs-unlink fn-bs-marker-rename-dropped
                            fn-bs-k0m-with-root-entry fn-bs-statep fn-bs-durable-entry))))))
(defthm fn-bs-k0s-frontier-rename-preserves-relation
  (let ((ino (fn-bs-lookup b :staging stage)))
    (implies (and (fn-bs-store-relation b k)
                  (not (fn-bs-replay-visiblep k))
                  (not (fn-bs-ops-for-dir (fn-bs-pending b) :root))
                  (not (fn-bs-ops-for-dir (fn-bs-pending b) :transactions))
                  (fn-bs-namep stage)
                  (fn-bs-inop ino)
                  (fn-bs-fencedp b ino)
                  (consp (assoc-equal ino (fn-bs-inodes b)))
                  (fn-sf-frontier-new-visiblep k)
                  (not (fn-sf-record-present-visiblep k))
                  (equal (fn-bs-frontier-decode (fn-bs-durable-content b ino)) (fn-sf-frontier-candidate k))
                  (equal (fn-bs-durable-frontier b) (fn-sf-frontier k))
                  (equal (fn-bs-durable-records b) (fn-sf-records k)))
             (fn-bs-store-relation (mv-nth 1 (fn-bs-rename b :staging stage :root *fn-bs-frontier-name* outcome)) k)))
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-k0s-relation-facts
                 (:instance fn-bs-k0-add-pending-frontier-rename-transports-relation
                  (b6 b) (k6 k) (ino (fn-bs-lookup b :staging stage)) (sdir :staging) (sname stage)))
           :in-theory (e/d (fn-bs-rename) (fn-bs-store-relation fn-bs-lookup fn-bs-statep)))))

; The root barrier over a pending marker rename, every outcome: it lands the
; marker entry (the landed resolution) or drops it (the dropped resolution).
(defun fn-bs-k0s-all-marker-sets (ops ino)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp ops)
      (and (consp (car ops)) (equal (car (car ops)) :set-entry) (equal (nth 1 (car ops)) :root)
           (equal (nth 2 (car ops)) *fn-bs-history-marker-name*) (equal (nth 3 (car ops)) ino)
           (fn-bs-k0s-all-marker-sets (cdr ops) ino))
    t))
(defthm fn-bs-k0s-all-marker-sets-of-append
  (equal (fn-bs-k0s-all-marker-sets (append a b) ino)
         (and (fn-bs-k0s-all-marker-sets a ino) (fn-bs-k0s-all-marker-sets b ino))))
(defthm fn-bs-k0s-marker-onlyp-root-ops
  (implies (fn-bs-k0m-root-marker-onlyp ops ino)
           (fn-bs-k0s-all-marker-sets (fn-bs-ops-for-dir ops :root) ino))
  :hints (("Goal" :in-theory (enable fn-bs-k0m-root-marker-onlyp fn-bs-ops-for-dir))))
(defthm fn-bs-k0s-has-root-marker-root-ops
  (implies (fn-bs-k0m-has-root-marker ops) (consp (fn-bs-ops-for-dir ops :root)))
  :hints (("Goal" :in-theory (enable fn-bs-k0m-has-root-marker fn-bs-ops-for-dir))))
(defthm fn-bs-k0s-all-marker-sets-crash-select
  (implies (fn-bs-k0s-all-marker-sets ops ino)
           (fn-bs-k0s-all-marker-sets (fn-bs-crash-select ops ch u) ino))
  :hints (("Goal" :induct (fn-bs-crash-select ops ch u) :in-theory (enable fn-bs-crash-select))))
(defthm fn-bs-k0s-all-marker-sets-writes
  (implies (fn-bs-k0s-all-marker-sets ops ino) (equal (fn-bs-apply-writes inodes ops) inodes))
  :hints (("Goal" :in-theory (enable fn-bs-apply-writes))))
(defthm fn-bs-k0s-all-marker-sets-entries
  (implies (and (fn-bs-k0s-all-marker-sets ops ino) (consp ops))
           (equal (fn-bs-apply-entries dirs ops)
                  (fn-bs-put-assoc :root (fn-bs-put-assoc *fn-bs-history-marker-name* ino
                                                          (cdr (assoc-equal :root dirs)))
                                   dirs)))
  :hints (("Goal" :induct (fn-bs-apply-entries dirs ops) :in-theory (enable fn-bs-apply-entries))))
(defthm fn-bs-k0s-marker-onlyp-not-for-root
  (implies (fn-bs-k0m-root-marker-onlyp ops ino)
           (equal (fn-bs-ops-not-for-dir ops :root) (fn-bs-k0m-drop-root-marker ops)))
  :hints (("Goal" :in-theory (enable fn-bs-k0m-root-marker-onlyp fn-bs-ops-not-for-dir fn-bs-k0m-drop-root-marker))))
(defthm fn-bs-k0s-marker-barrier-resolves
  (implies (and (fn-bs-k0m-root-marker-onlyp (fn-bs-pending m) (fn-bs-k0s-root-target m))
                (fn-bs-k0m-has-root-marker (fn-bs-pending m)))
           (and (equal (mv-nth 1 (fn-bs-fsync-dir m :root :ok)) (fn-bs-k0s-marker-landed m))
                (member-equal (mv-nth 1 (fn-bs-fsync-dir m :root outcome))
                              (list (fn-bs-marker-rename-dropped m) (fn-bs-k0s-marker-landed m)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-k0s-marker-onlyp-root-ops (ops (fn-bs-pending m)) (ino (fn-bs-k0s-root-target m)))
                 (:instance fn-bs-k0s-all-marker-sets-crash-select (ops (fn-bs-ops-for-dir (fn-bs-pending m) :root))
                            (ino (fn-bs-k0s-root-target m)) (ch (cdr outcome)) (u (fn-bs-unit m)))
                 (:instance fn-bs-k0s-all-marker-sets-writes (ops (fn-bs-ops-for-dir (fn-bs-pending m) :root))
                            (ino (fn-bs-k0s-root-target m)) (inodes (fn-bs-inodes m)))
                 (:instance fn-bs-k0s-all-marker-sets-entries (ops (fn-bs-ops-for-dir (fn-bs-pending m) :root))
                            (ino (fn-bs-k0s-root-target m)) (dirs (fn-bs-dirs m)))
                 (:instance fn-bs-k0s-all-marker-sets-writes (ops (fn-bs-crash-select (fn-bs-ops-for-dir (fn-bs-pending m) :root) (cdr outcome) (fn-bs-unit m)))
                            (ino (fn-bs-k0s-root-target m)) (inodes (fn-bs-inodes m)))
                 (:instance fn-bs-k0s-all-marker-sets-entries (ops (fn-bs-crash-select (fn-bs-ops-for-dir (fn-bs-pending m) :root) (cdr outcome) (fn-bs-unit m)))
                            (ino (fn-bs-k0s-root-target m)) (dirs (fn-bs-dirs m))))
           :cases ((consp (fn-bs-crash-select (fn-bs-ops-for-dir (fn-bs-pending m) :root) (cdr outcome) (fn-bs-unit m))))
           :in-theory (e/d (fn-bs-fsync-dir fn-bs-fence-dir fn-bs-k0s-marker-landed fn-bs-marker-rename-dropped
                            fn-bs-k0m-with-root-entry
                            fn-bs-apply-ops-inodes-are-apply-writes fn-bs-apply-ops-dirs-are-apply-entries)
                           (fn-bs-apply-ops fn-bs-apply-entries fn-bs-apply-writes fn-bs-crash-select
                            fn-bs-k0s-root-target fn-bs-k0m-root-marker-onlyp fn-bs-k0m-has-root-marker)))
          (and stable-under-simplificationp '(:expand ((:free (i) (fn-bs-apply-writes i nil)) (:free (d) (fn-bs-apply-entries d nil)))))))

; The transaction link with every outcome, and the step-shape facts the
; general theorem uses.
(defthm fn-bs-k0s-writes-knownp-of-append
  (equal (fn-bs-writes-knownp (append a b) i)
         (and (fn-bs-writes-knownp a i) (fn-bs-writes-knownp b i)))
  :hints (("Goal" :induct (append a b) :in-theory (enable fn-bs-writes-knownp))))
(defthm fn-bs-k0s-knownp-of-append
  (equal (fn-bs-inode-list-knownp bs (append a b))
         (and (fn-bs-inode-list-knownp bs a) (fn-bs-inode-list-knownp bs b)))
  :hints (("Goal" :induct (append a b) :in-theory (enable fn-bs-inode-list-knownp))))
(defthm fn-bs-k0s-all-fencedp-of-append
  (equal (fn-bs-all-fencedp bs (append a b))
         (and (fn-bs-all-fencedp bs a) (fn-bs-all-fencedp bs b)))
  :hints (("Goal" :induct (append a b) :in-theory (enable fn-bs-all-fencedp))))
(defthm fn-bs-k0s-knownp-ignores-pending
  (equal (fn-bs-inode-list-knownp (fn-bs-make u i d p n) ys)
         (fn-bs-inode-list-knownp (fn-bs-make u i d nil n) ys))
  :hints (("Goal" :induct (len ys) :in-theory (enable fn-bs-inode-list-knownp))))
(defthm fn-bs-k0s-entry-targets-of-append
  (equal (fn-bs-pending-entry-targets (append a b))
         (append (fn-bs-pending-entry-targets a) (fn-bs-pending-entry-targets b)))
  :hints (("Goal" :induct (append a b) :in-theory (enable fn-bs-pending-entry-targets))))
(defthm fn-bs-k0s-all-fencedp-with-entry-op
  (equal (fn-bs-all-fencedp (fn-bs-make u i d (append p (list (list :set-entry dir name ino))) n) ys)
         (fn-bs-all-fencedp (fn-bs-make u i d p n) ys))
  :hints (("Goal" :induct (len ys) :in-theory (enable fn-bs-all-fencedp fn-bs-fencedp fn-bs-ops-for-ino-of-append fn-bs-ops-for-ino))))
(defthm fn-bs-k0s-durable-ignores-appended-pending
  (let ((b2 (fn-bs-make (fn-bs-unit b) (fn-bs-inodes b) (fn-bs-dirs b)
                        (append (fn-bs-pending b) ops) (fn-bs-next-ino b))))
    (and (equal (fn-bs-durable-entry b2 dir name) (fn-bs-durable-entry b dir name))
         (equal (fn-bs-durable-content b2 i) (fn-bs-durable-content b i))
         (equal (fn-bs-durable-names b2 dir) (fn-bs-durable-names b dir))
         (equal (fn-bs-durable b2) (fn-bs-durable b))
         (equal (fn-bs-durable-records b2) (fn-bs-durable-records b))
         (equal (fn-bs-durable-frontier b2) (fn-bs-durable-frontier b))))
  :hints (("Goal" :in-theory (e/d (fn-bs-durable-entry fn-bs-durable-content fn-bs-durable-names
                                   fn-bs-durable-records fn-bs-durable-frontier fn-bs-durable)
                                  (fn-bs-read-records)))))
(defthm fn-bs-k0s-all-fencedp-nil (fn-bs-all-fencedp b nil) :hints (("Goal" :in-theory (enable fn-bs-all-fencedp))))
(defthm fn-bs-k0s-knownp-nil (fn-bs-inode-list-knownp b nil) :hints (("Goal" :in-theory (enable fn-bs-inode-list-knownp))))
(defthm fn-bs-k0s-all-fencedp-cons
  (equal (fn-bs-all-fencedp b (cons x ys)) (and (fn-bs-fencedp b x) (fn-bs-all-fencedp b ys)))
  :hints (("Goal" :in-theory (enable fn-bs-all-fencedp))))
(defthm fn-bs-k0s-knownp-cons
  (equal (fn-bs-inode-list-knownp b (cons x ys))
         (and (consp (assoc-equal x (fn-bs-inodes b))) (fn-bs-inode-list-knownp b ys)))
  :hints (("Goal" :in-theory (enable fn-bs-inode-list-knownp))))
(defthm fn-bs-k0s-fencedp-appended-entry
  (equal (fn-bs-fencedp (fn-bs-make (fn-bs-unit b) (fn-bs-inodes b) (fn-bs-dirs b)
                                    (append (fn-bs-pending b) (list (list :set-entry dir name ino))) (fn-bs-next-ino b)) x)
         (fn-bs-fencedp b x))
  :hints (("Goal" :in-theory (enable fn-bs-fencedp fn-bs-ops-for-ino-of-append fn-bs-ops-for-ino))))
(defthm fn-bs-k0s-knownp-appended-pending
  (equal (fn-bs-inode-list-knownp (fn-bs-make (fn-bs-unit b) (fn-bs-inodes b) (fn-bs-dirs b)
                                              (append (fn-bs-pending b) ops) (fn-bs-next-ino b)) ys)
         (fn-bs-inode-list-knownp b ys))
  :hints (("Goal" :induct (len ys) :in-theory (e/d (fn-bs-inode-list-knownp) (fn-bs-k0s-knownp-cons fn-bs-k0s-knownp-ignores-pending)))))
(defthm fn-bs-k0s-make-of-parts
  (implies (fn-bs-shapep b)
           (equal (fn-bs-make (fn-bs-unit b) (fn-bs-inodes b) (fn-bs-dirs b) (fn-bs-pending b) (fn-bs-next-ino b)) b))
  :hints (("Goal" :expand ((len b) (len (cdr b)) (len (cddr b)) (len (cdddr b)) (len (cddddr b)) (len (cdr (cddddr b))) (len (cddr (cddddr b))))
           :in-theory (enable fn-bs-shapep fn-bs-make fn-bs-unit fn-bs-inodes fn-bs-dirs fn-bs-pending fn-bs-next-ino))))
(defthm fn-bs-k0s-entry-targets-of-one-set
  (equal (fn-bs-pending-entry-targets (list (list :set-entry dir name ino)))
         (if (member-equal dir '(:root :transactions)) (list ino) nil))
  :hints (("Goal" :in-theory (enable fn-bs-pending-entry-targets))))
(defthm fn-bs-k0s-add-pending-transaction-link-preserves-relation
  (implies (and (fn-bs-store-relation b k)
                (not (fn-bs-replay-visiblep k))
                (not (fn-bs-ops-for-dir (fn-bs-pending b) :transactions))
                (fn-bs-inop ino)
                (fn-bs-fencedp b ino)
                (consp (assoc-equal ino (fn-bs-inodes b)))
                (equal name (fn-bs-txn-name (len (fn-bs-durable-names b :transactions))))
                (fn-sf-record-present-visiblep k)
                (equal (fn-bs-durable-records b) (fn-sf-records k))
                (equal (fn-bs-record-of (fn-bs-durable b) ino) (fn-sf-record-candidate k)))
           (fn-bs-store-relation
            (fn-bs-make (fn-bs-unit b) (fn-bs-inodes b) (fn-bs-dirs b)
                        (append (fn-bs-pending b) (list (list :set-entry :transactions name ino)))
                        (fn-bs-next-ino b))
            k))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-store-relation-unfolds (bs b) (ks k))
                 (:instance fn-bs-op-listp-implies-true-listp (x (fn-bs-pending b))))
           :in-theory (e/d (fn-bs-store-relation fn-bs-pending-matches-phase fn-bs-pending-shape-okp
                            fn-bs-authority-fencedp fn-bs-authority-knownp fn-bs-authority-inode-list
                            fn-bs-ops-for-dir-of-append fn-bs-k0s-writes-knownp-of-append
                            fn-bs-writes-nonemptyp-of-append fn-bs-k0s-knownp-of-append fn-bs-k0s-all-fencedp-of-append
                            fn-bs-k0s-entry-targets-of-append fn-bs-k0s-durable-ignores-appended-pending fn-bs-k0s-all-fencedp-nil fn-bs-k0s-knownp-nil fn-bs-k0s-all-fencedp-cons fn-bs-k0s-knownp-cons fn-bs-k0s-knownp-appended-pending fn-bs-k0s-fencedp-appended-entry fn-bs-k0s-make-of-parts fn-bs-k0s-entry-targets-of-one-set fn-bs-statep fn-bs-shapep
                            fn-bs-op-listp-of-append fn-bs-writes-knownp fn-bs-writes-nonemptyp fn-bs-opp
                            fn-bs-op-listp fn-bs-entry-valuep fn-bs-namep)
                           (fn-bs-k0s-knownp-ignores-pending fn-bs-read-records fn-bs-record-of fn-sf-statep fn-bs-replay-visiblep fn-sf-crash-imagep
                            fn-bs-contiguous-namesp fn-bs-inode-list-knownp fn-bs-all-fencedp
                            fn-bs-durable fn-bs-durable-entry fn-bs-durable-names fn-bs-durable-records
                            fn-bs-durable-frontier fn-bs-durable-content
                            fn-sf-frontier-new-visiblep fn-sf-record-present-visiblep)))))
(defthm fn-bs-k0s-link-preserves-relation
  (let ((ino (fn-bs-lookup b :staging stage)))
    (implies (and (fn-bs-store-relation b k)
                  (not (fn-bs-replay-visiblep k))
                  (not (fn-bs-ops-for-dir (fn-bs-pending b) :transactions))
                  (fn-bs-fencedp b ino)
                  (consp (assoc-equal ino (fn-bs-inodes b)))
                  (equal name (fn-bs-txn-name (len (fn-bs-durable-names b :transactions))))
                  (fn-sf-record-present-visiblep k)
                  (equal (fn-bs-durable-records b) (fn-sf-records k))
                  (equal (fn-bs-record-of (fn-bs-durable b) ino) (fn-sf-record-candidate k)))
             (fn-bs-store-relation (mv-nth 1 (fn-bs-link b :staging stage :transactions name outcome)) k)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-k0s-add-pending-transaction-link-preserves-relation
                  (ino (fn-bs-lookup b :staging stage))))
           :in-theory (e/d (fn-bs-link) (fn-bs-store-relation fn-bs-lookup fn-bs-record-of fn-bs-durable
                                         fn-bs-durable-names fn-bs-durable-records fn-bs-fencedp)))))
(defthm fn-bs-k0s-observe-step
  (equal (fn-bs-step bs ks (list :observe event) outcome g c)
         (list :ok bs (fn-sf-dispatch ks event g c)))
  :hints (("Goal" :in-theory (enable fn-bs-step))))
(defthm fn-bs-k0s-syscall-step-keeps-kernel
  (implies (not (equal (car step) :observe))
           (equal (mv-nth 2 (fn-bs-step bs ks step outcome g c)) ks))
  :hints (("Goal" :in-theory (enable fn-bs-step))))
(defthm fn-bs-k0s-fsync-dir-ok-is-fence
  (equal (mv-nth 1 (fn-bs-fsync-dir s d :ok)) (fn-bs-fence-dir s d))
  :hints (("Goal" :in-theory (enable fn-bs-fsync-dir))))
(defthm fn-bs-k0s-observe-step-any
  (implies (equal (car step) :observe)
           (equal (fn-bs-step bs ks step outcome g c)
                  (list :ok bs (fn-sf-dispatch ks (nth 1 step) g c))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-bs-step) (fn-sf-dispatch)))))
