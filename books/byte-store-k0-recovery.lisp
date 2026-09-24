;; fn: K0 over the recovery program (P10, lane p10-k0-recovery).
;;
;; The last seven of the campaign's 25 cut coordinates
;; (tests/campaign/native_cuts.py RECOVERY_CUTS): recover-replayed, the five
;; recover-barrier cuts of fn-bs-recover-program, and recovery-stage-unlinked
;; of fn-bs-recover-stage-cleanup-program; and the issued-link error arm of
;; P-RECORD.
;;
;; ENTRY.  A process that recovers starts on a byte-level crash image of the
;; store it died on.  Every state the K0 books prove related at a POST cut is
;; an instance of (fn-bs-store-relation bs ks), so every theorem below takes
;; an ARBITRARY related (bs ks) and an arbitrary image with
;; (fn-bs-crash-imagep bs image).  The kernel the recovery starts from is the
;; one built from the image's scan (fn-bs-scan-store image: the config, the
;; frontier, the contiguous transaction namespace and its records):
;;
;;   fn-bs-crash-image-relates-to-recovery-entry-kernel  the :replaying seed
;;       fn-sn-observed-seed installs, over the scanned frontier and records,
;;       is related to the image.  No further hypothesis.
;;   fn-bs-host-recovery-keeps-relation-at-every-cut  THE HOST SUBJECT.  The
;;       native host reads the image (host/native/io.lisp fnn-recover,
;;       fnn-load-frontier and fnn-durable-records) and passes it to
;;       fnn-bridge-recover (io.lisp:713, called at :1478), which calls
;;       fn-store-sn-recover (host/store-node-host.lisp:145), which opens the
;;       store through fn-cpo-open-observed (:156; not fn-sn-open-observed,
;;       which K4 is stated over).  When that open succeeds, its kernel is
;;       exactly fn-bs-recovered-kernel at zero barriers
;;       (fn-bs-host-reopened-kernel-is-the-recovered-kernel), it is related to
;;       the image, and every pair of fn-bs-recover-program run from it is
;;       related; the program's first step, (:observe (:recover)), stutters on
;;       it because the host's open already performed that replay.
;;   fn-bs-scanned-recovery-keeps-relation-at-every-cut  the model's own
;;       entry: from the :replaying seed, when the scanned history is
;;       fn-sf-history-recoverablep, every pair of the run is related.  When
;;       it is not, (:recover) lands in :fault; the host faults before
;;       recover-replayed (io.lisp:1478-1480) and no cut is reached.
;;
;; Both run theorems say the byte state is the image at every pair (the five
;; fences drain nothing on a quiet store) and the last pair's kernel is :ready
;; at five barriers.  fn-bs-host-recovery-sweep-starts-related composes that
;; last pair with fn-bs-recover-sweep-keeps-relation-at-every-cut: every
;; recovery-stage-unlinked cut of the sweep is related.
;;
;; ISSUED-LINK ERROR ARM.  fn-bs-k0-record-link-error-arm-relation: whatever
;; link(2) did before reporting an errno -- nothing, or issue the entry
;; operation, which leaves the byte state of a successful link -- the byte
;; state paired with the kernel's (:record-link :error) is related.
;;
;; NOT COVERED: recovery inside a live process (host/native/admin.lisp:107
;; re-runs fnn-recover after a configuration publication on a store that is
;; not a crash image); the checkpoint phase machines; the general per-step K0.
;; No host line calls these byte-model programs; tools/native_program_check.py
;; is their tie to the host.
(in-package "ACL2")
(include-book "byte-store-keystones")
(include-book "byte-store-k0-staging")
(include-book "config-observed")

;; ---------------------------------------------------------------------------
;; 1. Authority inodes of a crash image are known.
(local
 (defun k0r-known (inodes inos)
   (if (consp inos)
       (and (consp (assoc-equal (car inos) inodes)) (k0r-known inodes (cdr inos)))
     t)))
(local
 (defthm k0r-knownp-is-known
   (equal (fn-bs-inode-list-knownp bs inos) (k0r-known (fn-bs-inodes bs) inos))
   :hints (("Goal" :in-theory (enable fn-bs-inode-list-knownp)))))
(local
 (defthm k0r-known-append
   (equal (k0r-known inodes (append a b)) (and (k0r-known inodes a) (k0r-known inodes b)))))
(local
 (defun k0r-targets (ops d)
   (cond ((atom ops) nil)
         ((and (equal (car (car ops)) :set-entry) (equal (nth 1 (car ops)) d))
          (cons (nth 3 (car ops)) (k0r-targets (cdr ops) d)))
         (t (k0r-targets (cdr ops) d)))))
(local
 (defthm k0r-targets-append
   (equal (k0r-targets (append a b) d) (append (k0r-targets a d) (k0r-targets b d)))))
(local
 (defthm k0r-assoc-put-assoc-consp
   (implies (consp (assoc-equal i al))
            (consp (assoc-equal i (fn-bs-put-assoc k v al))))
   :hints (("Goal" :in-theory (enable fn-bs-put-assoc)))))
(local
 (defthm k0r-apply-writes-keeps-keys
   (implies (consp (assoc-equal i inodes))
            (consp (assoc-equal i (fn-bs-apply-writes inodes ops))))
   :hints (("Goal" :in-theory (e/d (fn-bs-apply-writes) (fn-bs-put-assoc fn-bs-splice))))))
(local
 (defthm k0r-known-apply-writes
   (implies (k0r-known inodes xs) (k0r-known (fn-bs-apply-writes inodes ops) xs))
   :hints (("Goal" :induct (k0r-known inodes xs) :in-theory (disable fn-bs-apply-writes)))))
(local
 (defthm k0r-assoc-put-assoc
   (implies d (equal (assoc-equal d (fn-bs-put-assoc d2 x dirs))
                     (if (equal d d2) (cons d x) (assoc-equal d dirs))))
   :hints (("Goal" :in-theory (enable fn-bs-put-assoc)))))
(local
 (defthm k0r-assoc-del-assoc
   (implies n (equal (assoc-equal n (fn-bs-del-assoc k al))
                     (if (equal n k) nil (assoc-equal n al))))
   :hints (("Goal" :in-theory (enable fn-bs-del-assoc)))))
(local
 (defthm k0r-targets-of-tear-write
   (equal (k0r-targets (fn-bs-tear-write op sel i unit) d) nil)
   :hints (("Goal" :induct (fn-bs-tear-write op sel i unit)
            :in-theory (e/d (fn-bs-tear-write) (fn-bs-unit-count floor nfix fn-bs-take nthcdr))))))
(local
 (defthm k0r-entry-after-apply-entries
   (implies (and d n)
            (member-equal (cdr (assoc-equal n (cdr (assoc-equal d (fn-bs-apply-entries dirs ops)))))
                          (cons nil (cons (cdr (assoc-equal n (cdr (assoc-equal d dirs))))
                                          (k0r-targets ops d)))))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-bs-apply-entries)))))
(local
 (defthm k0r-targets-crash-select-subset
   (implies (member-equal i (k0r-targets (fn-bs-crash-select ops choices unit) d))
            (member-equal i (k0r-targets ops d)))
   :hints (("Goal" :in-theory (enable fn-bs-crash-select)))))
(local
 (defthm k0r-root-target-known
   (implies (and (k0r-known inodes (fn-bs-pending-entry-targets ops))
                 (member-equal i (k0r-targets ops :root)))
            (consp (assoc-equal i inodes)))
   :hints (("Goal" :in-theory (enable fn-bs-pending-entry-targets)))))
;; The transaction directory as a whole: every entry the image holds is an
;; entry the store held or a pending link's target.
(local
 (defthm k0r-known-strip-cdrs-put-assoc
   (implies (and (k0r-known inodes (strip-cdrs al)) (consp (assoc-equal v inodes)))
            (k0r-known inodes (strip-cdrs (fn-bs-put-assoc k v al))))
   :hints (("Goal" :in-theory (enable fn-bs-put-assoc)))))
(local
 (defthm k0r-known-strip-cdrs-del-assoc
   (implies (k0r-known inodes (strip-cdrs al))
            (k0r-known inodes (strip-cdrs (fn-bs-del-assoc k al))))
   :hints (("Goal" :in-theory (enable fn-bs-del-assoc)))))
(local
 (defthm k0r-known-apply-entries
   (implies (and d
                 (k0r-known inodes (strip-cdrs (cdr (assoc-equal d dirs))))
                 (k0r-known inodes (k0r-targets ops d)))
            (k0r-known inodes (strip-cdrs (cdr (assoc-equal d (fn-bs-apply-entries dirs ops))))))
   :hints (("Goal" :in-theory (enable fn-bs-apply-entries)))))
(local
 (defthm k0r-known-targets-crash-select
   (implies (k0r-known inodes (k0r-targets ops d))
            (k0r-known inodes (k0r-targets (fn-bs-crash-select ops choices unit) d)))
   :hints (("Goal" :in-theory (enable fn-bs-crash-select)))))
(local
 (defthm k0r-transaction-targets-are-entry-targets
   (implies (k0r-known inodes (fn-bs-pending-entry-targets ops))
            (k0r-known inodes (k0r-targets ops :transactions)))
   :hints (("Goal" :in-theory (enable fn-bs-pending-entry-targets)))))
(local
 (defthm k0r-crash-authority-known
   (implies (and (fn-bs-authority-knownp s)
                 (fn-bs-inop (fn-bs-durable-entry (fn-bs-crash s ch) :root *fn-bs-scan-config-name*))
                 (fn-bs-inop (fn-bs-durable-entry (fn-bs-crash s ch) :root *fn-bs-scan-frontier-name*)))
            (fn-bs-authority-knownp (fn-bs-crash s ch)))
   :hints (("Goal"
            :use ((:instance k0r-entry-after-apply-entries (d :root) (n *fn-bs-scan-config-name*)
                   (dirs (fn-bs-dirs s)) (ops (fn-bs-crash-select (fn-bs-pending s) ch (fn-bs-unit s))))
                  (:instance k0r-entry-after-apply-entries (d :root) (n *fn-bs-scan-frontier-name*)
                   (dirs (fn-bs-dirs s)) (ops (fn-bs-crash-select (fn-bs-pending s) ch (fn-bs-unit s))))
                  (:instance k0r-targets-crash-select-subset (d :root) (ops (fn-bs-pending s)) (choices ch)
                   (unit (fn-bs-unit s))
                   (i (fn-bs-durable-entry (fn-bs-crash s ch) :root *fn-bs-scan-config-name*)))
                  (:instance k0r-targets-crash-select-subset (d :root) (ops (fn-bs-pending s)) (choices ch)
                   (unit (fn-bs-unit s))
                   (i (fn-bs-durable-entry (fn-bs-crash s ch) :root *fn-bs-scan-frontier-name*))))
            :in-theory (e/d (fn-bs-authority-knownp fn-bs-authority-inode-list fn-bs-crash
                             fn-bs-durable-entry fn-bs-apply-ops-inodes-are-apply-writes
                             fn-bs-apply-ops-dirs-are-apply-entries)
                            (fn-bs-apply-ops fn-bs-apply-entries fn-bs-apply-writes fn-bs-crash-select
                             k0r-targets-crash-select-subset))))))
(local
 (defthm k0r-crash-image-authority-known
   (implies (and (fn-bs-authority-knownp bs) (fn-bs-crash-imagep bs image)
                 (fn-bs-inop (fn-bs-durable-entry image :root *fn-bs-scan-config-name*))
                 (fn-bs-inop (fn-bs-durable-entry image :root *fn-bs-scan-frontier-name*)))
            (fn-bs-authority-knownp image))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance k0r-crash-authority-known (s bs) (ch (fn-bs-crash-imagep-witness bs image))))
            :in-theory (union-theories '(fn-bs-crash-imagep) (theory 'minimal-theory))))))
(local
 (defthm k0r-crash-image-authority-entries
   (implies (and (fn-bs-store-relation bs ks) (fn-bs-crash-imagep bs image))
            (and (fn-bs-inop (fn-bs-durable-entry image :root *fn-bs-scan-config-name*))
                 (fn-bs-inop (fn-bs-durable-entry image :root *fn-bs-scan-frontier-name*))))
   :rule-classes nil
   :hints (("Goal"
            :use (fn-bs-store-crash-image-scans
                  (:instance fn-bs-crash-image-is-quiet (s bs))
                  (:instance fn-bs-scan-okp-unfolds (s image))
                  (:instance fn-bs-quiet-lookup-is-durable-entry (s image) (dir :root) (name *fn-bs-scan-config-name*))
                  (:instance fn-bs-quiet-lookup-is-durable-entry (s image) (dir :root) (name *fn-bs-scan-frontier-name*)))
            :in-theory (theory 'minimal-theory)))))
(local
 (defthm k0r-relation-authority-known
   (implies (fn-bs-store-relation bs ks) (fn-bs-authority-knownp bs))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn-bs-store-relation)
                                   (fn-bs-authority-knownp fn-bs-statep fn-sf-statep
                                    fn-bs-replay-matches-scan fn-bs-pending-matches-phase
                                    fn-sf-crash-imagep fn-bs-authority-fencedp
                                    fn-bs-durable-records))))))

;; ---------------------------------------------------------------------------
;; 2. A quiet store whose scan succeeds is related to every kernel that holds
;; exactly the scanned frontier and records.
(local
 (defthm k0r-true-list-of-len-one
   (implies (and (true-listp x) (equal (len x) 1)) (equal (list (car x)) x))
   :rule-classes nil))
(local
 (defthm k0r-quiet-durable-is-self
   (implies (and (fn-bs-statep s) (equal (fn-bs-pending s) nil))
            (equal (fn-bs-durable s) s))
   :hints (("Goal" :use ((:instance k0r-true-list-of-len-one (x (cdr (cddddr s)))))
            :in-theory (enable fn-bs-durable fn-bs-make fn-bs-statep fn-bs-shapep
                               fn-bs-unit fn-bs-inodes fn-bs-dirs fn-bs-pending fn-bs-next-ino)))))
(local
 (defthm k0r-quiet-all-fenced
   (implies (equal (fn-bs-pending s) nil) (fn-bs-all-fencedp s xs))
   :hints (("Goal" :in-theory (enable fn-bs-all-fencedp fn-bs-fencedp fn-bs-ops-for-ino)))))
(local
 (defthm k0r-quiet-scan-config
   (implies (fn-bs-scan-okp (fn-bs-scan-store s))
            (fn-bs-config-okp (fn-bs-content s (fn-bs-lookup s :root *fn-bs-scan-config-name*))))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-bs-scan-store fn-bs-scan-okp)))))
(local
 (defthm k0r-quiet-scan-names
   (implies (fn-bs-scan-okp (fn-bs-scan-store s))
            (fn-bs-contiguous-namesp (fn-bs-names s :transactions) (len (fn-bs-names s :transactions))))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable fn-bs-scan-store fn-bs-scan-okp)))))

(defthm fn-bs-quiet-scanned-store-is-related-to-a-replay-kernel
  (implies (and (fn-bs-statep img)
                (equal (fn-bs-pending img) nil)
                (fn-bs-scan-okp (fn-bs-scan-store img))
                (fn-bs-authority-knownp img)
                (fn-sf-statep k)
                (fn-bs-replay-visiblep k)
                (equal (fn-sf-frontier k) (fn-bs-scan-frontier (fn-bs-scan-store img)))
                (equal (fn-sf-records k) (fn-bs-scan-records (fn-bs-scan-store img)))
                (equal (fn-sf-successes k) nil))
           (fn-bs-store-relation img k))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-bs-scan-okp-unfolds (s img))
                 (:instance k0r-quiet-scan-config (s img))
                 (:instance k0r-quiet-scan-names (s img)))
           :in-theory (e/d (fn-bs-store-relation fn-bs-replay-matches-scan fn-bs-pending-shape-okp
                            fn-bs-authority-fencedp fn-bs-durable-records
                            fn-bs-durable-names fn-bs-ops-for-dir
                            fn-bs-quiet-lookup-is-durable-entry fn-bs-quiet-content-is-durable-content
                            fn-bs-quiet-names-are-durable-names)
                           (fn-bs-statep fn-sf-statep fn-bs-scan-store fn-bs-scan-okp
                            fn-bs-read-records fn-bs-authority-knownp fn-bs-durable
                            fn-bs-contiguous-namesp fn-bs-replay-visiblep
                            fn-bs-scan-frontier fn-bs-scan-records fn-bs-lookup fn-bs-content fn-bs-names)))))

(defthm fn-bs-quiet-scanned-store-is-related-to-a-ready-kernel
  (implies (and (fn-bs-statep img)
                (equal (fn-bs-pending img) nil)
                (fn-bs-scan-okp (fn-bs-scan-store img))
                (fn-bs-authority-knownp img)
                (fn-sf-statep k)
                (not (fn-bs-replay-visiblep k))
                (equal (fn-sf-frontier k) (fn-bs-scan-frontier (fn-bs-scan-store img)))
                (equal (fn-sf-records k) (fn-bs-scan-records (fn-bs-scan-store img))))
           (fn-bs-store-relation img k))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-bs-scan-okp-unfolds (s img))
                 (:instance k0r-quiet-scan-config (s img))
                 (:instance k0r-quiet-scan-names (s img)))
           :in-theory (e/d (fn-bs-store-relation fn-bs-pending-matches-phase fn-bs-pending-shape-okp
                            fn-sf-crash-imagep fn-bs-durable-frontier
                            fn-bs-authority-fencedp fn-bs-durable-records
                            fn-bs-durable-names fn-bs-ops-for-dir
                            fn-bs-quiet-lookup-is-durable-entry fn-bs-quiet-content-is-durable-content
                            fn-bs-quiet-names-are-durable-names)
                           (fn-bs-statep fn-sf-statep fn-bs-scan-store fn-bs-scan-okp
                            fn-bs-read-records fn-bs-authority-knownp fn-bs-durable
                            fn-bs-contiguous-namesp fn-bs-replay-visiblep
                            fn-bs-scan-frontier fn-bs-scan-records fn-bs-lookup fn-bs-content fn-bs-names)))))

;; ---------------------------------------------------------------------------
;; 3. The entry theorem.
;; The kernel fn-sn-observed-seed installs for the scanned image
;; (store-observed.lisp: (fn-sf-make :replaying frontier nil records nil nil
;; nil 0)); the input of the model's (:observe (:recover)).
(defun fn-bs-recovery-entry-kernel (image)
  (declare (xargs :guard t :verify-guards nil))
  (let ((scan (fn-bs-scan-store image)))
    (fn-sf-make :replaying (fn-bs-scan-frontier scan) nil (fn-bs-scan-records scan)
                nil nil nil 0)))
(local
 (defthm k0r-replay-seed-is-state
   (implies (and (fn-record-uint32p f) (fn-sf-record-listp r 0 0 f))
            (fn-sf-statep (fn-sf-make :replaying f nil r nil nil nil 0)))
   :hints (("Goal" :in-theory (enable fn-sf-statep fn-sf-phase-shapep)))))

(defthm fn-bs-crash-image-relates-to-recovery-entry-kernel
  (implies (and (fn-bs-store-relation bs ks) (fn-bs-crash-imagep bs image))
           (fn-bs-store-relation image (fn-bs-recovery-entry-kernel image)))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-bs-store-crash-image-scans
                 (:instance fn-bs-crash-image-is-quiet (s bs))
                 k0r-crash-image-authority-entries
                 (:instance k0r-crash-image-authority-known (bs bs))
                 k0r-relation-authority-known
                 fn-bs-store-crash-image-is-kernel-admissible
                 (:instance fn-bs-crash-imagep-preserves-statep (s bs))
                 (:instance fn-sf-recovery-admissible-image-facts (s ks)
                  (frontier (fn-bs-scan-frontier (fn-bs-scan-store image)))
                  (records (fn-bs-scan-records (fn-bs-scan-store image))))
                 (:instance fn-bs-quiet-scanned-store-is-related-to-a-replay-kernel
                  (img image) (k (fn-bs-recovery-entry-kernel image))))
           :in-theory (e/d (fn-bs-recovery-entry-kernel fn-bs-replay-visiblep
                            fn-bs-quiet-lookup-is-durable-entry)
                           (fn-bs-store-relation
                            fn-bs-crash-imagep fn-sf-statep fn-bs-statep fn-bs-scan-store fn-bs-scan-okp
                            fn-bs-scan-frontier fn-bs-scan-records fn-sf-record-listp
                            fn-bs-replay-matches-scan fn-bs-pending-matches-phase fn-sf-crash-imagep
                            fn-bs-authority-knownp fn-bs-authority-fencedp fn-bs-durable-records
                            fn-sf-recovery-crash-imagep fn-bs-contiguous-namesp)))))

(defthm fn-bs-crash-image-recovery-facts
  (implies (and (fn-bs-store-relation bs ks) (fn-bs-crash-imagep bs image))
           (and (fn-bs-statep image)
                (equal (fn-bs-pending image) nil)
                (fn-bs-scan-okp (fn-bs-scan-store image))
                (fn-bs-authority-knownp image)
                (fn-record-uint32p (fn-bs-scan-frontier (fn-bs-scan-store image)))
                (fn-sf-record-listp (fn-bs-scan-records (fn-bs-scan-store image)) 0 0
                                    (fn-bs-scan-frontier (fn-bs-scan-store image)))))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-bs-store-crash-image-scans
                 (:instance fn-bs-crash-image-is-quiet (s bs))
                 k0r-crash-image-authority-entries
                 k0r-crash-image-authority-known
                 fn-bs-store-crash-image-is-kernel-admissible
                 fn-bs-store-relation-unfolds
                 k0r-relation-authority-known
                 (:instance fn-bs-crash-imagep-preserves-statep (s bs))
                 (:instance fn-sf-recovery-admissible-image-facts (s ks)
                  (frontier (fn-bs-scan-frontier (fn-bs-scan-store image)))
                  (records (fn-bs-scan-records (fn-bs-scan-store image)))))
           :in-theory (theory 'minimal-theory))))

;; ---------------------------------------------------------------------------
;; 4. The recovery program from a quiet image: the byte state never moves,
;; the kernel counts its barriers.
(defun fn-bs-recovered-kernel (frontier records n)
  (declare (xargs :guard t :verify-guards nil))
  (fn-sf-make (if (equal n *fn-sf-recovery-barrier-count*) :ready :recovering)
              frontier nil records nil nil nil n))
(local
 (defthm k0r-recovered-kernel-is-state
   (implies (and (fn-record-uint32p f) (fn-sf-record-listp r 0 0 f)
                 (natp n) (<= n *fn-sf-recovery-barrier-count*))
            (fn-sf-statep (fn-bs-recovered-kernel f r n)))
   :hints (("Goal" :in-theory (enable fn-sf-statep fn-sf-phase-shapep fn-bs-recovered-kernel)))))
(local
 (defthm k0r-recovered-kernel-barrier
   (implies (and (fn-record-uint32p f) (fn-sf-record-listp r 0 0 f)
                 (natp n) (< n *fn-sf-recovery-barrier-count*))
            (equal (fn-sf-dispatch (fn-bs-recovered-kernel f r n) '(:recovery-barrier :ok) g c)
                   (fn-bs-recovered-kernel f r (1+ n))))
   :hints (("Goal" :use k0r-recovered-kernel-is-state
            :in-theory (e/d (fn-sf-dispatch fn-sf-recovery-barrier fn-bs-recovered-kernel)
                            (fn-sf-statep k0r-recovered-kernel-is-state))))))
(defthm fn-bs-recovered-kernel-recover-stutters
  (equal (fn-sf-dispatch (fn-bs-recovered-kernel f r 0) '(:recover) g c)
         (fn-bs-recovered-kernel f r 0))
  :hints (("Goal" :in-theory (enable fn-sf-dispatch fn-sf-recover fn-bs-recovered-kernel))))
(local
 (defthm k0r-quiet-fence-file
   (implies (and (fn-bs-statep s) (equal (fn-bs-pending s) nil))
            (equal (fn-bs-fence-file s ino) s))
   :hints (("Goal" :use k0r-quiet-durable-is-self
            :in-theory (e/d (fn-bs-fence-file fn-bs-durable fn-bs-ops-for-ino fn-bs-ops-not-for-ino
                             fn-bs-apply-ops)
                            (k0r-quiet-durable-is-self fn-bs-statep))))))
(local
 (defthm k0r-quiet-fence-dir
   (implies (and (fn-bs-statep s) (equal (fn-bs-pending s) nil))
            (equal (fn-bs-fence-dir s dir) s))
   :hints (("Goal" :use k0r-quiet-durable-is-self
            :in-theory (e/d (fn-bs-fence-dir fn-bs-durable fn-bs-ops-for-dir fn-bs-ops-not-for-dir
                             fn-bs-apply-ops)
                            (k0r-quiet-durable-is-self fn-bs-statep))))))

;; Indices: 0 (:recover), 1 recover-replayed, then per barrier fsync, observe,
;; cut; the five recover-barrier cuts are pairs 4, 7, 10, 13 and 16.
(defthm fn-bs-recover-program-run-from-a-quiet-image
  (implies (and (fn-bs-statep image) (equal (fn-bs-pending image) nil)
                (fn-record-uint32p f) (fn-sf-record-listp r 0 0 f)
                (equal (fn-sf-dispatch k '(:recover) groups capacity)
                       (fn-bs-recovered-kernel f r 0)))
           (equal (fn-bs-run image k (fn-bs-recover-program) nil groups capacity)
                  (list (cons image (fn-bs-recovered-kernel f r 0))
                        (cons image (fn-bs-recovered-kernel f r 0))
                        (cons image (fn-bs-recovered-kernel f r 0))
                        (cons image (fn-bs-recovered-kernel f r 1))
                        (cons image (fn-bs-recovered-kernel f r 1))
                        (cons image (fn-bs-recovered-kernel f r 1))
                        (cons image (fn-bs-recovered-kernel f r 2))
                        (cons image (fn-bs-recovered-kernel f r 2))
                        (cons image (fn-bs-recovered-kernel f r 2))
                        (cons image (fn-bs-recovered-kernel f r 3))
                        (cons image (fn-bs-recovered-kernel f r 3))
                        (cons image (fn-bs-recovered-kernel f r 3))
                        (cons image (fn-bs-recovered-kernel f r 4))
                        (cons image (fn-bs-recovered-kernel f r 4))
                        (cons image (fn-bs-recovered-kernel f r 4))
                        (cons image (fn-bs-recovered-kernel f r 5))
                        (cons image (fn-bs-recovered-kernel f r 5)))))
  :rule-classes nil
  :hints (("Goal" :expand ((:free (b k s o) (fn-bs-run b k s o groups capacity)))
           :in-theory (e/d (fn-bs-recover-program fn-bs-step fn-bs-fsync-file fn-bs-fsync-dir)
                           (fn-bs-fence-file fn-bs-fence-dir fn-sf-dispatch fn-bs-recovered-kernel
                            fn-bs-statep fn-bs-lookup fn-sf-record-listp)))))

(defthm fn-bs-quiet-scanned-store-is-related-to-every-recovered-kernel
  (implies (and (fn-bs-statep img)
                (equal (fn-bs-pending img) nil)
                (fn-bs-scan-okp (fn-bs-scan-store img))
                (fn-bs-authority-knownp img)
                (fn-record-uint32p (fn-bs-scan-frontier (fn-bs-scan-store img)))
                (fn-sf-record-listp (fn-bs-scan-records (fn-bs-scan-store img)) 0 0
                                    (fn-bs-scan-frontier (fn-bs-scan-store img)))
                (natp n) (<= n *fn-sf-recovery-barrier-count*))
           (fn-bs-store-relation img (fn-bs-recovered-kernel (fn-bs-scan-frontier (fn-bs-scan-store img))
                                                             (fn-bs-scan-records (fn-bs-scan-store img))
                                                             n)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance k0r-recovered-kernel-is-state
                  (f (fn-bs-scan-frontier (fn-bs-scan-store img)))
                  (r (fn-bs-scan-records (fn-bs-scan-store img))))
                 (:instance fn-bs-quiet-scanned-store-is-related-to-a-replay-kernel
                  (k (fn-bs-recovered-kernel (fn-bs-scan-frontier (fn-bs-scan-store img))
                                             (fn-bs-scan-records (fn-bs-scan-store img)) n)))
                 (:instance fn-bs-quiet-scanned-store-is-related-to-a-ready-kernel
                  (k (fn-bs-recovered-kernel (fn-bs-scan-frontier (fn-bs-scan-store img))
                                             (fn-bs-scan-records (fn-bs-scan-store img)) n))))
           :in-theory (e/d (fn-bs-recovered-kernel fn-bs-replay-visiblep)
                           (fn-bs-statep fn-sf-statep fn-bs-scan-store fn-bs-scan-okp fn-sf-record-listp
                            fn-bs-scan-frontier fn-bs-scan-records fn-bs-store-relation
                            fn-bs-authority-knownp k0r-recovered-kernel-is-state)))))

;; ---------------------------------------------------------------------------
;; 5. The six recovery-program cuts, from any kernel whose (:recover)
;; observation lands on the recovered kernel at zero barriers.
(defthm fn-bs-recover-program-keeps-relation-at-every-cut
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-crash-imagep bs image)
                (equal (fn-sf-dispatch k '(:recover) groups capacity)
                       (fn-bs-recovered-kernel (fn-bs-scan-frontier (fn-bs-scan-store image))
                                               (fn-bs-scan-records (fn-bs-scan-store image)) 0)))
           (let ((run (fn-bs-run image k (fn-bs-recover-program) nil groups capacity)))
             (and (fn-bs-run-relatedp run)
                  (equal (len run) 17)
                  (equal (car (nth 16 run)) image)
                  (equal (cdr (nth 16 run))
                         (fn-bs-recovered-kernel (fn-bs-scan-frontier (fn-bs-scan-store image))
                                                 (fn-bs-scan-records (fn-bs-scan-store image))
                                                 *fn-sf-recovery-barrier-count*)))))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-bs-crash-image-recovery-facts
                 (:instance fn-bs-recover-program-run-from-a-quiet-image
                  (f (fn-bs-scan-frontier (fn-bs-scan-store image)))
                  (r (fn-bs-scan-records (fn-bs-scan-store image))))
                 (:instance fn-bs-quiet-scanned-store-is-related-to-every-recovered-kernel (img image) (n 0))
                 (:instance fn-bs-quiet-scanned-store-is-related-to-every-recovered-kernel (img image) (n 1))
                 (:instance fn-bs-quiet-scanned-store-is-related-to-every-recovered-kernel (img image) (n 2))
                 (:instance fn-bs-quiet-scanned-store-is-related-to-every-recovered-kernel (img image) (n 3))
                 (:instance fn-bs-quiet-scanned-store-is-related-to-every-recovered-kernel (img image) (n 4))
                 (:instance fn-bs-quiet-scanned-store-is-related-to-every-recovered-kernel (img image) (n 5)))
           :in-theory (e/d (fn-bs-run-relatedp)
                           (fn-bs-run fn-bs-store-relation fn-bs-recovered-kernel fn-bs-statep
                            fn-bs-scan-store fn-bs-scan-okp fn-bs-scan-frontier fn-bs-scan-records
                            fn-sf-record-listp fn-bs-authority-knownp fn-sf-dispatch fn-bs-crash-imagep)))))

;; The model's entry: the :replaying seed over a recoverable scanned history.
(defthm fn-bs-recovery-entry-kernel-recovers
  (implies (and (fn-record-uint32p (fn-bs-scan-frontier (fn-bs-scan-store image)))
                (fn-sf-record-listp (fn-bs-scan-records (fn-bs-scan-store image)) 0 0
                                    (fn-bs-scan-frontier (fn-bs-scan-store image)))
                (fn-sf-history-recoverablep groups capacity
                                            (fn-bs-scan-records (fn-bs-scan-store image))
                                            (fn-bs-scan-frontier (fn-bs-scan-store image))))
           (equal (fn-sf-dispatch (fn-bs-recovery-entry-kernel image) '(:recover) groups capacity)
                  (fn-bs-recovered-kernel (fn-bs-scan-frontier (fn-bs-scan-store image))
                                          (fn-bs-scan-records (fn-bs-scan-store image)) 0)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance k0r-replay-seed-is-state
                  (f (fn-bs-scan-frontier (fn-bs-scan-store image)))
                  (r (fn-bs-scan-records (fn-bs-scan-store image)))))
           :in-theory (e/d (fn-sf-dispatch fn-sf-recover fn-bs-recovery-entry-kernel fn-bs-recovered-kernel)
                           (fn-sf-statep fn-sf-history-recoverablep fn-bs-scan-store
                            fn-bs-scan-frontier fn-bs-scan-records fn-sf-record-listp)))))

(defthm fn-bs-scanned-recovery-keeps-relation-at-every-cut
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-crash-imagep bs image)
                (fn-sf-history-recoverablep groups capacity
                                            (fn-bs-scan-records (fn-bs-scan-store image))
                                            (fn-bs-scan-frontier (fn-bs-scan-store image))))
           (let ((run (fn-bs-run image (fn-bs-recovery-entry-kernel image)
                                 (fn-bs-recover-program) nil groups capacity)))
             (and (fn-bs-store-relation image (fn-bs-recovery-entry-kernel image))
                  (fn-bs-run-relatedp run)
                  (equal (len run) 17)
                  (equal (car (nth 16 run)) image)
                  (equal (fn-sf-phase (cdr (nth 16 run))) :ready))))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-bs-crash-image-relates-to-recovery-entry-kernel
                 fn-bs-crash-image-recovery-facts
                 fn-bs-recovery-entry-kernel-recovers
                 (:instance fn-bs-recover-program-keeps-relation-at-every-cut
                  (k (fn-bs-recovery-entry-kernel image))))
           :in-theory (union-theories '(fn-bs-recovered-kernel fn-sf-phase-of-fn-sf-make)
                                      (theory 'minimal-theory)))))

;; The host subject: the kernel fn-cpo-open-observed returns.
(defthm fn-bs-host-reopened-kernel-is-the-recovered-kernel
  (implies (fn-sn-open-okp (fn-cpo-open-observed configs frontier events))
           (equal (fn-sn-files (fn-sn-open-state (fn-cpo-open-observed configs frontier events)))
                  (fn-bs-recovered-kernel frontier events 0)))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (e/d (fn-cpo-open-observed fn-cpo-install fn-bs-recovered-kernel
                 fn-sn-update-replayed fn-sn-open-okp fn-cnode-domain)
                (fn-cpr-replay fn-cpr-loop fn-replay-identity
                 fn-replay-identity-loop fn-stx-index-of-store
                 fn-sn-statep fn-cnode-statep fn-sn-observed-seed
                 fn-replay-advance-txid fn-sn-with-configuration)))))

(defthm fn-bs-host-recovery-keeps-relation-at-every-cut
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-crash-imagep bs image)
                (fn-sn-open-okp (fn-cpo-open-observed configs
                                                      (fn-bs-scan-frontier (fn-bs-scan-store image))
                                                      (fn-bs-scan-records (fn-bs-scan-store image)))))
           (let* ((host (fn-sn-files (fn-sn-open-state
                                      (fn-cpo-open-observed configs
                                                            (fn-bs-scan-frontier (fn-bs-scan-store image))
                                                            (fn-bs-scan-records (fn-bs-scan-store image))))))
                  (run (fn-bs-run image host (fn-bs-recover-program) nil groups capacity)))
             (and (fn-bs-store-relation image host)
                  (fn-bs-run-relatedp run)
                  (equal (len run) 17)
                  (equal (car (nth 16 run)) image)
                  (equal (fn-sf-phase (cdr (nth 16 run))) :ready))))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-bs-crash-image-recovery-facts
                 (:instance fn-bs-host-reopened-kernel-is-the-recovered-kernel
                  (frontier (fn-bs-scan-frontier (fn-bs-scan-store image)))
                  (events (fn-bs-scan-records (fn-bs-scan-store image))))
                 (:instance fn-bs-recovered-kernel-recover-stutters
                  (f (fn-bs-scan-frontier (fn-bs-scan-store image)))
                  (r (fn-bs-scan-records (fn-bs-scan-store image))) (g groups) (c capacity))
                 (:instance fn-bs-quiet-scanned-store-is-related-to-every-recovered-kernel (img image) (n 0))
                 (:instance fn-bs-recover-program-keeps-relation-at-every-cut
                  (k (fn-bs-recovered-kernel (fn-bs-scan-frontier (fn-bs-scan-store image))
                                             (fn-bs-scan-records (fn-bs-scan-store image)) 0))))
           :in-theory (union-theories '(fn-bs-recovered-kernel fn-sf-phase-of-fn-sf-make
                                        (:executable-counterpart natp) (:executable-counterpart <)
                                        (:executable-counterpart equal) (:executable-counterpart if))
                                      (theory 'minimal-theory)))))

;; ---------------------------------------------------------------------------
;; 6. recovery-stage-unlinked: the sweep starts from the last pair.
(local
 (defthm k0r-run-relatedp-nth
   (implies (and (fn-bs-run-relatedp pairs) (natp k) (< k (len pairs)))
            (fn-bs-store-relation (car (nth k pairs)) (cdr (nth k pairs))))
   :hints (("Goal" :in-theory (e/d (fn-bs-run-relatedp nth) (fn-bs-store-relation))))))

(defthm fn-bs-host-recovery-sweep-starts-related
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-crash-imagep bs image)
                (fn-sn-open-okp (fn-cpo-open-observed configs
                                                      (fn-bs-scan-frontier (fn-bs-scan-store image))
                                                      (fn-bs-scan-records (fn-bs-scan-store image)))))
           (let* ((host (fn-sn-files (fn-sn-open-state
                                      (fn-cpo-open-observed configs
                                                            (fn-bs-scan-frontier (fn-bs-scan-store image))
                                                            (fn-bs-scan-records (fn-bs-scan-store image))))))
                  (last (nth 16 (fn-bs-run image host (fn-bs-recover-program) nil groups capacity))))
             (and (fn-bs-store-relation (car last) (cdr last))
                  (fn-bs-sweep-run-okp
                   (fn-bs-run (car last) (cdr last) (fn-bs-recover-sweep-program names) outcomes
                              groups capacity)
                   (cdr last) (fn-bs-scan-store (car last))))))
  :rule-classes nil
  :hints (("Goal"
           :use (fn-bs-host-recovery-keeps-relation-at-every-cut
                 (:instance k0r-run-relatedp-nth (k 16)
                  (pairs (fn-bs-run image
                                    (fn-sn-files (fn-sn-open-state
                                                  (fn-cpo-open-observed configs
                                                                        (fn-bs-scan-frontier (fn-bs-scan-store image))
                                                                        (fn-bs-scan-records (fn-bs-scan-store image)))))
                                    (fn-bs-recover-program) nil groups capacity)))
                 (:instance fn-bs-recover-sweep-keeps-relation-at-every-cut
                  (bs (car (nth 16 (fn-bs-run image
                                              (fn-sn-files (fn-sn-open-state
                                                            (fn-cpo-open-observed configs
                                                                                  (fn-bs-scan-frontier (fn-bs-scan-store image))
                                                                                  (fn-bs-scan-records (fn-bs-scan-store image)))))
                                              (fn-bs-recover-program) nil groups capacity))))
                  (ks (cdr (nth 16 (fn-bs-run image
                                              (fn-sn-files (fn-sn-open-state
                                                            (fn-cpo-open-observed configs
                                                                                  (fn-bs-scan-frontier (fn-bs-scan-store image))
                                                                                  (fn-bs-scan-records (fn-bs-scan-store image)))))
                                              (fn-bs-recover-program) nil groups capacity))))))
           :in-theory (union-theories '((:executable-counterpart natp) (:executable-counterpart <))
                                      (theory 'minimal-theory)))))

;; ---------------------------------------------------------------------------
;; 7. The issued-link error arm of P-RECORD.  link(2) at 941 returns an errno
;; after the entry operation was issued; the host observes
;; (:record-link :error) and raises StoreIndeterminate.
(defthm fn-bs-issued-link-bytes-are-the-linked-bytes
  (implies (equal (cdr outcome) :issued)
           (equal (mv-nth 1 (fn-bs-link bs sdir sname ddir dname outcome))
                  (mv-nth 1 (fn-bs-link bs sdir sname ddir dname :ok))))
  :hints (("Goal" :in-theory (enable fn-bs-link))))
(local
 (defthm k0r-record-run-link-step
   (implies (consp (nth 10 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity)))
            (let ((run (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity)))
              (and (equal (car (nth 10 run))
                          (mv-nth 1 (fn-bs-link (car (nth 6 run)) :staging stage :transactions name :ok)))
                   (equal (cdr (nth 6 run)) (fn-sf-record-file-result ks :ok)))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :expand ((:free (b k s o) (fn-bs-run b k s o groups capacity)))
            :in-theory (e/d (fn-bs-record-program fn-bs-step fn-sf-dispatch)
                            (fn-bs-create fn-bs-write fn-bs-fsync-file fn-bs-fsync-dir
                             fn-bs-link fn-bs-unlink fn-bs-lookup
                             fn-sf-record-file-result fn-sf-record-link-result
                             fn-sf-record-dir-result))))))
(local
 (defthm k0r-record-link-error-kernel-transport-facts
   (implies (and (fn-sf-statep ks) (fn-bs-record-inputp ks stage name frame))
            (let* ((k6 (fn-sf-record-file-result ks :ok))
                   (ok (fn-sf-record-link-result k6 :ok))
                   (err (fn-sf-record-link-result k6 :error)))
              (and (fn-sf-statep err)
                   (not (fn-bs-replay-visiblep ok))
                   (not (fn-bs-replay-visiblep err))
                   (equal (fn-sf-frontier err) (fn-sf-frontier ok))
                   (equal (fn-sf-records err) (fn-sf-records ok))
                   (equal (fn-sf-record-candidate err) (fn-sf-record-candidate ok))
                   (equal (fn-sf-frontier-candidate err) (fn-sf-frontier-candidate ok))
                   (iff (fn-sf-frontier-new-visiblep err) (fn-sf-frontier-new-visiblep ok))
                   (iff (fn-sf-record-present-visiblep err) (fn-sf-record-present-visiblep ok)))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn-sf-record-file-result-preserves-state (s ks) (result :ok))
                         (:instance fn-sf-record-link-result-preserves-state
                          (s (fn-sf-record-file-result ks :ok)) (result :error)))
            :in-theory (e/d (fn-bs-record-inputp fn-sf-record-link-result fn-sf-record-file-result
                             fn-bs-replay-visiblep fn-sf-frontier-new-visiblep fn-sf-record-present-visiblep)
                            (fn-sf-statep fn-sf-record-file-result-preserves-state
                             fn-sf-record-link-result-preserves-state))))))

(local
 (defthm fn-bs-k0-record-issued-link-error-arm-relation
   (implies (and (fn-bs-store-relation bs ks)
                 (fn-bs-record-inputp ks stage name frame)
                 (not (fn-bs-lookup bs :staging stage))
                 (equal (cdr outcome) :issued))
            (let ((p6 (nth 6 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity))))
              (fn-bs-store-relation
               (mv-nth 1 (fn-bs-link (car p6) :staging stage :transactions name outcome))
               (fn-sf-record-link-result (cdr p6) :error))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :use (fn-bs-k0-record-attempted-cut-establishes-relation
                  fn-bs-k0-record-run-linked-shape
                  k0r-record-run-link-step
                  fn-bs-store-relation-unfolds
                  k0r-record-link-error-kernel-transport-facts
                  (:instance fn-bs-k0c-related-pair-is-consp
                   (x (nth 10 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity))))
                  (:instance fn-bs-issued-link-bytes-are-the-linked-bytes
                   (bs (car (nth 6 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity))))
                   (sdir :staging) (sname stage) (ddir :transactions) (dname name))
                  (:instance fn-bs-k0-kernel-transport
                   (bs (car (nth 10 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity))))
                   (ks (fn-sf-record-link-result (fn-sf-record-file-result ks :ok) :ok))
                   (ks2 (fn-sf-record-link-result (fn-sf-record-file-result ks :ok) :error))))
            :in-theory (union-theories '(car-cons cdr-cons) (theory 'minimal-theory))))))

(defthm fn-bs-link-bytes-are-unchanged-or-linked
  (or (equal (mv-nth 1 (fn-bs-link bs sdir sname ddir dname outcome)) bs)
      (equal (mv-nth 1 (fn-bs-link bs sdir sname ddir dname outcome))
             (mv-nth 1 (fn-bs-link bs sdir sname ddir dname :ok))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-bs-link))))

;; Every outcome of the link at 941 -- refused before issue (the byte state
;; of pair 6, lane p10-k0-b's arm) or issued and then reported as an errno
;; (the byte state of a successful link) -- with the kernel's
;; (:record-link :error) observation is related.
(defthm fn-bs-k0-record-link-error-arm-relation
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-record-inputp ks stage name frame)
                (not (fn-bs-lookup bs :staging stage)))
           (let ((p6 (nth 6 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity))))
             (fn-bs-store-relation
              (mv-nth 1 (fn-bs-link (car p6) :staging stage :transactions name outcome))
              (fn-sf-record-link-result (cdr p6) :error))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-k0-record-error-arms-relation
                 (:instance fn-bs-k0-record-issued-link-error-arm-relation (outcome '(:eio . :issued)))
                 (:instance fn-bs-link-bytes-are-unchanged-or-linked
                  (bs (car (nth 6 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity))))
                  (sdir :staging) (sname stage) (ddir :transactions) (dname name))
                 (:instance fn-bs-issued-link-bytes-are-the-linked-bytes
                  (outcome '(:eio . :issued))
                  (bs (car (nth 6 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity))))
                  (sdir :staging) (sname stage) (ddir :transactions) (dname name)))
           :in-theory (theory 'minimal-theory))))

(in-theory (disable fn-bs-recovery-entry-kernel fn-bs-recovered-kernel
                    fn-bs-recovered-kernel-recover-stutters
                    fn-bs-issued-link-bytes-are-the-linked-bytes))
