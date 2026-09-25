;; fn: the recovery program by the general step, and the in-process
;; re-recovery (P-RECOVER, lane k0-recovery).
;;
;; fn-bs-k0v-recover-program-by-step: from ANY byte state related to the
;; kernel the host's reopen installs (fn-bs-recovered-kernel f r 0, phase
;; :recovering, fn-bs-host-reopened-kernel-is-the-recovered-kernel), with
;; whatever the pending list holds -- in particular the one un-fenced :root
;; rename or :transactions link a process that died between its rename or
;; link and the directory fence leaves in the page cache -- every step of
;; fn-bs-recover-program satisfies fn-bs-k0-step-inputp at the pair the run
;; reaches before it (fn-bs-k0v-steps-coveredp), every pair of the run is
;; related, and the run ends at the drained state (the :transactions, :root
;; and :parent fences applied, authority quiet) with the kernel :ready.
;; The quiet-image theorems of byte-store-k0-recovery are the special case
;; of an empty authority pending list.
;;
;; fn-bs-k0v-host-rerecovery-keeps-relation-at-every-cut: the in-process
;; re-recovery at host/native/admin.lisp:107 (fnn-admin-verify-under-lock:
;; fnn-bridge-reset, then fnn-recover in the same process).  fnn-recover
;; reads the LIVE view (fnn-load-frontier, fnn-durable-records), which is
;; fn-bs-scan-store of the byte state itself, not of a crash image, and
;; passes it to fnn-bridge-recover (host/native/io.lisp), which calls
;; fn-store-sn-recover and so fn-cpo-open-observed.  From a related pair
;; whose :root and :transactions directories are quiet, when that open
;; succeeds, its kernel is related to the live state and every pair of the
;; recovery program run from it is related.  The pair need not be a crash
;; image and its kernel need not carry an empty success list: the reset
;; discards the old kernel and the reopen builds one with none.
;;
;; The quiet hypothesis is what the host line has: the administrative
;; process opened the store through the same recovery (whose fences drain
;; :root and :transactions) and published only a configuration record, which
;; touches neither directory.  It is sufficient, not shown necessary.  Not
;; covered here: that the administrative publication's own syscalls keep the
;; pair related (there is no byte program for it).
(in-package "ACL2")
(include-book "byte-store-k0-step")
(include-book "byte-store-k0-recovery")

(defthm fn-bs-k0v-recovered-kernel-parts
  (implies (fn-sf-statep (fn-bs-recovered-kernel f r n))
           (and (fn-record-uint32p f) (fn-sf-record-listp r 0 0 f)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-sf-statep fn-sf-phase-shapep fn-bs-recovered-kernel))))
(defthm fn-bs-k0v-related-root-lookups-are-fenced
  (implies (fn-bs-store-relation bs ks)
           (and (fn-bs-fencedp bs (fn-bs-lookup bs :root *fn-bs-scan-config-name*))
                (fn-bs-fencedp bs (fn-bs-lookup bs :root *fn-bs-scan-frontier-name*))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :cases ((consp (fn-bs-ops-for-dir (fn-bs-pending bs) :root)))
           :use (fn-bs-store-relation-implies-the-pending-shape
                 fn-bs-store-relation-fences-the-root-inodes
                 (:instance fn-bs-lookup-of-an-untouched-name (s bs) (dir :root) (name *fn-bs-scan-config-name*))
                 (:instance fn-bs-lookup-of-an-untouched-name (s bs) (dir :root) (name *fn-bs-scan-frontier-name*))
                 (:instance fn-bs-lookup-of-a-pending-target (s bs) (dir :root) (name *fn-bs-scan-frontier-name*))
                 (:instance fn-bs-shape-leaves-the-config-name-quiet)
                 (:instance fn-bs-shape-at-the-frontier-name))
           :in-theory (e/d ()
                           (fn-bs-store-relation fn-bs-lookup fn-bs-fencedp fn-bs-lookup-of-an-untouched-name
                            fn-bs-lookup-of-a-pending-target fn-bs-durable-entry fn-bs-pending-shape-okp
                            fn-bs-shape-leaves-the-config-name-quiet fn-bs-shape-at-the-frontier-name fn-bs-ops-for-name fn-bs-ops-for-dir)))
          (and stable-under-simplificationp
               '(:in-theory (e/d (fn-bs-pending-shape-okp)
                           (fn-bs-store-relation fn-bs-lookup fn-bs-fencedp fn-bs-lookup-of-an-untouched-name
                            fn-bs-lookup-of-a-pending-target fn-bs-durable-entry fn-bs-ops-for-name fn-bs-ops-for-dir))))))
(local
 (defthm k0v-recovered-kernel-is-state
   (implies (and (fn-record-uint32p f) (fn-sf-record-listp r 0 0 f)
                 (natp n) (<= n *fn-sf-recovery-barrier-count*))
            (fn-sf-statep (fn-bs-recovered-kernel f r n)))
   :hints (("Goal" :in-theory (enable fn-sf-statep fn-sf-phase-shapep fn-bs-recovered-kernel)))))
(local
 (defthm k0v-recovered-kernel-barrier
   (implies (and (fn-record-uint32p f) (fn-sf-record-listp r 0 0 f)
                 (natp n) (< n *fn-sf-recovery-barrier-count*))
            (equal (fn-sf-dispatch (fn-bs-recovered-kernel f r n) '(:recovery-barrier :ok) g c)
                   (fn-bs-recovered-kernel f r (1+ n))))
   :hints (("Goal" :use k0v-recovered-kernel-is-state
            :in-theory (e/d (fn-sf-dispatch fn-sf-recovery-barrier fn-bs-recovered-kernel)
                            (fn-sf-statep k0v-recovered-kernel-is-state))))))
(local
 (defthm k0v-fsync-results
   (and (equal (mv-nth 0 (fn-bs-fsync-file s ino :ok)) :ok)
        (equal (mv-nth 0 (fn-bs-fsync-dir s d :ok)) :ok))
   :hints (("Goal" :in-theory (enable fn-bs-fsync-file fn-bs-fsync-dir)))))
(local
 (defthm k0v-recovered-kernel-recover-stutters
   (equal (fn-sf-dispatch (fn-bs-recovered-kernel f r 0) '(:recover) g c)
          (fn-bs-recovered-kernel f r 0))
   :hints (("Goal" :in-theory (enable fn-sf-dispatch fn-sf-recover fn-bs-recovered-kernel)))))
(defun fn-bs-k0v-drained (bs)
  (declare (xargs :guard t :verify-guards nil))
  (fn-bs-fence-dir (fn-bs-fence-dir (fn-bs-fence-dir bs :transactions) :root) :parent))
(defthm fn-bs-k0v-recover-program-run
  (implies (and (fn-bs-statep bs)
                (fn-bs-fencedp bs (fn-bs-lookup bs :root *fn-bs-scan-config-name*))
                (fn-bs-fencedp bs (fn-bs-lookup bs :root *fn-bs-scan-frontier-name*))
                (fn-record-uint32p f) (fn-sf-record-listp r 0 0 f))
           (let ((b1 (fn-bs-fence-dir bs :transactions))
                 (b2 (fn-bs-fence-dir (fn-bs-fence-dir bs :transactions) :root))
                 (b3 (fn-bs-k0v-drained bs)))
             (equal (fn-bs-run bs (fn-bs-recovered-kernel f r 0) (fn-bs-recover-program) nil groups capacity)
                    (list (cons bs (fn-bs-recovered-kernel f r 0))
                          (cons bs (fn-bs-recovered-kernel f r 0))
                          (cons bs (fn-bs-recovered-kernel f r 0))
                          (cons bs (fn-bs-recovered-kernel f r 1))
                          (cons bs (fn-bs-recovered-kernel f r 1))
                          (cons bs (fn-bs-recovered-kernel f r 1))
                          (cons bs (fn-bs-recovered-kernel f r 2))
                          (cons bs (fn-bs-recovered-kernel f r 2))
                          (cons b1 (fn-bs-recovered-kernel f r 2))
                          (cons b1 (fn-bs-recovered-kernel f r 3))
                          (cons b1 (fn-bs-recovered-kernel f r 3))
                          (cons b2 (fn-bs-recovered-kernel f r 3))
                          (cons b2 (fn-bs-recovered-kernel f r 4))
                          (cons b2 (fn-bs-recovered-kernel f r 4))
                          (cons b3 (fn-bs-recovered-kernel f r 4))
                          (cons b3 (fn-bs-recovered-kernel f r 5))
                          (cons b3 (fn-bs-recovered-kernel f r 5))))))
  :rule-classes nil
  :hints (("Goal" :expand ((:free (b k s o) (fn-bs-run b k s o groups capacity)))
           :in-theory (e/d (fn-bs-recover-program fn-bs-step fn-bs-k0v-drained fn-bs-k0s-fsync-dir-ok-is-fence
                            fn-bs-k0w-fenced-fsync-file-is-identity)
                           (fn-bs-fsync-file fn-bs-fsync-dir fn-bs-fence-file fn-bs-fence-dir fn-sf-dispatch fn-bs-recovered-kernel
                            fn-bs-statep fn-bs-lookup fn-sf-record-listp fn-bs-fencedp)))))
(local
 (defthm k0v-recovered-kernel-window-facts
   (and (equal (fn-sf-frontier (fn-bs-recovered-kernel f r n)) f)
        (equal (fn-sf-records (fn-bs-recovered-kernel f r n)) r)
        (equal (fn-sf-successes (fn-bs-recovered-kernel f r n)) nil)
        (iff (fn-bs-replay-visiblep (fn-bs-recovered-kernel f r n))
             (not (equal n *fn-sf-recovery-barrier-count*))))
   :hints (("Goal" :in-theory (enable fn-bs-recovered-kernel fn-bs-replay-visiblep)))))
(local
 (defthm k0v-swap
   (implies (and (fn-bs-store-relation b (fn-bs-recovered-kernel f r 0))
                 (natp n) (< n *fn-sf-recovery-barrier-count*))
            (fn-bs-store-relation b (fn-bs-recovered-kernel f r n)))
   :hints (("Goal" :use ((:instance fn-bs-k0w-window-kernel-swap (bs b) (ks (fn-bs-recovered-kernel f r 0))
                                    (ks1 (fn-bs-recovered-kernel f r n)))
                         (:instance fn-bs-store-relation-unfolds (bs b) (ks (fn-bs-recovered-kernel f r 0)))
                         (:instance fn-bs-k0v-recovered-kernel-parts (n 0))
                         (:instance k0v-recovered-kernel-is-state))
            :in-theory (e/d () (fn-bs-store-relation fn-bs-recovered-kernel fn-sf-statep k0v-recovered-kernel-is-state
                                fn-sf-record-listp fn-bs-replay-visiblep))))))
(local
 (defthm k0v-fence-step
   (implies (and (fn-bs-store-relation b (fn-bs-recovered-kernel f r 0)))
            (fn-bs-store-relation (fn-bs-fence-dir b d) (fn-bs-recovered-kernel f r 0)))
   :hints (("Goal" :use ((:instance fn-bs-k0w-fence-preserves-relation (bs b) (ks (fn-bs-recovered-kernel f r 0))))
            :in-theory (e/d () (fn-bs-store-relation fn-bs-recovered-kernel fn-bs-fence-dir))))))
(defthm fn-bs-k0v-drained-is-quiet
  (fn-bs-k0w-authority-quietp (fn-bs-k0v-drained bs))
  :hints (("Goal" :in-theory (e/d (fn-bs-k0v-drained fn-bs-k0w-authority-quietp fn-bs-k8-fence-pending-is-filtered
                                   fn-bs-k8-other-directory-ops-survive-filter fn-bs-ops-for-dir-of-ops-not-for-dir)
                                  (fn-bs-fence-dir fn-bs-ops-for-dir fn-bs-ops-not-for-dir)))))
(local
 (defthm k0v-drained-ready
   (implies (fn-bs-store-relation b (fn-bs-recovered-kernel f r 0))
            (fn-bs-store-relation (fn-bs-k0v-drained b) (fn-bs-recovered-kernel f r 5)))
   :hints (("Goal" :use ((:instance fn-bs-k0w-quiet-window-exit (bs (fn-bs-k0v-drained b))
                                    (ks (fn-bs-recovered-kernel f r 0)) (ks1 (fn-bs-recovered-kernel f r 5)))
                         (:instance k0v-fence-step (d :transactions))
                         (:instance k0v-fence-step (b (fn-bs-fence-dir b :transactions)) (d :root))
                         (:instance k0v-fence-step (b (fn-bs-fence-dir (fn-bs-fence-dir b :transactions) :root)) (d :parent))
                         (:instance fn-bs-k0v-drained-is-quiet (bs b))
                         (:instance fn-bs-store-relation-unfolds (bs b) (ks (fn-bs-recovered-kernel f r 0)))
                         (:instance fn-bs-k0v-recovered-kernel-parts (n 0))
                         (:instance k0v-recovered-kernel-is-state (n 5)))
            :in-theory (e/d (fn-bs-k0v-drained)
                            (fn-bs-store-relation fn-bs-recovered-kernel fn-sf-statep k0v-recovered-kernel-is-state
                             fn-sf-record-listp fn-bs-fence-dir k0v-fence-step fn-bs-k0v-drained-is-quiet
                             fn-bs-k0w-authority-quietp))))))
(defun fn-bs-k0v-steps-coveredp (pairs steps)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp steps)
      (and (consp pairs)
           (fn-bs-k0-step-inputp (car (car pairs)) (cdr (car pairs)) (car steps) :ok)
           (fn-bs-k0v-steps-coveredp (cdr pairs) (cdr steps)))
    t))
(local
 (defthm k0v-recovered-kernel-phase
   (and (equal (fn-sf-phase (fn-bs-recovered-kernel f r n))
               (if (equal n *fn-sf-recovery-barrier-count*) :ready :recovering))
        (equal (fn-sf-barriers (fn-bs-recovered-kernel f r n)) n))
   :hints (("Goal" :in-theory (enable fn-bs-recovered-kernel)))))
(local
 (defthm k0v-entry-facts
   (implies (fn-bs-store-relation bs (fn-bs-recovered-kernel f r 0))
            (and (fn-bs-statep bs)
                 (fn-record-uint32p f) (fn-sf-record-listp r 0 0 f)
                 (fn-bs-fencedp bs (fn-bs-lookup bs :root *fn-bs-scan-config-name*))
                 (fn-bs-fencedp bs (fn-bs-lookup bs :root *fn-bs-scan-frontier-name*))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn-bs-store-relation-unfolds (ks (fn-bs-recovered-kernel f r 0)))
                         (:instance fn-bs-k0v-related-root-lookups-are-fenced (ks (fn-bs-recovered-kernel f r 0)))
                         (:instance fn-bs-k0v-recovered-kernel-parts (n 0)))
            :in-theory (theory 'minimal-theory)))))
(local
 (defthm k0v-explicit-run-facts
   (implies (fn-bs-store-relation bs (fn-bs-recovered-kernel f r 0))
            (and (fn-bs-k0v-steps-coveredp (cons (cons bs (fn-bs-recovered-kernel f r 0)) (list (cons bs (fn-bs-recovered-kernel f r 0))
                          (cons bs (fn-bs-recovered-kernel f r 0))
                          (cons bs (fn-bs-recovered-kernel f r 0))
                          (cons bs (fn-bs-recovered-kernel f r 1))
                          (cons bs (fn-bs-recovered-kernel f r 1))
                          (cons bs (fn-bs-recovered-kernel f r 1))
                          (cons bs (fn-bs-recovered-kernel f r 2))
                          (cons bs (fn-bs-recovered-kernel f r 2))
                          (cons (fn-bs-fence-dir bs :transactions) (fn-bs-recovered-kernel f r 2))
                          (cons (fn-bs-fence-dir bs :transactions) (fn-bs-recovered-kernel f r 3))
                          (cons (fn-bs-fence-dir bs :transactions) (fn-bs-recovered-kernel f r 3))
                          (cons (fn-bs-fence-dir (fn-bs-fence-dir bs :transactions) :root) (fn-bs-recovered-kernel f r 3))
                          (cons (fn-bs-fence-dir (fn-bs-fence-dir bs :transactions) :root) (fn-bs-recovered-kernel f r 4))
                          (cons (fn-bs-fence-dir (fn-bs-fence-dir bs :transactions) :root) (fn-bs-recovered-kernel f r 4))
                          (cons (fn-bs-k0v-drained bs) (fn-bs-recovered-kernel f r 4))
                          (cons (fn-bs-k0v-drained bs) (fn-bs-recovered-kernel f r 5))
                          (cons (fn-bs-k0v-drained bs) (fn-bs-recovered-kernel f r 5))))
                                           (fn-bs-recover-program))
                 (fn-bs-run-relatedp (list (cons bs (fn-bs-recovered-kernel f r 0))
                          (cons bs (fn-bs-recovered-kernel f r 0))
                          (cons bs (fn-bs-recovered-kernel f r 0))
                          (cons bs (fn-bs-recovered-kernel f r 1))
                          (cons bs (fn-bs-recovered-kernel f r 1))
                          (cons bs (fn-bs-recovered-kernel f r 1))
                          (cons bs (fn-bs-recovered-kernel f r 2))
                          (cons bs (fn-bs-recovered-kernel f r 2))
                          (cons (fn-bs-fence-dir bs :transactions) (fn-bs-recovered-kernel f r 2))
                          (cons (fn-bs-fence-dir bs :transactions) (fn-bs-recovered-kernel f r 3))
                          (cons (fn-bs-fence-dir bs :transactions) (fn-bs-recovered-kernel f r 3))
                          (cons (fn-bs-fence-dir (fn-bs-fence-dir bs :transactions) :root) (fn-bs-recovered-kernel f r 3))
                          (cons (fn-bs-fence-dir (fn-bs-fence-dir bs :transactions) :root) (fn-bs-recovered-kernel f r 4))
                          (cons (fn-bs-fence-dir (fn-bs-fence-dir bs :transactions) :root) (fn-bs-recovered-kernel f r 4))
                          (cons (fn-bs-k0v-drained bs) (fn-bs-recovered-kernel f r 4))
                          (cons (fn-bs-k0v-drained bs) (fn-bs-recovered-kernel f r 5))
                          (cons (fn-bs-k0v-drained bs) (fn-bs-recovered-kernel f r 5))))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
           :use (k0v-entry-facts
                                  (:instance k0v-swap (b bs) (n 0)) (:instance k0v-swap (b bs) (n 1)) (:instance k0v-swap (b bs) (n 2))
                 (:instance k0v-fence-step (b bs) (d :transactions))
                 (:instance k0v-swap (b (fn-bs-fence-dir bs :transactions)) (n 2))
                 (:instance k0v-swap (b (fn-bs-fence-dir bs :transactions)) (n 3))
                 (:instance k0v-fence-step (b (fn-bs-fence-dir bs :transactions)) (d :root))
                 (:instance k0v-swap (b (fn-bs-fence-dir (fn-bs-fence-dir bs :transactions) :root)) (n 3))
                 (:instance k0v-swap (b (fn-bs-fence-dir (fn-bs-fence-dir bs :transactions) :root)) (n 4))
                 (:instance k0v-fence-step (b (fn-bs-fence-dir (fn-bs-fence-dir bs :transactions) :root)) (d :parent))
                 (:instance k0v-swap (b (fn-bs-k0v-drained bs)) (n 4))
                 (:instance k0v-drained-ready (b bs))
                 (:instance fn-bs-k0v-drained-is-quiet))
           :in-theory (e/d (fn-bs-k0v-drained fn-bs-k0v-steps-coveredp fn-bs-run-relatedp fn-bs-recover-program
                            fn-bs-k0-step-inputp fn-bs-k0w-step-inputp fn-bs-k0w-observation-inputp
                            fn-bs-k0-outside-step-inputp fn-bs-k0s-covered-of-relation)
                           (fn-bs-store-relation fn-bs-recovered-kernel fn-bs-fence-dir fn-bs-run
                            fn-bs-k0w-authority-quietp fn-bs-lookup fn-bs-fencedp fn-bs-statep fn-sf-record-listp
                            k0v-swap k0v-fence-step k0v-drained-ready fn-bs-k0v-drained-is-quiet fn-bs-k0-coveredp
                            fn-bs-ops-for-dir))))))
(defthm fn-bs-k0v-recover-program-by-step
  (implies (fn-bs-store-relation bs (fn-bs-recovered-kernel f r 0))
           (let ((run (fn-bs-run bs (fn-bs-recovered-kernel f r 0) (fn-bs-recover-program) nil groups capacity)))
             (and (fn-bs-k0v-steps-coveredp (cons (cons bs (fn-bs-recovered-kernel f r 0)) run)
                                            (fn-bs-recover-program))
                  (fn-bs-run-relatedp run)
                  (equal (len run) 17)
                  (equal (car (nth 16 run)) (fn-bs-k0v-drained bs))
                  (equal (cdr (nth 16 run)) (fn-bs-recovered-kernel f r *fn-sf-recovery-barrier-count*)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (k0v-entry-facts k0v-explicit-run-facts fn-bs-k0v-recover-program-run)
           :in-theory (union-theories '(len nth car-cons cdr-cons (:executable-counterpart zp) (:executable-counterpart binary-+)
                                        (:executable-counterpart equal) (:executable-counterpart <) (:executable-counterpart natp))
                                      (theory 'minimal-theory)))))
(defthm fn-bs-k0v-quiet-view-reads-durable
  (implies (and (fn-bs-store-relation bs ks) (fn-bs-k0w-authority-quietp bs))
           (and (equal (fn-bs-lookup bs :root *fn-bs-scan-config-name*)
                       (fn-bs-durable-entry bs :root *fn-bs-scan-config-name*))
                (equal (fn-bs-lookup bs :root *fn-bs-scan-frontier-name*)
                       (fn-bs-durable-entry bs :root *fn-bs-scan-frontier-name*))
                (equal (fn-bs-content bs (fn-bs-durable-entry bs :root *fn-bs-scan-config-name*))
                       (fn-bs-durable-content bs (fn-bs-durable-entry bs :root *fn-bs-scan-config-name*)))
                (equal (fn-bs-content bs (fn-bs-durable-entry bs :root *fn-bs-scan-frontier-name*))
                       (fn-bs-durable-content bs (fn-bs-durable-entry bs :root *fn-bs-scan-frontier-name*)))
                (equal (fn-bs-names bs :transactions) (fn-bs-durable-names bs :transactions))
                (equal (fn-bs-read-records bs 0 (len (fn-bs-durable-names bs :transactions)))
                       (fn-bs-durable-records bs))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-store-relation-fences-the-root-inodes
                 fn-bs-store-relation-view-namespace-without-a-pending-link
                 fn-bs-view-reads-the-durable-records
                 (:instance fn-bs-content-of-a-fenced-inode (s bs) (ino (fn-bs-durable-entry bs :root *fn-bs-scan-config-name*)))
                 (:instance fn-bs-content-of-a-fenced-inode (s bs) (ino (fn-bs-durable-entry bs :root *fn-bs-scan-frontier-name*)))
                 (:instance fn-bs-lookup-of-an-untouched-name (s bs) (dir :root) (name *fn-bs-scan-config-name*))
                 (:instance fn-bs-lookup-of-an-untouched-name (s bs) (dir :root) (name *fn-bs-scan-frontier-name*))
                 (:instance fn-bs-ops-for-name-through-ops-for-dir (ops (fn-bs-pending bs)) (dir :root) (name *fn-bs-scan-config-name*))
                 (:instance fn-bs-ops-for-name-through-ops-for-dir (ops (fn-bs-pending bs)) (dir :root) (name *fn-bs-scan-frontier-name*)))
           :in-theory (e/d (fn-bs-k0w-authority-quietp)
                           (fn-bs-store-relation fn-bs-lookup fn-bs-content fn-bs-names fn-bs-read-records fn-bs-durable-names
                            fn-bs-durable-records fn-bs-durable-entry fn-bs-durable-content fn-bs-fencedp fn-bs-ops-for-name
                            fn-bs-ops-for-dir fn-bs-lookup-of-an-untouched-name fn-bs-content-of-a-fenced-inode)))))
(defthm fn-bs-k0v-quiet-kernel-admits-durable
  (implies (and (fn-bs-store-relation bs ks) (fn-bs-k0w-authority-quietp bs))
           (fn-sf-recovery-crash-imagep ks (fn-bs-durable-frontier bs) (fn-bs-durable-records bs)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :cases ((fn-bs-replay-visiblep ks))
           :use (fn-bs-store-relation-unfolds fn-bs-store-relation-window-unfolds
                 fn-bs-k0v-quiet-view-reads-durable
                 (:instance fn-bs-replay-matches-scan-unfolds)
                 (:instance fn-bs-scan-okp-unfolds (s bs)))
           :in-theory (e/d (fn-sf-recovery-crash-imagep fn-sf-crash-imagep fn-bs-durable-frontier)
                           (fn-bs-store-relation fn-bs-lookup fn-bs-content fn-bs-names fn-bs-read-records fn-bs-durable-names
                            fn-bs-durable-records fn-bs-durable-entry fn-bs-durable-content fn-bs-scan-store fn-bs-scan-okp
                            fn-bs-scan-frontier fn-bs-scan-records fn-sf-statep fn-bs-replay-matches-scan fn-bs-replay-visiblep
                            fn-bs-pending-matches-phase fn-sf-frontier-rollback-visiblep fn-sf-record-rollback-visiblep
                            fn-sf-frontier-new-visiblep fn-sf-record-present-visiblep fn-bs-k0w-authority-quietp)))))
(defthm fn-bs-k0v-quiet-scan-is-durable
  (implies (and (fn-bs-store-relation bs ks) (fn-bs-k0w-authority-quietp bs))
           (equal (fn-bs-scan-store bs)
                  (list :ok (fn-bs-durable-frontier bs) (fn-bs-durable-records bs))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-store-relation-unfolds fn-bs-k0v-quiet-view-reads-durable fn-bs-k0v-quiet-kernel-admits-durable
                 (:instance fn-sf-recovery-admissible-image-facts (s ks) (frontier (fn-bs-durable-frontier bs))
                            (records (fn-bs-durable-records bs))))
           :in-theory (e/d (fn-bs-scan-store fn-bs-durable-frontier fn-bs-contiguous-namesp)
                           (fn-bs-store-relation fn-bs-lookup fn-bs-content fn-bs-names fn-bs-read-records fn-bs-durable-names
                            fn-bs-durable-records fn-bs-durable-entry fn-bs-durable-content fn-sf-statep
                            fn-sf-recovery-crash-imagep fn-sf-record-listp fn-bs-k0w-authority-quietp
                            fn-bs-txn-names fn-sf-recovery-admissible-image-facts)))))
(defthm fn-bs-k0v-quiet-pair-relates-to-rerecovered-kernel
  (implies (and (fn-bs-store-relation bs ks) (fn-bs-k0w-authority-quietp bs))
           (fn-bs-store-relation bs (fn-bs-recovered-kernel (fn-bs-scan-frontier (fn-bs-scan-store bs))
                                                            (fn-bs-scan-records (fn-bs-scan-store bs)) 0)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-store-relation-unfolds fn-bs-k0v-quiet-scan-is-durable fn-bs-k0v-quiet-kernel-admits-durable
                 fn-bs-store-relation-implies-the-pending-shape
                 (:instance fn-sf-recovery-admissible-image-facts (s ks) (frontier (fn-bs-durable-frontier bs))
                            (records (fn-bs-durable-records bs)))
                 (:instance k0v-recovered-kernel-is-state (f (fn-bs-durable-frontier bs)) (r (fn-bs-durable-records bs)) (n 0)))
           :in-theory (e/d (fn-bs-store-relation fn-bs-replay-matches-scan fn-bs-scan-okp fn-bs-scan-frontier fn-bs-scan-records
                            fn-bs-k0w-authority-quietp)
                           (fn-bs-scan-store fn-bs-durable-frontier fn-bs-durable-records fn-bs-statep fn-sf-statep
                            fn-bs-pending-shape-okp fn-bs-authority-fencedp fn-bs-authority-knownp fn-bs-recovered-kernel
                            fn-sf-recovery-crash-imagep fn-sf-record-listp fn-sf-recovery-admissible-image-facts
                            k0v-recovered-kernel-is-state fn-bs-durable-content fn-bs-durable-entry fn-bs-durable-names
                            fn-bs-contiguous-namesp fn-bs-ops-for-dir fn-sf-crash-imagep)))))
(defthm fn-bs-k0v-host-rerecovery-keeps-relation-at-every-cut
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-k0w-authority-quietp bs)
                (fn-sn-open-okp (fn-cpo-open-observed configs
                                                      (fn-bs-scan-frontier (fn-bs-scan-store bs))
                                                      (fn-bs-scan-records (fn-bs-scan-store bs)))))
           (let* ((host (fn-sn-files (fn-sn-open-state
                                      (fn-cpo-open-observed configs
                                                            (fn-bs-scan-frontier (fn-bs-scan-store bs))
                                                            (fn-bs-scan-records (fn-bs-scan-store bs))))))
                  (run (fn-bs-run bs host (fn-bs-recover-program) nil groups capacity)))
             (and (fn-bs-store-relation bs host)
                  (fn-bs-k0v-steps-coveredp (cons (cons bs host) run) (fn-bs-recover-program))
                  (fn-bs-run-relatedp run)
                  (equal (len run) 17)
                  (equal (fn-sf-phase (cdr (nth 16 run))) :ready))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-k0v-quiet-pair-relates-to-rerecovered-kernel
                 (:instance fn-bs-host-reopened-kernel-is-the-recovered-kernel
                  (frontier (fn-bs-scan-frontier (fn-bs-scan-store bs)))
                  (events (fn-bs-scan-records (fn-bs-scan-store bs))))
                 (:instance fn-bs-k0v-recover-program-by-step
                  (f (fn-bs-scan-frontier (fn-bs-scan-store bs)))
                  (r (fn-bs-scan-records (fn-bs-scan-store bs))))
                 (:instance k0v-recovered-kernel-phase
                  (f (fn-bs-scan-frontier (fn-bs-scan-store bs)))
                  (r (fn-bs-scan-records (fn-bs-scan-store bs))) (n 5)))
           :in-theory (union-theories '((:executable-counterpart equal) (:executable-counterpart if))
                                      (theory 'minimal-theory)))))
