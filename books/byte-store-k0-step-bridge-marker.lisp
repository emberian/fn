;; fn: the marker half of the K0 step bridge (lane k0-corollaries): the
;; generic covered-to-related lemmas, the marker program's pairs derived by
;; fn-bs-step-preserves-k0-coverage alone, its two per-cut corollaries and
;; the marker error arms.  See byte-store-k0-step-bridge for the record.
(in-package "ACL2")
(include-book "byte-store-k0-step")


(defthm fn-bs-k0b-has-root-marker-is-a-root-op
  (implies (fn-bs-k0m-has-root-marker ops)
           (fn-bs-k0m-has-root-marker (fn-bs-ops-for-dir ops :root)))
  :hints (("Goal" :in-theory (enable fn-bs-k0m-has-root-marker fn-bs-ops-for-dir))))
(defthm fn-bs-k0b-shape-has-no-root-marker
  (implies (fn-bs-pending-shape-okp b)
           (not (fn-bs-k0m-has-root-marker (fn-bs-ops-for-dir (fn-bs-pending b) :root))))
  :hints (("Goal" :in-theory (e/d (fn-bs-pending-shape-okp fn-bs-k0m-has-root-marker)
                                  (fn-bs-fencedp fn-bs-inop fn-bs-durable-names)))))
(defthm fn-bs-k0b-relation-has-no-root-marker
  (implies (fn-bs-store-relation b k)
           (not (fn-bs-k0m-has-root-marker (fn-bs-pending b))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-store-relation-window-unfolds (bs b) (ks k))
                 (:instance fn-bs-k0b-has-root-marker-is-a-root-op (ops (fn-bs-pending b)))
                 fn-bs-k0b-shape-has-no-root-marker)
           :in-theory (e/d (fn-bs-pending-matches-phase fn-bs-replay-matches-scan)
                           (fn-bs-store-relation fn-bs-k0b-has-root-marker-is-a-root-op
                            fn-bs-k0b-shape-has-no-root-marker fn-bs-statep fn-bs-pending-shape-okp
                            fn-bs-k0m-has-root-marker fn-bs-ops-for-dir fn-sf-crash-imagep fn-bs-scan-store
                            fn-bs-scan-okp)))))
(defthm fn-bs-k0b-covered-without-root-marker-is-related
  (implies (and (fn-bs-k0-coveredp b k) (not (fn-bs-k0m-has-root-marker (fn-bs-pending b))))
           (fn-bs-store-relation b k))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-bs-k0-coveredp fn-bs-k0s-marker-pendingp) (fn-bs-store-relation)))))
(defthm fn-bs-k0b-covered-with-root-marker-is-pending
  (implies (and (fn-bs-k0-coveredp b k) (fn-bs-k0m-has-root-marker (fn-bs-pending b)))
           (fn-bs-k0s-marker-pendingp b k))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-bs-k0-coveredp) (fn-bs-store-relation fn-bs-k0s-marker-pendingp)))))
(defthm fn-bs-k0b-root-quiet-has-no-root-marker
  (implies (not (fn-bs-ops-for-dir ops :root))
           (not (fn-bs-k0m-has-root-marker ops)))
  :hints (("Goal" :in-theory (enable fn-bs-k0m-has-root-marker fn-bs-ops-for-dir))))
(defthm fn-bs-k0b-completing-transactions-quiet
  (implies (and (fn-bs-store-relation bs ks) (fn-bs-finish-inputp ks sequence txid))
           (not (fn-bs-ops-for-dir (fn-bs-pending bs) :transactions)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-bs-store-relation-window-unfolds))
           :in-theory (e/d (fn-bs-replay-visiblep fn-bs-finish-inputp fn-bs-pending-matches-phase
                            fn-sf-record-present-visiblep)
                           (fn-bs-store-relation fn-bs-pending-shape-okp fn-sf-crash-imagep)))))
(defthm fn-bs-k0b-authority-of-staging-extension
  (implies (not (fn-bs-pending-entry-targets extra))
           (equal (fn-bs-authority-inode-list
                   (fn-bs-make u i (fn-bs-dirs bs) (append (fn-bs-pending bs) extra) n))
                  (fn-bs-authority-inode-list bs)))
  :hints (("Goal" :in-theory (enable fn-bs-authority-inode-list fn-bs-durable-entry))))
(defthm fn-bs-k0b-marker-staging-facts
  (implies (and (fn-bs-store-relation bs ks) (stringp stage) (not (fn-bs-lookup bs :staging stage))
                (fn-cbor-octet-listp octets) (consp octets))
           (let ((n (fn-bs-next-ino bs)))
             (and (equal (fn-bs-lookup (fn-bs-marker-b1 bs stage) :staging stage) n)
                  (equal (fn-bs-lookup (fn-bs-marker-b2 bs stage octets) :staging stage) n)
                  (equal (fn-bs-lookup (fn-bs-marker-b3 bs stage octets) :staging stage) n)
                  (natp n)
                  (equal (fn-bs-authority-inode-list (fn-bs-marker-b1 bs stage)) (fn-bs-authority-inode-list bs))
                  (equal (fn-bs-authority-inode-list (fn-bs-marker-b2 bs stage octets)) (fn-bs-authority-inode-list bs))
                  (equal (fn-bs-authority-inode-list (fn-bs-marker-b3 bs stage octets)) (fn-bs-authority-inode-list bs))
                  (not (member-equal n (fn-bs-authority-inode-list bs))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-k0m-syscall-states fn-bs-related-allocation-is-fresh
                 (:instance fn-bs-store-relation-unfolds)
                 (:instance fn-bs-k6-write-keeps-lookup (bs (fn-bs-marker-b1 bs stage)) (ino (fn-bs-next-ino bs))
                  (offset 0) (dir :staging) (name stage)))
           :in-theory (e/d (fn-bs-marker-b1 fn-bs-marker-b2 fn-bs-marker-b3 fn-bs-statep)
                           (fn-bs-store-relation fn-bs-lookup fn-bs-write fn-bs-authority-inode-list
                            fn-bs-k6-write-keeps-lookup)))))
(defmacro fn-bs-k0b-marker-hyps ()
  '(and (fn-bs-store-relation bs ks)
        (fn-bs-finish-inputp ks sequence txid)
        (stringp stage)
        (not (fn-bs-lookup bs :staging stage))
        (fn-cbor-octet-listp octets) (consp octets)))
(defun fn-bs-k0b-marker-fsync-outcomep (bs stage octets outcome)
  (declare (xargs :guard t :verify-guards nil))
  (let ((b2 (fn-bs-marker-b2 bs stage octets)))
    (or (equal outcome :ok)
        (fn-bs-crash-choicesp (cdr outcome)
                              (fn-bs-ops-for-ino (fn-bs-pending b2) (fn-bs-next-ino bs))
                              (fn-bs-unit b2)))))
(defthm fn-bs-k0b-marker-step-inputs
  (implies (fn-bs-k0b-marker-hyps)
           (and (fn-bs-k0-step-inputp bs ks (list :create :staging stage) outcome)
                (implies (fn-bs-store-relation (fn-bs-marker-b1 bs stage) ks)
                         (fn-bs-k0-step-inputp (fn-bs-marker-b1 bs stage) ks
                                               (list :write-all :staging stage octets) outcome))
                (implies (and (fn-bs-store-relation (fn-bs-marker-b2 bs stage octets) ks)
                              (fn-bs-k0b-marker-fsync-outcomep bs stage octets outcome))
                         (fn-bs-k0-step-inputp (fn-bs-marker-b2 bs stage octets) ks
                                               (list :fsync-file :staging stage) outcome))
                (implies (fn-bs-store-relation (fn-bs-marker-b3 bs stage octets) ks)
                         (fn-bs-k0-step-inputp (fn-bs-marker-b3 bs stage octets) ks
                                               (list :rename :staging stage :root *fn-bs-history-marker-name*)
                                               outcome))
                (implies (fn-bs-k0s-marker-pendingp (fn-bs-marker-b4 bs stage octets) ks)
                         (fn-bs-k0-step-inputp (fn-bs-marker-b4 bs stage octets) ks
                                               (list :fsync-dir :root) outcome))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-k0m-completing-window-facts fn-bs-k0b-completing-transactions-quiet
                 fn-bs-k0b-marker-staging-facts)
           :in-theory (e/d (fn-bs-k0-step-inputp fn-bs-k0b-marker-fsync-outcomep fn-bs-inop
                            fn-bs-marker-b1 fn-bs-marker-b2 fn-bs-marker-b3 fn-bs-ops-for-dir-of-append)
                           (fn-bs-store-relation fn-bs-lookup fn-bs-authority-inode-list
                            fn-bs-k0s-marker-pendingp fn-bs-k0-coveredp fn-bs-replay-visiblep
                            fn-bs-finish-inputp fn-bs-crash-choicesp fn-bs-ops-for-ino fn-bs-k0-observation-inputp)))))
(defthm fn-bs-k0b-marker-rename-b3
  (implies (and (equal (fn-bs-lookup (fn-bs-marker-b3 bs stage octets) :staging stage) (fn-bs-next-ino bs))
                (natp (fn-bs-next-ino bs)))
           (equal (fn-bs-rename (fn-bs-marker-b3 bs stage octets) :staging stage
                                :root *fn-bs-history-marker-name* :ok)
                  (list :ok (fn-bs-marker-b4 bs stage octets))))
  :hints (("Goal" :in-theory (e/d (fn-bs-rename fn-bs-marker-b3 fn-bs-marker-b4 fn-bs-inop) (fn-bs-lookup)))))
(defthm fn-bs-k0b-write-ok-result
  (implies (assoc-equal ino (fn-bs-inodes s))
           (equal (mv-nth 0 (fn-bs-write s ino offset octets :ok)) :ok))
  :hints (("Goal" :in-theory (enable fn-bs-write))))
(defthm fn-bs-k0b-marker-b1-has-stage-inode
  (assoc-equal (fn-bs-next-ino bs) (fn-bs-inodes (fn-bs-marker-b1 bs stage)))
  :hints (("Goal" :in-theory (enable fn-bs-marker-b1))))
(defthm fn-bs-k0b-fsync-ok-results
  (and (equal (mv-nth 0 (fn-bs-fsync-file s ino :ok)) :ok)
       (equal (mv-nth 0 (fn-bs-fsync-dir s dir :ok)) :ok))
  :hints (("Goal" :in-theory (enable fn-bs-fsync-file fn-bs-fsync-dir))))
(defthm fn-bs-k0b-marker-steps
  (implies (fn-bs-k0b-marker-hyps)
           (and (equal (fn-bs-step bs ks (list :create :staging stage) :ok g c)
                       (list :ok (fn-bs-marker-b1 bs stage) ks))
                (equal (fn-bs-step (fn-bs-marker-b1 bs stage) ks (list :write-all :staging stage octets) :ok g c)
                       (list :ok (fn-bs-marker-b2 bs stage octets) ks))
                (equal (fn-bs-step (fn-bs-marker-b2 bs stage octets) ks (list :fsync-file :staging stage) :ok g c)
                       (list :ok (fn-bs-marker-b3 bs stage octets) ks))
                (equal (fn-bs-step (fn-bs-marker-b3 bs stage octets) ks
                                   (list :rename :staging stage :root *fn-bs-history-marker-name*) :ok g c)
                       (list :ok (fn-bs-marker-b4 bs stage octets) ks))
                (equal (fn-bs-step (fn-bs-marker-b4 bs stage octets) ks (list :fsync-dir :root) :ok g c)
                       (list :ok (fn-bs-marker-b5 bs stage octets) ks))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-k0m-syscall-states fn-bs-k0m-resolutions fn-bs-k0m-completing-window-facts
                 (:instance fn-bs-k0-staging-create-fresh-facts (b bs) (k ks))
                 fn-bs-k0b-marker-staging-facts (:instance fn-bs-store-relation-unfolds))
           :in-theory (e/d (fn-bs-step)
                           (fn-bs-store-relation fn-bs-lookup fn-bs-fsync-file fn-bs-fsync-dir fn-bs-rename
                            fn-bs-create fn-bs-write fn-bs-unlink fn-bs-fence-dir fn-bs-k0s-fsync-dir-ok-is-fence
                            fn-bs-statep fn-bs-marker-b1 fn-bs-marker-b2 fn-bs-marker-b3 fn-bs-marker-b4 fn-bs-marker-b5
                            fn-bs-authority-inode-list fn-bs-finish-inputp)))))
(defthm fn-bs-k0b-marker-root-markers
  (implies (not (fn-bs-ops-for-dir (fn-bs-pending bs) :root))
           (and (not (fn-bs-k0m-has-root-marker (fn-bs-pending (fn-bs-marker-b1 bs stage))))
                (not (fn-bs-k0m-has-root-marker (fn-bs-pending (fn-bs-marker-b2 bs stage octets))))
                (not (fn-bs-k0m-has-root-marker (fn-bs-pending (fn-bs-marker-b3 bs stage octets))))
                (fn-bs-k0m-has-root-marker (fn-bs-pending (fn-bs-marker-b4 bs stage octets)))
                (not (fn-bs-k0m-has-root-marker (fn-bs-pending (fn-bs-marker-b5 bs stage octets))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-bs-marker-b1 fn-bs-marker-b2 fn-bs-marker-b3 fn-bs-marker-b4
                                     fn-bs-marker-b5 fn-bs-k0m-has-root-marker))))
(defthm fn-bs-k0b-marker-pairs-by-step
  (implies (fn-bs-k0b-marker-hyps)
           (and (fn-bs-store-relation (fn-bs-marker-b1 bs stage) ks)
                (fn-bs-store-relation (fn-bs-marker-b2 bs stage octets) ks)
                (fn-bs-store-relation (fn-bs-marker-b3 bs stage octets) ks)
                (fn-bs-k0s-marker-pendingp (fn-bs-marker-b4 bs stage octets) ks)
                (fn-bs-store-relation (fn-bs-marker-b5 bs stage octets) ks)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-k0b-marker-step-inputs (outcome :ok))
                 (:instance fn-bs-k0b-marker-steps (g nil) (c nil))
                 fn-bs-k0m-completing-window-facts fn-bs-k0b-marker-root-markers
                 (:instance fn-bs-step-preserves-k0-coverage (bs bs) (step (list :create :staging stage)) (outcome :ok) (groups nil) (capacity nil))
                 (:instance fn-bs-step-preserves-k0-coverage (bs (fn-bs-marker-b1 bs stage)) (step (list :write-all :staging stage octets)) (outcome :ok) (groups nil) (capacity nil))
                 (:instance fn-bs-step-preserves-k0-coverage (bs (fn-bs-marker-b2 bs stage octets)) (step (list :fsync-file :staging stage)) (outcome :ok) (groups nil) (capacity nil))
                 (:instance fn-bs-step-preserves-k0-coverage (bs (fn-bs-marker-b3 bs stage octets)) (step (list :rename :staging stage :root *fn-bs-history-marker-name*)) (outcome :ok) (groups nil) (capacity nil))
                 (:instance fn-bs-step-preserves-k0-coverage (bs (fn-bs-marker-b4 bs stage octets)) (step (list :fsync-dir :root)) (outcome :ok) (groups nil) (capacity nil))
                 (:instance fn-bs-k0b-covered-without-root-marker-is-related (b (fn-bs-marker-b1 bs stage)) (k ks))
                 (:instance fn-bs-k0b-covered-without-root-marker-is-related (b (fn-bs-marker-b2 bs stage octets)) (k ks))
                 (:instance fn-bs-k0b-covered-without-root-marker-is-related (b (fn-bs-marker-b3 bs stage octets)) (k ks))
                 (:instance fn-bs-k0b-covered-with-root-marker-is-pending (b (fn-bs-marker-b4 bs stage octets)) (k ks))
                 (:instance fn-bs-k0b-covered-without-root-marker-is-related (b (fn-bs-marker-b5 bs stage octets)) (k ks)))
           :in-theory (e/d () (fn-bs-store-relation fn-bs-k0-coveredp fn-bs-k0s-marker-pendingp fn-bs-k0-step-inputp
                               fn-bs-step fn-bs-lookup fn-bs-finish-inputp fn-bs-k0m-has-root-marker
                               fn-bs-marker-b1 fn-bs-marker-b2 fn-bs-marker-b3 fn-bs-marker-b4 fn-bs-marker-b5
                               fn-bs-replay-visiblep)))))
(defthm fn-bs-k0b-marker-landed-b4
  (implies (fn-bs-k0b-marker-hyps)
           (equal (fn-bs-k0s-marker-landed (fn-bs-marker-b4 bs stage octets))
                  (fn-bs-marker-b5 bs stage octets)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-k0m-syscall-states fn-bs-k0m-resolutions fn-bs-k0m-completing-window-facts
                 (:instance fn-bs-store-relation-unfolds))
           :in-theory (e/d (fn-bs-k0s-marker-landed fn-bs-k0s-root-target fn-bs-ops-for-dir-of-append)
                           (fn-bs-store-relation fn-bs-statep fn-bs-lookup fn-bs-marker-b1 fn-bs-marker-b2
                            fn-bs-marker-b3 fn-bs-marker-b5 fn-bs-k0m-with-root-entry fn-bs-marker-rename-dropped
                            fn-bs-unlink fn-bs-write fn-bs-fsync-file fn-bs-fsync-dir fn-bs-create
                            fn-bs-finish-inputp fn-bs-replay-visiblep))
           :expand ((fn-bs-marker-b4 bs stage octets)))))
(defthm fn-bs-k0-marker-cuts-relation-by-step
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-finish-inputp ks sequence txid)
                (stringp stage)
                (not (fn-bs-lookup bs :staging stage))
                (fn-cbor-octet-listp octets) (consp octets))
           (let ((run (fn-bs-run bs ks (fn-bs-marker-program stage octets) nil groups capacity)))
             (and (fn-bs-store-relation (car (nth 1 run)) (cdr (nth 1 run)))
                  (fn-bs-store-relation (car (nth 3 run)) (cdr (nth 3 run)))
                  (fn-bs-store-relation (car (nth 5 run)) (cdr (nth 5 run)))
                  (fn-bs-store-relation (fn-bs-marker-rename-dropped (car (nth 7 run)))
                                        (cdr (nth 7 run)))
                  (fn-bs-store-relation (car (nth 9 run)) (cdr (nth 9 run))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-k0b-marker-pairs-by-step fn-bs-k0m-completing-window-facts
                 (:instance fn-bs-store-relation-unfolds))
           :in-theory (e/d (fn-bs-marker-run-shape fn-bs-k0s-marker-pendingp)
                           (fn-bs-store-relation fn-bs-statep fn-bs-lookup fn-bs-marker-program fn-bs-run
                            fn-bs-marker-b1 fn-bs-marker-b2 fn-bs-marker-b3 fn-bs-marker-b4 fn-bs-marker-b5
                            fn-bs-marker-rename-dropped fn-bs-k0s-marker-landed fn-bs-k0m-has-root-marker
                            fn-bs-k0m-root-marker-onlyp fn-bs-finish-inputp fn-bs-replay-visiblep)))))
(defthm fn-bs-k0-marker-replaced-cut-relation-by-step
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
           :use (fn-bs-k0b-marker-pairs-by-step fn-bs-k0m-completing-window-facts fn-bs-k0b-marker-landed-b4
                 fn-bs-k0m-resolutions
                 (:instance fn-bs-k0-covered-crash-image-is-a-related-image (bs (fn-bs-marker-b4 bs stage octets)))
                 (:instance fn-bs-store-relation-unfolds))
           :in-theory (e/d (fn-bs-marker-run-shape fn-bs-k0s-marker-pendingp fn-bs-k0-coveredp)
                           (fn-bs-store-relation fn-bs-statep fn-bs-lookup fn-bs-marker-program fn-bs-run
                            fn-bs-marker-b1 fn-bs-marker-b2 fn-bs-marker-b3 fn-bs-marker-b4 fn-bs-marker-b5
                            fn-bs-marker-rename-dropped fn-bs-k0s-marker-landed fn-bs-k0m-has-root-marker
                            fn-bs-k0m-root-marker-onlyp fn-bs-finish-inputp fn-bs-replay-visiblep
                            fn-bs-crash-imagep fn-bs-fsync-dir fn-bs-k0s-fsync-dir-ok-is-fence)))))
(defun fn-bs-k0b-marker-step-coveredp (pre step outcome ks groups capacity)
  (declare (xargs :guard t :verify-guards nil))
  (mv-let (r bs1 ks1) (fn-bs-step (car pre) (cdr pre) step outcome groups capacity)
    (declare (ignore r))
    (and (fn-bs-k0-coveredp bs1 ks1)
         (equal ks1 ks)
         (equal (fn-sf-phase ks1) :completing))))
(defthm fn-bs-k0b-marker-program-steps
  (let ((prog (fn-bs-marker-program stage octets)))
    (and (equal (nth 0 prog) (list :create :staging stage))
         (equal (nth 2 prog) (list :write-all :staging stage octets))
         (equal (nth 4 prog) (list :fsync-file :staging stage))
         (equal (nth 6 prog) (list :rename :staging stage :root *fn-bs-history-marker-name*))
         (equal (nth 8 prog) (list :fsync-dir :root))))
  :hints (("Goal" :in-theory (enable fn-bs-marker-program))))
(defthm fn-bs-step-at-marker-pairs-preserves-k0-coverage
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-finish-inputp ks sequence txid)
                (stringp stage)
                (not (fn-bs-lookup bs :staging stage))
                (fn-cbor-octet-listp octets) (consp octets)
                (fn-bs-k0b-marker-fsync-outcomep bs stage octets outcome))
           (let ((run (fn-bs-run bs ks (fn-bs-marker-program stage octets) nil groups capacity))
                 (prog (fn-bs-marker-program stage octets)))
             (and (fn-bs-k0b-marker-step-coveredp (cons bs ks) (nth 0 prog) outcome ks groups capacity)
                  (fn-bs-k0b-marker-step-coveredp (nth 1 run) (nth 2 prog) outcome ks groups capacity)
                  (fn-bs-k0b-marker-step-coveredp (nth 3 run) (nth 4 prog) outcome ks groups capacity)
                  (fn-bs-k0b-marker-step-coveredp (nth 5 run) (nth 6 prog) outcome ks groups capacity)
                  (fn-bs-k0b-marker-step-coveredp (nth 7 run) (nth 8 prog) outcome ks groups capacity))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-k0b-marker-pairs-by-step fn-bs-k0m-completing-window-facts fn-bs-k0b-marker-step-inputs
                 (:instance fn-bs-store-relation-unfolds)
                 (:instance fn-bs-step-preserves-k0-coverage (step (list :create :staging stage)))
                 (:instance fn-bs-step-preserves-k0-coverage (bs (fn-bs-marker-b1 bs stage)) (step (list :write-all :staging stage octets)))
                 (:instance fn-bs-step-preserves-k0-coverage (bs (fn-bs-marker-b2 bs stage octets)) (step (list :fsync-file :staging stage)))
                 (:instance fn-bs-step-preserves-k0-coverage (bs (fn-bs-marker-b3 bs stage octets)) (step (list :rename :staging stage :root *fn-bs-history-marker-name*)))
                 (:instance fn-bs-step-preserves-k0-coverage (bs (fn-bs-marker-b4 bs stage octets)) (step (list :fsync-dir :root))))
           :in-theory (e/d (fn-bs-marker-run-shape fn-bs-k0b-marker-step-coveredp
                            fn-bs-k0s-syscall-step-keeps-kernel fn-bs-finish-inputp)
                           (fn-bs-store-relation fn-bs-statep fn-bs-lookup fn-bs-run fn-bs-step fn-bs-marker-program
                            fn-bs-marker-b1 fn-bs-marker-b2 fn-bs-marker-b3 fn-bs-marker-b4 fn-bs-marker-b5
                            fn-bs-k0-coveredp fn-bs-k0-step-inputp fn-bs-k0s-marker-pendingp
                            fn-bs-k0b-marker-fsync-outcomep fn-bs-replay-visiblep)))))
