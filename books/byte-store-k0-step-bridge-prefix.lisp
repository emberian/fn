;; fn: the K0 step bridge's program prefixes (lane k0-cuts, PKT-084/085).
;;
;; Keystone: fn-bs-step-preserves-k0-coverage (byte-store-k0-step).  The
;; frontier and record programs each begin with the same three syscalls on a
;; fresh staging name -- create, write-all, fsync-file -- whose states are
;; fn-bs-k0p-s1, -s2 and -s3 here, as fn-bs-marker-b1..b3 are for the marker
;; program.  fn-bs-k0p-stage-pairs-by-step derives the relation at all three
;; from the entry pair by the keystone alone, for any related entry state
;; outside the recovery window whose root and transaction directories are
;; quiet.  fn-bs-k0p-frontier-run-prefix and fn-bs-k0p-record-run-prefix
;; restate each program's run up to its staged-durable cut as those states.
;; Then, each by the keystone at the pair before the cut:
;;   fn-bs-k0-frontier-created-and-written-cut-relation-by-step (pairs 2, 4)
;;   fn-bs-k0-frontier-staged-durable-cut-relation-by-step (pair 7)
;;   fn-bs-k0-record-created-and-written-cut-relation-by-step (pairs 1, 3)
;;   fn-bs-k0-record-staged-durable-cut-relation-by-step (pair 6)
;;   fn-bs-k0-record-linked-cut-relation-by-step (pair 8): the link's step
;;   inputs at pair 6 are discharged by fn-bs-k0p-record-link-inputs -- the
;;   next transaction name (fn-bs-k0p-staged-candidate-is-next-sequence, the
;;   exported copy of a local lemma of byte-store-record-provenance-bytes),
;;   the fenced, allocated source reading as the candidate, the destination
;;   absent and the durable record list exactly the kernel's.
;; The per-cut theorems of byte-store-k0-staging and byte-store-k0 stay in
;; place.  The generic run lemmas (fn-bs-k0b-cut-after-step and its
;; neighbours) moved here from byte-store-k0-step-bridge, which now chains
;; every frontier and record corollary from these.
(in-package "ACL2")
(include-book "byte-store-k0-step-bridge-marker")

(defthm fn-bs-k0b-run-consp-forward-base
  (implies (and (consp (nth 1 (fn-bs-run bs ks steps nil g c)))
                (equal (mv-nth 0 (fn-bs-step (car (nth 0 (fn-bs-run bs ks steps nil g c)))
                                             (cdr (nth 0 (fn-bs-run bs ks steps nil g c)))
                                             (nth 1 steps) :ok g c))
                       :ok)
                (consp (nthcdr 2 steps)))
           (consp (nth 2 (fn-bs-run bs ks steps nil g c))))
  :rule-classes nil
  :hints (("Goal" :expand ((fn-bs-run bs ks steps nil g c)
                           (:free (b k2) (fn-bs-run b k2 (cdr steps) nil g c))
                           (:free (b k2) (fn-bs-run b k2 (cddr steps) nil g c)))
           :in-theory (e/d (nth nthcdr) (fn-bs-step)))))
(defthm fn-bs-k0b-run-nth-consp-forward
  (implies (and (natp k)
                (consp (nth (1+ k) (fn-bs-run bs ks steps nil g c)))
                (equal (mv-nth 0 (fn-bs-step (car (nth k (fn-bs-run bs ks steps nil g c)))
                                             (cdr (nth k (fn-bs-run bs ks steps nil g c)))
                                             (nth (1+ k) steps) :ok g c))
                       :ok)
                (consp (nthcdr (+ 2 k) steps)))
           (consp (nth (+ 2 k) (fn-bs-run bs ks steps nil g c))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-bs-k0c-ind k bs ks steps nil g c)
           :expand ((fn-bs-run bs ks steps nil g c))
           :in-theory (e/d (nth nthcdr) (fn-bs-run fn-bs-step)))
          ("Subgoal *1/1" :use (fn-bs-k0b-run-consp-forward-base))))
(defthm fn-bs-k0b-consp-nthcdr-earlier
  (implies (and (natp n) (consp (nthcdr (1+ n) x))) (consp (nthcdr n x)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable nthcdr))))
(defthm fn-bs-k0b-cut-after-step-pair
  (implies (and (natp k)
                (member-equal (car (nth k steps)) '(:observe :cut :fsync-file :fsync-dir))
                (consp (nth k (fn-bs-run bs ks steps nil g c)))
                (equal (car (nth (+ 2 k) steps)) :cut)
                (consp (nthcdr (+ 2 k) steps))
                (equal (mv-nth 0 (fn-bs-step (car (nth k (fn-bs-run bs ks steps nil g c)))
                                             (cdr (nth k (fn-bs-run bs ks steps nil g c)))
                                             (nth (1+ k) steps) :ok g c))
                       :ok))
           (and (consp (nth (+ 2 k) (fn-bs-run bs ks steps nil g c)))
                (equal (nth (+ 2 k) (fn-bs-run bs ks steps nil g c))
                       (cons (mv-nth 1 (fn-bs-step (car (nth k (fn-bs-run bs ks steps nil g c)))
                                                   (cdr (nth k (fn-bs-run bs ks steps nil g c)))
                                                   (nth (1+ k) steps) :ok g c))
                             (mv-nth 2 (fn-bs-step (car (nth k (fn-bs-run bs ks steps nil g c)))
                                                   (cdr (nth k (fn-bs-run bs ks steps nil g c)))
                                                   (nth (1+ k) steps) :ok g c))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-k0c-run-nth-consp-step-forward)
                 (:instance fn-bs-k0c-nth-succ)
                 (:instance fn-bs-k0b-run-nth-consp-forward)
                 (:instance fn-bs-k0b-consp-nthcdr-earlier (n (1+ k)) (x steps))
                 (:instance fn-bs-k0c-cut-pair-is-previous-pair (k (1+ k)) (outs nil)))
           :in-theory (e/d () (fn-bs-run fn-bs-step nth nthcdr)))))
(defthm fn-bs-k0b-covered-of-pair
  (implies (and (equal p (cons a b)) (fn-bs-k0-coveredp a b))
           (fn-bs-k0-coveredp (car p) (cdr p)))
  :rule-classes nil)
(defthm fn-bs-k0b-cut-after-step
  (implies (and (and (natp k)
                (member-equal (car (nth k steps)) '(:observe :cut :fsync-file :fsync-dir))
                (consp (nth k (fn-bs-run bs ks steps nil g c)))
                (equal (car (nth (+ 2 k) steps)) :cut)
                (consp (nthcdr (+ 2 k) steps))
                (equal (mv-nth 0 (fn-bs-step (car (nth k (fn-bs-run bs ks steps nil g c)))
                                             (cdr (nth k (fn-bs-run bs ks steps nil g c)))
                                             (nth (1+ k) steps) :ok g c))
                       :ok))
                (fn-bs-k0-step-inputp (car (nth k (fn-bs-run bs ks steps nil g c)))
                                      (cdr (nth k (fn-bs-run bs ks steps nil g c)))
                                      (nth (1+ k) steps) :ok))
           (let ((p (nth (+ 2 k) (fn-bs-run bs ks steps nil g c))))
             (fn-bs-k0-coveredp (car p) (cdr p))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-k0b-cut-after-step-pair
                 (:instance fn-bs-k0b-covered-of-pair
                  (p (nth (+ 2 k) (fn-bs-run bs ks steps nil g c)))
                  (a (mv-nth 1 (fn-bs-step (car (nth k (fn-bs-run bs ks steps nil g c)))
                                           (cdr (nth k (fn-bs-run bs ks steps nil g c)))
                                           (nth (1+ k) steps) :ok g c)))
                  (b (mv-nth 2 (fn-bs-step (car (nth k (fn-bs-run bs ks steps nil g c)))
                                           (cdr (nth k (fn-bs-run bs ks steps nil g c)))
                                           (nth (1+ k) steps) :ok g c))))
                 (:instance fn-bs-step-preserves-k0-coverage
                  (bs (car (nth k (fn-bs-run bs ks steps nil g c))))
                  (ks (cdr (nth k (fn-bs-run bs ks steps nil g c))))
                  (step (nth (1+ k) steps)) (outcome :ok) (groups g) (capacity c)))
           :in-theory (theory 'minimal-theory))))
(defthm fn-bs-k0b-run-consp-backward
  (implies (and (natp k) (consp (nth (1+ k) (fn-bs-run bs ks steps outs g c))))
           (consp (nth k (fn-bs-run bs ks steps outs g c))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-bs-k0c-ind k bs ks steps outs g c)
           :expand ((fn-bs-run bs ks steps outs g c))
           :in-theory (e/d (nth) (fn-bs-run fn-bs-step)))))
(defthm fn-bs-k0b-syscall-carries-kernel
  (implies (and (natp k) (consp (nth (1+ k) (fn-bs-run bs ks steps nil g c)))
                (not (equal (car (nth (1+ k) steps)) :observe)))
           (equal (cdr (nth (1+ k) (fn-bs-run bs ks steps nil g c)))
                  (cdr (nth k (fn-bs-run bs ks steps nil g c)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-k0c-nth-succ
                 (:instance fn-bs-k0s-syscall-step-keeps-kernel
                  (bs (car (nth k (fn-bs-run bs ks steps nil g c))))
                  (ks (cdr (nth k (fn-bs-run bs ks steps nil g c))))
                  (step (nth (1+ k) steps)) (outcome :ok)))
           :in-theory (e/d () (fn-bs-run fn-bs-step nth)))))
(defthm fn-bs-k0b-record-program-steps
  (let ((prog (fn-bs-record-program stage name frame)))
    (and (equal (car (nth 0 prog)) :create) (equal (car (car prog)) :create) (equal (car (nth 1 prog)) :cut)
         (equal (car (nth 2 prog)) :write-all) (equal (car (nth 3 prog)) :cut)
         (equal (car (nth 4 prog)) :fsync-file) (consp prog)
         (equal (nth 5 prog) '(:observe (:record-file :ok)))
         (equal (car (nth 6 prog)) :cut)
         (equal (car (nth 7 prog)) :link)
         (equal (car (nth 8 prog)) :cut)
         (equal (nth 9 prog) '(:observe (:record-link :ok)))
         (equal (car (nth 10 prog)) :cut) (consp (nthcdr 10 prog))
         (equal (nth 11 prog) '(:fsync-dir :transactions))
         (equal (car (nth 12 prog)) :cut) (consp (nthcdr 12 prog))
         (equal (nth 13 prog) '(:observe (:record-dir :ok)))
         (equal (car (nth 14 prog)) :cut) (consp (nthcdr 14 prog))
         (equal (nth 15 prog) (list :unlink :staging stage))
         (equal (car (nth 16 prog)) :cut) (consp (nthcdr 16 prog))
         (equal (nth 17 prog) '(:fsync-dir :staging))
         (equal (car (nth 18 prog)) :cut) (consp (nthcdr 18 prog))))
  :hints (("Goal" :in-theory (enable fn-bs-record-program))))

(defun fn-bs-k0p-s1 (bs stage)
  (declare (xargs :guard t :verify-guards nil))
  (mv-let (r s1) (fn-bs-create bs :staging stage :ok) (declare (ignore r)) s1))
(defun fn-bs-k0p-s2 (bs stage octets)
  (declare (xargs :guard t :verify-guards nil))
  (let ((s1 (fn-bs-k0p-s1 bs stage)))
    (mv-let (r s2) (fn-bs-write s1 (fn-bs-lookup s1 :staging stage) 0 octets :ok) (declare (ignore r)) s2)))
(defun fn-bs-k0p-s3 (bs stage octets)
  (declare (xargs :guard t :verify-guards nil))
  (let ((s2 (fn-bs-k0p-s2 bs stage octets)))
    (mv-let (r s3) (fn-bs-fsync-file s2 (fn-bs-lookup s2 :staging stage) :ok) (declare (ignore r)) s3)))
(defthm fn-bs-k0p-related-quiet-outside-visible-phases
  (implies (and (fn-bs-store-relation bs ks) (not (fn-bs-replay-visiblep ks))
                (not (fn-sf-frontier-new-visiblep ks)) (not (fn-sf-record-present-visiblep ks)))
           (and (not (fn-bs-ops-for-dir (fn-bs-pending bs) :root))
                (not (fn-bs-ops-for-dir (fn-bs-pending bs) :transactions))))
  :rule-classes nil
  :hints (("Goal" :use (fn-bs-store-relation-window-unfolds fn-bs-pending-matches-phase-unfolds)
           :in-theory (e/d () (fn-bs-store-relation fn-bs-pending-matches-phase fn-sf-crash-imagep
                               fn-bs-pending-shape-okp fn-sf-frontier-new-visiblep fn-sf-record-present-visiblep
                               fn-bs-durable-records fn-bs-durable-content)))))
(defthm fn-bs-k0p-stage-lookups
  (implies (and (fn-bs-namep stage) (not (fn-bs-lookup bs :staging stage)))
           (and (equal (fn-bs-lookup (fn-bs-k0p-s1 bs stage) :staging stage) (fn-bs-next-ino bs))
                (equal (fn-bs-lookup (fn-bs-k0p-s2 bs stage octets) :staging stage) (fn-bs-next-ino bs))
                (consp (assoc-equal (fn-bs-next-ino bs) (fn-bs-inodes (fn-bs-k0p-s1 bs stage))))))
  :hints (("Goal" :in-theory (e/d (fn-bs-k0p-s1 fn-bs-k0p-s2 fn-bs-create fn-bs-k6-write-keeps-lookup) (fn-bs-lookup fn-bs-write)))))
(defthm fn-bs-k0p-write-keeps-authority-list
  (equal (fn-bs-authority-inode-list (mv-nth 1 (fn-bs-write s ino offset octets :ok)))
         (fn-bs-authority-inode-list s))
  :hints (("Goal" :in-theory (enable fn-bs-write fn-bs-authority-inode-list fn-bs-durable-entry
                                     fn-bs-pending-entry-targets))))
(defthm fn-bs-k0p-write-keeps-dir-ops
  (equal (fn-bs-ops-for-dir (fn-bs-pending (mv-nth 1 (fn-bs-write s ino offset octets :ok))) d)
         (fn-bs-ops-for-dir (fn-bs-pending s) d))
  :hints (("Goal" :in-theory (enable fn-bs-write fn-bs-ops-for-dir-of-append fn-bs-ops-for-dir))))
(defthm fn-bs-k0p-fsync-file-keeps-dir-ops
  (equal (fn-bs-ops-for-dir (fn-bs-pending (mv-nth 1 (fn-bs-fsync-file s ino :ok))) d)
         (fn-bs-ops-for-dir (fn-bs-pending s) d))
  :hints (("Goal" :in-theory (enable fn-bs-fsync-file fn-bs-fence-file))))
(defthm fn-bs-k0p-stage-dir-ops2
  (implies (not (equal d :staging))
           (and (equal (fn-bs-ops-for-dir (fn-bs-pending (fn-bs-k0p-s1 bs stage)) d)
                       (fn-bs-ops-for-dir (fn-bs-pending bs) d))
                (equal (fn-bs-ops-for-dir (fn-bs-pending (fn-bs-k0p-s2 bs stage octets)) d)
                       (fn-bs-ops-for-dir (fn-bs-pending bs) d))
                (equal (fn-bs-ops-for-dir (fn-bs-pending (fn-bs-k0p-s3 bs stage octets)) d)
                       (fn-bs-ops-for-dir (fn-bs-pending bs) d))))
  :hints (("Goal" :in-theory (e/d (fn-bs-k0p-s1 fn-bs-k0p-s2 fn-bs-k0p-s3 fn-bs-create fn-bs-ops-for-dir-of-append)
                                  (fn-bs-lookup fn-bs-write fn-bs-fsync-file)))
          (and stable-under-simplificationp '(:in-theory (e/d (fn-bs-ops-for-dir) (fn-bs-lookup fn-bs-write fn-bs-fsync-file))))))
(defthm fn-bs-k0p-stage-steps
  (implies (and (fn-bs-namep stage) (not (fn-bs-lookup bs :staging stage)))
           (and (equal (fn-bs-step bs k (list :create :staging stage) :ok g c)
                       (list :ok (fn-bs-k0p-s1 bs stage) k))
                (equal (fn-bs-step (fn-bs-k0p-s1 bs stage) k (list :write-all :staging stage octets) :ok g c)
                       (list :ok (fn-bs-k0p-s2 bs stage octets) k))
                (equal (fn-bs-step (fn-bs-k0p-s2 bs stage octets) k (list :fsync-file :staging stage) :ok g c)
                       (list :ok (fn-bs-k0p-s3 bs stage octets) k))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-bs-step fn-bs-k0p-s2 fn-bs-k0p-s3 fn-bs-k0b-write-ok-result fn-bs-k0b-fsync-ok-results)
                           (fn-bs-lookup fn-bs-write fn-bs-fsync-file fn-bs-k0p-s1)))
          (and stable-under-simplificationp '(:in-theory (e/d (fn-bs-step fn-bs-k0p-s1 fn-bs-create fn-bs-write) (fn-bs-lookup fn-bs-fsync-file))))))
(defmacro fn-bs-k0p-stage-hyps ()
  '(and (fn-bs-store-relation bs ks)
        (not (fn-bs-replay-visiblep ks))
        (not (fn-bs-ops-for-dir (fn-bs-pending bs) :root))
        (not (fn-bs-ops-for-dir (fn-bs-pending bs) :transactions))
        (fn-bs-namep stage)
        (not (fn-bs-lookup bs :staging stage))
        (fn-cbor-octet-listp octets)))
(defthm fn-bs-k0p-s1-fresh
  (implies (and (fn-bs-store-relation bs ks) (fn-bs-namep stage) (not (fn-bs-lookup bs :staging stage)))
           (not (member-equal (fn-bs-next-ino bs) (fn-bs-authority-inode-list (fn-bs-k0p-s1 bs stage)))))
  :hints (("Goal" :use ((:instance fn-bs-k0-staging-create-fresh-facts (b bs) (k ks)))
           :in-theory (e/d (fn-bs-k0p-s1) (fn-bs-store-relation fn-bs-lookup fn-bs-authority-inode-list fn-bs-create)))))
(defthm fn-bs-k0p-s2-authority
  (equal (fn-bs-authority-inode-list (fn-bs-k0p-s2 bs stage octets))
         (fn-bs-authority-inode-list (fn-bs-k0p-s1 bs stage)))
  :hints (("Goal" :in-theory (e/d (fn-bs-k0p-s2) (fn-bs-k0p-s1 fn-bs-authority-inode-list fn-bs-lookup)))))
(defthm fn-bs-k0p-stage-step-inputs
  (implies (fn-bs-k0p-stage-hyps)
           (and (fn-bs-k0-step-inputp bs ks (list :create :staging stage) :ok)
                (implies (fn-bs-store-relation (fn-bs-k0p-s1 bs stage) ks)
                         (fn-bs-k0-step-inputp (fn-bs-k0p-s1 bs stage) ks
                                               (list :write-all :staging stage octets) :ok))
                (implies (fn-bs-store-relation (fn-bs-k0p-s2 bs stage octets) ks)
                         (fn-bs-k0-step-inputp (fn-bs-k0p-s2 bs stage octets) ks
                                               (list :fsync-file :staging stage) :ok))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-store-relation-unfolds))
           :in-theory (e/d (fn-bs-k0-step-inputp fn-bs-k0p-stage-dir-ops2 fn-bs-k0p-stage-lookups fn-bs-statep)
                           (fn-bs-store-relation fn-bs-lookup fn-bs-authority-inode-list fn-bs-k0p-s1 fn-bs-k0p-s2
                            fn-bs-k0s-marker-pendingp fn-bs-k0-coveredp fn-bs-replay-visiblep
                            fn-bs-crash-choicesp fn-bs-ops-for-ino fn-bs-k0-observation-inputp)))))
(defthm fn-bs-k0p-stage-pairs-by-step
  (implies (fn-bs-k0p-stage-hyps)
           (and (fn-bs-store-relation (fn-bs-k0p-s1 bs stage) ks)
                (fn-bs-store-relation (fn-bs-k0p-s2 bs stage octets) ks)
                (fn-bs-store-relation (fn-bs-k0p-s3 bs stage octets) ks)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-k0p-stage-step-inputs
                 (:instance fn-bs-k0p-stage-steps (k ks) (g nil) (c nil))
                 (:instance fn-bs-step-preserves-k0-coverage (step (list :create :staging stage)) (outcome :ok) (groups nil) (capacity nil))
                 (:instance fn-bs-step-preserves-k0-coverage (bs (fn-bs-k0p-s1 bs stage)) (step (list :write-all :staging stage octets)) (outcome :ok) (groups nil) (capacity nil))
                 (:instance fn-bs-step-preserves-k0-coverage (bs (fn-bs-k0p-s2 bs stage octets)) (step (list :fsync-file :staging stage)) (outcome :ok) (groups nil) (capacity nil))
                 (:instance fn-bs-k0b-covered-without-root-marker-is-related (b (fn-bs-k0p-s1 bs stage)) (k ks))
                 (:instance fn-bs-k0b-covered-without-root-marker-is-related (b (fn-bs-k0p-s2 bs stage octets)) (k ks))
                 (:instance fn-bs-k0b-covered-without-root-marker-is-related (b (fn-bs-k0p-s3 bs stage octets)) (k ks))
                 (:instance fn-bs-k0b-root-quiet-has-no-root-marker (ops (fn-bs-pending (fn-bs-k0p-s1 bs stage))))
                 (:instance fn-bs-k0b-root-quiet-has-no-root-marker (ops (fn-bs-pending (fn-bs-k0p-s2 bs stage octets))))
                 (:instance fn-bs-k0b-root-quiet-has-no-root-marker (ops (fn-bs-pending (fn-bs-k0p-s3 bs stage octets)))))
           :in-theory (e/d (fn-bs-k0p-stage-dir-ops2)
                           (fn-bs-store-relation fn-bs-k0-coveredp fn-bs-k0s-marker-pendingp fn-bs-k0-step-inputp
                            fn-bs-step fn-bs-lookup fn-bs-k0m-has-root-marker fn-bs-k0b-root-quiet-has-no-root-marker
                            fn-bs-k0p-s1 fn-bs-k0p-s2 fn-bs-k0p-s3 fn-bs-replay-visiblep)))))
(defthm fn-bs-k0p-frontier-run-prefix
  (implies (and (fn-bs-namep stage) (not (fn-bs-lookup bs :staging stage)))
           (equal (fn-bs-run bs ks (fn-bs-frontier-program stage octets) nil g c)
                  (let* ((k0 (fn-sf-dispatch ks '(:start-frontier) g c))
                         (k6 (fn-sf-dispatch k0 '(:frontier-file :ok) g c))
                         (s1 (fn-bs-k0p-s1 bs stage)) (s2 (fn-bs-k0p-s2 bs stage octets))
                         (s3 (fn-bs-k0p-s3 bs stage octets)))
                    (list* (cons bs k0) (cons s1 k0) (cons s1 k0) (cons s2 k0) (cons s2 k0)
                           (cons s3 k0) (cons s3 k6) (cons s3 k6)
                           (fn-bs-run s3 k6 (nthcdr 8 (fn-bs-frontier-program stage octets)) nil g c)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-k0p-stage-steps (k (fn-sf-dispatch ks '(:start-frontier) g c))))
           :expand ((:free (b k s) (fn-bs-run b k s nil g c)))
           :in-theory (e/d (fn-bs-frontier-program fn-bs-k0s-observe-step fn-bs-k0c-cut-step-is-identity)
                           (fn-bs-step fn-bs-run fn-bs-lookup fn-sf-dispatch fn-bs-k0p-s1 fn-bs-k0p-s2 fn-bs-k0p-s3)))))
(defthm fn-bs-k0p-record-run-prefix
  (implies (and (fn-bs-namep stage) (not (fn-bs-lookup bs :staging stage)))
           (equal (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil g c)
                  (let* ((k5 (fn-sf-dispatch ks '(:record-file :ok) g c))
                         (s1 (fn-bs-k0p-s1 bs stage)) (s2 (fn-bs-k0p-s2 bs stage frame))
                         (s3 (fn-bs-k0p-s3 bs stage frame)))
                    (list* (cons s1 ks) (cons s1 ks) (cons s2 ks) (cons s2 ks)
                           (cons s3 ks) (cons s3 k5) (cons s3 k5)
                           (fn-bs-run s3 k5 (nthcdr 7 (fn-bs-record-program stage name frame)) nil g c)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-k0p-stage-steps (k ks) (octets frame)))
           :expand ((:free (b k s) (fn-bs-run b k s nil g c)))
           :in-theory (e/d (fn-bs-record-program fn-bs-k0s-observe-step fn-bs-k0c-cut-step-is-identity)
                           (fn-bs-step fn-bs-run fn-bs-lookup fn-sf-dispatch fn-bs-k0p-s1 fn-bs-k0p-s2 fn-bs-k0p-s3)))))
(defthm fn-bs-k0p-frontier-entry-facts
  (implies (and (fn-bs-store-relation bs ks) (fn-bs-frontier-inputp ks stage octets))
           (let ((k0 (fn-sf-dispatch ks '(:start-frontier) g c)))
             (and (fn-bs-store-relation bs k0)
                  (not (fn-bs-replay-visiblep k0))
                  (not (fn-sf-frontier-new-visiblep k0))
                  (not (fn-sf-record-present-visiblep k0)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-step-preserves-k0-coverage (step '(:observe (:start-frontier))) (outcome :ok) (groups g) (capacity c))
                 (:instance fn-bs-k0b-covered-without-root-marker-is-related (b bs) (k (fn-sf-dispatch ks '(:start-frontier) g c)))
                 (:instance fn-bs-k0b-relation-has-no-root-marker (b bs) (k ks))
                 fn-bs-store-relation-unfolds)
           :in-theory (e/d (fn-bs-k0-step-inputp fn-bs-k0-observation-inputp fn-bs-frontier-noncommit-observationp
                            fn-bs-k0s-observe-step fn-bs-frontier-inputp fn-sf-dispatch fn-sf-start-frontier
                            fn-bs-replay-visiblep fn-sf-frontier-new-visiblep fn-sf-record-present-visiblep)
                           (fn-bs-store-relation fn-bs-k0-coveredp fn-bs-k0m-has-root-marker fn-sf-statep
                            fn-bs-k0b-relation-has-no-root-marker)))))
(defthm fn-bs-k0-frontier-created-and-written-cut-relation-by-step
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-frontier-inputp ks stage octets)
                (not (fn-bs-lookup bs :staging stage)))
           (let ((run (fn-bs-run bs ks (fn-bs-frontier-program stage octets) nil groups capacity)))
             (and (fn-bs-store-relation (car (nth 2 run)) (cdr (nth 2 run)))
                  (fn-bs-store-relation (car (nth 4 run)) (cdr (nth 4 run))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-k0p-frontier-run-prefix (g groups) (c capacity))
                 (:instance fn-bs-k0p-frontier-entry-facts (g groups) (c capacity))
                 (:instance fn-bs-k0p-related-quiet-outside-visible-phases (ks (fn-sf-dispatch ks '(:start-frontier) groups capacity)))
                 (:instance fn-bs-k0p-stage-pairs-by-step (ks (fn-sf-dispatch ks '(:start-frontier) groups capacity))))
           :in-theory (e/d (fn-bs-frontier-inputp)
                           (fn-bs-store-relation fn-bs-run fn-bs-frontier-program fn-sf-dispatch fn-bs-lookup
                            fn-bs-k0p-s1 fn-bs-k0p-s2 fn-bs-k0p-s3 fn-bs-replay-visiblep
                            fn-sf-frontier-new-visiblep fn-sf-record-present-visiblep)))))
(defthm fn-bs-k0-frontier-staged-durable-cut-relation-by-step
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-frontier-inputp ks stage octets)
                (not (fn-bs-lookup bs :staging stage)))
           (let ((p (nth 7 (fn-bs-run bs ks (fn-bs-frontier-program stage octets) nil groups capacity))))
             (fn-bs-store-relation (car p) (cdr p))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-k0p-frontier-run-prefix (g groups) (c capacity))
                 (:instance fn-bs-k0p-frontier-entry-facts (g groups) (c capacity))
                 (:instance fn-bs-k0p-related-quiet-outside-visible-phases (ks (fn-sf-dispatch ks '(:start-frontier) groups capacity)))
                 (:instance fn-bs-k0p-stage-pairs-by-step (ks (fn-sf-dispatch ks '(:start-frontier) groups capacity)))
                 (:instance fn-bs-step-preserves-k0-coverage (bs (fn-bs-k0p-s3 bs stage octets))
                  (ks (fn-sf-dispatch ks '(:start-frontier) groups capacity))
                  (step '(:observe (:frontier-file :ok))) (outcome :ok))
                 (:instance fn-bs-k0b-covered-without-root-marker-is-related
                  (b (fn-bs-k0p-s3 bs stage octets))
                  (k (fn-sf-dispatch (fn-sf-dispatch ks '(:start-frontier) groups capacity) '(:frontier-file :ok) groups capacity)))
                 (:instance fn-bs-k0b-root-quiet-has-no-root-marker (ops (fn-bs-pending (fn-bs-k0p-s3 bs stage octets)))))
           :in-theory (e/d (fn-bs-frontier-inputp fn-bs-k0-step-inputp fn-bs-k0-observation-inputp
                            fn-bs-frontier-noncommit-observationp fn-bs-k0s-observe-step fn-bs-k0p-stage-dir-ops2)
                           (fn-bs-store-relation fn-bs-run fn-bs-frontier-program fn-sf-dispatch fn-bs-lookup
                            fn-bs-k0p-s1 fn-bs-k0p-s2 fn-bs-k0p-s3 fn-bs-replay-visiblep fn-bs-k0-coveredp
                            fn-bs-k0m-has-root-marker fn-bs-k0b-root-quiet-has-no-root-marker
                            fn-sf-frontier-new-visiblep fn-sf-record-present-visiblep)))))
(defthm fn-bs-k0p-record-entry-phase
  (implies (fn-bs-record-inputp ks stage name frame)
           (and (not (fn-bs-replay-visiblep ks))
                (not (fn-sf-frontier-new-visiblep ks))
                (not (fn-sf-record-present-visiblep ks))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-bs-record-inputp fn-bs-replay-visiblep fn-sf-frontier-new-visiblep
                                     fn-sf-record-present-visiblep))))
(defthm fn-bs-k0-record-created-and-written-cut-relation-by-step
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-record-inputp ks stage name frame)
                (not (fn-bs-lookup bs :staging stage)))
           (let ((run (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity)))
             (and (fn-bs-store-relation (car (nth 1 run)) (cdr (nth 1 run)))
                  (fn-bs-store-relation (car (nth 3 run)) (cdr (nth 3 run))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-k0p-record-run-prefix (g groups) (c capacity))
                 fn-bs-k0p-record-entry-phase
                 fn-bs-k0p-related-quiet-outside-visible-phases
                 (:instance fn-bs-k0p-stage-pairs-by-step (octets frame)))
           :in-theory (e/d (fn-bs-record-inputp)
                           (fn-bs-store-relation fn-bs-run fn-bs-record-program fn-sf-dispatch fn-bs-lookup
                            fn-bs-k0p-s1 fn-bs-k0p-s2 fn-bs-k0p-s3 fn-bs-replay-visiblep
                            fn-sf-frontier-new-visiblep fn-sf-record-present-visiblep)))))
(defthm fn-bs-k0p-record-staged-durable-pair
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-record-inputp ks stage name frame)
                (not (fn-bs-lookup bs :staging stage)))
           (fn-bs-store-relation (fn-bs-k0p-s3 bs stage frame) (fn-sf-dispatch ks '(:record-file :ok) g c)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-k0p-record-entry-phase
                 fn-bs-k0p-related-quiet-outside-visible-phases
                 (:instance fn-bs-k0p-stage-pairs-by-step (octets frame))
                 (:instance fn-bs-step-preserves-k0-coverage (bs (fn-bs-k0p-s3 bs stage frame))
                  (step '(:observe (:record-file :ok))) (outcome :ok) (groups g) (capacity c))
                 (:instance fn-bs-k0b-covered-without-root-marker-is-related
                  (b (fn-bs-k0p-s3 bs stage frame)) (k (fn-sf-dispatch ks '(:record-file :ok) g c)))
                 (:instance fn-bs-k0b-root-quiet-has-no-root-marker (ops (fn-bs-pending (fn-bs-k0p-s3 bs stage frame)))))
           :in-theory (e/d (fn-bs-record-inputp fn-bs-k0-step-inputp fn-bs-k0-observation-inputp
                            fn-bs-k0s-observe-step fn-bs-k0p-stage-dir-ops2)
                           (fn-bs-store-relation fn-sf-dispatch fn-bs-lookup
                            fn-bs-k0p-s1 fn-bs-k0p-s2 fn-bs-k0p-s3 fn-bs-replay-visiblep fn-bs-k0-coveredp
                            fn-bs-k0m-has-root-marker fn-bs-k0b-root-quiet-has-no-root-marker
                            fn-bs-frontier-noncommit-observationp
                            fn-sf-frontier-new-visiblep fn-sf-record-present-visiblep)))))
(defthm fn-bs-k0-record-staged-durable-cut-relation-by-step
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-record-inputp ks stage name frame)
                (not (fn-bs-lookup bs :staging stage)))
           (let ((p (nth 6 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity))))
             (fn-bs-store-relation (car p) (cdr p))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-k0p-record-run-prefix (g groups) (c capacity))
                 (:instance fn-bs-k0p-record-staged-durable-pair (g groups) (c capacity)))
           :in-theory (e/d (fn-bs-record-inputp)
                           (fn-bs-store-relation fn-bs-run fn-bs-record-program fn-sf-dispatch fn-bs-lookup
                            fn-bs-k0p-s1 fn-bs-k0p-s2 fn-bs-k0p-s3)))))
(defthm fn-bs-k0p-record-file-kernel
  (implies (and (fn-sf-statep ks) (equal (fn-sf-phase ks) :record-staged))
           (let ((k5 (fn-sf-dispatch ks '(:record-file :ok) g c)))
             (and (equal (fn-sf-phase k5) :record-data-durable)
                  (equal (fn-sf-records k5) (fn-sf-records ks))
                  (equal (fn-sf-record-candidate k5) (fn-sf-record-candidate ks)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-sf-dispatch fn-sf-record-file-result) (fn-sf-statep)))))
(defthm fn-bs-k0p-staged-candidate-is-next-sequence
  (implies (and (fn-sf-statep ks)
                (equal (fn-sf-phase ks) :record-staged))
           (equal (fn-store-event-sequence (fn-sf-record-candidate ks))
                  (len (fn-sf-records ks))))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (e/d (fn-sf-statep fn-sf-phase-shapep
                 fn-sf-record-phasep fn-sf-candidatep)
                (fn-store-event-sequence fn-store-event-p
                 fn-sf-record-listp fn-sf-success-listp
                 fn-sf-shapep)))))
(defthm fn-bs-k0p-record-s3-facts
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-record-inputp ks stage name frame)
                (not (fn-bs-lookup bs :staging stage)))
           (let ((s3 (fn-bs-k0p-s3 bs stage frame)) (n (fn-bs-next-ino bs)))
             (and (equal (fn-bs-lookup s3 :staging stage) n)
                  (fn-bs-fencedp s3 n)
                  (equal (fn-bs-durable-content s3 n) frame)
                  (consp (assoc-equal n (fn-bs-inodes s3)))
                  (equal (fn-bs-dirs s3) (fn-bs-dirs bs))
                  (not (fn-bs-lookup s3 :transactions name))
                  (fn-bs-inop n))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-k0p-record-run-prefix (g nil) (c nil))
                 fn-bs-store-relation-unfolds
                 (:instance fn-bs-k0s-octets-are-true-lists (xs frame))
                 (:instance fn-bs-k6-file-cut-source-is-fenced-frame (groups nil) (capacity nil))
                 (:instance fn-bs-k0-file-cut-has-new-inode (groups nil) (capacity nil))
                 (:instance fn-bs-k6-file-cut-dirs-are-input-dirs (groups nil) (capacity nil))
                 (:instance fn-bs-k6-related-input-file-cut-final-name-absent (groups nil) (capacity nil))
                 (:instance fn-bs-k6-state-next-ino-is-inop))
           :in-theory (e/d (fn-bs-record-inputp) (fn-bs-store-relation fn-bs-run fn-bs-record-program fn-sf-dispatch fn-bs-lookup
                               fn-bs-k0p-s1 fn-bs-k0p-s2 fn-bs-k0p-s3 fn-bs-statep fn-bs-k0s-octets-are-true-lists
                               fn-bs-fencedp fn-bs-durable-content fn-bs-inop)))))
(defthm fn-bs-k0p-link-ok-result
  (implies (and (fn-bs-inop (fn-bs-lookup b sdir sname)) (not (fn-bs-lookup b ddir dname)))
           (equal (mv-nth 0 (fn-bs-step b k (list :link sdir sname ddir dname) :ok g c)) :ok))
  :hints (("Goal" :in-theory (e/d (fn-bs-step fn-bs-link) (fn-bs-lookup fn-bs-inop)))))
(defthm fn-bs-k0p-record-staged-durable-records
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-record-inputp ks stage name frame)
                (not (fn-bs-lookup bs :staging stage)))
           (equal (fn-bs-durable-records (fn-bs-k0p-s3 bs stage frame)) (fn-sf-records ks)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-k0p-record-staged-durable-pair (g nil) (c nil))
                 fn-bs-k0p-record-s3-facts fn-bs-store-relation-unfolds
                 (:instance fn-bs-k0p-record-file-kernel (g nil) (c nil))
                 (:instance fn-bs-store-relation-window-unfolds (bs (fn-bs-k0p-s3 bs stage frame))
                  (ks (fn-sf-dispatch ks '(:record-file :ok) nil nil)))
                 (:instance fn-bs-durable-records-length (bs (fn-bs-k0p-s3 bs stage frame))
                  (ks (fn-sf-dispatch ks '(:record-file :ok) nil nil)))
                 fn-bs-k6-related-staged-durable-name-count-is-record-count)
           :in-theory (e/d (fn-bs-record-inputp fn-sf-crash-imagep fn-bs-replay-visiblep fn-bs-durable-names)
                           (fn-bs-store-relation fn-sf-dispatch fn-bs-lookup fn-bs-k0p-s1 fn-bs-k0p-s2 fn-bs-k0p-s3
                            fn-bs-durable-records fn-bs-pending-matches-phase fn-sf-statep fn-bs-statep
                            fn-sf-frontier-new-visiblep fn-sf-record-present-visiblep)))))
(defthm fn-bs-k0p-record-link-inputs
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-record-inputp ks stage name frame)
                (not (fn-bs-lookup bs :staging stage)))
           (let ((s3 (fn-bs-k0p-s3 bs stage frame)) (k5 (fn-sf-dispatch ks '(:record-file :ok) g c)))
             (and (fn-bs-k0-step-inputp s3 k5 (list :link :staging stage :transactions name) :ok)
                  (equal (mv-nth 0 (fn-bs-step s3 k5 (list :link :staging stage :transactions name) :ok g c)) :ok))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-k0p-record-staged-durable-pair fn-bs-k0p-record-s3-facts fn-bs-k0p-record-file-kernel
                 fn-bs-k0p-record-staged-durable-records fn-bs-store-relation-unfolds
                 fn-bs-k0p-staged-candidate-is-next-sequence
                 fn-bs-k6-related-staged-durable-name-count-is-record-count
                 fn-bs-k0p-record-entry-phase fn-bs-k0p-related-quiet-outside-visible-phases)
           :in-theory (e/d (fn-bs-record-inputp fn-bs-k0-step-inputp fn-bs-replay-visiblep fn-sf-record-present-visiblep
                            fn-bs-durable-names fn-bs-k8-record-of-durable-is-durable-content fn-bs-k0p-stage-dir-ops2)
                           (fn-bs-store-relation fn-sf-dispatch fn-bs-lookup fn-bs-k0p-s1 fn-bs-k0p-s2 fn-bs-k0p-s3
                            fn-bs-durable-records fn-sf-statep fn-bs-statep fn-bs-fencedp fn-bs-durable-content
                            fn-bs-record-of-octets fn-store-event-sequence fn-bs-inop
                            fn-sf-frontier-new-visiblep)))))
(defthm fn-bs-k0p-link-step-keeps-root-marker-status
  (implies (not (equal ddir :root))
           (equal (fn-bs-k0m-has-root-marker (fn-bs-pending (mv-nth 1 (fn-bs-step b k (list :link sdir sname ddir dname) o g c))))
                  (fn-bs-k0m-has-root-marker (fn-bs-pending b))))
  :hints (("Goal" :in-theory (e/d (fn-bs-step fn-bs-link fn-bs-k0m-has-root-marker) (fn-bs-lookup fn-bs-inop)))))
(defthm fn-bs-k0p-record-program-link-steps
  (let ((prog (fn-bs-record-program stage name frame)))
    (and (equal (nth 7 prog) (list :link :staging stage :transactions name))
         (consp (nthcdr 8 prog))))
  :hints (("Goal" :in-theory (enable fn-bs-record-program))))
(defthm fn-bs-k0-record-linked-cut-relation-by-step
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-record-inputp ks stage name frame)
                (not (fn-bs-lookup bs :staging stage)))
           (let ((p (nth 8 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity))))
             (fn-bs-store-relation (car p) (cdr p))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-k0p-record-run-prefix (g groups) (c capacity))
                 (:instance fn-bs-k0p-record-link-inputs (g groups) (c capacity))
                 fn-bs-k0p-record-entry-phase fn-bs-k0p-related-quiet-outside-visible-phases
                 (:instance fn-bs-k0b-root-quiet-has-no-root-marker (ops (fn-bs-pending (fn-bs-k0p-s3 bs stage frame))))
                 (:instance fn-bs-k0b-cut-after-step (k 6) (steps (fn-bs-record-program stage name frame)) (g groups) (c capacity))
                 (:instance fn-bs-k0b-cut-after-step-pair (k 6) (steps (fn-bs-record-program stage name frame)) (g groups) (c capacity))
                 (:instance fn-bs-k0b-covered-without-root-marker-is-related
                  (b (car (nth 8 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity))))
                  (k (cdr (nth 8 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity))))))
           :in-theory (e/d (fn-bs-k0b-record-program-steps fn-bs-k0p-record-program-link-steps fn-bs-k0p-stage-dir-ops2
                            fn-bs-k0p-link-step-keeps-root-marker-status fn-bs-record-inputp)
                           (fn-bs-store-relation fn-bs-run fn-bs-record-program fn-sf-dispatch fn-bs-lookup
                            fn-bs-k0p-s1 fn-bs-k0p-s2 fn-bs-k0p-s3 fn-bs-step fn-bs-k0-step-inputp
                            fn-bs-k0-coveredp fn-bs-k0m-has-root-marker fn-bs-k0b-root-quiet-has-no-root-marker
                            nth nthcdr fn-bs-replay-visiblep fn-sf-frontier-new-visiblep fn-sf-record-present-visiblep)))))
