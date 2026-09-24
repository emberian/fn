;; fn: K0 at the staging-only cuts, frontier-replaced/-attempted and the
;; error arms (P10, lane p10-k0-b).  Split from books/byte-store-k0 to keep
;; each book under the ten-second rule; the hypotheses are that book's.
;;
;; Under byte-store-k0's hypotheses (arbitrary related state, typed input,
;; absent stage):
;;   P-FRONTIER  frontier-created, frontier-written (staging-only steps),
;;       frontier-replaced, frontier-attempted (the rename transport, with
;;       the pair-6 authority-quiet premise restated and proved here).
;;   P-RECORD    record-created, record-written, record-stage-unlinked,
;;       record-staging-cleaned (staging-only steps; the unlink succeeds).
;;   Staging-only step lemmas over an arbitrary related state outside the
;;       recovery window: create, write to a non-authority inode, unlink and
;;       fence of a non-authority directory each preserve the relation.
;;   Error arms: the host's error observation applied to the pair where the
;;       EIO lands keeps the relation -- (:frontier-replace :error) after a
;;       rename that failed or was issued, (:frontier-dir :error) at the
;;       frontier barrier, (:record-link :error) after a failed link,
;;       (:record-dir :error) at the record barrier.  An EIO at any other
;;       campaign cut makes the host fence with no observation, so the state
;;       is the cut pair, already related above.
;;
;; OPEN: see the header of books/byte-store-k0.
(in-package "ACL2")
(include-book "byte-store-k0")

;; byte-store-k0's local list helpers, restated (they are local there).
(local
 (defthm fn-bs-k0t-pending-entry-targets-of-append
  (equal (fn-bs-pending-entry-targets (append a b))
         (append (fn-bs-pending-entry-targets a)
                 (fn-bs-pending-entry-targets b)))
  :hints (("Goal" :induct (append a b)
           :in-theory (enable fn-bs-pending-entry-targets)))))
(local
 (defthm fn-bs-k0t-all-fencedp-of-append
   (equal (fn-bs-all-fencedp bs (append a b))
          (and (fn-bs-all-fencedp bs a) (fn-bs-all-fencedp bs b)))
   :hints (("Goal" :induct (append a b) :in-theory (enable fn-bs-all-fencedp)))))
(local
 (defthm fn-bs-k0t-known-of-append
   (equal (fn-bs-inode-list-knownp bs (append a b))
          (and (fn-bs-inode-list-knownp bs a) (fn-bs-inode-list-knownp bs b)))
   :hints (("Goal" :induct (append a b) :in-theory (enable fn-bs-inode-list-knownp)))))
(local
 (defun fn-bs-k0t-fenced-in (p xs)
   (if (consp xs)
       (and (null (fn-bs-ops-for-ino p (car xs))) (fn-bs-k0t-fenced-in p (cdr xs)))
     t)))
(local
 (defthm fn-bs-k0t-all-fencedp-is-fenced-in
   (equal (fn-bs-all-fencedp bs xs) (fn-bs-k0t-fenced-in (fn-bs-pending bs) xs))
   :hints (("Goal" :in-theory (enable fn-bs-all-fencedp fn-bs-fencedp)))))
(local
 (defthm fn-bs-k0t-fenced-in-of-append-list
   (equal (fn-bs-k0t-fenced-in p (append a b))
          (and (fn-bs-k0t-fenced-in p a) (fn-bs-k0t-fenced-in p b)))))
(local
 (defthm fn-bs-k0t-fenced-in-ignores-entry-op
   (equal (fn-bs-k0t-fenced-in (append p (list (list :set-entry dir name ino))) xs)
          (fn-bs-k0t-fenced-in p xs))
   :hints (("Goal" :induct (len xs)
            :in-theory (enable fn-bs-ops-for-ino-of-append fn-bs-ops-for-ino)))))
(local
 (defun fn-bs-k0t-knownp-in (inodes xs)
   (if (consp xs)
       (and (consp (assoc-equal (car xs) inodes)) (fn-bs-k0t-knownp-in inodes (cdr xs)))
     t)))
(local
 (defthm fn-bs-k0t-known-list-is-knownp-in
   (equal (fn-bs-inode-list-knownp bs xs) (fn-bs-k0t-knownp-in (fn-bs-inodes bs) xs))
   :hints (("Goal" :in-theory (enable fn-bs-inode-list-knownp)))))
(local
 (defthm fn-bs-k0t-knownp-in-of-append
   (equal (fn-bs-k0t-knownp-in i (append a b))
          (and (fn-bs-k0t-knownp-in i a) (fn-bs-k0t-knownp-in i b)))))
(local (defthm fn-bs-k0t-writes-knownp-of-append
  (equal (fn-bs-writes-knownp (append a b) i)
         (and (fn-bs-writes-knownp a i) (fn-bs-writes-knownp b i)))
  :hints (("Goal" :induct (append a b) :in-theory (enable fn-bs-writes-knownp)))))
(local (defthm fn-bs-k0t-writes-nonemptyp-of-append
  (equal (fn-bs-writes-nonemptyp (append a b))
         (and (fn-bs-writes-nonemptyp a) (fn-bs-writes-nonemptyp b)))
  :hints (("Goal" :induct (append a b) :in-theory (enable fn-bs-writes-nonemptyp)))))
(local (defthm fn-bs-k0t-fenced-in-ignores-rename-ops
   (equal (fn-bs-k0t-fenced-in (append p (list (list :set-entry dir name ino)
                                                (list :del-entry sdir sname))) xs)
          (fn-bs-k0t-fenced-in p xs))
   :hints (("Goal" :induct (len xs)
            :in-theory (enable fn-bs-ops-for-ino-of-append fn-bs-ops-for-ino)))))
(local (defthm fn-bs-k0t-fencedp-ignores-rename-ops
   (equal (fn-bs-fencedp (fn-bs-make u i d (append p (list (list :set-entry dir name ino)
                                                          (list :del-entry sdir sname))) n) x)
          (fn-bs-fencedp (fn-bs-make u i d p n) x))
   :hints (("Goal" :in-theory (enable fn-bs-fencedp fn-bs-ops-for-ino-of-append fn-bs-ops-for-ino)))))
(local (defthm fn-bs-k0t-fencedp-of-own-fields
   (implies (fn-bs-statep b)
            (equal (fn-bs-fencedp (fn-bs-make (fn-bs-unit b) (fn-bs-inodes b) (fn-bs-dirs b)
                                              (fn-bs-pending b) (fn-bs-next-ino b)) x)
                   (fn-bs-fencedp b x)))
   :hints (("Goal" :in-theory (enable fn-bs-fencedp)))))

;; ---- lane p10-k0-b: frontier-replaced and frontier-attempted.
(local
 (defthm fn-bs-k0f-filter-inode-writes-keeps-dir-ops
   (equal (fn-bs-ops-for-dir (fn-bs-ops-not-for-ino ops ino) dir)
          (fn-bs-ops-for-dir ops dir))
   :hints (("Goal" :induct (fn-bs-ops-not-for-ino ops ino)
            :in-theory (enable fn-bs-ops-not-for-ino fn-bs-ops-for-dir)))))
(defthm fn-bs-k0-frontier-file-cut-authority-quiet-restated
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-frontier-inputp ks stage octets)
                (not (fn-bs-lookup bs :staging stage)))
           (let ((file (car (nth 5 (fn-bs-run bs ks (fn-bs-frontier-program stage octets)
                                              nil groups capacity)))))
             (and (equal (fn-bs-ops-for-dir (fn-bs-pending file) :root) nil)
                  (equal (fn-bs-ops-for-dir (fn-bs-pending file) :transactions) nil))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-store-relation-unfolds
                 fn-bs-ready-relation-authority-is-quiet
                 fn-bs-k0-frontier-file-cut-is-write-fence)
           :in-theory (e/d (fn-bs-frontier-inputp fn-bs-create fn-bs-write fn-bs-fence-file
                            fn-bs-ops-for-dir-of-append)
                           (fn-bs-run fn-bs-frontier-program fn-bs-store-relation
                            fn-bs-statep fn-bs-lookup fn-bs-ops-not-for-ino)))))
(defthm fn-bs-k0-frontier-run-rename-shape
  (implies (consp (nth 12 (fn-bs-run bs ks (fn-bs-frontier-program stage octets) nil groups capacity)))
           (let ((run (fn-bs-run bs ks (fn-bs-frontier-program stage octets) nil groups capacity)))
             (and (equal (car (nth 8 run))
                         (mv-nth 1 (fn-bs-rename (car (nth 6 run)) :staging stage
                                                 :root *fn-bs-frontier-name* :ok)))
                  (equal (cdr (nth 8 run)) (cdr (nth 6 run)))
                  (equal (nth 9 run) (nth 8 run))
                  (equal (car (nth 10 run)) (car (nth 8 run)))
                  (equal (cdr (nth 10 run)) (fn-sf-frontier-replace-result (cdr (nth 8 run)) :ok))
                  (equal (nth 11 run) (nth 10 run)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :expand ((:free (b k s o) (fn-bs-run b k s o groups capacity)))
           :in-theory (e/d (fn-bs-frontier-program fn-bs-step fn-sf-dispatch)
                           (fn-bs-create fn-bs-write fn-bs-fsync-file fn-bs-fsync-dir
                            fn-bs-rename fn-bs-lookup fn-sf-start-frontier
                            fn-sf-frontier-file-result fn-sf-frontier-replace-result
                            fn-sf-frontier-dir-result)))))
(defthm fn-bs-k0-frontier-observation-pair-facts
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-frontier-inputp ks stage octets)
                (not (fn-bs-lookup bs :staging stage)))
           (let* ((run (fn-bs-run bs ks (fn-bs-frontier-program stage octets) nil groups capacity))
                  (b6 (car (nth 6 run))) (k6 (cdr (nth 6 run))))
             (and (equal (fn-sf-phase k6) :frontier-data-durable)
                  (equal (fn-sf-frontier k6) (fn-sf-frontier ks))
                  (equal (fn-sf-frontier-candidate k6) (1+ (fn-sf-frontier ks)))
                  (equal (fn-sf-records k6) (fn-sf-records ks))
                  (equal (fn-bs-durable-frontier b6) (fn-sf-frontier ks))
                  (equal (fn-bs-durable-records b6) (fn-sf-records ks))
                  (equal (fn-bs-frontier-decode (fn-bs-durable-content b6 (fn-bs-next-ino bs)))
                         (1+ (fn-sf-frontier ks)))
                  (equal (fn-bs-lookup b6 :staging stage) (fn-bs-next-ino bs))
                  (fn-bs-inop (fn-bs-next-ino bs))
                  (equal (fn-bs-ops-for-dir (fn-bs-pending b6) :root) nil)
                  (equal (fn-bs-ops-for-dir (fn-bs-pending b6) :transactions) nil))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-store-relation-unfolds
                 fn-bs-store-relation-window-unfolds
                 fn-bs-k0-frontier-file-cut-authority-quiet-restated
                 fn-bs-k0-frontier-file-observation-keeps-byte-state
                 fn-bs-k0-frontier-file-cut-kernel-is-file-observation
                 fn-bs-k0-frontier-file-cut-keeps-old-frontier
                 fn-bs-k0-frontier-file-cut-keeps-durable-records
                 fn-bs-k0-frontier-file-cut-has-exact-frame
                 fn-bs-k0-frontier-file-cut-source-is-new-inode
                 (:instance fn-sf-start-frontier-preserves-state (s ks)))
           :in-theory (e/d (fn-bs-frontier-inputp fn-sf-start-frontier fn-sf-frontier-file-result
                            fn-bs-replay-visiblep fn-sf-crash-imagep fn-sf-frontier-new-visiblep
                            fn-sf-record-present-visiblep fn-bs-statep fn-bs-inop)
                           (fn-bs-run fn-bs-frontier-program fn-bs-store-relation
                            fn-bs-durable-frontier fn-bs-durable-records fn-bs-durable-content
                            fn-bs-lookup fn-bs-pending-matches-phase fn-sf-statep
                            fn-cbor-octet-listp)))))
(defthm fn-bs-k0-frontier-replace-kernel-fields
  (implies (and (fn-sf-statep k6) (equal (fn-sf-phase k6) :frontier-data-durable))
           (let ((k (fn-sf-frontier-replace-result k6 :ok)))
             (and (fn-sf-statep k)
                  (equal (fn-sf-phase k) :frontier-attempted)
                  (equal (fn-sf-frontier k) (fn-sf-frontier k6))
                  (equal (fn-sf-frontier-candidate k) (fn-sf-frontier-candidate k6))
                  (equal (fn-sf-records k) (fn-sf-records k6)))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-sf-frontier-replace-result-preserves-state (s k6) (result :ok)))
           :in-theory (e/d (fn-sf-frontier-replace-result)
                           (fn-sf-statep fn-sf-frontier-replace-result-preserves-state)))))
(defthm fn-bs-k0-frontier-replaced-cut-relation
     (implies (and (fn-bs-store-relation bs ks)
                   (fn-bs-frontier-inputp ks stage octets)
                   (not (fn-bs-lookup bs :staging stage)))
              (let ((p (nth 9 (fn-bs-run bs ks (fn-bs-frontier-program stage octets) nil groups capacity))))
                (fn-bs-store-relation (car p) (cdr p))))
     :rule-classes nil
     :hints (("Goal" :do-not-induct t
              :use (fn-bs-k0-frontier-observation-pair-facts
                    fn-bs-k0-frontier-file-observation-establishes-relation
                    fn-bs-k0-frontier-dir-cut-establishes-relation
                    fn-bs-k0-frontier-run-rename-shape
                    fn-bs-k0-frontier-file-observation-new-inode-fenced
                    fn-bs-k0-frontier-file-observation-has-new-inode
                    fn-bs-store-relation-unfolds
                    (:instance fn-bs-k0c-related-pair-is-consp
                     (x (nth 12 (fn-bs-run bs ks (fn-bs-frontier-program stage octets) nil groups capacity))))
                    (:instance fn-bs-store-relation-unfolds
                     (bs (car (nth 6 (fn-bs-run bs ks (fn-bs-frontier-program stage octets) nil groups capacity))))
                     (ks (cdr (nth 6 (fn-bs-run bs ks (fn-bs-frontier-program stage octets) nil groups capacity)))))
                    (:instance fn-bs-k0-frontier-replace-kernel-fields
                     (k6 (cdr (nth 6 (fn-bs-run bs ks (fn-bs-frontier-program stage octets) nil groups capacity))))
                )
                    (:instance fn-bs-k0-add-pending-frontier-rename-transports-relation
                     (b6 (car (nth 6 (fn-bs-run bs ks (fn-bs-frontier-program stage octets) nil groups capacity))))
                     (k6 (cdr (nth 6 (fn-bs-run bs ks (fn-bs-frontier-program stage octets) nil groups capacity))))
                     (k (cdr (nth 6 (fn-bs-run bs ks (fn-bs-frontier-program stage octets) nil groups capacity))))
                     (ino (fn-bs-next-ino bs)) (sdir :staging) (sname stage)))
              :in-theory (e/d (fn-bs-frontier-inputp fn-bs-rename fn-bs-replay-visiblep
                               fn-sf-frontier-new-visiblep fn-sf-record-present-visiblep
                               fn-bs-dir-idp)
                              (fn-bs-run fn-bs-frontier-program fn-bs-store-relation fn-sf-statep
                               fn-bs-statep fn-bs-durable-frontier fn-bs-durable-records
                               fn-bs-durable-content fn-bs-lookup fn-bs-fencedp fn-bs-inop
                               fn-bs-make fn-bs-namep fn-sf-frontier-replace-result fn-sf-frontier-replace-result-preserves-state)))))
(defthm fn-bs-k0-frontier-attempted-cut-relation
     (implies (and (fn-bs-store-relation bs ks)
                   (fn-bs-frontier-inputp ks stage octets)
                   (not (fn-bs-lookup bs :staging stage)))
              (let ((p (nth 11 (fn-bs-run bs ks (fn-bs-frontier-program stage octets) nil groups capacity))))
                (fn-bs-store-relation (car p) (cdr p))))
     :rule-classes nil
     :hints (("Goal" :do-not-induct t
              :use (fn-bs-k0-frontier-observation-pair-facts
                    fn-bs-k0-frontier-file-observation-establishes-relation
                    fn-bs-k0-frontier-dir-cut-establishes-relation
                    fn-bs-k0-frontier-run-rename-shape
                    fn-bs-k0-frontier-file-observation-new-inode-fenced
                    fn-bs-k0-frontier-file-observation-has-new-inode
                    fn-bs-store-relation-unfolds
                    (:instance fn-bs-k0c-related-pair-is-consp
                     (x (nth 12 (fn-bs-run bs ks (fn-bs-frontier-program stage octets) nil groups capacity))))
                    (:instance fn-bs-store-relation-unfolds
                     (bs (car (nth 6 (fn-bs-run bs ks (fn-bs-frontier-program stage octets) nil groups capacity))))
                     (ks (cdr (nth 6 (fn-bs-run bs ks (fn-bs-frontier-program stage octets) nil groups capacity)))))
                    (:instance fn-bs-k0-frontier-replace-kernel-fields
                     (k6 (cdr (nth 6 (fn-bs-run bs ks (fn-bs-frontier-program stage octets) nil groups capacity))))
                )
                    (:instance fn-bs-k0-add-pending-frontier-rename-transports-relation
                     (b6 (car (nth 6 (fn-bs-run bs ks (fn-bs-frontier-program stage octets) nil groups capacity))))
                     (k6 (cdr (nth 6 (fn-bs-run bs ks (fn-bs-frontier-program stage octets) nil groups capacity))))
                     (k (fn-sf-frontier-replace-result (cdr (nth 6 (fn-bs-run bs ks (fn-bs-frontier-program stage octets) nil groups capacity))) :ok))
                     (ino (fn-bs-next-ino bs)) (sdir :staging) (sname stage)))
              :in-theory (e/d (fn-bs-frontier-inputp fn-bs-rename fn-bs-replay-visiblep
                               fn-sf-frontier-new-visiblep fn-sf-record-present-visiblep
                               fn-bs-dir-idp)
                              (fn-bs-run fn-bs-frontier-program fn-bs-store-relation fn-sf-statep
                               fn-bs-statep fn-bs-durable-frontier fn-bs-durable-records
                               fn-bs-durable-content fn-bs-lookup fn-bs-fencedp fn-bs-inop
                               fn-bs-make fn-bs-namep fn-sf-frontier-replace-result fn-sf-frontier-replace-result-preserves-state)))))

;; ---- lane p10-k0-b: staging-only steps.
(defun fn-bs-k0-writes-avoid (ops inos)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp ops)
      (and (or (not (equal (car (car ops)) :write))
               (not (member-equal (nth 1 (car ops)) inos)))
           (fn-bs-k0-writes-avoid (cdr ops) inos))
    t))
(local (defthm fn-bs-k0t-writes-avoid-fenced-in
  (implies (fn-bs-k0t-fenced-in p xs)
           (equal (fn-bs-k0t-fenced-in (append p ops) xs)
                  (fn-bs-k0t-fenced-in ops xs)))
  :hints (("Goal" :induct (len xs) :in-theory (enable fn-bs-ops-for-ino-of-append fn-bs-ops-for-ino)))))
(local (defthm fn-bs-k0t-writes-avoid-member
  (implies (and (fn-bs-k0-writes-avoid ops xs) (member-equal x xs))
           (equal (fn-bs-ops-for-ino ops x) nil))
  :hints (("Goal" :induct (fn-bs-k0-writes-avoid ops xs)
           :in-theory (enable fn-bs-ops-for-ino)))))
(local (defthm fn-bs-k0t-entry-targets-of-quiet-ops
  (implies (and (not (fn-bs-ops-for-dir ops :root))
                (not (fn-bs-ops-for-dir ops :transactions)))
           (equal (fn-bs-pending-entry-targets ops) nil))
  :hints (("Goal" :induct (fn-bs-pending-entry-targets ops)
           :in-theory (enable fn-bs-pending-entry-targets fn-bs-ops-for-dir)))))
(local (defthm fn-bs-k0t-writes-avoid-cons
  (implies (fn-bs-k0-writes-avoid ops (cons a ys))
           (fn-bs-k0-writes-avoid ops ys))
  :hints (("Goal" :induct (fn-bs-k0-writes-avoid ops ys)))))
(local (defthm fn-bs-k0t-writes-avoid-self-fenced-in
  (implies (fn-bs-k0-writes-avoid ops xs)
           (fn-bs-k0t-fenced-in ops xs))
  :hints (("Goal" :induct (len xs)))))
(local (defthm fn-bs-k0t-writes-avoid-append-right
  (implies (fn-bs-k0-writes-avoid ops (append a ys))
           (fn-bs-k0-writes-avoid ops ys))
  :hints (("Goal" :induct (len a)))))
(local (defthm fn-bs-k0t-first-dir-op-is-entry-target
  (implies (and (member-equal dir '(:root :transactions))
                (consp (fn-bs-ops-for-dir p dir))
                (equal (car (car (fn-bs-ops-for-dir p dir))) :set-entry))
           (member-equal (nth 3 (car (fn-bs-ops-for-dir p dir)))
                         (fn-bs-pending-entry-targets p)))
  :hints (("Goal" :induct (fn-bs-ops-for-dir p dir)
           :in-theory (enable fn-bs-ops-for-dir fn-bs-pending-entry-targets)))))
(local (defthm fn-bs-k0t-writes-avoid-authority-targets
  (implies (fn-bs-k0-writes-avoid ops (fn-bs-authority-inode-list b))
           (fn-bs-k0-writes-avoid ops (fn-bs-pending-entry-targets (fn-bs-pending b))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-bs-authority-inode-list)
           :use ((:instance fn-bs-k0t-writes-avoid-append-right
                  (a (list* (fn-bs-durable-entry b :root *fn-bs-scan-config-name*)
                            (fn-bs-durable-entry b :root *fn-bs-scan-frontier-name*)
                            (strip-cdrs (cdr (assoc-equal :transactions (fn-bs-dirs b))))))
                  (ys (fn-bs-pending-entry-targets (fn-bs-pending b)))))))))
(defthm fn-bs-k0-durable-projections-ignore-pending
  (implies (fn-bs-statep b)
           (let ((b2 (fn-bs-make (fn-bs-unit b) (fn-bs-inodes b) (fn-bs-dirs b) p (fn-bs-next-ino b))))
             (and (equal (fn-bs-durable-entry b2 dir name) (fn-bs-durable-entry b dir name))
                  (equal (fn-bs-durable-content b2 ino) (fn-bs-durable-content b ino))
                  (equal (fn-bs-durable-names b2 dir) (fn-bs-durable-names b dir))
                  (equal (fn-bs-durable-records b2) (fn-bs-durable-records b))
                  (equal (fn-bs-durable-frontier b2) (fn-bs-durable-frontier b)))))
  :hints (("Goal" :in-theory (e/d (fn-bs-durable-entry fn-bs-durable-content fn-bs-durable-names
                                   fn-bs-durable-records fn-bs-durable-frontier fn-bs-durable)
                                  (fn-bs-read-records fn-bs-statep)))))
(defthm fn-bs-k0-staging-extension-keeps-authority
  (implies (and (fn-bs-statep b)
                (fn-bs-authority-fencedp b)
                (fn-bs-authority-knownp b)
                (not (fn-bs-ops-for-dir ops :root))
                (not (fn-bs-ops-for-dir ops :transactions))
                (fn-bs-k0-writes-avoid ops (fn-bs-authority-inode-list b)))
           (let ((b2 (fn-bs-make (fn-bs-unit b) (fn-bs-inodes b) (fn-bs-dirs b)
                                 (append (fn-bs-pending b) ops) (fn-bs-next-ino b))))
             (and (fn-bs-authority-fencedp b2)
                  (fn-bs-authority-knownp b2)
                  (equal (fn-bs-ops-for-dir (fn-bs-pending b2) :root)
                         (fn-bs-ops-for-dir (fn-bs-pending b) :root))
                  (equal (fn-bs-ops-for-dir (fn-bs-pending b2) :transactions)
                         (fn-bs-ops-for-dir (fn-bs-pending b) :transactions)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-bs-authority-fencedp fn-bs-authority-knownp fn-bs-authority-inode-list
                            fn-bs-ops-for-dir-of-append)
                           (fn-bs-durable-entry fn-bs-statep fn-bs-inode-list-knownp)))))
(defthm fn-bs-k0-staging-extension-keeps-pending-match
  (implies (and (fn-bs-statep b)
                (fn-bs-pending-matches-phase b k)
                (not (fn-bs-ops-for-dir ops :root))
                (not (fn-bs-ops-for-dir ops :transactions))
                (fn-bs-k0-writes-avoid ops (fn-bs-authority-inode-list b)))
           (fn-bs-pending-matches-phase
            (fn-bs-make (fn-bs-unit b) (fn-bs-inodes b) (fn-bs-dirs b)
                        (append (fn-bs-pending b) ops) (fn-bs-next-ino b))
            k))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-k0t-writes-avoid-authority-targets
                 (:instance fn-bs-k0t-first-dir-op-is-entry-target (p (fn-bs-pending b)) (dir :root))
                 (:instance fn-bs-k0t-first-dir-op-is-entry-target (p (fn-bs-pending b)) (dir :transactions))
                 (:instance fn-bs-k0t-writes-avoid-member (xs (fn-bs-pending-entry-targets (fn-bs-pending b)))
                            (x (nth 3 (car (fn-bs-ops-for-dir (fn-bs-pending b) :root)))))
                 (:instance fn-bs-k0t-writes-avoid-member (xs (fn-bs-pending-entry-targets (fn-bs-pending b)))
                            (x (nth 3 (car (fn-bs-ops-for-dir (fn-bs-pending b) :transactions))))))
           :in-theory (e/d (fn-bs-pending-matches-phase fn-bs-pending-shape-okp fn-bs-fencedp
                            fn-bs-ops-for-dir-of-append fn-bs-ops-for-ino-of-append)
                           (fn-bs-durable fn-bs-durable-entry fn-bs-durable-names fn-bs-statep
                            fn-bs-durable-records fn-bs-durable-frontier fn-bs-durable-content
                            fn-bs-record-of fn-bs-authority-inode-list fn-bs-pending-entry-targets
                            fn-sf-frontier-new-visiblep fn-sf-record-present-visiblep
                            fn-bs-k0t-writes-avoid-member)))))
(defthm fn-bs-k0-pending-staging-extension-preserves-relation
  (implies (and (fn-bs-store-relation b k)
                (not (fn-bs-replay-visiblep k))
                (fn-bs-statep (fn-bs-make (fn-bs-unit b) (fn-bs-inodes b) (fn-bs-dirs b)
                                          (append (fn-bs-pending b) ops) (fn-bs-next-ino b)))
                (not (fn-bs-ops-for-dir ops :root))
                (not (fn-bs-ops-for-dir ops :transactions))
                (fn-bs-k0-writes-avoid ops (fn-bs-authority-inode-list b)))
           (fn-bs-store-relation
            (fn-bs-make (fn-bs-unit b) (fn-bs-inodes b) (fn-bs-dirs b)
                        (append (fn-bs-pending b) ops) (fn-bs-next-ino b))
            k))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-store-relation-unfolds (bs b) (ks k))
                 (:instance fn-bs-store-relation-window-unfolds (bs b) (ks k))
                 fn-bs-k0-staging-extension-keeps-authority
                 fn-bs-k0-staging-extension-keeps-pending-match)
           :in-theory (e/d (fn-bs-store-relation)
                           (fn-bs-durable fn-bs-durable-entry fn-bs-durable-names fn-bs-statep
                            fn-bs-durable-records fn-bs-durable-frontier fn-bs-durable-content
                            fn-bs-authority-fencedp fn-bs-authority-knownp fn-bs-pending-matches-phase
                            fn-bs-replay-matches-scan fn-sf-crash-imagep fn-sf-statep
                            fn-bs-contiguous-namesp fn-bs-replay-visiblep)))))
(local (defthm fn-bs-k0t-assoc-value-in-strip-cdrs
  (implies (cdr (assoc-equal name al))
           (member-equal (cdr (assoc-equal name al)) (strip-cdrs al)))))
(defthm fn-bs-k0-fresh-inode-txn-agreement
  (implies (and (natp nx)
                (not (member-equal nx (strip-cdrs (cdr (assoc-equal :transactions dirs))))))
           (fn-bs-txn-prefix-agreesp (fn-bs-make u (cons (cons nx nil) inodes) dirs nil m)
                                     (fn-bs-make u inodes dirs nil m2) i count))
  :rule-classes nil
  :hints (("Goal" :induct (fn-bs-txn-prefix-agreesp (fn-bs-make u (cons (cons nx nil) inodes) dirs nil m)
                                                    (fn-bs-make u inodes dirs nil m2) i count)
           :in-theory (e/d (fn-bs-txn-prefix-agreesp fn-bs-lookup fn-bs-content fn-bs-view fn-bs-apply-ops)
                           ()))
          ("Subgoal *1/2" :use ((:instance fn-bs-k0t-assoc-value-in-strip-cdrs
                                 (name (fn-bs-txn-name i)) (al (cdr (assoc-equal :transactions dirs))))))))
(local (defthm fn-bs-k0t-member-of-append
  (iff (member-equal x (append a b))
       (or (member-equal x a) (member-equal x b)))))
(defthm fn-bs-k0-fresh-inode-projections
  (let ((b1 (fn-bs-make (fn-bs-unit b) (cons (cons (fn-bs-next-ino b) nil) (fn-bs-inodes b))
                        (fn-bs-dirs b) p m)))
    (and (equal (fn-bs-durable-entry b1 dir name) (fn-bs-durable-entry b dir name))
         (equal (fn-bs-durable-names b1 dir) (fn-bs-durable-names b dir))
         (equal (fn-bs-durable-content b1 x)
                (if (equal x (fn-bs-next-ino b)) nil (fn-bs-durable-content b x)))
         (equal (fn-bs-pending b1) p)
         (equal (fn-bs-authority-inode-list b1)
                (fn-bs-authority-inode-list (fn-bs-make (fn-bs-unit b) (fn-bs-inodes b) (fn-bs-dirs b)
                                                        p (fn-bs-next-ino b))))))
  :hints (("Goal" :in-theory (enable fn-bs-durable-entry fn-bs-durable-names fn-bs-durable-content
                                     fn-bs-authority-inode-list))))
(defthm fn-bs-k0-fresh-inode-durable-records
  (implies (and (fn-bs-statep b)
                (not (member-equal (fn-bs-next-ino b) (fn-bs-authority-inode-list b))))
           (equal (fn-bs-durable-records
                   (fn-bs-make (fn-bs-unit b) (cons (cons (fn-bs-next-ino b) nil) (fn-bs-inodes b))
                               (fn-bs-dirs b) p m))
                  (fn-bs-durable-records b)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-k0-fresh-inode-txn-agreement
                  (nx (fn-bs-next-ino b)) (u (fn-bs-unit b)) (inodes (fn-bs-inodes b))
                  (dirs (fn-bs-dirs b)) (m m) (m2 (fn-bs-next-ino b)) (i 0)
                  (count (len (fn-bs-durable-names b :transactions))))
                 (:instance fn-bs-read-records-under-agreement
                  (a (fn-bs-make (fn-bs-unit b) (cons (cons (fn-bs-next-ino b) nil) (fn-bs-inodes b))
                                 (fn-bs-dirs b) nil m))
                  (b (fn-bs-make (fn-bs-unit b) (fn-bs-inodes b) (fn-bs-dirs b) nil (fn-bs-next-ino b)))
                  (n 0) (count (len (fn-bs-durable-names b :transactions)))))
           :in-theory (e/d (fn-bs-durable-records fn-bs-durable fn-bs-authority-inode-list fn-bs-statep)
                           (fn-bs-read-records fn-bs-txn-prefix-agreesp fn-bs-durable-names
                            fn-bs-read-records-under-agreement)))))
(local (defthm fn-bs-k0t-knownp-in-of-cons-inode
  (implies (fn-bs-k0t-knownp-in inodes xs)
           (fn-bs-k0t-knownp-in (cons (cons n v) inodes) xs))
  :hints (("Goal" :induct (len xs)))))
(defthm fn-bs-k0-staging-create-shape
  (implies (not (fn-bs-lookup b :staging stage))
           (equal (fn-bs-create b :staging stage :ok)
                  (mv :ok (fn-bs-make (fn-bs-unit b) (cons (cons (fn-bs-next-ino b) nil) (fn-bs-inodes b))
                                      (fn-bs-dirs b)
                                      (append (fn-bs-pending b)
                                              (list (list :set-entry :staging stage (fn-bs-next-ino b))))
                                      (1+ (fn-bs-next-ino b))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-bs-create) (fn-bs-lookup)))))
(defthm fn-bs-k0-staging-create-keeps-authority-and-match
  (implies (and (fn-bs-statep b)
                (not (member-equal (fn-bs-next-ino b) (fn-bs-authority-inode-list b)))
                (fn-bs-authority-fencedp b)
                (fn-bs-authority-knownp b)
                (fn-bs-pending-matches-phase b k))
           (let ((b1 (fn-bs-make (fn-bs-unit b) (cons (cons (fn-bs-next-ino b) nil) (fn-bs-inodes b))
                                 (fn-bs-dirs b)
                                 (append (fn-bs-pending b)
                                         (list (list :set-entry :staging stage (fn-bs-next-ino b))))
                                 (1+ (fn-bs-next-ino b)))))
             (and (fn-bs-authority-fencedp b1)
                  (fn-bs-authority-knownp b1)
                  (fn-bs-pending-matches-phase b1 k))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-k0t-first-dir-op-is-entry-target (p (fn-bs-pending b)) (dir :root))
                 (:instance fn-bs-k0t-first-dir-op-is-entry-target (p (fn-bs-pending b)) (dir :transactions)))
           :in-theory (e/d (fn-bs-authority-fencedp fn-bs-authority-knownp fn-bs-authority-inode-list
                            fn-bs-pending-matches-phase fn-bs-pending-shape-okp fn-bs-fencedp
                            fn-bs-ops-for-dir-of-append fn-bs-ops-for-ino-of-append
                            fn-bs-ops-for-dir fn-bs-ops-for-ino fn-bs-pending-entry-targets)
                           (fn-bs-durable-entry fn-bs-statep fn-bs-inode-list-knownp
                            fn-bs-durable-records fn-bs-durable fn-bs-durable-names fn-bs-record-of
                            fn-sf-frontier-new-visiblep fn-sf-record-present-visiblep)))))
(defthm fn-bs-k0-staging-create-preserves-relation
  (implies (and (fn-bs-store-relation b k)
                (not (fn-bs-replay-visiblep k))
                (fn-bs-namep stage)
                (not (fn-bs-lookup b :staging stage)))
           (fn-bs-store-relation (mv-nth 1 (fn-bs-create b :staging stage :ok)) k))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-k0-staging-create-shape
                 (:instance fn-bs-store-relation-unfolds (bs b) (ks k))
                 (:instance fn-bs-store-relation-window-unfolds (bs b) (ks k))
                 (:instance fn-bs-related-allocation-is-fresh (bs b) (ks k))
                 (:instance fn-bs-create-preserves-statep (s b) (dir :staging) (name stage) (outcome :ok))
                 (:instance fn-bs-k0-staging-create-keeps-authority-and-match (stage stage))
                 (:instance fn-bs-k0-fresh-inode-durable-records
                  (p (append (fn-bs-pending b) (list (list :set-entry :staging stage (fn-bs-next-ino b)))))
                  (m (1+ (fn-bs-next-ino b)))))
           :in-theory (e/d (fn-bs-store-relation fn-bs-durable-frontier fn-bs-authority-inode-list)
                           (fn-bs-durable fn-bs-durable-names fn-bs-statep fn-bs-create
                            fn-bs-durable-records fn-bs-lookup
                            fn-bs-authority-fencedp fn-bs-authority-knownp fn-bs-pending-matches-phase
                            fn-bs-replay-matches-scan fn-sf-crash-imagep fn-sf-statep
                            fn-bs-contiguous-namesp fn-bs-replay-visiblep fn-bs-create-preserves-statep
                            fn-bs-k0-fresh-inode-durable-records)))))
(local (defthm fn-bs-k0t-apply-writes-of-dir-ops
  (equal (fn-bs-apply-writes inodes (fn-bs-ops-for-dir ops dir)) inodes)
  :hints (("Goal" :induct (fn-bs-ops-for-dir ops dir)
           :in-theory (enable fn-bs-ops-for-dir fn-bs-apply-writes)))))
(local (defthm fn-bs-k0t-entry-targets-survive-staging-filter
  (equal (fn-bs-pending-entry-targets (fn-bs-ops-not-for-dir ops :staging))
         (fn-bs-pending-entry-targets ops))
  :hints (("Goal" :induct (fn-bs-ops-not-for-dir ops :staging)
           :in-theory (enable fn-bs-ops-not-for-dir fn-bs-pending-entry-targets)))))
(defthm fn-bs-k0-fence-dir-keeps-inodes
  (equal (fn-bs-inodes (fn-bs-fence-dir b dir)) (fn-bs-inodes b))
  :hints (("Goal" :in-theory (enable fn-bs-fence-dir fn-bs-apply-ops-inodes-are-apply-writes))))
(defthm fn-bs-k0-fence-dir-keeps-unit-and-next
  (and (equal (fn-bs-unit (fn-bs-fence-dir b dir)) (fn-bs-unit b))
       (equal (fn-bs-next-ino (fn-bs-fence-dir b dir)) (fn-bs-next-ino b)))
  :hints (("Goal" :in-theory (enable fn-bs-fence-dir))))
(defthm fn-bs-k0-fence-dir-keeps-durable-content
  (equal (fn-bs-durable-content (fn-bs-fence-dir b dir) x) (fn-bs-durable-content b x))
  :hints (("Goal" :in-theory (enable fn-bs-durable-content))))
(local (defthm fn-bs-k0t-fenced-in-of-dir-filter
  (equal (fn-bs-k0t-fenced-in (fn-bs-ops-not-for-dir p dir) xs)
         (fn-bs-k0t-fenced-in p xs))
  :hints (("Goal" :induct (len xs)))))
(defthm fn-bs-k0-staging-fence-projections
  (let ((b1 (fn-bs-fence-dir b :staging)))
    (and (equal (assoc-equal :root (fn-bs-dirs b1)) (assoc-equal :root (fn-bs-dirs b)))
         (equal (assoc-equal :transactions (fn-bs-dirs b1)) (assoc-equal :transactions (fn-bs-dirs b)))
         (equal (fn-bs-durable-entry b1 :root name) (fn-bs-durable-entry b :root name))
         (equal (fn-bs-durable-content b1 x) (fn-bs-durable-content b x))
         (equal (fn-bs-durable-names b1 :transactions) (fn-bs-durable-names b :transactions))
         (equal (fn-bs-durable-frontier b1) (fn-bs-durable-frontier b))
         (equal (fn-bs-authority-inode-list b1) (fn-bs-authority-inode-list b))
         (equal (fn-bs-ops-for-dir (fn-bs-pending b1) :root) (fn-bs-ops-for-dir (fn-bs-pending b) :root))
         (equal (fn-bs-ops-for-dir (fn-bs-pending b1) :transactions)
                (fn-bs-ops-for-dir (fn-bs-pending b) :transactions))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-bs-fence-dir-touches-only-its-directory (s b) (dir :staging) (other :root))
                        (:instance fn-bs-fence-dir-touches-only-its-directory (s b) (dir :staging) (other :transactions)))
           :in-theory (e/d (fn-bs-durable-entry fn-bs-durable-content fn-bs-durable-names
                            fn-bs-durable-frontier fn-bs-authority-inode-list)
                           (fn-bs-fence-dir-touches-only-its-directory fn-bs-fence-dir)))))
(defthm fn-bs-k0-same-transaction-dir-agreement
  (implies (equal (assoc-equal :transactions d1) (assoc-equal :transactions d2))
           (fn-bs-txn-prefix-agreesp (fn-bs-make u i d1 nil m) (fn-bs-make u i d2 nil m2) n count))
  :rule-classes nil
  :hints (("Goal" :induct (fn-bs-txn-prefix-agreesp (fn-bs-make u i d1 nil m) (fn-bs-make u i d2 nil m2) n count)
           :in-theory (enable fn-bs-txn-prefix-agreesp fn-bs-lookup fn-bs-content fn-bs-view fn-bs-apply-ops))))
(defthm fn-bs-k0-staging-fence-keeps-durable-records
  (equal (fn-bs-durable-records (fn-bs-fence-dir b :staging))
         (fn-bs-durable-records b))
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-k0-staging-fence-projections
                 (:instance fn-bs-k0-same-transaction-dir-agreement
                  (u (fn-bs-unit (fn-bs-fence-dir b :staging))) (i (fn-bs-inodes b))
                  (d1 (fn-bs-dirs (fn-bs-fence-dir b :staging))) (d2 (fn-bs-dirs b))
                  (m (fn-bs-next-ino (fn-bs-fence-dir b :staging))) (m2 (fn-bs-next-ino b))
                  (n 0) (count (len (fn-bs-durable-names b :transactions))))
                 (:instance fn-bs-read-records-under-agreement
                  (a (fn-bs-durable (fn-bs-fence-dir b :staging)))
                  (b (fn-bs-make (fn-bs-unit (fn-bs-fence-dir b :staging)) (fn-bs-inodes b) (fn-bs-dirs b)
                                 nil (fn-bs-next-ino b)))
                  (n 0) (count (len (fn-bs-durable-names b :transactions)))))
           :in-theory (e/d (fn-bs-durable-records fn-bs-durable)
                           (fn-bs-read-records fn-bs-txn-prefix-agreesp fn-bs-durable-names
                            fn-bs-read-records-under-agreement fn-bs-fence-dir)))))
(defthm fn-bs-k0-staging-fence-preserves-relation
  (implies (and (fn-bs-store-relation b k)
                (not (fn-bs-replay-visiblep k)))
           (fn-bs-store-relation (fn-bs-fence-dir b :staging) k))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-k0-staging-fence-projections (name *fn-bs-scan-config-name*))
                 (:instance fn-bs-k0-staging-fence-projections (name *fn-bs-scan-frontier-name*)
                  (x (fn-bs-durable-entry b :root *fn-bs-scan-config-name*)))
                 (:instance fn-bs-store-relation-unfolds (bs b) (ks k))
                 (:instance fn-bs-store-relation-window-unfolds (bs b) (ks k))
                 (:instance fn-bs-fence-dir-preserves-statep (s b) (dir :staging)))
           :in-theory (e/d (fn-bs-store-relation fn-bs-authority-fencedp fn-bs-authority-knownp
                            fn-bs-pending-matches-phase fn-bs-pending-shape-okp
                            fn-bs-k8-record-of-durable-is-durable-content)
                           (fn-bs-durable fn-bs-durable-names fn-bs-statep fn-bs-fence-dir
                            fn-bs-durable-records fn-bs-durable-frontier fn-bs-durable-entry
                            fn-bs-durable-content fn-bs-authority-inode-list fn-bs-record-of
                            fn-bs-replay-matches-scan fn-sf-crash-imagep fn-sf-statep
                            fn-bs-contiguous-namesp fn-bs-replay-visiblep fn-bs-fence-dir-preserves-statep
                            fn-bs-all-fencedp fn-bs-inode-list-knownp fn-bs-fencedp
                            fn-sf-frontier-new-visiblep fn-sf-record-present-visiblep)))))
(defthm fn-bs-k0-staging-write-preserves-relation
  (implies (and (fn-bs-store-relation b k)
                (not (fn-bs-replay-visiblep k))
                (fn-cbor-octet-listp octets)
                (not (member-equal ino (fn-bs-authority-inode-list b))))
           (fn-bs-store-relation (mv-nth 1 (fn-bs-write b ino 0 octets :ok)) k))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-store-relation-unfolds (bs b) (ks k))
                 (:instance fn-bs-write-preserves-statep (s b) (offset 0) (outcome :ok))
                 (:instance fn-bs-k0-pending-staging-extension-preserves-relation
                  (ops (list (list :write ino 0 (fn-bs-take (len octets) octets))))))
           :in-theory (e/d (fn-bs-write fn-bs-ops-for-dir fn-bs-k0-writes-avoid)
                           (fn-bs-store-relation fn-bs-statep fn-bs-write-preserves-statep
                            fn-bs-authority-inode-list fn-bs-take fn-bs-replay-visiblep)))))
(defthm fn-bs-k0-staging-unlink-preserves-relation
  (implies (and (fn-bs-store-relation b k)
                (not (fn-bs-replay-visiblep k))
                (not (equal dir :root))
                (not (equal dir :transactions)))
           (fn-bs-store-relation (mv-nth 1 (fn-bs-unlink b dir name :ok)) k))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-bs-store-relation-unfolds (bs b) (ks k))
                 (:instance fn-bs-unlink-preserves-statep (s b) (outcome :ok))
                 (:instance fn-bs-k0-pending-staging-extension-preserves-relation
                  (ops (list (list :del-entry dir name)))))
           :in-theory (e/d (fn-bs-unlink fn-bs-ops-for-dir fn-bs-k0-writes-avoid)
                           (fn-bs-store-relation fn-bs-statep fn-bs-unlink-preserves-statep
                            fn-bs-authority-inode-list fn-bs-lookup fn-bs-replay-visiblep)))))
(defthm fn-bs-k0-frontier-run-prefix-shape
  (implies (consp (nth 6 (fn-bs-run bs ks (fn-bs-frontier-program stage octets) nil groups capacity)))
           (let ((run (fn-bs-run bs ks (fn-bs-frontier-program stage octets) nil groups capacity))
                 (b1 (mv-nth 1 (fn-bs-create bs :staging stage :ok))))
             (and (equal (nth 2 run) (cons b1 (fn-sf-start-frontier ks)))
                  (equal (nth 4 run)
                         (cons (mv-nth 1 (fn-bs-write b1 (fn-bs-lookup b1 :staging stage) 0 octets :ok))
                               (fn-sf-start-frontier ks))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :expand ((:free (b k s o) (fn-bs-run b k s o groups capacity)))
           :in-theory (e/d (fn-bs-frontier-program fn-bs-step fn-sf-dispatch)
                           (fn-bs-create fn-bs-write fn-bs-fsync-file fn-bs-fsync-dir
                            fn-bs-rename fn-bs-lookup fn-sf-start-frontier
                            fn-sf-frontier-file-result fn-sf-frontier-replace-result
                            fn-sf-frontier-dir-result)))))
(defthm fn-bs-k0t-entry-after-last-set
   (implies (and dir name)
            (equal (fn-bs-entry-after
                    (append ops (list (list :set-entry dir name ino)))
                    old dir name)
                   ino))
   :hints (("Goal"
            :use ((:instance fn-bs-entry-after-of-append
                             (a ops)
                             (b (list (list :set-entry dir name ino)))))
            :in-theory (e/d (fn-bs-entry-after)
                            (fn-bs-entry-after-of-append)))))
(defthm fn-bs-k0t-lookup-after-pending-set
   (implies (and dir name)
            (equal (fn-bs-lookup
                    (fn-bs-make unit inodes dirs
                                (append pending
                                        (list (list :set-entry dir name ino)))
                                next)
                    dir name)
                   ino))
   :hints (("Goal"
            :use ((:instance fn-bs-apply-entries-entry-is-entry-after
                             (dirs dirs)
                             (ops (append pending
                                          (list (list :set-entry dir name ino))))))
            :in-theory (e/d (fn-bs-lookup fn-bs-view
                             fn-bs-apply-ops-dirs-are-apply-entries)
                            (fn-bs-apply-ops fn-bs-apply-entries
                             fn-bs-entry-after)))))
(defthm fn-bs-k0t-created-stage-lookup
   (implies (and (fn-bs-statep bs)
                 (fn-bs-namep stage)
                 (not (fn-bs-lookup bs :staging stage)))
            (equal (fn-bs-lookup
                    (mv-nth 1 (fn-bs-create bs :staging stage :ok))
                    :staging stage)
                   (fn-bs-next-ino bs)))
   :hints (("Goal" :in-theory (e/d (fn-bs-create)
                                   (fn-bs-statep fn-bs-lookup)))))
(defthm fn-bs-k0-staging-create-fresh-facts
  (implies (and (fn-bs-store-relation b k)
                (fn-bs-namep stage)
                (not (fn-bs-lookup b :staging stage)))
           (let ((b1 (mv-nth 1 (fn-bs-create b :staging stage :ok))))
             (and (equal (mv-nth 0 (fn-bs-create b :staging stage :ok)) :ok)
                  (equal (fn-bs-lookup b1 :staging stage) (fn-bs-next-ino b))
                  (not (member-equal (fn-bs-next-ino b) (fn-bs-authority-inode-list b1))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-k0-staging-create-shape
                 (:instance fn-bs-store-relation-unfolds (bs b) (ks k))
                 (:instance fn-bs-related-allocation-is-fresh (bs b) (ks k))
                 (:instance fn-bs-k0-fresh-inode-projections
                  (p (append (fn-bs-pending b) (list (list :set-entry :staging stage (fn-bs-next-ino b)))))
                  (m (1+ (fn-bs-next-ino b)))))
           :in-theory (e/d (fn-bs-authority-inode-list fn-bs-k0t-pending-entry-targets-of-append)
                           (fn-bs-store-relation fn-bs-statep fn-bs-create fn-bs-durable-entry
                            fn-bs-k0-fresh-inode-projections fn-bs-lookup)))))
(defthm fn-bs-k0-frontier-created-and-written-cut-relation
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-frontier-inputp ks stage octets)
                (not (fn-bs-lookup bs :staging stage)))
           (let ((run (fn-bs-run bs ks (fn-bs-frontier-program stage octets) nil groups capacity)))
             (and (fn-bs-store-relation (car (nth 2 run)) (cdr (nth 2 run)))
                  (fn-bs-store-relation (car (nth 4 run)) (cdr (nth 4 run))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-k0-frontier-run-prefix-shape
                 fn-bs-k0-frontier-file-observation-establishes-relation
                 fn-bs-start-frontier-preserves-relation
                 (:instance fn-bs-k0c-related-pair-is-consp
                  (x (nth 6 (fn-bs-run bs ks (fn-bs-frontier-program stage octets) nil groups capacity))))
                 (:instance fn-bs-k0-staging-create-preserves-relation
                  (b bs) (k (fn-sf-start-frontier ks)))
                 (:instance fn-bs-k0-staging-create-fresh-facts (b bs) (k ks))
                 (:instance fn-bs-k0-staging-write-preserves-relation
                  (b (mv-nth 1 (fn-bs-create bs :staging stage :ok))) (k (fn-sf-start-frontier ks))
                  (ino (fn-bs-next-ino bs))))
           :in-theory (e/d (fn-bs-frontier-inputp fn-bs-replay-visiblep fn-sf-start-frontier)
                           (fn-bs-run fn-bs-frontier-program fn-bs-store-relation fn-sf-statep
                            fn-bs-create fn-bs-write fn-bs-statep fn-bs-lookup
                            fn-bs-authority-inode-list)))))
(defthm fn-bs-k0-record-run-prefix-shape
  (implies (consp (nth 10 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity)))
           (let ((run (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity))
                 (b1 (mv-nth 1 (fn-bs-create bs :staging stage :ok))))
             (and (equal (nth 1 run) (cons b1 ks))
                  (equal (nth 3 run)
                         (cons (mv-nth 1 (fn-bs-write b1 (fn-bs-lookup b1 :staging stage) 0 frame :ok))
                               ks)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :expand ((:free (b k s o) (fn-bs-run b k s o groups capacity)))
           :in-theory (e/d (fn-bs-record-program fn-bs-step fn-sf-dispatch)
                           (fn-bs-create fn-bs-write fn-bs-fsync-file fn-bs-fsync-dir
                            fn-bs-link fn-bs-unlink fn-bs-lookup
                            fn-sf-record-file-result fn-sf-record-link-result
                            fn-sf-record-dir-result)))))
(defthm fn-bs-k0-record-created-and-written-cut-relation
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-record-inputp ks stage name frame)
                (not (fn-bs-lookup bs :staging stage)))
           (let ((run (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity)))
             (and (fn-bs-store-relation (car (nth 1 run)) (cdr (nth 1 run)))
                  (fn-bs-store-relation (car (nth 3 run)) (cdr (nth 3 run))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-k0-record-run-prefix-shape
                 fn-bs-k0-record-attempted-cut-establishes-relation
                 (:instance fn-bs-k0c-related-pair-is-consp
                  (x (nth 10 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity))))
                 (:instance fn-bs-k0-staging-create-preserves-relation (b bs) (k ks))
                 (:instance fn-bs-k0-staging-create-fresh-facts (b bs) (k ks))
                 (:instance fn-bs-k0-staging-write-preserves-relation
                  (b (mv-nth 1 (fn-bs-create bs :staging stage :ok))) (k ks) (octets frame)
                  (ino (fn-bs-next-ino bs))))
           :in-theory (e/d (fn-bs-record-inputp fn-bs-replay-visiblep)
                           (fn-bs-run fn-bs-record-program fn-bs-store-relation fn-sf-statep
                            fn-bs-create fn-bs-write fn-bs-statep fn-bs-lookup
                            fn-bs-authority-inode-list)))))
(defthm fn-bs-k0-lookup-by-dir-table-and-dir-ops
  (implies (and dir name
                (equal (assoc-equal dir (fn-bs-dirs a)) (assoc-equal dir (fn-bs-dirs b)))
                (equal (fn-bs-ops-for-dir (fn-bs-pending a) dir) (fn-bs-ops-for-dir (fn-bs-pending b) dir)))
           (equal (fn-bs-lookup a dir name) (fn-bs-lookup b dir name)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-bs-entry-after-through-ops-for-name
                         (ops (fn-bs-pending a)) (old (cdr (assoc-equal name (cdr (assoc-equal dir (fn-bs-dirs a)))))))
                        (:instance fn-bs-entry-after-through-ops-for-name
                         (ops (fn-bs-pending b)) (old (cdr (assoc-equal name (cdr (assoc-equal dir (fn-bs-dirs b)))))))
                        (:instance fn-bs-apply-entries-entry-is-entry-after (dirs (fn-bs-dirs a)) (ops (fn-bs-pending a)))
                        (:instance fn-bs-apply-entries-entry-is-entry-after (dirs (fn-bs-dirs b)) (ops (fn-bs-pending b)))
                        (:instance fn-bs-ops-for-name-through-ops-for-dir (ops (fn-bs-pending a)))
                        (:instance fn-bs-ops-for-name-through-ops-for-dir (ops (fn-bs-pending b))))
           :in-theory (e/d (fn-bs-lookup fn-bs-view fn-bs-apply-ops-dirs-are-apply-entries)
                           (fn-bs-apply-entries fn-bs-apply-ops fn-bs-entry-after fn-bs-ops-for-name)))))
(defthm fn-bs-k0-record-run-cleanup-shape
  (implies (and (consp (nth 14 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity)))
                (fn-bs-lookup (car (nth 14 (fn-bs-run bs ks (fn-bs-record-program stage name frame)
                                                      nil groups capacity)))
                              :staging stage))
           (let* ((run (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity))
                  (b15 (mv-nth 1 (fn-bs-unlink (car (nth 14 run)) :staging stage :ok))))
             (and (equal (car (nth 14 run)) (car (nth 11 run)))
                  (equal (nth 16 run) (cons b15 (cdr (nth 14 run))))
                  (equal (nth 18 run) (cons (fn-bs-fence-dir b15 :staging) (cdr (nth 14 run)))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :expand ((:free (b k s o) (fn-bs-run b k s o groups capacity)))
           :in-theory (e/d (fn-bs-record-program fn-bs-step fn-sf-dispatch fn-bs-fsync-dir fn-bs-unlink)
                           (fn-bs-create fn-bs-write fn-bs-fsync-file fn-bs-fence-dir
                            fn-bs-link fn-bs-lookup
                            fn-sf-record-file-result fn-sf-record-link-result
                            fn-sf-record-dir-result)))))
(defthm fn-bs-k0-record-run-pair-14-byte-is-pair-11
  (implies (consp (nth 14 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity)))
           (let ((run (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity)))
             (equal (car (nth 14 run)) (car (nth 11 run)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :expand ((:free (b k s o) (fn-bs-run b k s o groups capacity)))
           :in-theory (e/d (fn-bs-record-program fn-bs-step fn-sf-dispatch)
                           (fn-bs-create fn-bs-write fn-bs-fsync-file fn-bs-fsync-dir fn-bs-unlink
                            fn-bs-link fn-bs-lookup
                            fn-sf-record-file-result fn-sf-record-link-result
                            fn-sf-record-dir-result)))))
(defthm fn-bs-k0-record-completing-stage-lookup
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-record-inputp ks stage name frame)
                (not (fn-bs-lookup bs :staging stage)))
           (equal (fn-bs-lookup (car (nth 14 (fn-bs-run bs ks (fn-bs-record-program stage name frame)
                                                        nil groups capacity)))
                                :staging stage)
                  (fn-bs-next-ino bs)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-k0-record-completing-cut-relation
                 fn-bs-k0-record-pair-11-is-transaction-fence
                 fn-bs-k0-record-run-link-pair-shape fn-bs-k0-record-run-linked-shape
                 fn-bs-k0-record-attempted-cut-establishes-relation
                 fn-bs-k6-file-cut-source-is-fenced-frame
                 fn-bs-store-relation-unfolds
                 (:instance fn-bs-k0c-related-pair-is-consp
                  (x (nth 14 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity))))
                 (:instance fn-bs-k0c-related-pair-is-consp
                  (x (nth 10 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity))))
                 fn-bs-k0-record-run-pair-14-byte-is-pair-11
                 (:instance fn-bs-fence-dir-touches-only-its-directory
                  (s (car (nth 10 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity))))
                  (dir :transactions) (other :staging))
                 (:instance fn-bs-k0-lookup-by-dir-table-and-dir-ops
                  (a (fn-bs-fence-dir (car (nth 10 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity))) :transactions))
                  (b (car (nth 10 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity))))
                  (dir :staging) (name stage))
                 (:instance fn-bs-k0-lookup-by-dir-table-and-dir-ops
                  (a (car (nth 8 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity))))
                  (b (car (nth 5 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity))))
                  (dir :staging) (name stage)))
           :in-theory (e/d (fn-bs-record-inputp fn-bs-ops-for-dir-of-append fn-bs-ops-for-dir)
                           (fn-bs-run fn-bs-record-program fn-bs-store-relation fn-sf-statep
                            fn-bs-statep fn-bs-lookup fn-bs-fence-dir fn-bs-fencedp
                            fn-bs-durable-content fn-bs-fence-dir-touches-only-its-directory
                            fn-sf-record-link-result fn-sf-record-file-result)))))
(local (defthm fn-bs-k0t-state-next-ino-natp
  (implies (fn-bs-statep b) (natp (fn-bs-next-ino b)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn-bs-statep)))))
(defthm fn-bs-k0-record-cleanup-cut-relation
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-record-inputp ks stage name frame)
                (not (fn-bs-lookup bs :staging stage)))
           (let ((run (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity)))
             (and (fn-bs-store-relation (car (nth 16 run)) (cdr (nth 16 run)))
                  (fn-bs-store-relation (car (nth 18 run)) (cdr (nth 18 run))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-k0-record-completing-cut-relation
                 fn-bs-k0-record-completing-stage-lookup
                 fn-bs-k0-record-run-cleanup-shape
                 fn-bs-store-relation-unfolds
                 (:instance fn-bs-k0c-related-pair-is-consp
                  (x (nth 14 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity))))
                 (:instance fn-bs-k0-staging-unlink-preserves-relation
                  (b (car (nth 14 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity))))
                  (k (cdr (nth 14 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity))))
                  (dir :staging) (name stage))
                 (:instance fn-bs-k0-staging-fence-preserves-relation
                  (b (mv-nth 1 (fn-bs-unlink (car (nth 14 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity))) :staging stage :ok)))
                  (k (cdr (nth 14 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity))))))
           :in-theory (e/d (fn-bs-replay-visiblep)
                           (fn-bs-run fn-bs-record-program fn-bs-store-relation fn-sf-statep
                            fn-bs-statep fn-bs-lookup fn-bs-fence-dir fn-bs-unlink fn-bs-record-inputp)))))

;; ---- lane p10-k0-b: error arms (the host observation after an EIO, applied to the cut pair).
(defthm fn-bs-record-link-error-preserves-relation
  (implies (fn-bs-store-relation bs ks)
           (fn-bs-store-relation bs (fn-sf-record-link-result ks :error)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-sf-record-link-result-preserves-state (s ks) (result :error)))
           :in-theory (e/d (fn-bs-store-relation fn-bs-pending-matches-phase
                             fn-bs-replay-visiblep fn-sf-crash-imagep
                             fn-sf-frontier-new-visiblep fn-sf-record-present-visiblep
                             fn-sf-record-link-result)
                            (fn-bs-statep fn-sf-statep fn-bs-pending-shape-okp
                             fn-bs-authority-fencedp fn-bs-authority-knownp
                             fn-bs-ops-for-dir)))))
(defthm fn-bs-record-dir-error-preserves-relation
  (implies (fn-bs-store-relation bs ks)
           (fn-bs-store-relation bs (fn-sf-record-dir-result ks :error)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-sf-record-dir-result-preserves-state (s ks) (result :error)))
           :in-theory (e/d (fn-bs-store-relation fn-bs-pending-matches-phase
                             fn-bs-replay-visiblep fn-sf-crash-imagep
                             fn-sf-frontier-new-visiblep fn-sf-record-present-visiblep
                             fn-sf-record-dir-result)
                            (fn-bs-statep fn-sf-statep fn-bs-pending-shape-okp
                             fn-bs-authority-fencedp fn-bs-authority-knownp
                             fn-bs-ops-for-dir)))))
(defthm fn-bs-k0-frontier-replace-error-kernel-fields
  (implies (and (fn-sf-statep k6) (equal (fn-sf-phase k6) :frontier-data-durable))
           (let ((k (fn-sf-frontier-replace-result k6 :error)))
             (and (fn-sf-statep k)
                  (equal (fn-sf-phase k) :fenced-frontier)
                  (equal (fn-sf-frontier k) (fn-sf-frontier k6))
                  (equal (fn-sf-frontier-candidate k) (fn-sf-frontier-candidate k6))
                  (equal (fn-sf-records k) (fn-sf-records k6)))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-sf-frontier-replace-result-preserves-state (s k6) (result :error)))
           :in-theory (e/d (fn-sf-frontier-replace-result)
                           (fn-sf-statep fn-sf-frontier-replace-result-preserves-state)))))
(defthm fn-bs-k0-frontier-issued-rename-error-arm-relation
     (implies (and (fn-bs-store-relation bs ks)
                   (fn-bs-frontier-inputp ks stage octets)
                   (not (fn-bs-lookup bs :staging stage)))
              (let ((p (nth 9 (fn-bs-run bs ks (fn-bs-frontier-program stage octets) nil groups capacity))))
                (fn-bs-store-relation (car p) (fn-sf-frontier-replace-result (cdr (nth 6 (fn-bs-run bs ks (fn-bs-frontier-program stage octets) nil groups capacity))) :error))))
     :rule-classes nil
     :hints (("Goal" :do-not-induct t
              :use (fn-bs-k0-frontier-observation-pair-facts
                    fn-bs-k0-frontier-file-observation-establishes-relation
                    fn-bs-k0-frontier-dir-cut-establishes-relation
                    fn-bs-k0-frontier-run-rename-shape
                    fn-bs-k0-frontier-file-observation-new-inode-fenced
                    fn-bs-k0-frontier-file-observation-has-new-inode
                    fn-bs-store-relation-unfolds
                    (:instance fn-bs-k0c-related-pair-is-consp
                     (x (nth 12 (fn-bs-run bs ks (fn-bs-frontier-program stage octets) nil groups capacity))))
                    (:instance fn-bs-store-relation-unfolds
                     (bs (car (nth 6 (fn-bs-run bs ks (fn-bs-frontier-program stage octets) nil groups capacity))))
                     (ks (cdr (nth 6 (fn-bs-run bs ks (fn-bs-frontier-program stage octets) nil groups capacity)))))
                    (:instance fn-bs-k0-frontier-replace-error-kernel-fields
                     (k6 (cdr (nth 6 (fn-bs-run bs ks (fn-bs-frontier-program stage octets) nil groups capacity))))
                )
                    (:instance fn-bs-k0-add-pending-frontier-rename-transports-relation
                     (b6 (car (nth 6 (fn-bs-run bs ks (fn-bs-frontier-program stage octets) nil groups capacity))))
                     (k6 (cdr (nth 6 (fn-bs-run bs ks (fn-bs-frontier-program stage octets) nil groups capacity))))
                     (k (fn-sf-frontier-replace-result (cdr (nth 6 (fn-bs-run bs ks (fn-bs-frontier-program stage octets) nil groups capacity))) :error))
                     (ino (fn-bs-next-ino bs)) (sdir :staging) (sname stage)))
              :in-theory (e/d (fn-bs-frontier-inputp fn-bs-rename fn-bs-replay-visiblep
                               fn-sf-frontier-new-visiblep fn-sf-record-present-visiblep
                               fn-bs-dir-idp)
                              (fn-bs-run fn-bs-frontier-program fn-bs-store-relation fn-sf-statep
                               fn-bs-statep fn-bs-durable-frontier fn-bs-durable-records
                               fn-bs-durable-content fn-bs-lookup fn-bs-fencedp fn-bs-inop
                               fn-bs-make fn-bs-namep fn-sf-frontier-replace-result fn-sf-frontier-replace-result-preserves-state)))))
(defthm fn-bs-k0-frontier-error-arms-relation
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-frontier-inputp ks stage octets)
                (not (fn-bs-lookup bs :staging stage)))
           (let ((run (fn-bs-run bs ks (fn-bs-frontier-program stage octets) nil groups capacity)))
             (and (fn-bs-store-relation (car (nth 6 run))
                                        (fn-sf-frontier-replace-result (cdr (nth 6 run)) :error))
                  (fn-bs-store-relation (car (nth 11 run))
                                        (fn-sf-frontier-dir-result (cdr (nth 11 run)) :error)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-k0-frontier-file-observation-establishes-relation
                 fn-bs-k0-frontier-attempted-cut-relation
                 (:instance fn-bs-frontier-replace-result-preserves-relation
                  (bs (car (nth 6 (fn-bs-run bs ks (fn-bs-frontier-program stage octets) nil groups capacity))))
                  (ks (cdr (nth 6 (fn-bs-run bs ks (fn-bs-frontier-program stage octets) nil groups capacity))))
                  (result :error))
                 (:instance fn-bs-frontier-dir-error-preserves-relation
                  (bs (car (nth 11 (fn-bs-run bs ks (fn-bs-frontier-program stage octets) nil groups capacity))))
                  (ks (cdr (nth 11 (fn-bs-run bs ks (fn-bs-frontier-program stage octets) nil groups capacity))))))
           :in-theory (theory 'minimal-theory))))
(defthm fn-bs-k0-record-error-arms-relation
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-record-inputp ks stage name frame)
                (not (fn-bs-lookup bs :staging stage)))
           (let ((run (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity)))
             (and (fn-bs-store-relation (car (nth 6 run))
                                        (fn-sf-record-link-result (cdr (nth 6 run)) :error))
                  (fn-bs-store-relation (car (nth 10 run))
                                        (fn-sf-record-dir-result (cdr (nth 10 run)) :error)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-k0-record-staged-durable-cut-relation
                 fn-bs-k0-record-attempted-cut-establishes-relation
                 (:instance fn-bs-record-link-error-preserves-relation
                  (bs (car (nth 6 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity))))
                  (ks (cdr (nth 6 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity)))))
                 (:instance fn-bs-record-dir-error-preserves-relation
                  (bs (car (nth 10 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity))))
                  (ks (cdr (nth 10 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity))))))
           :in-theory (theory 'minimal-theory))))
