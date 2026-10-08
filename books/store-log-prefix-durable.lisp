; Acknowledgement safety needs a complete durable prefix, with its pending
; writes isolated from that prefix.  It does not need R's zero-filled extent,
; whole-store quietness, directory publication, or a natural-number inode key.
; The copy creates its inode at the head of the inode table; carrying that
; fact makes even the total-logic NIL-key case explicit, without assuming
; arbitrary association tables behave like well-formed maps.
(in-package "ACL2")
(include-book "store-log-durable")
(local (include-book "arithmetic/top" :dir :system))
(defun fn-lgp-contentp (c ks unit genesis max)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((f (fn-lgk-frontier ks))
         (w (fn-lg-log (fn-lgk-inflight ks) (fn-lgk-last ks) unit)))
    (and 
         
         
         (<= f (len c))
         (equal (fn-lg-scan (fn-bs-take f c) genesis unit max)
                (cons (fn-lgk-committed ks) f))
         (equal (fn-lg-scan-last (fn-bs-take f c) genesis unit max) (fn-lgk-last ks))
         (fn-frame-digestp (fn-lgk-last ks))
         
         (fn-lg-recordsp (fn-lgk-inflight ks) max)
         (fn-lg-recordsp (fn-lgk-batch ks) max)
         (<= (+ f (len w)) (len c))
         (true-listp (fn-lgk-committed ks))
         (<= (fn-lgk-acked ks) (len (fn-lgk-committed ks))))))
(defthm fn-lgp-take-append-prefix
 (implies (and (true-listp x) (equal n (len x)))
          (equal (fn-bs-take n (append x y)) x))
 :hints (("Goal" :induct (fn-bs-take n x) :in-theory (enable fn-bs-take))))
(local
 (defthm fn-lgp-take-then-tail
 (implies (<= (nfix n) (len x))
          (equal (append (fn-bs-take n x) (nthcdr n x)) x))
 :hints (("Goal" :induct (fn-bs-take n x) :in-theory (enable fn-bs-take)))))
(local
 (defthm fn-lgp-len-take (equal (len (fn-bs-take n x)) (nfix n))))
(local
 (defthm fn-lgp-take-true-listp (true-listp (fn-bs-take n x))))
(defthm fn-lgp-log-of-atom
 (implies (not (consp records)) (equal (fn-lg-log records prev unit) nil))
 :hints (("Goal" :in-theory (enable fn-lg-log-unfolds))))
(local
 (defthm fn-lgp-len-tail
 (equal (len (nthcdr n x)) (nfix (- (len x) (nfix n))))))
(local
 (defthm fn-lgp-append-assoc
 (equal (append (append x y) z) (append x (append y z)))))
(local (defthm fn-lgp-recordsp-nil (fn-lg-recordsp nil max)
 :hints (("Goal" :in-theory (enable fn-lg-recordsp)))))
(local
 (defthm fn-lgp-fence-content
  (implies (and  (true-listp d) 
                (equal (len d) (fn-lgk-frontier ks))
                (fn-lgp-contentp (append d z) ks unit genesis max))
           (let ((w (fn-lg-log (fn-lgk-inflight ks) (fn-lgk-last ks) unit)))
             (fn-lgp-contentp (append d (append w (nthcdr (len w) z)))
                                 (fn-lgk-fence ks unit) unit genesis max)))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-lg-scan fn-lg-scan-last fn-lg-log fn-lg-recordsp mod
                               fn-lg-scan-of-complete-append fn-lg-scan-last-of-complete-append
                               )
           :use (
                 (:instance fn-lg-log-true-listp (records (fn-lgk-inflight ks))
                            (prev (fn-lgk-last ks)))
                 (:instance fn-lg-scan-of-complete-append
                            (x (fn-lg-log (fn-lgk-inflight ks) (fn-lgk-last ks) unit))
                            (prev genesis))
                 (:instance fn-lg-scan-last-of-complete-append
                            (x (fn-lg-log (fn-lgk-inflight ks) (fn-lgk-last ks) unit))
                            (prev genesis))
                 (:instance fn-lg-scan-of-log (records (fn-lgk-inflight ks))
                            (prev (fn-lgk-last ks)))
                 (:instance fn-lg-scan-last-of-log-append (records (fn-lgk-inflight ks))
                            (prev (fn-lgk-last ks)) (x nil))
                 
                 (:instance fn-lg-last-trailer-digestp (records (fn-lgk-inflight ks))
                            (prev (fn-lgk-last ks))))))))
(defun fn-lgp-headedp (inodes ino)
 (declare (xargs :guard t))
 (and (consp inodes) (consp (car inodes)) (equal (caar inodes) ino)))
(local
 (defthm fn-lgp-head-assoc
 (implies (fn-lgp-headedp inodes ino)
          (equal (assoc-equal ino inodes) (car inodes)))
 :hints (("Goal" :in-theory (enable assoc-equal)))))
(local
 (defthm fn-lgp-put-keeps-head
 (implies (fn-lgp-headedp inodes ino)
          (fn-lgp-headedp (fn-bs-put-assoc i v inodes) ino))
 :hints (("Goal" :in-theory (enable fn-bs-put-assoc)))))
(local
 (defthm fn-lgp-head-content-of-put
 (implies (fn-lgp-headedp inodes ino)
          (equal (cdr (assoc-equal ino (fn-bs-put-assoc i v inodes)))
                 (if (equal i ino) v (cdr (assoc-equal ino inodes)))))
 :hints (("Goal" :in-theory (enable fn-bs-put-assoc assoc-equal)))))
(local
 (defun fn-lgp-safep (bs ks ino genesis max)
 (declare (xargs :verify-guards nil))
 (let ((c (fn-bs-durable-content bs ino)) (f (fn-lgk-frontier ks)))
  (and (fn-lgp-headedp (fn-bs-inodes bs) ino)
       (<= f (len c))
       (equal (fn-lg-scan (fn-bs-take f c) genesis (fn-bs-unit bs) max)
              (cons (fn-lgk-committed ks) f))
       (fn-lgu-writes-at-or-above (fn-bs-pending bs) ino f)
       (true-listp (fn-lgk-committed ks))
       (<= (fn-lgk-acked ks) (len (fn-lgk-committed ks)))))))
(defun fn-lgp-relp (bs ks ino genesis max)
 (declare (xargs :verify-guards nil))
 (and (fn-lgp-headedp (fn-bs-inodes bs) ino)
      (fn-lgp-contentp (fn-bs-durable-content bs ino) ks (fn-bs-unit bs) genesis max)
      (equal (fn-bs-ops-for-ino (fn-bs-pending bs) ino)
             (if (consp (fn-lgk-inflight ks))
                 (list (list :write ino (fn-lgk-frontier ks)
                             (fn-lg-log (fn-lgk-inflight ks) (fn-lgk-last ks) (fn-bs-unit bs))))
                 nil))))
(local
 (defun fn-lgp-invp (bs ks ino genesis max)
 (declare (xargs :verify-guards nil))
 (or (fn-lgp-relp bs ks ino genesis max)
     (and (equal (fn-lgk-phase ks) :fault) (fn-lgp-safep bs ks ino genesis max)))))
(local
 (defun fn-lgp-all-safep (pairs ino genesis max)
 (declare (xargs :verify-guards nil))
 (if (atom pairs) t
  (and (fn-lgp-safep (caar pairs) (cdar pairs) ino genesis max)
       (fn-lgp-all-safep (cdr pairs) ino genesis max)))))
(local
 (defthm fn-lgp-apply-op-keeps-head
 (implies (fn-lgp-headedp inodes ino)
          (fn-lgp-headedp (car (fn-bs-apply-op inodes dirs op)) ino))
 :hints (("Goal" :in-theory (e/d (fn-bs-apply-op) (fn-lgp-headedp fn-bs-put-assoc fn-bs-splice))))))
(local
 (defthm fn-lgp-apply-ops-keeps-head
 (implies (fn-lgp-headedp inodes ino)
          (fn-lgp-headedp (car (fn-bs-apply-ops inodes dirs ops)) ino))
 :hints (("Goal" :induct (fn-bs-apply-ops inodes dirs ops)
          :in-theory (e/d (fn-bs-apply-ops) (fn-lgp-headedp fn-bs-apply-op))))))
(local
 (in-theory (disable fn-lgp-headedp)))
(local (in-theory (disable fn-lgp-head-assoc assoc-equal fn-lgc-log-len-is-the-log-length)))
(local
 (defthm fn-lgp-writes-above-filter
 (equal (fn-lgu-writes-at-or-above (fn-bs-ops-for-ino ops ino) ino f)
        (fn-lgu-writes-at-or-above ops ino f))
 :hints (("Goal" :induct (fn-bs-ops-for-ino ops ino)
          :in-theory (enable fn-bs-ops-for-ino fn-lgu-writes-at-or-above)))))
(local
 (defthm fn-lgp-write-keeps-inodes
 (equal (fn-bs-inodes (mv-nth 1 (fn-bs-write bs ino off octets outcome)))
        (fn-bs-inodes bs))
 :hints (("Goal" :in-theory (enable fn-bs-write)))))
(local
 (defthm fn-lgp-fsync-keeps-head
 (implies (fn-lgp-headedp (fn-bs-inodes bs) ino)
          (fn-lgp-headedp (fn-bs-inodes (mv-nth 1 (fn-bs-fsync-file bs ino outcome))) ino))
 :hints (("Goal" :in-theory (e/d (fn-bs-fsync-file fn-bs-fence-file)
                               (fn-lgp-headedp fn-bs-apply-ops fn-bs-ops-for-ino fn-bs-crash-select))))))
(local
 (defthm fn-lgp-unit-of-write
   (equal (fn-bs-unit (mv-nth 1 (fn-bs-write s ino offset octets outcome))) (fn-bs-unit s))
   :hints (("Goal" :in-theory (enable fn-bs-write)))))
(local
 (defthm fn-lgp-unit-of-fsync-file
   (equal (fn-bs-unit (mv-nth 1 (fn-bs-fsync-file s ino outcome))) (fn-bs-unit s))
   :hints (("Goal" :in-theory (enable fn-bs-fsync-file fn-bs-fence-file)))))
(local
 (defthm fn-lgp-unit-of-crash
   (equal (fn-bs-unit (fn-bs-crash s choices)) (fn-bs-unit s))
   :hints (("Goal" :in-theory (enable fn-bs-crash)))))
(local
 (defthm fn-lgp-len-take (equal (len (fn-bs-take n x)) (nfix n))))
(local
 (defthm fn-lgp-take-of-append-short
   (implies (and (natp f) (<= f (len a)))
            (equal (fn-bs-take f (append a b)) (fn-bs-take f a)))))
(local
 (defthm fn-lgp-splice-keeps-the-prefix
   (implies (and (natp f) (<= f (nfix off)))
            (and (equal (fn-bs-take f (fn-bs-splice old off oct)) (fn-bs-take f old))
                 (<= f (len (fn-bs-splice old off oct)))))
   :hints (("Goal" :in-theory (e/d (fn-bs-splice) (fn-bs-take))))))
(local
 (defthm fn-lgp-apply-op-content
   (implies (fn-lgp-headedp inodes ino)
            (equal (cdr (assoc-equal ino (car (fn-bs-apply-op inodes dirs op))))
                   (if (and (equal (car op) :write) (equal (nth 1 op) ino))
                       (fn-bs-splice (cdr (assoc-equal ino inodes)) (nth 2 op) (nth 3 op))
                     (cdr (assoc-equal ino inodes)))))
   :hints (("Goal" :cases ((equal (nth 1 op) ino))
            :in-theory (e/d (fn-bs-apply-op) (fn-bs-take fn-bs-splice fn-bs-put-assoc fn-bs-del-assoc))))))
(local
 (defthm fn-lgp-apply-ops-keeps-the-prefix
   (implies (and (fn-lgp-headedp inodes ino) (natp f) (fn-lgu-writes-at-or-above ops ino f))
            (let ((c2 (cdr (assoc-equal ino (mv-nth 0 (fn-bs-apply-ops inodes dirs ops)))))
                  (c (cdr (assoc-equal ino inodes))))
              (and (equal (fn-bs-take f c2) (fn-bs-take f c))
                   (implies (<= f (len c)) (<= f (len c2))))))
   :hints (("Goal" :induct (fn-bs-apply-ops inodes dirs ops)
            :in-theory (e/d () (fn-bs-apply-op fn-bs-take fn-bs-splice fn-bs-put-assoc fn-bs-del-assoc))))))
(local
 (defthm fn-lgp-writes-at-or-above-of-append
  (equal (fn-lgu-writes-at-or-above (append a b) ino f)
         (and (fn-lgu-writes-at-or-above a ino f) (fn-lgu-writes-at-or-above b ino f)))))
(local
 (defthm fn-lgp-max-at-or-above-linear
   (implies (and (natp o) (integerp y)) (<= o (nfix (max o y))))
   :rule-classes :linear))
(local
 (defthm fn-lgp-tear-write-at-or-above
   (implies (or (not (equal (nth 1 op) ino)) (<= (nfix f) (nfix (nth 2 op))))
            (fn-lgu-writes-at-or-above (fn-bs-tear-write op sels i unit) ino f))
   :hints (("Goal" :induct (fn-bs-tear-write op sels i unit)
            :expand ((fn-bs-tear-write op sels i unit))
            :do-not '(generalize fertilize)
            :in-theory (e/d (fn-lgp-max-at-or-above-linear)
                            (fn-bs-take fn-bs-zeros fn-bs-unit-count max nfix floor))))))
(local
 (defthm fn-lgp-crash-select-writes-at-or-above
  (implies (fn-lgu-writes-at-or-above ops ino f)
           (fn-lgu-writes-at-or-above (fn-bs-crash-select ops choices unit) ino f))
  :hints (("Goal" :induct (fn-bs-crash-select ops choices unit)
           :in-theory (disable fn-bs-tear-write))
          ("Subgoal *1/1" :use ((:instance fn-lgp-tear-write-at-or-above
                                           (op (car ops)) (sels (car choices)) (i 0)))))))
(local
 (defthm fn-lgp-ops-for-ino-writes-at-or-above
  (implies (fn-lgu-writes-at-or-above ops ino f)
           (and (fn-lgu-writes-at-or-above (fn-bs-ops-for-ino ops j) ino f)
                (fn-lgu-writes-at-or-above (fn-bs-ops-not-for-ino ops j) ino f)))))
(local
 (defthm fn-lgp-take-then-nthcdr-any
   (implies (and (natp n) (<= n (len x)))
            (equal (append (fn-bs-take n x) (nthcdr n x)) x))))
(local
 (defthm fn-lgp-crash-with-choices-keeps-the-prefix
  (implies (and (fn-lgp-headedp (fn-bs-inodes s) ino) (natp f) (fn-lgu-writes-at-or-above (fn-bs-pending s) ino f)
                (<= f (len (fn-bs-durable-content s ino))))
           (let ((c2 (fn-bs-durable-content (fn-bs-crash s choices) ino)))
             (and (equal (fn-bs-take f c2) (fn-bs-take f (fn-bs-durable-content s ino)))
                  (<= f (len c2)))))
  :hints (("Goal" :in-theory (e/d (fn-bs-crash fn-bs-durable-content)
                                  (fn-bs-take fn-bs-apply-ops fn-bs-crash-select
                                   fn-lgp-apply-ops-keeps-the-prefix))
           :use ((:instance fn-lgp-apply-ops-keeps-the-prefix
                            (inodes (fn-bs-inodes s)) (dirs (fn-bs-dirs s))
                            (ops (fn-bs-crash-select (fn-bs-pending s) choices (fn-bs-unit s)))))))))
(local
 (defthm fn-lgp-crash-keeps-the-prefix
  (implies (and (fn-lgp-headedp (fn-bs-inodes s) ino) (natp f) (fn-lgu-writes-at-or-above (fn-bs-pending s) ino f)
                (<= f (len (fn-bs-durable-content s ino)))
                (fn-bs-crash-imagep s image))
           (let ((c2 (fn-bs-durable-content image ino)))
             (and (equal (fn-bs-take f c2) (fn-bs-take f (fn-bs-durable-content s ino)))
                  (<= f (len c2)))))
  :hints (("Goal" :in-theory (e/d (fn-bs-crash-imagep)
                                  (fn-bs-take fn-bs-crash fn-bs-durable-content))))))
(local
 (defthm fn-lgp-safe-image-scans-the-committed-records-first
  (implies (and (fn-lgp-safep bs ks ino genesis max) (fn-bs-crash-imagep bs image))
           (let* ((c (fn-bs-durable-content bs ino)) (c2 (fn-bs-durable-content image ino))
                  (f (fn-lgk-frontier ks)) (unit (fn-bs-unit bs)))
             (equal (car (fn-lg-scan c2 genesis unit max))
                    (append (fn-lgk-committed ks)
                            (car (fn-lg-scan (nthcdr f c2)
                                             (fn-lg-scan-last (fn-bs-take f c) genesis unit max)
                                             unit max))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-lgp-safep)
                           (fn-bs-take fn-lg-scan fn-lg-scan-last fn-bs-durable-content
                            fn-bs-crash-imagep fn-lgp-crash-keeps-the-prefix
                            fn-lgp-take-then-nthcdr-any fn-lg-scan-of-complete-append
                            fn-lgk-frontier fn-lgk-committed))
           :use ((:instance fn-lgp-crash-keeps-the-prefix (s bs) (f (fn-lgk-frontier ks)))
                 (:instance fn-lgp-take-then-nthcdr-any (n (fn-lgk-frontier ks))
                            (x (fn-bs-durable-content image ino)))
                 (:instance fn-lg-scan-of-complete-append
                            (d (fn-bs-take (fn-lgk-frontier ks) (fn-bs-durable-content bs ino)))
                            (x (nthcdr (fn-lgk-frontier ks) (fn-bs-durable-content image ino)))
                            (prev genesis) (unit (fn-bs-unit bs))))))))
(local
 (defthm fn-lgp-safep-acked-within
  (implies (fn-lgp-safep bs ks ino genesis max)
           (and (<= (fn-lgk-acked ks) (len (fn-lgk-committed ks)))
                (natp (fn-lgk-acked ks))))
  :rule-classes nil))
(local
 (defthm fn-lgp-take-of-append-within
   (implies (and (natp a) (<= a (len c)))
            (equal (take a (append c x)) (take a c)))))
(local
 (defthm fn-lgp-len-append
   (equal (len (append c x)) (+ (len c) (len x)))))
(local
 (defthm fn-lgp-safe-image-recovers-the-acknowledged-records
  (implies (and (fn-lgp-safep bs ks ino genesis max) (fn-bs-crash-imagep bs image))
           (let ((a (fn-lgk-acked ks))
                 (recovered (fn-lgk-committed
                             (fn-lgk-recover (fn-bs-durable-content image ino)
                                             genesis (fn-bs-unit bs) max next-txid))))
             (and (<= a (len recovered))
                  (equal (take a recovered) (take a (fn-lgk-committed ks))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-lgu-recovered-kernel-holds-the-scan)
                           (fn-lgp-safep fn-lg-scan fn-lg-scan-last fn-bs-take fn-lgk-recover
                            fn-bs-durable-content fn-bs-crash-imagep fn-lgk-committed fn-lgk-acked
                            fn-lgp-safe-image-scans-the-committed-records-first take))
           :use ((:instance fn-lgp-safe-image-scans-the-committed-records-first)
                 (:instance fn-lgp-safep-acked-within))))))
(local
 (defthm fn-lgp-related-state-is-safe
  (implies (fn-lgp-relp bs ks ino genesis max)
           (fn-lgp-safep bs ks ino genesis max))
  :hints (("Goal" :use ((:instance fn-lgp-writes-above-filter (ops (fn-bs-pending bs)) (f (fn-lgk-frontier ks)))) :in-theory (e/d (fn-lgp-relp fn-lgp-contentp)
                                  (fn-lgp-writes-above-filter fn-lg-scan fn-lg-scan-last fn-lg-log fn-bs-take fn-lg-zerosp
                                   fn-lg-recordsp fn-frame-digestp fn-bs-durable-content mod))))))
(local
 (defthm fn-lgp-safep-when-fields-agree
  (implies (and (fn-lgp-safep bs ks ino genesis max)
                (equal (fn-lgk-committed k2) (fn-lgk-committed ks))
                (equal (fn-lgk-frontier k2) (fn-lgk-frontier ks))
                (<= (fn-lgk-acked k2) (len (fn-lgk-committed ks))))
           (fn-lgp-safep bs k2 ino genesis max))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-lgp-safep)
                                  (fn-lg-scan fn-bs-take fn-bs-durable-content
                                   fn-lgk-committed fn-lgk-frontier fn-lgk-acked))))))
(local
 (defthm fn-lgp-write-parts
   (let ((s1 (mv-nth 1 (fn-bs-write bs ino off octets outcome))))
     (and (equal (fn-bs-durable-content s1 i) (fn-bs-durable-content bs i))
          (equal (fn-bs-unit s1) (fn-bs-unit bs))
          (implies (and (fn-lgu-writes-at-or-above (fn-bs-pending bs) ino f)
                        (<= (nfix f) (nfix off)))
                   (fn-lgu-writes-at-or-above (fn-bs-pending s1) ino f))))
   :hints (("Goal" :in-theory (e/d (fn-bs-write fn-bs-durable-content) (fn-bs-take))))))
(local
 (defthm fn-lgp-write-keeps-safe
  (implies (and (fn-lgp-safep bs ks ino genesis max)
                (<= (fn-lgk-frontier ks) (nfix off)))
           (fn-lgp-safep (mv-nth 1 (fn-bs-write bs ino off octets outcome)) ks ino genesis max))
  :hints (("Goal" :in-theory (e/d (fn-lgp-safep)
                                  (fn-bs-write fn-lg-scan fn-bs-take fn-lgk-frontier fn-lgk-committed
                                   fn-bs-durable-content fn-lgu-writes-at-or-above))))))
(local
 (defthm fn-lgp-fsync-keeps-safe
  (implies (fn-lgp-safep bs ks ino genesis max)
           (fn-lgp-safep (mv-nth 1 (fn-bs-fsync-file bs ino outcome)) ks ino genesis max))
  :hints (("Goal" :in-theory (e/d (fn-lgp-safep fn-bs-fsync-file fn-bs-fence-file fn-bs-durable-content)
                                  (fn-lg-scan fn-bs-take fn-lgk-frontier fn-lgk-committed
                                   fn-bs-apply-ops fn-bs-crash-select fn-bs-ops-for-ino
                                   fn-bs-ops-not-for-ino fn-lgp-apply-ops-keeps-the-prefix))
           :use ((:instance fn-lgp-apply-ops-keeps-the-prefix
                            (inodes (fn-bs-inodes bs)) (dirs (fn-bs-dirs bs)) (f (fn-lgk-frontier ks))
                            (ops (fn-bs-ops-for-ino (fn-bs-pending bs) ino)))
                 (:instance fn-lgp-apply-ops-keeps-the-prefix
                            (inodes (fn-bs-inodes bs)) (dirs (fn-bs-dirs bs)) (f (fn-lgk-frontier ks))
                            (ops (fn-bs-crash-select (fn-bs-ops-for-ino (fn-bs-pending bs) ino)
                                                     (cdr outcome) (fn-bs-unit bs)))))))))
(local
 (defthm fn-lgp-all-safep-of-append
 (equal (fn-lgp-all-safep (append a b) ino genesis max)
        (and (fn-lgp-all-safep a ino genesis max) (fn-lgp-all-safep b ino genesis max)))
 :hints (("Goal" :induct (append a b)
          :in-theory (union-theories '(fn-lgp-all-safep binary-append (:induction binary-append) car-cons cdr-cons)
                                    (theory 'minimal-theory))))))
(local
 (defthm fn-lgp-all-safep-member
 (implies (and (fn-lgp-all-safep pairs ino genesis max) (member-equal pair pairs))
          (fn-lgp-safep (car pair) (cdr pair) ino genesis max))
 :hints (("Goal" :induct (fn-lgp-all-safep pairs ino genesis max)
          :in-theory (union-theories '(fn-lgp-all-safep (:induction fn-lgp-all-safep) member-equal car-cons cdr-cons)
                                    (theory 'minimal-theory))))))
(local
 (defthm fn-lgp-relp-when-fields-agree
  (implies (and (fn-lgp-relp bs ks ino genesis max)
                (equal (fn-lgk-committed k2) (fn-lgk-committed ks))
                (equal (fn-lgk-last k2) (fn-lgk-last ks))
                (equal (fn-lgk-frontier k2) (fn-lgk-frontier ks))
                (equal (fn-lgk-inflight k2) (fn-lgk-inflight ks))
                (fn-lg-recordsp (fn-lgk-batch k2) max)
                (<= (fn-lgk-acked k2) (len (fn-lgk-committed ks))))
           (fn-lgp-relp bs k2 ino genesis max))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-lgp-relp fn-lgp-contentp)
                           (fn-lg-scan fn-lg-scan-last fn-lg-log mod fn-lg-recordsp fn-bs-take
                            fn-lg-zerosp fn-frame-digestp nthcdr fn-bs-durable-content
                            fn-lgk-committed fn-lgk-last fn-lgk-frontier fn-lgk-inflight
                            fn-lgk-batch fn-lgk-acked))))))
(local
 (defthm fn-lgp-relp-forward
  (implies (fn-lgp-relp bs ks ino genesis max)
           (and (fn-lg-recordsp (fn-lgk-batch ks) max)
                (<= (fn-lgk-acked ks) (len (fn-lgk-committed ks)))))
  :rule-classes :forward-chaining
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-lgp-relp fn-lgp-contentp)
                           (fn-lg-scan fn-lg-scan-last fn-lg-log mod fn-lg-recordsp fn-bs-take
                            fn-lg-zerosp fn-frame-digestp nthcdr fn-bs-durable-content
                            fn-lgk-committed fn-lgk-last fn-lgk-frontier fn-lgk-inflight
                            fn-lgk-batch fn-lgk-acked))))))
(local
 (defthm fn-lgp-prepare-preserves-relation
  (implies (and (fn-lgp-relp bs ks ino genesis max) (fn-lg-recordp record max))
           (fn-lgp-relp bs (fn-lgk-prepare ks record) ino genesis max))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-lgk-fields-of-make)
                           (fn-lgk-make fn-lgp-relp fn-lgk-committed fn-lgk-last fn-lgk-frontier
                            fn-lgk-next-txid fn-lgk-batch fn-lgk-inflight fn-lgk-acked fn-lgk-phase
                            fn-lg-recordp))
           :use ((:instance fn-lgp-relp-when-fields-agree (k2 (fn-lgk-prepare ks record))))))))
(local
 (defthm fn-lgp-finish-one-preserves-relation
  (implies (fn-lgp-relp bs ks ino genesis max)
           (fn-lgp-relp bs (fn-lgk-finish-one ks) ino genesis max))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-lgk-fields-of-make)
                           (fn-lgk-make fn-lgp-relp fn-lgk-committed fn-lgk-last fn-lgk-frontier
                            fn-lgk-next-txid fn-lgk-batch fn-lgk-inflight fn-lgk-acked fn-lgk-phase))
           :use ((:instance fn-lgp-relp-when-fields-agree (k2 (fn-lgk-finish-one ks))))))))
(local
 (defthm fn-lgp-t-prepare-preserves-relation
  (implies (and (fn-lgp-relp bs ks ino genesis max) (fn-lg-recordp record max))
           (fn-lgp-relp bs (fn-lgt-prepare ks record) ino genesis max))
  :hints (("Goal" :in-theory (disable fn-lgp-relp fn-lgk-prepare fn-lg-recordp)))))
(local
 (defthm fn-lgp-take-preserves-relation
  (implies (and (fn-lgp-relp bs ks ino genesis max) (fn-lg-recordp record max))
           (fn-lgp-relp bs (cadr (fn-olr-take ks record txid count octets bmax omax unit))
                        ino genesis max))
  :hints (("Goal" :in-theory (disable fn-lgk-prepare fn-lgp-relp fn-lg-recordp
                                      fn-olr-entry-octets)))))
(local
 (defthm fn-lgp-take-all
 (implies (true-listp x) (equal (fn-bs-take (len x) x) x))
 :hints (("Goal" :in-theory (enable fn-bs-take)))))
(local
 (defthm fn-lgp-splice-at-prefix
 (implies (and (true-listp d) (true-listp w))
          (equal (fn-bs-splice (append d z) (len d) w)
                 (append d (append w (nthcdr (len w) z)))))
 :hints (("Goal" :in-theory (enable fn-bs-splice)))))
(local
 (defthm fn-lgp-content-forward
 (implies (fn-lgp-contentp c ks unit genesis max)
          (and (<= (fn-lgk-frontier ks) (len c))
               (<= (+ (fn-lgk-frontier ks)
                      (len (fn-lg-log (fn-lgk-inflight ks) (fn-lgk-last ks) unit)))
                   (len c))))
 :rule-classes :forward-chaining))
(local
 (defthm fn-lgp-fence-content-splice
 (implies (fn-lgp-contentp c ks unit genesis max)
          (fn-lgp-contentp (fn-bs-splice c (fn-lgk-frontier ks)
                         (fn-lg-log (fn-lgk-inflight ks) (fn-lgk-last ks) unit))
                       (fn-lgk-fence ks unit) unit genesis max))
 :hints (("Goal" :do-not-induct t
          :in-theory (disable fn-lg-log fn-lgp-contentp fn-lgk-fence fn-bs-splice
                              fn-lgp-take-then-tail fn-lgp-splice-at-prefix
                              fn-lgp-fence-content fn-lgk-frontier)
          :use ((:instance fn-lgp-content-forward)
                (:instance fn-lgp-take-then-tail (n (fn-lgk-frontier ks)) (x c))
                (:instance fn-lgp-splice-at-prefix (d (fn-bs-take (fn-lgk-frontier ks) c))
                 (z (nthcdr (fn-lgk-frontier ks) c))
                 (w (fn-lg-log (fn-lgk-inflight ks) (fn-lgk-last ks) unit)))
                (:instance fn-lg-log-true-listp (records (fn-lgk-inflight ks))
                 (prev (fn-lgk-last ks)))
                (:instance fn-lgp-fence-content (d (fn-bs-take (fn-lgk-frontier ks) c))
                 (z (nthcdr (fn-lgk-frontier ks) c))))))))
(local
 (defthm fn-lgp-filter-after-fence
 (equal (fn-bs-ops-for-ino (fn-bs-ops-not-for-ino ops ino) ino) nil)
 :hints (("Goal" :induct (fn-bs-ops-not-for-ino ops ino)
          :in-theory (enable fn-bs-ops-for-ino fn-bs-ops-not-for-ino)))))
(local
 (defthm fn-lgp-fence-content-idle
 (implies (and (fn-lgp-contentp c ks unit genesis max) (not (consp (fn-lgk-inflight ks))))
          (fn-lgp-contentp c (fn-lgk-fence ks unit) unit genesis max))
 :hints (("Goal" :do-not-induct t
          :in-theory (disable fn-lg-scan fn-lg-scan-last fn-lg-recordsp)))))
(local
 (defthm fn-lgp-fence-preserves-relation
 (implies (fn-lgp-relp bs ks ino genesis max)
          (fn-lgp-relp (mv-nth 1 (fn-bs-fsync-file bs ino :ok))
                     (fn-lgk-fence ks (fn-bs-unit bs)) ino genesis max))
 :hints (("Goal" :do-not-induct t :cases ((consp (fn-lgk-inflight ks)))
          :in-theory (e/d (fn-lgp-relp fn-bs-fsync-file fn-bs-fence-file fn-bs-durable-content
                          fn-bs-apply-ops fn-bs-apply-op)
                         (fn-lgp-contentp fn-lg-log fn-lgk-fence fn-bs-splice fn-bs-put-assoc
                          fn-bs-ops-for-ino fn-bs-ops-not-for-ino))
          :use ((:instance fn-lgp-fence-content-splice (unit (fn-bs-unit bs))
                 (c (fn-bs-durable-content bs ino)))
                (:instance fn-lgp-fence-content-idle (unit (fn-bs-unit bs))
                 (c (fn-bs-durable-content bs ino))))))))
(local
 (defthm fn-lgp-head-present
 (implies (fn-lgp-headedp inodes ino) (assoc-equal ino inodes))
 :hints (("Goal" :in-theory (enable fn-lgp-headedp assoc-equal)))))
(local
 (defthm fn-lgp-append-preserves-relation
  (implies (and (fn-lgp-relp bs ks ino genesis max)
                (not (consp (fn-lgk-inflight ks)))
                (not (equal (fn-lgk-phase ks) :fault))
                (fn-lgk-fitsp ks (fn-bs-unit bs) (len (fn-bs-durable-content bs ino))))
           (fn-lgp-relp (mv-nth 1 (fn-bs-write bs ino (fn-lgk-frontier ks)
                                               (fn-lgk-append-octets ks (fn-bs-unit bs)) :ok))
                        (fn-lgk-append ks (fn-bs-unit bs) (len (fn-bs-durable-content bs ino)))
                        ino genesis max))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-bs-write fn-bs-durable-content fn-lgp-relp fn-lgp-contentp fn-bs-ops-for-ino-of-append)
                           (fn-lg-scan fn-lg-scan-last fn-lg-log fn-lg-recordsp))
           :use ((:instance fn-lg-log-true-listp (records (fn-lgk-batch ks))
                            (prev (fn-lgk-last ks)) (unit (fn-bs-unit bs))))))))
(local
 (defthm fn-lgp-filter-one-write
 (equal (fn-bs-ops-for-ino (list (list :write ino off x)) ino)
        (list (list :write ino off x)))
 :hints (("Goal" :in-theory (enable fn-bs-ops-for-ino)))))
(local
 (defthm fn-lgp-zeros-true-listp (true-listp (fn-bs-zeros n))))
(local
 (defthm fn-lgp-take-zeros
 (implies (natp n) (equal (fn-bs-take n (fn-bs-zeros n)) (fn-bs-zeros n)))
 :hints (("Goal" :use ((:instance fn-lgp-take-all (x (fn-bs-zeros n))))))))
(local
 (defthm fn-lgp-len-zeros
 (equal (len (fn-bs-zeros n)) (nfix n))
 :hints (("Goal" :in-theory (enable fn-bs-zeros)))))
(local
 (defthm fn-lgp-length-of-splice
 (equal (len (fn-bs-splice c off x))
        (+ (nfix off) (len x) (nfix (- (len c) (+ (nfix off) (len x))))))
 :hints (("Goal" :in-theory (enable fn-bs-splice)))))
(local
 (defthm fn-lgp-content-of-extension
 (implies (and (fn-lgp-contentp c ks unit genesis max)
               (not (consp (fn-lgk-inflight ks)))
               (natp next) (<= (len c) next))
          (and (fn-lgp-contentp (fn-bs-splice c (len c) (fn-bs-zeros (- next (len c))))
                              ks unit genesis max)
               (equal (len (fn-bs-splice c (len c) (fn-bs-zeros (- next (len c))))) next)))
 :hints (("Goal" :do-not-induct t
          :in-theory (e/d (fn-lgp-contentp)
                          (fn-lg-scan fn-lg-scan-last fn-lg-log fn-lg-recordsp fn-bs-splice fn-bs-zeros fn-bs-take))
          :use ((:instance fn-lgp-splice-keeps-the-prefix
                 (f (fn-lgk-frontier ks)) (off (len c)) (old c)
                 (oct (fn-bs-zeros (- next (len c))))))))))
(local
 (defthm fn-lgp-extend-keeps-the-relation
 (implies (and (fn-lgp-relp bs ks ino genesis max)
               (not (consp (fn-lgk-inflight ks)))
               (equal extent (len (fn-bs-durable-content bs ino)))
               (natp next) (<= extent next))
          (mv-let (pairs bs2 ok) (fn-lgu-extend bs k ino extent next eo1 eo2)
           (declare (ignore pairs))
           (implies ok
            (and (fn-lgp-relp bs2 ks ino genesis max)
                 (equal (len (fn-bs-durable-content bs2 ino)) next)))))
 :hints (("Goal" :do-not-induct t :cases ((equal next extent))
          :in-theory (e/d (fn-lgu-extend fn-lgp-relp fn-bs-write fn-bs-fsync-file fn-bs-fence-file
                           fn-bs-durable-content fn-bs-apply-op fn-bs-apply-ops
                           fn-bs-ops-for-ino-of-append)
                          (fn-lgp-contentp fn-bs-splice fn-bs-zeros fn-bs-put-assoc
                           fn-bs-ops-for-ino fn-bs-ops-not-for-ino fn-lgk-inflight))
          :use ((:instance fn-lgp-content-of-extension
                 (c (fn-bs-durable-content bs ino)) (unit (fn-bs-unit bs))))))))
(local
 (defthm fn-lgp-fence-failed-keeps-the-relation
  (implies (fn-lgp-relp bs ks ino genesis max)
           (fn-lgp-relp bs (fn-lgk-fence-failed ks) ino genesis max))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-lgk-fields-of-make fn-lgk-fence-failed)
                           (fn-lgk-make fn-lgp-relp fn-lgk-committed fn-lgk-last fn-lgk-frontier
                            fn-lgk-next-txid fn-lgk-batch fn-lgk-inflight fn-lgk-acked fn-lgk-phase))
           :use ((:instance fn-lgp-relp-forward)
                 (:instance fn-lgp-relp-when-fields-agree (k2 (fn-lgk-fence-failed ks))))))))
(local
 (defthm fn-lgp-consume-to-keeps-the-relation
  (implies (fn-lgp-relp bs ks ino genesis max)
           (fn-lgp-relp bs (fn-olr-consume-to ks txid) ino genesis max))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-lgk-fields-of-make fn-olr-consume-to)
                           (fn-lgk-make fn-lgp-relp fn-lgk-committed fn-lgk-last fn-lgk-frontier
                            fn-lgk-next-txid fn-lgk-batch fn-lgk-inflight fn-lgk-acked fn-lgk-phase))
           :use ((:instance fn-lgp-relp-forward)
                 (:instance fn-lgp-relp-when-fields-agree (k2 (fn-olr-consume-to ks txid))))))))
(local
 (defthm fn-lgp-kernel-op-keeps-the-relation
   (implies (and (fn-lgp-relp bs ks ino genesis max)
                 (fn-lgu-kernel-op-p op)
                 (implies (member-equal (car op) '(:prepare :take))
                          (fn-lg-recordp (nth 1 op) max)))
            (fn-lgp-relp bs (fn-lgk-host-step ks op) ino genesis max))
   :hints (("Goal" :do-not-induct t
            :in-theory (union-theories '(fn-lgk-host-step fn-lgu-kernel-op-p member-equal)
                                       (theory 'minimal-theory))
            :use ((:instance fn-lgp-t-prepare-preserves-relation (record (nth 1 op)))
                  (:instance fn-lgp-take-preserves-relation
                             (record (nth 1 op)) (txid (nth 2 op)) (count (nth 3 op))
                             (octets (nth 4 op)) (bmax (nth 5 op)) (omax (nth 6 op)) (unit (nth 7 op)))
                  (:instance fn-lgp-consume-to-keeps-the-relation (txid (nth 1 op)))
                  (:instance fn-lgp-finish-one-preserves-relation)
                  (:instance fn-lgp-fence-failed-keeps-the-relation))))))
(local
 (defthm fn-lgp-kernel-op-fields-under-fault
   (implies (and (equal (fn-lgk-phase ks) :fault)
                 (<= (fn-lgk-acked ks) (len (fn-lgk-committed ks)))
                 (fn-lgu-kernel-op-p op))
            (let ((k2 (fn-lgk-host-step ks op)))
              (and (equal (fn-lgk-phase k2) :fault)
                   (equal (fn-lgk-committed k2) (fn-lgk-committed ks))
                   (equal (fn-lgk-frontier k2) (fn-lgk-frontier ks))
                   (<= (fn-lgk-acked k2) (len (fn-lgk-committed ks))))))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-lgk-host-step fn-lgu-kernel-op-p fn-lgt-prepare fn-lgk-prepare
                             fn-olr-take fn-olr-consume-to fn-lgk-finish-one fn-lgk-fence-failed
                             fn-lgk-fields-of-make)
                            (fn-lgk-make fn-lgk-committed fn-lgk-last fn-lgk-frontier
                             fn-lgk-next-txid fn-lgk-batch fn-lgk-inflight fn-lgk-acked fn-lgk-phase
                             fn-lgk-append fn-lgk-fence fn-lgs-rotate
                             fn-lgs-rotate-admitsp fn-lgk-sealed-extent fn-olr-entry-octets))))))
(local
 (defthm fn-lgp-kernel-op-keeps-the-fault
   (implies (and (equal (fn-lgk-phase ks) :fault)
                 (fn-lgp-safep bs ks ino genesis max)
                 (fn-lgu-kernel-op-p op))
            (and (equal (fn-lgk-phase (fn-lgk-host-step ks op)) :fault)
                 (fn-lgp-safep bs (fn-lgk-host-step ks op) ino genesis max)))
   :hints (("Goal" :do-not-induct t
            :in-theory (disable fn-lgp-safep fn-lgk-host-step fn-lgu-kernel-op-p
                                fn-lgk-phase fn-lgk-committed fn-lgk-frontier fn-lgk-acked)
            :use ((:instance fn-lgp-safep-acked-within)
                  (:instance fn-lgp-kernel-op-fields-under-fault)
                  (:instance fn-lgp-safep-when-fields-agree (k2 (fn-lgk-host-step ks op))))))))
(local
 (defthm fn-lgp-safep-frontier-within
   (implies (fn-lgp-safep bs ks ino genesis max)
            (<= (fn-lgk-frontier ks) (len (fn-bs-durable-content bs ino))))
   :rule-classes :linear))
(local
 (defthm fn-lgp-extend-keeps-safe
  (implies (and (fn-lgp-safep bs k ino genesis max)
                (equal extent (len (fn-bs-durable-content bs ino))))
           (mv-let (pairs bs2 ok) (fn-lgu-extend bs k ino extent next eo1 eo2)
             (declare (ignore ok))
             (and (fn-lgp-all-safep pairs ino genesis max)
                  (fn-lgp-safep bs2 k ino genesis max)
                  (equal (fn-bs-unit bs2) (fn-bs-unit bs)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-lgp-safep fn-bs-write fn-bs-fsync-file fn-bs-zeros
                               fn-bs-durable-content fn-lgk-frontier)))))
(local
 (defthm fn-lgp-sealed-extent-facts
 (implies (natp extent)
          (let ((next (fn-lgk-sealed-extent ks extent unit)))
           (and (natp next) (<= extent next))))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d (fn-lgk-sealed-extent fn-olr-extension-needed-p fn-olr-extension-target)
                                (fn-lgk-append-octets fn-lg-log fn-lgc-sealed-extent-of-abstraction))))))
(local
 (defthm fn-lgp-fields-of-append
   (let ((k2 (fn-lgk-append ks unit extent)))
     (and (equal (fn-lgk-committed k2) (fn-lgk-committed ks))
          (equal (fn-lgk-frontier k2) (fn-lgk-frontier ks))
          (equal (fn-lgk-acked k2) (fn-lgk-acked ks))))
   :hints (("Goal" :in-theory (e/d (fn-lgk-append fn-lgk-fields-of-make)
                                   (fn-lgk-make fn-lgk-committed fn-lgk-frontier fn-lgk-acked
                                    fn-lgk-fitsp fn-lgk-inflight fn-lgk-phase fn-lgk-batch))))))
(local
 (defthm fn-lgp-fields-of-fence-failed
   (let ((k2 (fn-lgk-fence-failed ks)))
     (and (equal (fn-lgk-committed k2) (fn-lgk-committed ks))
          (equal (fn-lgk-frontier k2) (fn-lgk-frontier ks))
          (equal (fn-lgk-acked k2) (fn-lgk-acked ks))
          (equal (fn-lgk-phase k2) :fault)))
   :hints (("Goal" :in-theory (e/d (fn-lgk-fence-failed fn-lgk-fields-of-make)
                                   (fn-lgk-make fn-lgk-committed fn-lgk-frontier fn-lgk-acked
                                    fn-lgk-phase))))))
(local
 (defthm fn-lgp-safe-of-append-and-fence-failed
   (implies (fn-lgp-safep bs ks ino genesis max)
            (and (fn-lgp-safep bs (fn-lgk-append ks unit extent) ino genesis max)
                 (fn-lgp-safep bs (fn-lgk-fence-failed ks) ino genesis max)))
   :hints (("Goal" :in-theory (disable fn-lgp-safep fn-lgk-append fn-lgk-fence-failed)
            :use ((:instance fn-lgp-safep-acked-within)
                  (:instance fn-lgp-safep-when-fields-agree (k2 (fn-lgk-append ks unit extent)))
                  (:instance fn-lgp-safep-when-fields-agree (k2 (fn-lgk-fence-failed ks))))))))
(local
 (defthm fn-lgp-seal-step-from-the-relation
   (implies (and (fn-lgp-relp bs ks ino genesis max)
                 (consp op) (equal (car op) :seal))
            (mv-let (pairs bs1 ks1) (fn-lgu-host-step bs ks op ino max)
              (and (fn-lgp-all-safep pairs ino genesis max)
                   (fn-lgp-invp bs1 ks1 ino genesis max)
                   (equal (fn-bs-unit bs1) (fn-bs-unit bs)))))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-lgu-host-step fn-lgp-invp fn-lg-append-admitsp)
                            (fn-lgp-relp fn-lgp-safep fn-lgu-extend fn-bs-write fn-bs-fsync-file
                             fn-lgk-append fn-lgk-fence-failed fn-lgk-sealed-extent fn-lgk-append-octets
                             fn-lgk-fitsp fn-bs-durable-content fn-lgk-frontier fn-lgk-inflight
                             fn-lgk-phase mod
                             fn-lgp-append-preserves-relation fn-lgp-extend-keeps-the-relation
                             fn-lgp-extend-keeps-safe))
            :use (
                  (:instance fn-lgp-related-state-is-safe)
                  (:instance fn-lgp-sealed-extent-facts
                             (unit (fn-bs-unit bs)) (extent (len (fn-bs-durable-content bs ino))))
                  (:instance fn-lgp-extend-keeps-safe
                             (k (fn-lgk-append ks (fn-bs-unit bs)
                                               (fn-lgk-sealed-extent ks (len (fn-bs-durable-content bs ino))
                                                                     (fn-bs-unit bs))))
                             (extent (len (fn-bs-durable-content bs ino)))
                             (next (fn-lgk-sealed-extent ks (len (fn-bs-durable-content bs ino))
                                                         (fn-bs-unit bs)))
                             (eo1 (nth 1 op)) (eo2 (nth 2 op)))
                  (:instance fn-lgp-extend-keeps-the-relation
                             (k (fn-lgk-append ks (fn-bs-unit bs)
                                               (fn-lgk-sealed-extent ks (len (fn-bs-durable-content bs ino))
                                                                     (fn-bs-unit bs))))
                             (extent (len (fn-bs-durable-content bs ino)))
                             (next (fn-lgk-sealed-extent ks (len (fn-bs-durable-content bs ino))
                                                         (fn-bs-unit bs)))
                             (eo1 (nth 1 op)) (eo2 (nth 2 op)))
                  (:instance fn-lgp-append-preserves-relation
                             (bs (mv-nth 1 (fn-lgu-extend bs
                                                          (fn-lgk-append ks (fn-bs-unit bs)
                                                                         (fn-lgk-sealed-extent ks (len (fn-bs-durable-content bs ino))
                                                                                               (fn-bs-unit bs)))
                                                          ino (len (fn-bs-durable-content bs ino))
                                                          (fn-lgk-sealed-extent ks (len (fn-bs-durable-content bs ino))
                                                                                (fn-bs-unit bs))
                                                          (nth 1 op) (nth 2 op)))))
                  (:instance fn-lgp-write-keeps-safe
                             (bs (mv-nth 1 (fn-lgu-extend bs
                                                          (fn-lgk-append ks (fn-bs-unit bs)
                                                                         (fn-lgk-sealed-extent ks (len (fn-bs-durable-content bs ino))
                                                                                               (fn-bs-unit bs)))
                                                          ino (len (fn-bs-durable-content bs ino))
                                                          (fn-lgk-sealed-extent ks (len (fn-bs-durable-content bs ino))
                                                                                (fn-bs-unit bs))
                                                          (nth 1 op) (nth 2 op))))
                             (ks (fn-lgk-append ks (fn-bs-unit bs)
                                                (fn-lgk-sealed-extent ks (len (fn-bs-durable-content bs ino))
                                                                      (fn-bs-unit bs))))
                             (off (fn-lgk-frontier ks))
                             (octets (fn-lgk-append-octets ks (fn-bs-unit bs)))
                             (outcome (nth 3 op))))))))
(local
 (defthm fn-lgp-unit-of-fsync-any
   (equal (fn-bs-unit (mv-nth 1 (fn-bs-fsync-file s ino outcome))) (fn-bs-unit s))
   :hints (("Goal" :in-theory (enable fn-bs-fsync-file fn-bs-fence-file)))))
(local
 (defthm fn-lgp-fence-step-from-the-relation
   (implies (and (fn-lgp-relp bs ks ino genesis max)
                 (consp op) (equal (car op) :fence))
            (mv-let (pairs bs1 ks1) (fn-lgu-host-step bs ks op ino max)
              (and (fn-lgp-all-safep pairs ino genesis max)
                   (fn-lgp-invp bs1 ks1 ino genesis max)
                   (equal (fn-bs-unit bs1) (fn-bs-unit bs)))))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-lgu-host-step fn-lgp-invp)
                            (fn-lgp-relp fn-lgp-safep fn-bs-fsync-file fn-lgk-fence
                             fn-lgk-fence-failed fn-lgk-phase))
            :use ((:instance fn-lgp-related-state-is-safe)
                  (:instance fn-lgp-fence-preserves-relation)
                  (:instance fn-lgp-related-state-is-safe
                             (bs (mv-nth 1 (fn-bs-fsync-file bs ino :ok)))
                             (ks (fn-lgk-fence ks (fn-bs-unit bs))))
                  (:instance fn-lgp-fsync-keeps-safe (outcome (nth 1 op))))))))
(local
 (defthm fn-lgp-step-from-the-fault
   (implies (and (equal (fn-lgk-phase ks) :fault)
                 (fn-lgp-safep bs ks ino genesis max))
            (mv-let (pairs bs1 ks1) (fn-lgu-host-step bs ks op ino max)
              (and (fn-lgp-all-safep pairs ino genesis max)
                   (fn-lgp-invp bs1 ks1 ino genesis max)
                   (equal (fn-bs-unit bs1) (fn-bs-unit bs)))))
   :hints (("Goal" :do-not-induct t
            :in-theory (e/d (fn-lgu-host-step fn-lgp-invp fn-lg-append-admitsp)
                            (fn-lgp-relp fn-lgp-safep fn-lgk-host-step fn-lgu-kernel-op-p
                             fn-lgk-phase fn-lgk-inflight fn-lgk-fitsp fn-lgu-extend fn-bs-write
                             fn-bs-fsync-file fn-lgk-sealed-extent))
            :use ((:instance fn-lgp-kernel-op-keeps-the-fault))))))
(local
 (defthm fn-lgp-host-step-of-a-kernel-op
   (implies (and (fn-lgu-kernel-op-p op)
                 (implies (member-equal (car op) '(:prepare :take))
                          (equal (fn-lgu-take-verdict (nth 1 op) max) :admissible)))
            (equal (fn-lgu-host-step bs ks op ino max)
                   (list (list (cons bs (fn-lgk-host-step ks op))) bs (fn-lgk-host-step ks op))))
   :hints (("Goal" :in-theory (disable fn-lgk-host-step fn-lgu-take-verdict)))))
(local
 (defthm fn-lgp-host-step-of-a-refused-take
   (implies (and (fn-lgu-kernel-op-p op)
                 (member-equal (car op) '(:prepare :take))
                 (not (equal (fn-lgu-take-verdict (nth 1 op) max) :admissible)))
            (equal (fn-lgu-host-step bs ks op ino max) (list nil bs ks)))
   :hints (("Goal" :in-theory (disable fn-lgk-host-step fn-lgu-take-verdict)))))
(local
 (defthm fn-lgp-host-step-of-nothing
   (implies (and (not (fn-lgu-kernel-op-p op))
                 (not (and (consp op) (equal (car op) :seal)))
                 (not (and (consp op) (equal (car op) :fence))))
            (equal (fn-lgu-host-step bs ks op ino max) (list nil bs ks)))
   :hints (("Goal" :in-theory (disable fn-lgk-host-step)))))
(local
 (defthm fn-lgp-step-from-the-relation
   (implies (fn-lgp-relp bs ks ino genesis max)
            (mv-let (pairs bs1 ks1) (fn-lgu-host-step bs ks op ino max)
              (and (fn-lgp-all-safep pairs ino genesis max)
                   (fn-lgp-invp bs1 ks1 ino genesis max)
                   (equal (fn-bs-unit bs1) (fn-bs-unit bs)))))
   :hints (("Goal" :do-not-induct t
            :cases ((and (fn-lgu-kernel-op-p op)
                         (member-equal (car op) '(:prepare :take))
                         (not (equal (fn-lgu-take-verdict (nth 1 op) max) :admissible)))
                    (fn-lgu-kernel-op-p op)
                    (and (consp op) (equal (car op) :seal))
                    (and (consp op) (equal (car op) :fence)))
            :in-theory (e/d (fn-lgp-invp)
                            (fn-lgp-relp fn-lgp-safep fn-lgk-host-step fn-lgu-host-step
                             fn-lgu-kernel-op-p fn-lg-recordp fn-lgu-take-verdict
                             fn-lgp-host-step-of-a-kernel-op fn-lgp-host-step-of-a-refused-take
                             fn-lgp-seal-step-from-the-relation fn-lgp-fence-step-from-the-relation))
            :use ((:instance fn-lgu-take-verdict-admits-exactly-log-records (record (nth 1 op)))
                  (:instance fn-lgp-host-step-of-a-kernel-op)
                  (:instance fn-lgp-host-step-of-a-refused-take)
                  (:instance fn-lgp-seal-step-from-the-relation)
                  (:instance fn-lgp-fence-step-from-the-relation)
                  (:instance fn-lgp-kernel-op-keeps-the-relation)
                  (:instance fn-lgp-related-state-is-safe
                             (ks (fn-lgk-host-step ks op))))))))
(local
 (defthm fn-lgp-invp-is-safe
   (implies (fn-lgp-invp bs ks ino genesis max)
            (fn-lgp-safep bs ks ino genesis max))
   :hints (("Goal" :in-theory (disable fn-lgp-safep fn-lgp-relp)))))
(local
 (defthm fn-lgp-step-keeps-the-invariant
   (implies (fn-lgp-invp bs ks ino genesis max)
            (and (fn-lgp-all-safep (mv-nth 0 (fn-lgu-host-step bs ks op ino max)) ino genesis max)
                 (fn-lgp-invp (mv-nth 1 (fn-lgu-host-step bs ks op ino max))
                              (mv-nth 2 (fn-lgu-host-step bs ks op ino max)) ino genesis max)))
   :hints (("Goal" :do-not-induct t
            :in-theory (union-theories '(fn-lgp-invp) (theory 'minimal-theory))
            :use ((:instance fn-lgp-step-from-the-relation)
                  (:instance fn-lgp-step-from-the-fault))))))
(local
 (defthm fn-lgp-host-run-is-safe
  (implies (fn-lgp-invp bs ks ino genesis max)
           (fn-lgp-all-safep (fn-lgu-host-run bs ks ops ino max) ino genesis max))
  :hints (("Goal" :induct (fn-lgu-host-run bs ks ops ino max)
           :in-theory (union-theories '(fn-lgu-host-run fn-lgp-all-safep fn-lgp-all-safep-of-append
                                        fn-lgp-invp-is-safe car-cons cdr-cons
                                        (:induction fn-lgu-host-run))
                                      (theory 'minimal-theory)))
          ("Subgoal *1/2" :use ((:instance fn-lgp-step-keeps-the-invariant (op (car ops))))))))
(local
 (defthm fn-lgp-acknowledged-records-are-recovered-at-every-cut
  (implies (and (fn-lgp-relp bs ks ino genesis max)
                (member-equal pair (fn-lgu-host-run bs ks ops ino max))
                (fn-bs-crash-imagep (car pair) image))
           (let ((a (fn-lgk-acked (cdr pair)))
                 (recovered (fn-lgk-committed
                             (fn-lgk-recover (fn-bs-durable-content image ino)
                                             genesis (fn-bs-unit (car pair)) max next-txid))))
             (and (<= a (len recovered))
                  (equal (take a recovered) (take a (fn-lgk-committed (cdr pair)))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn-lgp-invp) (theory 'minimal-theory))
           :use ((:instance fn-lgp-host-run-is-safe)
                 (:instance fn-lgp-all-safep-member (pairs (fn-lgu-host-run bs ks ops ino max)))
                 (:instance fn-lgp-safe-image-recovers-the-acknowledged-records
                            (bs (car pair)) (ks (cdr pair))))))))
(local
 (defthm fn-lgu-host-final-is-a-cut
   (member-equal (fn-lgu-host-final bs ks ops ino max) (fn-lgu-host-run bs ks ops ino max))
   :hints (("Goal" :induct (fn-lgu-host-final bs ks ops ino max)
            :in-theory (disable fn-lgu-host-step)))))
(local
 (defthm fn-lgu-host-final-of-append
   (equal (fn-lgu-host-final bs ks (append x y) ino max)
          (let ((f (fn-lgu-host-final bs ks x ino max)))
            (fn-lgu-host-final (car f) (cdr f) y ino max)))
   :hints (("Goal" :induct (fn-lgu-host-final bs ks x ino max)
            :in-theory (disable fn-lgu-host-step)))))
(local
 (defthm fn-lgu-host-kops-of-append
   (equal (fn-lgu-host-kops bs ks (append x y) ino max)
          (let ((f (fn-lgu-host-final bs ks x ino max)))
            (append (fn-lgu-host-kops bs ks x ino max)
                    (fn-lgu-host-kops (car f) (cdr f) y ino max))))
   :hints (("Goal" :induct (fn-lgu-host-final bs ks x ino max)
            :in-theory (disable fn-lgu-host-step fn-lgu-step-kops)))))
(local
 (defthm fn-lgu-step-kops-of-finish-one
   (equal (fn-lgu-step-kops bs ks '(:finish-one) ino max) '((:finish-one)))
   :hints (("Goal" :in-theory (enable fn-lgu-step-kops fn-lgu-kernel-op-p)))))
(local
 (defthm fn-lgu-host-step-of-finish-one-bs
   (equal (mv-nth 1 (fn-lgu-host-step bs ks '(:finish-one) ino max)) bs)
   :hints (("Goal" :in-theory (e/d (fn-lgu-host-step fn-lgu-kernel-op-p) (fn-lgk-host-step))))))
(local
 (defun fn-lgu-kops-fin-ind (n bs ks ino max)
   (declare (xargs :guard t :verify-guards nil))
   (if (zp n) (list bs ks)
     (mv-let (pairs bs1 ks1) (fn-lgu-host-step bs ks '(:finish-one) ino max)
       (declare (ignore pairs bs1))
       (fn-lgu-kops-fin-ind (1- n) bs ks1 ino max)))))
(local
 (defthm fn-lgu-host-kops-of-finishes
   (equal (fn-lgu-host-kops bs ks (fn-lgu-finishes n) ino max)
          (fn-lgu-finishes n))
   :hints (("Goal" :induct (fn-lgu-kops-fin-ind n bs ks ino max)
            :expand ((fn-lgu-finishes n)
                     (:free (op rest) (fn-lgu-host-kops bs ks (cons op rest) ino max)))
            :in-theory (union-theories '(fn-lgu-kops-fin-ind fn-lgu-step-kops-of-finish-one
                                         fn-lgu-host-step-of-finish-one-bs zp
                                         car-cons cdr-cons (:executable-counterpart fn-lgu-finishes)
                                         append-to-nil binary-append (:induction fn-lgu-kops-fin-ind)
                                         fn-lgu-host-kops)
                                       (theory 'minimal-theory))))))
(local
 (defthm fn-lgp-lgc-host-run-of-append
   (equal (fn-lgc-host-run c (append x y)) (fn-lgc-host-run (fn-lgc-host-run c x) y))
   :hints (("Goal" :induct (fn-lgc-host-run c x) :in-theory (disable fn-lgc-host-step)))))
(local
 (defthm fn-lgp-host-kernel-acknowledges-only-recoverable-records
  (let* ((ks0 (fn-lgt-recover (fn-lgd-octets s) genesis (fn-bs-unit bs) max floor))
         (final (fn-lgu-host-final bs ks0 ops ino max))
         (host (fn-lgc-host-run (mv-nth 1 (fn-lgc-open s genesis (fn-bs-unit bs) max floor))
                                (fn-lgu-host-kops bs ks0 ops ino max))))
    (implies (fn-lgp-relp bs ks0 ino genesis max)
             (and (equal (fn-lgc-acked host) (fn-lgk-acked (cdr final)))
                  (implies (fn-bs-crash-imagep (car final) image)
                           (let ((a (fn-lgc-acked host))
                                 (recovered (fn-lgk-committed
                                             (fn-lgk-recover (fn-bs-durable-content image ino)
                                                             genesis (fn-bs-unit (car final)) max
                                                             next-txid))))
                             (and (<= a (len recovered))
                                  (equal (take a recovered)
                                         (take a (fn-lgk-committed (cdr final))))))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn-lgc-observers-of-abstraction
                                        fn-lgu-host-kops-run-to-the-final-kernel)
                                      (theory 'minimal-theory))
           :use ((:instance fn-lgc-run-refines-the-kernel
                            (unit (fn-bs-unit bs))
                            (ops (fn-lgu-host-kops bs (fn-lgt-recover (fn-lgd-octets s) genesis
                                                                      (fn-bs-unit bs) max floor)
                                                   ops ino max)))
                 (:instance fn-lgu-host-final-is-a-cut
                            (ks (fn-lgt-recover (fn-lgd-octets s) genesis (fn-bs-unit bs) max floor)))
                 (:instance fn-lgp-acknowledged-records-are-recovered-at-every-cut
                            (ks (fn-lgt-recover (fn-lgd-octets s) genesis (fn-bs-unit bs) max floor))
                            (pair (fn-lgu-host-final
                                   bs (fn-lgt-recover (fn-lgd-octets s) genesis (fn-bs-unit bs) max floor)
                                   ops ino max))))))))
(defthm fn-lgp-acknowledge-acknowledges-only-recoverable-records
  (let* ((ks0 (fn-lgt-recover (fn-lgd-octets s) genesis (fn-bs-unit bs) max floor))
         (run (fn-lgu-host-run bs ks0 (append ops (fn-lgu-finishes n)) ino max))
         (final (fn-lgu-host-final bs ks0 (append ops (fn-lgu-finishes n)) ino max))
         (host (fn-lgu-acknowledge
                (fn-lgc-host-run (mv-nth 1 (fn-lgc-open s genesis (fn-bs-unit bs) max floor))
                                 (fn-lgu-host-kops bs ks0 ops ino max))
                n)))
    (implies (fn-lgp-relp bs ks0 ino genesis max)
             (and
              ;; the count the host holds after acknowledging is the run's
              (equal (fn-lgc-acked host) (fn-lgk-acked (cdr final)))
              ;; ... and every crash image of the store it leaves recovers it
              (implies (fn-bs-crash-imagep (car final) image)
                       (let ((a (fn-lgc-acked host))
                             (recovered (fn-lgk-committed
                                         (fn-lgk-recover (fn-bs-durable-content image ino)
                                                         genesis (fn-bs-unit (car final)) max next-txid))))
                         (and (<= a (len recovered))
                              (equal (take a recovered) (take a (fn-lgk-committed (cdr final)))))))
              ;; at EVERY cut of the run, its acknowledged records are recovered
              ;; from every crash image of the cut
              (implies (and (member-equal pair run)
                            (fn-bs-crash-imagep (car pair) image))
                       (let ((a (fn-lgk-acked (cdr pair)))
                             (recovered (fn-lgk-committed
                                         (fn-lgk-recover (fn-bs-durable-content image ino)
                                                         genesis (fn-bs-unit (car pair)) max next-txid))))
                         (and (<= a (len recovered))
                              (equal (take a recovered) (take a (fn-lgk-committed (cdr pair))))))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn-lgu-acknowledge fn-lgu-host-kops-of-append
                                        fn-lgu-host-kops-of-finishes fn-lgp-lgc-host-run-of-append)
                                      (theory 'minimal-theory))
           :use ((:instance fn-lgp-host-kernel-acknowledges-only-recoverable-records
                            (ops (append ops (fn-lgu-finishes n))))
                 (:instance fn-lgp-acknowledged-records-are-recovered-at-every-cut
                            (ks (fn-lgt-recover (fn-lgd-octets s) genesis (fn-bs-unit bs) max floor))
                            (ops (append ops (fn-lgu-finishes n))))))))
(local
 (defun fn-lgp-take2-ind (m n x)
 (if (zp m) (list n x) (fn-lgp-take2-ind (1- m) (1- n) (cdr x)))))
(local
 (defun fn-lgp-drop-ind (k n x)
 (if (zp k) (list n x) (fn-lgp-drop-ind (1- k) (1- n) (cdr x)))))
(defthm fn-lgp-take-of-take
 (implies (and (natp m) (natp n) (<= m n))
          (equal (fn-bs-take m (fn-bs-take n x)) (fn-bs-take m x)))
 :hints (("Goal" :induct (fn-lgp-take2-ind m n x) :in-theory (enable fn-bs-take))))
(local
 (defthm fn-lgp-take-of-tail-of-take
 (implies (and (natp k) (natp m) (natp n) (<= (+ k m) n))
          (equal (fn-bs-take m (nthcdr k (fn-bs-take n x)))
                 (fn-bs-take m (nthcdr k x))))))
(local
 (defthm fn-lgp-tail-of-take
 (implies (and (natp k) (natp n) (<= k n))
          (equal (nthcdr k (fn-bs-take n x)) (fn-bs-take (- n k) (nthcdr k x))))
 :hints (("Goal" :induct (fn-lgp-drop-ind k n x) :in-theory (enable fn-bs-take)))))
(local
 (defthm fn-lgp-declared-len-of-padded-take
 (implies (and (natp n) (<= *fn-frame-header-octets* n)
               (<= *fn-frame-header-octets* (len x)))
          (equal (fn-lg-declared-len (fn-bs-take n x)) (fn-lg-declared-len x)))
 :hints (("Goal" :in-theory (e/d (fn-lg-declared-len)
                                (fn-cbor-u32-from fn-cbor-octet-listp fn-bs-take))))))
(local
 (defthm fn-lgp-slice-of-padded-take
 (implies (and (natp n) (consp (fn-lg-slice x)) (<= (len (fn-lg-slice x)) n))
          (equal (fn-lg-slice (fn-bs-take n x)) (fn-lg-slice x)))
 :hints (("Goal" :in-theory (e/d (fn-lg-slice)
                                (fn-lg-declared-len fn-bs-take fn-lg-slice-len))
          :use ((:instance fn-lg-slice-len (octets x)))))))
(defthm fn-lgp-scan-of-consumed-prefix
 (let ((f (cdr (fn-lg-scan x prev unit max))))
  (and (equal (fn-lg-scan (fn-bs-take f x) prev unit max) (fn-lg-scan x prev unit max))
       (equal (fn-lg-scan-last (fn-bs-take f x) prev unit max)
              (fn-lg-scan-last x prev unit max))))
 :hints (("Goal" :induct (fn-lg-scan x prev unit max)
          :expand ((fn-lg-scan x prev unit max) (fn-lg-scan-last x prev unit max))
          :in-theory (e/d ((:induction fn-lg-scan)) (fn-lg-slice fn-lg-entry-okp fn-lg-slice-records fn-lg-pad-len
                              fn-lg-declared-len fn-lg-slice-len fn-lg-trailer fn-bs-take (:definition fn-lg-scan) fn-lg-scan-last)))
         ("Subgoal *1/1" :expand ((fn-lg-scan x prev unit max) (fn-lg-scan-last x prev unit max)
                                  (fn-lg-scan (fn-bs-take 0 x) prev unit max)
                                  (fn-lg-scan-last (fn-bs-take 0 x) prev unit max)
                                  (fn-bs-take 0 x)))
         ("Subgoal *1/2"
          :expand ((fn-lg-scan x prev unit max) (fn-lg-scan-last x prev unit max)
                   (:free (n) (fn-lg-scan (fn-bs-take n x) prev unit max))
                   (:free (n) (fn-lg-scan-last (fn-bs-take n x) prev unit max)))
          :use ((:instance fn-lg-entry-okp-consp (slice (fn-lg-slice x)))))))
(local
 (defthm fn-lgp-apply-writes-keeps-head
 (implies (fn-lgp-headedp inodes ino) (fn-lgp-headedp (fn-bs-apply-writes inodes ops) ino))
 :hints (("Goal" :induct (fn-bs-apply-writes inodes ops)
          :in-theory (e/d (fn-bs-apply-writes) (fn-lgp-headedp fn-bs-put-assoc fn-bs-splice))))))
(local
 (defthm fn-lgp-apply-writes-last
 (implies (fn-lgp-headedp inodes ino)
          (equal (cdr (assoc-equal ino (fn-bs-apply-writes inodes (append ops (list (list :write ino 0 x))))))
                 (fn-bs-splice (cdr (assoc-equal ino (fn-bs-apply-writes inodes ops))) 0 x)))
 :hints (("Goal" :in-theory (e/d (fn-bs-apply-writes-of-append)
                                (fn-bs-splice fn-bs-put-assoc fn-bs-apply-writes))
          :expand ((:free (in) (fn-bs-apply-writes in (list (list :write ino 0 x))))
                   (:free (in) (fn-bs-apply-writes in nil)))))))
(local
 (defthm fn-lgp-splice-prefix
 (implies (true-listp x)
          (and (equal (fn-bs-take (len x) (fn-bs-splice old 0 x)) x)
               (<= (len x) (len (fn-bs-splice old 0 x)))))
 :hints (("Goal" :in-theory (e/d (fn-bs-splice) (fn-bs-take))
          :expand ((fn-bs-take 0 old))))))
(defthm fn-lgp-write-and-fence-copy
 (implies (and (fn-lgp-headedp (fn-bs-inodes bs) ino) (true-listp x))
  (let ((bs2 (mv-nth 1 (fn-bs-fsync-file (mv-nth 1 (fn-bs-write bs ino 0 x :ok)) ino :ok))))
   (and (fn-lgp-headedp (fn-bs-inodes bs2) ino)
        (equal (fn-bs-unit bs2) (fn-bs-unit bs))
        (equal (fn-bs-ops-for-ino (fn-bs-pending bs2) ino) nil)
        (equal (fn-bs-take (len x) (fn-bs-durable-content bs2 ino)) x)
        (<= (len x) (len (fn-bs-durable-content bs2 ino))))))
 :hints (("Goal" :do-not-induct t :cases ((consp x))
          :in-theory (e/d (fn-bs-write fn-bs-fsync-file fn-bs-fence-file fn-bs-durable-content
                           fn-bs-ops-for-ino-of-append fn-bs-apply-ops-inodes-are-apply-writes)
                          (fn-lgp-headedp fn-bs-splice fn-bs-apply-writes fn-bs-put-assoc
                           fn-bs-ops-for-ino fn-bs-ops-not-for-ino))
          :expand ((:free (c) (fn-bs-take 0 c))))))
(defthm fn-lgp-headedp-implies-consp
 (implies (fn-lgp-headedp inodes ino) (consp inodes))
 :rule-classes :forward-chaining
 :hints (("Goal" :in-theory (enable fn-lgp-headedp))))
