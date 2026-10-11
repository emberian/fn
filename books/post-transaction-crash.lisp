(in-package "ACL2")
(include-book "store-log-kernel")
(include-book "store-log-crash")

; The pieces of entry E at frontier F of lengths LS, in order.
(defun fn-ptx-sum (ls) (if (consp ls) (+ (nfix (car ls)) (fn-ptx-sum (cdr ls))) 0))
(defun fn-ptx-split-ops (ino f e ls)
  (if (consp ls)
      (cons (list :write ino (nfix f) (take (nfix (car ls)) e))
            (fn-ptx-split-ops ino (+ (nfix f) (nfix (car ls))) (nthcdr (nfix (car ls)) e) (cdr ls)))
    nil))
(defun fn-ptx-with-pending (bs pending)
  (fn-bs-make (fn-bs-unit bs) (fn-bs-inodes bs) (fn-bs-dirs bs) pending (fn-bs-next-ino bs)))

(defun fn-ptx-ops-octets (ops) (if (consp ops) (append (nth 3 (car ops)) (fn-ptx-ops-octets (cdr ops))) nil))
(defun fn-ptx-ops-contiguous-p (ops off)
  (if (consp ops)
      (and (equal (nth 2 (car ops)) off)
           (fn-ptx-ops-contiguous-p (cdr ops) (+ off (len (nth 3 (car ops))))))
    t))

;; theorem 0
(defthm fn-ptx-take-split
  (implies (and (natp a) (natp b) (<= (+ a b) (len e)))
           (equal (append (take a e) (take b (nthcdr a e))) (take (+ a b) e)))
  :hints (("Goal" :induct (take a e))))
(defthm fn-ptx-ops-octets-of-split
  (implies (<= (fn-ptx-sum ls) (len e))
           (equal (fn-ptx-ops-octets (fn-ptx-split-ops ino f e ls))
                  (take (fn-ptx-sum ls) e)))
  :hints (("Goal" :induct (fn-ptx-split-ops ino f e ls))))
(defthm fn-ptx-len-take
  (implies (and (natp n) (<= n (len e))) (equal (len (take n e)) n)))
(defthm fn-ptx-contiguous-of-split
  (implies (<= (fn-ptx-sum ls) (len e))
           (fn-ptx-ops-contiguous-p (fn-ptx-split-ops ino f e ls) (nfix f)))
  :hints (("Goal" :induct (fn-ptx-split-ops ino f e ls))))
(defthm fn-ptx-split-ops-cover
  (implies (<= (fn-ptx-sum ls) (len e))
           (and (equal (fn-ptx-ops-octets (fn-ptx-split-ops ino f e ls)) (take (fn-ptx-sum ls) e))
                (fn-ptx-ops-contiguous-p (fn-ptx-split-ops ino f e ls) (nfix f)))))

;; ops-bounds lemmas
(defthm fn-ptx-split-between
  (implies (<= (fn-ptx-sum ls) (len e))
           (fn-lg-writes-between (fn-ptx-split-ops ino f e ls) (nfix f) (+ (nfix f) (len e))))
  :hints (("Goal" :induct (fn-ptx-split-ops ino f e ls))))
(defthm fn-ptx-split-writes-to
  (fn-lg-writes-to (fn-ptx-split-ops ino f e ls) ino)
  :hints (("Goal" :induct (fn-ptx-split-ops ino f e ls))))
(defthm fn-ptx-take-between
  (implies (and (fn-lg-writes-between ops low b) (natp j) (<= j (len ops)))
           (fn-lg-writes-between (take j ops) low b))
  :hints (("Goal" :induct (take j ops))))
(defthm fn-ptx-take-writes-to
  (implies (and (fn-lg-writes-to ops ino) (natp j) (<= j (len ops)))
           (fn-lg-writes-to (take j ops) ino))
  :hints (("Goal" :induct (take j ops))))
(defthm fn-ptx-len-split-ops
  (equal (len (fn-ptx-split-ops ino f e ls)) (len ls)))
(encapsulate ()
  (local (include-book "arithmetic-5/top" :dir :system))
  (local (defthm fn-ptx-floor-mult-le
    (implies (and (natp y) (posp unit)) (<= (* unit (floor y unit)) y))
    :rule-classes :linear))
  (defthm fn-ptx-start-bound
    (implies (and (natp off) (posp len) (posp unit) (natp i)
                  (< i (fn-bs-unit-count off len unit)))
             (<= (* (+ (floor off unit) i) unit) (+ off len)))
    :hints (("Goal" :in-theory (e/d (fn-bs-unit-count) (fn-ptx-floor-mult-le))
             :use ((:instance fn-ptx-floor-mult-le (y (+ off len -1))))
             :nonlinearp t))))
(encapsulate ()
  (local (include-book "arithmetic-5/top" :dir :system))
  (local (in-theory (disable floor fn-bs-unit-count)))
  (local (defthm fn-ptx-start-bound2
    (implies (and (natp off) (natp len) (posp unit) (natp i)
                  (< i (fn-bs-unit-count off len unit)))
             (<= (+ (* i unit) (* unit (floor off unit))) (+ off len)))
    :hints (("Goal" :cases ((posp len))
             :in-theory (enable fn-bs-unit-count)
             :use fn-ptx-start-bound))))
  (defthm fn-ptx-tear-between-gen
    (implies (and (natp (nth 2 op)) (true-listp (nth 3 op)) (posp unit) (natp i))
             (and (fn-lg-writes-between (fn-bs-tear-write op sels i unit)
                                        (nth 2 op) (+ (nth 2 op) (len (nth 3 op))))
                  (fn-lg-writes-to (fn-bs-tear-write op sels i unit) (nth 1 op))))
    :hints (("Goal" :induct (fn-bs-tear-write op sels i unit)
             :in-theory (e/d ((:definition fn-bs-tear-write)) (fn-ptx-start-bound)))
            (and stable-under-simplificationp
                 '(:use ((:instance fn-ptx-start-bound2 (off (nth 2 op)) (len (len (nth 3 op))))))))))
(defthm fn-ptx-between-of-append
  (equal (fn-lg-writes-between (append a b) low bd)
         (and (fn-lg-writes-between a low bd) (fn-lg-writes-between b low bd))))
(defthm fn-ptx-writes-to-of-append
  (equal (fn-lg-writes-to (append a b) ino)
         (and (fn-lg-writes-to a ino) (fn-lg-writes-to b ino))))
(defthm fn-ptx-select-between
  (implies (and (fn-lg-writes-between ops low b) (fn-lg-writes-to ops ino) (posp unit))
           (and (fn-lg-writes-between (fn-bs-crash-select ops choices unit) low b)
                (fn-lg-writes-to (fn-bs-crash-select ops choices unit) ino)))
  :hints (("Goal" :induct (fn-bs-crash-select ops choices unit)
           :in-theory (enable fn-bs-crash-select))
          (and stable-under-simplificationp
               '(:use ((:instance fn-ptx-tear-between-gen (op (car ops)) (i 0) (sels (car choices)))
                       (:instance fn-lgc-writes-between-weaken
                                  (ops (fn-bs-tear-write (car ops) (car choices) 0 unit))
                                  (low (nth 2 (car ops)))
                                  (bound (+ (nth 2 (car ops)) (len (nth 3 (car ops)))))
                                  (low2 low) (bound2 b)))))))

;; octet-ness
(defthm fn-ptx-octets-of-append
  (implies (true-listp a)
           (equal (fn-cbor-octet-listp (append a b))
                  (and (fn-cbor-octet-listp a) (fn-cbor-octet-listp b))))
  :hints (("Goal" :in-theory (enable fn-cbor-octet-listp))))
(defthm fn-ptx-octets-of-zeros
  (fn-cbor-octet-listp (fn-bs-zeros n))
  :hints (("Goal" :in-theory (enable fn-cbor-octet-listp fn-cbor-octetp))))
(defthm fn-ptx-entry-octets
  (implies (and (fn-frame-digestp prev) (fn-lg-chunkp chunk max))
           (fn-cbor-octet-listp (fn-lg-entry prev chunk unit)))
  :hints (("Goal" :in-theory (disable fn-lg-frame fn-lg-chunkp fn-lg-pad-len)
           :use ((:instance fn-lg-frame-octets)
                 (:instance fn-lg-frame-true-listp)
                 (:instance fn-lg-chunk-body-octets)))))
(defthm fn-ptx-log-octets
  (implies (and (fn-frame-digestp prev) (fn-lg-recordsp records max))
           (fn-cbor-octet-listp (fn-lg-log records prev unit)))
  :hints (("Goal" :induct (fn-lg-log records prev unit)
           :in-theory (e/d (fn-lg-log-unfolds)
                           (fn-lg-entry fn-lg-frame fn-lg-trailer fn-lg-recordsp
                            fn-lg-chunkp (:definition fn-lg-log)
                            fn-lg-trailer-of-frame-digestp)))
          ("Subgoal *1/2" :expand ((fn-lg-log records prev unit) (fn-lg-log nil prev unit)))
          ("Subgoal *1/1"
           :use ((:instance fn-lg-chunkp-of-first-chunk)
                 (:instance fn-lg-recordsp-of-nthcdr (k (fn-lg-chunk-len records)))
                 (:instance fn-lg-trailer-of-frame-digestp
                            (chunk (fn-bs-take (fn-lg-chunk-len records) records)))
                 (:instance fn-lg-entry-true-listp
                            (chunk (fn-bs-take (fn-lg-chunk-len records) records)))
                 (:instance fn-ptx-entry-octets
                            (chunk (fn-bs-take (fn-lg-chunk-len records) records)))))))
(defun fn-ptx-octs-opsp (ops)
  (if (consp ops)
      (and (fn-cbor-octet-listp (nth 3 (car ops))) (fn-ptx-octs-opsp (cdr ops)))
    t))
(defthm fn-ptx-octets-of-take
  (implies (and (fn-cbor-octet-listp e) (natp n) (<= n (len e)))
           (fn-cbor-octet-listp (take n e)))
  :hints (("Goal" :in-theory (enable fn-cbor-octet-listp))))
(defthm fn-ptx-octets-of-nthcdr
  (implies (fn-cbor-octet-listp e) (fn-cbor-octet-listp (nthcdr n e)))
  :hints (("Goal" :in-theory (enable fn-cbor-octet-listp))))
(defthm fn-ptx-split-octs
  (implies (and (fn-cbor-octet-listp e) (<= (fn-ptx-sum ls) (len e)))
           (fn-ptx-octs-opsp (fn-ptx-split-ops ino f e ls)))
  :hints (("Goal" :induct (fn-ptx-split-ops ino f e ls))))
(defthm fn-ptx-take-octs
  (implies (and (fn-ptx-octs-opsp ops) (natp j) (<= j (len ops)))
           (fn-ptx-octs-opsp (take j ops)))
  :hints (("Goal" :induct (take j ops))))
(defthm fn-ptx-tear-octs
  (implies (and (fn-cbor-octet-listp (nth 3 op)) (fn-bs-selector-listp sels))
           (fn-ptx-octs-opsp (fn-bs-tear-write op sels i unit)))
  :hints (("Goal" :induct (fn-bs-tear-write op sels i unit)
           :in-theory (e/d ((:definition fn-bs-tear-write) fn-bs-selectorp)
                           (fn-bs-unit-count)))))
(defthm fn-ptx-octs-of-append
  (equal (fn-ptx-octs-opsp (append a b)) (and (fn-ptx-octs-opsp a) (fn-ptx-octs-opsp b))))
(defthm fn-ptx-select-octs
  (implies (and (fn-ptx-octs-opsp ops) (fn-lg-writes-to ops ino) (fn-bs-crash-choicesp choices ops unit))
           (fn-ptx-octs-opsp (fn-bs-crash-select ops choices unit)))
  :hints (("Goal" :induct (fn-bs-crash-select ops choices unit)
           :in-theory (e/d (fn-bs-crash-select fn-bs-crash-choicesp fn-bs-crash-choicep)
                           (fn-bs-tear-write fn-bs-unit-count)))))

;; shift to the zero domain
(defun fn-ptx-unshift (ops f)
  (if (consp ops)
      (cons (list :write (nth 1 (car ops)) (- (nfix (nth 2 (car ops))) (nfix f)) (nth 3 (car ops)))
            (fn-ptx-unshift (cdr ops) f))
    nil))
(defthm fn-ptx-unshift-between
  (implies (and (fn-lg-writes-between ops f b) (natp f))
           (fn-lg-writes-between (fn-ptx-unshift ops f) 0 (- b f))))
(defthm fn-ptx-unshift-octs
  (equal (fn-ptx-octs-opsp (fn-ptx-unshift ops f)) (fn-ptx-octs-opsp ops)))
(defun fn-ptx-ind2 (z ops f)
  (if (consp ops)
      (fn-ptx-ind2 (fn-bs-splice z (- (nfix (nth 2 (car ops))) (nfix f)) (nth 3 (car ops))) (cdr ops) f)
    z))
(defthm fn-ptx-splice-past-prefix2
  (implies (and (true-listp d) (natp off) (<= (len d) off))
           (equal (fn-bs-splice (append d z) off o)
                  (append d (fn-bs-splice z (- off (len d)) o))))
  :hints (("Goal" :use ((:instance fn-lg-splice-past-prefix (s (- off (len d))))))))
(defthm fn-ptx-apply-to-past-prefix
  (implies (and (true-listp d) (equal (len d) f) (natp f) (fn-lg-writes-between ops f b))
           (equal (fn-lg-apply-to (append d z) ops)
                  (append d (fn-lg-apply-to z (fn-ptx-unshift ops f)))))
  :hints (("Goal" :induct (fn-ptx-ind2 z ops f)
           :in-theory (disable fn-bs-splice)
           :expand ((fn-lg-apply-to (append d z) ops)))))

;; the crash of a write-only pending list
(defthm fn-ptx-assoc-of-put-assoc
  (implies ino (equal (assoc-equal ino (fn-bs-put-assoc ino v inodes)) (cons ino v))))
(defthm fn-ptx-put-assoc-twice
  (equal (fn-bs-put-assoc ino v2 (fn-bs-put-assoc ino v1 x)) (fn-bs-put-assoc ino v2 x)))
(defthm fn-ptx-put-assoc-same
  (implies (and ino (assoc-equal ino inodes))
           (equal (fn-bs-put-assoc ino (cdr (assoc-equal ino inodes)) inodes) inodes)))
(defthm fn-ptx-apply-writes-put
  (implies (and (fn-lg-writes-to ops ino) ino (assoc-equal ino inodes))
           (equal (fn-bs-apply-writes inodes ops)
                  (fn-bs-put-assoc ino (fn-lg-apply-to (cdr (assoc-equal ino inodes)) ops) inodes)))
  :hints (("Goal" :induct (fn-bs-apply-writes inodes ops)
           :in-theory (disable fn-bs-splice))))
(defthm fn-ptx-entries-of-writes
  (implies (fn-lg-writes-to ops ino) (equal (fn-bs-apply-entries dirs ops) dirs)))
(defthm fn-ptx-apply-ops-car
  (equal (car (fn-bs-apply-ops inodes dirs ops)) (fn-bs-apply-writes inodes ops))
  :hints (("Goal" :use fn-bs-apply-ops-inodes-are-apply-writes
           :in-theory (disable fn-bs-apply-ops-inodes-are-apply-writes))))
(defthm fn-ptx-crash-of-writes
  (implies (and (fn-lg-writes-to (fn-bs-crash-select (fn-bs-pending s) ch (fn-bs-unit s)) ino)
                ino (assoc-equal ino (fn-bs-inodes s)))
           (equal (fn-bs-crash s ch)
                  (fn-bs-make (fn-bs-unit s)
                              (fn-bs-put-assoc ino
                                               (fn-lg-apply-to (cdr (assoc-equal ino (fn-bs-inodes s)))
                                                               (fn-bs-crash-select (fn-bs-pending s) ch (fn-bs-unit s)))
                                               (fn-bs-inodes s))
                              (fn-bs-dirs s) nil (fn-bs-next-ino s))))
  :hints (("Goal" :in-theory (e/d (fn-bs-crash) (fn-bs-crash-select))
           :use ((:instance fn-bs-apply-ops-dirs-are-apply-entries
                            (inodes (fn-bs-inodes s)) (dirs (fn-bs-dirs s))
                            (ops (fn-bs-crash-select (fn-bs-pending s) ch (fn-bs-unit s))))))))

;; the all-garble one-write selection
(defun fn-ptx-gsels (x unit)
  (declare (xargs :measure (len x)))
  (if (or (atom x) (zp unit))
      nil
    (cons (cons :garble x) (fn-ptx-gsels (nthcdr unit x) unit))))
(defthm fn-ptx-gsels-selectors
  (implies (fn-cbor-octet-listp x) (fn-bs-selector-listp (fn-ptx-gsels x unit)))
  :hints (("Goal" :induct (fn-ptx-gsels x unit)
           :in-theory (enable fn-bs-selectorp))))
(defthm fn-ptx-splice-splice
  (implies (and (true-listp a) (true-listp b) (natp s))
           (equal (fn-bs-splice (fn-bs-splice c s a) (+ s (len a)) b)
                  (fn-bs-splice c s (append a b))))
  :hints (("Goal" :in-theory (enable fn-bs-splice))))
(defthm fn-ptx-pieces-step
  (implies (and (consp x) (consp w) (posp unit))
           (equal (fn-lg-pieces ino s w (fn-ptx-gsels x unit) unit)
                  (cons (list :write ino (nfix s) (fn-bs-take (min unit (len w)) x))
                        (fn-lg-pieces ino (+ (nfix s) unit) (nthcdr unit w)
                                      (fn-ptx-gsels (nthcdr unit x) unit) unit))))
  :hints (("Goal" :expand ((fn-ptx-gsels x unit)
                           (fn-lg-pieces ino s w (cons (cons :garble x) (fn-ptx-gsels (nthcdr unit x) unit)) unit)))))
(defthm fn-ptx-take-len-id
  (implies (true-listp x) (equal (fn-bs-take (len x) x) x)))
(defthm fn-ptx-take-nthcdr-append
  (implies (and (true-listp x) (natp n) (<= n (len x)))
           (equal (append (fn-bs-take n x) (nthcdr n x)) x)))
(defthm fn-ptx-len-pos
  (implies (consp x) (< 0 (len x)))
  :rule-classes :linear)
(defthm fn-ptx-consp-of-len
  (implies (and (consp x) (equal (len w) (len x))) (consp w))
  :hints (("Goal" :use (fn-ptx-len-pos) :in-theory (disable fn-ptx-len-pos))))
(defthm fn-ptx-pieces-step2
  (implies (and (consp x) (equal (len w) (len x)) (posp unit))
           (equal (fn-lg-pieces ino s w (fn-ptx-gsels x unit) unit)
                  (cons (list :write ino (nfix s) (fn-bs-take (min unit (len w)) x))
                        (fn-lg-pieces ino (+ (nfix s) unit) (nthcdr unit w)
                                      (fn-ptx-gsels (nthcdr unit x) unit) unit))))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use ((:instance fn-ptx-pieces-step) (:instance fn-ptx-consp-of-len)))))
(defun fn-ptx-ind4 (c x w s unit)
  (declare (xargs :measure (len x)))
  (if (or (atom x) (zp unit) (<= (len x) unit))
      (list c w s)
    (fn-ptx-ind4 (fn-bs-splice c s (fn-bs-take unit x))
                 (nthcdr unit x) (nthcdr unit w) (+ (nfix s) unit) unit)))
(defthm fn-ptx-nthcdr-atom
  (implies (and (true-listp x) (<= (len x) (nfix n))) (equal (nthcdr n x) nil))
  :hints (("Goal" :use ((:instance fn-lgc-consp-nthcdr)) :in-theory (disable fn-lgc-consp-nthcdr))))
(defthm fn-ptx-gsels-short
  (implies (and (true-listp x) (consp x) (<= (len x) unit) (posp unit))
           (equal (fn-ptx-gsels x unit) (list (cons :garble x))))
  :hints (("Goal" :expand ((fn-ptx-gsels x unit)))))
(defthm fn-ptx-pieces-single
  (implies (and (consp x) (<= (len x) unit) (posp unit) (equal (len w) (len x)) (true-listp x))
           (equal (fn-lg-pieces ino s w (list (cons :garble x)) unit)
                  (list (list :write ino (nfix s) x))))
  :hints (("Goal" :expand ((fn-lg-pieces ino s w (list (cons :garble x)) unit)))))
(defthm fn-ptx-take-bs-len
  (implies (and (true-listp x) (<= n (len x)) (natp n)) (equal (len (fn-bs-take n x)) n)))
(defthm fn-ptx-apply-step
  (implies (and (true-listp x) (< unit (len x)) (posp unit) (natp s) (equal (len w) (len x)))
           (equal (fn-lg-apply-to c (fn-lg-pieces ino s w (fn-ptx-gsels x unit) unit))
                  (fn-lg-apply-to (fn-bs-splice c s (fn-bs-take unit x))
                                  (fn-lg-pieces ino (+ s unit) (nthcdr unit w)
                                                (fn-ptx-gsels (nthcdr unit x) unit) unit))))
  :hints (("Goal" :in-theory (disable fn-lg-pieces fn-ptx-gsels fn-bs-splice fn-ptx-pieces-step fn-ptx-pieces-step2)
           :use ((:instance fn-ptx-pieces-step2))
           :expand ((fn-lg-apply-to c (cons (list :write ino s (fn-bs-take unit x))
                                            (fn-lg-pieces ino (+ s unit) (nthcdr unit w)
                                                          (fn-ptx-gsels (nthcdr unit x) unit) unit)))))))
(defthm fn-ptx-apply-to-single
  (equal (fn-lg-apply-to c (list op)) (fn-bs-splice c (nth 2 op) (nth 3 op)))
  :hints (("Goal" :expand ((fn-lg-apply-to c (list op))))))
(defthm fn-ptx-pieces-of-gsels
  (implies (and (true-listp x) (natp s) (posp unit) (equal (len x) (len w)))
           (equal (fn-lg-apply-to c (fn-lg-pieces ino s w (fn-ptx-gsels x unit) unit))
                  (if (consp x) (fn-bs-splice c s x) c)))
  :hints (("Goal" :induct (fn-ptx-ind4 c x w s unit)
           :in-theory (e/d (fn-ptx-take-nthcdr-append fn-ptx-take-bs-len)
                           (fn-bs-splice fn-lg-pieces fn-ptx-gsels fn-lg-pieces-shift
                            fn-ptx-pieces-step fn-ptx-pieces-step2 fn-lg-apply-to fn-lg-shift-ops)))
          ("Subgoal *1/2" :use ((:instance fn-ptx-splice-splice (a (fn-bs-take unit x)) (b (nthcdr unit x)))
                               (:instance fn-lgc-consp-nthcdr (n unit))))))

;; garble selection reproduces any content
(encapsulate ()
  (local (include-book "arithmetic-5/top" :dir :system))
  (defthm fn-ptx-gsels-len-bound
    (implies (and (true-listp x) (posp unit) (consp x))
             (< (* (+ -1 (len (fn-ptx-gsels x unit))) unit) (len x)))
    :hints (("Goal" :induct (fn-ptx-gsels x unit)
             :in-theory (disable fn-lgc-consp-nthcdr))
            ("Subgoal *1/2" :use ((:instance fn-lgc-consp-nthcdr (n unit)))))))
(defthm fn-ptx-gsels-len-le-count
  (implies (and (true-listp x) (posp unit) (natp k))
           (<= (len (fn-ptx-gsels x unit))
               (fn-bs-unit-count (* k unit) (len x) unit)))
  :hints (("Goal" :cases ((consp x))
           :use ((:instance fn-lgc-unit-count-aligned (len (len x)) (i (+ -1 (len (fn-ptx-gsels x unit)))))
                 (:instance fn-ptx-gsels-len-bound))
           :in-theory (disable fn-lgc-unit-count-aligned fn-ptx-gsels-len-bound))
          ("Subgoal 1" :expand ((fn-ptx-gsels x unit)))))
(defthm fn-ptx-apply-to-octets
  (implies (and (fn-cbor-octet-listp c) (fn-ptx-octs-opsp ops))
           (fn-cbor-octet-listp (fn-lg-apply-to c ops)))
  :hints (("Goal" :induct (fn-lg-apply-to c ops)
           :in-theory (e/d (fn-bs-splice-of-octets-are-octets) (fn-bs-splice)))))
(defthm fn-ptx-zerosp-octets
  (implies (fn-lg-zerosp z) (fn-cbor-octet-listp z))
  :hints (("Goal" :in-theory (enable fn-lg-zerosp fn-cbor-octet-listp fn-cbor-octetp))))
(defthm fn-ptx-zerosp-nthcdr-true
  (implies (fn-lg-zerosp z) (true-listp z)))
(defthm fn-ptx-splice-zero
  (implies (true-listp x) (equal (fn-bs-splice z 0 x) (append x (nthcdr (len x) z))))
  :hints (("Goal" :in-theory (enable fn-bs-splice))))
(defthm fn-ptx-take-facts
  (implies (and (natp n) (<= n (len r0)))
           (and (true-listp (take n r0)) (equal (len (take n r0)) n)))
  :hints (("Goal" :in-theory (enable take))))
(defthm fn-ptx-take-consp
  (implies (and (natp n) (< 0 n) (<= n (len r0))) (consp (take n r0)))
  :hints (("Goal" :in-theory (enable take))))
(defthm fn-ptx-take-append-nthcdr
  (implies (and (true-listp r0) (natp n) (<= n (len r0)))
           (equal (append (take n r0) (nthcdr n r0)) r0))
  :hints (("Goal" :in-theory (enable take))))
(defthm fn-ptx-core2
  (implies (and (true-listp r0) (<= (len e) (len r0)) (consp e) (posp unit) (true-listp z)
                (equal (nthcdr (len e) r0) (nthcdr (len e) z)))
           (equal (fn-lg-apply-to z (fn-lg-pieces ino 0 e (fn-ptx-gsels (take (len e) r0) unit) unit))
                  r0))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories (theory 'minimal-theory) '((:definition natp) (:definition posp) (:type-prescription len) (:definition true-listp)))
           :use ((:instance fn-ptx-pieces-of-gsels (c z) (x (take (len e) r0)) (w e) (s 0))
                 (:instance fn-ptx-take-append-nthcdr (n (len e)))
                 (:instance fn-ptx-splice-zero (x (take (len e) r0)))
                 (:instance fn-ptx-take-facts (n (len e)))
                 (:instance fn-ptx-take-consp (n (len e)))
                 (:instance fn-ptx-len-pos (x e))))))
(defthm fn-ptx-core
  (implies (and (true-listp z) (fn-lg-writes-between ops 0 (len e)) (<= (len e) (len z)) (consp e)
                (posp unit))
           (equal (fn-lg-apply-to z (fn-lg-pieces ino 0 e (fn-ptx-gsels (take (len e) (fn-lg-apply-to z ops)) unit) unit))
                  (fn-lg-apply-to z ops)))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories (theory 'minimal-theory) '((:definition natp) (:definition posp) (:type-prescription len)))
           :use ((:instance fn-ptx-core2 (r0 (fn-lg-apply-to z ops)))
                 (:instance fn-lg-apply-to-len-within (c z) (low 0) (bound (len e)))
                 (:instance fn-lg-nthcdr-of-apply-to-below (c z) (low 0) (b (len e)))
                 (:instance fn-lg-apply-to-true-listp (c z))))))

;; crash values
(defthm fn-ptx-pending-of-with-pending
  (and (equal (fn-bs-pending (fn-ptx-with-pending bs p)) p)
       (equal (fn-bs-unit (fn-ptx-with-pending bs p)) (fn-bs-unit bs))
       (equal (fn-bs-inodes (fn-ptx-with-pending bs p)) (fn-bs-inodes bs))
       (equal (fn-bs-dirs (fn-ptx-with-pending bs p)) (fn-bs-dirs bs))
       (equal (fn-bs-next-ino (fn-ptx-with-pending bs p)) (fn-bs-next-ino bs))))
(in-theory (disable fn-ptx-with-pending))
(defthm fn-ptx-split-crash-value
  (implies (and (posp (fn-bs-unit bs)) (true-listp d) (equal (len d) f) (natp f)
                ino (assoc-equal ino (fn-bs-inodes bs))
                (equal (fn-bs-durable-content bs ino) (append d z))
                (fn-lg-writes-between ops f b) (fn-lg-writes-to ops ino))
           (equal (fn-bs-crash (fn-ptx-with-pending bs ops) ch)
                  (fn-bs-make (fn-bs-unit bs)
                              (fn-bs-put-assoc ino
                                               (append d (fn-lg-apply-to z (fn-ptx-unshift (fn-bs-crash-select ops ch (fn-bs-unit bs)) f)))
                                               (fn-bs-inodes bs))
                              (fn-bs-dirs bs) nil (fn-bs-next-ino bs))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-bs-durable-content) (fn-bs-crash-select fn-bs-crash fn-lg-apply-to fn-ptx-unshift fn-bs-put-assoc
                               fn-bs-splice fn-bs-make fn-ptx-crash-of-writes fn-ptx-apply-to-past-prefix
                               fn-ptx-select-between))
           :use ((:instance fn-ptx-crash-of-writes (s (fn-ptx-with-pending bs ops)))
                 (:instance fn-ptx-select-between (unit (fn-bs-unit bs)) (low f) (choices ch))
                 (:instance fn-ptx-apply-to-past-prefix
                            (ops (fn-bs-crash-select ops ch (fn-bs-unit bs)))
                            (b b))))))
(defthm fn-ptx-zero-times (equal (* 0 x) 0))
(defthm fn-ptx-zero-plus (implies (acl2-numberp x) (equal (+ 0 x) x)))
(defthm fn-ptx-select-of-single
  (implies (and (natp k) (posp unit) (true-listp w))
           (equal (fn-bs-crash-select (list (list :write ino (* k unit) w)) (list sels) unit)
                  (fn-lg-pieces ino (* k unit) w sels unit)))
  :hints (("Goal" :in-theory (disable fn-lg-tear-write-is-pieces fn-bs-tear-write fn-lg-pieces fn-lg-pieces-shift)
           :expand ((fn-bs-crash-select (list (list :write ino (* k unit) w)) (list sels) unit))
           :use ((:instance fn-lg-tear-write-is-pieces (i 0))))))
(defthm fn-ptx-one-write-crash-value
  (implies (and (posp (fn-bs-unit bs)) (true-listp d) (equal (len d) (* k (fn-bs-unit bs))) (natp k)
                ino (assoc-equal ino (fn-bs-inodes bs))
                (equal (fn-bs-durable-content bs ino) (append d z))
                (true-listp e)
                (equal (fn-bs-pending bs) (list (list :write ino (len d) e))))
           (equal (fn-bs-crash bs (list sels))
                  (fn-bs-make (fn-bs-unit bs)
                              (fn-bs-put-assoc ino
                                               (append d (fn-lg-apply-to z (fn-lg-pieces ino 0 e sels (fn-bs-unit bs))))
                                               (fn-bs-inodes bs))
                              (fn-bs-dirs bs) nil (fn-bs-next-ino bs))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-bs-durable-content)
                           (fn-bs-crash fn-lg-apply-to fn-lg-pieces fn-bs-put-assoc fn-bs-tear-write
                            fn-bs-splice fn-bs-make fn-ptx-crash-of-writes fn-lg-apply-to-past-prefix
                            fn-ptx-select-of-single fn-bs-crash-select fn-lg-pieces-shift))
           :use ((:instance fn-ptx-crash-of-writes (s bs) (ch (list sels)))
                 (:instance fn-ptx-select-of-single (w e) (unit (fn-bs-unit bs)))
                 (:instance fn-lg-apply-to-past-prefix (s 0) (unit (fn-bs-unit bs)) (w e))
                 (:instance fn-lg-pieces-write-to (start (len d)) (w e) (sels sels) (unit (fn-bs-unit bs)))))))

;; one-write choice
(defthm fn-ptx-choicesp-of-one
  (implies (and (posp unit) (natp k) (true-listp e) (true-listp x) (fn-cbor-octet-listp x)
                (equal (len x) (len e)))
           (fn-bs-crash-choicesp (list (fn-ptx-gsels x unit))
                                 (list (list :write ino (* k unit) e)) unit))
  :hints (("Goal" :in-theory (e/d (fn-bs-crash-choicesp fn-bs-crash-choicep)
                                  (fn-ptx-gsels fn-bs-unit-count fn-ptx-gsels-len-le-count))
           :use ((:instance fn-ptx-gsels-len-le-count)
                 (:instance fn-ptx-gsels-selectors)))))
(encapsulate ()
  (local (include-book "arithmetic/top" :dir :system))
  (defthm fn-ptx-unshift-between2
    (implies (and (fn-lg-writes-between ops f (+ f l)) (natp f))
             (fn-lg-writes-between (fn-ptx-unshift ops f) 0 l))
    :hints (("Goal" :induct (fn-ptx-unshift ops f))))
  (defthm fn-ptx-len-apply-to-bound
    (implies (and (fn-lg-writes-between ops 0 l) (<= l (len z)) (true-listp z))
             (and (equal (len (fn-lg-apply-to z ops)) (len z))
                  (true-listp (fn-lg-apply-to z ops))))))
(defun fn-ptx-r0 (z ops ch unit f)
  (fn-lg-apply-to z (fn-ptx-unshift (fn-bs-crash-select ops ch unit) f)))
(defthm fn-ptx-r0-facts
  (implies (and (fn-lg-writes-between ops f (+ f (len e))) (fn-lg-writes-to ops ino)
                (natp f) (posp unit) (<= (len e) (len z)) (true-listp z)
                (fn-lg-zerosp z) (fn-cbor-octet-listp e) (consp e)
                (fn-ptx-octs-opsp ops) (fn-bs-crash-choicesp ch ops unit))
           (and (fn-lg-writes-between (fn-ptx-unshift (fn-bs-crash-select ops ch unit) f) 0 (len e))
                (equal (len (fn-ptx-r0 z ops ch unit f)) (len z))
                (true-listp (fn-ptx-r0 z ops ch unit f))
                (fn-cbor-octet-listp (fn-ptx-r0 z ops ch unit f))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-ptx-r0 fn-bs-crash-select fn-ptx-unshift fn-lg-apply-to
                               fn-ptx-select-between fn-ptx-unshift-between2 fn-ptx-len-apply-to-bound
                               fn-ptx-apply-to-octets fn-ptx-select-octs fn-ptx-unshift-octs)
           :expand ((fn-ptx-r0 z ops ch unit f))
           :use ((:instance fn-ptx-select-between (low f) (b (+ f (len e))) (choices ch))
                 (:instance fn-ptx-unshift-between2 (ops (fn-bs-crash-select ops ch unit)) (l (len e)))
                 (:instance fn-ptx-len-apply-to-bound (ops (fn-ptx-unshift (fn-bs-crash-select ops ch unit) f)) (l (len e)))
                 (:instance fn-ptx-select-octs (choices ch))
                 (:instance fn-ptx-unshift-octs (ops (fn-bs-crash-select ops ch unit)))
                 (:instance fn-ptx-apply-to-octets (c z) (ops (fn-ptx-unshift (fn-bs-crash-select ops ch unit) f)))
                 (:instance fn-ptx-zerosp-octets)))))

;; the image theorem
(defthm fn-ptx-r0-nthcdr
  (implies (and (fn-lg-writes-between ops f (+ f (len e))) (fn-lg-writes-to ops ino) (posp unit) (natp f) (<= (len e) (len z)))
           (equal (nthcdr (len e) (fn-ptx-r0 z ops ch unit f)) (nthcdr (len e) z)))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-ptx-r0 fn-bs-crash-select fn-ptx-unshift fn-lg-apply-to
                               fn-ptx-select-between fn-ptx-unshift-between2 fn-lg-nthcdr-of-apply-to-below)
           :expand ((fn-ptx-r0 z ops ch unit f))
           :use ((:instance fn-ptx-select-between (low f) (b (+ f (len e))) (choices ch))
                 (:instance fn-ptx-unshift-between2 (ops (fn-bs-crash-select ops ch unit)) (l (len e)))
                 (:instance fn-lg-nthcdr-of-apply-to-below (c z) (low 0) (b (len e))
                            (ops (fn-ptx-unshift (fn-bs-crash-select ops ch unit) f)))))))
(defthm fn-ptx-step-a
  (implies (and (posp (fn-bs-unit bs)) (true-listp d) (equal (len d) f) (natp f)
                ino (assoc-equal ino (fn-bs-inodes bs))
                (equal (fn-bs-durable-content bs ino) (append d z))
                (fn-lg-writes-between ops f b) (fn-lg-writes-to ops ino))
           (equal (fn-bs-crash (fn-ptx-with-pending bs ops) ch)
                  (fn-bs-make (fn-bs-unit bs)
                              (fn-bs-put-assoc ino (append d (fn-ptx-r0 z ops ch (fn-bs-unit bs) f)) (fn-bs-inodes bs))
                              (fn-bs-dirs bs) nil (fn-bs-next-ino bs))))
  :hints (("Goal" :do-not-induct t :in-theory (e/d (fn-ptx-r0) (fn-ptx-split-crash-value))
           :use ((:instance fn-ptx-split-crash-value)))))
(defthm fn-ptx-step-b
  (implies (and (posp (fn-bs-unit bs)) (true-listp d) (equal (len d) (* k (fn-bs-unit bs))) (natp k)
                ino (assoc-equal ino (fn-bs-inodes bs))
                (equal (fn-bs-durable-content bs ino) (append d z))
                (true-listp z) (consp e) (true-listp e)
                (equal (fn-bs-pending bs) (list (list :write ino (len d) e)))
                (true-listp r0) (<= (len e) (len r0))
                (equal (nthcdr (len e) r0) (nthcdr (len e) z)))
           (equal (fn-bs-crash bs (list (fn-ptx-gsels (take (len e) r0) (fn-bs-unit bs))))
                  (fn-bs-make (fn-bs-unit bs)
                              (fn-bs-put-assoc ino (append d r0) (fn-bs-inodes bs))
                              (fn-bs-dirs bs) nil (fn-bs-next-ino bs))))
  :hints (("Goal" :do-not-induct t :in-theory (theory 'minimal-theory)
           :use ((:instance fn-ptx-one-write-crash-value (sels (fn-ptx-gsels (take (len e) r0) (fn-bs-unit bs))))
                 (:instance fn-ptx-core2 (unit (fn-bs-unit bs)))))))
(defthm fn-ptx-take-octets
  (implies (and (fn-cbor-octet-listp r0) (natp n) (<= n (len r0)))
           (and (fn-cbor-octet-listp (take n r0)) (true-listp (take n r0)) (equal (len (take n r0)) n)))
  :hints (("Goal" :in-theory (enable take fn-cbor-octet-listp))))
(defthm fn-ptx-step-c
  (implies (and (posp unit) (natp k) (true-listp e) (true-listp x) (fn-cbor-octet-listp x)
                (equal (len x) (len e)) (equal (len d) (* k unit))
                (equal (fn-bs-pending bs) (list (list :write ino (len d) e))))
           (fn-bs-crash-choicesp (list (fn-ptx-gsels x unit)) (fn-bs-pending bs) unit))
  :hints (("Goal" :do-not-induct t :in-theory (disable fn-ptx-choicesp-of-one fn-ptx-gsels fn-bs-crash-choicesp)
           :use ((:instance fn-ptx-choicesp-of-one)))))
(defthm fn-ptx-natp-len (natp (len x)))
(defthm fn-ptx-split-image-m1
  (implies (and (posp (fn-bs-unit bs)) (true-listp d) (equal (len d) (* k (fn-bs-unit bs))) (natp k)
                ino (assoc-equal ino (fn-bs-inodes bs))
                (equal (fn-bs-durable-content bs ino) (append d z))
                (fn-lg-zerosp z) (true-listp e) (fn-cbor-octet-listp e) (consp e)
                (<= (len e) (len z))
                (equal (fn-bs-pending bs) (list (list :write ino (len d) e)))
                (fn-lg-writes-between ops (len d) (+ (len d) (len e))) (fn-lg-writes-to ops ino)
                (fn-ptx-octs-opsp ops)
                (fn-bs-crash-choicesp ch ops (fn-bs-unit bs)))
           (fn-bs-crash-imagep bs (fn-bs-crash (fn-ptx-with-pending bs ops) ch)))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories (theory 'minimal-theory) '((:definition natp) (:definition posp)))
           :use ((:instance fn-bs-crash-imagep-suff (s bs)
                            (choices (list (fn-ptx-gsels (take (len e) (fn-ptx-r0 z ops ch (fn-bs-unit bs) (len d))) (fn-bs-unit bs))))
                            (image (fn-bs-crash (fn-ptx-with-pending bs ops) ch)))
                 (:instance fn-ptx-step-a (f (len d)) (b (+ (len d) (len e))))
                 (:instance fn-ptx-step-b (r0 (fn-ptx-r0 z ops ch (fn-bs-unit bs) (len d))))
                 (:instance fn-ptx-step-c (unit (fn-bs-unit bs))
                            (x (take (len e) (fn-ptx-r0 z ops ch (fn-bs-unit bs) (len d)))))
                 (:instance fn-ptx-r0-facts (f (len d)) (unit (fn-bs-unit bs)))
                 (:instance fn-ptx-r0-nthcdr (f (len d)) (unit (fn-bs-unit bs)))
                 (:instance fn-ptx-take-octets (n (len e)) (r0 (fn-ptx-r0 z ops ch (fn-bs-unit bs) (len d))))
                 (:instance fn-ptx-zerosp-nthcdr-true)
                 (:instance fn-ptx-natp-len (x d)) (:instance fn-ptx-natp-len (x e))))))

(defthm fn-ptx-log-consp
  (implies (and (fn-frame-digestp prev) (fn-lg-recordsp records max) (consp records))
           (consp (fn-lg-log records prev unit)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-lg-log-unfolds fn-lg-entry)
                           (fn-lg-frame fn-lg-trailer fn-lg-recordsp fn-lg-chunkp (:definition fn-lg-log)
                            fn-lg-frame-consp fn-lg-chunkp-of-first-chunk))
           :use ((:instance fn-lg-chunkp-of-first-chunk)
                 (:instance fn-lg-frame-consp (chunk (fn-bs-take (fn-lg-chunk-len records) records)))
                 (:instance fn-lg-chunk-body-octets (chunk (fn-bs-take (fn-lg-chunk-len records) records)))))))
(defthm fn-ptx-split-ops-facts
  (implies (and (natp f) (<= (fn-ptx-sum ls) (len e)) (fn-cbor-octet-listp e) (natp j) (<= j (len ls)))
           (and (fn-lg-writes-between (take j (fn-ptx-split-ops ino f e ls)) f (+ f (len e)))
                (fn-lg-writes-to (take j (fn-ptx-split-ops ino f e ls)) ino)
                (fn-ptx-octs-opsp (take j (fn-ptx-split-ops ino f e ls)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-ptx-split-between fn-ptx-split-writes-to fn-ptx-take-between
                               fn-ptx-take-writes-to fn-ptx-take-octs fn-ptx-split-octs fn-ptx-split-ops take)
           :use ((:instance fn-ptx-split-between)
                 (:instance fn-ptx-split-writes-to)
                 (:instance fn-ptx-take-between (ops (fn-ptx-split-ops ino f e ls)) (low f) (b (+ f (len e))))
                 (:instance fn-ptx-take-writes-to (ops (fn-ptx-split-ops ino f e ls)))
                 (:instance fn-ptx-split-octs)
                 (:instance fn-ptx-take-octs (ops (fn-ptx-split-ops ino f e ls)))
                 (:instance fn-ptx-len-split-ops)))))
(defthm fn-ptx-imagep-unpack
  (implies (fn-bs-crash-imagep s image)
           (and (fn-bs-crash-choicesp (fn-bs-crash-imagep-witness s image) (fn-bs-pending s) (fn-bs-unit s))
                (equal image (fn-bs-crash s (fn-bs-crash-imagep-witness s image)))))
  :hints (("Goal" :in-theory (enable fn-bs-crash-imagep)))
  :rule-classes nil)

(defthm fn-ptx-relp-assoc
  (implies (fn-lgk-relp bs ks ino genesis max)
           (and ino (assoc-equal ino (fn-bs-inodes bs))))
  :hints (("Goal" :in-theory (enable fn-lgk-relp))) :rule-classes nil)
(defthm fn-ptx-split-crash-images-core
  (implies (and (fn-lgk-relp bs ks ino genesis max)
                (consp (fn-lgk-inflight ks))
                (equal e (fn-lg-log (fn-lgk-inflight ks) (fn-lgk-last ks) (fn-bs-unit bs)))
                (<= (fn-ptx-sum ls) (len e))
                (fn-lg-zerosp (nthcdr (fn-ptx-sum ls) e))
                (natp j) (<= j (len ls))
                (fn-bs-crash-imagep (fn-ptx-with-pending bs (take j (fn-ptx-split-ops ino (fn-lgk-frontier ks) e ls)))
                                    image))
           (fn-bs-crash-imagep bs image))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories (theory 'minimal-theory)
                                      '((:definition natp) (:definition posp)))
           :use ((:instance fn-lgk-relp-gives-the-tear-hypotheses)
                 (:instance fn-ptx-imagep-unpack
                            (s (fn-ptx-with-pending bs (take j (fn-ptx-split-ops ino (fn-lgk-frontier ks) e ls)))))
                 (:instance fn-ptx-pending-of-with-pending
                            (p (take j (fn-ptx-split-ops ino (fn-lgk-frontier ks) e ls))))
                 (:instance fn-ptx-split-image-m1
                            (d (fn-bs-take (fn-lgk-frontier ks) (fn-bs-durable-content bs ino)))
                            (z (nthcdr (fn-lgk-frontier ks) (fn-bs-durable-content bs ino)))
                            (k (floor (fn-lgk-frontier ks) (fn-bs-unit bs)))
                            (ops (take j (fn-ptx-split-ops ino (fn-lgk-frontier ks) e ls)))
                            (ch (fn-bs-crash-imagep-witness
                                 (fn-ptx-with-pending bs (take j (fn-ptx-split-ops ino (fn-lgk-frontier ks) e ls))) image)))
                 (:instance fn-ptx-split-ops-facts (f (fn-lgk-frontier ks)))
                 (:instance fn-ptx-relp-assoc)
                 (:instance fn-ptx-log-octets (prev (fn-lgk-last ks)) (records (fn-lgk-inflight ks)) (unit (fn-bs-unit bs)))
                 (:instance fn-lg-log-true-listp (prev (fn-lgk-last ks)) (records (fn-lgk-inflight ks)) (unit (fn-bs-unit bs)))
                 (:instance fn-ptx-log-consp (prev (fn-lgk-last ks)) (records (fn-lgk-inflight ks)) (unit (fn-bs-unit bs)))))))

;; P6 STRENGTHENED.  The core above keeps its eight hypotheses.  The four that the
;; statement below drops are discharged by cases: a nonzero tail of the entry past
;; the pieces (the pieces are a prefix of a split of the whole entry, with one
;; more piece that covers the tail), a J past the end (TAKE pads NIL operations,
;; which crash images ignore), a J that is no natural (TAKE of it is NIL), and a
;; related store with no record in flight (the entry is NIL, every piece writes no
;; octets).
(defun fn-ptx-all-nilp (x) (if (consp x) (and (null (car x)) (fn-ptx-all-nilp (cdr x))) t))
(defun fn-ptx-trim (ch ops)
  (if (and (consp ops) (consp ch)) (cons (car ch) (fn-ptx-trim (cdr ch) (cdr ops))) nil))
(defun fn-ptx-nils (n) (if (zp n) nil (cons nil (fn-ptx-nils (1- n)))))
(defthm fn-ptx-take-pad
  (implies (true-listp l)
           (equal (take j l)
                  (append (take (min (nfix j) (len l)) l)
                          (fn-ptx-nils (- (nfix j) (len l))))))
  :rule-classes nil
  :hints (("Goal" :induct (take j l))))
(defthm fn-ptx-all-nilp-of-nils (fn-ptx-all-nilp (fn-ptx-nils n)))
(defthm fn-ptx-apply-op-nil (equal (fn-bs-apply-op i d nil) (list i d))
  :hints (("Goal" :in-theory (enable fn-bs-apply-op))))
(defthm fn-ptx-apply-ops-of-nils
  (implies (fn-ptx-all-nilp b) (equal (fn-bs-apply-ops i d b) (list i d)))
  :hints (("Goal" :in-theory (disable fn-bs-apply-op))))
(defthm fn-ptx-apply-ops-append-nils
  (implies (fn-ptx-all-nilp b)
           (equal (fn-bs-apply-ops i d (append a b)) (fn-bs-apply-ops i d a)))
  :hints (("Goal" :in-theory (disable fn-bs-apply-op))))

(defthm fn-ptx-select-append
  (equal (fn-bs-crash-select (append ops pad) ch unit)
         (append (fn-bs-crash-select ops ch unit)
                 (fn-bs-crash-select pad (nthcdr (len ops) ch) unit)))
  :hints (("Goal" :induct (fn-bs-crash-select ops ch unit)
           :in-theory (enable fn-bs-crash-select))))
(defthm fn-ptx-select-of-nils
  (implies (fn-ptx-all-nilp pad)
           (fn-ptx-all-nilp (fn-bs-crash-select pad ch unit)))
  :hints (("Goal" :in-theory (enable fn-bs-crash-select))))
(defthm fn-ptx-all-nilp-append
  (equal (fn-ptx-all-nilp (append a b)) (and (fn-ptx-all-nilp a) (fn-ptx-all-nilp b))))
(defthm fn-ptx-select-trim
  (equal (fn-bs-crash-select ops (fn-ptx-trim ch ops) unit)
         (fn-bs-crash-select ops ch unit))
  :hints (("Goal" :induct (fn-bs-crash-select ops ch unit)
           :in-theory (enable fn-bs-crash-select))))
(defthm fn-ptx-trim-choicesp
  (implies (fn-bs-crash-choicesp ch (append ops pad) unit)
           (fn-bs-crash-choicesp (fn-ptx-trim ch ops) ops unit))
  :hints (("Goal" :induct (fn-ptx-trim ch ops)
           :in-theory (e/d (fn-bs-crash-choicesp) (fn-bs-crash-choicep fn-bs-unit-count fn-lg-writes-to)))))
(defthm fn-ptx-crash-drop-pad
  (implies (fn-ptx-all-nilp pad)
           (equal (fn-bs-crash (fn-ptx-with-pending bs (append ops pad)) ch)
                  (fn-bs-crash (fn-ptx-with-pending bs ops) (fn-ptx-trim ch ops))))
  :hints (("Goal" :in-theory (e/d (fn-bs-crash) (fn-bs-apply-op fn-bs-apply-ops fn-bs-make)))))

(defthm fn-ptx-imagep-drop-pad
  (implies (and (fn-ptx-all-nilp pad)
                (fn-bs-crash-imagep (fn-ptx-with-pending bs (append ops pad)) image))
           (fn-bs-crash-imagep (fn-ptx-with-pending bs ops) image))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-ptx-crash-drop-pad fn-ptx-trim-choicesp fn-bs-crash-imagep-suff)
           :use ((:instance fn-ptx-imagep-unpack (s (fn-ptx-with-pending bs (append ops pad))))
                 (:instance fn-ptx-crash-drop-pad
                            (ch (fn-bs-crash-imagep-witness (fn-ptx-with-pending bs (append ops pad)) image)))
                 (:instance fn-ptx-trim-choicesp
                            (ch (fn-bs-crash-imagep-witness (fn-ptx-with-pending bs (append ops pad)) image))
                            (unit (fn-bs-unit bs)))
                 (:instance fn-bs-crash-imagep-suff (s (fn-ptx-with-pending bs ops))
                            (choices (fn-ptx-trim (fn-bs-crash-imagep-witness (fn-ptx-with-pending bs (append ops pad)) image) ops)))))))
(defun fn-ptx-take-ind (j f e ls)
  (if (and (consp ls) (posp j))
      (fn-ptx-take-ind (1- j) (+ (nfix f) (nfix (car ls))) (nthcdr (nfix (car ls)) e) (cdr ls))
    (list j f e ls)))
(defthm fn-ptx-take-split-append
  (implies (and (natp j) (<= j (len ls)))
           (equal (take j (fn-ptx-split-ops ino f e (append ls tl)))
                  (take j (fn-ptx-split-ops ino f e ls))))
  :hints (("Goal" :induct (fn-ptx-take-ind j f e ls))))
(defthm fn-ptx-sum-append
  (equal (fn-ptx-sum (append ls tl)) (+ (fn-ptx-sum ls) (fn-ptx-sum tl))))

(defthm fn-ptx-sum-natp (natp (fn-ptx-sum ls)) :rule-classes :type-prescription)
(defthm fn-ptx-tail-ls-facts
  (implies (and (true-listp e) (<= (fn-ptx-sum ls) (len e)) (natp j) (<= j (len ls)))
           (let ((ls2 (append ls (list (- (len e) (fn-ptx-sum ls))))))
             (and (<= (fn-ptx-sum ls2) (len e))
                  (fn-lg-zerosp (nthcdr (fn-ptx-sum ls2) e))
                  (natp j) (<= j (len ls2)))))
  :hints (("Goal" :in-theory (enable fn-lg-zerosp))))
(defthm fn-ptx-split-crash-images-natj
  (implies (and (fn-lgk-relp bs ks ino genesis max)
                (consp (fn-lgk-inflight ks))
                (equal e (fn-lg-log (fn-lgk-inflight ks) (fn-lgk-last ks) (fn-bs-unit bs)))
                (<= (fn-ptx-sum ls) (len e))
                (natp j) (<= j (len ls))
                (fn-bs-crash-imagep (fn-ptx-with-pending bs (take j (fn-ptx-split-ops ino (fn-lgk-frontier ks) e ls)))
                                    image))
           (fn-bs-crash-imagep bs image))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'minimal-theory)
           :use ((:instance fn-ptx-split-crash-images-core
                            (ls (append ls (list (- (len e) (fn-ptx-sum ls))))))
                 (:instance fn-ptx-take-split-append (f (fn-lgk-frontier ks)) (tl (list (- (len e) (fn-ptx-sum ls)))))
                 (:instance fn-ptx-tail-ls-facts)
                 (:instance fn-lgk-relp-gives-the-tear-hypotheses)
                 (:instance fn-lg-log-true-listp (prev (fn-lgk-last ks)) (records (fn-lgk-inflight ks)) (unit (fn-bs-unit bs)))))))

(defthm fn-ptx-true-listp-split-ops (true-listp (fn-ptx-split-ops ino f e ls)))
(defthm fn-ptx-take-split-any
  (equal (take j (fn-ptx-split-ops ino f e ls))
         (append (take (min (nfix j) (len ls)) (fn-ptx-split-ops ino f e ls))
                 (fn-ptx-nils (- (nfix j) (len ls)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (disable take fn-ptx-split-ops)
           :use ((:instance fn-ptx-take-pad (l (fn-ptx-split-ops ino f e ls)))
                 (:instance fn-ptx-len-split-ops)))))
(defthm fn-ptx-natj-min
  (and (natp (min (nfix j) (len ls))) (<= (min (nfix j) (len ls)) (len ls))))
(defthm fn-ptx-split-crash-images-consp
  (implies (and (fn-lgk-relp bs ks ino genesis max)
                (consp (fn-lgk-inflight ks))
                (equal e (fn-lg-log (fn-lgk-inflight ks) (fn-lgk-last ks) (fn-bs-unit bs)))
                (<= (fn-ptx-sum ls) (len e))
                (fn-bs-crash-imagep (fn-ptx-with-pending bs (take j (fn-ptx-split-ops ino (fn-lgk-frontier ks) e ls)))
                                    image))
           (fn-bs-crash-imagep bs image))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'minimal-theory)
           :use ((:instance fn-ptx-take-split-any (f (fn-lgk-frontier ks)))
                 (:instance fn-ptx-imagep-drop-pad
                            (ops (take (min (nfix j) (len ls)) (fn-ptx-split-ops ino (fn-lgk-frontier ks) e ls)))
                            (pad (fn-ptx-nils (- (nfix j) (len ls)))))
                 (:instance fn-ptx-all-nilp-of-nils (n (- (nfix j) (len ls))))
                 (:instance fn-ptx-split-crash-images-natj (j (min (nfix j) (len ls))))
                 (:instance fn-ptx-natj-min)))))

(defun fn-ptx-noop-opsp (x)
  (if (consp x)
      (and (or (null (car x))
               (and (consp (car x)) (equal (car (car x)) :write) (null (nth 3 (car x)))))
           (fn-ptx-noop-opsp (cdr x)))
    t))
(defthm fn-ptx-split-ops-noop
  (implies (equal (fn-ptx-sum ls) 0) (fn-ptx-noop-opsp (fn-ptx-split-ops ino f e ls)))
  :hints (("Goal" :induct (fn-ptx-split-ops ino f e ls))))
(defthm fn-ptx-take-noop
  (implies (fn-ptx-noop-opsp x) (fn-ptx-noop-opsp (take j x)))
  :hints (("Goal" :induct (take j x))))
(defthm fn-ptx-tear-write-of-empty
  (implies (null (nth 3 op)) (equal (fn-bs-tear-write op sels i unit) nil))
  :hints (("Goal" :in-theory (enable fn-bs-tear-write fn-bs-unit-count))))
(defthm fn-ptx-select-of-noop
  (implies (fn-ptx-noop-opsp ops) (fn-ptx-all-nilp (fn-bs-crash-select ops ch unit)))
  :hints (("Goal" :in-theory (e/d (fn-bs-crash-select) (fn-bs-tear-write)))))
(defthm fn-ptx-crash-of-noop
  (implies (fn-ptx-noop-opsp ops)
           (equal (fn-bs-crash (fn-ptx-with-pending bs ops) ch)
                  (fn-bs-make (fn-bs-unit bs) (fn-bs-inodes bs) (fn-bs-dirs bs) nil (fn-bs-next-ino bs))))
  :hints (("Goal" :in-theory (e/d (fn-bs-crash) (fn-bs-apply-op fn-bs-apply-ops fn-bs-make fn-bs-crash-select))
           :use ((:instance fn-ptx-select-of-noop (unit (fn-bs-unit bs))
                            (ops ops))
                 (:instance fn-ptx-apply-ops-of-nils
                            (i (fn-bs-inodes bs)) (d (fn-bs-dirs bs))
                            (b (fn-bs-crash-select ops ch (fn-bs-unit bs))))))))

(defthm fn-ptx-crash-of-idle
  (implies (equal (fn-bs-pending bs) nil)
           (equal (fn-bs-crash bs ch)
                  (fn-bs-make (fn-bs-unit bs) (fn-bs-inodes bs) (fn-bs-dirs bs) nil (fn-bs-next-ino bs))))
  :hints (("Goal" :in-theory (enable fn-bs-crash fn-bs-crash-select fn-bs-apply-ops))))
(defthm fn-ptx-relp-idle-pending
  (implies (and (fn-lgk-relp bs ks ino genesis max) (not (consp (fn-lgk-inflight ks))))
           (equal (fn-bs-pending bs) nil))
  :hints (("Goal" :in-theory (enable fn-lgk-relp))))
(defthm fn-ptx-idle-entry-sum
  (implies (and (not (consp records)) (equal e (fn-lg-log records prev unit))
                (<= (fn-ptx-sum ls) (len e)))
           (equal (fn-ptx-sum ls) 0))
  :hints (("Goal" :expand ((fn-lg-log records prev unit))
           :use ((:instance fn-ptx-sum-natp)))))
(defthm fn-ptx-split-crash-images-idle
  (implies (and (fn-lgk-relp bs ks ino genesis max)
                (not (consp (fn-lgk-inflight ks)))
                (equal e (fn-lg-log (fn-lgk-inflight ks) (fn-lgk-last ks) (fn-bs-unit bs)))
                (<= (fn-ptx-sum ls) (len e))
                (fn-bs-crash-imagep (fn-ptx-with-pending bs (take j (fn-ptx-split-ops ino (fn-lgk-frontier ks) e ls)))
                                    image))
           (fn-bs-crash-imagep bs image))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories (theory 'minimal-theory) '((:definition fn-bs-crash-choicesp)))
           :use ((:instance fn-ptx-imagep-unpack
                            (s (fn-ptx-with-pending bs (take j (fn-ptx-split-ops ino (fn-lgk-frontier ks) e ls)))))
                 (:instance fn-ptx-relp-idle-pending)
                 (:instance fn-ptx-idle-entry-sum (records (fn-lgk-inflight ks)) (prev (fn-lgk-last ks)) (unit (fn-bs-unit bs)))
                 (:instance fn-ptx-split-ops-noop (f (fn-lgk-frontier ks)))
                 (:instance fn-ptx-take-noop (x (fn-ptx-split-ops ino (fn-lgk-frontier ks) e ls)))
                 (:instance fn-ptx-crash-of-noop
                            (ops (take j (fn-ptx-split-ops ino (fn-lgk-frontier ks) e ls)))
                            (ch (fn-bs-crash-imagep-witness
                                 (fn-ptx-with-pending bs (take j (fn-ptx-split-ops ino (fn-lgk-frontier ks) e ls))) image)))
                 (:instance fn-ptx-crash-of-idle (ch nil))
                 (:instance fn-bs-crash-imagep-suff (s bs) (choices nil))))))

(defthm fn-ptx-split-crash-images-are-entry-crash-images
  (implies (and (fn-lgk-relp bs ks ino genesis max)
                (equal e (fn-lg-log (fn-lgk-inflight ks) (fn-lgk-last ks) (fn-bs-unit bs)))
                (<= (fn-ptx-sum ls) (len e))
                (fn-bs-crash-imagep (fn-ptx-with-pending bs (take j (fn-ptx-split-ops ino (fn-lgk-frontier ks) e ls)))
                                    image))
           (fn-bs-crash-imagep bs image))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'minimal-theory)
           :use ((:instance fn-ptx-split-crash-images-consp)
                 (:instance fn-ptx-split-crash-images-idle)))))

;; What a related store's crash images keep (used by the teeth of P6): the durable
;; content from the end of the entry on, and an image never has operations pending.
(defthm fn-ptx-p6-nthcdr-plus-append
  (implies (and (true-listp d) (natp n))
           (equal (nthcdr (+ (len d) n) (append d x)) (nthcdr n x)))
  :rule-classes nil
  :hints (("Goal" :induct (len d))))
(defthm fn-ptx-p6-pieces-between0
  (implies (posp unit) (fn-lg-writes-between (fn-lg-pieces ino 0 w sels unit) 0 (len w)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-lg-pieces-between (start 0)))
           :in-theory (disable fn-lg-pieces-between fn-lg-pieces))))
(defthm fn-ptx-p6-tail-abstract
  (implies (and (posp (fn-bs-unit s)) (natp k) ino (true-listp d) (true-listp w)
                (equal (len d) (* k (fn-bs-unit s)))
                (equal (fn-bs-durable-content s ino) (append d z))
                (equal (fn-bs-pending s) (list (list :write ino (len d) w)))
                (<= (len w) (len z))
                (fn-bs-crash-imagep s image))
           (equal (nthcdr (+ (len d) (len w)) (fn-bs-durable-content image ino))
                  (nthcdr (len w) z)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories (theory 'minimal-theory)
                                      '((:definition natp) (:definition posp) (:executable-counterpart natp)
                                        (:rewrite unicity-of-0) (:rewrite fn-ptx-natp-len)))
           :use ((:instance fn-bs-crash-of-aligned-append)
                 (:instance fn-lg-nthcdr-of-apply-to-below
                            (c z) (ops (fn-lg-pieces ino 0 w (fn-lg-crash-sels s image) (fn-bs-unit s)))
                            (low 0) (b (len w)))
                 (:instance fn-ptx-p6-pieces-between0 (sels (fn-lg-crash-sels s image)) (unit (fn-bs-unit s)))
                 (:instance fn-ptx-p6-nthcdr-plus-append (n (len w))
                            (x (fn-lg-apply-to z (fn-lg-pieces ino 0 w (fn-lg-crash-sels s image) (fn-bs-unit s)))))))))
(defthm fn-ptx-p6-image-keeps-the-tail
  (implies (and (fn-lgk-relp bs ks ino genesis max)
                (consp (fn-lgk-inflight ks))
                (equal e (fn-lg-log (fn-lgk-inflight ks) (fn-lgk-last ks) (fn-bs-unit bs)))
                (fn-bs-crash-imagep bs image))
           (equal (nthcdr (+ (fn-lgk-frontier ks) (len e)) (fn-bs-durable-content image ino))
                  (nthcdr (+ (fn-lgk-frontier ks) (len e)) (fn-bs-durable-content bs ino))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories (theory 'minimal-theory)
                                      '((:definition natp) (:definition posp) (:executable-counterpart natp)
                                        (:rewrite fn-ptx-natp-len) (:type-prescription len)))
           :use ((:instance fn-lgk-relp-gives-the-tear-hypotheses)
                 (:instance fn-ptx-p6-tail-abstract
                            (s bs) (k (floor (fn-lgk-frontier ks) (fn-bs-unit bs)))
                            (d (fn-bs-take (fn-lgk-frontier ks) (fn-bs-durable-content bs ino)))
                            (z (nthcdr (fn-lgk-frontier ks) (fn-bs-durable-content bs ino)))
                            (w e))
                 (:instance fn-lg-log-true-listp (prev (fn-lgk-last ks)) (records (fn-lgk-inflight ks)) (unit (fn-bs-unit bs)))
                 (:instance fn-ptx-p6-nthcdr-plus-append
                            (d (fn-bs-take (fn-lgk-frontier ks) (fn-bs-durable-content bs ino)))
                            (n (len e))
                            (x (nthcdr (fn-lgk-frontier ks) (fn-bs-durable-content bs ino))))))))
(defthm fn-ptx-p6-crash-has-no-pending
  (equal (fn-bs-pending (fn-bs-crash s ch)) nil)
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-bs-crash))))
(defthm fn-ptx-p6-pending-is-no-image
  (implies (consp (fn-bs-pending image)) (not (fn-bs-crash-imagep s image)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-bs-crash)
           :use ((:instance fn-ptx-imagep-unpack)
                 (:instance fn-ptx-p6-crash-has-no-pending (ch (fn-bs-crash-imagep-witness s image)))))))
;; An image of a related store keeps the durable content BEFORE the pending entry too
;; (the committed log): the first frontier octets (used by the img teeth of P6).
(defthm fn-ptx-p6-take-of-append
  (implies (and (true-listp d) (equal (len d) f))
           (equal (fn-bs-take f (append d x)) d))
  :rule-classes nil
  :hints (("Goal" :induct (len d) :in-theory (enable fn-bs-take))))
(defthm fn-ptx-p6-image-keeps-the-prefix
  (implies (and (fn-lgk-relp bs ks ino genesis max)
                (consp (fn-lgk-inflight ks))
                (equal e (fn-lg-log (fn-lgk-inflight ks) (fn-lgk-last ks) (fn-bs-unit bs)))
                (fn-bs-crash-imagep bs image))
           (equal (fn-bs-take (fn-lgk-frontier ks) (fn-bs-durable-content image ino))
                  (fn-bs-take (fn-lgk-frontier ks) (fn-bs-durable-content bs ino))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories (theory 'minimal-theory)
                                      '((:definition natp) (:definition posp) (:executable-counterpart natp)
                                        (:rewrite fn-ptx-natp-len) (:type-prescription len)))
           :use ((:instance fn-lgk-relp-gives-the-tear-hypotheses)
                 (:instance fn-bs-crash-of-aligned-append
                            (s bs) (k (floor (fn-lgk-frontier ks) (fn-bs-unit bs)))
                            (d (fn-bs-take (fn-lgk-frontier ks) (fn-bs-durable-content bs ino)))
                            (z (nthcdr (fn-lgk-frontier ks) (fn-bs-durable-content bs ino)))
                            (w e))
                 (:instance fn-lg-log-true-listp (prev (fn-lgk-last ks)) (records (fn-lgk-inflight ks)) (unit (fn-bs-unit bs)))
                 (:instance fn-ptx-p6-take-of-append (f (fn-lgk-frontier ks))
                            (d (fn-bs-take (fn-lgk-frontier ks) (fn-bs-durable-content bs ino)))
                            (x (nthcdr (fn-lgk-frontier ks) (fn-bs-durable-content bs ino))))
                 (:instance fn-ptx-p6-take-of-append (f (fn-lgk-frontier ks))
                            (d (fn-bs-take (fn-lgk-frontier ks) (fn-bs-durable-content bs ino)))
                            (x (fn-lg-apply-to (nthcdr (fn-lgk-frontier ks) (fn-bs-durable-content bs ino))
                                 (fn-lg-pieces ino 0 e (fn-lg-crash-sels bs image) (fn-bs-unit bs)))))))))
(defthm fn-ptx-p6-idle-image
  (implies (and (equal (fn-bs-pending s) nil) (fn-bs-crash-imagep s image))
           (equal image (fn-bs-make (fn-bs-unit s) (fn-bs-inodes s) (fn-bs-dirs s) nil (fn-bs-next-ino s))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-bs-crash)
           :use ((:instance fn-ptx-imagep-unpack)
                 (:instance fn-ptx-crash-of-idle (ch (fn-bs-crash-imagep-witness s image)))))))

(defthm fn-ptx-torn-entry-is-no-partial-record
  (implies (and (fn-lgk-relp bs ks ino genesis max)
                (equal (fn-lgk-inflight ks) (list r))
                (equal e (fn-lg-log (list r) (fn-lgk-last ks) (fn-bs-unit bs)))
                (<= (fn-ptx-sum ls) (len e))
                (fn-lg-zerosp (nthcdr (fn-ptx-sum ls) e))
                (natp j) (<= j (len ls))
                (fn-bs-crash-imagep (fn-ptx-with-pending bs (take j (fn-ptx-split-ops ino (fn-lgk-frontier ks) e ls)))
                                    image))
           (let ((content (fn-bs-durable-content image ino))
                 (f (fn-lgk-frontier ks)) (unit (fn-bs-unit bs)))
             (or (fn-lg-crash-verdictp (fn-lg-scan content genesis unit max)
                                       (fn-lgk-committed ks) f (list r) (fn-lgk-last ks) unit)
                 (fn-lg-forgery-in (nthcdr f content) (list r) (fn-lgk-last ks) unit max))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'minimal-theory)
           :use ((:instance fn-ptx-split-crash-images-are-entry-crash-images)
                 (:instance fn-lgk-crash-of-related-state-is-a-prefix)))))

(defthm fn-ptx-prefix-of-one
  (implies (and (fn-lg-prefixp p (list r)) (true-listp p))
           (or (equal p nil) (equal p (list r))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-lg-prefixp))))
(defthm fn-ptx-nthcdr-true-listp
  (implies (true-listp x) (true-listp (nthcdr n x))))
(defthm fn-ptx-crash-verdict-of-one-record-true-scan
  (implies (and (true-listp committed) (true-listp (car scan))
                (fn-lg-crash-verdictp scan committed f (list r) last unit))
           (or (equal (car scan) committed)
               (equal (car scan) (append committed (list r)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-lg-crash-verdictp) (fn-lg-prefixp))
           :use ((:instance fn-ptx-prefix-of-one (p (nthcdr (len committed) (car scan))))))))
(defthm fn-ptx-crash-verdict-of-one-record-of-scan
  (implies (and (true-listp committed)
                (fn-lg-crash-verdictp (fn-lg-scan content genesis unit max) committed f (list r) last unit))
           (or (equal (car (fn-lg-scan content genesis unit max)) committed)
               (equal (car (fn-lg-scan content genesis unit max)) (append committed (list r)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (disable fn-lg-crash-verdictp fn-lg-scan)
           :use ((:instance fn-ptx-crash-verdict-of-one-record-true-scan (scan (fn-lg-scan content genesis unit max)))
                 (:instance fn-lgc-scan-records-true-listp (octets content) (prev genesis))))))

;; the satisfiable witness (theorem 4)
(defun fn-ptx-w-unit () 4)
(defun fn-ptx-w-max () 4096)
(defun fn-ptx-w-genesis () *fn-lg-genesis*)
(defun fn-ptx-w-r () (list 11 12 7))
(defun fn-ptx-w-c0 ()
  (append (fn-lg-log (list (list 1 2 3)) (fn-ptx-w-genesis) (fn-ptx-w-unit)) (fn-bs-zeros 200)))
(defun fn-ptx-w-ks ()
  (fn-lgk-append (fn-lgk-prepare (fn-lgk-recover (fn-ptx-w-c0) (fn-ptx-w-genesis) (fn-ptx-w-unit) (fn-ptx-w-max) 0)
                                 (fn-ptx-w-r))
                 (fn-ptx-w-unit) (len (fn-ptx-w-c0))))
(defun fn-ptx-w-e ()
  (fn-lg-log (list (fn-ptx-w-r)) (fn-lgk-last (fn-ptx-w-ks)) (fn-ptx-w-unit)))
(defun fn-ptx-w-bs ()
  (fn-bs-make (fn-ptx-w-unit) (list (cons 0 (fn-ptx-w-c0))) nil
              (list (list :write 0 (fn-lgk-frontier (fn-ptx-w-ks)) (fn-ptx-w-e))) 1))
(defun fn-ptx-w-ls () (list 10 20 47))
(defun fn-ptx-w-ops () (take 2 (fn-ptx-split-ops 0 (fn-lgk-frontier (fn-ptx-w-ks)) (fn-ptx-w-e) (fn-ptx-w-ls))))
(defun fn-ptx-w-s2 () (fn-ptx-with-pending (fn-ptx-w-bs) (fn-ptx-w-ops)))
(defun fn-ptx-w-choices ()
  (list (list :new :new :new) (list :new :new :new :new :new :new)))
(defun fn-ptx-w-image () (fn-bs-crash (fn-ptx-w-s2) (fn-ptx-w-choices)))
(defthm fn-ptx-p6-witness-image
  (fn-bs-crash-imagep (fn-ptx-w-s2) (fn-ptx-w-image))
  :hints (("Goal" :in-theory (enable fn-ptx-with-pending)
           :use ((:instance fn-bs-crash-imagep-suff (s (fn-ptx-w-s2)) (choices (fn-ptx-w-choices))
                            (image (fn-ptx-w-image)))))))
(defthm fn-ptx-p6-witness
  (and (fn-lgk-relp (fn-ptx-w-bs) (fn-ptx-w-ks) 0 (fn-ptx-w-genesis) (fn-ptx-w-max))
       (equal (fn-lgk-inflight (fn-ptx-w-ks)) (list (fn-ptx-w-r)))
       (equal (fn-ptx-w-e) (fn-lg-log (list (fn-ptx-w-r)) (fn-lgk-last (fn-ptx-w-ks)) (fn-bs-unit (fn-ptx-w-bs))))
       (<= (fn-ptx-sum (fn-ptx-w-ls)) (len (fn-ptx-w-e)))
       (fn-lg-zerosp (nthcdr (fn-ptx-sum (fn-ptx-w-ls)) (fn-ptx-w-e)))
       (natp 2) (<= 2 (len (fn-ptx-w-ls)))
       (fn-bs-crash-imagep (fn-ptx-with-pending (fn-ptx-w-bs)
                                                (take 2 (fn-ptx-split-ops 0 (fn-lgk-frontier (fn-ptx-w-ks)) (fn-ptx-w-e) (fn-ptx-w-ls))))
                           (fn-ptx-w-image))
       (equal (car (fn-lg-scan (fn-bs-durable-content (fn-ptx-w-image) 0) (fn-ptx-w-genesis) (fn-bs-unit (fn-ptx-w-bs)) (fn-ptx-w-max)))
              (fn-lgk-committed (fn-ptx-w-ks)))
       (fn-lg-crash-verdictp (fn-lg-scan (fn-bs-durable-content (fn-ptx-w-image) 0) (fn-ptx-w-genesis) (fn-bs-unit (fn-ptx-w-bs)) (fn-ptx-w-max))
                             (fn-lgk-committed (fn-ptx-w-ks)) (fn-lgk-frontier (fn-ptx-w-ks))
                             (list (fn-ptx-w-r)) (fn-lgk-last (fn-ptx-w-ks)) (fn-bs-unit (fn-ptx-w-bs)))
       (equal (fn-lgk-committed (fn-ptx-w-ks)) '((1 2 3))))
  :hints (("Goal" :in-theory (enable fn-ptx-w-s2 fn-ptx-w-ops)
           :use ((:instance fn-ptx-p6-witness-image)))))
