; One decoded node or one supplied NIL-name byte per classification action.
; Full cold controller/producer composition remains a separate obligation.
(in-package "ACL2")
(include-book "history-decoded-record-cursor")
(local (include-book "arithmetic/top" :dir :system))

; phase, original node, current node, prefix count, NIL child, capture, lease.
(defun fn-hrcur-dos-shapep (c)
  (declare (xargs :guard t))
  (and (fn-hrcur-widthp c 7)
       (member-eq (fn-hrcur-field 0 c)
                  '(:scan :nil :octets :not-octets :refused))
       (natp (fn-hrcur-field 3 c))
       (< (fn-hrcur-field 3 c) *fn-hrcur-u64-bound*)))

(defun fn-hrcur-dos-begin (node capture lease)
  (declare (xargs :guard t))
  (list :scan node node 0 nil capture lease))

(defun fn-hrcur-dos-set (phase node count child c)
  (declare (xargs :guard t))
  (list phase (fn-hrcur-field 1 c) node count child
        (fn-hrcur-field 5 c) (fn-hrcur-field 6 c)))

(defun fn-hrcur-dos-close (count c)
  (declare (xargs :guard (natp count)))
  (fn-hrcur-dos-set (if (< 0 count) :octets :not-octets)
                    (fn-hrcur-field 2 c) count nil c))

(defun fn-hrcur-dos-tick (c)
  (declare (xargs :guard t))
  (let* ((phase (fn-hrcur-field 0 c))
         (node (fn-hrcur-field 2 c)) (count (fn-hrcur-field 3 c))
         (kind (fn-hrcur-field 0 node)))
    (cond
     ((not (fn-hrcur-dos-shapep c)) (mv '(:refused :octet-scan) c))
     ((eq phase :octets) (mv (list :done :octets count) c))
     ((eq phase :not-octets) (mv '(:done :not-octets) c))
     ((eq phase :nil)
      (mv-let (v child) (fn-hrcur-nil-tick (fn-hrcur-field 4 c))
        (cond ((and (consp v) (eq (car v) :need-byte)) (mv v c))
              ((equal v '(:done :nil))
               (mv :continue (fn-hrcur-dos-close count c)))
              ((equal v '(:done :not-nil))
               (mv :continue (fn-hrcur-dos-set :not-octets node count nil c)))
              (t (mv v (fn-hrcur-dos-set :refused node count child c))))))
     ((not (eq phase :scan)) (mv '(:refused :octet-scan) c))
     ((eq kind :pair)
      (let ((head (fn-hrcur-field 1 node)))
        (if (and (eq (fn-hrcur-field 0 head) :atom)
                 (fn-scc-octetp (fn-hrcur-field 1 head)))
            (if (< (+ 1 count) *fn-hrcur-u64-bound*)
                (mv :continue
                    (fn-hrcur-dos-set :scan (fn-hrcur-field 2 node)
                                      (+ 1 count) nil c))
              (mv '(:refused :octet-count)
                  (fn-hrcur-dos-set :refused node count nil c)))
          (mv :continue (fn-hrcur-dos-set :not-octets node count nil c)))))
     ((eq kind :atom)
      (mv :continue
          (if (null (fn-hrcur-field 1 node)) (fn-hrcur-dos-close count c)
            (fn-hrcur-dos-set :not-octets node count nil c))))
     ((eq kind :span)
      (let ((op (fn-hrcur-field 1 node)) (pkg (fn-hrcur-field 2 node))
            (offset (fn-hrcur-field 3 node)) (length (fn-hrcur-field 4 node)))
        (cond
         ((equal op 6)
          (if (and (natp length) (< length *fn-hrcur-u64-bound*)
                   (< (+ count length) *fn-hrcur-u64-bound*))
              (mv :continue (fn-hrcur-dos-close (+ count length) c))
            (mv '(:refused :octet-count)
                (fn-hrcur-dos-set :refused node count nil c))))
         ((equal op 3)
          (mv :continue (fn-hrcur-dos-set :not-octets node count nil c)))
         ((and (equal op 4) (member-equal pkg '(0 1 2)))
          (if (and (member-equal pkg '(1 2)) (equal length 3))
              (mv :continue
                  (fn-hrcur-dos-set :nil node count
                    (fn-hrcur-nil-begin pkg offset length
                                       (fn-hrcur-field 5 c) (fn-hrcur-field 6 c)) c))
            (mv :continue (fn-hrcur-dos-set :not-octets node count nil c))))
         (t (mv '(:refused :octet-node)
                (fn-hrcur-dos-set :refused node count nil c))))))
     (t (mv '(:refused :octet-node)
            (fn-hrcur-dos-set :refused node count nil c))))))

(defun fn-hrcur-dos-supply (c position byte)
  (declare (xargs :guard t))
  (if (and (fn-hrcur-dos-shapep c) (eq (fn-hrcur-field 0 c) :nil))
      (mv-let (v child) (fn-hrcur-nil-supply (fn-hrcur-field 4 c) position byte)
        (if (eq v :continue)
            (mv :continue (fn-hrcur-dos-set :nil (fn-hrcur-field 2 c)
                                          (fn-hrcur-field 3 c) child c))
          (mv v c)))
    (mv '(:refused :octet-response) c)))

; Proof-only denotation and domain. Runtime ticks never execute these scans.
(defun-nx fn-hrcur-dos-domainp (node pool)
  (declare (xargs :measure (acl2-count node)))
  (case (fn-hrcur-field 0 node)
    (:atom (and (fn-hrcur-widthp node 2)
                (not (consp (fn-hrcur-field 1 node)))
                (fn-scc-atomp (fn-hrcur-field 1 node))))
    (:pair (and (fn-hrcur-widthp node 3)
                (fn-hrcur-dos-domainp (fn-hrcur-field 1 node) pool)
                (fn-hrcur-dos-domainp (fn-hrcur-field 2 node) pool)))
    (:span (and (fn-hrcur-widthp node 5)
                (member-equal (fn-hrcur-field 1 node) '(3 4 6))
                (member-equal (fn-hrcur-field 2 node) '(0 1 2))
                (natp (fn-hrcur-field 3 node))
                (< (fn-hrcur-field 3 node) *fn-hrcur-u64-bound*)
                (natp (fn-hrcur-field 4 node))
                (< (+ (fn-hrcur-field 3 node) (fn-hrcur-field 4 node))
                   *fn-hrcur-u64-bound*)
                (<= (+ (fn-hrcur-field 3 node) (fn-hrcur-field 4 node))
                    (len pool))))
    (otherwise nil)))

(defun-nx fn-hrcur-dos-value (node count pool)
  (let ((x (fn-hdc-abstract node pool)))
    (if (and (fn-scc-octet-listp x) (or (< 0 (nfix count)) (consp x)))
        (list :octets (+ (nfix count) (len x)))
      '(:not-octets))))

(defun-nx fn-hrcur-dos-prefixp (original current count)
  (declare (xargs :measure (nfix count)))
  (if (zp count) (equal original current)
    (and (eq (fn-hrcur-field 0 original) :pair)
         (eq (fn-hrcur-field 0 (fn-hrcur-field 1 original)) :atom)
         (fn-scc-octetp (fn-hrcur-field 1 (fn-hrcur-field 1 original)))
         (fn-hrcur-dos-prefixp (fn-hrcur-field 2 original) current (1- count)))))

(defun-nx fn-hrcur-dos-invariantp (c pool)
  (let* ((node (fn-hrcur-field 2 c)) (count (fn-hrcur-field 3 c))
         (child (fn-hrcur-field 4 c))
         (goal (fn-hrcur-dos-value (fn-hrcur-field 1 c) 0 pool)))
    (and (fn-hrcur-dos-shapep c) (fn-scc-octet-listp pool)
         (fn-hrcur-dos-domainp (fn-hrcur-field 1 c) pool)
         (case (fn-hrcur-field 0 c)
           ((:scan :nil)
            (and (fn-hrcur-dos-prefixp (fn-hrcur-field 1 c) node count)
                 (fn-hrcur-dos-domainp node pool)
                 (< (+ count (len (fn-hdc-abstract node pool)))
                    *fn-hrcur-u64-bound*)
                 (equal goal (fn-hrcur-dos-value node count pool))
                 (implies (eq (fn-hrcur-field 0 c) :nil)
                   (and (eq (fn-hrcur-field 0 node) :span)
                        (equal (fn-hrcur-field 1 node) 4)
                        (equal (fn-hrcur-field 1 child) (fn-hrcur-field 2 node))
                        (equal (fn-hrcur-field 2 child) (fn-hrcur-field 3 node))
                        (equal (fn-hrcur-field 3 child) (fn-hrcur-field 4 node))
                        (equal (fn-hrcur-field 5 child) (fn-hrcur-field 5 c))
                        (equal (fn-hrcur-field 6 child) (fn-hrcur-field 6 c))
                        (fn-hrcur-nil-invariantp child pool)))))
           (:octets (and (< 0 count) (equal goal (list :octets count))))
           (:not-octets
            (and (fn-hrcur-dos-prefixp (fn-hrcur-field 1 c) node count)
                 (fn-hrcur-dos-domainp node pool)
                 (equal (fn-hrcur-dos-value node count pool) '(:not-octets))
                 (equal goal '(:not-octets))))
           (otherwise nil)))))

(defthm fn-hrcur-dos-begin-establishes-invariant
  (implies (and (fn-hrcur-dos-domainp node pool) (fn-scc-octet-listp pool)
                (< (len (fn-hdc-abstract node pool)) *fn-hrcur-u64-bound*))
           (fn-hrcur-dos-invariantp (fn-hrcur-dos-begin node capture lease) pool))
  :hints (("Goal" :in-theory
           (enable fn-hrcur-dos-begin fn-hrcur-dos-invariantp
                   fn-hrcur-dos-shapep))))

(defthm fn-hrcur-dos-request-keeps-cursor
  (implies (eq (fn-hrcur-field 0 (mv-nth 0 (fn-hrcur-dos-tick c))) :need-byte)
           (equal (mv-nth 1 (fn-hrcur-dos-tick c)) c))
  :hints (("Goal" :in-theory
           (enable fn-hrcur-dos-tick fn-hrcur-nil-tick))))

(defthm fn-hrcur-dos-tick-keeps-capture-lease
  (and (equal (fn-hrcur-field 5 (mv-nth 1 (fn-hrcur-dos-tick c)))
              (fn-hrcur-field 5 c))
       (equal (fn-hrcur-field 6 (mv-nth 1 (fn-hrcur-dos-tick c)))
              (fn-hrcur-field 6 c)))
  :hints (("Goal" :in-theory
           (enable fn-hrcur-dos-tick fn-hrcur-dos-set fn-hrcur-dos-close
                   fn-hrcur-nil-tick))))

(defthm fn-hrcur-dos-supply-keeps-capture-lease
  (and (equal (fn-hrcur-field 5 (mv-nth 1 (fn-hrcur-dos-supply c position byte)))
              (fn-hrcur-field 5 c))
       (equal (fn-hrcur-field 6 (mv-nth 1 (fn-hrcur-dos-supply c position byte)))
              (fn-hrcur-field 6 c)))
  :hints (("Goal" :in-theory
           (enable fn-hrcur-dos-supply fn-hrcur-dos-set))))

(local
 (defthm fn-hrcur-dos-field-is-nth
   (implies (natp i) (equal (fn-hrcur-field i x) (nth i x)))
   :hints (("Goal" :induct (fn-hrcur-field i x)
            :in-theory (enable fn-hrcur-field nth)))))
(local (in-theory (disable fn-hrcur-dos-field-is-nth)))

(local
 (defthm fn-hrcur-dos-consp-length-positive
   (implies (consp x) (< 0 (len x)))
   :rule-classes :linear
   :hints (("Goal" :in-theory (enable len)))))

(local
 (defthm fn-hrcur-dos-len-nthcdr
   (implies (and (natp offset) (<= offset (len pool)))
            (equal (len (nthcdr offset pool)) (- (len pool) offset)))
   :hints (("Goal" :induct (nthcdr offset pool)
            :in-theory (enable nthcdr)))))
(local
 (defthm fn-hrcur-dos-len-take
   (equal (len (take count pool)) (nfix count))
   :hints (("Goal" :induct (take count pool) :in-theory (enable take)))))
(local
 (defthm fn-hrcur-dos-slice-octets
   (implies (and (fn-scc-octet-listp pool) (natp offset) (natp count)
                 (<= (+ offset count) (len pool)))
            (fn-scc-octet-listp (take count (nthcdr offset pool))))
   :hints (("Goal" :use ((:instance fn-scc-octet-listp-take
                          (x (nthcdr offset pool)) (n count)))
            :in-theory (e/d (fn-scc-octet-listp-facts)
                            (fn-scc-octet-listp take nthcdr))))))

(local
 (defthm fn-hrcur-dos-abstract-octet
   (implies (fn-hrcur-dos-domainp node pool)
            (equal (fn-scc-octetp (fn-hdc-abstract node pool))
                   (and (eq (fn-hrcur-field 0 node) :atom)
                        (fn-scc-octetp (fn-hrcur-field 1 node)) t)))
   :hints (("Goal" :do-not-induct t
            :expand ((fn-hrcur-dos-domainp node pool) (fn-hdc-abstract node pool))
            :in-theory (enable fn-hrcur-dos-domainp fn-hdc-abstract
                               fn-hrcur-field fn-scc-octetp fn-scc-intern)))))

(local
 (defthm fn-hrcur-dos-abstract-span-six
   (implies (and (fn-hrcur-dos-domainp node pool)
                 (fn-scc-octet-listp pool)
                 (eq (fn-hrcur-field 0 node) :span)
                 (equal (fn-hrcur-field 1 node) 6))
            (and (fn-scc-octet-listp (fn-hdc-abstract node pool))
                 (equal (len (fn-hdc-abstract node pool))
                        (fn-hrcur-field 4 node))))
   :hints (("Goal" :do-not-induct t
            :expand ((fn-hrcur-dos-domainp node pool) (fn-hdc-abstract node pool))
            :in-theory (e/d (fn-hrcur-dos-field-is-nth)
                             (fn-hrcur-dos-domainp fn-hdc-abstract
                              fn-scc-octet-listp))))))

(local
 (defthm fn-hrcur-dos-value-pair-step
   (implies (and (fn-hrcur-dos-domainp node pool) (natp count)
                 (eq (fn-hrcur-field 0 node) :pair)
                 (fn-scc-octetp (fn-hdc-abstract (fn-hrcur-field 1 node) pool)))
            (equal (fn-hrcur-dos-value node count pool)
                   (fn-hrcur-dos-value (fn-hrcur-field 2 node) (+ 1 count) pool)))
   :hints (("Goal" :do-not-induct t
            :expand ((fn-hdc-abstract node pool))
            :in-theory (e/d (fn-hrcur-dos-value fn-hrcur-field fn-scc-octet-listp)
                             (fn-hrcur-dos-domainp fn-hdc-abstract))))))

(defthm fn-hrcur-dos-terminal-refines-current-codec-classification
  (implies (and (fn-hrcur-dos-invariantp c pool)
                (equal (mv-nth 0 (fn-hrcur-dos-tick c))
                       (list :done :octets count)))
           (and (fn-scc-octets-valuep
                   (fn-hdc-abstract (fn-hrcur-field 1 c) pool))
                (equal count (len (fn-hdc-abstract (fn-hrcur-field 1 c) pool)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-hrcur-dos-invariantp fn-hrcur-dos-tick
                            fn-hrcur-dos-value fn-scc-octets-valuep
                            fn-hrcur-nil-tick)
                           (fn-hdc-abstract fn-hrcur-dos-domainp
                            fn-hrcur-dos-shapep fn-hrcur-dos-set
                            fn-hrcur-dos-close)))))

(defthm fn-hrcur-dos-terminal-rejection-refines-current-codec
  (implies (and (fn-hrcur-dos-invariantp c pool)
                (equal (mv-nth 0 (fn-hrcur-dos-tick c)) '(:done :not-octets)))
           (not (fn-scc-octets-valuep
                   (fn-hdc-abstract (fn-hrcur-field 1 c) pool))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-hrcur-dos-invariantp fn-hrcur-dos-tick
                            fn-hrcur-dos-value fn-scc-octets-valuep
                            fn-hrcur-nil-tick)
                           (fn-hdc-abstract fn-hrcur-dos-domainp
                            fn-hrcur-dos-shapep fn-hrcur-dos-set
                            fn-hrcur-dos-close)))))

(local
 (defthm fn-hrcur-dos-nil-supply-keeps-coordinates
   (and (equal (fn-hrcur-field 1 (mv-nth 1 (fn-hrcur-nil-supply c position byte)))
               (fn-hrcur-field 1 c))
        (equal (fn-hrcur-field 2 (mv-nth 1 (fn-hrcur-nil-supply c position byte)))
               (fn-hrcur-field 2 c))
        (equal (fn-hrcur-field 3 (mv-nth 1 (fn-hrcur-nil-supply c position byte)))
               (fn-hrcur-field 3 c)))
   :hints (("Goal" :in-theory (enable fn-hrcur-nil-supply)))))

(defthm fn-hrcur-dos-supply-preserves-classification
  (implies (and (fn-hrcur-dos-invariantp c pool)
                (eq (fn-hrcur-field 0 c) :nil)
                (eq (fn-hrcur-field 0 (fn-hrcur-field 4 c)) :check)
                (equal position
                       (+ (fn-hrcur-field 2 (fn-hrcur-field 4 c))
                          (fn-hrcur-field 4 (fn-hrcur-field 4 c))))
                (equal byte (nth position pool)))
           (and (equal (mv-nth 0 (fn-hrcur-dos-supply c position byte)) :continue)
                (fn-hrcur-dos-invariantp
                  (mv-nth 1 (fn-hrcur-dos-supply c position byte)) pool)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hrcur-nil-supply-preserves-invariant
                            (c (fn-hrcur-field 4 c))))
           :in-theory (e/d (fn-hrcur-dos-invariantp fn-hrcur-dos-supply
                            fn-hrcur-dos-set fn-hrcur-dos-shapep)
                           (fn-hdc-abstract fn-hrcur-dos-domainp
                            fn-hrcur-dos-value
                            fn-hrcur-nil-supply fn-hrcur-nil-invariantp
                            fn-hrcur-nil-supply-preserves-invariant)))))

(local
 (defthm fn-hrcur-dos-prefix-step
   (implies (and (natp count) (fn-hrcur-dos-prefixp original current count)
                 (eq (fn-hrcur-field 0 current) :pair)
                 (eq (fn-hrcur-field 0 (fn-hrcur-field 1 current)) :atom)
                 (fn-scc-octetp (fn-hrcur-field 1 (fn-hrcur-field 1 current))))
            (fn-hrcur-dos-prefixp original (fn-hrcur-field 2 current) (+ 1 count)))
   :hints (("Goal" :induct (fn-hrcur-dos-prefixp original current count)
            :in-theory (enable fn-hrcur-dos-prefixp)))))

(local
 (defthm fn-hrcur-dos-pair-fields
   (implies (and (fn-hrcur-dos-domainp node pool)
                 (eq (fn-hrcur-field 0 node) :pair))
            (and (fn-hrcur-dos-domainp (fn-hrcur-field 1 node) pool)
                 (fn-hrcur-dos-domainp (fn-hrcur-field 2 node) pool)
                 (equal (fn-hdc-abstract node pool)
                        (cons (fn-hdc-abstract (fn-hrcur-field 1 node) pool)
                              (fn-hdc-abstract (fn-hrcur-field 2 node) pool)))))
   :hints (("Goal" :do-not-induct t
            :expand ((fn-hrcur-dos-domainp node pool) (fn-hdc-abstract node pool))
            :in-theory (e/d (fn-hrcur-field)
                             (fn-hrcur-dos-domainp fn-hdc-abstract))))))

(local
 (defthm fn-hrcur-dos-atom-field
   (implies (and (fn-hrcur-dos-domainp node pool)
                 (eq (fn-hrcur-field 0 node) :atom))
            (and (not (consp (fn-hrcur-field 1 node)))
                 (equal (fn-hdc-abstract node pool) (fn-hrcur-field 1 node))))
   :hints (("Goal" :do-not-induct t
            :expand ((fn-hrcur-dos-domainp node pool) (fn-hdc-abstract node pool))
            :in-theory (e/d (fn-hrcur-field)
                             (fn-hrcur-dos-domainp fn-hdc-abstract))))))

(local
 (defthm fn-hrcur-dos-span-constructor-unfolds
   (implies (and (fn-hrcur-dos-domainp node pool)
                 (eq (fn-hrcur-field 0 node) :span))
            (equal node (fn-hdc-span (fn-hrcur-field 1 node)
                           (fn-hrcur-field 2 node) (fn-hrcur-field 3 node)
                           (fn-hrcur-field 4 node))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :expand ((fn-hrcur-dos-domainp node pool)
                     (:free (xs) (fn-hrcur-widthp xs 0))
                     (:free (xs) (fn-hrcur-widthp xs 1))
                     (:free (xs) (fn-hrcur-widthp xs 2))
                     (:free (xs) (fn-hrcur-widthp xs 3))
                     (:free (xs) (fn-hrcur-widthp xs 4))
                     (:free (xs) (fn-hrcur-widthp xs 5))
                     (:free (xs) (fn-hrcur-field 0 xs))
                     (:free (xs) (fn-hrcur-field 1 xs))
                     (:free (xs) (fn-hrcur-field 2 xs))
                     (:free (xs) (fn-hrcur-field 3 xs))
                     (:free (xs) (fn-hrcur-field 4 xs)))
            :in-theory (e/d (fn-hrcur-field fn-hrcur-widthp fn-hdc-span)
                             (fn-hrcur-dos-domainp))))))
(local
 (defthm fn-hrcur-dos-span-four-symbolp
   (implies (and (fn-hrcur-dos-domainp node pool)
                 (eq (fn-hrcur-field 0 node) :span)
                 (equal (fn-hrcur-field 1 node) 4))
            (symbolp (fn-hdc-abstract node pool)))
   :hints (("Goal" :do-not-induct t
            :expand ((fn-hdc-abstract node pool))
            :in-theory (e/d (fn-hrcur-field fn-scc-intern)
                             (fn-hrcur-dos-domainp fn-hdc-abstract))))))
(local
 (defthm fn-hrcur-dos-span-four-null
   (implies (and (fn-hrcur-dos-domainp node pool) (fn-scc-octet-listp pool)
                 (eq (fn-hrcur-field 0 node) :span)
                 (equal (fn-hrcur-field 1 node) 4))
            (equal (fn-scc-octet-listp (fn-hdc-abstract node pool))
                   (fn-hrcur-nil-model (fn-hrcur-field 2 node)
                     (fn-hrcur-field 3 node) (fn-hrcur-field 4 node) pool)))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-hrcur-dos-span-constructor-unfolds)
                  (:instance fn-hrcur-dos-span-four-symbolp)
                  (:instance fn-hrcur-nil-model-refines-decoded-symbol
                    (pkg (fn-hrcur-field 2 node)) (offset (fn-hrcur-field 3 node))
                    (count (fn-hrcur-field 4 node))))
            :expand ((fn-hrcur-dos-domainp node pool)
                     (fn-scc-octet-listp (fn-hdc-abstract node pool)))
            :in-theory (e/d (fn-scc-octet-listp)
                            (fn-hrcur-dos-domainp fn-hdc-abstract fn-hdc-span
                             fn-hrcur-nil-model fn-hrcur-dos-span-four-symbolp
                             fn-hrcur-nil-model-refines-decoded-symbol))))))

(local
 (defthm fn-hrcur-dos-span-three-not-octets
   (implies (and (fn-hrcur-dos-domainp node pool)
                 (eq (fn-hrcur-field 0 node) :span)
                 (equal (fn-hrcur-field 1 node) 3))
            (not (fn-scc-octet-listp (fn-hdc-abstract node pool))))
   :hints (("Goal" :do-not-induct t
            :expand ((fn-hrcur-dos-domainp node pool) (fn-hdc-abstract node pool))
            :in-theory (e/d (fn-hrcur-field fn-scc-octet-listp)
                             (fn-hrcur-dos-domainp fn-hdc-abstract))))))

(local
 (defthm fn-hrcur-dos-domain-fields
   (implies (fn-hrcur-dos-domainp node pool)
            (and (member-eq (fn-hrcur-field 0 node) '(:atom :pair :span))
                 (implies (eq (fn-hrcur-field 0 node) :span)
                   (and (member-equal (fn-hrcur-field 1 node) '(3 4 6))
                        (member-equal (fn-hrcur-field 2 node) '(0 1 2))
                        (natp (fn-hrcur-field 3 node))
                        (< (fn-hrcur-field 3 node) *fn-hrcur-u64-bound*)
                        (natp (fn-hrcur-field 4 node))
                        (< (+ (fn-hrcur-field 3 node) (fn-hrcur-field 4 node))
                           *fn-hrcur-u64-bound*)
                        (<= (+ (fn-hrcur-field 3 node) (fn-hrcur-field 4 node))
                            (len pool))))))
   :hints (("Goal" :expand ((fn-hrcur-dos-domainp node pool))
            :in-theory (disable fn-hrcur-dos-domainp)))))

(local
 (defthm fn-hrcur-dos-nil-invariant-fields
   (implies (fn-hrcur-nil-invariantp child pool)
            (fn-hrcur-nil-shapep child))
   :hints (("Goal" :in-theory (enable fn-hrcur-nil-invariantp)))))

(local
 (defthm fn-hrcur-dos-nil-model-noncheck-unfolds
   (implies (or (not (member-equal pkg '(1 2))) (not (equal count 3)))
            (not (fn-hrcur-nil-model pkg offset count pool)))
   :hints (("Goal" :in-theory (enable fn-hrcur-nil-model)))))
(local
 (defthm fn-hrcur-dos-nil-begin-fields
   (implies (and (member-equal pkg '(0 1 2)) (natp offset) (natp count)
                 (< (+ offset count) *fn-hrcur-u64-bound*))
            (and (equal (fn-hrcur-field 1 (fn-hrcur-nil-begin pkg offset count capture lease)) pkg)
                 (equal (fn-hrcur-field 2 (fn-hrcur-nil-begin pkg offset count capture lease)) offset)
                 (equal (fn-hrcur-field 3 (fn-hrcur-nil-begin pkg offset count capture lease)) count)
                 (equal (fn-hrcur-field 5 (fn-hrcur-nil-begin pkg offset count capture lease)) capture)
                 (equal (fn-hrcur-field 6 (fn-hrcur-nil-begin pkg offset count capture lease)) lease)))
   :hints (("Goal" :in-theory (enable fn-hrcur-nil-begin)))))

(local
 (defthm fn-hrcur-dos-scan-tick-preserves
   (implies (and (fn-hrcur-dos-invariantp c pool)
                 (eq (fn-hrcur-field 0 c) :scan))
            (fn-hrcur-dos-invariantp (mv-nth 1 (fn-hrcur-dos-tick c)) pool))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-hrcur-dos-domain-fields (node (fn-hrcur-field 2 c)))
                  (:instance fn-hrcur-dos-abstract-span-six (node (fn-hrcur-field 2 c)))
                  (:instance fn-hrcur-dos-span-four-null (node (fn-hrcur-field 2 c)))
                  (:instance fn-hrcur-dos-prefix-step
                    (original (fn-hrcur-field 1 c)) (current (fn-hrcur-field 2 c))
                    (count (fn-hrcur-field 3 c)))
                  (:instance fn-hrcur-dos-pair-fields (node (fn-hrcur-field 2 c))))
            :in-theory (e/d (fn-hrcur-dos-invariantp fn-hrcur-dos-tick
                             fn-hrcur-dos-shapep fn-hrcur-dos-set fn-hrcur-dos-close
                             fn-hrcur-dos-value fn-scc-octet-listp)
                            (fn-hrcur-dos-domainp fn-hdc-abstract fn-hrcur-dos-domain-fields
                             fn-hrcur-dos-abstract-span-six fn-hrcur-dos-span-four-null
                             fn-hrcur-nil-begin fn-hrcur-nil-model-refines-decoded-symbol
                             fn-hrcur-dos-prefix-step fn-hrcur-dos-pair-fields
                             fn-hrcur-nil-invariantp fn-hrcur-nil-model
                             fn-hrcur-dos-prefixp))))))

(local
 (defthm fn-hrcur-dos-nil-tick-verdicts
   (implies (fn-hrcur-nil-invariantp child pool)
            (let ((v (mv-nth 0 (fn-hrcur-nil-tick child))))
              (or (eq (fn-hrcur-field 0 v) :need-byte)
                  (equal v '(:done :nil)) (equal v '(:done :not-nil)))))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :in-theory (enable fn-hrcur-nil-invariantp fn-hrcur-nil-tick
                               fn-hrcur-nil-shapep)))))

(local
 (defthm fn-hrcur-dos-nil-tick-preserves
   (implies (and (fn-hrcur-dos-invariantp c pool)
                 (eq (fn-hrcur-field 0 c) :nil))
            (fn-hrcur-dos-invariantp (mv-nth 1 (fn-hrcur-dos-tick c)) pool))
   :rule-classes nil
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-hrcur-dos-nil-tick-verdicts (child (fn-hrcur-field 4 c)))
                  (:instance fn-hrcur-dos-span-four-null (node (fn-hrcur-field 2 c)))
                  (:instance fn-hrcur-dos-span-four-symbolp (node (fn-hrcur-field 2 c)))
                  (:instance fn-hrcur-nil-tick-denotes-symbol-nullness
                              (c (fn-hrcur-field 4 c))))
            :in-theory (e/d (fn-hrcur-dos-invariantp fn-hrcur-dos-tick
                             fn-hrcur-dos-shapep fn-hrcur-dos-set fn-hrcur-dos-close
                             fn-hrcur-dos-value fn-scc-octet-listp)
                            (fn-hrcur-dos-domainp fn-hdc-abstract fn-hrcur-nil-tick
                             fn-hrcur-dos-span-four-null fn-hrcur-dos-span-four-symbolp
                             fn-hrcur-nil-model-refines-decoded-symbol
                             fn-hrcur-nil-invariantp fn-hrcur-nil-model
                             fn-hrcur-nil-tick-denotes-symbol-nullness
                             fn-hrcur-dos-prefixp))))))

(local
 (defthm fn-hrcur-dos-invariant-control
   (implies (fn-hrcur-dos-invariantp c pool)
            (and (fn-hrcur-dos-shapep c)
                 (member-eq (fn-hrcur-field 0 c)
                            '(:scan :nil :octets :not-octets))))
   :hints (("Goal" :in-theory (e/d (fn-hrcur-dos-invariantp)
                                  (fn-hrcur-dos-domainp fn-hrcur-dos-prefixp
                                   fn-hrcur-dos-value fn-hdc-abstract))))))

(defthm fn-hrcur-dos-tick-preserves-classification
  (implies (fn-hrcur-dos-invariantp c pool)
           (fn-hrcur-dos-invariantp (mv-nth 1 (fn-hrcur-dos-tick c)) pool))
  :hints (("Goal" :do-not-induct t
           :use (fn-hrcur-dos-scan-tick-preserves fn-hrcur-dos-nil-tick-preserves
                 fn-hrcur-dos-invariant-control)
           :cases ((eq (fn-hrcur-field 0 c) :scan) (eq (fn-hrcur-field 0 c) :nil))
           :in-theory (e/d (fn-hrcur-dos-tick)
                           (fn-hrcur-dos-invariantp fn-hrcur-dos-invariant-control
                            fn-hrcur-dos-shapep fn-hrcur-dos-domainp
                            fn-hrcur-dos-value fn-hrcur-dos-prefixp)))))

(defun fn-hrcur-dos-work (c)
  (declare (xargs :guard t :verify-guards nil))
  (case (fn-hrcur-field 0 c)
    (:scan (+ 5 (* 4 (acl2-count (fn-hrcur-field 2 c)))))
    (:nil (+ 1 (* 4 (acl2-count (fn-hrcur-field 2 c)))
             (fn-hrcur-nil-work (fn-hrcur-field 4 c))))
    (otherwise 0)))

(local
 (defthm fn-hrcur-dos-cdr-node-smaller
   (implies (eq (fn-hrcur-field 0 node) :pair)
            (< (acl2-count (fn-hrcur-field 2 node)) (acl2-count node)))
   :rule-classes :linear
   :hints (("Goal" :do-not-induct t
            :expand ((:free (xs) (fn-hrcur-field 0 xs))
                     (:free (xs) (fn-hrcur-field 1 xs))
                     (:free (xs) (fn-hrcur-field 2 xs)))
            :in-theory (enable acl2-count)))))
(local
 (defthm fn-hrcur-dos-nil-begin-work-bound
   (<= (fn-hrcur-nil-work (fn-hrcur-nil-begin pkg offset count capture lease)) 3)
   :rule-classes :linear
   :hints (("Goal" :in-theory (enable fn-hrcur-nil-work fn-hrcur-nil-begin)))))

(defthm fn-hrcur-dos-tick-productive-progress
  (implies (equal (mv-nth 0 (fn-hrcur-dos-tick c)) :continue)
           (< (fn-hrcur-dos-work (mv-nth 1 (fn-hrcur-dos-tick c)))
              (fn-hrcur-dos-work c)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-hrcur-dos-tick fn-hrcur-dos-set fn-hrcur-dos-close
                            fn-hrcur-dos-shapep fn-hrcur-dos-work fn-hrcur-nil-tick)
                           (fn-hrcur-nil-work fn-hrcur-nil-begin)))))

(defthm fn-hrcur-dos-supply-productive-progress
  (implies (and (fn-hrcur-dos-shapep c) (eq (fn-hrcur-field 0 c) :nil)
                (fn-hrcur-nil-shapep (fn-hrcur-field 4 c))
                (eq (fn-hrcur-field 0 (fn-hrcur-field 4 c)) :check)
                (< (fn-hrcur-field 4 (fn-hrcur-field 4 c)) 3)
                (equal position (+ (fn-hrcur-field 2 (fn-hrcur-field 4 c))
                                   (fn-hrcur-field 4 (fn-hrcur-field 4 c))))
                (fn-scc-octetp byte))
           (< (fn-hrcur-dos-work (mv-nth 1 (fn-hrcur-dos-supply c position byte)))
              (fn-hrcur-dos-work c)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-hrcur-nil-supply-progress (c (fn-hrcur-field 4 c))))
           :in-theory (e/d (fn-hrcur-dos-work fn-hrcur-dos-supply fn-hrcur-dos-set
                            fn-hrcur-nil-supply)
                           (fn-hrcur-nil-work fn-hrcur-nil-supply-progress)))))

(in-theory (disable fn-hrcur-dos-shapep fn-hrcur-dos-begin fn-hrcur-dos-set
                    fn-hrcur-dos-close fn-hrcur-dos-tick fn-hrcur-dos-supply
                    fn-hrcur-dos-domainp fn-hrcur-dos-value
                    fn-hrcur-dos-invariantp fn-hrcur-dos-prefixp fn-hrcur-dos-work))
