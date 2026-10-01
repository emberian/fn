; Actual typed Store-row grammar to shallow decoded remap path.
; Ghost functions only; never a served validator.
(in-package "ACL2")
(include-book "held-record")
(include-book "snapshot-remap-cold-domain")

(defun-nx fn-rccg-logical-prefixp (n x)
 (declare (xargs :measure (nfix n)))
 (if (zp n) t
  (and (consp x) (not (fn-scc-octet-listp x))
       (fn-rccg-logical-prefixp (1- n) (cdr x)))))

(local (defthm fn-rccg-field-is-nth
 (implies (natp i) (equal (fn-hrcur-field i c) (nth i c)))
 :hints (("Goal" :induct (fn-hrcur-field i c)
 :in-theory (enable fn-hrcur-field nth)))))

(local (defthm fn-rccg-len-nthcdr
 (implies (and (natp offset) (<= offset (len pool)))
  (equal (len (nthcdr offset pool)) (- (len pool) offset)))
 :hints (("Goal" :induct (nthcdr offset pool) :in-theory (enable nthcdr)))))

(local (defthm fn-rccg-octet-slice
 (implies (and (fn-scc-octet-listp pool) (natp offset) (natp count)
               (<= (+ offset count) (len pool)))
  (fn-scc-octet-listp (take count (nthcdr offset pool))))
 :hints (("Goal" :use ((:instance fn-scc-octet-listp-take
                        (x (nthcdr offset pool)) (n count)))
 :in-theory (e/d (fn-scc-octet-listp-facts) (fn-scc-octet-listp take nthcdr))))))

(local (defthm fn-rccg-nonoctet-list-has-decoded-pair
 (implies (and (fn-hrcur-cold-domainp node pool) (fn-scc-octet-listp pool)
               (consp (fn-hdc-abstract node pool))
               (not (fn-scc-octet-listp (fn-hdc-abstract node pool))))
  (fn-odm-pairp node))
 :hints (("Goal" :do-not-induct t
 :cases ((eq (fn-hrcur-field 0 node) :atom)
         (eq (fn-hrcur-field 0 node) :pair)
         (eq (fn-hrcur-field 0 node) :span))
 :in-theory (e/d (fn-hrcur-cold-domainp fn-hrcur-dos-domainp fn-hdc-abstract
                  fn-odm-pairp fn-hrcur-widthp)
                 (fn-scc-octet-listp take nthcdr fn-scc-intern))))))

(local (defthm fn-rccg-pair-abstract-frame
 (implies (fn-odm-pairp node)
  (equal (fn-hdc-abstract node pool)
         (cons (fn-hdc-abstract (fn-hdc-car node) pool)
               (fn-hdc-abstract (fn-hdc-cdr node) pool))))
 :hints (("Goal" :do-not-induct t
 :in-theory (enable fn-odm-pairp fn-hdc-abstract fn-hdc-car fn-hdc-cdr)))))
(local (defthm fn-rccg-pair-cdr-has-domain
 (implies (and (fn-odm-pairp node) (fn-hrcur-cold-domainp node pool))
  (fn-hrcur-cold-domainp (fn-hdc-cdr node) pool))
 :hints (("Goal" :do-not-induct t
 :in-theory (enable fn-odm-pairp fn-hdc-cdr fn-hrcur-cold-domainp
                    fn-hrcur-field fn-hrcur-widthp)))))

(defthm fn-rccg-typed-logical-prefix-is-decoded-replacement-path
 (implies (and (natp n) (fn-hrcur-cold-domainp node pool)
               (fn-scc-octet-listp pool)
               (fn-rccg-logical-prefixp n (fn-hdc-abstract node pool)))
  (fn-odm-prefixp n node))
 :hints (("Goal" :induct (fn-odm-prefixp n node)
 :in-theory (e/d (fn-rccg-logical-prefixp fn-odm-prefixp)
                 (fn-hrcur-cold-domainp fn-hrcur-dos-domainp fn-hdc-abstract
                  fn-odm-pairp fn-hdc-cdr fn-hdc-car fn-scc-octet-listp)))))

(defthm fn-rccg-actual-held-grammar-has-replacement-prefix
 (implies (fn-held-p h) (fn-rccg-logical-prefixp 5 h))
 :hints (("Goal" :do-not-induct t
 :in-theory (enable fn-held-p fn-held-internals fn-rccg-logical-prefixp
                    fn-scc-octet-listp fn-scc-octetp))))

(defthm fn-rccg-actual-composite-grammar-has-outer-prefix
 (implies (fn-hstxa-p h) (fn-rccg-logical-prefixp 3 h))
 :hints (("Goal" :do-not-induct t
 :in-theory (enable fn-hstxa-p fn-stxa-p fn-held-p fn-held-internals
                    fn-rccg-logical-prefixp fn-scc-octet-listp fn-scc-octetp))))

(local (defthm fn-rccg-one-prefix-is-pair
 (equal (fn-odm-prefixp 1 node) (fn-odm-pairp node))
 :hints (("Goal" :expand ((fn-odm-prefixp 1 node) (fn-odm-prefixp 0 (fn-hdc-cdr node)))))))
(local (defthm fn-rccg-pair-car-has-domain
 (implies (and (fn-odm-pairp node) (fn-hrcur-cold-domainp node pool))
  (fn-hrcur-cold-domainp (fn-hdc-car node) pool))
 :hints (("Goal" :do-not-induct t
 :in-theory (enable fn-odm-pairp fn-hdc-car fn-hrcur-cold-domainp
                    fn-hrcur-field fn-hrcur-widthp)))))

(local (defthm fn-rccg-selected-path-has-domain
 (implies (and (natp i) (fn-odm-prefixp (1+ i) node)
               (fn-hrcur-cold-domainp node pool))
  (fn-hrcur-cold-domainp (fn-odm-at i node) pool))
 :hints (("Goal" :induct (fn-odm-at i node)
 :in-theory (e/d (fn-odm-at fn-odm-prefixp)
                 (fn-hrcur-cold-domainp fn-hdc-cdr fn-hdc-car
                  fn-odm-pairp fn-hdc-abstract))))))

(defthm fn-rccg-actual-typed-held-has-decoded-remap-path
 (implies (and (fn-held-p (fn-hdc-abstract node pool))
               (fn-hrcur-cold-domainp node pool) (fn-scc-octet-listp pool))
  (fn-odm-prefixp 5 node))
 :hints (("Goal"
 :use ((:instance fn-rccg-typed-logical-prefix-is-decoded-replacement-path (n 5)))
 :in-theory (disable fn-hdc-abstract fn-held-p fn-odm-prefixp
                    fn-rccg-logical-prefixp fn-hrcur-cold-domainp fn-scc-octet-listp))))

(local (defthm fn-rccg-composite-has-held-nth
 (implies (fn-hstxa-p h) (fn-held-p (nth 2 h)))
 :hints (("Goal" :expand ((nth 2 h) (nth 1 (cdr h)) (nth 0 (cddr h)))
 :in-theory (e/d (fn-hstxa-p) (fn-held-p fn-stxa-p))))))

(defthm fn-rccg-actual-typed-composite-has-decoded-remap-path
 (implies (and (fn-hstxa-p (fn-hdc-abstract node pool))
               (fn-hrcur-cold-domainp node pool) (fn-scc-octet-listp pool))
  (and (fn-odm-prefixp 3 node)
       (fn-odm-prefixp 5 (fn-odm-at 2 node))))
 :hints (("Goal"
 :use ((:instance fn-rccg-typed-logical-prefix-is-decoded-replacement-path (n 3))
       (:instance fn-rccg-selected-path-has-domain (i 2))
       (:instance fn-odm-at-refines-the-logical-field-read (n 2))
       (:instance fn-rccg-actual-typed-held-has-decoded-remap-path
        (node (fn-odm-at 2 node))))
 :in-theory (e/d ()
                 (fn-hstxa-p fn-hdc-abstract fn-held-p fn-stxa-p fn-odm-prefixp fn-odm-at
                  fn-rccg-logical-prefixp fn-hrcur-cold-domainp fn-scc-octet-listp)))))
