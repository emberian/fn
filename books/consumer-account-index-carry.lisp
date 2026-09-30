; Actual persistent account trie update with parallel canonical size metadata.
; The metadata relation is proof-only. The update reads fixed-size carries and
; rebuilds only the selected path/list prefixes, never summarizing a shared tree.
(in-package "ACL2")
(include-book "consumer-account-index")
(include-book "consumer-account-index-shape")
(include-book "store-tree-size")

(defun fn-cait-size (carry)
  (declare (xargs :guard t))
  (if (fn-scs-carryp carry) carry (fn-scs-atom nil)))

(defun fn-cait-carry (metadata)
  (declare (xargs :guard t))
  (fn-cait-size (fn-ag-car metadata)))

(defun fn-cait-value-carry (metadata)
  (declare (xargs :guard t))
  (fn-cait-size (fn-ag-car (fn-ag-cdr metadata))))

(defun fn-cait-child (metadata)
  (declare (xargs :guard t))
  (fn-ag-car (fn-ag-cdr (fn-ag-cdr metadata))))

(defun fn-cait-tail (metadata)
  (declare (xargs :guard t))
  (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr metadata)))))

(defun fn-cait-key-carry (key)
  (declare (xargs :guard t))
  (fn-scs-atom (if (or (integerp key) (characterp key)
                       (stringp key) (symbolp key)) key nil)))

(defun fn-cait-node (key value-carry child tail)
  (declare (xargs :guard t))
  (let* ((v (fn-cait-size value-carry))
         (entry (fn-scs-cons (fn-cait-key-carry key) v))
         (root (fn-scs-cons entry (fn-cait-carry tail))))
    (list root v child tail)))

; A metadata lookup follows exactly the branch search used for the value.
(defun fn-cait-branch-child (key branches metadata)
  (declare (xargs :guard t))
  (if (consp branches)
      (if (equal key (fn-ag-car (fn-ag-car branches)))
          (fn-cait-child metadata)
        (fn-cait-branch-child key (cdr branches) (fn-cait-tail metadata)))
    nil))

; MV2 is (actual changed branch list, its maintained metadata). Untouched
; entry/subtrie annotations are borrowed literally; no shared-child traversal.
(defun fn-cait-branch-put (key value value-carry child branches metadata)
  (declare (xargs :guard t))
  (if (consp branches)
      (if (equal key (fn-ag-car (car branches)))
          (mv (cons (cons key value) (cdr branches))
              (fn-cait-node key value-carry child (fn-cait-tail metadata)))
        (mv-let (tail tail-metadata)
          (fn-cait-branch-put key value value-carry child
                              (cdr branches) (fn-cait-tail metadata))
          (mv (cons (car branches) tail)
              (fn-cait-node (fn-ag-car (car branches))
                             (fn-cait-value-carry metadata)
                             (fn-cait-child metadata) tail-metadata))))
    (mv (list (cons key value)) (fn-cait-node key value-carry child nil))))

(defun fn-cait-put-octets (name value value-carry trie metadata)
  (declare (xargs :guard t))
  (if (consp name)
      (let ((key (fn-cai-key-character (car name))))
        (mv-let (child child-metadata)
          (fn-cait-put-octets
           (cdr name) value value-carry (fn-midx-branch-get key trie)
           (fn-cait-branch-child key trie metadata))
          (fn-cait-branch-put key child (fn-cait-carry child-metadata)
                              child-metadata trie metadata)))
    (fn-cait-branch-put *fn-midx-value-key* value value-carry nil trie metadata)))

; Proof abstraction only; never run at staging, admission or publication.
(defun fn-cait-annotation (trie)
  (declare (xargs :guard t :verify-guards nil :measure (acl2-count trie)))
  (if (consp trie)
      (let* ((entry (car trie)) (key (fn-ag-car entry))
             (value (fn-ag-cdr entry)))
        (list (fn-scs-summary trie) (fn-scs-summary value)
              (if (characterp key) (fn-cait-annotation value) nil)
              (fn-cait-annotation (cdr trie))))
    nil))

(defthm fn-cait-size-of-summary
  (equal (fn-cait-size (fn-scs-summary x)) (fn-scs-summary x))
  :hints (("Goal" :in-theory (enable fn-cait-size))))

(defthm fn-cait-carry-of-annotation
  (implies (true-listp trie)
           (equal (fn-cait-carry (fn-cait-annotation trie))
                  (fn-scs-summary trie)))
  :hints (("Goal" :in-theory (enable fn-cait-carry fn-cait-annotation))))

(defthm fn-cait-branch-put-has-existing-value
  (equal (mv-nth 0 (fn-cait-branch-put key value value-carry child branches metadata))
         (fn-midx-branch-put key value branches))
  :hints (("Goal" :induct (fn-cait-branch-put key value value-carry child branches metadata)
           :in-theory (enable fn-cait-branch-put fn-midx-branch-put))))

(defthm fn-cait-put-has-existing-value
  (equal (mv-nth 0 (fn-cait-put-octets name value value-carry trie metadata))
         (fn-cai-put-octets name value trie))
  :hints (("Goal" :induct (fn-cait-put-octets name value value-carry trie metadata)
           :in-theory (e/d (fn-cait-put-octets fn-cai-put-octets)
                            (fn-cait-branch-put fn-midx-branch-put
                             fn-cai-put-is-existing-trie-put
                             fn-cait-branch-child fn-midx-branch-get
                             fn-cai-key-character)))))

(local
 (defthm fn-cait-alphabet-trie-is-list
   (implies (fn-cais-alphabet-triep trie) (true-listp trie))
   :hints (("Goal" :induct (fn-cais-alphabet-triep trie)
            :in-theory (enable fn-cais-alphabet-triep)))))

(local
 (defthm fn-cait-key-carry-is-summary
   (implies (or (characterp key) (equal key *fn-midx-value-key*))
            (equal (fn-cait-key-carry key) (fn-scs-summary key)))
   :hints (("Goal" :in-theory (enable fn-cait-key-carry)))))

(local
 (defthm fn-cait-node-is-annotation
   (implies (and (or (characterp key) (equal key *fn-midx-value-key*))
                 (true-listp tail))
            (equal (fn-cait-node key (fn-scs-summary value)
                                (if (characterp key) (fn-cait-annotation value) nil)
                                (fn-cait-annotation tail))
                   (fn-cait-annotation (cons (cons key value) tail))))
   :hints (("Goal"
            :use ((:instance fn-scs-cons-preserves-canonical-size
                             (x key) (y value)
                             (a (fn-scs-summary key)) (d (fn-scs-summary value)))
                  (:instance fn-scs-cons-preserves-canonical-size
                             (x (cons key value)) (y tail)
                             (a (fn-scs-summary (cons key value)))
                             (d (fn-scs-summary tail))))
            :in-theory
            (e/d (fn-cait-node fn-cait-annotation)
                 (fn-scs-summary fn-scs-cons fn-cait-carry fn-cait-key-carry
                  fn-cait-size fn-scs-cons-preserves-canonical-size))))))

(local
 (defthm fn-cait-node-empty-is-annotation
   (implies (or (characterp key) (equal key *fn-midx-value-key*))
            (equal (fn-cait-node key (fn-scs-summary value)
                                (if (characterp key) (fn-cait-annotation value) nil) nil)
                   (fn-cait-annotation (list (cons key value)))))
   :hints (("Goal" :use ((:instance fn-cait-node-is-annotation (tail nil)))
            :in-theory (disable fn-cait-node fn-cait-annotation)))))

(local
 (defthm fn-cait-node-character
   (implies (and (characterp key) (true-listp tail))
            (equal (fn-cait-node key (fn-scs-summary value)
                                (fn-cait-annotation value) (fn-cait-annotation tail))
                   (fn-cait-annotation (cons (cons key value) tail))))
   :hints (("Goal" :use fn-cait-node-is-annotation
            :in-theory (disable fn-cait-node fn-cait-annotation)))))
(local
 (defthm fn-cait-node-terminal
   (implies (true-listp tail)
            (equal (fn-cait-node *fn-midx-value-key* (fn-scs-summary value)
                                nil (fn-cait-annotation tail))
                   (fn-cait-annotation (cons (cons *fn-midx-value-key* value) tail))))
   :hints (("Goal" :use ((:instance fn-cait-node-is-annotation (key *fn-midx-value-key*)))
            :in-theory (disable fn-cait-node fn-cait-annotation)))))
(local
 (defthm fn-cait-node-character-empty
   (implies (characterp key)
            (equal (fn-cait-node key (fn-scs-summary value) (fn-cait-annotation value) nil)
                   (fn-cait-annotation (list (cons key value)))))
   :hints (("Goal" :use fn-cait-node-empty-is-annotation
            :in-theory (disable fn-cait-node fn-cait-annotation)))))
(local
 (defthm fn-cait-node-terminal-empty
   (equal (fn-cait-node *fn-midx-value-key* (fn-scs-summary value) nil nil)
          (fn-cait-annotation (list (cons *fn-midx-value-key* value))))
   :hints (("Goal" :use ((:instance fn-cait-node-empty-is-annotation (key *fn-midx-value-key*)))
            :in-theory (disable fn-cait-node fn-cait-annotation)))))

(local
 (defthm fn-cait-branch-put-is-list
   (implies (true-listp branches)
            (true-listp (fn-midx-branch-put key value branches)))
   :hints (("Goal" :induct (fn-midx-branch-put key value branches)
            :in-theory (enable fn-midx-branch-put)))))

(local
 (defthm fn-cait-get-child-is-annotation
   (implies (and (fn-cais-alphabet-triep trie) (characterp key))
            (equal (fn-cait-branch-child key trie (fn-cait-annotation trie))
                   (fn-cait-annotation (fn-midx-branch-get key trie))))
   :hints (("Goal" :induct (fn-cait-branch-child key trie metadata)
            :in-theory (enable fn-cait-branch-child fn-cait-annotation
                               fn-cait-child fn-cait-tail fn-midx-branch-get
                               fn-cais-alphabet-triep)))))

(defthm fn-cait-branch-put-maintains-annotation
  (implies (and (fn-cais-alphabet-triep branches)
                (or (characterp key) (equal key *fn-midx-value-key*))
                (equal value-carry (fn-scs-summary value))
                (equal child (if (characterp key) (fn-cait-annotation value) nil))
                (equal metadata (fn-cait-annotation branches)))
           (equal (mv-nth 1 (fn-cait-branch-put key value value-carry child branches metadata))
                  (fn-cait-annotation (fn-midx-branch-put key value branches))))
  :hints (("Goal" :induct (fn-cait-branch-put key value value-carry child branches metadata)
           :in-theory
           (e/d (fn-cait-branch-put fn-midx-branch-put fn-cais-alphabet-triep
                  fn-cait-tail fn-cait-value-carry fn-cait-child)
                (fn-cait-node fn-cait-carry fn-scs-summary fn-cait-key-carry
                 fn-scs-cons fn-cait-size)))))

(local
 (defthm fn-cait-existing-put-is-list
   (implies (fn-cais-alphabet-triep trie)
            (true-listp (fn-cai-put-octets name value trie)))
   :hints (("Goal" :in-theory
            (e/d (fn-cai-put-octets)
                 (fn-midx-branch-put fn-midx-branch-get
                  fn-cai-put-is-existing-trie-put))))))

; Boundary keystone: the actual returned value is the existing exact trie and
; every retained annotation, including the root canonical byte size, is exact.
; VALUE-CARRY is supplied by the bounded account/binding constructor; this
; function never encodes or walks that value to rediscover its size.
(defthm fn-cait-put-maintains-canonical-annotation
  (implies (and (fn-cais-alphabet-triep trie)
                (equal metadata (fn-cait-annotation trie))
                (equal value-carry (fn-scs-summary value)))
           (equal (mv-nth 1 (fn-cait-put-octets name value value-carry trie metadata))
                  (fn-cait-annotation (fn-cai-put-octets name value trie))))
  :hints (("Goal" :induct (fn-cait-put-octets name value value-carry trie metadata)
           :in-theory
           (e/d (fn-cait-put-octets fn-cai-put-octets)
                (fn-cait-branch-put fn-midx-branch-put fn-cait-branch-child
                 fn-midx-branch-get fn-cai-key-character fn-cait-carry
                 fn-cait-annotation fn-scs-summary fn-cai-put-is-existing-trie-put)))))

(defthm fn-cait-put-root-size-is-exact
  (implies (and (fn-cais-alphabet-triep trie)
                (equal metadata (fn-cait-annotation trie))
                (equal value-carry (fn-scs-summary value)))
           (equal (fn-cait-carry
                   (mv-nth 1 (fn-cait-put-octets name value value-carry trie metadata)))
                  (fn-scs-summary (mv-nth 0 (fn-cait-put-octets name value value-carry trie metadata)))))
  :hints (("Goal" :in-theory (e/d (fn-cais-triep)
                                   (fn-cait-put-octets fn-cai-put-octets
                                    fn-cait-annotation fn-cait-carry fn-scs-summary))
           :use ((:instance fn-cait-existing-put-is-list)))))

(in-theory (disable fn-cait-size fn-cait-carry fn-cait-value-carry
                    fn-cait-child fn-cait-tail fn-cait-key-carry fn-cait-node
                    fn-cait-branch-child fn-cait-branch-put fn-cait-put-octets
                    fn-cait-annotation))

; Conservative primitive-constructor allowances, proof/measurement only.
; One metadata node constructs four spine conses, two three-field carries,
; one scalar-key carry, and at most two fallback NIL carries: <=19 conses.
; At most two actual trie conses per rebuilt branch entry makes21. These
; allowances do not charge caller row/credential/context/control objects,
; scalar-width work or retained/retired graphs, and are not a heap theorem.
(defun fn-cait-path-cons-allowance (name trie)
  (declare (xargs :guard t))
  (* 21 (fn-cais-put-conses name trie)))

; The extra metadata child lookup follows the same immutable path. The
; terminal lookup is overcharged once, preserving a simple conservative bound.
(defun fn-cait-path-entry-allowance (name trie)
  (declare (xargs :guard t))
  (+ (fn-cais-put-visits name trie) (fn-cais-get-visits name trie)))

(defthm fn-cait-path-cons-allowance-bound
  (implies (fn-cais-triep trie)
           (<= (fn-cait-path-cons-allowance name trie) (* 5439 (1+ (len name)))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable fn-cait-path-cons-allowance))))

(defthm fn-cait-path-entry-allowance-bound
  (implies (fn-cais-triep trie)
           (<= (fn-cait-path-entry-allowance name trie) (* 771 (1+ (len name)))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable fn-cait-path-entry-allowance))))

(in-theory (disable fn-cait-path-cons-allowance fn-cait-path-entry-allowance))
