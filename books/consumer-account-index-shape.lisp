; Maintained finite alphabet facts for the selected exact character trie.
(in-package "ACL2")
(include-book "consumer-account-index")

(defun fn-cais-octet-alphabet (n)
  (declare (xargs :guard (and (natp n) (<= n 256)) :measure (nfix n)))
  (if (zp n) nil
    (cons (1- n) (fn-cais-octet-alphabet (1- n)))))

(defun fn-cais-branch-alphabet ()
  (declare (xargs :guard t))
  (cons *fn-midx-value-key* (fn-cai-key (fn-cais-octet-alphabet 256))))

(defthm fn-cais-octet-alphabet-member
  (implies (and (natp n) (natp x))
           (iff (member-equal x (fn-cais-octet-alphabet n)) (< x n)))
  :hints (("Goal" :induct (fn-cais-octet-alphabet n)
           :in-theory (enable fn-cais-octet-alphabet))))

(defthm fn-cais-key-alphabet-member
  (implies (and (fn-cbor-octetp x) (fn-cbor-octet-listp xs))
           (iff (member-equal (fn-cai-key-character x) (fn-cai-key xs))
                (member-equal x xs)))
  :hints (("Goal" :induct (fn-cai-key xs)
           :in-theory (e/d (fn-cai-key fn-cbor-octet-listp)
                           (fn-cai-key-character)))))

(defthm fn-cais-octet-alphabet-is-octets
  (implies (and (natp n) (<= n 256))
           (fn-cbor-octet-listp (fn-cais-octet-alphabet n)))
  :hints (("Goal" :in-theory (enable fn-cais-octet-alphabet fn-cbor-octet-listp
                                    fn-cbor-octetp))))

(defthm fn-cais-admitted-octet-key-is-in-alphabet
  (implies (fn-cbor-octetp x)
           (member-equal (fn-cai-key-character x) (fn-cais-branch-alphabet)))
  :hints (("Goal"
           :use ((:instance fn-cais-key-alphabet-member
                            (xs (fn-cais-octet-alphabet 256)))
                 (:instance fn-cais-octet-alphabet-is-octets (n 256))
                 (:instance fn-cais-octet-alphabet-member (n 256)))
           :in-theory (e/d (fn-cbor-octetp member-equal fn-cais-branch-alphabet)
                            (fn-cai-key-character fn-cai-key
                             (:e fn-cai-key) (:e fn-cais-octet-alphabet)
                             (:e fn-cais-branch-alphabet)
                             fn-cais-octet-alphabet
                             fn-cais-key-alphabet-member
                             fn-cais-octet-alphabet-is-octets
                             fn-cais-octet-alphabet-member)))))

; General finite alphabet cardinality, independent of accounts. The helper
; induction consumes one remaining distinct key and removes its alphabet slot.
(defun fn-cais-subset-length-induct (xs ys)
  (declare (xargs :guard (true-listp ys)))
  (if (consp xs)
      (fn-cais-subset-length-induct (cdr xs) (remove-equal (car xs) ys))
    ys))

(defthm fn-cais-member-remove
 (iff (member-equal x (remove-equal a ys))
      (and (not (equal x a)) (member-equal x ys)))
 :hints (("Goal" :induct (remove-equal a ys) :in-theory (enable remove-equal))))
(defthm fn-cais-subset-remove
 (implies (and (subsetp-equal xs ys) (not (member-equal a xs)))
          (subsetp-equal xs (remove-equal a ys)))
 :hints (("Goal" :induct (subsetp-equal xs ys) :in-theory (enable subsetp-equal))))
(defthm fn-cais-remove-length-at-most
 (<= (len (remove-equal a ys)) (len ys))
 :rule-classes :linear
 :hints (("Goal" :induct (remove-equal a ys) :in-theory (enable remove-equal))))
(defthm fn-cais-remove-member-shortens
 (implies (member-equal a ys) (< (len (remove-equal a ys)) (len ys)))
 :rule-classes :linear
 :hints (("Goal" :induct (remove-equal a ys) :in-theory (enable remove-equal))))
(defthm fn-cais-distinct-subset-has-bounded-length
 (implies (and (no-duplicatesp-equal xs) (subsetp-equal xs ys))
          (<= (len xs) (len ys)))
 :rule-classes :linear
 :hints (("Goal" :induct (fn-cais-subset-length-induct xs ys)
          :in-theory (enable no-duplicatesp-equal subsetp-equal))))

(in-theory (disable fn-cais-branch-alphabet (:e fn-cais-branch-alphabet)))
(defthm fn-cais-terminal-in-alphabet (member-equal *fn-midx-value-key* (fn-cais-branch-alphabet)) :hints (("Goal" :in-theory (e/d (fn-cais-branch-alphabet) ((:e fn-cais-branch-alphabet))))))
(defun fn-cais-alphabet-triep (trie)
 (declare (xargs :guard t))
 (if (consp trie)
  (let* ((entry (fn-ag-car trie)) (key (fn-ag-car entry)))
   (and (member-equal key (fn-cais-branch-alphabet))
        (if (characterp key) (fn-cais-alphabet-triep (fn-ag-cdr entry))
         (equal key *fn-midx-value-key*))
        (fn-cais-alphabet-triep (fn-ag-cdr trie))))
  (null trie)))
(defun fn-cais-triep (trie)
 (declare (xargs :guard t))
 (and (fn-midx-unique-branchesp trie) (fn-cais-alphabet-triep trie)))
(defthm fn-cais-alphabet-keys
 (implies (fn-cais-alphabet-triep trie)
          (subsetp-equal (fn-midx-branch-keys trie) (fn-cais-branch-alphabet)))
 :hints (("Goal" :induct (fn-cais-alphabet-triep trie)
          :in-theory (enable fn-cais-alphabet-triep fn-midx-branch-keys))))
(defthm fn-cais-unique-keys
 (implies (fn-midx-unique-branchesp trie)
          (no-duplicatesp-equal (fn-midx-branch-keys trie)))
 :hints (("Goal" :induct (fn-midx-unique-branchesp trie)
          :in-theory (enable fn-midx-unique-branchesp fn-midx-branch-keys))))
(defthm fn-cais-keys-length
 (equal (len (fn-midx-branch-keys trie)) (len trie))
 :hints (("Goal" :induct (len trie) :in-theory (enable fn-midx-branch-keys))))
(defthm fn-cais-alphabet-length
 (equal (len (fn-cais-branch-alphabet)) 257)
 :hints (("Goal" :in-theory (enable fn-cais-branch-alphabet fn-cai-key fn-cais-octet-alphabet))))
(defthm fn-cais-fanout-bound
 (implies (fn-cais-triep trie) (<= (len trie) 257))
 :rule-classes :linear
 :hints (("Goal" :in-theory (enable fn-cais-triep)
          :use ((:instance fn-cais-distinct-subset-has-bounded-length
                           (xs (fn-midx-branch-keys trie))
                           (ys (fn-cais-branch-alphabet)))))))
(defthm fn-cais-get-preserves-alphabet
 (implies (and (fn-cais-alphabet-triep trie) (characterp key))
          (fn-cais-alphabet-triep (fn-midx-branch-get key trie)))
 :hints (("Goal" :induct (fn-midx-branch-get key trie)
          :in-theory (enable fn-midx-branch-get fn-cais-alphabet-triep))))
(defthm fn-cais-put-preserves-alphabet
 (implies (and (fn-cais-alphabet-triep trie)
               (member-equal key (fn-cais-branch-alphabet))
               (if (characterp key) (fn-cais-alphabet-triep value)
                (equal key *fn-midx-value-key*)))
          (fn-cais-alphabet-triep (fn-midx-branch-put key value trie)))
 :hints (("Goal" :induct (fn-midx-branch-put key value trie)
          :in-theory (enable fn-midx-branch-put fn-cais-alphabet-triep))))
(defthm fn-cais-put-octets-preserves-trie
 (implies (and (fn-cais-triep trie) (fn-cbor-octet-listp name))
          (fn-cais-triep (fn-cai-put-octets name row trie)))
 :hints (("Goal" :induct (fn-cai-put-octets name row trie)
          :in-theory (e/d (fn-cai-put-octets fn-cais-triep fn-cbor-octet-listp)
                          (fn-cai-key-character fn-cai-put-is-existing-trie-put fn-midx-branch-get fn-midx-branch-put fn-cais-branch-alphabet
                           (:e fn-cais-branch-alphabet))))))
(defun fn-cais-branch-get-visits (key branches)
 (declare (xargs :guard t))
 (if (consp branches)
  (if (equal key (fn-ag-car (fn-ag-car branches))) 1
   (1+ (fn-cais-branch-get-visits key (fn-ag-cdr branches)))) 0))
(defun fn-cais-branch-put-conses (key branches)
 (declare (xargs :guard t))
 (if (consp branches)
  (if (equal key (fn-ag-car (fn-ag-car branches))) 2
   (1+ (fn-cais-branch-put-conses key (fn-ag-cdr branches)))) 2))
(defthm fn-cais-get-visits-length
 (<= (fn-cais-branch-get-visits key trie) (len trie))
 :rule-classes :linear
 :hints (("Goal" :induct (fn-cais-branch-get-visits key trie))))
(defthm fn-cais-put-conses-length
 (<= (fn-cais-branch-put-conses key trie) (+ 2 (len trie)))
 :rule-classes :linear
 :hints (("Goal" :induct (fn-cais-branch-put-conses key trie))))
(defthm fn-cais-get-preserves-trie
 (implies (and (fn-cais-triep trie) (characterp key))
  (fn-cais-triep (fn-midx-branch-get key trie)))
 :hints (("Goal" :in-theory (enable fn-cais-triep))))
(defun fn-cais-get-visits (name trie)
 (declare (xargs :guard t))
 (if (consp name)
  (+ (fn-cais-branch-get-visits (fn-cai-key-character (car name)) trie)
     (fn-cais-get-visits (cdr name)
       (fn-midx-branch-get (fn-cai-key-character (car name)) trie)))
  (fn-cais-branch-get-visits *fn-midx-value-key* trie)))
(defun fn-cais-put-conses (name trie)
 (declare (xargs :guard t))
 (if (consp name)
  (+ (fn-cais-branch-put-conses (fn-cai-key-character (car name)) trie)
     (fn-cais-put-conses (cdr name)
       (fn-midx-branch-get (fn-cai-key-character (car name)) trie)))
  (fn-cais-branch-put-conses *fn-midx-value-key* trie)))
(defun fn-cais-put-visits (name trie)
 (declare (xargs :guard t))
 (if (consp name)
  (+ (* 2 (fn-cais-branch-get-visits (fn-cai-key-character (car name)) trie))
     (fn-cais-put-visits (cdr name)
       (fn-midx-branch-get (fn-cai-key-character (car name)) trie)))
  (fn-cais-branch-get-visits *fn-midx-value-key* trie)))
(defthm fn-cais-get-path-bound
 (implies (fn-cais-triep trie)
  (<= (fn-cais-get-visits name trie) (* 257 (1+ (len name)))))
 :rule-classes :linear
 :hints (("Goal" :induct (fn-cais-get-visits name trie)
  :in-theory (e/d (fn-cais-get-visits) (fn-midx-branch-get fn-cais-triep)))))
(defthm fn-cais-put-allocation-path-bound
 (implies (fn-cais-triep trie)
  (<= (fn-cais-put-conses name trie) (* 259 (1+ (len name)))))
 :rule-classes :linear
 :hints (("Goal" :induct (fn-cais-put-conses name trie)
  :in-theory (e/d (fn-cais-put-conses) (fn-midx-branch-get fn-cais-triep)))))
(defthm fn-cais-put-work-path-bound
 (implies (fn-cais-triep trie)
  (<= (fn-cais-put-visits name trie) (* 514 (1+ (len name)))))
 :rule-classes :linear
 :hints (("Goal" :induct (fn-cais-put-visits name trie)
  :in-theory (e/d (fn-cais-put-visits) (fn-midx-branch-get fn-cais-triep)))))
