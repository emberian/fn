; The carried retention trie and its refresh invariant (D14 Part A).
; Pin leaves share the ledger's positional records; release leaves share ID
; strings. A root :finds edge carries the find invariant. Reads of membership
; and stored IDs ignore that edge. Marked carries have string/unique pin IDs,
; unique release IDs, disjoint pin/release IDs, and exact pin-record answers.
; Build is linear with the retention keyset checks; delta touches only the
; changed pin/release prefix and paths. The recognizer is never a served scan.
; Memory: one tag cons per :end bucket, none per ordinary branch or leaf.
; Exact 10k random 64-hex count (seed 289): PRF-289 27,808 conses, tagged
; 27,808 (zero buckets), plus two for the root mark = 27,810. The earlier
; character trie costs 1,246,484 on this fixture; the historical header's
; different fixture gave 1,246,448. See build/d14/memory_count.py.
(in-package "ACL2")
(include-book "retain-known")
(include-book "msgid-index")
(local (in-theory (disable (tau-system))))
(local (in-theory (enable (:definition fn-midx-branch-get))))

; 1. Compressed trie: record and string leaves, tagged end buckets.
(defun fn-rit-leaf-id (x)
  (declare (xargs :guard t))
  (if (stringp x) x
    (if (and (consp x) (stringp (car x))) (car x) nil)))
(defun fn-rit-leafp (x)
  (declare (xargs :guard t))
  (stringp (fn-rit-leaf-id x)))
(defun fn-rit-branchp (x)
  (declare (xargs :guard t))
  (and (consp x) (consp (car x))))
; One cons for the bucket tag, none for a branch or a leaf.
; The bucket is (:end . LEAVES); leaves share the ledger's own records.
(defun fn-rit-bucket-find (id xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (if (and (fn-rit-leafp (car xs))
               (equal id (fn-rit-leaf-id (car xs))))
          (car xs)
        (fn-rit-bucket-find id (cdr xs)))
    nil))
(defun fn-rit-bucket-put (new xs)
  (declare (xargs :guard t))
  (if (consp xs)
      (if (equal (fn-rit-leaf-id new) (fn-rit-leaf-id (car xs)))
          (cons new (cdr xs))
        (cons (car xs) (fn-rit-bucket-put new (cdr xs))))
    (list new)))
(defun fn-rit-get (id i node)
  (declare (xargs :guard (and (stringp id) (natp i))
                  :measure (nfix (- (length id) (nfix i)))))
  (cond ((fn-rit-leafp node)
         (if (equal id (fn-rit-leaf-id node)) node nil))
        ((not (fn-rit-branchp node)) nil)
        ((and (mbt (and (stringp id) (natp i))) (< i (length id)))
         (fn-rit-get id (1+ i) (fn-midx-branch-get (char id i) node)))
        (t (fn-rit-bucket-find
            id (fn-ag-cdr (fn-midx-branch-get :end node))))))
(defun fn-rit-hasp (id i node)
  (declare (xargs :guard (and (stringp id) (natp i))))
  (if (fn-rit-get id i node) t nil))
(defun fn-rit-lift (old i)
  (declare (xargs :guard (and (fn-rit-leafp old) (natp i))))
  (let ((id (fn-rit-leaf-id old)))
    (if (and (mbt (and (stringp id) (natp i))) (< i (length id)))
        (list (cons (char id i) old))
      (list (cons :end (list :end old))))))
(defun fn-rit-put (new i node)
  (declare (xargs :guard (and (fn-rit-leafp new) (natp i))
                  :measure (+ (* 2 (nfix (- (length (fn-rit-leaf-id new)) (nfix i))))
                              (if (fn-rit-leafp node) 1 0))))
  (let ((id (fn-rit-leaf-id new)))
    (cond ((fn-rit-leafp node)
           (if (equal (fn-rit-leaf-id node) id)
               new
             (fn-rit-put new i (fn-rit-lift node i))))
          ((not (fn-rit-branchp node)) new)
          ((and (mbt (and (stringp id) (natp i))) (< i (length id)))
           (let ((key (char id i)))
             (fn-midx-branch-put
              key (fn-rit-put new (1+ i) (fn-midx-branch-get key node)) node)))
          (t (fn-midx-branch-put
              :end (cons :end (fn-rit-bucket-put
                              new (fn-ag-cdr (fn-midx-branch-get :end node))))
              node)))))
(mutual-recursion
 (defun fn-rit-strings (x)
   (declare (xargs :guard t :measure (acl2-count x)))
   (cond ((fn-rit-leafp x) (list (fn-rit-leaf-id x)))
         ((fn-rit-branchp x)
          (append (if (equal (caar x) :finds) nil
                    (if (equal (caar x) :end)
                        (fn-rit-leaves-strings (fn-ag-cdr (cdar x)))
                      (fn-rit-strings (cdar x))))
                  (fn-rit-branches-strings (cdr x))))
         (t nil)))
 (defun fn-rit-branches-strings (xs)
   (declare (xargs :guard t :measure (acl2-count xs)))
   (if (consp xs)
       (append (if (and (consp (car xs)) (not (equal (caar xs) :finds)))
                   (if (equal (caar xs) :end)
                       (fn-rit-leaves-strings (fn-ag-cdr (cdar xs)))
                     (fn-rit-strings (cdar xs)))
                 nil)
               (fn-rit-branches-strings (cdr xs)))
     nil))
 (defun fn-rit-leaves-strings (xs)
   (declare (xargs :guard t :measure (acl2-count xs)))
   (if (consp xs)
       (if (fn-rit-leafp (car xs))
           (cons (fn-rit-leaf-id (car xs)) (fn-rit-leaves-strings (cdr xs)))
         (fn-rit-leaves-strings (cdr xs)))
     nil)))

(local (in-theory (enable fn-midx-branch-get)))
; A lookup at a leaf, a branch and an empty node.
(defthm fn-rit-hasp-of-leaf
  (implies (fn-rit-leafp node)
           (equal (fn-rit-hasp x i node) (equal (fn-rit-leaf-id node) x)))
  :hints (("Goal" :expand ((fn-rit-hasp x i node)))))

(defthm fn-rit-hasp-of-branch
  (implies (fn-rit-branchp node)
           (equal (fn-rit-hasp x i node)
                  (if (and (stringp x) (natp i) (< i (length x)))
                      (fn-rit-hasp x (+ 1 i)
                                   (fn-midx-branch-get (char x i) node))
                    (if (fn-rit-bucket-find x (cdr (fn-midx-branch-get :end node))) t nil))))
  :hints (("Goal" :expand ((fn-rit-hasp x i node)))))

(defthm fn-rit-hasp-of-atom
  (implies (and (not (fn-rit-leafp node)) (not (fn-rit-branchp node)))
           (not (fn-rit-hasp x i node)))
  :hints (("Goal" :expand ((fn-rit-hasp x i node)))))

; A character key is never the bucket key, and holds no string.
(local
 (defthm fn-rit-nth-char-list
   (implies (character-listp l)
            (or (characterp (nth i l)) (equal (nth i l) nil)))
   :rule-classes nil))

(defthm fn-rit-char-type
  (or (characterp (char x i)) (equal (char x i) nil))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable char)
           :use ((:instance fn-rit-nth-char-list (l (coerce x 'list)))))))

(defthm fn-rit-char-not-end
  (not (equal (char x i) :end)))

(local
 (defthm fn-rit-hasp-of-lift
   (implies (and (stringp x) (fn-rit-leafp old) (natp i))
            (equal (fn-rit-hasp x i (fn-rit-lift old i))
                   (equal x (fn-rit-leaf-id old))))
   :hints (("Goal" :in-theory (disable fn-rit-hasp char)
            :cases ((< i (length x)))))))

(local
 (defthm fn-rit-branchp-of-branch-put
   (implies (fn-rit-branchp node)
            (fn-rit-branchp (fn-midx-branch-put k v node)))
   :hints (("Goal" :expand ((fn-midx-branch-put k v node))))))
(local
 (defthm fn-rit-bucket-find-of-put
   (implies (fn-rit-leafp new)
            (equal (fn-rit-bucket-find x (fn-rit-bucket-put new xs))
                   (if (equal x (fn-rit-leaf-id new))
                       new (fn-rit-bucket-find x xs))))))

(defthm fn-rit-hasp-of-put
  (implies (and (stringp x) (fn-rit-leafp new) (natp i))
           (iff (fn-rit-hasp x i (fn-rit-put new i node))
                (or (equal x (fn-rit-leaf-id new)) (fn-rit-hasp x i node))))
  :hints (("Goal" :induct (fn-rit-put new i node)
           :in-theory (disable fn-rit-lift fn-rit-hasp char length))))

(local
 (defthm fn-rit-member-of-append
   (iff (member-equal y (append a b))
        (or (member-equal y a) (member-equal y b)))))
(local
 (defthm fn-rit-strings-is-branches
   (implies (fn-rit-branchp a)
            (equal (fn-rit-strings a) (fn-rit-branches-strings a)))
   :hints (("Goal" :expand ((fn-rit-strings a) (fn-rit-branches-strings a))))))
(local
 (defthm fn-rit-strings-of-branch-get
   (implies (and (not (equal k :finds)) (not (equal k :end))
                 (not (member-equal y (fn-rit-branches-strings a))))
            (not (member-equal y (fn-rit-strings (fn-midx-branch-get k a)))))
   :hints (("Goal" :induct (fn-midx-branch-get k a)
            :in-theory (disable fn-rit-strings)))))
(local
 (defthm fn-rit-strings-of-end-get
   (implies (not (member-equal y (fn-rit-branches-strings a)))
            (not (member-equal y (fn-rit-leaves-strings
                                 (cdr (fn-midx-branch-get :end a))))))
   :hints (("Goal" :induct (fn-midx-branch-get :end a)
            :in-theory (disable fn-rit-strings)))))
(local
 (defthm fn-rit-strings-of-branch-put
   (implies (and (not (member-equal y (fn-rit-strings v)))
                 (not (equal k :end))
                 (not (member-equal y (fn-rit-branches-strings a))))
            (not (member-equal y (fn-rit-branches-strings
                                 (fn-midx-branch-put k v a)))))
   :hints (("Goal" :induct (fn-midx-branch-put k v a)
            :in-theory (disable fn-rit-strings)))))
(local
 (defthm fn-rit-strings-of-end-put
   (implies (and (not (member-equal y (fn-rit-leaves-strings (cdr v))))
                 (not (member-equal y (fn-rit-branches-strings a))))
            (not (member-equal y (fn-rit-branches-strings
                                 (fn-midx-branch-put :end v a)))))
   :hints (("Goal" :induct (fn-midx-branch-put :end v a)
            :in-theory (disable fn-rit-strings)))))
(local
 (defthm fn-rit-strings-when-member
   (implies (and (stringp y) (member-equal y l))
            (member-equal y (fn-rit-leaves-strings l)))))
(local
 (defthm fn-rit-strings-of-char
   (equal (fn-rit-strings (char x i)) nil)
   :hints (("Goal" :in-theory (disable char)))))
(local
 (defthm fn-rit-strings-of-lift
   (implies (and (fn-rit-leafp old) (not (equal y (fn-rit-leaf-id old))))
            (not (member-equal y (fn-rit-strings (fn-rit-lift old i)))))
   :hints (("Goal" :in-theory (disable char)))))
(local
 (defthm fn-rit-strings-of-bucket-put
   (implies (and (not (equal y (fn-rit-leaf-id new)))
                 (not (member-equal y (fn-rit-leaves-strings xs))))
            (not (member-equal y (fn-rit-leaves-strings
                                 (fn-rit-bucket-put new xs)))))))
(local
 (defthm fn-rit-strings-of-end-bucket-put
   (implies (and (not (equal y (fn-rit-leaf-id new)))
                 (not (member-equal y (fn-rit-branches-strings a))))
            (not (member-equal y
                   (fn-rit-branches-strings
                    (fn-midx-branch-put :end
                     (cons :end (fn-rit-bucket-put new
                                 (cdr (fn-midx-branch-get :end a)))) a)))))
   :hints (("Goal"
            :in-theory (union-theories '(cdr cdr-cons)
                                        (theory 'minimal-theory))
            :use ((:instance fn-rit-strings-of-end-get)
                  (:instance fn-rit-strings-of-bucket-put
                             (xs (cdr (fn-midx-branch-get :end a))))
                  (:instance fn-rit-strings-of-end-put
                             (v (cons :end (fn-rit-bucket-put new
                                    (cdr (fn-midx-branch-get :end a)))))))))))
(defthm fn-rit-strings-of-put
  (implies (and (fn-rit-leafp new)
                (not (equal y (fn-rit-leaf-id new)))
                (not (member-equal y (fn-rit-strings node))))
           (not (member-equal y (fn-rit-strings (fn-rit-put new i node)))))
  :hints (("Goal" :induct (fn-rit-put new i node)
           :in-theory (disable fn-rit-lift char fn-rit-branches-strings
                               fn-rit-leaves-strings fn-rit-bucket-put
                               fn-midx-branch-put fn-midx-branch-get))))
(local
 (defthm fn-rit-bucket-find-is-stored
   (implies (and (fn-rit-bucket-find x xs) (stringp x))
            (member-equal x (fn-rit-leaves-strings xs)))))
(local
 (defthm fn-rit-end-find-is-stored
   (implies (and (fn-rit-bucket-find x (cdr (fn-midx-branch-get :end a)))
                 (stringp x))
            (member-equal x (fn-rit-branches-strings a)))
   :hints (("Goal" :in-theory (theory 'minimal-theory)
            :use ((:instance fn-rit-strings-of-end-get (y x))
                  (:instance fn-rit-bucket-find-is-stored
                             (xs (cdr (fn-midx-branch-get :end a))))))))
)
(defthm fn-rit-hasp-is-stored
  (implies (and (fn-rit-hasp x i node) (stringp x))
           (member-equal x (fn-rit-strings node)))
  :hints (("Goal" :induct (fn-rit-get x i node)
           :in-theory (disable char fn-rit-branches-strings
                               fn-rit-leaves-strings fn-rit-bucket-find
                               fn-midx-branch-get))))
(in-theory (disable fn-rit-hasp fn-rit-get fn-rit-put fn-rit-lift))

; Value counterparts of the membership lemmas; no carry hypothesis.
(local
 (defthm fn-rit-get-of-leaf
   (implies (fn-rit-leafp node)
            (equal (fn-rit-get x i node)
                   (if (equal x (fn-rit-leaf-id node)) node nil)))
   :hints (("Goal" :expand ((fn-rit-get x i node))))))
(local
 (defthm fn-rit-get-of-branch
   (implies (fn-rit-branchp node)
            (equal (fn-rit-get x i node)
                   (if (and (stringp x) (natp i) (< i (length x)))
                       (fn-rit-get x (+ 1 i)
                                   (fn-midx-branch-get (char x i) node))
                     (fn-rit-bucket-find x (cdr (fn-midx-branch-get :end node))))))
   :hints (("Goal" :expand ((fn-rit-get x i node))))))
(local
 (defthm fn-rit-get-of-empty
   (implies (and (not (fn-rit-leafp node)) (not (fn-rit-branchp node)))
            (equal (fn-rit-get x i node) nil))
   :hints (("Goal" :expand ((fn-rit-get x i node))))))
(local
 (defthm fn-rit-get-of-lift
   (implies (and (stringp x) (fn-rit-leafp old) (natp i))
            (equal (fn-rit-get x i (fn-rit-lift old i))
                   (if (equal x (fn-rit-leaf-id old)) old nil)))
   :hints (("Goal" :in-theory (e/d (fn-rit-lift) (fn-rit-get char))
            :cases ((< i (length x)))))))
(defthm fn-rit-get-of-put
  (implies (and (stringp x) (fn-rit-leafp new) (natp i))
           (equal (fn-rit-get x i (fn-rit-put new i node))
                  (if (equal x (fn-rit-leaf-id new)) new
                    (fn-rit-get x i node))))
  :hints (("Goal" :induct (fn-rit-put new i node)
           :in-theory (e/d (fn-rit-put) (fn-rit-lift fn-rit-get char length)))))

; Root metadata is the first alist edge. Queries use only character/:end
; keys; enumeration deliberately ignores :finds. No metadata is a leaf.
(defun fn-prc-root (trie)
  (declare (xargs :guard t))
  (if (fn-rit-leafp trie) (fn-rit-lift trie 0)
    (if (fn-rit-branchp trie) trie nil)))
(defun fn-prc-mark (trie mark)
  (declare (xargs :guard t))
  (let ((root (fn-prc-root trie)))
    (cons (cons :finds (if mark t nil))
          (if (and (consp root) (consp (car root)) (eq (caar root) :finds))
              (cdr root) root))))
(defun fn-prc-carry-findsp (carry)
  (declare (xargs :guard t))
  (and (consp carry) (consp (cdr carry)) (consp (cadr carry))
       (eq (caadr carry) :finds) (eq (cdadr carry) t)))
(defthm fn-prc-mark-findsp
  (equal (fn-prc-carry-findsp (cons ledger (fn-prc-mark trie mark)))
         (if mark t nil)))
(local
 (defthm fn-rit-char-not-finds
   (not (equal (char x i) :finds))
   :hints (("Goal" :in-theory (disable char)))))
(defthm fn-rit-get-of-mark
  (implies (stringp id)
           (equal (fn-rit-get id 0 (fn-prc-mark trie mark))
                  (fn-rit-get id 0 trie)))
  :hints (("Goal" :in-theory (e/d (fn-rit-lift) (char fn-rit-get)))))
(defthm fn-rit-strings-of-mark
  (equal (fn-rit-strings (fn-prc-mark trie mark)) (fn-rit-strings trie))
  :hints (("Goal" :in-theory (e/d (fn-rit-lift) (char)))))

; The set operations the carry uses: an id is a string at depth 0.
(defun fn-prc-has (id trie)
  (declare (xargs :guard t))
  (and (stringp id) (fn-rit-hasp id 0 trie)))

(defun fn-prc-add (id trie)
  (declare (xargs :guard t))
  (if (and (stringp id) (not (fn-rit-hasp id 0 trie)))
      (fn-rit-put id 0 trie)
    trie))

(defthm fn-prc-has-of-add
  (implies (stringp x)
           (iff (fn-prc-has x (fn-prc-add id trie))
                (or (equal x id) (fn-prc-has x trie)))))

(defthm fn-prc-strings-of-add
  (implies (and (not (equal y id)) (not (member-equal y (fn-rit-strings trie))))
           (not (member-equal y (fn-rit-strings (fn-prc-add id trie))))))

(defthm fn-prc-has-is-stored
  (implies (fn-prc-has x trie)
           (and (stringp x) (member-equal x (fn-rit-strings trie)))))

(in-theory (disable fn-prc-has fn-prc-add))

; -----------------------------------------------------------------------------
; 2. The trie of a ledger (the rebuild), and the carry's recognizer.

; Guard-t readers never validate or scan the ledger on the marked path.
(defun fn-prc-find (id trie)
  (declare (xargs :guard t))
  (if (stringp id)
      (let ((leaf (fn-rit-get id 0 trie)))
        (if (consp leaf) leaf nil))
    nil))
(defun fn-prc-find-scan (id pins)
  (declare (xargs :guard t))
  (if (consp pins)
      (if (equal id (fn-retain-obligation-id (car pins)))
          (car pins)
        (fn-prc-find-scan id (cdr pins)))
    nil))
(defthm fn-prc-find-scan-is-find-id
  (equal (fn-prc-find-scan id pins) (fn-retain-find-id id pins)))
(local
 (defthm fn-prc-find-implies-has
   (implies (fn-prc-find id trie) (fn-prc-has id trie))
   :hints (("Goal" :in-theory (enable fn-prc-has fn-rit-hasp)))))
(defthm fn-prc-has-of-mark
  (equal (fn-prc-has id (fn-prc-mark trie mark)) (fn-prc-has id trie))
  :hints (("Goal" :in-theory (e/d (fn-prc-has fn-rit-hasp)
                                 (fn-prc-mark)))))
(defthm fn-prc-find-of-mark
  (equal (fn-prc-find id (fn-prc-mark trie mark)) (fn-prc-find id trie))
  :hints (("Goal" :in-theory (disable fn-prc-mark))))
(defun fn-prc-find-pin (id ledger carry)
  (declare (xargs :guard t))
  (if (and (consp carry) (equal (car carry) ledger)
           (fn-prc-carry-findsp carry))
      (fn-prc-find id (cdr carry))
    (fn-prc-find-scan id (fn-retain-pins ledger))))
(in-theory (disable fn-prc-mark fn-prc-root fn-prc-carry-findsp fn-prc-find-pin))

(defun fn-prc-add-pin (pin trie)
  (declare (xargs :guard t))
  (if (and (consp pin) (stringp (car pin))
           (not (fn-prc-find (car pin) trie)))
      (fn-rit-put pin 0 trie)
    trie))
(defthm fn-prc-has-of-add-pin
  (implies (stringp x)
           (iff (fn-prc-has x (fn-prc-add-pin pin trie))
                (or (equal x (fn-retain-obligation-id pin))
                    (fn-prc-has x trie))))
  :hints (("Goal" :use ((:instance fn-prc-find-implies-has (id (car pin))))
           :in-theory (e/d (fn-prc-has fn-retain-obligation-id)
                           (fn-prc-find)))))
(defthm fn-prc-strings-of-add-pin
  (implies (and (not (equal y (fn-retain-obligation-id pin)))
                (not (member-equal y (fn-rit-strings trie))))
           (not (member-equal y (fn-rit-strings (fn-prc-add-pin pin trie)))))
  :hints (("Goal" :in-theory (e/d (fn-retain-obligation-id)
                                 (fn-prc-find)))))
(in-theory (disable fn-prc-add-pin fn-prc-find))

(defun fn-prc-add-pins (pins trie)
  (declare (xargs :guard t))
  (if (consp pins)
      (fn-prc-add-pins (cdr pins)
                       (fn-prc-add-pin (car pins) trie))
    trie))

(defun fn-prc-add-releases (releases trie)
  (declare (xargs :guard t))
  (if (consp releases)
      (fn-prc-add-releases (cdr releases)
                           (fn-prc-add (fn-retain-release-id (car releases))
                                       trie))
    trie))

(defthm fn-prc-has-of-add-pins
  (implies (stringp x)
           (iff (fn-prc-has x (fn-prc-add-pins pins trie))
                (or (member-equal x (fn-retain-obligation-ids pins))
                    (fn-prc-has x trie)))))

(defthm fn-prc-strings-of-add-pins
  (implies (and (not (member-equal y (fn-retain-obligation-ids pins)))
                (not (member-equal y (fn-rit-strings trie))))
           (not (member-equal y (fn-rit-strings (fn-prc-add-pins pins trie))))))

(defthm fn-prc-has-of-add-releases
  (implies (stringp x)
           (iff (fn-prc-has x (fn-prc-add-releases releases trie))
                (or (member-equal x (fn-retain-release-ids releases))
                    (fn-prc-has x trie)))))

(defthm fn-prc-strings-of-add-releases
  (implies (and (not (member-equal y (fn-retain-release-ids releases)))
                (not (member-equal y (fn-rit-strings trie))))
           (not (member-equal y (fn-rit-strings (fn-prc-add-releases releases trie))))))

; Total ID collectors for mark construction; the model collectors have
; obligation-list guards and cannot run on arbitrary refresh inputs.
(defun fn-prc-pin-ids (pins)
  (declare (xargs :guard t))
  (if (consp pins)
      (cons (fn-retain-obligation-id (car pins)) (fn-prc-pin-ids (cdr pins)))
    nil))
(defun fn-prc-release-ids (releases)
  (declare (xargs :guard t))
  (if (consp releases)
      (cons (fn-retain-release-id (car releases)) (fn-prc-release-ids (cdr releases)))
    nil))
(defthm fn-prc-pin-ids-is-obligation-ids
  (equal (fn-prc-pin-ids pins) (fn-retain-obligation-ids pins)))
(defthm fn-prc-release-ids-is-release-ids
  (equal (fn-prc-release-ids releases) (fn-retain-release-ids releases)))
; RED 2/3: mark eligibility checks string pin IDs, uniqueness of both
; ID lists, and pin/release disjointness.
(defun fn-prc-ledger-findsp (ledger)
  (declare (xargs :guard t))
  (let ((pins (fn-prc-pin-ids (fn-retain-pins ledger)))
        (released (fn-prc-release-ids (fn-retain-releases ledger))))
    (and (fn-retain-string-listp pins)
         (fn-retain-no-duplicatesp pins)
         (fn-retain-no-duplicatesp released)
         (fn-retain-ids-disjointp pins released))))

(defun fn-prc-build (ledger)
  (declare (xargs :guard t))
  (fn-prc-mark
   (fn-prc-add-pins (fn-retain-pins ledger)
                    (fn-prc-add-releases (fn-retain-releases ledger) nil))
   (fn-prc-ledger-findsp ledger)))

(local (in-theory (disable fn-prc-find-scan-is-find-id)))
(defthm fn-prc-find-of-add-pin
  (equal (fn-prc-find x (fn-prc-add-pin pin trie))
         (if (and (stringp x) (equal x (fn-retain-obligation-id pin))
                  (not (fn-prc-find x trie)))
             pin
           (fn-prc-find x trie)))
  :hints (("Goal" :in-theory (enable fn-prc-add-pin fn-prc-find
                                    fn-retain-obligation-id))))
(defthm fn-prc-find-of-add
  (equal (fn-prc-find x (fn-prc-add id trie)) (fn-prc-find x trie))
  :hints (("Goal" :in-theory (enable fn-prc-add fn-prc-has fn-prc-find
                                    fn-rit-hasp))))
(defthm fn-prc-find-of-add-pins
  (equal (fn-prc-find x (fn-prc-add-pins pins trie))
         (if (fn-prc-find x trie)
             (fn-prc-find x trie)
           (if (stringp x) (fn-prc-find-scan x pins) nil)))
  :hints (("Goal" :induct (fn-prc-add-pins pins trie)
           :in-theory (disable fn-prc-find fn-prc-add-pin))))
(defthm fn-prc-find-of-add-releases
  (equal (fn-prc-find x (fn-prc-add-releases releases trie))
         (fn-prc-find x trie)))
(local
 (defthm fn-prc-find-of-nil
   (equal (fn-prc-find x nil) nil)
   :hints (("Goal" :in-theory (enable fn-prc-find fn-rit-get)))))
(local
 (defthm fn-prc-find-scan-non-string
   (implies (and (fn-retain-string-listp (fn-retain-obligation-ids pins))
                 (not (stringp x)))
            (equal (fn-prc-find-scan x pins) nil))
   :hints (("Goal" :induct (fn-prc-find-scan x pins)))))
(defthm fn-prc-find-of-build
  (implies (fn-prc-ledger-findsp ledger)
           (equal (fn-prc-find id (fn-prc-build ledger))
                  (fn-prc-find-scan id (fn-retain-pins ledger)))))

; The recognizer's halves.  Complete: every (string) id the ledger knows is
; in the trie.  Sound: every string stored in the trie is an id the ledger
; knows.  Each is a scan that returns its first counterexample (a witness
; the proofs instantiate), nil when there is none.
(defun fn-prc-pins-miss (pins trie)
  (declare (xargs :guard t))
  (if (consp pins)
      (let ((id (fn-retain-obligation-id (car pins))))
        (if (and (stringp id) (not (fn-prc-has id trie)))
            (list id)
          (fn-prc-pins-miss (cdr pins) trie)))
    nil))

(defun fn-prc-releases-miss (releases trie)
  (declare (xargs :guard t))
  (if (consp releases)
      (let ((id (fn-retain-release-id (car releases))))
        (if (and (stringp id) (not (fn-prc-has id trie)))
            (list id)
          (fn-prc-releases-miss (cdr releases) trie)))
    nil))

(defun fn-prc-unknown (strings ledger)
  (declare (xargs :guard t))
  (if (consp strings)
      (if (fn-rii-knownp (car strings) ledger)
          (fn-prc-unknown (cdr strings) ledger)
        (list (car strings)))
    nil))

(defun fn-prc-set-okp (ledger trie)
  (declare (xargs :guard t))
  (and (not (fn-prc-pins-miss (fn-retain-pins ledger) trie))
       (not (fn-prc-releases-miss (fn-retain-releases ledger) trie))
       (not (fn-prc-unknown (fn-rit-strings trie) ledger))))

(local
 (defthm fn-prc-pins-miss-when-member
   (implies (and (not (fn-prc-pins-miss pins trie))
                 (stringp x)
                 (member-equal x (fn-retain-obligation-ids pins)))
            (fn-prc-has x trie))))

(local
 (defthm fn-prc-pins-miss-witness
   (implies (fn-prc-pins-miss pins trie)
            (and (stringp (car (fn-prc-pins-miss pins trie)))
                 (member-equal (car (fn-prc-pins-miss pins trie))
                               (fn-retain-obligation-ids pins))
                 (not (fn-prc-has (car (fn-prc-pins-miss pins trie)) trie))))))

(local
 (defthm fn-prc-releases-miss-when-member
   (implies (and (not (fn-prc-releases-miss releases trie))
                 (stringp x)
                 (member-equal x (fn-retain-release-ids releases)))
            (fn-prc-has x trie))))

(local
 (defthm fn-prc-releases-miss-witness
   (implies (fn-prc-releases-miss releases trie)
            (and (stringp (car (fn-prc-releases-miss releases trie)))
                 (member-equal (car (fn-prc-releases-miss releases trie))
                               (fn-retain-release-ids releases))
                 (not (fn-prc-has (car (fn-prc-releases-miss releases trie))
                                  trie))))))

(local
 (defthm fn-prc-unknown-when-member
   (implies (and (not (fn-prc-unknown strings ledger))
                 (member-equal y strings))
            (fn-rii-knownp y ledger))
   :hints (("Goal" :in-theory (disable fn-rii-knownp-is-known-idp)))))

(local
 (defthm fn-prc-unknown-witness-member
   (implies (fn-prc-unknown strings ledger)
            (member-equal (car (fn-prc-unknown strings ledger)) strings))
   :hints (("Goal" :in-theory (disable fn-rii-knownp-is-known-idp)))))

(local
 (defthm fn-prc-unknown-witness-unknown
   (implies (fn-prc-unknown strings ledger)
            (not (fn-rii-knownp (car (fn-prc-unknown strings ledger))
                                ledger)))
   :hints (("Goal" :in-theory (disable fn-rii-knownp-is-known-idp)))))

(local
 (defthm fn-prc-unknown-witness
   (implies (fn-prc-unknown strings ledger)
            (and (member-equal (car (fn-prc-unknown strings ledger)) strings)
                 (not (fn-rii-knownp (car (fn-prc-unknown strings ledger))
                                     ledger))))
   :hints (("Goal" :in-theory (disable fn-rii-knownp-is-known-idp)))))

(local
 (defthm fn-prc-knownp-unfolds
   (iff (fn-rii-knownp id ledger)
        (or (member-equal id (fn-retain-obligation-ids (fn-retain-pins ledger)))
            (member-equal id (fn-retain-release-ids (fn-retain-releases ledger)))))
   :hints (("Goal" :in-theory (enable fn-retain-known-idp)
            :use fn-rii-knownp-is-known-idp))))

; What a reader uses: under the recognizer the trie answers, for every
; string, exactly whether the ledger knows it.
(defthm fn-prc-set-okp-is-knownp
  (implies (and (fn-prc-set-okp ledger trie) (stringp x))
           (iff (fn-prc-has x trie)
                (fn-rii-knownp x ledger)))
  :hints (("Goal" :in-theory (disable fn-prc-has-is-stored)
           :use ((:instance fn-prc-has-is-stored)
                 (:instance fn-prc-unknown-when-member
                            (y x) (strings (fn-rit-strings trie)))))))

(local
 (defun fn-rit-strings-induct (x)
   (declare (xargs :measure (acl2-count x)))
   (if (consp x)
       (list (fn-rit-strings-induct (cdr x))
             (if (consp (car x))
                 (list (fn-rit-strings-induct (cdar x))
                       (fn-rit-strings-induct (cdr (cdar x))))
               nil))
     nil)))
(local
 (defthm fn-rit-strings-all-strings
   (implies (not (stringp y))
            (and (not (member-equal y (fn-rit-strings x)))
                 (not (member-equal y (fn-rit-branches-strings x)))
                 (not (member-equal y (fn-rit-leaves-strings x)))))
   :hints (("Goal" :induct (fn-rit-strings-induct x)))))

(local
 (defthm fn-prc-strings-are-strings
   (implies (member-equal y (fn-rit-strings x)) (stringp y))))

(local
 (defthm fn-prc-build-is-known
   (implies (not (fn-rii-knownp y ledger))
            (not (member-equal y (fn-rit-strings (fn-prc-build ledger)))))))

(local
 (defthm fn-prc-build-has-known
   (implies (and (stringp x)
                 (or (member-equal x (fn-retain-obligation-ids
                                      (fn-retain-pins ledger)))
                     (member-equal x (fn-retain-release-ids
                                      (fn-retain-releases ledger)))))
            (fn-prc-has x (fn-prc-build ledger)))))

(defthm fn-prc-set-okp-of-build
  (fn-prc-set-okp ledger (fn-prc-build ledger))
  :hints (("Goal"
           :in-theory (disable fn-prc-pins-miss-witness fn-prc-releases-miss-witness
                               fn-prc-unknown-witness fn-prc-build
                               fn-prc-knownp-unfolds)
           :use ((:instance fn-prc-pins-miss-witness
                            (pins (fn-retain-pins ledger))
                            (trie (fn-prc-build ledger)))
                 (:instance fn-prc-releases-miss-witness
                            (releases (fn-retain-releases ledger))
                            (trie (fn-prc-build ledger)))
                 (:instance fn-prc-unknown-witness
                            (strings (fn-rit-strings (fn-prc-build ledger))))))))

(in-theory (disable fn-prc-set-okp))

(defun fn-prc-pins-fitp (pins trie)
  (declare (xargs :guard t))
  (if (consp pins)
      (let ((id (fn-retain-obligation-id (car pins))))
        (and (stringp id)
             (equal (fn-prc-find id trie) (car pins))
             (not (fn-ag-member id (fn-prc-pin-ids (cdr pins))))
             (fn-prc-pins-fitp (cdr pins) trie)))
    t))
; The two finite scans implement A3. Checking every stored ID also checks
; every stored record; release-only IDs add no constraint once pins agree.
(defun fn-prc-find-miss (ids pins trie)
  (declare (xargs :guard t))
  (if (consp ids)
      (if (equal (fn-prc-find (car ids) trie) (fn-prc-find-scan (car ids) pins))
          (fn-prc-find-miss (cdr ids) pins trie)
        (list (car ids)))
    nil))
; RED 3: release IDs are unique and no release is also a pin. Together
; with pins-fitp and find agreement, absence of a release's find means
; pin/release disjointness, including on deliberately forged carries.
(defun fn-prc-releases-fitp (releases trie)
  (declare (xargs :guard t))
  (if (consp releases)
      (let ((id (fn-retain-release-id (car releases))))
        (and (not (fn-prc-find id trie))
             (not (fn-ag-member id (fn-prc-release-ids (cdr releases))))
             (fn-prc-releases-fitp (cdr releases) trie)))
    t))
(defun fn-prc-find-okp (ledger trie)
  (declare (xargs :guard t))
  (and (fn-prc-pins-fitp (fn-retain-pins ledger) trie)
       (fn-prc-releases-fitp (fn-retain-releases ledger) trie)
       (not (fn-prc-find-miss (fn-prc-pin-ids (fn-retain-pins ledger))
                             (fn-retain-pins ledger) trie))
       (not (fn-prc-find-miss (fn-rit-strings trie)
                             (fn-retain-pins ledger) trie))))

(defun fn-prc-carryp (carry)
  (declare (xargs :guard t))
  (or (atom carry)
      (and (fn-prc-set-okp (car carry) (cdr carry))
           (implies (fn-prc-carry-findsp carry)
                    (fn-prc-find-okp (car carry) (cdr carry))))))

(defthm fn-prc-carryp-when-atom
  (implies (atom carry) (fn-prc-carryp carry)))



; -----------------------------------------------------------------------------
; 3. The refresh: the same ledger keeps the carry; a ledger reached from the
; carried one by retention steps (releases consed on the carried releases;
; pins = new pins and the carried pins less released ones) applies that
; delta; anything else (the first POST, a recovery) rebuilds.

; RELEASES1 is RELEASES0 under a prefix of new releases.
(defun fn-prc-releases-tailp (r1 r0)
  (declare (xargs :guard t))
  (cond ((equal r1 r0) t)
        ((atom r1) nil)
        (t (fn-prc-releases-tailp (cdr r1) r0))))

; A release replaces a record leaf, including when its id was already known.
(defun fn-prc-release-put (id trie)
  (declare (xargs :guard t))
  (if (stringp id) (fn-rit-put id 0 trie) trie))
(defthm fn-prc-has-of-release-put
  (implies (stringp x)
           (iff (fn-prc-has x (fn-prc-release-put id trie))
                (or (equal x id) (fn-prc-has x trie))))
  :hints (("Goal" :in-theory (enable fn-prc-has))))
(defthm fn-prc-strings-of-release-put
  (implies (and (not (equal y id)) (not (member-equal y (fn-rit-strings trie))))
           (not (member-equal y (fn-rit-strings (fn-prc-release-put id trie))))))
(in-theory (disable fn-prc-release-put))

; The ids of that prefix put into TRIE.
(defun fn-prc-add-new-releases (r1 r0 trie)
  (declare (xargs :guard t))
  (cond ((equal r1 r0) trie)
        ((atom r1) trie)
        (t (fn-prc-add-new-releases
            (cdr r1) r0 (fn-prc-release-put (fn-retain-release-id (car r1)) trie)))))

(defun fn-prc-new-release-idp (x r1 r0)
  (declare (xargs :guard t))
  (cond ((equal r1 r0) nil)
        ((atom r1) nil)
        (t (or (equal x (fn-retain-release-id (car r1)))
               (fn-prc-new-release-idp x (cdr r1) r0)))))

(defthm fn-prc-has-of-add-new-releases
  (implies (stringp x)
           (iff (fn-prc-has x (fn-prc-add-new-releases r1 r0 trie))
                (or (fn-prc-new-release-idp x r1 r0)
                    (fn-prc-has x trie))))
  :hints (("Goal" :induct (fn-prc-add-new-releases r1 r0 trie))))

(defthm fn-prc-strings-of-add-new-releases
  (implies (and (not (fn-prc-new-release-idp y r1 r0))
                (not (member-equal y (fn-rit-strings trie))))
           (not (member-equal y (fn-rit-strings (fn-prc-add-new-releases r1 r0 trie)))))
  :hints (("Goal" :induct (fn-prc-add-new-releases r1 r0 trie))))

(local
 (defthm fn-prc-new-release-idp-is-member
   (implies (fn-prc-new-release-idp x r1 r0)
            (member-equal x (fn-retain-release-ids r1)))))

(local
 (defthm fn-prc-releases-tailp-members
   (implies (fn-prc-releases-tailp r1 r0)
            (and (implies (member-equal x (fn-retain-release-ids r0))
                          (member-equal x (fn-retain-release-ids r1)))
                 (implies (member-equal x (fn-retain-release-ids r1))
                          (or (fn-prc-new-release-idp x r1 r0)
                              (member-equal x (fn-retain-release-ids r0))))))))

; Every carried pin's id is released (in RTRIE, the new releases' ids).
(defun fn-prc-all-released (p0 rtrie)
  (declare (xargs :guard t))
  (if (consp p0)
      (and (fn-prc-has (fn-retain-obligation-id (car p0)) rtrie)
           (fn-prc-all-released (cdr p0) rtrie))
    t))

(local
 (defthm fn-prc-release-known-strings
   (implies (and (fn-prc-find id trie)
                 (not (member-equal y (fn-rit-strings trie))))
            (not (member-equal y (fn-rit-strings (fn-prc-release-put id trie)))))
   :hints (("Goal" :use ((:instance fn-prc-find-implies-has)
                         (:instance fn-prc-has-is-stored (x id))
                         (:instance fn-prc-strings-of-release-put))
            :in-theory (theory 'minimal-theory)))))
(defthm fn-prc-find-of-release-put
  (equal (fn-prc-find x (fn-prc-release-put id trie))
         (if (equal x id) nil (fn-prc-find x trie)))
  :hints (("Goal" :in-theory (enable fn-prc-find fn-prc-release-put))))

; The pins walk: P1 against the carried P0.  A pin EQUAL to the carried
; head is carried; a carried head whose id was released is skipped; any
; other pin of P1 is new and its id is put.  After a skip or a put the rest
; is tried whole (EQUAL; one EQ test when P1's tail is P0's, which is how a
; commit's cons and a release's fn-retain-remove-id leave them), so a
; commit costs O(1) and a release O(position of the released pin), with no
; allocation but the put ids.  Returns (mv OK TRIE); not OK means the delta
; is not of this shape and the caller rebuilds.
(defun fn-prc-pins-walk (p1 p0 rtrie trie check)
  (declare (xargs :guard t :measure (+ (len p1) (len p0))))
  (cond ((and check (equal p1 p0)) (mv t trie))
        ((and (atom p1) (atom p0)) (mv t trie))
        ((and (consp p1) (consp p0) (equal (car p1) (car p0)))
         (fn-prc-pins-walk (cdr p1) (cdr p0) rtrie trie nil))
        ((and (consp p0)
              (fn-prc-has (fn-retain-obligation-id (car p0)) rtrie))
         (let ((id (fn-retain-obligation-id (car p0))))
           (if (and (consp (car p0))
                    (equal (fn-prc-find id trie) (car p0)))
               (fn-prc-pins-walk p1 (cdr p0) rtrie
                                 (fn-prc-release-put id trie) t)
             (mv nil trie))))
        ((consp p1)
         (let ((id (fn-retain-obligation-id (car p1))))
           (if (and (stringp id) (not (fn-prc-has id trie)))
               (fn-prc-pins-walk (cdr p1) p0 rtrie
                                 (fn-prc-add-pin (car p1) trie) t)
             (mv nil trie))))
        (t (mv nil trie))))

(local
 (defthm fn-prc-all-released-member
   (implies (and (fn-prc-all-released p0 rtrie)
                 (member-equal x (fn-retain-obligation-ids p0)))
            (fn-prc-has x rtrie))))

(defthm fn-prc-pins-walk-monotone
  (implies (fn-prc-has x trie)
           (fn-prc-has x (mv-nth 1 (fn-prc-pins-walk p1 p0 rtrie trie check)))))

(defthm fn-prc-pins-walk-strings
  (implies (and (not (member-equal y (fn-rit-strings trie)))
                (not (member-equal y (fn-retain-obligation-ids p1))))
           (not (member-equal y (fn-rit-strings
                            (mv-nth 1 (fn-prc-pins-walk p1 p0 rtrie trie check)))))))

(defthm fn-prc-pins-walk-covers-new
  (implies (and (mv-nth 0 (fn-prc-pins-walk p1 p0 rtrie trie check))
                (stringp x)
                (member-equal x (fn-retain-obligation-ids p1)))
           (or (member-equal x (fn-retain-obligation-ids p0))
               (fn-prc-has x (mv-nth 1 (fn-prc-pins-walk p1 p0 rtrie trie check))))))

(defthm fn-prc-pins-walk-keeps-or-releases
  (implies (and (mv-nth 0 (fn-prc-pins-walk p1 p0 rtrie trie check))
                (member-equal x (fn-retain-obligation-ids p0)))
           (or (member-equal x (fn-retain-obligation-ids p1))
               (fn-prc-has x rtrie))))

; Pin agreement also validates uniqueness of a marked carry. The mark is
; untrusted data when a caller supplies an arbitrary carry to a theorem.

(local
 (defthm fn-prc-fit-head-facts
   (implies (and (fn-prc-pins-fitp pins trie) (consp pins))
            (and (stringp (fn-retain-obligation-id (car pins)))
                 (consp (car pins))
                 (equal (fn-prc-find (fn-retain-obligation-id (car pins)) trie)
                        (car pins))
                 (not (member-equal (fn-retain-obligation-id (car pins))
                                    (fn-retain-obligation-ids (cdr pins))))
                 (fn-prc-pins-fitp (cdr pins) trie)))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable fn-retain-obligation-id)))))
(local
 (defthm fn-prc-fitp-when-atom
   (implies (atom pins) (fn-prc-pins-fitp pins trie))))
(local
 (defthm fn-prc-find-not-has
   (implies (not (fn-prc-has id trie))
            (equal (fn-prc-find id trie) nil))
   :hints (("Goal" :use fn-prc-find-implies-has))))
(local
 (defthm fn-prc-fit-member-has
   (implies (and (fn-prc-pins-fitp pins trie)
                 (member-equal x (fn-retain-obligation-ids pins)))
            (fn-prc-has x trie))
   :hints (("Goal" :induct (fn-prc-pins-fitp pins trie)
            :in-theory (enable fn-retain-obligation-id)))))
(local
 (defthm fn-prc-fit-of-fresh-pin
   (implies (and (fn-prc-pins-fitp pins trie)
                 (not (fn-prc-has (fn-retain-obligation-id pin) trie)))
            (fn-prc-pins-fitp pins (fn-prc-add-pin pin trie)))
   :hints (("Goal" :induct (fn-prc-pins-fitp pins trie)
            :in-theory (disable fn-prc-add-pin fn-prc-find)))))
(local
 (defthm fn-prc-fit-of-unmentioned-release
   (implies (and (fn-prc-pins-fitp pins trie)
                 (not (member-equal id (fn-retain-obligation-ids pins))))
            (fn-prc-pins-fitp pins (fn-prc-release-put id trie)))
   :hints (("Goal" :induct (fn-prc-pins-fitp pins trie)
            :in-theory (disable fn-prc-release-put fn-prc-find)))))
(local
 (defthm fn-prc-walk-keeps-unmentioned-record
   (implies (and (fn-prc-find x trie)
                 (not (member-equal x (fn-retain-obligation-ids p0))))
            (equal (fn-prc-find x (mv-nth 1 (fn-prc-pins-walk p1 p0 rtrie trie check)))
                   (fn-prc-find x trie)))
   :hints (("Goal" :induct (fn-prc-pins-walk p1 p0 rtrie trie check)
            :in-theory (disable fn-prc-find fn-prc-add-pin fn-prc-release-put)))))
(local
 (defthm fn-prc-walk-known-only-from-p0
   (implies (and (mv-nth 0 (fn-prc-pins-walk p1 p0 rtrie trie check))
                 (fn-prc-has x trie)
                 (not (member-equal x (fn-retain-obligation-ids p0))))
            (not (member-equal x (fn-retain-obligation-ids p1))))
   :hints (("Goal" :induct (fn-prc-pins-walk p1 p0 rtrie trie check)
            :in-theory (disable fn-prc-find fn-prc-add-pin fn-prc-release-put)))))
(local
 (defthm fn-prc-walk-no-extra-finds
   (implies (and (mv-nth 0 (fn-prc-pins-walk p1 p0 rtrie trie check))
                 (not (member-equal x (fn-retain-obligation-ids p1)))
                 (implies (fn-prc-find x trie)
                          (member-equal x (fn-retain-obligation-ids p0))))
            (not (fn-prc-find x
                   (mv-nth 1 (fn-prc-pins-walk p1 p0 rtrie trie check)))))
   :hints (("Goal" :induct (fn-prc-pins-walk p1 p0 rtrie trie check)
            :in-theory (disable fn-prc-find fn-prc-add-pin fn-prc-release-put)))))
(local
 (defthm fn-prc-fit-fresh-not-member
   (implies (and (fn-prc-pins-fitp pins trie) (not (fn-prc-has x trie)))
            (not (member-equal x (fn-retain-obligation-ids pins))))
   :hints (("Goal" :in-theory (theory 'minimal-theory)
            :use fn-prc-fit-member-has))))
(local
 (defthm fn-prc-fit-cons-after-walk
   (implies
    (and (consp p1) (consp (car p1))
         (stringp (fn-retain-obligation-id (car p1)))
         (equal (fn-prc-find (fn-retain-obligation-id (car p1)) trie) (car p1))
         (not (member-equal (fn-retain-obligation-id (car p1))
                           (fn-retain-obligation-ids p0)))
         (mv-nth 0 (fn-prc-pins-walk (cdr p1) p0 rtrie trie check))
         (fn-prc-pins-fitp (cdr p1)
                           (mv-nth 1 (fn-prc-pins-walk (cdr p1) p0 rtrie trie check))))
    (fn-prc-pins-fitp p1
                      (mv-nth 1 (fn-prc-pins-walk (cdr p1) p0 rtrie trie check))))
   :hints (("Goal"
            :expand ((fn-prc-pins-fitp p1
                      (mv-nth 1 (fn-prc-pins-walk (cdr p1) p0 rtrie trie check))))
            :in-theory (union-theories '(fn-ag-member fn-prc-pin-ids-is-obligation-ids)
                                       (theory 'minimal-theory))
            :use ((:instance fn-prc-find-implies-has
                             (id (fn-retain-obligation-id (car p1))))
                  (:instance fn-prc-walk-keeps-unmentioned-record
                             (x (fn-retain-obligation-id (car p1))) (p1 (cdr p1)))
                  (:instance fn-prc-walk-known-only-from-p0
                             (x (fn-retain-obligation-id (car p1))) (p1 (cdr p1))))))))
(local
 (defthm fn-prc-walk-preserves-fit
   (implies (and (fn-prc-pins-fitp p0 trie)
                 (mv-nth 0 (fn-prc-pins-walk p1 p0 rtrie trie check)))
            (fn-prc-pins-fitp p1
              (mv-nth 1 (fn-prc-pins-walk p1 p0 rtrie trie check))))
   :hints (("Goal" :induct (fn-prc-pins-walk p1 p0 rtrie trie check)
            :in-theory (disable fn-prc-find fn-prc-add-pin fn-prc-release-put
                                fn-prc-pins-fitp)))))

(local
 (defthm fn-prc-miss-with-unmentioned-head
   (implies (not (member-equal (fn-retain-obligation-id pin) ids))
            (equal (fn-prc-find-miss ids (cons pin pins) trie)
                   (fn-prc-find-miss ids pins trie)))
   :hints (("Goal" :induct (fn-prc-find-miss ids pins trie)
            :in-theory (disable fn-prc-find)))))
(local
 (defthm fn-prc-fit-from-miss
   (implies (and (fn-retain-string-listp (fn-retain-obligation-ids pins))
                 (fn-retain-no-duplicatesp (fn-retain-obligation-ids pins))
                 (not (fn-prc-find-miss (fn-retain-obligation-ids pins) pins trie)))
            (fn-prc-pins-fitp pins trie))
   :hints (("Goal" :induct (fn-prc-pins-fitp pins trie)
            :in-theory (disable fn-prc-find)))))
(local
 (defthm fn-prc-find-miss-of-build
   (implies (fn-prc-ledger-findsp ledger)
            (not (fn-prc-find-miss ids (fn-retain-pins ledger) (fn-prc-build ledger))))
   :hints (("Goal" :induct (fn-prc-find-miss ids (fn-retain-pins ledger)
                                          (fn-prc-build ledger))
            :in-theory (disable fn-prc-build fn-prc-find fn-prc-ledger-findsp)))))
(local
 (defthm fn-prc-scan-absent
   (implies (not (member-equal id (fn-retain-obligation-ids pins)))
            (not (fn-prc-find-scan id pins)))))
(local
 (defthm fn-prc-disjoint-member
   (implies (and (not (intersection-equal xs ys)) (member-equal x ys))
            (not (member-equal x xs)))))
(local
 (defthm fn-prc-disjoint-tail
   (implies (not (intersection-equal xs (cons y ys)))
            (not (intersection-equal xs ys)))))
(local
 (defthm fn-prc-releases-fit-of-build
   (implies (and (fn-prc-ledger-findsp ledger)
                 (fn-retain-no-duplicatesp (fn-retain-release-ids releases))
                 (not (intersection-equal
                       (fn-retain-obligation-ids (fn-retain-pins ledger))
                       (fn-retain-release-ids releases))))
            (fn-prc-releases-fitp releases (fn-prc-build ledger)))
   :hints (("Goal" :induct (fn-prc-releases-fitp releases (fn-prc-build ledger))
            :in-theory (disable fn-prc-build fn-prc-find fn-prc-ledger-findsp
                                fn-prc-find-scan)))))

(defthm fn-prc-find-okp-of-build
  (implies (fn-prc-ledger-findsp ledger)
           (fn-prc-find-okp ledger (fn-prc-build ledger)))
  :hints (("Goal" :in-theory (disable fn-prc-build fn-prc-pins-fitp fn-prc-find-miss)
           :use ((:instance fn-prc-fit-from-miss (pins (fn-retain-pins ledger))
                            (trie (fn-prc-build ledger)))))))

(local
 (defthm fn-prc-find-miss-when-member
   (implies (and (not (fn-prc-find-miss ids pins trie)) (member-equal id ids))
            (equal (fn-prc-find id trie) (fn-prc-find-scan id pins)))
   :hints (("Goal" :induct (fn-prc-find-miss ids pins trie)
            :in-theory (disable fn-prc-find fn-prc-find-scan)))))
(local
 (defthm fn-prc-find-scan-member
   (implies (fn-prc-find-scan id pins)
            (member-equal id (fn-retain-obligation-ids pins)))))
(local
 (defthm fn-prc-fit-scan-member
   (implies (fn-prc-pins-fitp pins trie)
            (iff (fn-prc-find-scan id pins)
                 (member-equal id (fn-retain-obligation-ids pins))))
   :hints (("Goal" :induct (fn-prc-pins-fitp pins trie)
            :in-theory (enable fn-retain-obligation-id)))))
(local
 (defthm fn-prc-fit-find-scan
   (implies (and (fn-prc-pins-fitp pins trie) (fn-prc-find-scan id pins))
            (equal (fn-prc-find id trie) (fn-prc-find-scan id pins)))
   :hints (("Goal" :induct (fn-prc-pins-fitp pins trie)
            :in-theory (disable fn-prc-find)))))
(local
 (defthm fn-prc-find-is-stored
   (implies (fn-prc-find id trie)
            (member-equal id (fn-rit-strings trie)))
   :hints (("Goal" :in-theory (theory 'minimal-theory)
            :use ((:instance fn-prc-find-implies-has)
                  (:instance fn-prc-has-is-stored (x id)))))))
(local
 (defthm fn-prc-find-okp-no-extras
   (implies (and (fn-prc-find-okp ledger trie) (fn-prc-find id trie))
            (member-equal id (fn-retain-obligation-ids (fn-retain-pins ledger))))
   :hints (("Goal" :in-theory (union-theories '(fn-prc-find-okp)
                                        (theory 'minimal-theory))
            :use ((:instance fn-prc-find-is-stored)
                  (:instance fn-prc-find-miss-when-member
                             (ids (fn-rit-strings trie)) (pins (fn-retain-pins ledger)))
                  (:instance fn-prc-find-scan-member
                             (pins (fn-retain-pins ledger))))))))
(local
 (defthm fn-prc-walk-find-correct
   (implies (and (fn-prc-pins-fitp p0 trie)
                 (mv-nth 0 (fn-prc-pins-walk p1 p0 rtrie trie check))
                 (implies (fn-prc-find id trie)
                          (member-equal id (fn-retain-obligation-ids p0))))
            (equal (fn-prc-find id
                     (mv-nth 1 (fn-prc-pins-walk p1 p0 rtrie trie check)))
                   (fn-prc-find-scan id p1)))
   :hints (("Goal" :in-theory (theory 'minimal-theory)
            :use ((:instance fn-prc-walk-preserves-fit)
                  (:instance fn-prc-walk-no-extra-finds (x id))
                  (:instance fn-prc-fit-find-scan (pins p1)
                             (trie (mv-nth 1 (fn-prc-pins-walk p1 p0 rtrie trie check))))
                  (:instance fn-prc-fit-scan-member (pins p1)
                             (trie (mv-nth 1 (fn-prc-pins-walk p1 p0 rtrie trie check)))))))))

; A new release must have named a pin before the walk and be cleared by
; the walk. Only a successful skipped-pin branch can clear such a record.
; Remove each checked ID from BEFORE so duplicate release IDs are rejected
; without scanning the unchanged release tail.
(defun fn-prc-new-releases-clearedp (r1 r0 before after)
  (declare (xargs :guard t))
  (cond ((equal r1 r0) t)
        ((atom r1) nil)
        (t (let ((id (fn-retain-release-id (car r1))))
             (and (fn-prc-find id before) (not (fn-prc-find id after))
                  (fn-prc-new-releases-clearedp (cdr r1) r0
                                                (fn-prc-release-put id before) after))))))
(defthm fn-prc-find-of-add-new-releases
  (equal (fn-prc-find id (fn-prc-add-new-releases r1 r0 trie))
         (if (fn-prc-new-release-idp id r1 r0) nil (fn-prc-find id trie)))
  :hints (("Goal" :induct (fn-prc-add-new-releases r1 r0 trie))))
(local
 (defthm fn-prc-cleared-release-not-found
   (implies (and (fn-prc-new-releases-clearedp r1 r0 before after)
                 (fn-prc-new-release-idp id r1 r0))
            (not (fn-prc-find id after)))
   :hints (("Goal" :induct (fn-prc-new-releases-clearedp r1 r0 before after)
            :in-theory (disable fn-prc-find)))))
(local
 (defthm fn-prc-find-of-cleared-releases
   (implies (fn-prc-new-releases-clearedp r1 r0 before trie)
            (equal (fn-prc-find id (fn-prc-add-new-releases r1 r0 trie))
                   (fn-prc-find id trie)))
   :hints (("Goal" :in-theory (disable fn-prc-add-new-releases
                                     fn-prc-new-releases-clearedp fn-prc-new-release-idp)))))
(local
 (defthm fn-prc-fit-of-cleared-releases
   (implies (and (fn-prc-pins-fitp pins trie)
                 (fn-prc-new-releases-clearedp r1 r0 before trie))
            (fn-prc-pins-fitp pins (fn-prc-add-new-releases r1 r0 trie)))
   :hints (("Goal" :induct (fn-prc-pins-fitp pins trie)
            :in-theory (disable fn-prc-add-new-releases fn-prc-new-releases-clearedp
                                fn-prc-find-of-add-new-releases fn-prc-find)))))
(local
 (defthm fn-prc-fit-of-mark
   (equal (fn-prc-pins-fitp pins (fn-prc-mark trie mark))
          (fn-prc-pins-fitp pins trie))
   :hints (("Goal" :induct (fn-prc-pins-fitp pins trie)
            :in-theory (disable fn-prc-mark fn-prc-find)))))
(local
 (defthm fn-prc-find-miss-of-mark
   (equal (fn-prc-find-miss ids pins (fn-prc-mark trie mark))
          (fn-prc-find-miss ids pins trie))
   :hints (("Goal" :induct (fn-prc-find-miss ids pins trie)
            :in-theory (disable fn-prc-mark fn-prc-find fn-prc-find-scan)))))
(local
 (defthm fn-prc-releases-fit-of-mark
   (equal (fn-prc-releases-fitp releases (fn-prc-mark trie mark))
          (fn-prc-releases-fitp releases trie))
   :hints (("Goal" :induct (fn-prc-releases-fitp releases trie)
            :in-theory (disable fn-prc-mark fn-prc-find)))))
(defthm fn-prc-find-okp-of-mark
  (equal (fn-prc-find-okp ledger (fn-prc-mark trie mark))
         (fn-prc-find-okp ledger trie))
  :hints (("Goal" :in-theory (disable fn-prc-pins-fitp fn-prc-find-miss fn-prc-mark))))
(local
 (defthm fn-prc-walk-find-correct-from-okp
   (implies (and (fn-prc-find-okp l0 trie)
                 (mv-nth 0 (fn-prc-pins-walk p1 (fn-retain-pins l0) rtrie trie check)))
            (equal (fn-prc-find id
                    (mv-nth 1 (fn-prc-pins-walk p1 (fn-retain-pins l0) rtrie trie check)))
                   (fn-prc-find-scan id p1)))
   :hints (("Goal" :in-theory (union-theories '(fn-prc-find-okp)
                                             (theory 'minimal-theory))
            :use ((:instance fn-prc-walk-find-correct (p0 (fn-retain-pins l0)))
                  (:instance fn-prc-find-okp-no-extras (ledger l0)))))))
(local
 (defthm fn-prc-find-miss-of-walk
   (implies (and (fn-prc-find-okp l0 trie)
                 (mv-nth 0 (fn-prc-pins-walk p1 (fn-retain-pins l0) rtrie trie check)))
            (not (fn-prc-find-miss ids p1
                  (mv-nth 1 (fn-prc-pins-walk p1 (fn-retain-pins l0) rtrie trie check)))))
   :hints (("Goal" :induct (fn-prc-find-miss ids p1
                            (mv-nth 1 (fn-prc-pins-walk p1 (fn-retain-pins l0)
                                                      rtrie trie check)))
            :in-theory (disable fn-prc-pins-walk fn-prc-pins-fitp fn-prc-find
                                fn-prc-find-scan fn-prc-find-okp mv-nth)))))
(local
 (defthm fn-prc-find-miss-of-cleared-releases
   (implies (fn-prc-new-releases-clearedp r1 r0 before trie)
            (equal (fn-prc-find-miss ids pins (fn-prc-add-new-releases r1 r0 trie))
                   (fn-prc-find-miss ids pins trie)))
   :hints (("Goal" :induct (fn-prc-find-miss ids pins trie)
            :in-theory (disable fn-prc-add-new-releases fn-prc-new-releases-clearedp
                                fn-prc-find-of-add-new-releases fn-prc-find fn-prc-find-scan)))))

(local
 (defthm fn-prc-mark-of-branch-put
   (implies (not (equal key :finds))
            (equal (fn-prc-carry-findsp (cons ledger (fn-midx-branch-put key value node)))
                   (fn-prc-carry-findsp (cons ledger node))))
   :hints (("Goal" :in-theory (enable fn-prc-carry-findsp fn-midx-branch-put)
            :expand ((fn-midx-branch-put key value node))))))
(local
 (defthm fn-prc-mark-of-lift
   (not (fn-prc-carry-findsp (cons ledger (fn-rit-lift leaf i))))
   :hints (("Goal" :in-theory (e/d (fn-prc-carry-findsp fn-rit-lift) (char))))))
(local
 (defthm fn-prc-mark-of-put
   (implies (fn-rit-leafp new)
            (equal (fn-prc-carry-findsp (cons ledger (fn-rit-put new i node)))
                   (fn-prc-carry-findsp (cons ledger node))))
   :hints (("Goal" :induct (fn-rit-put new i node)
            :in-theory (e/d (fn-rit-put fn-prc-carry-findsp)
                            (fn-rit-lift char fn-midx-branch-put)) ))))
(local
 (defthm fn-prc-mark-of-add-pin
   (equal (fn-prc-carry-findsp (cons ledger (fn-prc-add-pin pin trie)))
          (fn-prc-carry-findsp (cons ledger trie)))
   :hints (("Goal" :in-theory (enable fn-prc-add-pin)))))
(local
 (defthm fn-prc-mark-of-release-put
   (equal (fn-prc-carry-findsp (cons ledger (fn-prc-release-put id trie)))
          (fn-prc-carry-findsp (cons ledger trie)))
   :hints (("Goal" :in-theory (enable fn-prc-release-put)))))
(local
 (defthm fn-prc-mark-of-walk
   (equal (fn-prc-carry-findsp
           (cons ledger (mv-nth 1 (fn-prc-pins-walk p1 p0 rtrie trie check))))
          (fn-prc-carry-findsp (cons ledger trie)))
   :hints (("Goal" :induct (fn-prc-pins-walk p1 p0 rtrie trie check)
            :in-theory (disable fn-prc-carry-findsp)))))
(local
 (defthm fn-prc-mark-of-add-new-releases
   (equal (fn-prc-carry-findsp (cons ledger (fn-prc-add-new-releases r1 r0 trie)))
          (fn-prc-carry-findsp (cons ledger trie)))
   :hints (("Goal" :induct (fn-prc-add-new-releases r1 r0 trie)
            :in-theory (disable fn-prc-carry-findsp)))))

(defun fn-prc-delta (carry ledger)
  (declare (xargs :guard (consp carry)))
  (let* ((l0 (car carry))
         (r0 (fn-retain-releases l0))
         (r1 (fn-retain-releases ledger)))
    (if (and (fn-prc-carry-findsp carry) (fn-prc-releases-tailp r1 r0))
        (mv-let (ok trie)
          (fn-prc-pins-walk (fn-retain-pins ledger) (fn-retain-pins l0)
                            (fn-prc-add-new-releases r1 r0 nil)
                            (cdr carry) t)
          (if (and ok (fn-prc-new-releases-clearedp r1 r0 (cdr carry) trie))
              (mv t (fn-prc-add-new-releases r1 r0 trie))
            (mv nil nil)))
      (mv nil nil))))

(defun fn-prc-refresh (carry ledger)
  (declare (xargs :guard t))
  (if (and (consp carry) (equal (car carry) ledger))
      carry
    (mv-let (ok trie)
      (if (consp carry) (fn-prc-delta carry ledger) (mv nil nil))
      (if ok
          (cons ledger trie)
        (cons ledger (fn-prc-build ledger))))))

;; The delta's trie, in the carried ledger L0's and the new ledger L1's
;; terms, and what the three halves of the recognizer need of it.
(defmacro fn-prc-delta-trie (l1 l0 trie)
  `(fn-prc-add-new-releases
    (fn-retain-releases ,l1) (fn-retain-releases ,l0)
    (mv-nth 1 (fn-prc-pins-walk (fn-retain-pins ,l1) (fn-retain-pins ,l0)
                                (fn-prc-add-new-releases
                                 (fn-retain-releases ,l1)
                                 (fn-retain-releases ,l0) nil)
                                ,trie t))))

(defmacro fn-prc-delta-okp (l1 l0 trie)
  `(and (fn-prc-releases-tailp (fn-retain-releases ,l1) (fn-retain-releases ,l0))
        (mv-nth 0 (fn-prc-pins-walk (fn-retain-pins ,l1) (fn-retain-pins ,l0)
                                    (fn-prc-add-new-releases
                                     (fn-retain-releases ,l1)
                                     (fn-retain-releases ,l0) nil)
                                    ,trie t))))

(local
 (defthm fn-prc-has-of-nil
   (not (fn-prc-has x nil))
   :hints (("Goal" :in-theory (enable fn-prc-has)))))

(local
 (defthm fn-prc-delta-sound
   (implies (and (fn-prc-delta-okp l1 l0 trie)
                 (not (fn-prc-unknown (fn-rit-strings trie) l0))
                 (member-equal y (fn-rit-strings (fn-prc-delta-trie l1 l0 trie))))
            (fn-rii-knownp y l1))
   :rule-classes nil
   :hints (("Goal"
            :in-theory (theory 'minimal-theory)
            :use ((:instance fn-prc-strings-of-add-new-releases
                             (r1 (fn-retain-releases l1)) (r0 (fn-retain-releases l0))
                             (trie (mv-nth 1 (fn-prc-pins-walk
                                              (fn-retain-pins l1) (fn-retain-pins l0)
                                              (fn-prc-add-new-releases
                                               (fn-retain-releases l1)
                                               (fn-retain-releases l0) nil)
                                              trie t))))
                  (:instance fn-prc-new-release-idp-is-member
                             (x y) (r1 (fn-retain-releases l1))
                             (r0 (fn-retain-releases l0)))
                  (:instance fn-prc-pins-walk-strings
                             (p1 (fn-retain-pins l1)) (p0 (fn-retain-pins l0))
                             (rtrie (fn-prc-add-new-releases
                                     (fn-retain-releases l1)
                                     (fn-retain-releases l0) nil))
                             (check t))
                  (:instance fn-prc-unknown-when-member
                             (strings (fn-rit-strings trie)) (ledger l0))
                  (:instance fn-prc-knownp-unfolds (id y) (ledger l0))
                  (:instance fn-prc-knownp-unfolds (id y) (ledger l1))
                  (:instance fn-prc-pins-walk-keeps-or-releases
                             (x y)
                             (p1 (fn-retain-pins l1)) (p0 (fn-retain-pins l0))
                             (rtrie (fn-prc-add-new-releases
                                     (fn-retain-releases l1)
                                     (fn-retain-releases l0) nil))
                             (check t))
                  (:instance fn-prc-has-of-add-new-releases
                             (x y) (r1 (fn-retain-releases l1))
                             (r0 (fn-retain-releases l0)) (trie nil))
                  (:instance fn-prc-has-of-nil (x y))
                  (:instance fn-prc-releases-tailp-members
                             (x y) (r1 (fn-retain-releases l1))
                             (r0 (fn-retain-releases l0)))
                  (:instance fn-prc-strings-are-strings
                             (x (fn-prc-delta-trie l1 l0 trie))))))))

(local
 (defthm fn-prc-delta-complete
   (implies (and (fn-prc-delta-okp l1 l0 trie)
                 (not (fn-prc-pins-miss (fn-retain-pins l0) trie))
                 (not (fn-prc-releases-miss (fn-retain-releases l0) trie))
                 (stringp x)
                 (or (member-equal x (fn-retain-obligation-ids (fn-retain-pins l1)))
                     (member-equal x (fn-retain-release-ids (fn-retain-releases l1)))))
            (fn-prc-has x (fn-prc-delta-trie l1 l0 trie)))
   :rule-classes nil
   :hints (("Goal"
            :in-theory (theory 'minimal-theory)
            :use ((:instance fn-prc-pins-walk-covers-new
                             (p1 (fn-retain-pins l1)) (p0 (fn-retain-pins l0))
                             (rtrie (fn-prc-add-new-releases
                                     (fn-retain-releases l1)
                                     (fn-retain-releases l0) nil))
                             (check t))
                  (:instance fn-prc-pins-miss-when-member
                             (pins (fn-retain-pins l0)))
                  (:instance fn-prc-releases-miss-when-member
                             (releases (fn-retain-releases l0)))
                  (:instance fn-prc-pins-walk-monotone
                             (p1 (fn-retain-pins l1)) (p0 (fn-retain-pins l0))
                             (rtrie (fn-prc-add-new-releases
                                     (fn-retain-releases l1)
                                     (fn-retain-releases l0) nil))
                             (check t))
                  (:instance fn-prc-has-of-add-new-releases
                             (r1 (fn-retain-releases l1)) (r0 (fn-retain-releases l0))
                             (trie (mv-nth 1 (fn-prc-pins-walk
                                              (fn-retain-pins l1) (fn-retain-pins l0)
                                              (fn-prc-add-new-releases
                                               (fn-retain-releases l1)
                                               (fn-retain-releases l0) nil)
                                              trie t))))
                  (:instance fn-prc-releases-tailp-members
                             (r1 (fn-retain-releases l1))
                             (r0 (fn-retain-releases l0))))))))

; The delta keeps the recognizer: its trie is the carried one with the new
; pins' and new releases' ids put, and every carried id is still known
; (carried, or released).
(defthm fn-prc-set-okp-of-delta
  (implies (and (consp carry)
                (fn-prc-set-okp (car carry) (cdr carry))
                (mv-nth 0 (fn-prc-delta carry ledger)))
           (fn-prc-set-okp ledger (mv-nth 1 (fn-prc-delta carry ledger))))
  :hints (("Goal"
           :in-theory (e/d (fn-prc-set-okp)
                           (fn-prc-pins-miss-witness fn-prc-releases-miss-witness
                            fn-prc-unknown-witness fn-prc-pins-walk
                            fn-prc-add-new-releases fn-prc-releases-tailp
                            fn-prc-pins-miss fn-prc-releases-miss
                            fn-prc-unknown))
           :use ((:instance fn-prc-pins-miss-witness
                            (pins (fn-retain-pins ledger))
                            (trie (fn-prc-delta-trie ledger (car carry) (cdr carry))))
                 (:instance fn-prc-releases-miss-witness
                            (releases (fn-retain-releases ledger))
                            (trie (fn-prc-delta-trie ledger (car carry) (cdr carry))))
                 (:instance fn-prc-unknown-witness
                            (strings (fn-rit-strings
                                      (fn-prc-delta-trie ledger (car carry)
                                                         (cdr carry))))
                            (ledger ledger))
                 (:instance fn-prc-delta-complete
                            (l1 ledger) (l0 (car carry)) (trie (cdr carry))
                            (x (car (fn-prc-pins-miss
                                     (fn-retain-pins ledger)
                                     (fn-prc-delta-trie ledger (car carry)
                                                        (cdr carry))))))
                 (:instance fn-prc-delta-complete
                            (l1 ledger) (l0 (car carry)) (trie (cdr carry))
                            (x (car (fn-prc-releases-miss
                                     (fn-retain-releases ledger)
                                     (fn-prc-delta-trie ledger (car carry)
                                                        (cdr carry))))))
                 (:instance fn-prc-delta-sound
                            (l1 ledger) (l0 (car carry)) (trie (cdr carry))
                            (y (car (fn-prc-unknown
                                     (fn-rit-strings
                                      (fn-prc-delta-trie ledger (car carry)
                                                         (cdr carry)))
                                     ledger))))))))

(defthm fn-prc-delta-requires-mark
  (implies (mv-nth 0 (fn-prc-delta carry ledger))
           (fn-prc-carry-findsp carry))
  :hints (("Goal" :in-theory (disable fn-prc-pins-walk fn-prc-add-new-releases
                                     fn-prc-new-releases-clearedp))))
(defthm fn-prc-build-findsp
  (equal (fn-prc-carry-findsp (cons l0 (fn-prc-build ledger)))
         (fn-prc-ledger-findsp ledger))
  :hints (("Goal" :in-theory (disable fn-prc-ledger-findsp))))
(defthm fn-prc-carryp-of-build
  (fn-prc-carryp (cons ledger (fn-prc-build ledger)))
  :hints (("Goal" :in-theory (disable fn-prc-build fn-prc-find-okp
                                     fn-prc-set-okp fn-prc-ledger-findsp))))
(local
 (defthm fn-prc-releases-fit-member
   (implies (and (fn-prc-releases-fitp releases trie)
                 (member-equal id (fn-retain-release-ids releases)))
            (not (fn-prc-find id trie)))
   :hints (("Goal" :induct (fn-prc-releases-fitp releases trie)
            :in-theory (disable fn-prc-find)))))
(local
 (defthm fn-prc-releases-fit-of-release-put
   (implies (fn-prc-releases-fitp releases trie)
            (fn-prc-releases-fitp releases (fn-prc-release-put id trie)))
   :hints (("Goal" :induct (fn-prc-releases-fitp releases trie)
            :in-theory (disable fn-prc-find fn-prc-release-put)))))
(local
 (defthm fn-prc-cleared-absent
   (implies (and (fn-prc-new-releases-clearedp r1 r0 before after)
                 (not (fn-prc-find id before))
                 (not (member-equal id (fn-retain-release-ids r0))))
            (not (member-equal id (fn-retain-release-ids r1))))
   :hints (("Goal" :induct (fn-prc-new-releases-clearedp r1 r0 before after)
            :in-theory (disable fn-prc-find fn-prc-release-put)))))
(local
 (defthm fn-prc-cleared-head-unique
   (implies (and (fn-prc-new-releases-clearedp rest r0
                         (fn-prc-release-put id before) after)
                 (fn-prc-releases-fitp r0 before)
                 (fn-prc-find id before))
            (not (member-equal id (fn-retain-release-ids rest))))
   :hints (("Goal" :in-theory (union-theories '(fn-prc-find-of-release-put)
                                               (theory 'minimal-theory))
            :use ((:instance fn-prc-cleared-absent (r1 rest)
                             (before (fn-prc-release-put id before)))
                  (:instance fn-prc-releases-fit-member (releases r0) (trie before)))))))
(local
 (defthm fn-prc-releases-fit-of-cleared
   (implies (and (fn-prc-new-releases-clearedp r1 r0 before after)
                 (fn-prc-releases-fitp r0 before)
                 (fn-prc-releases-fitp r0 after))
            (fn-prc-releases-fitp r1 after))
   :hints (("Goal" :induct (fn-prc-new-releases-clearedp r1 r0 before after)
            :in-theory (disable fn-prc-find fn-prc-release-put)))))
(local
 (defthm fn-prc-releases-fit-of-add-new-releases
   (implies (fn-prc-releases-fitp releases trie)
            (fn-prc-releases-fitp releases (fn-prc-add-new-releases r1 r0 trie)))
   :hints (("Goal" :induct (fn-prc-add-new-releases r1 r0 trie)
            :in-theory (disable fn-prc-releases-fitp fn-prc-release-put)))))
(local
 (defthm fn-prc-walk-keeps-known-absent
   (implies (and (not (fn-prc-find id trie))
                 (or (not (stringp id)) (fn-prc-has id trie)))
            (not (fn-prc-find id
                   (mv-nth 1 (fn-prc-pins-walk p1 p0 rtrie trie check)))))
   :hints (("Goal" :induct (fn-prc-pins-walk p1 p0 rtrie trie check)
            :in-theory (disable fn-prc-find fn-prc-add-pin fn-prc-release-put)))))
(local
 (defthm fn-prc-releases-fit-of-walk
   (implies (and (fn-prc-releases-fitp releases trie)
                 (not (fn-prc-releases-miss releases trie)))
            (fn-prc-releases-fitp releases
             (mv-nth 1 (fn-prc-pins-walk p1 p0 rtrie trie check))))
   :hints (("Goal" :induct (fn-prc-releases-fitp releases trie)
            :in-theory (disable fn-prc-pins-walk fn-prc-find mv-nth)))))

(defthm fn-prc-find-okp-of-delta
  (implies (and (consp carry)
                (fn-prc-find-okp (car carry) (cdr carry))
                (fn-prc-set-okp (car carry) (cdr carry))
                (mv-nth 0 (fn-prc-delta carry ledger)))
           (fn-prc-find-okp ledger (mv-nth 1 (fn-prc-delta carry ledger))))
  :hints (("Goal"
           :in-theory (e/d (fn-prc-delta fn-prc-find-okp fn-prc-set-okp)
                           (fn-prc-pins-walk fn-prc-add-new-releases fn-prc-find-miss
                            fn-prc-pins-fitp fn-prc-new-releases-clearedp
                            fn-prc-find-of-add-new-releases fn-retain-obligation-ids
                            fn-prc-find fn-prc-find-scan fn-prc-find-miss-of-walk))
           :use ((:instance fn-prc-find-miss-of-walk
                            (l0 (car carry)) (trie (cdr carry))
                            (p1 (fn-retain-pins ledger))
                            (rtrie (fn-prc-add-new-releases (fn-retain-releases ledger)
                                                          (fn-retain-releases (car carry)) nil))
                            (check t) (ids (fn-retain-obligation-ids (fn-retain-pins ledger))))
                 (:instance fn-prc-find-miss-of-walk
                            (l0 (car carry)) (trie (cdr carry))
                            (p1 (fn-retain-pins ledger))
                            (rtrie (fn-prc-add-new-releases (fn-retain-releases ledger)
                                                          (fn-retain-releases (car carry)) nil))
                            (check t)
                            (ids (fn-rit-strings
                                  (fn-prc-delta-trie ledger (car carry) (cdr carry)))))))))
(defthm fn-prc-carryp-of-delta
  (implies (and (consp carry) (fn-prc-carryp carry)
                (mv-nth 0 (fn-prc-delta carry ledger)))
           (fn-prc-carryp (cons ledger (mv-nth 1 (fn-prc-delta carry ledger)))))
  :hints (("Goal" :in-theory (e/d (fn-prc-carryp)
                                 (fn-prc-set-okp fn-prc-find-okp fn-prc-delta))
           :use ((:instance fn-prc-find-okp-of-delta)
                 (:instance fn-prc-set-okp-of-delta)
                 (:instance fn-prc-delta-requires-mark)))))

(local
 (defthm fn-prc-fit-pin-ids
   (implies (fn-prc-pins-fitp pins trie)
            (and (fn-retain-string-listp (fn-retain-obligation-ids pins))
                 (fn-retain-no-duplicatesp (fn-retain-obligation-ids pins))))
   :hints (("Goal" :induct (fn-prc-pins-fitp pins trie)
            :in-theory (disable fn-prc-find)))))
(local
 (defthm fn-prc-fit-release-ids
   (implies (fn-prc-releases-fitp releases trie)
            (fn-retain-no-duplicatesp (fn-retain-release-ids releases)))
   :hints (("Goal" :induct (fn-prc-releases-fitp releases trie)
            :in-theory (disable fn-prc-find)))))
(local
 (defthm fn-prc-fit-ids-disjoint
   (implies (and (fn-prc-pins-fitp pins trie)
                 (fn-prc-releases-fitp releases trie))
            (not (intersection-equal (fn-retain-obligation-ids pins)
                                     (fn-retain-release-ids releases))))
   :hints (("Goal" :induct (fn-prc-pins-fitp pins trie)
            :in-theory (disable fn-prc-releases-fitp fn-prc-find)))))
; Explicitly connect the executable fit checks to RED 3's four conditions.
(defthm fn-prc-find-okp-implies-ledger-findsp
  (implies (fn-prc-find-okp ledger trie) (fn-prc-ledger-findsp ledger))
  :hints (("Goal" :in-theory (disable fn-prc-pins-fitp fn-prc-releases-fitp
                                     fn-prc-find-miss))))

(defthm fn-prc-carryp-of-refresh
  (implies (fn-prc-carryp carry)
           (fn-prc-carryp (fn-prc-refresh carry ledger)))
  :hints (("Goal" :in-theory (disable fn-prc-delta fn-prc-set-okp fn-prc-build
                                     fn-prc-carryp fn-prc-find-okp mv-nth))))

(local
 (defthm fn-prc-find-okp-is-find-scan
   (implies (fn-prc-find-okp ledger trie)
            (equal (fn-prc-find id trie)
                   (fn-prc-find-scan id (fn-retain-pins ledger))))
   :hints (("Goal" :in-theory (union-theories '(fn-prc-find-okp)
                                              (theory 'minimal-theory))
            :use ((:instance fn-prc-find-okp-no-extras)
                  (:instance fn-prc-fit-find-scan (pins (fn-retain-pins ledger)))
                  (:instance fn-prc-fit-scan-member (pins (fn-retain-pins ledger))))))))

(defthm fn-prc-find-pin-is-find-id
    (implies (fn-prc-carryp carry)
             (equal (fn-prc-find-pin id ledger carry)
                    (fn-retain-find-id id (fn-retain-pins ledger))))
    :hints (("Goal" :in-theory
             (e/d (fn-prc-find-pin fn-prc-carryp fn-prc-find-scan-is-find-id)
                  (fn-prc-find fn-prc-find-scan fn-prc-find-okp fn-prc-set-okp)))))

(defthm fn-prc-find-pin-of-refresh-is-find-id
  (implies (fn-prc-carryp carry)
           (equal (fn-prc-find-pin id ledger (fn-prc-refresh carry ledger))
                  (fn-retain-find-id id (fn-retain-pins ledger))))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use ((:instance fn-prc-carryp-of-refresh)
                 (:instance fn-prc-find-pin-is-find-id
                            (carry (fn-prc-refresh carry ledger)))))))

(local
 (defthm fn-prc-obligation-ids-are-strings
   (implies (fn-retain-obligation-listp pins)
            (fn-retain-string-listp (fn-retain-obligation-ids pins)))
   :hints (("Goal" :in-theory (enable fn-retain-obligationp
                                     fn-retain-obligation-listp)))))
(local
 (defthm fn-prc-statep-implies-ledger-findsp
   (implies (fn-retain-statep ledger) (fn-prc-ledger-findsp ledger))
   :hints (("Goal" :in-theory (enable fn-retain-statep fn-prc-ledger-findsp)))))
(local
 (defthm fn-prc-mark-ignores-ledger-name
   (equal (fn-prc-carry-findsp (cons ledger (cdr carry)))
          (fn-prc-carry-findsp carry))
   :hints (("Goal" :in-theory (enable fn-prc-carry-findsp)))))
(local
 (defthm fn-prc-delta-preserves-mark
   (implies (mv-nth 0 (fn-prc-delta carry ledger))
            (fn-prc-carry-findsp (cons ledger (mv-nth 1 (fn-prc-delta carry ledger)))))
   :hints (("Goal" :in-theory
            (e/d (fn-prc-delta)
                 (fn-prc-carry-findsp fn-prc-pins-walk fn-prc-add-new-releases
                  fn-prc-new-releases-clearedp mv-nth))))))
(defthm fn-prc-refresh-keeps-the-mark-on-a-fit-ledger
  (implies (and (fn-prc-carryp carry)
                (or (atom carry) (fn-prc-carry-findsp carry))
                (fn-retain-statep ledger))
           (fn-prc-carry-findsp (fn-prc-refresh carry ledger)))
  :hints (("Goal" :in-theory
           (e/d (fn-prc-refresh)
                (fn-prc-carryp fn-prc-carry-findsp fn-prc-delta fn-prc-build
                 fn-prc-ledger-findsp fn-retain-statep mv-nth)))))

(defthm fn-prc-refresh-names-the-ledger
  (and (consp (fn-prc-refresh carry ledger))
       (equal (car (fn-prc-refresh carry ledger)) ledger)))

(in-theory (disable fn-prc-carryp fn-prc-refresh fn-prc-delta fn-prc-set-okp
                    fn-prc-build))

