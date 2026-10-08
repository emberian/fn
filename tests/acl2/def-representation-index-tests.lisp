; What `def-representation-index' generates (books/def-representation-index
; .lisp), run on a toy log whose hash puts two keys in ONE bucket, and its
; teeth: each declaration refused or failing below is the toy with one
; premise of the generic theory removed.  The history store is the real
; instance (tests/acl2/def-representation-history-tests.lisp).
;
; The toy: objects are conses (K . PAYLOAD), the key is the natural K, the hash
; sends the keys 0 and 1 to ONE bucket (so a lookup of 1 walks objects of key
; 0 and the exact test alone separates them), the test is key equality.

(in-package "ACL2")
(include-book "../../books/def-representation-index")
(include-book "must-fail-checked")
(include-book "std/testing/assert-bang" :dir :system)

(defun dri-key (ev) (declare (xargs :guard t)) (if (and (consp ev) (natp (car ev))) (car ev) nil))
(defun dri-hash (k salt) (declare (xargs :guard t) (ignore salt)) (if (and (natp k) (< k 2)) 0 1))
(defun dri-test (k ev) (declare (xargs :guard t)) (and (natp k) (consp ev) (equal (car ev) k)))
(defun dri-proj (ev) (declare (xargs :guard t)) ev)

(defun dri-ap (x) (declare (xargs :guard t)) (true-listp x))
(defun create-dri-a () (declare (xargs :guard t)) nil)
(defun dri-a-count (a) (declare (xargs :guard (dri-ap a))) (len a))
(defun dri-a-at (i a)
  (declare (xargs :guard (and (natp i) (dri-ap a) (< i (dri-a-count a))))) (nth i a))
(defun dri-a-append (ev a) (declare (xargs :guard (dri-ap a))) (append a (list ev)))
(defun dri-a-clear (salt a)
  (declare (xargs :guard (unsigned-byte-p 32 salt)) (ignore salt a)) nil)
(defun dri-a-q (k h)
  (declare (xargs :guard (natp k)))
  (if (consp h)
      (if (dri-test k (car h))
          (cons (dri-proj (car h)) (dri-a-q k (cdr h)))
        (dri-a-q k (cdr h)))
    nil))

(defthm dri-hash-natp (natp (dri-hash k salt)) :rule-classes :type-prescription)
(defthm dri-test-implies-key
  (implies (dri-test k ev) (and (natp k) (equal (dri-key ev) k))))
(defthm dri-q-of-atom (implies (not (consp h)) (equal (dri-a-q k h) nil)))
(defthm dri-q-of-cons
  (equal (dri-a-q k (cons x r))
         (if (dri-test k x) (cons (dri-proj x) (dri-a-q k r)) (dri-a-q k r))))

(def-representation-index dri (ev :object)
  :index (:key dri-key :key-p natp :hash dri-hash :test dri-test :project dri-proj
          :query-export dri-q)
  :model (:recognizer dri-ap :creator create-dri-a :count dri-a-count :at dri-a-at
          :append dri-a-append :clear dri-a-clear :query dri-a-q)
  :lemmas (dri-hash-natp dri-test-implies-key dri-q-of-atom dri-q-of-cons))

(defabsstobj dri
  :attachable t
  :foundation dri$c
  :recognizer (dri-p :logic dri-ap :exec dri$cp)
  :creator (create-dri :logic create-dri-a :exec create-dri$c)
  :corr-fn dri$corr
  :exports ((dri-count :logic dri-a-count :exec dri$c-count)
            (dri-at :logic dri-a-at :exec dri$c-at)
            (dri-q :logic dri-a-q :exec dri$c-q)
            (dri-append :logic dri-a-append :exec dri$c-append :protect t)
            (dri-clear :logic dri-a-clear :exec dri$c-clear :protect t))
  :corr-fn-exists t)

; The positive witness: appends, a lookup in the one shared bucket, a clear.
(defun dri-run ()
  (declare (xargs :guard t))
  (with-local-stobj dri
    (mv-let (out dri)
      (let* ((dri (dri-append '(1 . a) dri)) (dri (dri-append '(1 . b) dri))
             (dri (dri-append '(0 . c) dri)) (dri (dri-append '(2 . d) dri))
             (before (list (dri-count dri) (dri-at 2 dri) (dri-q 1 dri) (dri-q 0 dri)
                           (dri-q 2 dri) (dri-q 9 dri)))
             (dri (dri-clear 5 dri)))
        (mv (list before (dri-count dri) (dri-q 1 dri)) dri))
      out)))

(assert! (equal (dri-run) '((4 (0 . c) ((1 . a) (1 . b)) ((0 . c)) ((2 . d)) nil) 0 nil)))

; The clear stores its salt in the register and the logical clear ignores it.
(defun dri-salt-run ()
  (declare (xargs :guard t))
  (with-local-stobj dri$c
    (mv-let (out dri$c)
      (let* ((dri$c (dri$c-append '(1 . a) dri$c)) (dri$c (dri$c-clear 5 dri$c)))
        (mv (list (dri$c-count dri$c) (dri$c-salt dri$c)) dri$c))
      out)))

(assert! (equal (dri-salt-run) '(0 5)))
(assert! (equal (dri-a-clear 5 '(1 2)) (dri-a-clear 6 '(1 2))))

; -----------------------------------------------------------------------------
; Teeth.

; The hash must be a natural: a hash that is not is refused by the generic
; theory's constraint, which no lemma of the instance proves.
(defun dri-bad-hash (k salt) (declare (xargs :guard t) (ignore k salt)) -1)

(must-fail-checked
 (def-representation-index drib1 (ev :object)
   :index (:key dri-key :key-p natp :hash dri-bad-hash :test dri-test :project dri-proj
           :query-export drib1-q)
   :model (:recognizer dri-ap :creator create-dri-a :count dri-a-count :at dri-a-at
           :append dri-a-append :clear dri-a-clear :query dri-a-q)
   :lemmas (dri-test-implies-key dri-q-of-atom dri-q-of-cons))
 :unchecked "dri-bad-hash is not a natural, so the constraint is not provable")

; The test must imply the key: a test that accepts an object of another key
; is refused (a bucket would then not be complete for its key).
(defun dri-loose-test (k ev) (declare (xargs :guard t) (ignore k)) (consp ev))
(defun dri-loose-q (k h)
  (declare (xargs :guard (natp k)))
  (if (consp h)
      (if (dri-loose-test k (car h))
          (cons (dri-proj (car h)) (dri-loose-q k (cdr h)))
        (dri-loose-q k (cdr h)))
    nil))
(defthm dri-loose-q-of-atom (implies (not (consp h)) (equal (dri-loose-q k h) nil)))
(defthm dri-loose-q-of-cons
  (equal (dri-loose-q k (cons x r))
         (if (dri-loose-test k x) (cons (dri-proj x) (dri-loose-q k r)) (dri-loose-q k r))))

(must-fail-checked
 (def-representation-index drib2 (ev :object)
   :index (:key dri-key :key-p natp :hash dri-hash :test dri-loose-test :project dri-proj
           :query-export drib2-q)
   :model (:recognizer dri-ap :creator create-dri-a :count dri-a-count :at dri-a-at
           :append dri-a-append :clear dri-a-clear :query dri-loose-q)
   :lemmas (dri-hash-natp dri-loose-q-of-atom dri-loose-q-of-cons))
 :unchecked "dri-loose-test accepts objects of every key: test-implies-key is not provable")

; The logical query must be the filter by the test, oldest first.
(defun dri-rev-q (k h)
  (declare (xargs :guard (natp k)))
  (if (consp h)
      (if (dri-test k (car h))
          (append (dri-rev-q k (cdr h)) (list (dri-proj (car h))))
        (dri-rev-q k (cdr h)))
    nil))

(must-fail-checked
 (def-representation-index drib3 (ev :object)
   :index (:key dri-key :key-p natp :hash dri-hash :test dri-test :project dri-proj
           :query-export drib3-q)
   :model (:recognizer dri-ap :creator create-dri-a :count dri-a-count :at dri-a-at
           :append dri-a-append :clear dri-a-clear :query dri-rev-q)
   :lemmas (dri-hash-natp dri-test-implies-key dri-q-of-atom dri-q-of-cons))
 :unchecked "dri-rev-q lists newest first: the cons equation is not provable")

; Malformed declarations are refused at expansion.
(must-fail-checked
 (def-representation-index drib4 (ev :octets)
   :index (:key dri-key :key-p natp :hash dri-hash :test dri-test :project dri-proj
           :query-export drib4-q)
   :model (:recognizer dri-ap :creator create-dri-a :count dri-a-count :at dri-a-at
           :append dri-a-append :clear dri-a-clear :query dri-a-q)
   :lemmas nil)
 :unchecked "refused at expansion: the column must be :object")

(must-fail-checked
 (def-representation-index drib5 (ev :object)
   :index (:key dri-no-such-fn :key-p natp :hash dri-hash :test dri-test :project dri-proj
           :query-export drib5-q)
   :model (:recognizer dri-ap :creator create-dri-a :count dri-a-count :at dri-a-at
           :append dri-a-append :clear dri-a-clear :query dri-a-q)
   :lemmas nil)
 :unchecked "refused at expansion: the key function is not in the world")

(must-fail-checked
 (def-representation-index drib6 (ev :object)
   :index (:key dri-key :key-p natp :hash dri-hash :test dri-test :project dri-proj
           :query-export other-q)
   :model (:recognizer dri-ap :creator create-dri-a :count dri-a-count :at dri-a-at
           :append dri-a-append :clear dri-a-clear :query dri-a-q)
   :lemmas nil)
 :unchecked "refused at expansion: the query export is not named NAME-SUFFIX")
