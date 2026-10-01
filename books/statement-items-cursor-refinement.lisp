; Proof-only span denotation. These functions never run on the served path.
(in-package "ACL2")
(include-book "statement-items-cursor")
(include-book "statement-items-reference")

(defun fn-sic-item-abstract (item)
 (declare (xargs :guard t :verify-guards nil))
 (if (equal (fn-cbor-ag-car item) :bytes)
  (cons :bytes (take (nfix (fn-sic-at 2 item)) (fn-sic-at 3 item))) item))
(defun fn-sic-items-abstract (items)
 (declare (xargs :guard t :verify-guards nil))
 (if (consp items)
  (cons (fn-sic-item-abstract (car items)) (fn-sic-items-abstract (cdr items))) nil))
(defun fn-sic-result-abstract (c)
 (declare (xargs :guard t :verify-guards nil))
 (let ((result (fn-sic-result c)))
  (if (fn-stmt-okp result) (fn-stmt-ok (fn-sic-items-abstract (fn-stmt-value result))) result)))

(defthm fn-sic-zero-quantum-preserves-continuation
 (equal (fn-sic-run 0 c) c)
 :hints (("Goal" :in-theory (enable fn-sic-run))))
(defthm fn-sic-done-is-absorbing
 (implies (equal (fn-sic-at 0 c) :done) (equal (fn-sic-step c) c))
 :hints (("Goal" :in-theory (enable fn-sic-step))))
(defthm fn-sic-run-is-resumable
 (implies (and (natp a) (natp b))
  (equal (fn-sic-run (+ a b) c) (fn-sic-run b (fn-sic-run a c))))
 :hints (("Goal" :induct (fn-sic-run a c)
          :in-theory (e/d (fn-sic-run) (fn-sic-step fn-sic-at)))))


(local (progn
(defthm fn-sic-at-is-nth
 (implies (natp i) (equal (fn-sic-at i x) (nth i x)))
 :hints (("Goal" :induct (fn-sic-at i x)
  :in-theory (enable fn-sic-at nth fn-cbor-ag-car fn-cbor-ag-cdr))))
(defthm fn-sic-put-is-update-nth
 (implies (natp i) (equal (fn-sic-put i v x) (update-nth i v x)))
 :hints (("Goal" :induct (fn-sic-put i v x)
  :in-theory (enable fn-sic-put update-nth fn-cbor-ag-car fn-cbor-ag-cdr))))
(defthm fn-sic-at-of-put
 (implies (and (natp i) (natp j))
  (equal (fn-sic-at i (fn-sic-put j value c))
   (if (equal i j) value (fn-sic-at i c))))
 :hints (("Goal" :in-theory (disable fn-sic-at fn-sic-put))))

))

(local (progn
(defthm fn-sic-at-of-cons
 (implies (natp i)
  (equal (fn-sic-at i (cons head tail))
   (if (zp i) head (fn-sic-at (1- i) tail))))
 :hints (("Goal" :in-theory (enable fn-sic-at fn-cbor-ag-car fn-cbor-ag-cdr))))

))

(defun fn-sic-preflight-complete (c)
 (declare (xargs :guard t :verify-guards nil
  :measure (if (equal (fn-sic-at 0 c) :preflight)
               (+ 1 (acl2-count (fn-sic-at 2 c))) 0)
  :hints (("Goal" :in-theory (e/d (fn-sic-step
    fn-sic-error fn-sic-finish fn-cbor-ag-car fn-cbor-ag-cdr)
   (fn-cbor-octetp fn-stmt-error fn-sic-at fn-sic-put
    fn-sic-at-is-nth fn-sic-put-is-update-nth))))))
 (if (equal (fn-sic-at 0 c) :preflight)
  (fn-sic-preflight-complete (fn-sic-step c)) c))


(defthm fn-sic-preflight-is-exact-old-validation
 (implies (and (equal (fn-sic-at 0 c) :preflight) (natp (fn-sic-at 4 c)))
  (let* ((d (fn-sic-preflight-complete c))
         (limited (not (fn-cbor-at-mostp (fn-sic-at 2 c) (fn-sic-at 4 c))))
         (malformed (or (fn-sic-at 7 c) (not (fn-cbor-octet-listp (fn-sic-at 2 c)))))
         (valid (and (not limited) (not malformed))))
   (and (equal (fn-sic-result d)
               (cond (limited (fn-stmt-error :limit)) (malformed (fn-stmt-error :malformed)) (t :pending)))
        (equal (fn-sic-at 0 d) (if valid :head :done))
        (implies valid (and (equal (fn-sic-at 2 d) (fn-sic-at 1 c)) (equal (fn-sic-at 3 d) 0)))
        (equal (fn-sic-at 1 d) (fn-sic-at 1 c))
        (equal (fn-sic-at 5 d) (fn-sic-at 5 c))
        (equal (fn-sic-at 6 d) (fn-sic-at 6 c)))))
 :hints (("Goal" :induct (fn-sic-preflight-complete c)
  :in-theory (e/d (fn-sic-preflight-complete fn-sic-step fn-sic-result
    fn-sic-error fn-sic-finish fn-cbor-at-mostp fn-cbor-octet-listp nfix)
   (fn-sic-at fn-sic-put fn-sic-at-is-nth fn-sic-put-is-update-nth fn-stmt-error fn-cbor-octetp)))))


(defun fn-sic-preflight-cost (c)
 (declare (xargs :guard t :verify-guards nil
  :measure (if (equal (fn-sic-at 0 c) :preflight)
               (+ 1 (acl2-count (fn-sic-at 2 c))) 0)
  :hints (("Goal" :in-theory (e/d (fn-sic-step fn-sic-error fn-sic-finish)
   (fn-cbor-octetp fn-stmt-error fn-sic-at fn-sic-put
    fn-sic-at-is-nth fn-sic-put-is-update-nth))))))
 (if (equal (fn-sic-at 0 c) :preflight)
  (+ 1 (fn-sic-preflight-cost (fn-sic-step c))) 0))
(defthm fn-sic-preflight-completion-is-paid-run
 (equal (fn-sic-run (fn-sic-preflight-cost c) c) (fn-sic-preflight-complete c))
 :hints (("Goal" :induct (fn-sic-preflight-complete c)
  :in-theory (e/d (fn-sic-preflight-complete fn-sic-preflight-cost fn-sic-run)
   (fn-sic-step fn-sic-at fn-sic-put fn-sic-at-is-nth fn-sic-put-is-update-nth)))))
(defthm fn-sic-preflight-cost-is-profile-bounded
 (implies (equal (fn-sic-at 0 c) :preflight)
  (<= (fn-sic-preflight-cost c) (+ 1 (nfix (fn-sic-at 4 c)))))
 :hints (("Goal" :induct (fn-sic-preflight-complete c)
  :in-theory (e/d (fn-sic-preflight-complete fn-sic-preflight-cost fn-sic-step
    fn-sic-error fn-sic-finish nfix)
   (fn-sic-at fn-sic-put fn-sic-at-is-nth fn-sic-put-is-update-nth fn-cbor-octetp fn-stmt-error)))))


(defun fn-sic-argument-complete (c)
 (declare (xargs :guard t :verify-guards nil
  :measure (if (equal (fn-sic-at 0 c) :argument) (+ 1 (nfix (fn-sic-at 10 c))) 0)
  :hints (("Goal" :in-theory (e/d (fn-sic-step fn-sic-error fn-sic-finish nfix)
   (fn-sic-at fn-sic-put fn-sic-at-is-nth fn-sic-put-is-update-nth fn-stmt-error))))))
 (if (equal (fn-sic-at 0 c) :argument)
  (fn-sic-argument-complete (fn-sic-step c)) c))
(defun fn-sic-bytes-complete (c)
 (declare (xargs :guard t :verify-guards nil
  :measure (if (equal (fn-sic-at 0 c) :bytes) (+ 1 (nfix (fn-sic-at 14 c))) 0)
  :hints (("Goal" :in-theory (e/d (fn-sic-step fn-sic-error fn-sic-finish fn-sic-push nfix)
   (fn-sic-at fn-sic-put fn-sic-at-is-nth fn-sic-put-is-update-nth fn-stmt-error))))))
 (if (equal (fn-sic-at 0 c) :bytes)
  (fn-sic-bytes-complete (fn-sic-step c)) c))
(defun fn-sic-item-complete (c)
 (declare (xargs :guard t :verify-guards nil))
 (let* ((head (fn-sic-step c)) (argument (fn-sic-argument-complete head))
        (checked (if (equal (fn-sic-at 0 argument) :argument-check) (fn-sic-step argument) argument)))
  (fn-sic-bytes-complete checked)))


(defun fn-sic-argument-width (additional)
 (declare (xargs :guard t :verify-guards nil))
 (cond ((equal additional 24) 1) ((equal additional 25) 2) ((equal additional 26) 4) (t 0)))

(local (progn
(defun fn-sic-argument-run (quantum c)
 (declare (xargs :guard t :verify-guards nil :measure (nfix quantum)))
 (if (or (zp quantum) (not (equal (fn-sic-at 0 c) :argument))) c
  (fn-sic-argument-run (1- quantum) (fn-sic-step c))))
(defthm fn-sic-argument-complete-is-small-run
 (implies (and (posp quantum) (<= (nfix (fn-sic-at 10 c)) quantum))
  (equal (fn-sic-argument-complete c) (fn-sic-argument-run quantum c)))
 :hints (("Goal" :induct (fn-sic-argument-run quantum c)
  :in-theory (e/d (fn-sic-argument-complete fn-sic-argument-run fn-sic-step fn-sic-error fn-sic-finish posp nfix)
   (fn-sic-at fn-sic-put fn-sic-at-is-nth fn-sic-put-is-update-nth fn-stmt-error)))))

))

(local (progn
(defthm fn-sic-argument-complete-is-small-run-total
 (implies (and (posp quantum)
               (or (not (equal (fn-sic-at 0 c) :argument))
                   (<= (nfix (fn-sic-at 10 c)) quantum)))
  (equal (fn-sic-argument-complete c) (fn-sic-argument-run quantum c)))
 :hints (("Goal" :use fn-sic-argument-complete-is-small-run
  :in-theory (e/d (fn-sic-argument-complete fn-sic-argument-run)
   (fn-sic-step fn-sic-at fn-sic-argument-complete-is-small-run)))))

))

(local (progn
(defthm fn-sic-argument-complete-is-four-run
 (implies (or (not (equal (fn-sic-at 0 c) :argument))
              (<= (nfix (fn-sic-at 10 c)) 4))
  (equal (fn-sic-argument-complete c) (fn-sic-argument-run 4 c)))
 :hints (("Goal" :use ((:instance fn-sic-argument-complete-is-small-run-total (quantum 4)))
  :in-theory (disable fn-sic-argument-complete fn-sic-argument-run fn-sic-step fn-sic-at
    fn-sic-argument-complete-is-small-run-total))))

))

(defthm fn-sic-argument-complete-is-old-argument
 (implies (and (natp additional) (natp (fn-sic-at 3 c)) (fn-cbor-octet-listp (fn-sic-at 2 c)))
  (let* ((d (fn-sic-argument-complete (fn-sic-argument-start major additional c)))
         (a (fn-cbor-decode-argument additional (fn-sic-at 2 c))))
   (and (equal (fn-sic-at 0 d) (if (fn-cbor-result-okp a) :argument-check :done))
        (equal (fn-sic-result d) (if (fn-cbor-result-okp a) :pending (fn-stmt-error (fn-cbor-result-value a))))
        (implies (fn-cbor-result-okp a)
         (and (equal (fn-sic-at 11 d) (fn-cbor-result-value a))
              (equal (fn-sic-at 2 d) (fn-cbor-result-rest a))
              (equal (fn-sic-at 3 d) (+ (fn-sic-at 3 c) (fn-sic-argument-width additional)))))
        (equal (fn-sic-at 1 d) (fn-sic-at 1 c))
        (equal (fn-sic-at 5 d) (fn-sic-at 5 c))
        (equal (fn-sic-at 6 d) (fn-sic-at 6 c))
        (equal (fn-sic-at 16 d) (fn-sic-at 16 c))
        (equal (fn-sic-at 8 d) major) (equal (fn-sic-at 9 d) additional))))
 :hints (("Goal" :do-not-induct t
  :expand ((:free (d) (fn-sic-argument-run 4 d))
           (:free (d) (fn-sic-argument-run 3 d))
           (:free (d) (fn-sic-argument-run 2 d))
           (:free (d) (fn-sic-argument-run 1 d))
           (:free (d) (fn-sic-argument-run 0 d)))
  :in-theory (e/d (fn-sic-argument-run fn-sic-argument-start fn-sic-argument-width
    fn-sic-step fn-sic-error fn-sic-finish fn-sic-result nfix
    fn-cbor-decode-argument fn-cbor-u16-from fn-cbor-u32-from fn-cbor-octet-listp fn-cbor-octetp
    fn-cbor-result-okp fn-cbor-result-value fn-cbor-result-rest fn-cbor-ok fn-cbor-error
    fn-cbor-ag-car fn-cbor-ag-cdr)
   (fn-sic-argument-complete fn-sic-argument-complete-is-small-run fn-sic-argument-complete-is-small-run-total
    fn-sic-at fn-sic-put fn-sic-at-is-nth fn-sic-put-is-update-nth)))))


(defthm fn-sic-bytes-complete-is-borrowed-span
 (implies (and (equal (fn-sic-at 0 c) :bytes) (natp (fn-sic-at 3 c)) (natp (fn-sic-at 14 c)))
  (let* ((d (fn-sic-bytes-complete c))
         (present (fn-cbor-at-leastp (fn-sic-at 2 c) (fn-sic-at 14 c))))
   (and (equal (fn-sic-at 0 d) (if present :head :done))
        (equal (fn-sic-result d) (if present :pending (fn-stmt-error :truncated)))
        (implies present
         (and (equal (fn-sic-at 2 d) (nthcdr (fn-sic-at 14 c) (fn-sic-at 2 c)))
              (equal (fn-sic-at 3 d) (+ (fn-sic-at 3 c) (fn-sic-at 14 c)))
              (equal (fn-sic-items-abstract (fn-sic-at 16 d))
               (cons (cons :bytes (take (nfix (fn-sic-at 13 c)) (fn-sic-at 15 c)))
                     (fn-sic-items-abstract (fn-sic-at 16 c))))))
        (equal (fn-sic-at 1 d) (fn-sic-at 1 c))
        (equal (fn-sic-at 5 d) (fn-sic-at 5 c))
        (equal (fn-sic-at 6 d) (fn-sic-at 6 c)))))
 :hints (("Goal" :induct (fn-sic-bytes-complete c)
  :in-theory (e/d (fn-sic-bytes-complete fn-sic-step fn-sic-push fn-sic-error fn-sic-finish fn-sic-result
    fn-sic-items-abstract fn-sic-item-abstract fn-cbor-at-leastp nthcdr nfix)
   (fn-sic-at fn-sic-put fn-sic-at-is-nth fn-sic-put-is-update-nth fn-stmt-error fn-cbor-octetp take
    fn-cbor-at-leastp-is-length-lower-bound)))))


(local (progn
(defthm fn-sic-argument-complete-outside-phase
 (implies (not (equal (fn-sic-at 0 c) :argument)) (equal (fn-sic-argument-complete c) c))
 :hints (("Goal" :expand (fn-sic-argument-complete c))))
(defthm fn-sic-bytes-complete-outside-phase
 (implies (not (equal (fn-sic-at 0 c) :bytes)) (equal (fn-sic-bytes-complete c) c))
 :hints (("Goal" :expand (fn-sic-bytes-complete c))))

))

(local (progn
(defthm fn-sic-old-argument-has-natural-value-and-octet-rest
 (implies (and (natp additional) (fn-cbor-octet-listp xs)
               (fn-cbor-result-okp (fn-cbor-decode-argument additional xs)))
  (and (natp (fn-cbor-result-value (fn-cbor-decode-argument additional xs)))
       (<= (fn-cbor-result-value (fn-cbor-decode-argument additional xs)) 4294967295)
       (fn-cbor-octet-listp (fn-cbor-result-rest (fn-cbor-decode-argument additional xs)))))
 :hints (("Goal" :do-not-induct t
  :in-theory (enable fn-cbor-decode-argument fn-cbor-result-okp fn-cbor-result-value fn-cbor-result-rest
    fn-cbor-ok fn-cbor-error fn-cbor-ag-car fn-cbor-ag-cdr fn-cbor-u16-from fn-cbor-u32-from
    fn-cbor-octet-listp fn-cbor-octetp))))

))

(defthm fn-sic-item-complete-is-old-item
 (implies (and (equal (fn-sic-at 0 c) :head)
               (consp (fn-sic-at 2 c)) (fn-cbor-octet-listp (fn-sic-at 2 c))
               (natp (fn-sic-at 3 c)) (posp (fn-sic-at 6 c)) (natp (fn-sic-at 5 c)))
  (let* ((d (fn-sic-item-complete c))
         (a (fn-cbor-decode-prechecked (fn-sic-at 2 c) (fn-sic-at 5 c))))
   (and (equal (fn-sic-at 0 d) (if (fn-cbor-result-okp a) :head :done))
        (equal (fn-sic-result d) (if (fn-cbor-result-okp a) :pending (fn-stmt-error (fn-cbor-result-value a))))
        (implies (fn-cbor-result-okp a)
         (and (equal (fn-sic-at 2 d) (fn-cbor-result-rest a))
              (natp (fn-sic-at 3 d))
              (equal (fn-sic-items-abstract (fn-sic-at 16 d))
               (cons (fn-cbor-result-value a) (fn-sic-items-abstract (fn-sic-at 16 c))))))
        (equal (fn-sic-at 1 d) (fn-sic-at 1 c))
        (equal (fn-sic-at 5 d) (fn-sic-at 5 c))
        (equal (fn-sic-at 6 d) (1- (fn-sic-at 6 c))))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-sic-old-argument-has-natural-value-and-octet-rest
    (additional (car (fn-sic-at 2 c))) (xs (cdr (fn-sic-at 2 c))))
   (:instance fn-sic-old-argument-has-natural-value-and-octet-rest
    (additional (- (car (fn-sic-at 2 c)) 64)) (xs (cdr (fn-sic-at 2 c)))))
  :in-theory (e/d (fn-sic-item-complete fn-sic-step fn-sic-error fn-sic-finish fn-sic-push fn-sic-result
    fn-sic-item-abstract fn-sic-items-abstract nfix posp
    fn-cbor-decode-prechecked fn-cbor-decode-unsigned fn-cbor-decode-bytes-bounded
    fn-cbor-octet-listp fn-cbor-octetp fn-cbor-result-okp fn-cbor-result-value fn-cbor-result-rest
    fn-cbor-ok fn-cbor-error fn-cbor-ag-car fn-cbor-ag-cdr)
   (fn-sic-at fn-sic-put fn-sic-at-is-nth fn-sic-put-is-update-nth
    fn-sic-argument-complete fn-sic-argument-start fn-sic-argument-run fn-sic-bytes-complete
    fn-sic-argument-complete-is-four-run fn-sic-argument-complete-is-small-run
    fn-sic-argument-complete-is-small-run-total fn-cbor-decode-argument take
    fn-cbor-at-leastp-is-length-lower-bound fn-stmt-error)))))


(local (progn
(defthm fn-sic-octet-listp-of-nthcdr
 (implies (fn-cbor-octet-listp xs) (fn-cbor-octet-listp (nthcdr n xs)))
 :hints (("Goal" :induct (nthcdr n xs) :in-theory (enable nthcdr fn-cbor-octet-listp))))

))

(local (progn
(defthm fn-sic-old-item-has-octet-rest
 (implies (and (fn-cbor-octet-listp xs) (natp budget)
               (fn-cbor-result-okp (fn-cbor-decode-prechecked xs budget)))
  (fn-cbor-octet-listp (fn-cbor-result-rest (fn-cbor-decode-prechecked xs budget))))
 :hints (("Goal"  :do-not-induct t
 :use ((:instance fn-sic-old-argument-has-natural-value-and-octet-rest (additional (car xs)) (xs (cdr xs)))
 (:instance fn-sic-old-argument-has-natural-value-and-octet-rest (additional (- (car xs) 64)) (xs (cdr xs))))
 :in-theory (e/d (fn-cbor-decode-prechecked fn-cbor-decode-unsigned fn-cbor-decode-bytes-bounded
    fn-cbor-result-okp fn-cbor-result-rest fn-cbor-ok fn-cbor-error fn-cbor-octet-listp)
    (fn-cbor-decode-argument fn-cbor-at-leastp fn-cbor-at-leastp-is-length-lower-bound take nthcdr)))))

))

(local (progn
(defthm fn-sic-argument-complete-retains-ordered-items
 (equal (fn-sic-at 17 (fn-sic-argument-complete c)) (fn-sic-at 17 c))
 :hints (("Goal" :induct (fn-sic-argument-complete c)
 :in-theory (e/d (fn-sic-argument-complete fn-sic-step fn-sic-error fn-sic-finish)
 (fn-sic-at fn-sic-put fn-sic-at-is-nth fn-sic-put-is-update-nth fn-sic-argument-complete-is-four-run fn-sic-argument-complete-is-small-run fn-sic-argument-complete-is-small-run-total)))))
(defthm fn-sic-bytes-complete-retains-ordered-items
 (equal (fn-sic-at 17 (fn-sic-bytes-complete c)) (fn-sic-at 17 c))
 :hints (("Goal" :induct (fn-sic-bytes-complete c)
 :in-theory (e/d (fn-sic-bytes-complete fn-sic-step fn-sic-error fn-sic-finish fn-sic-push)
 (fn-sic-at fn-sic-put fn-sic-at-is-nth fn-sic-put-is-update-nth fn-sic-argument-complete-is-four-run fn-sic-argument-complete-is-small-run fn-sic-argument-complete-is-small-run-total)))))

))

(local (progn
(defthm fn-sic-item-complete-retains-ordered-items
 (implies (equal (fn-sic-at 0 c) :head)
  (equal (fn-sic-at 17 (fn-sic-item-complete c)) (fn-sic-at 17 c)))
 :hints (("Goal" :in-theory (e/d (fn-sic-item-complete fn-sic-step fn-sic-error fn-sic-finish fn-sic-push fn-sic-argument-start)
 (fn-sic-at fn-sic-put fn-sic-at-is-nth fn-sic-put-is-update-nth fn-sic-argument-complete fn-sic-bytes-complete
 fn-sic-argument-complete-is-four-run fn-sic-argument-complete-is-small-run fn-sic-argument-complete-is-small-run-total)))))

))

(defun fn-sic-reverse-complete (c)
 (declare (xargs :guard t :verify-guards nil
  :measure (if (equal (fn-sic-at 0 c) :reverse) (+ 1 (acl2-count (fn-sic-at 16 c))) 0)
  :hints (("Goal" :in-theory (e/d (fn-sic-step fn-sic-finish)
   (fn-sic-at fn-sic-put fn-sic-at-is-nth fn-sic-put-is-update-nth))))))
 (if (equal (fn-sic-at 0 c) :reverse) (fn-sic-reverse-complete (fn-sic-step c)) c))
(defthm fn-sic-abstract-of-revappend
 (equal (fn-sic-items-abstract (revappend x y))
        (revappend (fn-sic-items-abstract x) (fn-sic-items-abstract y)))
 :hints (("Goal" :induct (revappend x y) :in-theory (enable revappend fn-sic-items-abstract))))
(defthm fn-sic-reverse-complete-is-ordered-result
 (implies (equal (fn-sic-at 0 c) :reverse)
  (let ((d (fn-sic-reverse-complete c)))
   (and (equal (fn-sic-at 0 d) :done)
    (equal (fn-sic-result-abstract d)
     (fn-stmt-ok (revappend (fn-sic-items-abstract (fn-sic-at 16 c))
                           (fn-sic-items-abstract (fn-sic-at 17 c))))))))
 :hints (("Goal" :induct (fn-sic-reverse-complete c)
  :in-theory (e/d (fn-sic-reverse-complete fn-sic-step fn-sic-finish fn-sic-result-abstract
    fn-sic-result fn-stmt-okp fn-stmt-value fn-stmt-ok fn-sic-items-abstract revappend)
   (fn-sic-at fn-sic-put fn-sic-at-is-nth fn-sic-put-is-update-nth)))))


(defun fn-sic-sequence-complete (fuel c)
 (declare (xargs :guard t :verify-guards nil :measure (nfix fuel)))
 (if (not (equal (fn-sic-at 0 c) :head)) c
  (if (not (consp (fn-sic-at 2 c))) (fn-sic-reverse-complete (fn-sic-step c))
   (if (zp fuel) (fn-sic-step c)
    (fn-sic-sequence-complete (1- fuel) (fn-sic-item-complete c))))))


(local (progn
(defthm fn-sic-at-is-nth
 (implies (natp i) (equal (fn-sic-at i x) (nth i x)))
 :hints (("Goal" :induct (fn-sic-at i x)
  :in-theory (enable fn-sic-at nth fn-cbor-ag-car fn-cbor-ag-cdr))))
(defthm fn-sic-put-is-update-nth
 (implies (natp i) (equal (fn-sic-put i v x) (update-nth i v x)))
 :hints (("Goal" :induct (fn-sic-put i v x)
  :in-theory (enable fn-sic-put update-nth fn-cbor-ag-car fn-cbor-ag-cdr))))
(defthm fn-sic-at-of-put
 (implies (and (natp i) (natp j))
  (equal (fn-sic-at i (fn-sic-put j value c))
   (if (equal i j) value (fn-sic-at i c))))
 :hints (("Goal" :in-theory (disable fn-sic-at fn-sic-put))))

))

(local (progn
(defthm fn-sic-at-of-cons
 (implies (natp i)
  (equal (fn-sic-at i (cons head tail))
   (if (zp i) head (fn-sic-at (1- i) tail))))
 :hints (("Goal" :in-theory (enable fn-sic-at fn-cbor-ag-car fn-cbor-ag-cdr))))

))

(defun fn-sic-preflight-complete (c)
 (declare (xargs :guard t :verify-guards nil
  :measure (if (equal (fn-sic-at 0 c) :preflight)
               (+ 1 (acl2-count (fn-sic-at 2 c))) 0)
  :hints (("Goal" :in-theory (e/d (fn-sic-step
    fn-sic-error fn-sic-finish fn-cbor-ag-car fn-cbor-ag-cdr)
   (fn-cbor-octetp fn-stmt-error fn-sic-at fn-sic-put
    fn-sic-at-is-nth fn-sic-put-is-update-nth))))))
 (if (equal (fn-sic-at 0 c) :preflight)
  (fn-sic-preflight-complete (fn-sic-step c)) c))


(defthm fn-sic-preflight-is-exact-old-validation
 (implies (and (equal (fn-sic-at 0 c) :preflight) (natp (fn-sic-at 4 c)))
  (let* ((d (fn-sic-preflight-complete c))
         (limited (not (fn-cbor-at-mostp (fn-sic-at 2 c) (fn-sic-at 4 c))))
         (malformed (or (fn-sic-at 7 c) (not (fn-cbor-octet-listp (fn-sic-at 2 c)))))
         (valid (and (not limited) (not malformed))))
   (and (equal (fn-sic-result d)
               (cond (limited (fn-stmt-error :limit)) (malformed (fn-stmt-error :malformed)) (t :pending)))
        (equal (fn-sic-at 0 d) (if valid :head :done))
        (implies valid (and (equal (fn-sic-at 2 d) (fn-sic-at 1 c)) (equal (fn-sic-at 3 d) 0)))
        (equal (fn-sic-at 1 d) (fn-sic-at 1 c))
        (equal (fn-sic-at 5 d) (fn-sic-at 5 c))
        (equal (fn-sic-at 6 d) (fn-sic-at 6 c)))))
 :hints (("Goal" :induct (fn-sic-preflight-complete c)
  :in-theory (e/d (fn-sic-preflight-complete fn-sic-step fn-sic-result
    fn-sic-error fn-sic-finish fn-cbor-at-mostp fn-cbor-octet-listp nfix)
   (fn-sic-at fn-sic-put fn-sic-at-is-nth fn-sic-put-is-update-nth fn-stmt-error fn-cbor-octetp)))))


(defun fn-sic-preflight-cost (c)
 (declare (xargs :guard t :verify-guards nil
  :measure (if (equal (fn-sic-at 0 c) :preflight)
               (+ 1 (acl2-count (fn-sic-at 2 c))) 0)
  :hints (("Goal" :in-theory (e/d (fn-sic-step fn-sic-error fn-sic-finish)
   (fn-cbor-octetp fn-stmt-error fn-sic-at fn-sic-put
    fn-sic-at-is-nth fn-sic-put-is-update-nth))))))
 (if (equal (fn-sic-at 0 c) :preflight)
  (+ 1 (fn-sic-preflight-cost (fn-sic-step c))) 0))
(defthm fn-sic-preflight-completion-is-paid-run
 (equal (fn-sic-run (fn-sic-preflight-cost c) c) (fn-sic-preflight-complete c))
 :hints (("Goal" :induct (fn-sic-preflight-complete c)
  :in-theory (e/d (fn-sic-preflight-complete fn-sic-preflight-cost fn-sic-run)
   (fn-sic-step fn-sic-at fn-sic-put fn-sic-at-is-nth fn-sic-put-is-update-nth)))))
(defthm fn-sic-preflight-cost-is-profile-bounded
 (implies (equal (fn-sic-at 0 c) :preflight)
  (<= (fn-sic-preflight-cost c) (+ 1 (nfix (fn-sic-at 4 c)))))
 :hints (("Goal" :induct (fn-sic-preflight-complete c)
  :in-theory (e/d (fn-sic-preflight-complete fn-sic-preflight-cost fn-sic-step
    fn-sic-error fn-sic-finish nfix)
   (fn-sic-at fn-sic-put fn-sic-at-is-nth fn-sic-put-is-update-nth fn-cbor-octetp fn-stmt-error)))))


(defun fn-sic-argument-complete (c)
 (declare (xargs :guard t :verify-guards nil
  :measure (if (equal (fn-sic-at 0 c) :argument) (+ 1 (nfix (fn-sic-at 10 c))) 0)
  :hints (("Goal" :in-theory (e/d (fn-sic-step fn-sic-error fn-sic-finish nfix)
   (fn-sic-at fn-sic-put fn-sic-at-is-nth fn-sic-put-is-update-nth fn-stmt-error))))))
 (if (equal (fn-sic-at 0 c) :argument)
  (fn-sic-argument-complete (fn-sic-step c)) c))
(defun fn-sic-bytes-complete (c)
 (declare (xargs :guard t :verify-guards nil
  :measure (if (equal (fn-sic-at 0 c) :bytes) (+ 1 (nfix (fn-sic-at 14 c))) 0)
  :hints (("Goal" :in-theory (e/d (fn-sic-step fn-sic-error fn-sic-finish fn-sic-push nfix)
   (fn-sic-at fn-sic-put fn-sic-at-is-nth fn-sic-put-is-update-nth fn-stmt-error))))))
 (if (equal (fn-sic-at 0 c) :bytes)
  (fn-sic-bytes-complete (fn-sic-step c)) c))
(defun fn-sic-item-complete (c)
 (declare (xargs :guard t :verify-guards nil))
 (let* ((head (fn-sic-step c)) (argument (fn-sic-argument-complete head))
        (checked (if (equal (fn-sic-at 0 argument) :argument-check) (fn-sic-step argument) argument)))
  (fn-sic-bytes-complete checked)))


(defun fn-sic-argument-width (additional)
 (declare (xargs :guard t :verify-guards nil))
 (cond ((equal additional 24) 1) ((equal additional 25) 2) ((equal additional 26) 4) (t 0)))

(local (progn
(defun fn-sic-argument-run (quantum c)
 (declare (xargs :guard t :verify-guards nil :measure (nfix quantum)))
 (if (or (zp quantum) (not (equal (fn-sic-at 0 c) :argument))) c
  (fn-sic-argument-run (1- quantum) (fn-sic-step c))))
(defthm fn-sic-argument-complete-is-small-run
 (implies (and (posp quantum) (<= (nfix (fn-sic-at 10 c)) quantum))
  (equal (fn-sic-argument-complete c) (fn-sic-argument-run quantum c)))
 :hints (("Goal" :induct (fn-sic-argument-run quantum c)
  :in-theory (e/d (fn-sic-argument-complete fn-sic-argument-run fn-sic-step fn-sic-error fn-sic-finish posp nfix)
   (fn-sic-at fn-sic-put fn-sic-at-is-nth fn-sic-put-is-update-nth fn-stmt-error)))))

))

(local (progn
(defthm fn-sic-argument-complete-is-small-run-total
 (implies (and (posp quantum)
               (or (not (equal (fn-sic-at 0 c) :argument))
                   (<= (nfix (fn-sic-at 10 c)) quantum)))
  (equal (fn-sic-argument-complete c) (fn-sic-argument-run quantum c)))
 :hints (("Goal" :use fn-sic-argument-complete-is-small-run
  :in-theory (e/d (fn-sic-argument-complete fn-sic-argument-run)
   (fn-sic-step fn-sic-at fn-sic-argument-complete-is-small-run)))))

))

(local (progn
(defthm fn-sic-argument-complete-is-four-run
 (implies (or (not (equal (fn-sic-at 0 c) :argument))
              (<= (nfix (fn-sic-at 10 c)) 4))
  (equal (fn-sic-argument-complete c) (fn-sic-argument-run 4 c)))
 :hints (("Goal" :use ((:instance fn-sic-argument-complete-is-small-run-total (quantum 4)))
  :in-theory (disable fn-sic-argument-complete fn-sic-argument-run fn-sic-step fn-sic-at
    fn-sic-argument-complete-is-small-run-total))))

))

(defthm fn-sic-argument-complete-is-old-argument
 (implies (and (natp additional) (natp (fn-sic-at 3 c)) (fn-cbor-octet-listp (fn-sic-at 2 c)))
  (let* ((d (fn-sic-argument-complete (fn-sic-argument-start major additional c)))
         (a (fn-cbor-decode-argument additional (fn-sic-at 2 c))))
   (and (equal (fn-sic-at 0 d) (if (fn-cbor-result-okp a) :argument-check :done))
        (equal (fn-sic-result d) (if (fn-cbor-result-okp a) :pending (fn-stmt-error (fn-cbor-result-value a))))
        (implies (fn-cbor-result-okp a)
         (and (equal (fn-sic-at 11 d) (fn-cbor-result-value a))
              (equal (fn-sic-at 2 d) (fn-cbor-result-rest a))
              (equal (fn-sic-at 3 d) (+ (fn-sic-at 3 c) (fn-sic-argument-width additional)))))
        (equal (fn-sic-at 1 d) (fn-sic-at 1 c))
        (equal (fn-sic-at 5 d) (fn-sic-at 5 c))
        (equal (fn-sic-at 6 d) (fn-sic-at 6 c))
        (equal (fn-sic-at 16 d) (fn-sic-at 16 c))
        (equal (fn-sic-at 8 d) major) (equal (fn-sic-at 9 d) additional))))
 :hints (("Goal" :do-not-induct t
  :expand ((:free (d) (fn-sic-argument-run 4 d))
           (:free (d) (fn-sic-argument-run 3 d))
           (:free (d) (fn-sic-argument-run 2 d))
           (:free (d) (fn-sic-argument-run 1 d))
           (:free (d) (fn-sic-argument-run 0 d)))
  :in-theory (e/d (fn-sic-argument-run fn-sic-argument-start fn-sic-argument-width
    fn-sic-step fn-sic-error fn-sic-finish fn-sic-result nfix
    fn-cbor-decode-argument fn-cbor-u16-from fn-cbor-u32-from fn-cbor-octet-listp fn-cbor-octetp
    fn-cbor-result-okp fn-cbor-result-value fn-cbor-result-rest fn-cbor-ok fn-cbor-error
    fn-cbor-ag-car fn-cbor-ag-cdr)
   (fn-sic-argument-complete fn-sic-argument-complete-is-small-run fn-sic-argument-complete-is-small-run-total
    fn-sic-at fn-sic-put fn-sic-at-is-nth fn-sic-put-is-update-nth)))))


(defthm fn-sic-bytes-complete-is-borrowed-span
 (implies (and (equal (fn-sic-at 0 c) :bytes) (natp (fn-sic-at 3 c)) (natp (fn-sic-at 14 c)))
  (let* ((d (fn-sic-bytes-complete c))
         (present (fn-cbor-at-leastp (fn-sic-at 2 c) (fn-sic-at 14 c))))
   (and (equal (fn-sic-at 0 d) (if present :head :done))
        (equal (fn-sic-result d) (if present :pending (fn-stmt-error :truncated)))
        (implies present
         (and (equal (fn-sic-at 2 d) (nthcdr (fn-sic-at 14 c) (fn-sic-at 2 c)))
              (equal (fn-sic-at 3 d) (+ (fn-sic-at 3 c) (fn-sic-at 14 c)))
              (equal (fn-sic-items-abstract (fn-sic-at 16 d))
               (cons (cons :bytes (take (nfix (fn-sic-at 13 c)) (fn-sic-at 15 c)))
                     (fn-sic-items-abstract (fn-sic-at 16 c))))))
        (equal (fn-sic-at 1 d) (fn-sic-at 1 c))
        (equal (fn-sic-at 5 d) (fn-sic-at 5 c))
        (equal (fn-sic-at 6 d) (fn-sic-at 6 c)))))
 :hints (("Goal" :induct (fn-sic-bytes-complete c)
  :in-theory (e/d (fn-sic-bytes-complete fn-sic-step fn-sic-push fn-sic-error fn-sic-finish fn-sic-result
    fn-sic-items-abstract fn-sic-item-abstract fn-cbor-at-leastp nthcdr nfix)
   (fn-sic-at fn-sic-put fn-sic-at-is-nth fn-sic-put-is-update-nth fn-stmt-error fn-cbor-octetp take
    fn-cbor-at-leastp-is-length-lower-bound)))))


(local (progn
(defthm fn-sic-argument-complete-outside-phase
 (implies (not (equal (fn-sic-at 0 c) :argument)) (equal (fn-sic-argument-complete c) c))
 :hints (("Goal" :expand (fn-sic-argument-complete c))))
(defthm fn-sic-bytes-complete-outside-phase
 (implies (not (equal (fn-sic-at 0 c) :bytes)) (equal (fn-sic-bytes-complete c) c))
 :hints (("Goal" :expand (fn-sic-bytes-complete c))))

))

(local (progn
(defthm fn-sic-old-argument-has-natural-value-and-octet-rest
 (implies (and (natp additional) (fn-cbor-octet-listp xs)
               (fn-cbor-result-okp (fn-cbor-decode-argument additional xs)))
  (and (natp (fn-cbor-result-value (fn-cbor-decode-argument additional xs)))
       (<= (fn-cbor-result-value (fn-cbor-decode-argument additional xs)) 4294967295)
       (fn-cbor-octet-listp (fn-cbor-result-rest (fn-cbor-decode-argument additional xs)))))
 :hints (("Goal" :do-not-induct t
  :in-theory (enable fn-cbor-decode-argument fn-cbor-result-okp fn-cbor-result-value fn-cbor-result-rest
    fn-cbor-ok fn-cbor-error fn-cbor-ag-car fn-cbor-ag-cdr fn-cbor-u16-from fn-cbor-u32-from
    fn-cbor-octet-listp fn-cbor-octetp))))

))

(defthm fn-sic-item-complete-is-old-item
 (implies (and (equal (fn-sic-at 0 c) :head)
               (consp (fn-sic-at 2 c)) (fn-cbor-octet-listp (fn-sic-at 2 c))
               (natp (fn-sic-at 3 c)) (posp (fn-sic-at 6 c)) (natp (fn-sic-at 5 c)))
  (let* ((d (fn-sic-item-complete c))
         (a (fn-cbor-decode-prechecked (fn-sic-at 2 c) (fn-sic-at 5 c))))
   (and (equal (fn-sic-at 0 d) (if (fn-cbor-result-okp a) :head :done))
        (equal (fn-sic-result d) (if (fn-cbor-result-okp a) :pending (fn-stmt-error (fn-cbor-result-value a))))
        (implies (fn-cbor-result-okp a)
         (and (equal (fn-sic-at 2 d) (fn-cbor-result-rest a))
              (natp (fn-sic-at 3 d))
              (equal (fn-sic-items-abstract (fn-sic-at 16 d))
               (cons (fn-cbor-result-value a) (fn-sic-items-abstract (fn-sic-at 16 c))))))
        (equal (fn-sic-at 1 d) (fn-sic-at 1 c))
        (equal (fn-sic-at 5 d) (fn-sic-at 5 c))
        (equal (fn-sic-at 6 d) (1- (fn-sic-at 6 c))))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-sic-old-argument-has-natural-value-and-octet-rest
    (additional (car (fn-sic-at 2 c))) (xs (cdr (fn-sic-at 2 c))))
   (:instance fn-sic-old-argument-has-natural-value-and-octet-rest
    (additional (- (car (fn-sic-at 2 c)) 64)) (xs (cdr (fn-sic-at 2 c)))))
  :in-theory (e/d (fn-sic-item-complete fn-sic-step fn-sic-error fn-sic-finish fn-sic-push fn-sic-result
    fn-sic-item-abstract fn-sic-items-abstract nfix posp
    fn-cbor-decode-prechecked fn-cbor-decode-unsigned fn-cbor-decode-bytes-bounded
    fn-cbor-octet-listp fn-cbor-octetp fn-cbor-result-okp fn-cbor-result-value fn-cbor-result-rest
    fn-cbor-ok fn-cbor-error fn-cbor-ag-car fn-cbor-ag-cdr)
   (fn-sic-at fn-sic-put fn-sic-at-is-nth fn-sic-put-is-update-nth
    fn-sic-argument-complete fn-sic-argument-start fn-sic-argument-run fn-sic-bytes-complete
    fn-sic-argument-complete-is-four-run fn-sic-argument-complete-is-small-run
    fn-sic-argument-complete-is-small-run-total fn-cbor-decode-argument take
    fn-cbor-at-leastp-is-length-lower-bound fn-stmt-error)))))


(local (progn
(defthm fn-sic-octet-listp-of-nthcdr
 (implies (fn-cbor-octet-listp xs) (fn-cbor-octet-listp (nthcdr n xs)))
 :hints (("Goal" :induct (nthcdr n xs) :in-theory (enable nthcdr fn-cbor-octet-listp))))

))

(local (progn
(defthm fn-sic-old-item-has-octet-rest
 (implies (and (fn-cbor-octet-listp xs) (natp budget)
               (fn-cbor-result-okp (fn-cbor-decode-prechecked xs budget)))
  (fn-cbor-octet-listp (fn-cbor-result-rest (fn-cbor-decode-prechecked xs budget))))
 :hints (("Goal"  :do-not-induct t
 :use ((:instance fn-sic-old-argument-has-natural-value-and-octet-rest (additional (car xs)) (xs (cdr xs)))
 (:instance fn-sic-old-argument-has-natural-value-and-octet-rest (additional (- (car xs) 64)) (xs (cdr xs))))
 :in-theory (e/d (fn-cbor-decode-prechecked fn-cbor-decode-unsigned fn-cbor-decode-bytes-bounded
    fn-cbor-result-okp fn-cbor-result-rest fn-cbor-ok fn-cbor-error fn-cbor-octet-listp)
    (fn-cbor-decode-argument fn-cbor-at-leastp fn-cbor-at-leastp-is-length-lower-bound take nthcdr)))))

))

(local (progn
(defthm fn-sic-argument-complete-retains-ordered-items
 (equal (fn-sic-at 17 (fn-sic-argument-complete c)) (fn-sic-at 17 c))
 :hints (("Goal" :induct (fn-sic-argument-complete c)
 :in-theory (e/d (fn-sic-argument-complete fn-sic-step fn-sic-error fn-sic-finish)
 (fn-sic-at fn-sic-put fn-sic-at-is-nth fn-sic-put-is-update-nth fn-sic-argument-complete-is-four-run fn-sic-argument-complete-is-small-run fn-sic-argument-complete-is-small-run-total)))))
(defthm fn-sic-bytes-complete-retains-ordered-items
 (equal (fn-sic-at 17 (fn-sic-bytes-complete c)) (fn-sic-at 17 c))
 :hints (("Goal" :induct (fn-sic-bytes-complete c)
 :in-theory (e/d (fn-sic-bytes-complete fn-sic-step fn-sic-error fn-sic-finish fn-sic-push)
 (fn-sic-at fn-sic-put fn-sic-at-is-nth fn-sic-put-is-update-nth fn-sic-argument-complete-is-four-run fn-sic-argument-complete-is-small-run fn-sic-argument-complete-is-small-run-total)))))

))

(local (progn
(defthm fn-sic-item-complete-retains-ordered-items
 (implies (equal (fn-sic-at 0 c) :head)
  (equal (fn-sic-at 17 (fn-sic-item-complete c)) (fn-sic-at 17 c)))
 :hints (("Goal" :in-theory (e/d (fn-sic-item-complete fn-sic-step fn-sic-error fn-sic-finish fn-sic-push fn-sic-argument-start)
 (fn-sic-at fn-sic-put fn-sic-at-is-nth fn-sic-put-is-update-nth fn-sic-argument-complete fn-sic-bytes-complete
 fn-sic-argument-complete-is-four-run fn-sic-argument-complete-is-small-run fn-sic-argument-complete-is-small-run-total)))))

))

(local (progn
(defthm fn-sic-item-complete-retains-octet-domain
 (implies (and (equal (fn-sic-at 0 c) :head)
   (consp (fn-sic-at 2 c)) (fn-cbor-octet-listp (fn-sic-at 2 c))
   (natp (fn-sic-at 3 c)) (posp (fn-sic-at 6 c)) (natp (fn-sic-at 5 c))
   (equal (fn-sic-at 0 (fn-sic-item-complete c)) :head))
  (fn-cbor-octet-listp (fn-sic-at 2 (fn-sic-item-complete c))))
 :hints (("Goal" :use ((:instance fn-sic-item-complete-is-old-item)
   (:instance fn-sic-old-item-has-octet-rest (xs (fn-sic-at 2 c)) (budget (fn-sic-at 5 c))))
 :in-theory (disable fn-sic-item-complete fn-sic-item-complete-is-old-item fn-sic-at
   fn-sic-old-item-has-octet-rest fn-cbor-octet-listp fn-cbor-result-rest fn-cbor-result-okp))))

))

(local (progn
(defthm fn-sic-error-has-exact-abstract-result
 (equal (fn-sic-result-abstract (fn-sic-error code c)) (fn-stmt-error code))
 :hints (("Goal" :in-theory (e/d (fn-sic-result-abstract fn-sic-result fn-sic-error fn-sic-finish
    fn-stmt-okp fn-stmt-error)
    (fn-sic-at fn-sic-put fn-sic-at-is-nth fn-sic-put-is-update-nth)))))
(defthm fn-sic-item-error-has-exact-abstract-result
 (implies (and (equal (fn-sic-at 0 c) :head)
   (consp (fn-sic-at 2 c)) (fn-cbor-octet-listp (fn-sic-at 2 c))
   (natp (fn-sic-at 3 c)) (posp (fn-sic-at 6 c)) (natp (fn-sic-at 5 c))
   (not (fn-cbor-result-okp (fn-cbor-decode-prechecked (fn-sic-at 2 c) (fn-sic-at 5 c)))))
  (equal (fn-sic-result-abstract (fn-sic-item-complete c))
   (fn-stmt-error (fn-cbor-result-value (fn-cbor-decode-prechecked (fn-sic-at 2 c) (fn-sic-at 5 c))))))
 :hints (("Goal" :use ((:instance fn-sic-item-complete-is-old-item))
 :in-theory (e/d (fn-sic-result-abstract fn-stmt-okp fn-stmt-error)
 (fn-sic-item-complete fn-sic-at fn-sic-at-is-nth fn-sic-result fn-sic-item-complete-is-old-item)))))

))

(defun fn-sic-reverse-complete (c)
 (declare (xargs :guard t :verify-guards nil
  :measure (if (equal (fn-sic-at 0 c) :reverse) (+ 1 (acl2-count (fn-sic-at 16 c))) 0)
  :hints (("Goal" :in-theory (e/d (fn-sic-step fn-sic-finish)
   (fn-sic-at fn-sic-put fn-sic-at-is-nth fn-sic-put-is-update-nth))))))
 (if (equal (fn-sic-at 0 c) :reverse) (fn-sic-reverse-complete (fn-sic-step c)) c))
(defthm fn-sic-abstract-of-revappend
 (equal (fn-sic-items-abstract (revappend x y))
        (revappend (fn-sic-items-abstract x) (fn-sic-items-abstract y)))
 :hints (("Goal" :induct (revappend x y) :in-theory (enable revappend fn-sic-items-abstract))))
(defthm fn-sic-reverse-complete-is-ordered-result
 (implies (equal (fn-sic-at 0 c) :reverse)
  (let ((d (fn-sic-reverse-complete c)))
   (and (equal (fn-sic-at 0 d) :done)
    (equal (fn-sic-result-abstract d)
     (fn-stmt-ok (revappend (fn-sic-items-abstract (fn-sic-at 16 c))
                           (fn-sic-items-abstract (fn-sic-at 17 c))))))))
 :hints (("Goal" :induct (fn-sic-reverse-complete c)
  :in-theory (e/d (fn-sic-reverse-complete fn-sic-step fn-sic-finish fn-sic-result-abstract
    fn-sic-result fn-stmt-okp fn-stmt-value fn-stmt-ok fn-sic-items-abstract revappend)
   (fn-sic-at fn-sic-put fn-sic-at-is-nth fn-sic-put-is-update-nth)))))


(defun fn-sic-sequence-complete (fuel c)
 (declare (xargs :guard t :verify-guards nil :measure (nfix fuel)))
 (if (not (equal (fn-sic-at 0 c) :head)) c
  (if (not (consp (fn-sic-at 2 c))) (fn-sic-reverse-complete (fn-sic-step c))
   (if (zp fuel) (fn-sic-step c)
    (fn-sic-sequence-complete (1- fuel) (fn-sic-item-complete c))))))

(defthm fn-sic-sequence-complete-is-old-items
 (implies (and (equal (fn-sic-at 0 c) :head) (natp fuel)
    (equal (fn-sic-at 6 c) fuel) (natp (fn-sic-at 3 c)) (natp (fn-sic-at 5 c))
    (fn-cbor-octet-listp (fn-sic-at 2 c)) (equal (fn-sic-at 17 c) nil))
  (let* ((d (fn-sic-sequence-complete fuel c))
         (a (fn-stmt-decode-items-prechecked fuel (fn-sic-at 2 c) (fn-sic-at 5 c))))
   (and (equal (fn-sic-at 0 d) :done)
    (equal (fn-sic-result-abstract d)
     (if (fn-stmt-okp a)
      (fn-stmt-ok (revappend (fn-sic-items-abstract (fn-sic-at 16 c)) (fn-stmt-value a))) a)))))
 :hints (("Goal" :induct (fn-sic-sequence-complete fuel c)
 :expand ((fn-sic-result-abstract (fn-sic-put 0 :done (fn-sic-put 18 '(:error :too-many-items) c))) (:free (fuel) (fn-stmt-decode-items-prechecked fuel (fn-sic-at 2 c) (fn-sic-at 5 c)))
 (fn-stmt-decode-items-prechecked (fn-sic-at 6 c) (fn-sic-at 2 c) (fn-sic-at 5 c)))
  :in-theory (e/d (fn-sic-sequence-complete
    fn-stmt-okp fn-stmt-value fn-stmt-ok fn-stmt-error fn-sic-result
    fn-cbor-result-value fn-cbor-result-rest fn-sic-step fn-sic-error fn-sic-finish revappend fn-sic-items-abstract)
   (fn-sic-item-complete fn-sic-reverse-complete fn-sic-argument-complete fn-sic-bytes-complete
    fn-sic-result-abstract natp posp fn-sic-at fn-sic-put fn-sic-at-is-nth fn-sic-put-is-update-nth
    fn-cbor-octet-listp fn-stmt-decode-items-prechecked fn-cbor-decode-prechecked fn-cbor-result-okp
    fn-sic-argument-complete-is-four-run fn-sic-argument-complete-is-small-run
    fn-sic-argument-complete-is-small-run-total)))))


(local (progn
(defthm fn-sic-preflight-retains-item-chains
 (and (equal (fn-sic-at 16 (fn-sic-preflight-complete c)) (fn-sic-at 16 c))
      (equal (fn-sic-at 17 (fn-sic-preflight-complete c)) (fn-sic-at 17 c)))
 :hints (("Goal" :induct (fn-sic-preflight-complete c)
 :in-theory (e/d (fn-sic-preflight-complete fn-sic-step fn-sic-error fn-sic-finish)
 (fn-sic-at fn-sic-put fn-sic-at-is-nth fn-sic-put-is-update-nth)))))
(defthm fn-sic-sequence-complete-outside-head
 (implies (not (equal (fn-sic-at 0 c) :head))
  (equal (fn-sic-sequence-complete fuel c) c))
 :hints (("Goal" :expand (fn-sic-sequence-complete fuel c))))

))

(local (progn
(defthm fn-sic-preflight-result-has-no-item-abstraction
 (implies (and (equal (fn-sic-at 0 c) :preflight) (natp (fn-sic-at 4 c)))
  (equal (fn-sic-result-abstract (fn-sic-preflight-complete c))
         (fn-sic-result (fn-sic-preflight-complete c))))
 :hints (("Goal" :use ((:instance fn-sic-preflight-is-exact-old-validation))
 :in-theory (e/d (fn-sic-result-abstract fn-stmt-okp fn-stmt-error)
 (fn-sic-result fn-sic-preflight-complete fn-sic-preflight-is-exact-old-validation
  fn-sic-at fn-sic-at-is-nth fn-cbor-at-mostp fn-cbor-octet-listp)))))

))

(local (progn
(defthm fn-sic-old-items-success-is-exact-ok
 (implies (fn-stmt-okp (fn-stmt-decode-items-prechecked fuel xs budget))
  (equal (fn-stmt-ok (fn-stmt-value (fn-stmt-decode-items-prechecked fuel xs budget)))
         (fn-stmt-decode-items-prechecked fuel xs budget)))
 :hints (("Goal" :induct (fn-stmt-decode-items-prechecked fuel xs budget)
 :in-theory (e/d (fn-stmt-decode-items-prechecked fn-stmt-okp fn-stmt-value fn-stmt-ok fn-stmt-error)
 (fn-cbor-decode-prechecked fn-cbor-result-okp fn-cbor-result-rest fn-cbor-result-value)))))

))

(defun fn-sic-complete (c)
 (declare (xargs :guard t :verify-guards nil))
 (let ((d (fn-sic-preflight-complete c)))
  (fn-sic-sequence-complete (nfix (fn-sic-at 6 d)) d)))

(defthm fn-sic-complete-begin-is-exact-old-result
 (implies (and (natp fuel) (natp outer-budget) (natp item-budget))
  (let ((d (fn-sic-complete (fn-sic-begin fuel octets outer-budget item-budget))))
   (and (equal (fn-sic-at 0 d) :done)
    (equal (fn-sic-result-abstract d)
     (fn-stmt-decode-items-bounded-impl fuel octets outer-budget item-budget)))))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-sic-old-items-success-is-exact-ok (xs octets) (budget item-budget)))
 :cases ((and (fn-cbor-at-mostp octets outer-budget) (fn-cbor-octet-listp octets))
 (and (fn-cbor-at-mostp octets outer-budget) (not (fn-cbor-octet-listp octets))))
  :in-theory (e/d (fn-sic-complete fn-sic-begin fn-stmt-decode-items-bounded-impl
    fn-stmt-error fn-sic-result fn-stmt-okp)
   (fn-stmt-value fn-stmt-ok fn-sic-old-items-success-is-exact-ok fn-sic-result-abstract natp fn-sic-at fn-sic-put fn-sic-at-is-nth fn-sic-put-is-update-nth fn-sic-preflight-complete
    fn-sic-sequence-complete fn-cbor-at-mostp fn-cbor-octet-listp
    fn-stmt-decode-items-prechecked)))))



(local (progn
(defthm fn-sic-at-is-nth
 (implies (natp i) (equal (fn-sic-at i x) (nth i x)))
 :hints (("Goal" :induct (fn-sic-at i x)
  :in-theory (enable fn-sic-at nth fn-cbor-ag-car fn-cbor-ag-cdr))))
(defthm fn-sic-put-is-update-nth
 (implies (natp i) (equal (fn-sic-put i v x) (update-nth i v x)))
 :hints (("Goal" :induct (fn-sic-put i v x)
  :in-theory (enable fn-sic-put update-nth fn-cbor-ag-car fn-cbor-ag-cdr))))
(defthm fn-sic-at-of-put
 (implies (and (natp i) (natp j))
  (equal (fn-sic-at i (fn-sic-put j value c))
   (if (equal i j) value (fn-sic-at i c))))
 :hints (("Goal" :in-theory (disable fn-sic-at fn-sic-put))))

))

(local (progn
(defthm fn-sic-at-of-cons
 (implies (natp i)
  (equal (fn-sic-at i (cons head tail))
   (if (zp i) head (fn-sic-at (1- i) tail))))
 :hints (("Goal" :in-theory (enable fn-sic-at fn-cbor-ag-car fn-cbor-ag-cdr))))

))

(defun fn-sic-preflight-complete (c)
 (declare (xargs :guard t :verify-guards nil
  :measure (if (equal (fn-sic-at 0 c) :preflight)
               (+ 1 (acl2-count (fn-sic-at 2 c))) 0)
  :hints (("Goal" :in-theory (e/d (fn-sic-step
    fn-sic-error fn-sic-finish fn-cbor-ag-car fn-cbor-ag-cdr)
   (fn-cbor-octetp fn-stmt-error fn-sic-at fn-sic-put
    fn-sic-at-is-nth fn-sic-put-is-update-nth))))))
 (if (equal (fn-sic-at 0 c) :preflight)
  (fn-sic-preflight-complete (fn-sic-step c)) c))


(defthm fn-sic-preflight-is-exact-old-validation
 (implies (and (equal (fn-sic-at 0 c) :preflight) (natp (fn-sic-at 4 c)))
  (let* ((d (fn-sic-preflight-complete c))
         (limited (not (fn-cbor-at-mostp (fn-sic-at 2 c) (fn-sic-at 4 c))))
         (malformed (or (fn-sic-at 7 c) (not (fn-cbor-octet-listp (fn-sic-at 2 c)))))
         (valid (and (not limited) (not malformed))))
   (and (equal (fn-sic-result d)
               (cond (limited (fn-stmt-error :limit)) (malformed (fn-stmt-error :malformed)) (t :pending)))
        (equal (fn-sic-at 0 d) (if valid :head :done))
        (implies valid (and (equal (fn-sic-at 2 d) (fn-sic-at 1 c)) (equal (fn-sic-at 3 d) 0)))
        (equal (fn-sic-at 1 d) (fn-sic-at 1 c))
        (equal (fn-sic-at 5 d) (fn-sic-at 5 c))
        (equal (fn-sic-at 6 d) (fn-sic-at 6 c)))))
 :hints (("Goal" :induct (fn-sic-preflight-complete c)
  :in-theory (e/d (fn-sic-preflight-complete fn-sic-step fn-sic-result
    fn-sic-error fn-sic-finish fn-cbor-at-mostp fn-cbor-octet-listp nfix)
   (fn-sic-at fn-sic-put fn-sic-at-is-nth fn-sic-put-is-update-nth fn-stmt-error fn-cbor-octetp)))))


(defun fn-sic-preflight-cost (c)
 (declare (xargs :guard t :verify-guards nil
  :measure (if (equal (fn-sic-at 0 c) :preflight)
               (+ 1 (acl2-count (fn-sic-at 2 c))) 0)
  :hints (("Goal" :in-theory (e/d (fn-sic-step fn-sic-error fn-sic-finish)
   (fn-cbor-octetp fn-stmt-error fn-sic-at fn-sic-put
    fn-sic-at-is-nth fn-sic-put-is-update-nth))))))
 (if (equal (fn-sic-at 0 c) :preflight)
  (+ 1 (fn-sic-preflight-cost (fn-sic-step c))) 0))
(defthm fn-sic-preflight-completion-is-paid-run
 (equal (fn-sic-run (fn-sic-preflight-cost c) c) (fn-sic-preflight-complete c))
 :hints (("Goal" :induct (fn-sic-preflight-complete c)
  :in-theory (e/d (fn-sic-preflight-complete fn-sic-preflight-cost fn-sic-run)
   (fn-sic-step fn-sic-at fn-sic-put fn-sic-at-is-nth fn-sic-put-is-update-nth)))))
(defthm fn-sic-preflight-cost-is-profile-bounded
 (implies (equal (fn-sic-at 0 c) :preflight)
  (<= (fn-sic-preflight-cost c) (+ 1 (nfix (fn-sic-at 4 c)))))
 :hints (("Goal" :induct (fn-sic-preflight-complete c)
  :in-theory (e/d (fn-sic-preflight-complete fn-sic-preflight-cost fn-sic-step
    fn-sic-error fn-sic-finish nfix)
   (fn-sic-at fn-sic-put fn-sic-at-is-nth fn-sic-put-is-update-nth fn-cbor-octetp fn-stmt-error)))))


(defun fn-sic-argument-complete (c)
 (declare (xargs :guard t :verify-guards nil
  :measure (if (equal (fn-sic-at 0 c) :argument) (+ 1 (nfix (fn-sic-at 10 c))) 0)
  :hints (("Goal" :in-theory (e/d (fn-sic-step fn-sic-error fn-sic-finish nfix)
   (fn-sic-at fn-sic-put fn-sic-at-is-nth fn-sic-put-is-update-nth fn-stmt-error))))))
 (if (equal (fn-sic-at 0 c) :argument)
  (fn-sic-argument-complete (fn-sic-step c)) c))
(defun fn-sic-bytes-complete (c)
 (declare (xargs :guard t :verify-guards nil
  :measure (if (equal (fn-sic-at 0 c) :bytes) (+ 1 (nfix (fn-sic-at 14 c))) 0)
  :hints (("Goal" :in-theory (e/d (fn-sic-step fn-sic-error fn-sic-finish fn-sic-push nfix)
   (fn-sic-at fn-sic-put fn-sic-at-is-nth fn-sic-put-is-update-nth fn-stmt-error))))))
 (if (equal (fn-sic-at 0 c) :bytes)
  (fn-sic-bytes-complete (fn-sic-step c)) c))
(defun fn-sic-item-complete (c)
 (declare (xargs :guard t :verify-guards nil))
 (let* ((head (fn-sic-step c)) (argument (fn-sic-argument-complete head))
        (checked (if (equal (fn-sic-at 0 argument) :argument-check) (fn-sic-step argument) argument)))
  (fn-sic-bytes-complete checked)))


(defun fn-sic-argument-width (additional)
 (declare (xargs :guard t :verify-guards nil))
 (cond ((equal additional 24) 1) ((equal additional 25) 2) ((equal additional 26) 4) (t 0)))

(local (progn
(defun fn-sic-argument-run (quantum c)
 (declare (xargs :guard t :verify-guards nil :measure (nfix quantum)))
 (if (or (zp quantum) (not (equal (fn-sic-at 0 c) :argument))) c
  (fn-sic-argument-run (1- quantum) (fn-sic-step c))))
(defthm fn-sic-argument-complete-is-small-run
 (implies (and (posp quantum) (<= (nfix (fn-sic-at 10 c)) quantum))
  (equal (fn-sic-argument-complete c) (fn-sic-argument-run quantum c)))
 :hints (("Goal" :induct (fn-sic-argument-run quantum c)
  :in-theory (e/d (fn-sic-argument-complete fn-sic-argument-run fn-sic-step fn-sic-error fn-sic-finish posp nfix)
   (fn-sic-at fn-sic-put fn-sic-at-is-nth fn-sic-put-is-update-nth fn-stmt-error)))))

))

(local (progn
(defthm fn-sic-argument-complete-is-small-run-total
 (implies (and (posp quantum)
               (or (not (equal (fn-sic-at 0 c) :argument))
                   (<= (nfix (fn-sic-at 10 c)) quantum)))
  (equal (fn-sic-argument-complete c) (fn-sic-argument-run quantum c)))
 :hints (("Goal" :use fn-sic-argument-complete-is-small-run
  :in-theory (e/d (fn-sic-argument-complete fn-sic-argument-run)
   (fn-sic-step fn-sic-at fn-sic-argument-complete-is-small-run)))))

))

(local (progn
(defthm fn-sic-argument-complete-is-four-run
 (implies (or (not (equal (fn-sic-at 0 c) :argument))
              (<= (nfix (fn-sic-at 10 c)) 4))
  (equal (fn-sic-argument-complete c) (fn-sic-argument-run 4 c)))
 :hints (("Goal" :use ((:instance fn-sic-argument-complete-is-small-run-total (quantum 4)))
  :in-theory (disable fn-sic-argument-complete fn-sic-argument-run fn-sic-step fn-sic-at
    fn-sic-argument-complete-is-small-run-total))))

))

(defthm fn-sic-argument-complete-is-old-argument
 (implies (and (natp additional) (natp (fn-sic-at 3 c)) (fn-cbor-octet-listp (fn-sic-at 2 c)))
  (let* ((d (fn-sic-argument-complete (fn-sic-argument-start major additional c)))
         (a (fn-cbor-decode-argument additional (fn-sic-at 2 c))))
   (and (equal (fn-sic-at 0 d) (if (fn-cbor-result-okp a) :argument-check :done))
        (equal (fn-sic-result d) (if (fn-cbor-result-okp a) :pending (fn-stmt-error (fn-cbor-result-value a))))
        (implies (fn-cbor-result-okp a)
         (and (equal (fn-sic-at 11 d) (fn-cbor-result-value a))
              (equal (fn-sic-at 2 d) (fn-cbor-result-rest a))
              (equal (fn-sic-at 3 d) (+ (fn-sic-at 3 c) (fn-sic-argument-width additional)))))
        (equal (fn-sic-at 1 d) (fn-sic-at 1 c))
        (equal (fn-sic-at 5 d) (fn-sic-at 5 c))
        (equal (fn-sic-at 6 d) (fn-sic-at 6 c))
        (equal (fn-sic-at 16 d) (fn-sic-at 16 c))
        (equal (fn-sic-at 8 d) major) (equal (fn-sic-at 9 d) additional))))
 :hints (("Goal" :do-not-induct t
  :expand ((:free (d) (fn-sic-argument-run 4 d))
           (:free (d) (fn-sic-argument-run 3 d))
           (:free (d) (fn-sic-argument-run 2 d))
           (:free (d) (fn-sic-argument-run 1 d))
           (:free (d) (fn-sic-argument-run 0 d)))
  :in-theory (e/d (fn-sic-argument-run fn-sic-argument-start fn-sic-argument-width
    fn-sic-step fn-sic-error fn-sic-finish fn-sic-result nfix
    fn-cbor-decode-argument fn-cbor-u16-from fn-cbor-u32-from fn-cbor-octet-listp fn-cbor-octetp
    fn-cbor-result-okp fn-cbor-result-value fn-cbor-result-rest fn-cbor-ok fn-cbor-error
    fn-cbor-ag-car fn-cbor-ag-cdr)
   (fn-sic-argument-complete fn-sic-argument-complete-is-small-run fn-sic-argument-complete-is-small-run-total
    fn-sic-at fn-sic-put fn-sic-at-is-nth fn-sic-put-is-update-nth)))))


(defthm fn-sic-bytes-complete-is-borrowed-span
 (implies (and (equal (fn-sic-at 0 c) :bytes) (natp (fn-sic-at 3 c)) (natp (fn-sic-at 14 c)))
  (let* ((d (fn-sic-bytes-complete c))
         (present (fn-cbor-at-leastp (fn-sic-at 2 c) (fn-sic-at 14 c))))
   (and (equal (fn-sic-at 0 d) (if present :head :done))
        (equal (fn-sic-result d) (if present :pending (fn-stmt-error :truncated)))
        (implies present
         (and (equal (fn-sic-at 2 d) (nthcdr (fn-sic-at 14 c) (fn-sic-at 2 c)))
              (equal (fn-sic-at 3 d) (+ (fn-sic-at 3 c) (fn-sic-at 14 c)))
              (equal (fn-sic-items-abstract (fn-sic-at 16 d))
               (cons (cons :bytes (take (nfix (fn-sic-at 13 c)) (fn-sic-at 15 c)))
                     (fn-sic-items-abstract (fn-sic-at 16 c))))))
        (equal (fn-sic-at 1 d) (fn-sic-at 1 c))
        (equal (fn-sic-at 5 d) (fn-sic-at 5 c))
        (equal (fn-sic-at 6 d) (fn-sic-at 6 c)))))
 :hints (("Goal" :induct (fn-sic-bytes-complete c)
  :in-theory (e/d (fn-sic-bytes-complete fn-sic-step fn-sic-push fn-sic-error fn-sic-finish fn-sic-result
    fn-sic-items-abstract fn-sic-item-abstract fn-cbor-at-leastp nthcdr nfix)
   (fn-sic-at fn-sic-put fn-sic-at-is-nth fn-sic-put-is-update-nth fn-stmt-error fn-cbor-octetp take
    fn-cbor-at-leastp-is-length-lower-bound)))))


(local (progn
(defthm fn-sic-argument-complete-outside-phase
 (implies (not (equal (fn-sic-at 0 c) :argument)) (equal (fn-sic-argument-complete c) c))
 :hints (("Goal" :expand (fn-sic-argument-complete c))))
(defthm fn-sic-bytes-complete-outside-phase
 (implies (not (equal (fn-sic-at 0 c) :bytes)) (equal (fn-sic-bytes-complete c) c))
 :hints (("Goal" :expand (fn-sic-bytes-complete c))))

))

(local (progn
(defthm fn-sic-old-argument-has-natural-value-and-octet-rest
 (implies (and (natp additional) (fn-cbor-octet-listp xs)
               (fn-cbor-result-okp (fn-cbor-decode-argument additional xs)))
  (and (natp (fn-cbor-result-value (fn-cbor-decode-argument additional xs)))
       (<= (fn-cbor-result-value (fn-cbor-decode-argument additional xs)) 4294967295)
       (fn-cbor-octet-listp (fn-cbor-result-rest (fn-cbor-decode-argument additional xs)))))
 :hints (("Goal" :do-not-induct t
  :in-theory (enable fn-cbor-decode-argument fn-cbor-result-okp fn-cbor-result-value fn-cbor-result-rest
    fn-cbor-ok fn-cbor-error fn-cbor-ag-car fn-cbor-ag-cdr fn-cbor-u16-from fn-cbor-u32-from
    fn-cbor-octet-listp fn-cbor-octetp))))

))

(defthm fn-sic-item-complete-is-old-item
 (implies (and (equal (fn-sic-at 0 c) :head)
               (consp (fn-sic-at 2 c)) (fn-cbor-octet-listp (fn-sic-at 2 c))
               (natp (fn-sic-at 3 c)) (posp (fn-sic-at 6 c)) (natp (fn-sic-at 5 c)))
  (let* ((d (fn-sic-item-complete c))
         (a (fn-cbor-decode-prechecked (fn-sic-at 2 c) (fn-sic-at 5 c))))
   (and (equal (fn-sic-at 0 d) (if (fn-cbor-result-okp a) :head :done))
        (equal (fn-sic-result d) (if (fn-cbor-result-okp a) :pending (fn-stmt-error (fn-cbor-result-value a))))
        (implies (fn-cbor-result-okp a)
         (and (equal (fn-sic-at 2 d) (fn-cbor-result-rest a))
              (natp (fn-sic-at 3 d))
              (equal (fn-sic-items-abstract (fn-sic-at 16 d))
               (cons (fn-cbor-result-value a) (fn-sic-items-abstract (fn-sic-at 16 c))))))
        (equal (fn-sic-at 1 d) (fn-sic-at 1 c))
        (equal (fn-sic-at 5 d) (fn-sic-at 5 c))
        (equal (fn-sic-at 6 d) (1- (fn-sic-at 6 c))))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-sic-old-argument-has-natural-value-and-octet-rest
    (additional (car (fn-sic-at 2 c))) (xs (cdr (fn-sic-at 2 c))))
   (:instance fn-sic-old-argument-has-natural-value-and-octet-rest
    (additional (- (car (fn-sic-at 2 c)) 64)) (xs (cdr (fn-sic-at 2 c)))))
  :in-theory (e/d (fn-sic-item-complete fn-sic-step fn-sic-error fn-sic-finish fn-sic-push fn-sic-result
    fn-sic-item-abstract fn-sic-items-abstract nfix posp
    fn-cbor-decode-prechecked fn-cbor-decode-unsigned fn-cbor-decode-bytes-bounded
    fn-cbor-octet-listp fn-cbor-octetp fn-cbor-result-okp fn-cbor-result-value fn-cbor-result-rest
    fn-cbor-ok fn-cbor-error fn-cbor-ag-car fn-cbor-ag-cdr)
   (fn-sic-at fn-sic-put fn-sic-at-is-nth fn-sic-put-is-update-nth
    fn-sic-argument-complete fn-sic-argument-start fn-sic-argument-run fn-sic-bytes-complete
    fn-sic-argument-complete-is-four-run fn-sic-argument-complete-is-small-run
    fn-sic-argument-complete-is-small-run-total fn-cbor-decode-argument take
    fn-cbor-at-leastp-is-length-lower-bound fn-stmt-error)))))


(local (progn
(defthm fn-sic-octet-listp-of-nthcdr
 (implies (fn-cbor-octet-listp xs) (fn-cbor-octet-listp (nthcdr n xs)))
 :hints (("Goal" :induct (nthcdr n xs) :in-theory (enable nthcdr fn-cbor-octet-listp))))

))

(local (progn
(defthm fn-sic-old-item-has-octet-rest
 (implies (and (fn-cbor-octet-listp xs) (natp budget)
               (fn-cbor-result-okp (fn-cbor-decode-prechecked xs budget)))
  (fn-cbor-octet-listp (fn-cbor-result-rest (fn-cbor-decode-prechecked xs budget))))
 :hints (("Goal"  :do-not-induct t
 :use ((:instance fn-sic-old-argument-has-natural-value-and-octet-rest (additional (car xs)) (xs (cdr xs)))
 (:instance fn-sic-old-argument-has-natural-value-and-octet-rest (additional (- (car xs) 64)) (xs (cdr xs))))
 :in-theory (e/d (fn-cbor-decode-prechecked fn-cbor-decode-unsigned fn-cbor-decode-bytes-bounded
    fn-cbor-result-okp fn-cbor-result-rest fn-cbor-ok fn-cbor-error fn-cbor-octet-listp)
    (fn-cbor-decode-argument fn-cbor-at-leastp fn-cbor-at-leastp-is-length-lower-bound take nthcdr)))))

))

(local (progn
(defthm fn-sic-argument-complete-retains-ordered-items
 (equal (fn-sic-at 17 (fn-sic-argument-complete c)) (fn-sic-at 17 c))
 :hints (("Goal" :induct (fn-sic-argument-complete c)
 :in-theory (e/d (fn-sic-argument-complete fn-sic-step fn-sic-error fn-sic-finish)
 (fn-sic-at fn-sic-put fn-sic-at-is-nth fn-sic-put-is-update-nth fn-sic-argument-complete-is-four-run fn-sic-argument-complete-is-small-run fn-sic-argument-complete-is-small-run-total)))))
(defthm fn-sic-bytes-complete-retains-ordered-items
 (equal (fn-sic-at 17 (fn-sic-bytes-complete c)) (fn-sic-at 17 c))
 :hints (("Goal" :induct (fn-sic-bytes-complete c)
 :in-theory (e/d (fn-sic-bytes-complete fn-sic-step fn-sic-error fn-sic-finish fn-sic-push)
 (fn-sic-at fn-sic-put fn-sic-at-is-nth fn-sic-put-is-update-nth fn-sic-argument-complete-is-four-run fn-sic-argument-complete-is-small-run fn-sic-argument-complete-is-small-run-total)))))

))

(local (progn
(defthm fn-sic-item-complete-retains-ordered-items
 (implies (equal (fn-sic-at 0 c) :head)
  (equal (fn-sic-at 17 (fn-sic-item-complete c)) (fn-sic-at 17 c)))
 :hints (("Goal" :in-theory (e/d (fn-sic-item-complete fn-sic-step fn-sic-error fn-sic-finish fn-sic-push fn-sic-argument-start)
 (fn-sic-at fn-sic-put fn-sic-at-is-nth fn-sic-put-is-update-nth fn-sic-argument-complete fn-sic-bytes-complete
 fn-sic-argument-complete-is-four-run fn-sic-argument-complete-is-small-run fn-sic-argument-complete-is-small-run-total)))))

))

(local (progn
(defthm fn-sic-item-complete-retains-octet-domain
 (implies (and (equal (fn-sic-at 0 c) :head)
   (consp (fn-sic-at 2 c)) (fn-cbor-octet-listp (fn-sic-at 2 c))
   (natp (fn-sic-at 3 c)) (posp (fn-sic-at 6 c)) (natp (fn-sic-at 5 c))
   (equal (fn-sic-at 0 (fn-sic-item-complete c)) :head))
  (fn-cbor-octet-listp (fn-sic-at 2 (fn-sic-item-complete c))))
 :hints (("Goal" :use ((:instance fn-sic-item-complete-is-old-item)
   (:instance fn-sic-old-item-has-octet-rest (xs (fn-sic-at 2 c)) (budget (fn-sic-at 5 c))))
 :in-theory (disable fn-sic-item-complete fn-sic-item-complete-is-old-item fn-sic-at
   fn-sic-old-item-has-octet-rest fn-cbor-octet-listp fn-cbor-result-rest fn-cbor-result-okp))))

))

(local (progn
(defthm fn-sic-error-has-exact-abstract-result
 (equal (fn-sic-result-abstract (fn-sic-error code c)) (fn-stmt-error code))
 :hints (("Goal" :in-theory (e/d (fn-sic-result-abstract fn-sic-result fn-sic-error fn-sic-finish
    fn-stmt-okp fn-stmt-error)
    (fn-sic-at fn-sic-put fn-sic-at-is-nth fn-sic-put-is-update-nth)))))
(defthm fn-sic-item-error-has-exact-abstract-result
 (implies (and (equal (fn-sic-at 0 c) :head)
   (consp (fn-sic-at 2 c)) (fn-cbor-octet-listp (fn-sic-at 2 c))
   (natp (fn-sic-at 3 c)) (posp (fn-sic-at 6 c)) (natp (fn-sic-at 5 c))
   (not (fn-cbor-result-okp (fn-cbor-decode-prechecked (fn-sic-at 2 c) (fn-sic-at 5 c)))))
  (equal (fn-sic-result-abstract (fn-sic-item-complete c))
   (fn-stmt-error (fn-cbor-result-value (fn-cbor-decode-prechecked (fn-sic-at 2 c) (fn-sic-at 5 c))))))
 :hints (("Goal" :use ((:instance fn-sic-item-complete-is-old-item))
 :in-theory (e/d (fn-sic-result-abstract fn-stmt-okp fn-stmt-error)
 (fn-sic-item-complete fn-sic-at fn-sic-at-is-nth fn-sic-result fn-sic-item-complete-is-old-item)))))

))

(defun fn-sic-reverse-complete (c)
 (declare (xargs :guard t :verify-guards nil
  :measure (if (equal (fn-sic-at 0 c) :reverse) (+ 1 (acl2-count (fn-sic-at 16 c))) 0)
  :hints (("Goal" :in-theory (e/d (fn-sic-step fn-sic-finish)
   (fn-sic-at fn-sic-put fn-sic-at-is-nth fn-sic-put-is-update-nth))))))
 (if (equal (fn-sic-at 0 c) :reverse) (fn-sic-reverse-complete (fn-sic-step c)) c))
(defthm fn-sic-abstract-of-revappend
 (equal (fn-sic-items-abstract (revappend x y))
        (revappend (fn-sic-items-abstract x) (fn-sic-items-abstract y)))
 :hints (("Goal" :induct (revappend x y) :in-theory (enable revappend fn-sic-items-abstract))))
(defthm fn-sic-reverse-complete-is-ordered-result
 (implies (equal (fn-sic-at 0 c) :reverse)
  (let ((d (fn-sic-reverse-complete c)))
   (and (equal (fn-sic-at 0 d) :done)
    (equal (fn-sic-result-abstract d)
     (fn-stmt-ok (revappend (fn-sic-items-abstract (fn-sic-at 16 c))
                           (fn-sic-items-abstract (fn-sic-at 17 c))))))))
 :hints (("Goal" :induct (fn-sic-reverse-complete c)
  :in-theory (e/d (fn-sic-reverse-complete fn-sic-step fn-sic-finish fn-sic-result-abstract
    fn-sic-result fn-stmt-okp fn-stmt-value fn-stmt-ok fn-sic-items-abstract revappend)
   (fn-sic-at fn-sic-put fn-sic-at-is-nth fn-sic-put-is-update-nth)))))


(defun fn-sic-sequence-complete (fuel c)
 (declare (xargs :guard t :verify-guards nil :measure (nfix fuel)))
 (if (not (equal (fn-sic-at 0 c) :head)) c
  (if (not (consp (fn-sic-at 2 c))) (fn-sic-reverse-complete (fn-sic-step c))
   (if (zp fuel) (fn-sic-step c)
    (fn-sic-sequence-complete (1- fuel) (fn-sic-item-complete c))))))

(defthm fn-sic-sequence-complete-is-old-items
 (implies (and (equal (fn-sic-at 0 c) :head) (natp fuel)
    (equal (fn-sic-at 6 c) fuel) (natp (fn-sic-at 3 c)) (natp (fn-sic-at 5 c))
    (fn-cbor-octet-listp (fn-sic-at 2 c)) (equal (fn-sic-at 17 c) nil))
  (let* ((d (fn-sic-sequence-complete fuel c))
         (a (fn-stmt-decode-items-prechecked fuel (fn-sic-at 2 c) (fn-sic-at 5 c))))
   (and (equal (fn-sic-at 0 d) :done)
    (equal (fn-sic-result-abstract d)
     (if (fn-stmt-okp a)
      (fn-stmt-ok (revappend (fn-sic-items-abstract (fn-sic-at 16 c)) (fn-stmt-value a))) a)))))
 :hints (("Goal" :induct (fn-sic-sequence-complete fuel c)
 :expand ((fn-sic-result-abstract (fn-sic-put 0 :done (fn-sic-put 18 '(:error :too-many-items) c))) (:free (fuel) (fn-stmt-decode-items-prechecked fuel (fn-sic-at 2 c) (fn-sic-at 5 c)))
 (fn-stmt-decode-items-prechecked (fn-sic-at 6 c) (fn-sic-at 2 c) (fn-sic-at 5 c)))
  :in-theory (e/d (fn-sic-sequence-complete
    fn-stmt-okp fn-stmt-value fn-stmt-ok fn-stmt-error fn-sic-result
    fn-cbor-result-value fn-cbor-result-rest fn-sic-step fn-sic-error fn-sic-finish revappend fn-sic-items-abstract)
   (fn-sic-item-complete fn-sic-reverse-complete fn-sic-argument-complete fn-sic-bytes-complete
    fn-sic-result-abstract natp posp fn-sic-at fn-sic-put fn-sic-at-is-nth fn-sic-put-is-update-nth
    fn-cbor-octet-listp fn-stmt-decode-items-prechecked fn-cbor-decode-prechecked fn-cbor-result-okp
    fn-sic-argument-complete-is-four-run fn-sic-argument-complete-is-small-run
    fn-sic-argument-complete-is-small-run-total)))))


(local (progn
(defthm fn-sic-preflight-retains-item-chains
 (and (equal (fn-sic-at 16 (fn-sic-preflight-complete c)) (fn-sic-at 16 c))
      (equal (fn-sic-at 17 (fn-sic-preflight-complete c)) (fn-sic-at 17 c)))
 :hints (("Goal" :induct (fn-sic-preflight-complete c)
 :in-theory (e/d (fn-sic-preflight-complete fn-sic-step fn-sic-error fn-sic-finish)
 (fn-sic-at fn-sic-put fn-sic-at-is-nth fn-sic-put-is-update-nth)))))
(defthm fn-sic-sequence-complete-outside-head
 (implies (not (equal (fn-sic-at 0 c) :head))
  (equal (fn-sic-sequence-complete fuel c) c))
 :hints (("Goal" :expand (fn-sic-sequence-complete fuel c))))

))

(local (progn
(defthm fn-sic-preflight-result-has-no-item-abstraction
 (implies (and (equal (fn-sic-at 0 c) :preflight) (natp (fn-sic-at 4 c)))
  (equal (fn-sic-result-abstract (fn-sic-preflight-complete c))
         (fn-sic-result (fn-sic-preflight-complete c))))
 :hints (("Goal" :use ((:instance fn-sic-preflight-is-exact-old-validation))
 :in-theory (e/d (fn-sic-result-abstract fn-stmt-okp fn-stmt-error)
 (fn-sic-result fn-sic-preflight-complete fn-sic-preflight-is-exact-old-validation
  fn-sic-at fn-sic-at-is-nth fn-cbor-at-mostp fn-cbor-octet-listp)))))

))

(local (progn
(defthm fn-sic-old-items-success-is-exact-ok
 (implies (fn-stmt-okp (fn-stmt-decode-items-prechecked fuel xs budget))
  (equal (fn-stmt-ok (fn-stmt-value (fn-stmt-decode-items-prechecked fuel xs budget)))
         (fn-stmt-decode-items-prechecked fuel xs budget)))
 :hints (("Goal" :induct (fn-stmt-decode-items-prechecked fuel xs budget)
 :in-theory (e/d (fn-stmt-decode-items-prechecked fn-stmt-okp fn-stmt-value fn-stmt-ok fn-stmt-error)
 (fn-cbor-decode-prechecked fn-cbor-result-okp fn-cbor-result-rest fn-cbor-result-value)))))

))

(defun fn-sic-complete (c)
 (declare (xargs :guard t :verify-guards nil))
 (let ((d (fn-sic-preflight-complete c)))
  (fn-sic-sequence-complete (nfix (fn-sic-at 6 d)) d)))

(defthm fn-sic-complete-begin-is-exact-old-result
 (implies (and (natp fuel) (natp outer-budget) (natp item-budget))
  (let ((d (fn-sic-complete (fn-sic-begin fuel octets outer-budget item-budget))))
   (and (equal (fn-sic-at 0 d) :done)
    (equal (fn-sic-result-abstract d)
     (fn-stmt-decode-items-bounded-impl fuel octets outer-budget item-budget)))))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-sic-old-items-success-is-exact-ok (xs octets) (budget item-budget)))
 :cases ((and (fn-cbor-at-mostp octets outer-budget) (fn-cbor-octet-listp octets))
 (and (fn-cbor-at-mostp octets outer-budget) (not (fn-cbor-octet-listp octets))))
  :in-theory (e/d (fn-sic-complete fn-sic-begin fn-stmt-decode-items-bounded-impl
    fn-stmt-error fn-sic-result fn-stmt-okp)
   (fn-stmt-value fn-stmt-ok fn-sic-old-items-success-is-exact-ok fn-sic-result-abstract natp fn-sic-at fn-sic-put fn-sic-at-is-nth fn-sic-put-is-update-nth fn-sic-preflight-complete
    fn-sic-sequence-complete fn-cbor-at-mostp fn-cbor-octet-listp
    fn-stmt-decode-items-prechecked)))))


(defun fn-sic-argument-cost (c)
 (declare (xargs :guard t :verify-guards nil
 :measure (if (equal (fn-sic-at 0 c) :argument) (+ 1 (nfix (fn-sic-at 10 c))) 0)
 :hints (("Goal" :in-theory (e/d (fn-sic-step fn-sic-error fn-sic-finish fn-sic-push nfix)
 (fn-sic-at fn-sic-put fn-sic-at-is-nth fn-sic-put-is-update-nth
 fn-sic-argument-complete-is-four-run fn-sic-argument-complete-is-small-run fn-sic-argument-complete-is-small-run-total))))))
 (if (equal (fn-sic-at 0 c) :argument) (+ 1 (fn-sic-argument-cost (fn-sic-step c))) 0))
(defthm fn-sic-argument-cost-is-natural
 (natp (fn-sic-argument-cost c)) :rule-classes (:rewrite :type-prescription)
 :hints (("Goal" :induct (fn-sic-argument-cost c) :in-theory (enable fn-sic-argument-cost))))
(defthm fn-sic-argument-completion-is-paid-run
 (equal (fn-sic-run (fn-sic-argument-cost c) c) (fn-sic-argument-complete c))
 :hints (("Goal" :induct (fn-sic-argument-complete c)
 :in-theory (e/d (fn-sic-argument-complete fn-sic-argument-cost fn-sic-run)
 (fn-sic-step fn-sic-at fn-sic-put fn-sic-at-is-nth fn-sic-put-is-update-nth
 fn-sic-argument-complete-is-four-run fn-sic-argument-complete-is-small-run fn-sic-argument-complete-is-small-run-total)))))
(defun fn-sic-bytes-cost (c)
 (declare (xargs :guard t :verify-guards nil
 :measure (if (equal (fn-sic-at 0 c) :bytes) (+ 1 (nfix (fn-sic-at 14 c))) 0)
 :hints (("Goal" :in-theory (e/d (fn-sic-step fn-sic-error fn-sic-finish fn-sic-push nfix)
 (fn-sic-at fn-sic-put fn-sic-at-is-nth fn-sic-put-is-update-nth
 fn-sic-argument-complete-is-four-run fn-sic-argument-complete-is-small-run fn-sic-argument-complete-is-small-run-total))))))
 (if (equal (fn-sic-at 0 c) :bytes) (+ 1 (fn-sic-bytes-cost (fn-sic-step c))) 0))
(defthm fn-sic-bytes-cost-is-natural
 (natp (fn-sic-bytes-cost c)) :rule-classes (:rewrite :type-prescription)
 :hints (("Goal" :induct (fn-sic-bytes-cost c) :in-theory (enable fn-sic-bytes-cost))))
(defthm fn-sic-bytes-completion-is-paid-run
 (equal (fn-sic-run (fn-sic-bytes-cost c) c) (fn-sic-bytes-complete c))
 :hints (("Goal" :induct (fn-sic-bytes-complete c)
 :in-theory (e/d (fn-sic-bytes-complete fn-sic-bytes-cost fn-sic-run)
 (fn-sic-step fn-sic-at fn-sic-put fn-sic-at-is-nth fn-sic-put-is-update-nth
 fn-sic-argument-complete-is-four-run fn-sic-argument-complete-is-small-run fn-sic-argument-complete-is-small-run-total)))))
(defun fn-sic-reverse-cost (c)
 (declare (xargs :guard t :verify-guards nil
 :measure (if (equal (fn-sic-at 0 c) :reverse) (+ 1 (acl2-count (fn-sic-at 16 c))) 0)
 :hints (("Goal" :in-theory (e/d (fn-sic-step fn-sic-error fn-sic-finish fn-sic-push nfix)
 (fn-sic-at fn-sic-put fn-sic-at-is-nth fn-sic-put-is-update-nth
 fn-sic-argument-complete-is-four-run fn-sic-argument-complete-is-small-run fn-sic-argument-complete-is-small-run-total))))))
 (if (equal (fn-sic-at 0 c) :reverse) (+ 1 (fn-sic-reverse-cost (fn-sic-step c))) 0))
(defthm fn-sic-reverse-cost-is-natural
 (natp (fn-sic-reverse-cost c)) :rule-classes (:rewrite :type-prescription)
 :hints (("Goal" :induct (fn-sic-reverse-cost c) :in-theory (enable fn-sic-reverse-cost))))
(defthm fn-sic-reverse-completion-is-paid-run
 (equal (fn-sic-run (fn-sic-reverse-cost c) c) (fn-sic-reverse-complete c))
 :hints (("Goal" :induct (fn-sic-reverse-complete c)
 :in-theory (e/d (fn-sic-reverse-complete fn-sic-reverse-cost fn-sic-run)
 (fn-sic-step fn-sic-at fn-sic-put fn-sic-at-is-nth fn-sic-put-is-update-nth
 fn-sic-argument-complete-is-four-run fn-sic-argument-complete-is-small-run fn-sic-argument-complete-is-small-run-total)))))


(defthm fn-sic-one-step-is-paid-run
 (equal (fn-sic-run 1 c) (fn-sic-step c))
 :hints (("Goal" :in-theory (enable fn-sic-run))))
(defun fn-sic-item-cost (c)
 (declare (xargs :guard t :verify-guards nil))
 (let* ((head (fn-sic-step c)) (argument (fn-sic-argument-complete head))
        (checkp (equal (fn-sic-at 0 argument) :argument-check))
        (checked (if checkp (fn-sic-step argument) argument)))
  (+ 1 (fn-sic-argument-cost head) (if checkp 1 0) (fn-sic-bytes-cost checked))))
(defthm fn-sic-item-cost-is-natural
 (natp (fn-sic-item-cost c)) :rule-classes (:rewrite :type-prescription)
 :hints (("Goal" :in-theory (enable fn-sic-item-cost))))
(defthm fn-sic-item-completion-is-paid-run
 (equal (fn-sic-run (fn-sic-item-cost c) c) (fn-sic-item-complete c))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-sic-run-is-resumable (a 1)
   (b (+ (fn-sic-argument-cost (fn-sic-step c))
      (if (equal (fn-sic-at 0 (fn-sic-argument-complete (fn-sic-step c))) :argument-check) 1 0)
      (fn-sic-bytes-cost (if (equal (fn-sic-at 0 (fn-sic-argument-complete (fn-sic-step c))) :argument-check)
       (fn-sic-step (fn-sic-argument-complete (fn-sic-step c))) (fn-sic-argument-complete (fn-sic-step c)))))))
  (:instance fn-sic-run-is-resumable (c (fn-sic-step c)) (a (fn-sic-argument-cost (fn-sic-step c)))
   (b (+ (if (equal (fn-sic-at 0 (fn-sic-argument-complete (fn-sic-step c))) :argument-check) 1 0)
      (fn-sic-bytes-cost (if (equal (fn-sic-at 0 (fn-sic-argument-complete (fn-sic-step c))) :argument-check)
       (fn-sic-step (fn-sic-argument-complete (fn-sic-step c))) (fn-sic-argument-complete (fn-sic-step c)))))))
  (:instance fn-sic-run-is-resumable (c (fn-sic-argument-complete (fn-sic-step c)))
   (a (if (equal (fn-sic-at 0 (fn-sic-argument-complete (fn-sic-step c))) :argument-check) 1 0))
   (b (fn-sic-bytes-cost (if (equal (fn-sic-at 0 (fn-sic-argument-complete (fn-sic-step c))) :argument-check)
       (fn-sic-step (fn-sic-argument-complete (fn-sic-step c))) (fn-sic-argument-complete (fn-sic-step c)))))))
 :in-theory (e/d (fn-sic-item-cost fn-sic-item-complete)
 (fn-sic-run-is-resumable fn-sic-run fn-sic-step fn-sic-at fn-sic-argument-complete fn-sic-bytes-complete
 fn-sic-argument-cost fn-sic-bytes-cost fn-sic-argument-complete-is-four-run
 fn-sic-argument-complete-is-small-run fn-sic-argument-complete-is-small-run-total)))))


(defun fn-sic-sequence-cost (fuel c)
 (declare (xargs :guard t :verify-guards nil :measure (nfix fuel)))
 (if (not (equal (fn-sic-at 0 c) :head)) 0
  (if (not (consp (fn-sic-at 2 c))) (+ 1 (fn-sic-reverse-cost (fn-sic-step c)))
   (if (zp fuel) 1
    (+ (fn-sic-item-cost c) (fn-sic-sequence-cost (1- fuel) (fn-sic-item-complete c)))))))
(defthm fn-sic-sequence-cost-is-natural
 (natp (fn-sic-sequence-cost fuel c)) :rule-classes (:rewrite :type-prescription)
 :hints (("Goal" :induct (fn-sic-sequence-cost fuel c) :in-theory (enable fn-sic-sequence-cost))))
(defthm fn-sic-sequence-completion-is-paid-run
 (equal (fn-sic-run (fn-sic-sequence-cost fuel c) c) (fn-sic-sequence-complete fuel c))
 :hints (("Goal" :induct (fn-sic-sequence-complete fuel c)
 :in-theory (e/d (fn-sic-sequence-cost fn-sic-sequence-complete)
 (fn-sic-run fn-sic-step fn-sic-at fn-sic-item-complete fn-sic-reverse-complete fn-sic-item-cost fn-sic-reverse-cost)))))


(defthm fn-sic-preflight-cost-is-natural
 (natp (fn-sic-preflight-cost c)) :rule-classes (:rewrite :type-prescription)
 :hints (("Goal" :induct (fn-sic-preflight-cost c) :in-theory (enable fn-sic-preflight-cost))))
(defun fn-sic-completion-cost (c)
 (declare (xargs :guard t :verify-guards nil))
 (let ((d (fn-sic-preflight-complete c)))
  (+ (fn-sic-preflight-cost c) (fn-sic-sequence-cost (nfix (fn-sic-at 6 d)) d))))
(defthm fn-sic-completion-cost-is-natural
 (natp (fn-sic-completion-cost c)) :rule-classes (:rewrite :type-prescription)
 :hints (("Goal" :in-theory (enable fn-sic-completion-cost))))
(defthm fn-sic-completion-is-paid-run
 (equal (fn-sic-run (fn-sic-completion-cost c) c) (fn-sic-complete c))
 :hints (("Goal" :in-theory (e/d (fn-sic-completion-cost fn-sic-complete)
 (fn-sic-run fn-sic-at fn-sic-preflight-complete fn-sic-preflight-cost
 fn-sic-sequence-complete fn-sic-sequence-cost)))))
(defthm fn-sic-paid-begin-completion-is-exact-old-result
 (implies (and (natp fuel) (natp outer-budget) (natp item-budget))
  (let* ((c (fn-sic-begin fuel octets outer-budget item-budget))
         (d (fn-sic-run (fn-sic-completion-cost c) c)))
   (and (equal (fn-sic-at 0 d) :done)
    (equal (fn-sic-result-abstract d)
     (fn-stmt-decode-items-bounded-impl fuel octets outer-budget item-budget)))))
 :hints (("Goal" :in-theory (disable fn-sic-complete fn-sic-begin fn-sic-completion-cost
 fn-sic-run fn-sic-at fn-sic-result-abstract fn-stmt-decode-items-bounded-impl))))


(in-theory (disable fn-sic-item-abstract fn-sic-items-abstract fn-sic-result-abstract
 fn-sic-preflight-complete fn-sic-preflight-cost fn-sic-argument-complete
 fn-sic-bytes-complete fn-sic-item-complete fn-sic-argument-width fn-sic-reverse-complete
 fn-sic-sequence-complete fn-sic-complete fn-sic-argument-cost fn-sic-bytes-cost fn-sic-reverse-cost
 fn-sic-item-cost fn-sic-sequence-cost fn-sic-completion-cost))
