; Successful paid nested statement decode retains exact borrowed source spans.
; All parser/old-reference support is local. No runtime validation is served.
(in-package "ACL2")
(include-book "statement-items-cursor-refinement")

(defun fn-sic-span-itemp (item source)
 (declare (xargs :guard t :verify-guards nil))
 (if (equal (fn-cbor-ag-car item) :bytes)
  (let ((start (fn-sic-at 1 item)) (count (fn-sic-at 2 item)))
   (and (true-listp item) (equal (len item) 4)
    (natp start) (natp count) (<= (+ start count) (len source))
    (equal (fn-sic-at 3 item) (nthcdr start source))))
  (and (consp item) (equal (car item) :uint) (natp (cdr item)) (<= (cdr item) 4294967295))))

(defun fn-sic-span-item-listp (items source)
 (declare (xargs :guard t :verify-guards nil))
 (if (consp items)
  (and (fn-sic-span-itemp (car items) source) (fn-sic-span-item-listp (cdr items) source))
  (equal items nil)))

(local (progn
(defthm fn-sic-fixed-four-list-has-shape
 (and (true-listp (list a b c d)) (equal (len (list a b c d)) 4))
 :hints (("Goal" :in-theory (enable true-listp len))))


(defthm fn-sic-nthcdr-is-composable
 (implies (and (natp a) (natp b))
  (equal (nthcdr (+ a b) xs) (nthcdr b (nthcdr a xs))))
 :hints (("Goal" :induct (nthcdr a xs) :in-theory (enable nthcdr))))

(defthm fn-sic-length-of-nthcdr
 (equal (len (nthcdr n xs)) (nfix (- (len xs) (nfix n))))
 :hints (("Goal" :induct (nthcdr n xs) :in-theory (enable nthcdr len nfix))))

(defun fn-sic-old-item-borrow (pos xs budget)
 (declare (xargs :guard t :verify-guards nil))
 (let* ((h (fn-cbor-ag-car xs)) (additional (if (< (nfix h) 32) h (- (nfix h) 64)))
        (arg (fn-cbor-decode-argument additional (fn-cbor-ag-cdr xs))))
  (if (< (nfix h) 32) (fn-cbor-result-value (fn-cbor-decode-prechecked xs budget))
   (list :bytes (+ 1 (nfix pos) (fn-sic-argument-width additional))
    (fn-cbor-result-value arg) (fn-cbor-result-rest arg)))))

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

(defthm fn-sic-at-of-cons
 (implies (natp i)
  (equal (fn-sic-at i (cons head tail))
   (if (zp i) head (fn-sic-at (1- i) tail))))
 :hints (("Goal" :in-theory (enable fn-sic-at fn-cbor-ag-car fn-cbor-ag-cdr))))

(defthm fn-sic-bytes-complete-has-exact-raw-span
 (implies (and (equal (fn-sic-at 0 c) :bytes)
   (fn-cbor-at-leastp (fn-sic-at 2 c) (nfix (fn-sic-at 14 c))))
  (equal (fn-sic-at 16 (fn-sic-bytes-complete c))
   (cons (list :bytes (nfix (fn-sic-at 12 c)) (nfix (fn-sic-at 13 c)) (fn-sic-at 15 c))
         (fn-sic-at 16 c))))
 :hints (("Goal" :induct (fn-sic-bytes-complete c)
 :in-theory (e/d (fn-sic-bytes-complete fn-sic-step fn-sic-push fn-sic-error fn-sic-finish
    fn-cbor-at-leastp nfix)
 (fn-sic-at fn-sic-put fn-sic-at-is-nth fn-sic-put-is-update-nth
 fn-cbor-at-leastp-is-length-lower-bound)))))

(defthm fn-sic-consp-has-positive-length
 (implies (consp xs) (< 0 (len xs))) :rule-classes :linear
 :hints (("Goal" :in-theory (enable len))))

(defthm fn-sic-old-argument-has-exact-geometry
 (implies (and (natp additional) (fn-cbor-octet-listp xs)
               (fn-cbor-result-okp (fn-cbor-decode-argument additional xs)))
  (and (equal (fn-cbor-result-rest (fn-cbor-decode-argument additional xs))
       (nthcdr (fn-sic-argument-width additional) xs))
       (<= (fn-sic-argument-width additional) (len xs))))
 :hints (("Goal" :do-not-induct t
 :in-theory (enable fn-cbor-decode-argument fn-sic-argument-width nthcdr len
   fn-cbor-result-okp fn-cbor-result-rest fn-cbor-ok fn-cbor-error fn-cbor-octet-listp
   fn-cbor-ag-car fn-cbor-ag-cdr))))

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

(defthm fn-sic-argument-complete-outside-phase
 (implies (not (equal (fn-sic-at 0 c) :argument)) (equal (fn-sic-argument-complete c) c))
 :hints (("Goal" :expand (fn-sic-argument-complete c))))

(defthm fn-sic-bytes-complete-outside-phase
 (implies (not (equal (fn-sic-at 0 c) :bytes)) (equal (fn-sic-bytes-complete c) c))
 :hints (("Goal" :expand (fn-sic-bytes-complete c))))

(defthm fn-sic-item-complete-has-exact-raw-item-geometry
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
              (let* ((h (car (fn-sic-at 2 c)))
                     (additional (if (< h 32) h (- h 64)))
                     (arg (fn-cbor-decode-argument additional (cdr (fn-sic-at 2 c))))
                     (start (+ 1 (fn-sic-at 3 c) (fn-sic-argument-width additional))))
                (and (equal (fn-sic-at 3 d) (+ start (if (< h 32) 0 (fn-cbor-result-value arg))))
                 (equal (fn-sic-at 16 d)
                  (cons (if (< h 32) (fn-cbor-result-value a)
                   (list :bytes start (fn-cbor-result-value arg) (fn-cbor-result-rest arg)))
                   (fn-sic-at 16 c)))))))
        (equal (fn-sic-at 1 d) (fn-sic-at 1 c))
        (equal (fn-sic-at 5 d) (fn-sic-at 5 c))
        (equal (fn-sic-at 6 d) (1- (fn-sic-at 6 c))))))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-sic-old-argument-has-natural-value-and-octet-rest
    (additional (car (fn-sic-at 2 c))) (xs (cdr (fn-sic-at 2 c))))
   (:instance fn-sic-old-argument-has-natural-value-and-octet-rest
    (additional (- (car (fn-sic-at 2 c)) 64)) (xs (cdr (fn-sic-at 2 c)))))
  :in-theory (e/d (fn-sic-item-complete fn-sic-step fn-sic-error fn-sic-finish fn-sic-push fn-sic-result
    fn-sic-item-abstract fn-sic-items-abstract fn-sic-argument-width nfix posp
    fn-cbor-decode-prechecked fn-cbor-decode-unsigned fn-cbor-decode-bytes-bounded
    fn-cbor-octet-listp fn-cbor-octetp fn-cbor-result-okp fn-cbor-result-value fn-cbor-result-rest
    fn-cbor-ok fn-cbor-error fn-cbor-ag-car fn-cbor-ag-cdr)
   (fn-sic-old-argument-has-exact-geometry fn-sic-at fn-sic-put fn-sic-at-is-nth fn-sic-put-is-update-nth
    fn-sic-argument-complete fn-sic-argument-start  fn-sic-bytes-complete
     
     fn-cbor-decode-argument take
    fn-cbor-at-leastp-is-length-lower-bound fn-stmt-error)))))

(defthm fn-sic-nthcdr-successor
 (implies (natp n) (equal (cdr (nthcdr n xs)) (nthcdr (+ 1 n) xs)))
 :hints (("Goal" :induct (nthcdr n xs) :in-theory (enable nthcdr))))

(defun fn-sic-old-item-advance (xs)
 (declare (xargs :guard t :verify-guards nil))
 (let* ((h (fn-cbor-ag-car xs)) (additional (if (< (nfix h) 32) h (- (nfix h) 64)))
        (arg (fn-cbor-decode-argument additional (fn-cbor-ag-cdr xs))))
  (+ 1 (fn-sic-argument-width additional)
   (if (< (nfix h) 32) 0 (nfix (fn-cbor-result-value arg))))))

(defthm fn-sic-nthcdr-commutes
 (implies (and (natp a) (natp b))
  (equal (nthcdr a (nthcdr b xs)) (nthcdr b (nthcdr a xs))))
 :hints (("Goal" :use ((:instance fn-sic-nthcdr-is-composable)
  (:instance fn-sic-nthcdr-is-composable (a b) (b a)))
 :in-theory (disable fn-sic-nthcdr-is-composable nthcdr))))

(defthm fn-sic-octet-listp-of-nthcdr
 (implies (fn-cbor-octet-listp xs) (fn-cbor-octet-listp (nthcdr n xs)))
 :hints (("Goal" :induct (nthcdr n xs) :in-theory (enable nthcdr fn-cbor-octet-listp))))

(defthm fn-sic-old-borrow-has-source-provenance
 (implies (and (natp pos) (natp budget) (fn-cbor-octet-listp source)
  (<= pos (len source)) (equal xs (nthcdr pos source)) (consp xs)
  (fn-cbor-result-okp (fn-cbor-decode-prechecked xs budget)))
  (and (fn-sic-span-itemp (fn-sic-old-item-borrow pos xs budget) source)
   (<= (+ pos (fn-sic-old-item-advance xs)) (len source))
   (equal (fn-cbor-result-rest (fn-cbor-decode-prechecked xs budget))
    (nthcdr (+ pos (fn-sic-old-item-advance xs)) source))))
 :hints (("Goal" :do-not-induct t
 :expand ((:free (xs) (nthcdr 0 xs)))
 :use ((:instance fn-sic-consp-has-positive-length (xs (nthcdr pos source))) (:instance fn-sic-octet-listp-of-nthcdr (n pos) (xs source)) (:instance fn-sic-old-argument-has-natural-value-and-octet-rest
   (additional (car xs)) (xs (cdr xs)))
  (:instance fn-sic-old-argument-has-natural-value-and-octet-rest
   (additional (- (car xs) 64)) (xs (cdr xs)))
  (:instance fn-sic-old-argument-has-exact-geometry (additional (car xs)) (xs (cdr xs)))
  (:instance fn-sic-old-argument-has-exact-geometry (additional (- (car xs) 64)) (xs (cdr xs))))
 :in-theory (e/d (fn-sic-span-itemp fn-sic-old-item-borrow fn-sic-old-item-advance
  fn-cbor-decode-prechecked fn-cbor-decode-unsigned fn-cbor-decode-bytes-bounded
  fn-cbor-result-okp fn-cbor-result-value fn-cbor-result-rest fn-cbor-ok fn-cbor-error
  fn-cbor-ag-car fn-cbor-ag-cdr fn-cbor-octet-listp fn-cbor-octetp nfix)
 (fn-sic-octet-listp-of-nthcdr fn-sic-old-argument-has-natural-value-and-octet-rest fn-sic-at fn-sic-at-is-nth fn-sic-put fn-sic-put-is-update-nth
  fn-cbor-decode-argument fn-sic-argument-width nthcdr len take fn-cbor-at-leastp
  fn-sic-old-argument-has-exact-geometry)))))

(defthm fn-sic-item-complete-preserves-source-spans
 (implies (and (equal (fn-sic-at 0 c) :head) (consp (fn-sic-at 2 c))
  (fn-cbor-octet-listp (fn-sic-at 2 c)) (natp (fn-sic-at 3 c))
  (posp (fn-sic-at 6 c)) (natp (fn-sic-at 5 c))
  (fn-cbor-octet-listp source) (equal (fn-sic-at 1 c) source)
  (<= (fn-sic-at 3 c) (len source))
  (equal (fn-sic-at 2 c) (nthcdr (fn-sic-at 3 c) source))
  (fn-sic-span-item-listp (fn-sic-at 16 c) source)
  (fn-cbor-result-okp (fn-cbor-decode-prechecked (fn-sic-at 2 c) (fn-sic-at 5 c))))
  (let ((d (fn-sic-item-complete c)))
   (and (equal (fn-sic-at 0 d) :head) (natp (fn-sic-at 3 d))
    (equal (fn-sic-at 1 d) source) (<= (fn-sic-at 3 d) (len source))
    (equal (fn-sic-at 2 d) (nthcdr (fn-sic-at 3 d) source))
    (fn-sic-span-item-listp (fn-sic-at 16 d) source))))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-sic-item-complete-has-exact-raw-item-geometry)
  (:instance fn-sic-old-borrow-has-source-provenance (pos (fn-sic-at 3 c))
   (xs (fn-sic-at 2 c)) (budget (fn-sic-at 5 c)))
  (:instance fn-sic-old-argument-has-natural-value-and-octet-rest
   (additional (car (fn-sic-at 2 c))) (xs (cdr (fn-sic-at 2 c))))
  (:instance fn-sic-old-argument-has-natural-value-and-octet-rest
   (additional (- (car (fn-sic-at 2 c)) 64)) (xs (cdr (fn-sic-at 2 c)))))
 :in-theory (e/d (fn-sic-span-item-listp fn-sic-old-item-borrow fn-sic-old-item-advance
  fn-cbor-decode-prechecked fn-cbor-decode-unsigned fn-cbor-decode-bytes-bounded
  fn-cbor-octet-listp fn-cbor-octetp fn-cbor-result-okp fn-cbor-result-value fn-cbor-result-rest
  fn-cbor-ok fn-cbor-error fn-cbor-ag-car fn-cbor-ag-cdr nfix)
 (fn-sic-at fn-sic-at-is-nth fn-sic-put fn-sic-put-is-update-nth fn-sic-item-complete
  fn-sic-item-complete-has-exact-raw-item-geometry fn-sic-old-borrow-has-source-provenance
  fn-sic-old-argument-has-natural-value-and-octet-rest
  fn-sic-old-argument-has-exact-geometry fn-sic-span-itemp fn-sic-argument-width
  fn-cbor-decode-argument nthcdr len fn-cbor-at-leastp take)))))

(defthm fn-sic-item-complete-preserves-issued-source-spans
 (implies (and (equal (fn-sic-at 0 c) :head) (consp (fn-sic-at 2 c))
  (fn-cbor-octet-listp (fn-sic-at 2 c)) (natp (fn-sic-at 3 c))
  (posp (fn-sic-at 6 c)) (natp (fn-sic-at 5 c))
  (fn-cbor-octet-listp (fn-sic-at 1 c)) t
  (<= (fn-sic-at 3 c) (len (fn-sic-at 1 c)))
  (equal (fn-sic-at 2 c) (nthcdr (fn-sic-at 3 c) (fn-sic-at 1 c)))
  (fn-sic-span-item-listp (fn-sic-at 16 c) (fn-sic-at 1 c))
  (fn-cbor-result-okp (fn-cbor-decode-prechecked (fn-sic-at 2 c) (fn-sic-at 5 c))))
  (let ((d (fn-sic-item-complete c)))
   (and (equal (fn-sic-at 0 d) :head) (natp (fn-sic-at 3 d))
    (equal (fn-sic-at 1 d) (fn-sic-at 1 c)) (<= (fn-sic-at 3 d) (len (fn-sic-at 1 c)))
    (equal (fn-sic-at 2 d) (nthcdr (fn-sic-at 3 d) (fn-sic-at 1 c)))
    (fn-sic-span-item-listp (fn-sic-at 16 d) (fn-sic-at 1 c)))))
 :hints (("Goal" :use ((:instance fn-sic-item-complete-preserves-source-spans (source (fn-sic-at 1 c))))
 :in-theory (disable fn-sic-item-complete-preserves-source-spans fn-sic-at fn-sic-item-complete
 fn-sic-span-item-listp fn-sic-item-complete-has-exact-raw-item-geometry fn-cbor-octet-listp
 fn-cbor-result-okp fn-cbor-decode-prechecked))))

(defthm fn-sic-empty-span-items-are-valid
 (fn-sic-span-item-listp nil source)
 :hints (("Goal" :in-theory (enable fn-sic-span-item-listp))))

(defthm fn-sic-reverse-complete-is-exact-raw-result
 (implies (equal (fn-sic-at 0 c) :reverse)
  (equal (fn-sic-result (fn-sic-reverse-complete c))
   (fn-stmt-ok (revappend (fn-sic-at 16 c) (fn-sic-at 17 c)))))
 :hints (("Goal" :induct (fn-sic-reverse-complete c)
 :in-theory (e/d (fn-sic-reverse-complete fn-sic-step fn-sic-finish fn-sic-result revappend)
 (fn-sic-at fn-sic-at-is-nth fn-sic-put fn-sic-put-is-update-nth fn-stmt-ok)))))

(defthm fn-sic-span-items-of-revappend
 (implies (and (fn-sic-span-item-listp x source) (fn-sic-span-item-listp y source))
  (fn-sic-span-item-listp (revappend x y) source))
 :hints (("Goal" :induct (revappend x y)
 :in-theory (enable fn-sic-span-item-listp revappend))))

(defthm fn-sic-sequence-complete-outside-head
 (implies (not (equal (fn-sic-at 0 c) :head)) (equal (fn-sic-sequence-complete fuel c) c))
 :hints (("Goal" :expand (fn-sic-sequence-complete fuel c))))

(defthm fn-sic-sequence-success-requires-item-success
 (implies (and (equal (fn-sic-at 0 c) :head) (consp (fn-sic-at 2 c))
  (fn-cbor-octet-listp (fn-sic-at 2 c)) (natp (fn-sic-at 3 c))
  (posp (fn-sic-at 6 c)) (natp (fn-sic-at 5 c))
  (fn-stmt-okp (fn-sic-result (fn-sic-sequence-complete fuel (fn-sic-item-complete c)))))
  (fn-cbor-result-okp (fn-cbor-decode-prechecked (fn-sic-at 2 c) (fn-sic-at 5 c))))
 :hints (("Goal" :do-not-induct t
 :cases ((fn-cbor-result-okp (fn-cbor-decode-prechecked (fn-sic-at 2 c) (fn-sic-at 5 c))))
 :use ((:instance fn-sic-item-complete-is-old-item))
 :in-theory (e/d (fn-stmt-okp fn-stmt-error)
 (fn-sic-item-complete fn-sic-item-complete-is-old-item fn-sic-at fn-sic-result fn-sic-sequence-complete
 fn-cbor-decode-prechecked fn-cbor-result-okp fn-cbor-octet-listp)))))

(defthm fn-sic-error-result-is-not-ok
 (not (fn-stmt-okp (fn-stmt-error code)))
 :hints (("Goal" :in-theory (enable fn-stmt-okp fn-stmt-error))))

(defthm fn-sic-error-list-is-not-ok
 (not (fn-stmt-okp (list :error code)))
 :hints (("Goal" :in-theory (enable fn-stmt-okp))))

(defthm fn-sic-argument-complete-retains-ordered-items
 (equal (fn-sic-at 17 (fn-sic-argument-complete c)) (fn-sic-at 17 c))
 :hints (("Goal" :induct (fn-sic-argument-complete c)
 :in-theory (e/d (fn-sic-argument-complete fn-sic-step fn-sic-error fn-sic-finish)
 (fn-sic-at fn-sic-put fn-sic-at-is-nth fn-sic-put-is-update-nth   )))))

(defthm fn-sic-bytes-complete-retains-ordered-items
 (equal (fn-sic-at 17 (fn-sic-bytes-complete c)) (fn-sic-at 17 c))
 :hints (("Goal" :induct (fn-sic-bytes-complete c)
 :in-theory (e/d (fn-sic-bytes-complete fn-sic-step fn-sic-error fn-sic-finish fn-sic-push)
 (fn-sic-at fn-sic-put fn-sic-at-is-nth fn-sic-put-is-update-nth   )))))

(defthm fn-sic-item-complete-retains-ordered-items
 (implies (equal (fn-sic-at 0 c) :head)
  (equal (fn-sic-at 17 (fn-sic-item-complete c)) (fn-sic-at 17 c)))
 :hints (("Goal" :in-theory (e/d (fn-sic-item-complete fn-sic-step fn-sic-error fn-sic-finish fn-sic-push fn-sic-argument-start)
 (fn-sic-at fn-sic-put fn-sic-at-is-nth fn-sic-put-is-update-nth fn-sic-argument-complete fn-sic-bytes-complete
   )))))

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

(defthm fn-sic-sequence-complete-retains-source-spans
 (implies (and (equal (fn-sic-at 0 c) :head) (natp fuel) (equal (fn-sic-at 6 c) fuel)
  (fn-cbor-octet-listp (fn-sic-at 2 c)) (natp (fn-sic-at 3 c)) (natp (fn-sic-at 5 c))
  (fn-cbor-octet-listp source) (equal (fn-sic-at 1 c) source)
  (<= (fn-sic-at 3 c) (len source))
  (equal (fn-sic-at 2 c) (nthcdr (fn-sic-at 3 c) source))
  (fn-sic-span-item-listp (fn-sic-at 16 c) source)
  (fn-sic-span-item-listp (fn-sic-at 17 c) source)
  (fn-stmt-okp (fn-sic-result (fn-sic-sequence-complete fuel c))))
  (fn-sic-span-item-listp (fn-stmt-value (fn-sic-result (fn-sic-sequence-complete fuel c))) source))
 :hints (("Goal" :induct (fn-sic-sequence-complete fuel c)
 :expand ((fn-sic-result (fn-sic-put 0 :done (fn-sic-put 18 '(:error :too-many-items) c))))
 :in-theory (e/d (fn-sic-sequence-complete fn-sic-step fn-sic-error fn-sic-finish
   fn-stmt-value fn-stmt-error fn-stmt-ok)
 (fn-stmt-okp natp posp fn-sic-at fn-sic-at-is-nth fn-sic-put fn-sic-put-is-update-nth
  fn-sic-item-complete fn-sic-reverse-complete fn-sic-result fn-sic-span-item-listp
  fn-sic-span-itemp fn-sic-old-item-borrow fn-sic-old-item-advance
  fn-cbor-octet-listp fn-cbor-result-okp fn-cbor-result-value fn-cbor-result-rest
  fn-sic-item-complete-has-exact-raw-item-geometry nthcdr len)))))

(defthm fn-sic-preflight-retains-item-chains
 (and (equal (fn-sic-at 16 (fn-sic-preflight-complete c)) (fn-sic-at 16 c))
      (equal (fn-sic-at 17 (fn-sic-preflight-complete c)) (fn-sic-at 17 c)))
 :hints (("Goal" :induct (fn-sic-preflight-complete c)
 :in-theory (e/d (fn-sic-preflight-complete fn-sic-step fn-sic-error fn-sic-finish)
 (fn-sic-at fn-sic-put fn-sic-at-is-nth fn-sic-put-is-update-nth)))))

(defthm fn-sic-abstraction-preserves-ok-outcome
 (equal (fn-stmt-okp (fn-sic-result-abstract c)) (fn-stmt-okp (fn-sic-result c)))
 :hints (("Goal" :in-theory (e/d (fn-sic-result-abstract fn-stmt-ok fn-stmt-okp)
 (fn-sic-result fn-sic-items-abstract)))))

(defthm fn-sic-complete-begin-retains-source-spans
 (implies (and (natp fuel) (natp outer-budget) (natp item-budget)
  (fn-stmt-okp (fn-sic-result (fn-sic-complete (fn-sic-begin fuel octets outer-budget item-budget)))))
  (fn-sic-span-item-listp
   (fn-stmt-value (fn-sic-result (fn-sic-complete (fn-sic-begin fuel octets outer-budget item-budget)))) octets))
 :hints (("Goal" :do-not-induct t
 :cases ((and (fn-cbor-at-mostp octets outer-budget) (fn-cbor-octet-listp octets)))
 :use ((:instance fn-sic-complete-begin-is-exact-old-result)
 (:instance fn-sic-abstraction-preserves-ok-outcome (c (fn-sic-complete (fn-sic-begin fuel octets outer-budget item-budget)))))
 :expand ((nthcdr 0 octets))
 :in-theory (e/d (fn-sic-complete fn-sic-begin fn-stmt-decode-items-bounded-impl
  fn-stmt-error)
 (fn-sic-abstraction-preserves-ok-outcome fn-stmt-okp fn-stmt-value natp fn-sic-at fn-sic-put fn-sic-at-is-nth fn-sic-put-is-update-nth
  fn-sic-result fn-sic-result-abstract fn-sic-preflight-complete fn-sic-sequence-complete
  fn-sic-complete-begin-is-exact-old-result fn-sic-span-item-listp fn-sic-span-itemp
  fn-cbor-at-mostp fn-cbor-octet-listp fn-stmt-decode-items-prechecked)))))

(defthm fn-sic-nthcdr-before-end-is-consp
 (implies (and (natp n) (< n (len xs))) (consp (nthcdr n xs)))
 :hints (("Goal" :induct (nthcdr n xs) :in-theory (enable nthcdr len))))
))

(defthm fn-sic-paid-begin-completion-retains-source-spans
 (implies (and (natp fuel) (natp outer-budget) (natp item-budget)
  (fn-stmt-okp (fn-sic-result (fn-sic-run (fn-sic-completion-cost (fn-sic-begin fuel octets outer-budget item-budget)) (fn-sic-begin fuel octets outer-budget item-budget)))))
  (fn-sic-span-item-listp
   (fn-stmt-value (fn-sic-result (fn-sic-run (fn-sic-completion-cost (fn-sic-begin fuel octets outer-budget item-budget)) (fn-sic-begin fuel octets outer-budget item-budget)))) octets))
 :hints (("Goal" :use ((:instance fn-sic-complete-begin-retains-source-spans))
 :in-theory (disable fn-sic-begin fn-sic-run fn-sic-completion-cost fn-sic-complete fn-sic-result fn-stmt-okp fn-stmt-value fn-sic-span-item-listp))))

(defthm fn-sic-paid-success-has-octet-source
 (implies (and (natp fuel) (natp outer-budget) (natp item-budget)
  (fn-stmt-okp (fn-sic-result (fn-sic-run (fn-sic-completion-cost (fn-sic-begin fuel octets outer-budget item-budget)) (fn-sic-begin fuel octets outer-budget item-budget)))))
  (fn-cbor-octet-listp octets))
 :hints (("Goal" :do-not-induct t
 :use ((:instance fn-sic-paid-begin-completion-is-exact-old-result)
 (:instance fn-sic-abstraction-preserves-ok-outcome
  (c (fn-sic-run (fn-sic-completion-cost (fn-sic-begin fuel octets outer-budget item-budget)) (fn-sic-begin fuel octets outer-budget item-budget)))))
 :in-theory (e/d (fn-stmt-decode-items-bounded-impl fn-stmt-error)
 (fn-sic-paid-begin-completion-is-exact-old-result fn-sic-abstraction-preserves-ok-outcome fn-stmt-okp fn-cbor-octet-listp fn-cbor-at-mostp fn-stmt-decode-items-prechecked fn-sic-begin fn-sic-run fn-sic-completion-cost fn-sic-complete fn-sic-result fn-sic-result-abstract)))))

(defthm fn-sic-borrowed-span-prefix-byte-is-octet
 (implies (and (fn-sic-span-itemp item source) (equal (fn-cbor-ag-car item) :bytes)
  (fn-cbor-octet-listp source) (natp i) (< i (fn-sic-at 2 item)))
  (fn-cbor-octetp (car (nthcdr i (fn-sic-at 3 item)))))
 :hints (("Goal" :do-not-induct t :use ((:instance fn-sic-octet-listp-of-nthcdr
 (xs source) (n (fn-sic-at 1 item)))
 (:instance fn-sic-octet-listp-of-nthcdr (xs (nthcdr (fn-sic-at 1 item) source)) (n i))
 (:instance fn-sic-nthcdr-before-end-is-consp (xs source) (n (+ i (fn-sic-at 1 item)))))
 :in-theory (e/d (fn-sic-span-itemp fn-cbor-octet-listp)
 (fn-sic-octet-listp-of-nthcdr fn-sic-at fn-cbor-octetp nthcdr len)))))

(in-theory (disable fn-sic-span-itemp fn-sic-span-item-listp))
