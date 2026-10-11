; One LIST ACTIVE row's parser and segment plan. No retained group-row list.
; Numeric accumulators follow the supported NNTP number representation; this
; source has no certified arithmetic/resource refinement yet (its guards are verified).
(in-package "ACL2")
(include-book "web-session")

(defun fn-wgl-start (at)
  (declare (xargs :guard t))
  ; field, field-start, name-span, high, high-valid, high-seen,
  ; low, low-valid, low-seen, status-count, status-n, pending, pending-at
  (list 0 at nil 0 t nil 0 t nil 0 t nil at))
; The parser state is thirteen fields; the counters and positions are
; naturals (the accumulators grow by a digit at a time from 0), and the
; name span, once the first field ends, is a (START . END) pair.
(defun fn-wgl-statep (x)
  (declare (xargs :guard t))
  (and (true-listp x) (equal (len x) 13)
       (natp (fn-wrq-nth 0 x)) (natp (fn-wrq-nth 1 x))
       (natp (fn-wrq-nth 3 x)) (natp (fn-wrq-nth 6 x))
       (natp (fn-wrq-nth 9 x)) (natp (fn-wrq-nth 12 x))
       (or (null (fn-wrq-nth 2 x)) (consp (fn-wrq-nth 2 x)))))

(defun fn-wgl-char (o at x)
  (declare (xargs :guard (and (natp at) (fn-wgl-statep x))))
  (let ((field (fn-wrq-nth 0 x)) (fs (fn-wrq-nth 1 x)) (name (fn-wrq-nth 2 x))
        (hi (fn-wrq-nth 3 x)) (hip (fn-wrq-nth 4 x)) (his (fn-wrq-nth 5 x))
        (lo (fn-wrq-nth 6 x)) (lop (fn-wrq-nth 7 x)) (los (fn-wrq-nth 8 x))
        (sc (fn-wrq-nth 9 x)) (sn (fn-wrq-nth 10 x)))
    (if (equal o 32)
        (list (1+ field) (1+ at) (if (equal field 0) (cons fs at) name)
              hi hip his lo lop los sc sn nil at)
      (list field fs name
            (if (and (equal field 1) (fn-ot-digitp o)) (+ (* 10 hi) (- o 48)) hi)
            (if (equal field 1) (and hip (fn-ot-digitp o)) hip)
            (or his (equal field 1))
            (if (and (equal field 2) (fn-ot-digitp o)) (+ (* 10 lo) (- o 48)) lo)
            (if (equal field 2) (and lop (fn-ot-digitp o)) lop)
            (or los (equal field 2))
            (if (equal field 3) (1+ sc) sc)
            (if (equal field 3) (and sn (equal o 110)) sn) nil at))))
(defun fn-wgl-row (x ce)
  (declare (xargs :guard (fn-wgl-statep x)))
  (let* ((name (or (fn-wrq-nth 2 x) (cons (fn-wrq-nth 1 x) ce)))
         (hi (and (fn-wrq-nth 4 x) (fn-wrq-nth 5 x) (fn-wrq-nth 3 x)))
         (lo (and (fn-wrq-nth 7 x) (fn-wrq-nth 8 x) (fn-wrq-nth 6 x)))
         (count (if (and hi lo (<= lo hi) (< 0 hi)) (+ 1 (- hi lo)) 0)))
    (list name (fn-ot-decimal-octets count)
          (and (equal (fn-wrq-nth 9 x) 1) (fn-wrq-nth 10 x)))))
(defun fn-wgl-feed (o at x)
  (declare (xargs :guard (and (natp at) (fn-wgl-statep x))))
  ; One pending octet excludes a closing CR LF without buffering the line.
  (let ((pending (fn-wrq-nth 11 x)) (pa (fn-wrq-nth 12 x)))
    (if (and (equal o 10) (equal pending 13))
        (mv (fn-wgl-row x pa) nil)
      (let ((next (if pending (fn-wgl-char pending pa x) x)))
        (mv nil (append (take 11 next) (list o at)))))))
(defun fn-wgl-rowp (row)
  (declare (xargs :guard t))
  (and (true-listp row) (equal (len row) 3) (consp (car row))))

(defun fn-wgl-segs (row)
  (declare (xargs :guard (fn-wgl-rowp row)))
  (let ((name (car row)))
    (fn-wr-group-row-segments (list (cons :s name)) (list (cons :v-u name))
                              (cadr row) (caddr row) nil)))

; What the windowed cursor relies on to carry the parser from octet to octet
; (web-article-stream fn-wpc-window-next).
(defthm fn-wgl-start-statep
  (implies (natp at) (fn-wgl-statep (fn-wgl-start at))))

(defthm fn-wgl-char-statep
  (implies (and (natp at) (fn-wgl-statep x))
           (fn-wgl-statep (fn-wgl-char o at x))))

;; (append (take 11 x) (list o at)) for a thirteen-field x: eleven kept fields.
(local
 (defthm fn-wgl-len-append
   (equal (len (append a b)) (+ (len a) (len b)))))

(local
 (defthm fn-wgl-len-take
   (implies (and (natp n) (<= n (len x))) (equal (len (take n x)) n))))

(local
 (defthm fn-wgl-nth-append-take
   (implies (and (natp k) (natp n) (< k n) (<= n (len x)))
            (equal (nth k (append (take n x) ys)) (nth k x)))))

(local
 (defthm fn-wgl-nth-append-take-fixed
   (implies (and (natp k) (< k 11) (<= 11 (len x)))
            (equal (fn-wrq-nth k (append (take 11 x) (list o at))) (fn-wrq-nth k x)))
   :hints (("Goal" :use (fn-wgl-nth-append-take) :in-theory (enable fn-wrq-nth-is-nth)))))

(local
 (defun fn-wgl-nth-append-ind (k a)
   (if (consp a) (fn-wgl-nth-append-ind (1- k) (cdr a)) k)))

(local
 (defthm fn-wgl-nth-append-beyond
   (implies (and (natp k) (<= (len a) k))
            (equal (nth k (append a b)) (nth (- k (len a)) b)))
   :hints (("Goal" :induct (fn-wgl-nth-append-ind k a)))))

(local
 (defthm fn-wgl-nth-12-of-feed
   (implies (<= 11 (len x))
            (and (equal (nth 12 (append (take 11 x) (list o at))) at)
                 (equal (nth 11 (append (take 11 x) (list o at))) o)))
   :hints (("Goal" :use ((:instance fn-wgl-nth-append-beyond (k 12) (a (take 11 x)) (b (list o at)))
                         (:instance fn-wgl-nth-append-beyond (k 11) (a (take 11 x)) (b (list o at))))))))

(defthm fn-wgl-feed-statep
  ; A feed that closes a row has no next state; every other feed has one.
  (implies (and (natp at) (fn-wgl-statep x)
                (not (mv-nth 0 (fn-wgl-feed o at x))))
           (fn-wgl-statep (mv-nth 1 (fn-wgl-feed o at x)))))

(defthm fn-wgl-feed-rowp
  (implies (and (natp at) (fn-wgl-statep x) (mv-nth 0 (fn-wgl-feed o at x)))
           (fn-wgl-rowp (mv-nth 0 (fn-wgl-feed o at x)))))

(defthm fn-wgl-segs-true-listp
  (true-listp (fn-wgl-segs row))
  :rule-classes :type-prescription)
