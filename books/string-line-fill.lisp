; Direct string-line rendering into the concrete octet buffer. Scalar loop
; registers replace per-character cursor and output lists. The returned cursor
; is allocated only once at the scheduling boundary.
(in-package "ACL2")
(include-book "string-line-cursor")
(include-book "octets-stobj")

(defun fn-slf-loop (text position phase bytes fn-octets)
  (declare (xargs :guard (natp bytes) :stobjs fn-octets
                  :measure (nfix bytes) :verify-guards nil))
  (if (zp bytes)
      (mv (fn-sl-make text position phase) fn-octets)
    (cond
     ((eq phase :stuff)
      (let ((fn-octets (fn-octets-append-octet 46 fn-octets)))
        (fn-slf-loop text position :text (1- bytes) fn-octets)))
     ((eq phase :text)
      (if (and (stringp text) (natp position) (< position (length text)))
          (let ((fn-octets (fn-octets-append-octet
                            (char-code (char text position)) fn-octets)))
            (fn-slf-loop text (1+ position)
                         (if (< (1+ position) (length text)) :text :cr)
                         (1- bytes) fn-octets))
        (let ((fn-octets (fn-octets-append-octet 13 fn-octets)))
          (fn-slf-loop text position :lf (1- bytes) fn-octets))))
     ((eq phase :cr)
      (let ((fn-octets (fn-octets-append-octet 13 fn-octets)))
        (fn-slf-loop text position :lf (1- bytes) fn-octets)))
     ((eq phase :lf)
      (let ((fn-octets (fn-octets-append-octet 10 fn-octets)))
        (mv nil fn-octets)))
     (t (mv nil fn-octets)))))

(verify-guards fn-slf-loop)

(defun fn-sl-fill (cur bytes fn-octets)
  (declare (xargs :guard (natp bytes) :stobjs fn-octets))
  (if (or (not cur) (zp bytes))
      (mv cur fn-octets)
    (fn-slf-loop (fn-cur-at 0 cur) (fn-cur-at 1 cur) (fn-cur-at 2 cur)
                 bytes fn-octets)))

; Scalar fill preserves the full logical residual for arbitrary input;
; the buffer abstraction supplies concrete output correspondence.
(local
 (defthm fn-slf-append-assoc (equal (append (append x y) z) (append x (append y z)))))

(local
 (defthm fn-slf-nthcdr-open
   (implies (and (natp k) (< k (len xs)))
            (equal (nthcdr k xs) (cons (nth k xs) (nthcdr (1+ k) xs))))
   :hints (("Goal" :in-theory (enable nth nthcdr)))))

(local
 (defthm fn-slf-octets-at-offset
   (implies (and (stringp text) (natp k) (< k (length text)))
            (equal (fn-nntp-string-octets-aux (nthcdr k (coerce text 'list)))
                   (cons (char-code (char text k))
                         (fn-nntp-string-octets-aux
                          (nthcdr (1+ k) (coerce text 'list))))))
   :hints (("Goal" :in-theory (e/d (char fn-nntp-string-octets-aux) (nthcdr))
            :use ((:instance fn-slf-nthcdr-open (xs (coerce text 'list))))))))

(local
 (defthm fn-slf-nthcdr-past
   (implies (and (natp k) (<= (len xs) k))
            (not (consp (nthcdr k xs))))))

(local
 (defthm fn-slf-octets-of-atom
   (implies (not (consp chars))
            (equal (fn-nntp-string-octets-aux chars) nil))
   :hints (("Goal" :in-theory (enable fn-nntp-string-octets-aux)))))

(local
 (defthm fn-slf-snoc-is-append (equal (fn-oct-snoc xs o) (append xs (list o))) :hints (("Goal" :induct (fn-oct-snoc xs o) :in-theory (enable fn-oct-snoc)))))

(local
 (defthm fn-slf-len-append (equal (len (append xs ys)) (+ (len xs) (len ys)))))

(local
 (defthm fn-slf-normalize-residual (equal (fn-sl-remaining (fn-sl-make (fn-cur-at 0 cur) (fn-cur-at 1 cur) (fn-cur-at 2 cur))) (fn-sl-remaining cur)) :hints (("Goal" :in-theory (enable fn-sl-remaining fn-sl-make)))))

(defthm fn-slf-loop-exact-residual
 (equal (append (mv-nth 1 (fn-slf-loop text position phase bytes fn-octets))
                 (fn-sl-remaining (mv-nth 0 (fn-slf-loop text position phase bytes fn-octets))))
         (append fn-octets (fn-sl-remaining (fn-sl-make text position phase))))
 :hints (("Goal" :induct (fn-slf-loop text position phase bytes fn-octets)
          :in-theory (e/d (fn-slf-loop fn-sl-make fn-sl-remaining)
                          (fn-nntp-string-octets-aux nthcdr char fn-slf-nthcdr-open)))))

(defthm fn-sl-fill-exact-residual
 (equal (append (mv-nth 1 (fn-sl-fill cur bytes fn-octets))
                (fn-sl-remaining (mv-nth 0 (fn-sl-fill cur bytes fn-octets))))
        (append fn-octets (fn-sl-remaining cur)))
 :hints (("Goal" :use ((:instance fn-slf-loop-exact-residual
                                (text (fn-cur-at 0 cur)) (position (fn-cur-at 1 cur))
                                (phase (fn-cur-at 2 cur))))
          :in-theory (e/d (fn-sl-fill)
                          (fn-slf-loop fn-sl-remaining fn-sl-make fn-cur-at
                           fn-slf-loop-exact-residual)))))

(defthm fn-slf-loop-byte-bound
 (<= (len (mv-nth 1 (fn-slf-loop text position phase bytes fn-octets)))
     (+ (len fn-octets) (nfix bytes)))
 :rule-classes :linear
 :hints (("Goal" :induct (fn-slf-loop text position phase bytes fn-octets)
          :in-theory (enable fn-slf-loop))))

(defthm fn-sl-fill-byte-bound
 (<= (len (mv-nth 1 (fn-sl-fill cur bytes fn-octets)))
     (+ (len fn-octets) (nfix bytes)))
 :rule-classes :linear
 :hints (("Goal" :in-theory (e/d (fn-sl-fill) (fn-slf-loop)))))
