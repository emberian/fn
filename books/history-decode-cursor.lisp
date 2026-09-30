; Current history codec: byte-fed decode primitives. Prefix fn-hdc-.
; No page I/O, eager row decoder, arbitrary item limit, or string materializer.
; The row assembler owns the immutable source's generation pin and funding.
(in-package "ACL2")
(include-book "store-tree-codec")
(local (include-book "arithmetic/top" :dir :system))

; Numeric instruction cursor: remaining digits, accumulated value, place.
; The current format supplies an octet digit count, hence at most 255
; little-endian digits. This is a codec bound, not a new admission ceiling.
(defun fn-hdc-numberp (c)
  (declare (xargs :guard t))
  (and (consp c) (natp (car c)) (< (car c) 256)
       (consp (cdr c)) (natp (cadr c))
       (consp (cddr c)) (posp (caddr c)) (null (cdddr c))))

(defun fn-hdc-number-begin (digits)
  (declare (xargs :guard (fn-scc-octetp digits)))
  (list digits 0 1))

(defun fn-hdc-number-feed (byte c)
  (declare (xargs :guard (and (fn-scc-octetp byte) (fn-hdc-numberp c))))
  (if (zp (car c)) c
    (list (1- (car c)) (+ (cadr c) (* (caddr c) byte))
          (* 256 (caddr c)))))

(defthm fn-hdc-number-begin-valid
  (implies (fn-scc-octetp digits)
           (fn-hdc-numberp (fn-hdc-number-begin digits)))
  :hints (("Goal" :in-theory (enable fn-scc-octetp))))

(defthm fn-hdc-number-feed-valid
  (implies (and (fn-hdc-numberp c) (fn-scc-octetp byte))
           (fn-hdc-numberp (fn-hdc-number-feed byte c)))
  :hints (("Goal" :in-theory (enable fn-scc-octetp))))

(defthm fn-hdc-number-feed-progress
  (implies (and (fn-hdc-numberp c) (< 0 (car c)))
           (equal (car (fn-hdc-number-feed byte c)) (1- (car c)))))

; Logical residual interpretation. Never evaluated by a decode tick.
(defun fn-hdc-number-value (c suffix)
  (declare (xargs :guard (fn-hdc-numberp c)))
  (+ (cadr c) (* (caddr c) (fn-scc-le-value suffix))))

; KEYSTONE: one actual byte-fed transition preserves the number represented
; by its accumulated prefix and remaining suffix. Nonempty, byte-domain
; witnesses remove both the byte agreement and cursor remaining premise.
(defthm fn-hdc-number-feed-preserves-value
  (implies (and (posp (car c)) (natp byte))
           (equal (fn-hdc-number-value (fn-hdc-number-feed byte c) suffix)
                  (fn-hdc-number-value c (cons byte suffix))))
  :hints (("Goal" :in-theory (enable fn-scc-le-value fn-scc-octetp))))

; Proof driver, not a served loop: each recursion is one public feed call.
(defun fn-hdc-number-run (bytes c)
  (declare (xargs :guard (and (fn-scc-octet-listp bytes) (fn-hdc-numberp c))
                  :verify-guards nil))
  (if (or (endp bytes) (zp (car c))) c
    (fn-hdc-number-run (cdr bytes) (fn-hdc-number-feed (car bytes) c))))

(defthm fn-hdc-number-run-valid
  (implies (and (fn-hdc-numberp c) (fn-scc-octet-listp bytes))
           (fn-hdc-numberp (fn-hdc-number-run bytes c)))
  :hints (("Goal" :in-theory (enable fn-scc-octet-listp fn-scc-octetp))))

(verify-guards fn-hdc-number-run
  :hints (("Goal" :in-theory (enable fn-scc-octet-listp fn-scc-octetp))))

(defthm fn-hdc-number-run-completes
  (implies (and (fn-hdc-numberp c) (fn-scc-octet-listp bytes)
                (equal (len bytes) (car c)))
           (equal (fn-hdc-number-run bytes c)
                  (list 0 (fn-hdc-number-value c bytes)
                        (* (caddr c) (expt 256 (len bytes))))))
  :hints (("Goal" :induct (fn-hdc-number-run bytes c)
           :in-theory (enable fn-hdc-number-value fn-scc-le-value
                              fn-scc-octet-listp fn-scc-octetp))))

(local
 (defthm fn-hdc-number-input-long-enough-unfolds
   (implies (equal n (len bytes)) (fn-scc-long-enoughp n bytes))
   :rule-classes nil
   :hints (("Goal" :induct (fn-scc-long-enoughp n bytes)
     :in-theory (enable fn-scc-long-enoughp)))))

; Current-codec refinement, including accepted nonminimal little-endian
; spellings: no new canonicality restriction is smuggled into the reader.
(defthm fn-hdc-number-is-current-codec
  (implies (and (fn-scc-octet-listp bytes) (< (len bytes) 256))
           (equal (cadr (fn-hdc-number-run bytes
                                          (fn-hdc-number-begin (len bytes))))
                  (car (fn-scc-read-nat (cons (len bytes) bytes)))))
  :hints (("Goal"
           :use ((:instance fn-hdc-number-run-completes
                            (c (fn-hdc-number-begin (len bytes))))
                 (:instance fn-hdc-number-input-long-enough-unfolds (n (len bytes))))
           :in-theory (enable fn-scc-read-nat fn-scc-long-enoughp
                              fn-scc-octetp))))

(in-theory (disable fn-hdc-numberp fn-hdc-number-begin
                    fn-hdc-number-feed fn-hdc-number-value fn-hdc-number-run))
