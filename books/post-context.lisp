; POST prepare context, version 1.  This book defines the format only;
; the fixed Section C statements are searched before their proofs are added.
(in-package "ACL2")
(include-book "post-acceptance-bound")
(include-book "cbor")
(set-verify-guards-eagerness 1)

; Keep the packet's predicate byte-identical without including the machine.
(defconst *fn-pctx-sufhead-max* 9)
(defconst *fn-ptx-sufhead-max* *fn-pctx-sufhead-max*)
(defconst *fn-pctx-max*
  (+ 1 8 (* 4 5) (* 3 (fn-adm-acc-out-max)) *fn-pctx-sufhead-max*))

(defun fn-pctx-p (ctx)
  (and (true-listp ctx) (equal (len ctx) 6)
       (natp (nth 0 ctx)) (< (nth 0 ctx) (expt 2 64))
       (fn-cbor-octet-listp (nth 1 ctx)) (<= (len (nth 1 ctx)) (fn-adm-acc-out-max))
       (fn-cbor-octet-listp (nth 2 ctx)) (<= (len (nth 2 ctx)) (fn-adm-acc-out-max))
       (natp (nth 3 ctx)) (< (nth 3 ctx) (expt 2 32))
       (fn-cbor-octet-listp (nth 4 ctx)) (<= (len (nth 4 ctx)) *fn-ptx-sufhead-max*)
       (fn-cbor-octet-listp (nth 5 ctx)) (<= (len (nth 5 ctx)) (fn-adm-acc-out-max))))
(verify-guards fn-pctx-p)

; Total access and concatenation also accept dotted lists and atoms.
(defun fn-pctx-get (n x)
  (declare (xargs :guard t :measure (nfix n)))
  (if (consp x)
      (if (zp (nfix n)) (car x) (fn-pctx-get (1- (nfix n)) (cdr x)))
    nil))

(defun fn-pctx-cat (x y)
  (declare (xargs :guard t))
  (if (consp x) (cons (car x) (fn-pctx-cat (cdr x) y)) y))

(defun fn-pctx-octets (x)
  (declare (xargs :guard t))
  (if (fn-cbor-octet-listp x) x nil))

; Fixed-width unsigned integers: nfix followed by low-width projection.
(defun fn-pctx-uint-be (n width)
  (declare (xargs :guard t :measure (nfix width)))
  (if (zp (nfix width))
      nil
    (cons (logand 255 (ash (nfix n) (- (* 8 (1- (nfix width))))))
          (fn-pctx-uint-be n (1- (nfix width))))))

(defun fn-pctx-encode-field (x)
  (declare (xargs :guard t))
  (let ((octets (fn-pctx-octets x)))
    (fn-pctx-cat (fn-pctx-uint-be (len octets) 4) octets)))

(defun fn-pctx-encode (ctx)
  (declare (xargs :guard t))
  (cons 1
        (fn-pctx-cat
         (fn-pctx-uint-be (fn-pctx-get 0 ctx) 8)
         (fn-pctx-cat
          (fn-pctx-encode-field (fn-pctx-get 1 ctx))
          (fn-pctx-cat
           (fn-pctx-encode-field (fn-pctx-get 2 ctx))
           (fn-pctx-cat
            (fn-pctx-uint-be (fn-pctx-get 3 ctx) 4)
            (fn-pctx-cat
             (fn-pctx-encode-field (fn-pctx-get 4 ctx))
             (fn-pctx-encode-field (fn-pctx-get 5 ctx)))))))))

; Read exactly n octets, leaving the suffix untouched, even when it is
; not an octet list.  No length scan of the suffix is needed.
(defun fn-pctx-read-octets (n x)
  (declare (xargs :guard t :measure (nfix n)))
  (cond ((zp (nfix n)) (list t nil x))
        ((and (consp x) (fn-cbor-octetp (car x)))
         (let ((d (fn-pctx-read-octets (1- (nfix n)) (cdr x))))
           (if (fn-pctx-get 0 d)
               (list t (cons (car x) (fn-pctx-get 1 d)) (fn-pctx-get 2 d))
             (list nil nil nil))))
        (t (list nil nil nil))))

(defun fn-pctx-octets-uint (x acc)
  (declare (xargs :guard t))
  (if (consp x)
      (fn-pctx-octets-uint (cdr x) (+ (* 256 (nfix acc)) (nfix (car x))))
    (nfix acc)))

(defun fn-pctx-read-uint (width x)
  (declare (xargs :guard t))
  (let ((d (fn-pctx-read-octets width x)))
    (if (fn-pctx-get 0 d)
        (list t (fn-pctx-octets-uint (fn-pctx-get 1 d) 0) (fn-pctx-get 2 d))
      (list nil nil nil))))

; Refuse an excessive advertised length before consuming or allocating
; its field.  A short field or a non-octet in the consumed prefix fails.
(defun fn-pctx-read-field (x bound)
  (declare (xargs :guard t))
  (let* ((d (fn-pctx-read-uint 4 x))
         (n (nfix (fn-pctx-get 1 d))))
    (if (and (fn-pctx-get 0 d) (<= n (nfix bound)))
        (fn-pctx-read-octets n (fn-pctx-get 2 d))
      (list nil nil nil))))

(defun fn-pctx-decode (x)
  (declare (xargs :guard t))
  (if (and (consp x) (equal (car x) 1))
      (let* ((tx (fn-pctx-read-uint 8 (cdr x)))
             (pre (fn-pctx-read-field (fn-pctx-get 2 tx) (fn-adm-acc-out-max)))
             (ins (fn-pctx-read-field (fn-pctx-get 2 pre) (fn-adm-acc-out-max)))
             (ioff (fn-pctx-read-uint 4 (fn-pctx-get 2 ins)))
             (sh (fn-pctx-read-field (fn-pctx-get 2 ioff) *fn-pctx-sufhead-max*))
             (st (fn-pctx-read-field (fn-pctx-get 2 sh) (fn-adm-acc-out-max)))
             (ctx (list (fn-pctx-get 1 tx) (fn-pctx-get 1 pre) (fn-pctx-get 1 ins)
                        (fn-pctx-get 1 ioff) (fn-pctx-get 1 sh) (fn-pctx-get 1 st))))
        (if (and (fn-pctx-get 0 tx) (fn-pctx-get 0 pre) (fn-pctx-get 0 ins)
                 (fn-pctx-get 0 ioff) (fn-pctx-get 0 sh) (fn-pctx-get 0 st)
                 (fn-pctx-p ctx))
            (list t ctx (+ 1 8 (* 4 5) (len (fn-pctx-get 1 pre))
                           (len (fn-pctx-get 1 ins)) (len (fn-pctx-get 1 sh))
                           (len (fn-pctx-get 1 st))))
          (list nil nil 0)))
    (list nil nil 0)))
