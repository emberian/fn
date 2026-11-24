; Wire sizes and exact parsing of the field kinds used in run page headers.
(in-package "ACL2")
(include-book "runs-header-varint-parse-proof")
(include-book "runs-stored-header-fields-proof")
(local (include-book "arithmetic-3/floor-mod/floor-mod" :dir :system))

(defun fn2-run-header-field-valid-p (k v)
  (declare (xargs :verify-guards nil))
  (case (fn2-layout-kind-code k)
    (1 (unsigned-byte-p 8 v)) (3 (unsigned-byte-p 32 v)) ((5 8) (unsigned-byte-p 60 v))
    (9 (and (unsigned-byte-p 8 v) (< v (len (caddr k))))) (otherwise nil)))

(defun fn2-run-header-values-valid-p (layout vals)
  (declare (xargs :verify-guards nil))
  (if (atom layout) (null vals)
    (and (consp (car layout)) (consp (cdar layout)) (consp vals)
         (fn2-run-header-field-valid-p (cadar layout) (car vals))
         (fn2-run-header-values-valid-p (cdr layout) (cdr vals)))))

(local
 (defthm fn2-run-le-reassemble-digit
   (implies (natp n) (equal (+ (mod n 256) (* 256 (floor n 256))) n))
   :rule-classes nil))

(local
 (defthm fn2-run-low-octet-as-remainder
   (implies (natp n) (equal (mod n 256) (- n (* 256 (floor n 256)))))
   :hints (("Goal" :use fn2-run-le-reassemble-digit))))

(local
 (defthm fn2-run-read-uint32-header-field
   (implies (unsigned-byte-p 32 n)
            (equal (fn2-layout-parse-field :u32 bytes (append (fn2-layout-le 4 n) suffix) 0 0 0 0 0 0 0)
                   (list :ok n suffix)))
   :hints (("Goal" :do-not-induct t
            :use (fn2-run-le-reassemble-digit (:instance fn2-run-le-reassemble-digit (n (floor n 256)))
                  (:instance fn2-run-le-reassemble-digit (n (floor n 65536))))
            :expand ((:free (v) (fn2-layout-le 4 v)) (:free (v) (fn2-layout-le 3 v))
                     (:free (v) (fn2-layout-le 2 v)) (:free (v) (fn2-layout-le 1 v))
                     (:free (v) (fn2-layout-le 0 v))
                     (:free (d r i v nx) (fn2-layout-parse-field :u32 bytes (cons d r) i v 0 0 0 0 nx)))
            :in-theory (e/d (fn2-layout-byte ash) (fn2-layout-le fn2-layout-parse-field))))))

(local
 (defthm fn2-run-header-field-parses
   (implies (fn2-run-header-field-valid-p k v)
            (equal (fn2-layout-parse-field k bytes (append (fn2-layout-field-octets k v) suffix)
                                           0 0 0 0 0 0 0)
                   (list :ok v suffix)))
   :hints (("Goal" :do-not-induct t
            :cases ((equal k :u32) (equal k :u8) (equal (fn2-layout-kind-code k) 9))
            :use ((:instance fn2-run-parse-header-varint (n v)))
            :expand ((:free (kind d r) (fn2-layout-parse-field kind bytes (cons d r) 0 0 0 0 0 0 0))
                     (:free (x) (fn2-layout-le 1 x)) (:free (x) (fn2-layout-le 0 x)))
            :in-theory (e/d (fn2-run-header-field-valid-p fn2-layout-field-octets fn2-layout-byte)
                         (fn2-layout-parse-field fn2-layout-le fn2-layout-varoctets))))))

(local (defthm fn2-run-header-append-assoc (equal (append (append a b) c) (append a (append b c)))))
(local (defthm fn2-run-header-append-width (equal (len (append a b)) (+ (len a) (len b)))))
(local (defthm fn2-run-header-append-octets
  (implies (and (fn-b3-octet-listp x) (fn-b3-octet-listp y)) (fn-b3-octet-listp (append x y)))))
(local
 (defthm fn2-run-header-le-shape
   (implies (natp v) (and (fn-b3-octet-listp (fn2-layout-le n v)) (equal (len (fn2-layout-le n v)) (nfix n))))
   :hints (("Goal" :induct (fn2-layout-le n v) :in-theory (enable fn2-layout-le)))))
(local
 (defthm fn2-run-header-varoctets-shape
   (implies (natp v) (fn-b3-octet-listp (fn2-layout-varoctets v)))
   :hints (("Goal" :induct (fn2-layout-varoctets v)))))

(local
 (defthm fn2-run-header-field-shape
   (let* ((bytes (fn2-layout-field-octets k v)) (width (fn2-layout-width k)))
     (implies (fn2-run-header-field-valid-p k v)
              (and (fn-b3-octet-listp bytes) (unsigned-byte-p 60 v) (fn2-run-scalar-kindp k)
                   (<= (len bytes) (or width 9)))))
   :hints (("Goal" :use ((:instance fn2-run-header-varint-fits (n v)))
            :in-theory (e/d (fn2-run-header-field-valid-p fn2-layout-field-octets fn2-layout-width fn2-run-scalar-kind-code)
                            (fn2-layout-le fn2-layout-varoctets fn2-layout-kind-code fn2-run-scalar-kindp))))))

(local
 (defthm fn2-run-valid-headers-parse-prefix
   (implies (fn2-run-header-values-valid-p layout vals)
            (equal (fn2-layout-parse layout (append (fn2-layout-octets layout vals) suffix))
                   (list :ok vals suffix)))
   :hints (("Goal" :induct (fn2-run-header-values-valid-p layout vals)
            :expand ((fn2-layout-octets layout vals) (:free (input) (fn2-layout-parse layout input)))
            :in-theory (disable fn2-layout-parse-field fn2-layout-field-octets fn2-run-header-field-valid-p)))))

(local
 (defthm fn2-run-header-field-fits-tail
   (implies (fn2-run-header-field-valid-p (cadr field) v)
            (<= (+ (len (fn2-layout-field-octets (cadr field) v)) (fn2-layout-max-size tail))
                (fn2-layout-max-size (cons field tail))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn2-run-header-field-shape (k (cadr field))))
            :expand ((fn2-layout-max-size (cons field tail)))
            :in-theory (e/d (fn2-run-header-field-valid-p fn2-layout-width)
                      (fn2-run-header-field-shape fn2-layout-field-octets fn2-layout-max-size fn2-run-scalar-kindp
                       fn2-layout-varsize unsigned-byte-p))))))

(local
 (defthm fn2-run-valid-headers-fit
   (implies (fn2-run-header-values-valid-p layout vals)
            (and (fn2-run-header-scalars-p layout vals)
                 (fn-b3-octet-listp (fn2-layout-octets layout vals))
                 (<= (len (fn2-layout-octets layout vals)) (fn2-layout-max-size layout))))
   :hints (("Goal" :induct (fn2-run-header-values-valid-p layout vals)
            :do-not '(preprocess) :expand ((fn2-layout-octets layout vals))
            :in-theory (disable fn2-layout-max-size fn2-run-header-field-shape fn2-layout-width fn2-run-scalar-kindp fn2-layout-field-octets
                                unsigned-byte-p fn2-run-header-field-valid-p))
           ("Subgoal *1/1" :expand ((fn2-layout-max-size layout)))
           ("Subgoal *1/2" :use ((:instance fn2-run-header-field-fits-tail (field (car layout)) (tail (cdr layout)) (v (car vals))) (:instance fn2-run-header-field-shape (k (cadar layout)) (v (car vals))))))))

(defthmd fn2-run-typed-header-has-canonical-encoding
  (implies (fn2-run-header-values-valid-p layout vals)
           (and (fn2-run-values-layoutp layout vals) (fn2-run-header-scalars-p layout vals)
                (fn-b3-octet-listp (fn2-layout-octets layout vals))
                (<= (len (fn2-layout-octets layout vals)) (fn2-layout-max-size layout))))
  :hints (("Goal" :use ((:instance fn2-run-valid-headers-parse-prefix (suffix nil)) fn2-run-valid-headers-fit)
           :in-theory (e/d (fn2-run-values-layoutp)
                     (fn2-run-header-values-valid-p fn2-run-header-scalars-p fn2-layout-octets fn2-layout-max-size
                      fn2-layout-parse fn2-run-valid-headers-parse-prefix fn2-run-valid-headers-fit)))))
