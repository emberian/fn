; Version2 durable account adoption records. Fixed credential field widths
; are the existing AUTHINFO v2 grammar: principal/digests32, salt16, name64.
; Table size is not capped here. One independently charged row is one stage.
; Source components only until the complete funded publisher/replay join.
(in-package "ACL2")
(include-book "consumer-position")

(defun fn-cac-u64p (x)
  (declare (xargs :guard t))
  (and (natp x) (<= x *fn-cbor-max-uint64*)))

(defun fn-cac-kinds (kind)
  (declare (xargs :guard t))
  (case kind
    (:authority-begin '(:id :u64 :u64 :policy))
    (:authority-row '(:id :u64 :id :u64 :bytes32 :bytes16
                     :bytes32 :bytes32 :bytes32 :flag))
    (:authority-tombstone '(:id :u64 :id :u64))
    (:authority-fence '(:id :u64 :u64 :bytes32))
    (:authority-discard '(:id :u64))
    (:authority-seal '(:id :u64 :u64 :bytes32))
    (:authority-prepare '(:id :u64))
    (otherwise nil)))

(defun fn-cac-code (kind)
  (declare (xargs :guard t))
  (case kind (:authority-begin 0) (:authority-row 1)
    (:authority-tombstone 2) (:authority-fence 3) (:authority-discard 4)
    (:authority-seal 5) (:authority-prepare 6)
    (otherwise nil)))

(defun fn-cac-kind (code)
  (declare (xargs :guard t))
  (case code (0 :authority-begin) (1 :authority-row)
    (2 :authority-tombstone) (3 :authority-fence) (4 :authority-discard)
    (5 :authority-seal) (6 :authority-prepare)
    (otherwise nil)))

(defun fn-cac-fieldp (value kind)
  (declare (xargs :guard t))
  (case kind
    (:u64 (fn-cac-u64p value))
    (:id (fn-cp-idp value))
    (:flag (or (equal value 0) (equal value 1)))
    (:policy (and (natp value) (<= value 7)))
    (:bytes32 (and (fn-cbor-octet-listp value) (equal (len value) 32)))
    (:bytes16 (and (fn-cbor-octet-listp value) (equal (len value) 16)))
    (otherwise nil)))

(defun fn-cac-field-width (value kind)
  (declare (xargs :guard t))
  (case kind (:u64 8) (:id (+ 1 (len value)))
    ((:flag :policy) 1) (:bytes32 32) (:bytes16 16) (otherwise 0)))

(defun fn-cac-field-ceiling (kind)
  (declare (xargs :guard t))
  (case kind (:u64 8) (:id 65) ((:flag :policy) 1)
    (:bytes32 32) (:bytes16 16) (otherwise 0)))

(defun fn-cac-fields-validp (values kinds)
  (declare (xargs :guard t :measure (len kinds)))
  (if (consp kinds)
      (and (consp values) (fn-cac-fieldp (car values) (car kinds))
           (fn-cac-fields-validp (cdr values) (cdr kinds)))
    (null values)))

(defun fn-cac-fields-charge (values kinds)
  (declare (xargs :guard t :measure (len kinds)))
  (if (consp kinds)
      (+ (fn-cac-field-width (fn-cp-nth 0 values) (car kinds))
         (fn-cac-fields-charge (if (consp values) (cdr values) nil) (cdr kinds)))
    0))

(defun fn-cac-fields-ceiling (kinds)
  (declare (xargs :guard t))
  (if (consp kinds)
      (+ (fn-cac-field-ceiling (car kinds)) (fn-cac-fields-ceiling (cdr kinds)))
    0))

(defun fn-cac-field-encode (value kind)
  (declare (xargs :guard t))
  (case kind (:u64 (if (fn-cac-u64p value) (fn-cbor-u64-bytes value) nil))
    (:id (if (true-listp value) (cons (len value) value) nil))
    ((:flag :policy) (list value))
    ((:bytes32 :bytes16) (if (true-listp value) value nil))
    (otherwise nil)))

(defun fn-cac-fields-encode (values kinds)
  (declare (xargs :guard t :measure (len kinds)))
  (if (consp kinds)
      (append (fn-cac-field-encode (fn-cp-nth 0 values) (car kinds))
              (fn-cac-fields-encode (if (consp values) (cdr values) nil) (cdr kinds)))
    nil))

(defun fn-cac-operationp (op)
  (declare (xargs :guard t))
  (let* ((kind (fn-cp-nth 0 op)) (kinds (fn-cac-kinds kind)))
    (and (consp op) (consp kinds)
         (fn-cac-fields-validp (cdr op) kinds)
         ; The candidate carries the exact base. A row's creation identity
         ; is nonzero; lifetime representability/publication freshness is
         ; an additional producer theorem, never inferred from this parser.
         (case kind
           (:authority-begin (posp (fn-cp-nth 3 op)))
           ((:authority-row :authority-tombstone) (posp (fn-cp-nth 4 op)))
           (otherwise t)))))

(defun fn-cac-eventp (event)
  (declare (xargs :guard t))
  (and (true-listp event) (equal (len event) 5)
       (eq (fn-cp-nth 0 event) :consumer-authority)
       (fn-cac-u64p (fn-cp-nth 1 event))
       (fn-cac-u64p (fn-cp-nth 2 event))
       (fn-cac-u64p (fn-cp-nth 3 event))
       (fn-cac-operationp (fn-cp-nth 4 event))))

(defun fn-cac-event-charge (event)
  (declare (xargs :guard t))
  (if (not (fn-cac-eventp event)) 0
    (let ((op (fn-cp-nth 4 event)))
      (+ 30 (fn-cac-fields-charge (cdr op) (fn-cac-kinds (car op)))))))

(defun fn-cac-encode (event)
  (declare (xargs :guard t))
  (if (not (fn-cac-eventp event)) nil
    (let ((op (fn-cp-nth 4 event)))
      (append '(102 110 99 101) (list 2 (fn-cac-code (car op)))
              (fn-cac-fields-encode
               (list (fn-cp-nth 1 event) (fn-cp-nth 2 event) (fn-cp-nth 3 event))
               '(:u64 :u64 :u64))
              (fn-cac-fields-encode (cdr op) (fn-cac-kinds (car op)))))))

(defun fn-cac-read-field (bytes kind)
  (declare (xargs :guard t))
  (let* ((n (case kind
              (:id (if (consp bytes) (nfix (car bytes)) 0))
              (:u64 8) ((:flag :policy) 1) (:bytes32 32) (:bytes16 16)
              (otherwise 0)))
         (body (if (eq kind :id) (if (consp bytes) (cdr bytes) nil) bytes)))
    (if (or (zp n) (> n (fn-cac-field-ceiling kind))
            (not (fn-cbor-at-leastp body n)))
        (list :error :field)
      (let ((value (case kind (:u64 (ec-call (fn-cbor-u64-from body)))
                     ((:flag :policy) (fn-cp-nth 0 body))
                     (otherwise (ec-call (take n body))))))
        (if (fn-cac-fieldp value kind)
            (list :ok value (ec-call (nthcdr n body)))
          (list :error :field))))))

(defun fn-cac-read-fields (bytes kinds)
  (declare (xargs :guard t :measure (len kinds)))
  (if (consp kinds)
      (let ((one (fn-cac-read-field bytes (car kinds))))
        (if (not (eq (car one) :ok)) one
          (let ((rest (fn-cac-read-fields (fn-cp-nth 2 one) (cdr kinds))))
            (if (not (eq (car rest) :ok)) rest
              (list :ok (cons (fn-cp-nth 1 one) (fn-cp-nth 1 rest))
                    (fn-cp-nth 2 rest))))))
    (list :ok nil bytes)))

; Maximal current row is321octets. The decoder's preflight is the derived
; sum of its fixed credential schema, not a stored-data/table-size ceiling.
; Actual owner admission additionally charges this exact row to profile R/H
; and retained heap/debt before constructing an outer physical frame.
(defun fn-cac-decode-exact (bytes)
  (declare (xargs :guard t))
  (if (or (not (fn-cbor-at-mostp bytes 321))
          (not (fn-cbor-octet-listp bytes))
          (not (equal (ec-call (take 4 bytes)) '(102 110 99 101)))
          (not (equal (fn-cp-nth 4 bytes) 2)))
      (list :error :authority-octets)
    (let* ((kind (fn-cac-kind (fn-cp-nth 5 bytes)))
           (coords (fn-cac-read-fields (ec-call (nthcdr 6 bytes)) '(:u64 :u64 :u64))))
      (if (or (not kind) (not (eq (car coords) :ok)))
          (list :error :authority-envelope)
        (let ((fields (fn-cac-read-fields (fn-cp-nth 2 coords) (fn-cac-kinds kind))))
          (if (or (not (eq (car fields) :ok)) (consp (fn-cp-nth 2 fields)))
              (list :error :authority-operation)
            (let* ((v (fn-cp-nth 1 coords))
                   (event (list :consumer-authority (fn-cp-nth 0 v)
                                (fn-cp-nth 1 v) (fn-cp-nth 2 v)
                                (cons kind (fn-cp-nth 1 fields)))))
              (if (fn-cac-eventp event) (list :ok event)
                (list :error :authority-operation)))))))))

(defthm fn-cac-fields-charge-is-encoded-length
  (implies (fn-cac-fields-validp values kinds)
           (equal (fn-cac-fields-charge values kinds)
                  (len (fn-cac-fields-encode values kinds))))
  :hints (("Goal" :induct (fn-cac-fields-encode values kinds)
           :in-theory (e/d (fn-cac-fields-charge fn-cac-fields-encode
                             fn-cac-field-width fn-cac-field-encode
                             fn-cac-fields-validp fn-cac-fieldp fn-cac-u64p
                             fn-cp-nth fn-cp-idp fn-cbor-at-mostp)
                            (fn-cbor-u64-bytes)))))

(local
 (defthm fn-cac-valid-field-fits-ceiling
   (implies (fn-cac-fieldp value kind)
            (<= (fn-cac-field-width value kind) (fn-cac-field-ceiling kind)))
   :rule-classes :linear
   :hints (("Goal" :use ((:instance fn-cp-id-length-bound (x value)))
            :in-theory (e/d (fn-cac-fieldp fn-cac-field-width fn-cac-field-ceiling)
                             (fn-cp-idp fn-cac-u64p))))))

(defthm fn-cac-valid-fields-fit-derived-ceiling
  (implies (fn-cac-fields-validp values kinds)
           (<= (fn-cac-fields-charge values kinds) (fn-cac-fields-ceiling kinds)))
  :hints (("Goal" :induct (fn-cac-fields-charge values kinds)
           :in-theory (e/d (fn-cac-fields-charge fn-cac-fields-ceiling
                             fn-cac-fields-validp fn-cp-nth)
                            (fn-cac-fields-charge-is-encoded-length
                             fn-cac-field-width fn-cac-field-ceiling
                             fn-cac-fieldp)))))

(defthm fn-cac-event-charge-is-exact-encoding
  (equal (fn-cac-event-charge event) (len (fn-cac-encode event)))
  :hints (("Goal" :in-theory
           (e/d (fn-cac-event-charge fn-cac-encode fn-cac-eventp
                  fn-cac-operationp fn-cac-fields-charge fn-cac-field-width
                  fn-cac-fields-encode fn-cac-field-encode fn-cac-fieldp
                  fn-cac-fields-validp fn-cac-kinds fn-cac-u64p fn-cp-nth)
                 (fn-cbor-u64-bytes fn-cp-idp)))))

(defthm fn-cac-event-charge-fits-derived-row-bound
  (<= (fn-cac-event-charge event) 321)
  :hints (("Goal"
           :cases ((fn-cac-eventp event))
           :use ((:instance fn-cac-valid-fields-fit-derived-ceiling
                            (values (cdr (fn-cp-nth 4 event)))
                            (kinds (fn-cac-kinds (car (fn-cp-nth 4 event))))))
           :in-theory (e/d (fn-cac-eventp fn-cac-operationp fn-cac-event-charge
                             fn-cac-kinds fn-cac-fields-ceiling fn-cac-field-ceiling
                             fn-cp-nth)
                            (fn-cac-fields-charge fn-cac-fields-validp
                             fn-cac-event-charge-is-exact-encoding
                             fn-cac-fields-charge-is-encoded-length
                             fn-cac-valid-fields-fit-derived-ceiling
                             fn-cac-fieldp fn-cp-idp)))))

(local
 (defthm fn-cac-take-width
   (implies (and (true-listp value) (equal (len value) n))
            (equal (take n (append value rest)) value))
   :hints (("Goal" :use ((:instance fn-cp-take-append-prefix (x value) (y rest)))
            :in-theory (disable take fn-cp-take-append-prefix)))))

(local
 (defthm fn-cac-nthcdr-width
   (implies (and (true-listp value) (equal (len value) n))
            (equal (nthcdr n (append value rest)) rest))
   :hints (("Goal" :use ((:instance fn-cp-nthcdr-append-prefix (x value) (y rest)))
            :in-theory (disable nthcdr fn-cp-nthcdr-append-prefix)))))

(local
 (defthm fn-cac-id-has-positive-length
   (implies (fn-cp-idp value) (< 0 (len value)))
   :rule-classes :linear
   :hints (("Goal" :in-theory (enable fn-cp-idp)))))

(defthm fn-cac-read-field-roundtrip
  (implies (fn-cac-fieldp value kind)
           (equal (fn-cac-read-field (append (fn-cac-field-encode value kind) rest) kind)
                  (list :ok value rest)))
  :hints (("Goal"
           :use ((:instance fn-cp-idp-true-listp (x value)))
           :in-theory
           (e/d (fn-cac-read-field fn-cac-field-encode fn-cac-fieldp
                  fn-cac-field-ceiling fn-cac-u64p fn-cp-nth nthcdr
                  fn-cbor-octet-listp-implies-true-listp
                  (:linear fn-cp-id-length-bound))
                 (fn-cbor-u64-bytes fn-cbor-u64-from fn-cp-idp
                  fn-cbor-at-leastp take)))))

(defthm fn-cac-read-fields-roundtrip
  (implies (fn-cac-fields-validp values kinds)
           (equal (fn-cac-read-fields (append (fn-cac-fields-encode values kinds) rest) kinds)
                  (list :ok values rest)))
  :hints (("Goal" :induct (fn-cac-fields-encode values kinds)
           :in-theory (e/d (fn-cac-fields-encode fn-cac-fields-validp
                             fn-cac-read-fields fn-cp-nth)
                            (fn-cac-field-encode fn-cac-read-field fn-cac-fieldp)))))

(defthm fn-cac-field-encoded-are-octets
  (implies (fn-cac-fieldp value kind)
           (fn-cbor-octet-listp (fn-cac-field-encode value kind)))
  :hints (("Goal"
           :use ((:instance fn-cp-id-bytes-octets (id value))
                 (:instance fn-cbor-u64-bytes-are-octets (n value)))
           :in-theory (e/d (fn-cac-field-encode fn-cac-fieldp fn-cac-u64p
                             fn-cp-id-bytes fn-cbor-octet-listp fn-cbor-octetp)
                            (fn-cbor-u64-bytes fn-cp-idp fn-cp-id-bytes-octets
                             fn-cbor-u64-bytes-are-octets)))))

(defthm fn-cac-fields-encoded-are-octets
  (implies (fn-cac-fields-validp values kinds)
           (fn-cbor-octet-listp (fn-cac-fields-encode values kinds)))
  :hints (("Goal" :induct (fn-cac-fields-encode values kinds)
           :in-theory (e/d (fn-cac-fields-encode fn-cac-fields-validp fn-cp-nth
                             fn-cbor-octet-listp-append)
                            (fn-cac-field-encode fn-cac-fieldp
                             fn-cbor-octet-listp binary-append)))))

(defthm fn-cac-kind-of-code
  (implies (fn-cac-kinds kind) (equal (fn-cac-kind (fn-cac-code kind)) kind))
  :hints (("Goal" :in-theory (enable fn-cac-kinds fn-cac-kind fn-cac-code))))

(defthm fn-cac-code-is-octet
  (implies (fn-cac-kinds kind) (fn-cbor-octetp (fn-cac-code kind)))
  :hints (("Goal" :in-theory (enable fn-cac-kinds fn-cac-code fn-cbor-octetp))))

(defthm fn-cac-header-is-octets
  (implies (fn-cac-kinds kind)
           (fn-cbor-octet-listp (list 2 (fn-cac-code kind))))
  :hints (("Goal" :in-theory (e/d (fn-cbor-octet-listp fn-cbor-octetp)
                                   (fn-cac-code fn-cac-kinds)))))

(defthm fn-cac-encode-is-octets
  (implies (fn-cac-eventp event) (fn-cbor-octet-listp (fn-cac-encode event)))
  :hints (("Goal" :in-theory
           (e/d (fn-cac-encode fn-cac-eventp fn-cac-operationp
                  fn-cac-fields-validp fn-cac-fieldp fn-cac-u64p fn-cp-nth
                  fn-cbor-octet-listp-append fn-cbor-octet-listp-implies-true-listp)
                 (fn-cac-kinds fn-cac-code fn-cac-fields-encode fn-cbor-octet-listp
                  binary-append fn-cp-idp)))))

(defthm fn-cac-encode-passes-preflight
  (implies (fn-cac-eventp event)
           (fn-cbor-at-mostp (fn-cac-encode event) 321))
  :hints (("Goal"
           :use ((:instance fn-cbor-at-mostp-from-length
                            (xs (fn-cac-encode event)) (bound 321))
                 (:instance fn-cac-event-charge-fits-derived-row-bound)
                 (:instance fn-cac-event-charge-is-exact-encoding))
           :in-theory (e/d (fn-cbor-octet-listp-implies-true-listp)
                            (fn-cac-encode fn-cac-eventp fn-cac-event-charge
                             fn-cac-event-charge-fits-derived-row-bound
                             fn-cac-event-charge-is-exact-encoding)))))

(defthm fn-cac-encode-header
  (implies (fn-cac-eventp event)
           (and (equal (take 4 (fn-cac-encode event)) '(102 110 99 101))
                (equal (fn-cp-nth 4 (fn-cac-encode event)) 2)
                (equal (fn-cp-nth 5 (fn-cac-encode event))
                       (fn-cac-code (fn-cp-nth 0 (fn-cp-nth 4 event))))))
  :hints (("Goal" :in-theory (e/d (fn-cac-encode fn-cp-nth take)
                                   (fn-cac-eventp fn-cac-fields-encode
                                    fn-cac-code)))))

(defthm fn-cac-encode-coordinates-read
  (implies (fn-cac-eventp event)
           (equal (fn-cac-read-fields (nthcdr 6 (fn-cac-encode event))
                                      '(:u64 :u64 :u64))
                  (list :ok (list (fn-cp-nth 1 event) (fn-cp-nth 2 event)
                                  (fn-cp-nth 3 event))
                        (fn-cac-fields-encode (cdr (fn-cp-nth 4 event))
                                               (fn-cac-kinds (car (fn-cp-nth 4 event)))))))
  :hints (("Goal" :in-theory
           (e/d (fn-cac-encode fn-cac-eventp fn-cac-fields-validp fn-cac-fieldp
                  fn-cp-nth nthcdr)
                 (fn-cac-read-fields fn-cac-fields-encode fn-cac-operationp
                  fn-cac-kinds fn-cac-code fn-cac-u64p)))))

(local
 (defthm fn-cac-empty-proper-tail
   (implies (and (true-listp xs) (equal (len xs) 0)) (equal xs nil))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable true-listp len)))))

(defthm fn-cac-event-reconstruct
  (implies (fn-cac-eventp event)
           (equal (list :consumer-authority (fn-cp-nth 1 event)
                         (fn-cp-nth 2 event) (fn-cp-nth 3 event)
                         (fn-cp-nth 4 event)) event))
  :hints (("Goal"
           :use ((:instance fn-cac-empty-proper-tail (xs (cdr (cddddr event)))))
           :expand ((len event) (len (cdr event)) (len (cddr event))
                    (len (cdddr event)) (len (cddddr event))
                    (fn-cp-nth 1 event) (fn-cp-nth 2 event)
                    (fn-cp-nth 3 event) (fn-cp-nth 4 event)
                    (fn-cp-nth 1 (cdr event))
                    (fn-cp-nth 1 (cddr event))
                    (fn-cp-nth 1 (cdddr event)))
           :in-theory (e/d (fn-cac-eventp fn-cp-nth len true-listp)
                            (fn-cac-operationp fn-cac-u64p)))))

(defthm fn-cac-read-fields-exact
  (implies (fn-cac-fields-validp values kinds)
           (equal (fn-cac-read-fields (fn-cac-fields-encode values kinds) kinds)
                  (list :ok values nil)))
  :hints (("Goal" :use ((:instance fn-cac-read-fields-roundtrip (rest nil)))
           :in-theory (disable fn-cac-read-fields fn-cac-fields-encode
                                fn-cac-read-fields-roundtrip))))

(defthm fn-cac-decode-after-encode-is-the-complete-event
  (implies (fn-cac-eventp event)
           (equal (fn-cac-decode-exact (fn-cac-encode event)) (list :ok event)))
  :hints (("Goal"
           :use ((:instance fn-cac-event-reconstruct))
           :in-theory
           (e/d (fn-cac-decode-exact fn-cac-eventp fn-cac-operationp fn-cp-nth)
                 (fn-cac-event-reconstruct
                  fn-cac-read-fields fn-cac-encode fn-cac-code fn-cac-kinds
                  fn-cac-kind fn-cac-fields-encode fn-cac-fields-validp
                  fn-cac-u64p fn-cbor-at-mostp fn-cbor-octet-listp
                  take nthcdr)))))

(in-theory (disable fn-cac-u64p fn-cac-kinds fn-cac-code fn-cac-kind
                    fn-cac-fieldp fn-cac-field-width fn-cac-field-ceiling
                    fn-cac-fields-validp fn-cac-fields-charge fn-cac-fields-ceiling
                    fn-cac-field-encode fn-cac-fields-encode fn-cac-operationp
                    fn-cac-eventp fn-cac-event-charge fn-cac-encode
                    fn-cac-read-field fn-cac-read-fields fn-cac-decode-exact))
