; Typed physical C account-adoption commit. This codec recognizes bytes, not
; authority: only the joint prepared-account/configuration interpreter may
; apply this variant. The ordinary configuration interpreter is unchanged.
(in-package "ACL2")
(include-book "config")
(include-book "consumer-authority-codec")

; Same five-field C envelope, with an eight-field typed change. Wide wire
; integers do not widen the actual allocator/generation admission domains.
(defun fn-cacm-marker (candidate base-config base-authority begin current count digest)
 (declare (xargs :guard t))
 (list :account-authority-adopt candidate base-config base-authority
       begin current count digest))

(defun fn-cacm-markerp (m)
 (declare (xargs :guard t))
 (and (fn-cbor-at-mostp m 8) (true-listp m) (equal (len m) 8)
      (eq (fn-cp-nth 0 m) :account-authority-adopt)
      (fn-cbor-at-mostp (fn-cp-nth 1 m) 64)
      (fn-cp-idp (fn-cp-nth 1 m))
      (fn-cac-u64p (fn-cp-nth 2 m)) (fn-cac-u64p (fn-cp-nth 3 m))
      (fn-cac-u64p (fn-cp-nth 4 m)) (fn-cac-u64p (fn-cp-nth 5 m))
      (fn-cac-u64p (fn-cp-nth 6 m))
      (fn-cbor-at-mostp (fn-cp-nth 7 m) 32)
      (fn-cac-fieldp (fn-cp-nth 7 m) :bytes32)))

(defun fn-cacm-recordp (r)
 (declare (xargs :guard t))
 (and (fn-cbor-at-mostp r 5) (fn-cfg-record-shapep r)
      (fn-cac-u64p (fn-cfg-record-sequence r))
      (fn-cac-u64p (fn-cfg-record-txid r))
      (fn-cac-u64p (fn-cfg-record-generation r))
      (fn-cacm-markerp (fn-cfg-record-change r))
      (fn-cbor-at-mostp (fn-cfg-record-stamp r) 5)
      (fn-cfg-stampp (fn-cfg-record-stamp r))))

; fn-cfg magic, explicit schema 1, exactly 15 CBOR items. The first item is
; variant 1. Version 0 ordinary delta bytes remain outside this decoder.
(defconst *fn-cacm-prefix* '(70 102 110 45 99 102 103 1 15))
(defconst *fn-cacm-kinds*
 '(:flag :u64 :u64 :u64 :u64 :u64 :u64 :flag :id
   :u64 :u64 :u64 :u64 :u64 :bytes32))

(defun fn-cacm-item-ceiling (kind)
 (declare (xargs :guard t))
 (case kind (:flag 1) (:u64 9) (:id 66) (:bytes32 34) (otherwise 0)))

(defun fn-cacm-items-ceiling (kinds)
 (declare (xargs :guard t))
 (if (consp kinds)
     (+ (fn-cacm-item-ceiling (car kinds)) (fn-cacm-items-ceiling (cdr kinds)))
   0))

(defun fn-cacm-octet-ceiling ()
 (declare (xargs :guard t))
 (+ (len *fn-cacm-prefix*) (fn-cacm-items-ceiling *fn-cacm-kinds*)))

(defun fn-cacm-values (r)
 (declare (xargs :guard t))
 (let ((m (fn-cfg-record-change r)) (s (fn-cfg-record-stamp r)))
  (list 1 (fn-cfg-record-sequence r) (fn-cfg-record-txid r)
        (fn-cfg-record-generation r)
        (fn-clock-monotonic s) (fn-clock-wall s) (fn-clock-wall-error s)
        (if (fn-clock-has-wall s) 1 0)
        (fn-cp-nth 1 m) (fn-cp-nth 2 m) (fn-cp-nth 3 m)
        (fn-cp-nth 4 m) (fn-cp-nth 5 m) (fn-cp-nth 6 m) (fn-cp-nth 7 m))))

(defun fn-cacm-items (values kinds)
 (declare (xargs :guard t :measure (len kinds)))
 (if (consp kinds)
     (cons (cons (if (member-eq (car kinds) '(:id :bytes32)) :bytes :uint)
                 (fn-cp-nth 0 values))
           (fn-cacm-items (if (consp values) (cdr values) nil) (cdr kinds)))
   nil))

(defun fn-cacm-read-items (items kinds)
 (declare (xargs :guard t :measure (len kinds)))
 (if (consp kinds)
     (let* ((item (fn-cp-nth 0 items))
            (value (if (consp item) (cdr item) nil))
            (kind (car kinds)))
      (if (not (and (consp items) (consp item)
                    (eq (car item) (if (member-eq kind '(:id :bytes32)) :bytes :uint))
                    (fn-cac-fieldp value kind)))
          '(:error :commit-field)
        (let ((tail (fn-cacm-read-items (cdr items) (cdr kinds))))
         (if (eq (fn-cp-nth 0 tail) :ok)
             (list :ok (cons value (fn-cp-nth 1 tail)))
           tail))))
   (if (null items) (list :ok nil) '(:error :commit-items))))

(defun fn-cacm-of-values (v)
 (declare (xargs :guard t))
 (fn-cfg-record-make
  (fn-cp-nth 1 v) (fn-cp-nth 2 v) (fn-cp-nth 3 v)
  (fn-cacm-marker (fn-cp-nth 8 v) (fn-cp-nth 9 v) (fn-cp-nth 10 v)
                  (fn-cp-nth 11 v) (fn-cp-nth 12 v) (fn-cp-nth 13 v)
                  (fn-cp-nth 14 v))
  (fn-clock-observation (fn-cp-nth 4 v) (fn-cp-nth 5 v)
                        (fn-cp-nth 6 v) (equal (fn-cp-nth 7 v) 1))))

(defun fn-cacm-encode (r)
 (declare (xargs :guard t))
 (if (fn-cacm-recordp r)
     (append *fn-cacm-prefix*
             (fn-cfg-item-octets (fn-cacm-items (fn-cacm-values r) *fn-cacm-kinds*)))
   nil))

(defun fn-cacm-decode-exact (octets)
 (declare (xargs :guard t))
 ; Bound traversal and allocation BEFORE inspecting external octets.
 (if (not (and (fn-cbor-at-mostp octets (fn-cacm-octet-ceiling))
               (fn-cbor-octet-listp octets)
               (equal (ec-call (take 9 octets)) *fn-cacm-prefix*)))
     '(:error :commit-envelope)
   (let ((parsed (fn-cfg-parse-items 15 (ec-call (nthcdr 9 octets)))))
    (if (not (and (fn-record-parse-okp parsed)
                  (null (fn-record-parse-rest parsed))))
        '(:error :commit-items)
      (let* ((read (fn-cacm-read-items (fn-record-parse-value parsed) *fn-cacm-kinds*))
             (v (fn-cp-nth 1 read)))
       (if (not (and (eq (fn-cp-nth 0 read) :ok) (equal (fn-cp-nth 0 v) 1)))
           '(:error :commit-variant)
         (let ((r (fn-cacm-of-values v)))
          (if (fn-cacm-recordp r) (list :ok r) '(:error :commit-record)))))))))

; Deliberately no apply function: shape/decoding cannot authorize adoption.
(in-theory (disable fn-cacm-marker fn-cacm-markerp fn-cacm-recordp
                    fn-cacm-item-ceiling fn-cacm-items-ceiling fn-cacm-octet-ceiling
                    fn-cacm-values fn-cacm-items fn-cacm-read-items
                    fn-cacm-of-values fn-cacm-encode fn-cacm-decode-exact))
