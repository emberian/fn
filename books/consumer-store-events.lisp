; E2 v1 consumer transactions in the one Store journal namespace.
; Publication, replay and the carried consumer projection join in Store.
(in-package "ACL2")
(include-book "consumer-position")

(defconst *fn-cpe-magic* '(102 110 99 101)) ; "fnce"
(defconst *fn-cpe-version* 1)
(defconst *fn-cpe-max-octets* 512)

; (:consumer sequence txid generation operation).  Operation payloads are
; bounded and versioned here; the same operation is handed to fn-cp-apply
; only after the enclosing Store transaction is durably completed.
(defun fn-cpe-make (sequence txid generation operation)
  (list :consumer sequence txid generation operation))

(defun fn-cpe-code (kind)
  (case kind
    (:bootstrap 0) (:register 1) (:ack 2) (:rebase 3)
    (:unregister 4) (:rollover 5) (otherwise nil)))

(defun fn-cpe-kind (code)
  (case code
    (0 :bootstrap) (1 :register) (2 :ack) (3 :rebase)
    (4 :unregister) (5 :rollover) (otherwise nil)))

(defun fn-cpe-kinds (kind)
  (case kind
    (:bootstrap '(:id :id))
    ((:register :rebase) '(:id :id :id :uint :uint :uint))
    (:unregister '(:id :uint))
    (:rollover '(:id))
    (otherwise nil)))

(defun fn-cpe-operationp (op)
  (let ((kind (fn-cp-nth 0 op)))
    (and (true-listp op)
         (case kind
           (:bootstrap
            (and (equal (len op) 3)
                 (fn-cp-fields-validp (cdr op) (fn-cpe-kinds kind))))
           ((:register :rebase)
            (and (equal (len op) 7)
                 (fn-cp-fields-validp (cdr op) (fn-cpe-kinds kind))
                 (posp (fn-cp-nth 6 op))))
           (:ack
            (and (equal (len op) 2)
                 (fn-cp-cursorp (fn-cp-nth 1 op))))
           (:unregister
            (and (equal (len op) 3)
                 (fn-cp-fields-validp (cdr op) (fn-cpe-kinds kind))
                 (posp (fn-cp-nth 2 op))))
           (:rollover
            (and (equal (len op) 2)
                 (fn-cp-fields-validp (cdr op) (fn-cpe-kinds kind))))
           (otherwise nil)))))

(defun fn-cpe-eventp (event)
  (and (true-listp event) (equal (len event) 5)
       (equal (fn-cp-nth 0 event) :consumer)
       (fn-cp-uintp (fn-cp-nth 1 event))
       (fn-cp-uintp (fn-cp-nth 2 event))
       (fn-cp-uintp (fn-cp-nth 3 event))
       (fn-cpe-operationp (fn-cp-nth 4 event))))

(defun fn-cpe-sequence (event) (fn-cp-nth 1 event))
(defun fn-cpe-txid (event) (fn-cp-nth 2 event))
(defun fn-cpe-generation (event) (fn-cp-nth 3 event))
(defun fn-cpe-operation (event) (fn-cp-nth 4 event))

; Four magic octets, one version octet, one kind octet, three uint32
; coordinates and one exact operation.  The longest valid operation is an
; ack carrying the 346-octet public cursor, for a 364-octet maximum.
(defun fn-cpe-encode (event)
  (if (not (fn-cpe-eventp event)) nil
    (let* ((op (fn-cpe-operation event))
           (kind (fn-cp-nth 0 op)))
      (append *fn-cpe-magic*
              (list *fn-cpe-version* (fn-cpe-code kind))
              (fn-cp-fields-encode
               (list (fn-cpe-sequence event) (fn-cpe-txid event)
                     (fn-cpe-generation event))
               '(:uint :uint :uint))
              (if (eq kind :ack)
                  (fn-cp-cursor-encode (fn-cp-nth 1 op))
                (fn-cp-fields-encode (cdr op) (fn-cpe-kinds kind)))))))

(defun fn-cpe-payload-decode (kind bytes)
  (declare (xargs :guard (fn-cbor-octet-listp bytes) :verify-guards nil))
  (if (eq kind :ack)
      (let ((cursor (fn-cp-cursor-decode bytes)))
        (if (eq (car cursor) :ok)
            (list :ok (list :ack (fn-cp-nth 1 cursor)))
          (list :error :operation)))
    (let ((fields (fn-cp-read-fields bytes (fn-cpe-kinds kind))))
      (if (and (eq (car fields) :ok)
               (null (fn-cp-nth 2 fields)))
          (list :ok (cons kind (fn-cp-nth 1 fields)))
        (list :error :operation)))))

(defun fn-cpe-decode-exact (bytes)
  (if (or (not (fn-cbor-at-mostp bytes *fn-cpe-max-octets*))
          (not (fn-cbor-octet-listp bytes)))
      (list :error :octets)
    (if (or (not (equal (take 4 bytes) *fn-cpe-magic*))
            (not (equal (fn-cp-nth 4 bytes) *fn-cpe-version*)))
        (list :error :version)
      (let ((kind (fn-cpe-kind (fn-cp-nth 5 bytes))))
        (if (not kind) (list :error :kind)
          (let ((coords (fn-cp-read-fields (nthcdr 6 bytes)
                                           '(:uint :uint :uint))))
            (if (not (eq (car coords) :ok))
                (list :error :coordinates)
              (let ((op (fn-cpe-payload-decode kind (fn-cp-nth 2 coords))))
                (if (not (eq (car op) :ok)) op
                  (let* ((v (fn-cp-nth 1 coords))
                         (event (fn-cpe-make
                                 (fn-cp-nth 0 v) (fn-cp-nth 1 v)
                                 (fn-cp-nth 2 v) (fn-cp-nth 1 op))))
                    (if (fn-cpe-eventp event) (list :ok event)
                      (list :error :event))))))))))))

(verify-guards fn-cpe-make)
(verify-guards fn-cpe-code)
(verify-guards fn-cpe-kind)
(verify-guards fn-cpe-kinds)
(verify-guards fn-cpe-operationp)
(verify-guards fn-cpe-eventp)
(verify-guards fn-cpe-sequence)
(verify-guards fn-cpe-txid)
(verify-guards fn-cpe-generation)
(verify-guards fn-cpe-operation)
(verify-guards fn-cpe-encode)
(verify-guards fn-cpe-payload-decode)

(defthm fn-cpe-read-fields-ok-rest-octets
  (implies (and (fn-cbor-octet-listp bytes)
                (equal (car (fn-cp-read-fields bytes kinds)) :ok))
           (fn-cbor-octet-listp (fn-cp-nth 2
                                  (fn-cp-read-fields bytes kinds))))
  :hints (("Goal" :induct (fn-cp-read-fields bytes kinds)
           :in-theory (enable fn-cp-read-fields fn-cp-read-id
                              fn-cp-read-u32))))

(verify-guards fn-cpe-decode-exact
  :hints (("Goal" :in-theory (disable fn-cp-read-fields))))

; This leaf does not assert a durable transaction until Store finish and
; observed reopen carry the consumer state on the actual owner path.
(in-theory (disable (:d fn-cpe-operationp) (:d fn-cpe-eventp)
                    (:d fn-cpe-encode) (:d fn-cpe-decode-exact)))
