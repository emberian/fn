; Durable account binding preparation, separate FNCE version3/code7.
; This codec carries a decision; a stage never installs or authorizes it.
(in-package "ACL2")
(include-book "consumer-authority-codec")

(defconst *fn-cab-field-kinds* '(:id :u64 :id :policy :policy :bytes32))
(defconst *fn-cab-zero-principal* (make-list 32 :initial-element 0))

(defun fn-cab-operation (candidate base login provenance mode principal)
 (declare (xargs :guard t))
 (list :authority-binding candidate base login provenance mode principal))

(defun fn-cab-decisionp (provenance mode principal)
 (declare (xargs :guard t))
 (and (case provenance
        (0 (or (equal mode 1) (equal mode 2)))
        (1 (equal mode 0))
        (2 (equal mode 1))
        (otherwise nil))
      (or (equal mode 2) (equal principal *fn-cab-zero-principal*))))

(defun fn-cab-operationp (op)
 (declare (xargs :guard t))
 (and (fn-cbor-at-mostp op 7) (consp op)
      (eq (car op) :authority-binding)
      (fn-cac-fields-validp (cdr op) *fn-cab-field-kinds*)
      (fn-cab-decisionp (fn-cp-nth 4 op) (fn-cp-nth 5 op) (fn-cp-nth 6 op))))

(defun fn-cab-eventp (event)
 (declare (xargs :guard t))
 (and (fn-cbor-at-mostp event 5) (true-listp event) (equal (len event) 5)
      (eq (fn-cp-nth 0 event) :consumer-authority)
      (fn-cac-u64p (fn-cp-nth 1 event))
      (fn-cac-u64p (fn-cp-nth 2 event))
      (fn-cac-u64p (fn-cp-nth 3 event))
      (fn-cab-operationp (fn-cp-nth 4 event))))

(defun fn-cab-event-charge (event)
 (declare (xargs :guard t))
 (if (fn-cab-eventp event)
     (+ 30 (fn-cac-fields-charge (cdr (fn-cp-nth 4 event)) *fn-cab-field-kinds*))
   0))

(defun fn-cab-octet-ceiling ()
 (declare (xargs :guard t))
 (+ 30 (fn-cac-fields-ceiling *fn-cab-field-kinds*)))

(defun fn-cab-encode (event)
 (declare (xargs :guard t))
 (if (not (fn-cab-eventp event)) nil
   (append '(102 110 99 101 3 7)
           (fn-cac-fields-encode
            (list (fn-cp-nth 1 event) (fn-cp-nth 2 event) (fn-cp-nth 3 event))
            '(:u64 :u64 :u64))
           (fn-cac-fields-encode (cdr (fn-cp-nth 4 event)) *fn-cab-field-kinds*))))

(defun fn-cab-decode-exact (bytes)
 (declare (xargs :guard t))
 ; Derived fixed-stage bound precedes external octet traversal/allocation.
 (if (not (and (fn-cbor-at-mostp bytes (fn-cab-octet-ceiling))
               (fn-cbor-octet-listp bytes)
               (equal (ec-call (take 6 bytes)) '(102 110 99 101 3 7))))
     '(:error :binding-envelope)
   (let ((coords (fn-cac-read-fields (ec-call (nthcdr 6 bytes)) '(:u64 :u64 :u64))))
    (if (not (eq (fn-cp-nth 0 coords) :ok)) '(:error :binding-coordinates)
      (let ((fields (fn-cac-read-fields (fn-cp-nth 2 coords) *fn-cab-field-kinds*)))
       (if (not (and (eq (fn-cp-nth 0 fields) :ok) (null (fn-cp-nth 2 fields))))
           '(:error :binding-fields)
         (let* ((v (fn-cp-nth 1 coords))
                (event (list :consumer-authority (fn-cp-nth 0 v) (fn-cp-nth 1 v)
                             (fn-cp-nth 2 v) (cons :authority-binding (fn-cp-nth 1 fields)))))
          (if (fn-cab-eventp event) (list :ok event) '(:error :binding-decision)))))))))

(in-theory (disable fn-cab-operation fn-cab-decisionp fn-cab-operationp
                    fn-cab-eventp fn-cab-event-charge fn-cab-octet-ceiling
                    fn-cab-encode fn-cab-decode-exact))
