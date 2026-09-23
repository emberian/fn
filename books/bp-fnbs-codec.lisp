; FNBS kind 5: exact received-bundle publication for fn-bpnf-step.
; The host copies these bytes to a private stage and never reads Lisp syntax.
(in-package "ACL2")
(include-book "bp-node-foundation")
(include-book "bp-node-machine-codec")
(include-book "frame-invariants")

(set-verify-guards-eagerness 0)

(defconst *fn-bpnf-stored-code* 5)
(defconst *fn-bpnf-stored-fields*
  '(:nat :nat :nat :nat :nat :nat :blob :nat :blob :nat :blob))

(defun fn-bpnf-frame-ingressp (ingress)
  (declare (xargs :guard t))
  (fn-bpnf-cl-ingressp ingress))

(defun fn-bpnf-frame-held (ingress arrival bundle wire)
  (declare (xargs :guard t))
  (fn-bpnf-held (fn-bpnf-ingress-principal ingress)
                 (fn-bpb-bundle-id bundle) arrival ingress nil nil
                 bundle wire nil nil nil '(:dispatch-pending) nil nil arrival))

(defun fn-bpnf-stored-record (epoch operation-id held)
  (declare (xargs :guard t))
  (list :bpnf-stored epoch operation-id held))

(defun fn-bpnf-stored-recordp (record)
  (declare (xargs :guard t))
  (and (true-listp record) (equal (len record) 4)
       (equal (car record) :bpnf-stored)
       (fn-frame-natp (nth 1 record))
       (fn-frame-natp (nth 2 record))
       (let* ((held (nth 3 record))
              (ingress (nth 4 held))
              (wire (fn-bpnf-held-wire held))
              (bundle (fn-bpnf-held-bundle held)))
         (and (fn-bpnf-frame-ingressp ingress)
              (fn-bpnf-heldp held)
              (fn-frame-natp (nth 3 held))
              (<= (len wire) *fn-bpnf-max-held-image*)
              (equal held (fn-bpnf-frame-held ingress (nth 3 held)
                                                bundle wire))))))

(defun fn-bpnf-stored-record-values (record)
  (declare (xargs :guard t))
  (let* ((held (nth 3 record))
         (ingress (nth 4 held))
         (session (fn-bpn-nth 1 ingress)))
    (list (nth 1 record) (nth 2 record) (nth 3 held)
          (car session) (cdr session) (fn-bpn-nth 2 ingress)
          (fn-bpn-peer-octets (fn-bpn-nth 3 ingress))
          (if (fn-bpn-nth 4 ingress) 1 0)
          (if (fn-bpn-nth 4 ingress) (fn-bpn-nth 4 ingress) '(0))
          (fn-bpn-nth 5 ingress)
          (fn-bpnf-held-wire held))))

(defun fn-bpnf-stored-record-protected (record)
  (declare (xargs :guard t))
  (if (not (fn-bpnf-stored-recordp record))
      :bad
    (let ((values (fn-bpnf-stored-record-values record)))
      (if (not (fn-frame-values-okp *fn-bpnf-stored-fields* values))
          :bad
        (let ((payload (fn-frame-fields-octets *fn-bpnf-stored-fields* values)))
          (if (fn-cbor-at-mostp payload *fn-bpn-lifecycle-max-payload*)
              (fn-frame-protected *fn-frame-magic-bundle-store*
                                  *fn-frame-version*
                                  *fn-bpnf-stored-code* payload)
            :bad))))))

(defun fn-bpnf-stored-record-frame (record)
  (declare (xargs :guard t))
  (let ((protected (fn-bpnf-stored-record-protected record)))
    (if (equal protected :bad) :bad
      (append protected (fn-frame-trailer protected)))))

(defun fn-bpnf-stored-from-values (values)
  (declare (xargs :guard t))
  (let* ((peer (fn-bpn-peer-from-octets (nth 6 values)))
         (wire (nth 10 values))
         (decoded (if (and (fn-cbor-octet-listp wire)
                           (<= (len wire) *fn-bpnf-max-held-image*))
                      (fn-bpb-decode wire *fn-bpnf-max-held-image*)
                    (fn-cbor-error :malformed)))
         (bundle (if (fn-cbor-result-okp decoded)
                     (fn-cbor-result-value decoded) nil))
         (principal-ok (or (and (equal (nth 7 values) 0)
                                (equal (nth 8 values) '(0)))
                           (and (equal (nth 7 values) 1)
                                (consp (nth 8 values))
                                (fn-bpn-machine-textp (nth 8 values)))))
         (ingress (list :cl (cons (nth 3 values) (nth 4 values))
                        (nth 5 values) peer
                        (if (equal (nth 7 values) 0) nil (nth 8 values))
                        (nth 9 values)))
         (held (fn-bpnf-frame-held ingress (nth 2 values) bundle wire))
         (record (fn-bpnf-stored-record (nth 0 values) (nth 1 values) held)))
    (if (and principal-ok (fn-bpnf-stored-recordp record)) record nil)))

(defun fn-bpnf-stored-record-unframe (octets)
  (declare (xargs :guard t))
  (if (not (fn-cbor-octet-listp octets)) nil
    (let ((answer (fn-frame-decode
                   octets
                   (fn-frame-trailer (fn-frame-protected-prefix octets))
                   *fn-bpn-lifecycle-max-payload*)))
      (if (not (and (fn-frame-result-okp answer)
                    (equal (fn-frame-result-magic answer)
                           *fn-frame-magic-bundle-store*)
                    (equal (fn-frame-result-version answer) *fn-frame-version*)
                    (equal (fn-frame-result-kind answer) *fn-bpnf-stored-code*)))
          nil
        (let ((parsed (fn-frame-fields-parse
                       *fn-bpnf-stored-fields*
                       (fn-frame-result-payload answer))))
          (if (fn-frame-parse-okp parsed)
              (fn-bpnf-stored-from-values (fn-frame-parse-value parsed))
            nil))))))

(defun fn-bpnf-stored-record-name-chars (epoch operation-id)
  (declare (xargs :guard t))
  (append (fn-bs-txn-digits epoch)
          (cons #\- (append (fn-bs-txn-digits operation-id)
                             *fn-bpn-lifecycle-name-suffix*))))

(defun fn-bpnf-stored-record-name (epoch operation-id)
  (declare (xargs :guard t :verify-guards nil))
  (coerce (fn-bpnf-stored-record-name-chars epoch operation-id) 'string))

(defthm fn-bpnf-stored-record-name-chars-are-characters
  (character-listp (fn-bpnf-stored-record-name-chars epoch operation-id))
  :hints (("Goal" :use ((:instance fn-bs-txn-name-chars-characters (n epoch))
                        (:instance fn-bs-txn-name-chars-characters
                                   (n operation-id)))
           :in-theory (enable fn-bpnf-stored-record-name-chars
                              fn-bs-txn-name-chars))))
