; FNBS kinds 8 and 9.  They carry attempt identity and settlement, while the
; exact forwarding image is emitted only by the live kind-8 durable callback.
(in-package "ACL2")
(include-book "bp-forward-attempt")
(set-verify-guards-eagerness 0)

(defconst *fn-bpnp-attempt-kind* 8)
(defconst *fn-bpnp-result-kind* 9)
(defconst *fn-bpnp-attempt-fields*
  '(:nat :nat :nat :blob :blob :nat :nat (:enum :none :some) :nat))
(defconst *fn-bpnp-result-fields*
  '(:nat :nat :nat :blob :nat :nat :nat :nat
    (:enum :sent :refused :failed :uncertain :resumed) :nat))
; :resumed is appended, so every earlier kind-9 frame keeps its octets.

(defun fn-bpnp-attempt-values (record)
  (declare (xargs :guard t))
  (let ((age (fn-bpn-nth 7 record))
        (session (fn-bpn-nth 6 record)))
    (list (fn-bpn-nth 1 record) (fn-bpn-nth 2 record)
          (fn-bpn-nth 3 record) (fn-bpn-nth 4 record)
          (if (fn-bpp-eidp (fn-bpn-nth 5 record))
              (fn-bpn-peer-octets (fn-bpn-nth 5 record)) nil)
          (if (consp session) (car session) 0)
          (if (consp session) (cdr session) 0)
          (if (null age) :none :some) (if (null age) 0 age))))

(defun fn-bpnp-result-values (record)
  (declare (xargs :guard t))
  (let ((session (fn-bpn-nth 7 record))
        (outcome (fn-bpn-nth 8 record)))
    (list (fn-bpn-nth 1 record) (fn-bpn-nth 2 record)
          (fn-bpn-nth 3 record) (fn-bpn-nth 4 record)
          (fn-bpn-nth 5 record) (fn-bpn-nth 6 record)
          (if (consp session) (car session) 0)
          (if (consp session) (cdr session) 0)
          (if (consp outcome) :refused outcome)
          (if (consp outcome) (fn-bpn-nth 1 outcome) 0))))

(defun fn-bpnp-forward-frame-with (kind fields values)
  (declare (xargs :guard (and (fn-cbor-octetp kind)
                              (fn-frame-spec-listp fields))))
  (if (not (fn-frame-values-okp fields values)) :bad
    (let ((payload (fn-frame-fields-octets fields values)))
      (if (not (and (fn-cbor-octet-listp payload)
                    (<= (len payload) *fn-bpn-lifecycle-max-payload*)))
          :bad
        (let ((protected
               (fn-frame-protected *fn-frame-magic-bundle-store*
                                   *fn-frame-version* kind payload)))
          (append protected (fn-frame-trailer protected)))))))

(defun fn-bpnp-attempt-frame (record)
  (declare (xargs :guard t))
  (if (fn-bpnp-forward-attempt-recordp record)
      (fn-bpnp-forward-frame-with
       *fn-bpnp-attempt-kind* *fn-bpnp-attempt-fields*
       (fn-bpnp-attempt-values record))
    :bad))

(defun fn-bpnp-result-frame (record)
  (declare (xargs :guard t))
  (if (fn-bpnp-forward-result-recordp record)
      (fn-bpnp-forward-frame-with
       *fn-bpnp-result-kind* *fn-bpnp-result-fields*
       (fn-bpnp-result-values record))
    :bad))

(defun fn-bpnp-attempt-from-values (values)
  (declare (xargs :guard t))
  (let ((age-tag (fn-bpn-nth 7 values))
        (age (fn-bpn-nth 8 values)))
    (if (and (or (equal age-tag :some) (equal age-tag :none))
             (or (not (equal age-tag :none)) (equal age 0)))
        (let ((record
               (fn-bpnp-forward-attempt-record
                (fn-bpn-nth 0 values) (fn-bpn-nth 1 values)
                (fn-bpn-nth 2 values) (fn-bpn-nth 3 values)
                (fn-bpn-peer-from-octets (fn-bpn-nth 4 values))
                (cons (fn-bpn-nth 5 values) (fn-bpn-nth 6 values))
                (if (equal age-tag :none) nil age))))
          (if (fn-bpnp-forward-attempt-recordp record) record nil))
      nil)))

(defun fn-bpnp-result-from-values (values)
  (declare (xargs :guard t))
  (let* ((status (fn-bpn-nth 8 values))
         (code (fn-bpn-nth 9 values))
         (outcome (if (equal status :refused) (list :refused code) status)))
    (if (and (or (equal status :refused) (equal code 0))
             (fn-bpnp-forward-outcomep outcome))
        (let ((record
               (fn-bpnp-forward-result-record
                (fn-bpn-nth 0 values) (fn-bpn-nth 1 values)
                (fn-bpn-nth 2 values) (fn-bpn-nth 3 values)
                (fn-bpn-nth 4 values) (fn-bpn-nth 5 values)
                (cons (fn-bpn-nth 6 values) (fn-bpn-nth 7 values))
                outcome)))
          (if (fn-bpnp-forward-result-recordp record) record nil))
      nil)))

(defun fn-bpnp-forward-unframe-with (octets kind fields)
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
                    (equal (fn-frame-result-kind answer) kind)
                    (fn-cbor-octet-listp (fn-frame-result-payload answer))))
          nil
        (let ((parsed (fn-frame-fields-parse
                       fields (fn-frame-result-payload answer))))
          (if (fn-frame-parse-okp parsed)
              (fn-frame-parse-value parsed)
            nil))))))

(defun fn-bpnp-attempt-unframe (octets)
  (declare (xargs :guard t))
  (let ((record (fn-bpnp-attempt-from-values
                 (fn-bpnp-forward-unframe-with
                  octets *fn-bpnp-attempt-kind* *fn-bpnp-attempt-fields*))))
    (if (equal (fn-bpnp-attempt-frame record) octets) record nil)))

(defun fn-bpnp-result-unframe (octets)
  (declare (xargs :guard t))
  (let ((record (fn-bpnp-result-from-values
                 (fn-bpnp-forward-unframe-with
                  octets *fn-bpnp-result-kind* *fn-bpnp-result-fields*))))
    (if (equal (fn-bpnp-result-frame record) octets) record nil)))
