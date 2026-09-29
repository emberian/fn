; FNBS kind 5: exact received-bundle publication for fn-bpnf-step.
; The host copies these bytes to a private stage and never reads Lisp syntax.
(in-package "ACL2")
(include-book "bp-node-foundation")
(include-book "bp-node-machine-codec")
(include-book "frame-invariants")
(include-book "consumer-position")

(set-verify-guards-eagerness 0)

(defconst *fn-bpnf-stored-code* 5)
; The wire field is `(:blob . *fn-bpnf-max-held-image*)' (PRF-134): a value
; within both widths encodes to the same octets as under `:blob'
; (books/frame-fields), so every kind-5 row written before keeps its bytes.
(defconst *fn-bpnf-stored-fields*
  `(:nat :nat :nat :nat :nat :nat :blob :nat :blob :nat
    (:blob . ,*fn-bpnf-max-held-image*)))
(defconst *fn-bpnf-stored-fields-v1*
  `(:nat :nat :nat :nat :nat :nat :blob :nat :blob :nat
    (:blob . ,*fn-bpnf-max-held-image*)
    :nat :nat :nat :nat))

(defun fn-bpnf-stored-frame-limit ()
  (declare (xargs :guard t))
  (+ *fn-frame-header-octets* *fn-bpn-lifecycle-max-payload*
     *fn-frame-trailer-octets*))

(defun fn-bpnf-frame-ingressp (ingress)
  (declare (xargs :guard t))
  (fn-bpnf-cl-ingressp ingress))

(verify-guards fn-bpnf-frame-ingressp)

; The held record's id is the bundle's (fn-bpb-bundle-id), so a held record
; is only ever built from a bundle: the guard says so, and every caller
; establishes it (the recognizer through fn-bpnf-heldp, the codec by its
; decode test).
(defun fn-bpnf-frame-held-with-anchor (ingress arrival bundle wire anchor)
  (declare (xargs :guard (fn-bpb-bundlep bundle)))
  (fn-bpnf-held (fn-bpnf-ingress-principal ingress)
                 (fn-bpb-bundle-id bundle) arrival ingress nil nil
                 bundle wire anchor nil nil '(:dispatch-pending) nil nil arrival))

(defun fn-bpnf-frame-held (ingress arrival bundle wire)
  (declare (xargs :guard (fn-bpb-bundlep bundle)))
  (fn-bpnf-frame-held-with-anchor ingress arrival bundle wire nil))

(verify-guards fn-bpnf-frame-held-with-anchor)
(verify-guards fn-bpnf-frame-held)

(defun fn-bpnf-stored-anchorp (anchor)
  (declare (xargs :guard t))
  (or (equal anchor '(:wall))
      (and (true-listp anchor) (equal (len anchor) 3)
           (equal (car anchor) :observed-age)
           (fn-frame-natp (cadr anchor))
           (fn-frame-natp (caddr anchor)))))

(verify-guards fn-bpnf-stored-anchorp)

(defun fn-bpnf-stored-record (epoch operation-id held)
  (declare (xargs :guard t))
  (list :bpnf-stored epoch operation-id held))

(defun fn-bpnf-stored-recordp (record)
  (declare (xargs :guard t))
  (and (true-listp record) (equal (len record) 4)
       (equal (car record) :bpnf-stored)
       (fn-frame-natp (nth 1 record))
       (fn-frame-natp (nth 2 record))
       ; The held record is recognised before its slots are read: a held
       ; record is a true list whose bundle is a bundle, which is what the
       ; reads below and the reconstruction through fn-bpnf-frame-held ask.
       ; The same conjuncts as before, in this order
       ; (fn-bpnf-stored-recordp-equals-before-guards,
       ; books/bp-fnbs-codec-equivalence).
       (fn-bpnf-heldp (nth 3 record))
       (let* ((held (nth 3 record))
              (ingress (nth 4 held))
              (wire (fn-bpnf-held-wire held))
              (bundle (fn-bpnf-held-bundle held)))
         (and (fn-bpnf-frame-ingressp ingress)
              (fn-frame-natp (nth 3 held))
              (<= (len wire) *fn-bpnf-max-held-image*)
              (or (equal held (fn-bpnf-frame-held ingress (nth 3 held)
                                                   bundle wire))
                  (and (fn-bpnf-stored-anchorp (nth 9 held))
                       (equal held
                              (fn-bpnf-frame-held-with-anchor
                               ingress (nth 3 held) bundle wire
                               (nth 9 held)))))))))

; A held record is a true list (fn-bpnf-heldp's first conjunct) whose bundle
; is a bundle (its sixth): the recognizer's reads and its reconstruction
; through fn-bpnf-frame-held ask exactly these.
(defthm fn-bpnf-heldp-is-a-true-list
  (implies (fn-bpnf-heldp h) (true-listp h))
  :hints (("Goal" :in-theory (enable fn-bpnf-heldp))))

(defthm fn-bpnf-heldp-bundle-is-a-bundle
  (implies (fn-bpnf-heldp h)
           (fn-bpb-bundlep (fn-bpnf-held-bundle h)))
  :hints (("Goal" :in-theory (enable fn-bpnf-heldp))))

(verify-guards fn-bpnf-stored-recordp
  :hints (("Goal" :in-theory (disable fn-bpnf-heldp fn-bpnf-frame-ingressp
                                      fn-bpnf-stored-anchorp fn-bpb-bundlep
                                      fn-bpnf-held-bundle fn-bpnf-held-wire
                                      fn-bpnf-frame-held
                                      fn-bpnf-frame-held-with-anchor))))

; What fn-bpnf-inspect-adu reads under the recognizer: the held record at
; slot 3 carries a bundle (fn-bpnf-heldp through the recognizer).
(defthm fn-bpnf-stored-recordp-held-bundle-is-a-bundle
  (implies (fn-bpnf-stored-recordp record)
           (fn-bpb-bundlep (fn-bpnf-held-bundle (fn-bpn-nth 3 record))))
  :hints (("Goal" :in-theory (e/d (fn-bpnf-stored-recordp)
                                  (fn-bpnf-heldp fn-bpnf-held-bundle
                                   fn-bpnf-frame-held
                                   fn-bpnf-frame-held-with-anchor
                                   fn-bpnf-frame-ingressp
                                   fn-bpnf-stored-anchorp fn-bpb-bundlep))
           :expand ((fn-bpn-nth 3 record) (fn-bpn-nth 2 (cdr record))
                    (fn-bpn-nth 1 (cddr record))
                    (fn-bpn-nth 0 (cdddr record))))))

(defun fn-bpnf-stored-record-values (record)
  (declare (xargs :guard t))
  (let* ((held (nth 3 record))
         (ingress (nth 4 held))
         (session (fn-bpn-nth 1 ingress)))
    (let ((base
            (list (nth 1 record) (nth 2 record) (nth 3 held)
                  (car session) (cdr session) (fn-bpn-nth 2 ingress)
                  (fn-bpn-peer-octets (fn-bpn-nth 3 ingress))
                  (if (fn-bpn-nth 4 ingress) 1 0)
                  (if (fn-bpn-nth 4 ingress) (fn-bpn-nth 4 ingress) '(0))
                  (fn-bpn-nth 5 ingress)
                  (fn-bpnf-held-wire held)))
          (anchor (nth 9 held)))
      (if (equal anchor '(:wall))
          (append base '(1 0 0 0))
        (if (and (consp anchor) (equal (car anchor) :observed-age))
            (append base (list 1 1 (cadr anchor) (caddr anchor)))
          base)))))

(defun fn-bpnf-stored-record-protected (record)
  (declare (xargs :guard t))
  (if (not (fn-bpnf-stored-recordp record))
      :bad
    (let ((values (fn-bpnf-stored-record-values record)))
      (if (not (fn-frame-values-okp
                (if (equal (len values) 11)
                    *fn-bpnf-stored-fields* *fn-bpnf-stored-fields-v1*)
                values))
          :bad
        (let ((payload (fn-frame-fields-octets
                        (if (equal (len values) 11)
                            *fn-bpnf-stored-fields* *fn-bpnf-stored-fields-v1*)
                        values)))
          (if (fn-cbor-at-mostp payload *fn-bpn-lifecycle-max-payload*)
              (fn-frame-protected *fn-frame-magic-bundle-store*
                                  *fn-frame-version*
                                  *fn-bpnf-stored-code* payload)
            :bad))))))

(defthm fn-bpnf-stored-record-protected-shape
  (or (equal (fn-bpnf-stored-record-protected record) :bad)
      (true-listp (fn-bpnf-stored-record-protected record)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-bpnf-stored-recordp fn-frame-fields-octets
                                      fn-frame-values-okp fn-bpnf-stored-record-values
                                      fn-cbor-at-mostp))))

; PROTECTED is the whole record frame (the bundle's wire in it), and ACL2's
; append recursed once per octet of it: the kind-5 persist of a 49,152-octet
; bundle died in BINARY-APPEND (40,721 frames) under
; fn-bpnf-publication-authorize.  This book verifies no guards (eagerness 0),
; and the host's *1* call of an unverified function runs its :logic, so the
; frame is guard-verified here (the protected prefix through ec-call) and its
; :exec appends in constant stack (fn-ag-append; lane depth-debt, PRF-919).
(defun fn-bpnf-stored-record-frame (record)
  (declare (xargs :guard t))
  (let ((protected (ec-call (fn-bpnf-stored-record-protected record))))
    (if (equal protected :bad) :bad
      (mbe :logic (append protected (fn-frame-trailer protected))
           :exec (fn-ag-append protected (fn-frame-trailer protected))))))

(verify-guards fn-bpnf-stored-record-frame
  :hints (("Goal" :use ((:instance fn-bpnf-stored-record-protected-shape))
                  :in-theory (disable fn-bpnf-stored-record-protected fn-frame-trailer))))

(verify-guards fn-bpn-peer-from-octets)
(verify-guards fn-bpnf-stored-record)

; A wire that does not decode to a bundle names no held record: the record
; the earlier body built from it failed fn-bpnf-stored-recordp (a held
; record's bundle is a bundle), so refusing before building it is the same
; function on every input (fn-bpnf-stored-from-values-equals-before-guards,
; books/bp-fnbs-codec-equivalence).
(defun fn-bpnf-stored-from-values (values)
  (declare (xargs :guard t))
  (let* ((peer (fn-bpn-peer-from-octets (fn-bpn-nth 6 values)))
         (wire (fn-bpn-nth 10 values))
         (decoded (if (and (fn-cbor-octet-listp wire)
                           (<= (len wire) *fn-bpnf-max-held-image*))
                      (fn-bpb-decode wire *fn-bpnf-max-held-image*)
                    (fn-cbor-error :malformed)))
         (bundle (if (fn-cbor-result-okp decoded)
                     (fn-cbor-result-value decoded) nil)))
    (if (not (fn-bpb-bundlep bundle))
        nil
      (let* ((principal-ok (or (and (equal (fn-bpn-nth 7 values) 0)
                                    (equal (fn-bpn-nth 8 values) '(0)))
                               (and (equal (fn-bpn-nth 7 values) 1)
                                    (consp (fn-bpn-nth 8 values))
                                    (fn-bpn-machine-textp (fn-bpn-nth 8 values)))))
             (ingress (list :cl (cons (fn-bpn-nth 3 values) (fn-bpn-nth 4 values))
                            (fn-bpn-nth 5 values) peer
                            (if (equal (fn-bpn-nth 7 values) 0) nil
                              (fn-bpn-nth 8 values))
                            (fn-bpn-nth 9 values)))
             (anchor
               (cond ((equal (len values) 11) nil)
                     ((and (equal (len values) 15)
                           (equal (fn-bpn-nth 11 values) 1)
                           (equal (fn-bpn-nth 12 values) 0)
                           (equal (fn-bpn-nth 13 values) 0)
                           (equal (fn-bpn-nth 14 values) 0))
                      '(:wall))
                     ((and (equal (len values) 15)
                           (equal (fn-bpn-nth 11 values) 1)
                           (equal (fn-bpn-nth 12 values) 1))
                      (list :observed-age (fn-bpn-nth 13 values)
                            (fn-bpn-nth 14 values)))
                     (t :bad)))
             (held (fn-bpnf-frame-held-with-anchor
                    ingress (fn-bpn-nth 2 values) bundle wire anchor))
             (record (fn-bpnf-stored-record (fn-bpn-nth 0 values)
                                            (fn-bpn-nth 1 values) held)))
        (if (and principal-ok (not (equal anchor :bad))
                 (fn-bpnf-stored-recordp record)) record nil)))))

(verify-guards fn-bpnf-stored-from-values
  :hints (("Goal" :in-theory (disable fn-bpnf-stored-recordp fn-bpb-bundlep
                                      fn-bpb-decode fn-bpn-peer-from-octets
                                      fn-bpn-machine-textp
                                      fn-bpnf-frame-held-with-anchor
                                      fn-bpnf-stored-record))))

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
        (let* ((payload (fn-frame-result-payload answer))
               (old (fn-frame-fields-parse
                     *fn-bpnf-stored-fields* payload))
               (new (if (fn-frame-parse-okp old)
                        nil
                      (fn-frame-fields-parse
                       *fn-bpnf-stored-fields-v1* payload)))
               (parsed (if (fn-frame-parse-okp old) old new))
               (record (if (fn-frame-parse-okp parsed)
                           (fn-bpnf-stored-from-values
                            (fn-frame-parse-value parsed))
                         nil)))
          (if (equal (fn-bpnf-stored-record-frame record) octets)
              record nil))))))

; The parse reads the decoded payload as octets; that it is one is
; fn-frame-decode-payload-octets (books/frame-fields, withdrawn from
; includers), supplied at this call's own digest and cap.
(verify-guards fn-bpnf-stored-record-unframe
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-frame-decode-payload-octets
                            (digest (fn-frame-trailer
                                     (fn-frame-protected-prefix octets)))
                            (max-payload *fn-bpn-lifecycle-max-payload*)))
           :in-theory (disable fn-bpnf-stored-from-values
                               fn-bpnf-stored-record-frame fn-frame-decode
                               fn-frame-fields-parse fn-frame-trailer
                               fn-frame-protected-prefix))))

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
