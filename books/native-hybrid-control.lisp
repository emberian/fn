(in-package "ACL2")
(include-book "native-control")
(include-book "hybrid-lifecycle")
(include-book "native-admin-shape")

(defconst *fn-nhctrl-enroll-kind* 4)
(defconst *fn-nhctrl-author-kind* 5)
(defconst *fn-nhctrl-revoke-kind* 6)
(defconst *fn-nhctrl-max-payload* 65536)
(defconst *fn-nhctrl-enroll-spec* '(:nat :blob :blob :blob))
(defconst *fn-nhctrl-author-spec* '(:nat :blob :blob :blob :text))
(defconst *fn-nhctrl-revoke-spec* '(:nat :blob))

(defun fn-native-hybrid-control-uint32 (text)
  (declare (xargs :guard t))
  (if (fn-native-admin-decimalp text)
      (fn-native-admin-decimal-value (coerce text 'list)) nil))

(defun fn-nhctrl-seal (kind specs values)
  ; `fn-frame-protected' frames the kind as one octet, so the octet is this
  ; function's precondition, not a fact about specs and values: the guard
  ; conjecture asked for (<= KIND 255) under the spec/value hypotheses alone.
  ; Both callers below pass a literal kind constant.
  (declare (xargs :guard (fn-cbor-octetp kind)))
  (if (not (and (fn-frame-spec-listp specs)
                (fn-frame-values-okp specs values))) :bad
    (let ((payload (fn-frame-fields-octets specs values)))
      (if (< *fn-nhctrl-max-payload* (len payload)) :bad
        (let ((protected (fn-frame-protected *fn-nctrl-magic*
                                             *fn-nctrl-version* kind payload)))
          (append protected (fn-frame-trailer protected)))))))

(defun fn-nhctrl-open-values (octets kind specs)
  ; `fn-frame-fields-parse' needs the opened payload to be octets.  That is
  ; `fn-frame-decode-payload-octets' (books/frame-fields) at this call's own
  ; digest and cap; the instance is supplied closed, since the rule does not
  ; fire on the guard conjecture's case split.
  (declare (xargs :guard t
                  :guard-hints
                  (("Goal" :do-not-induct t
                    :use ((:instance fn-frame-decode-payload-octets
                                     (octets octets)
                                     (digest (fn-frame-trailer
                                              (fn-frame-protected-prefix
                                               octets)))
                                     (max-payload *fn-nhctrl-max-payload*)))))))
  (if (not (and (fn-cbor-octet-listp octets)
                (fn-frame-spec-listp specs))) nil
    (let ((opened (fn-frame-decode octets
                                 (fn-frame-trailer
                                  (fn-frame-protected-prefix octets))
                                 *fn-nhctrl-max-payload*)))
    (if (not (and (fn-frame-result-okp opened)
                  (equal (fn-frame-result-magic opened) *fn-nctrl-magic*)
                  (equal (fn-frame-result-version opened) *fn-nctrl-version*)
                  (equal (fn-frame-result-kind opened) kind))) nil
      (let ((parsed (fn-frame-fields-parse specs
                                           (fn-frame-result-payload opened))))
        (if (and (fn-frame-parse-okp parsed)
                 (null (fn-frame-parse-rest parsed)))
            (fn-frame-parse-value parsed) nil))))))

(defun fn-native-hybrid-control-enroll-encode
    (keyring-generation principal ed-key ml-key)
  (declare (xargs :guard t))
  (if (not (and (fn-record-uint32p keyring-generation)
                (fn-hsig-exact-octets-p principal 32)
                (fn-hsig-exact-octets-p ed-key 32)
                (fn-hsig-exact-octets-p ml-key 1952))) :bad
    (fn-nhctrl-seal *fn-nhctrl-enroll-kind* *fn-nhctrl-enroll-spec*
                     (list keyring-generation principal ed-key ml-key))))

(defun fn-native-hybrid-control-enroll-decode (octets)
  (declare (xargs :guard t))
  (let ((v (fn-nhctrl-open-values octets *fn-nhctrl-enroll-kind*
                                  *fn-nhctrl-enroll-spec*)))
    ; The vector is decided before any `nth' of it, the way
    ; `fn-native-control-request-decode' decides its own: length alone is not
    ; a proper list, and `nth' needs one under a verified guard.
    (if (and (true-listp v)
             (equal (len v) 4)
             (fn-record-uint32p (nth 0 v))
             (fn-hsig-exact-octets-p (nth 1 v) 32)
             (fn-hsig-exact-octets-p (nth 2 v) 32)
             (fn-hsig-exact-octets-p (nth 3 v) 1952))
        (cons :hybrid-enroll v) nil)))

(defun fn-native-hybrid-control-author-encode
    (keyring-generation source ed-signature ml-signature ml-path)
  (declare (xargs :guard t))
  (if (not (and (fn-record-uint32p keyring-generation)
                (fn-cbor-octet-listp source)
                (consp source) (<= (len source) *fn-article-max-octets*)
                (fn-hsig-exact-octets-p ed-signature 64)
                (fn-hsig-exact-octets-p ml-signature 3309))) :bad
    (fn-nhctrl-seal
     *fn-nhctrl-author-kind* *fn-nhctrl-author-spec*
     (list keyring-generation source ed-signature ml-signature ml-path))))

(defun fn-native-hybrid-control-author-decode (octets)
  (declare (xargs :guard t))
  (let ((v (fn-nhctrl-open-values octets *fn-nhctrl-author-kind*
                                  *fn-nhctrl-author-spec*)))
    (if (and (true-listp v)
             (equal (len v) 5)
             (fn-record-uint32p (nth 0 v))
             (fn-cbor-at-mostp (nth 1 v) *fn-article-max-octets*)
             (consp (nth 1 v))
             (fn-hsig-exact-octets-p (nth 2 v) 64)
             (fn-hsig-exact-octets-p (nth 3 v) 3309))
        (cons :hybrid-author v) nil)))

(defun fn-native-hybrid-control-revoke-encode (keyring-generation principal)
  (declare (xargs :guard t))
  (if (not (and (fn-record-uint32p keyring-generation)
                (fn-hsig-exact-octets-p principal 32))) :bad
    (fn-nhctrl-seal *fn-nhctrl-revoke-kind* *fn-nhctrl-revoke-spec*
                    (list keyring-generation principal))))

(defun fn-native-hybrid-control-revoke-decode (octets)
  (declare (xargs :guard t))
  (let ((v (fn-nhctrl-open-values octets *fn-nhctrl-revoke-kind*
                                  *fn-nhctrl-revoke-spec*)))
    (if (and (true-listp v)
             (equal (len v) 2)
             (fn-record-uint32p (nth 0 v))
             (fn-hsig-exact-octets-p (nth 1 v) 32))
        (cons :hybrid-revoke v) nil)))
