(in-package "ACL2")
(include-book "native-control")
(include-book "hybrid-store")

(defconst *fn-nhctrl-enroll-kind* 4)
(defconst *fn-nhctrl-author-kind* 5)
(defconst *fn-nhctrl-max-payload* 65536)
(defconst *fn-nhctrl-enroll-spec* '(:nat :blob :blob :blob))
(defconst *fn-nhctrl-author-spec*
  '(:nat :text :blob :blob :blob :text :blob :text :text :text :nat))

(defun fn-nhctrl-seal (kind specs values)
  (declare (xargs :guard t))
  (if (not (and (fn-frame-spec-listp specs)
                (fn-frame-values-okp specs values))) :bad
    (let ((payload (fn-frame-fields-octets specs values)))
      (if (< *fn-nhctrl-max-payload* (len payload)) :bad
        (let ((protected (fn-frame-protected *fn-nctrl-magic*
                                             *fn-nctrl-version* kind payload)))
          (append protected (fn-frame-trailer protected)))))))

(defun fn-nhctrl-open-values (octets kind specs)
  (declare (xargs :guard t))
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
    (if (and (equal (len v) 4)
             (fn-record-uint32p (nth 0 v))
             (fn-hsig-exact-octets-p (nth 1 v) 32)
             (fn-hsig-exact-octets-p (nth 2 v) 32)
             (fn-hsig-exact-octets-p (nth 3 v) 1952))
        (cons :hybrid-enroll v) nil)))

(defun fn-native-hybrid-control-author-encode
    (keyring-generation msgid source ed-signature ml-signature ml-path groups
                        obligation content-subject release charge)
  (declare (xargs :guard t))
  (if (not (and (fn-record-uint32p keyring-generation)
                (fn-af-message-idp msgid)
                (fn-cbor-octet-listp source)
                (consp source) (<= (len source) *fn-article-max-octets*)
                (fn-hsig-exact-octets-p ed-signature 64)
                (fn-hsig-exact-octets-p ml-signature 3309)
                (fn-inj-group-namesp groups)
                (fn-record-uint32p charge))) :bad
    (fn-nhctrl-seal
     *fn-nhctrl-author-kind* *fn-nhctrl-author-spec*
     (list keyring-generation msgid source ed-signature ml-signature ml-path
           (fn-nctrl-groups-encode groups) obligation content-subject release charge))))

(defun fn-native-hybrid-control-author-decode (octets)
  (declare (xargs :guard t))
  (let ((v (fn-nhctrl-open-values octets *fn-nhctrl-author-kind*
                                  *fn-nhctrl-author-spec*)))
    (if (not (equal (len v) 11)) nil
      (let ((groups (fn-nctrl-groups-decode (nth 6 v))))
        (if (and (fn-record-uint32p (nth 0 v))
                 (fn-af-message-idp (nth 1 v))
                 (fn-cbor-at-mostp (nth 2 v) *fn-article-max-octets*)
                 (consp (nth 2 v))
                 (fn-hsig-exact-octets-p (nth 3 v) 64)
                 (fn-hsig-exact-octets-p (nth 4 v) 3309)
                 (fn-record-parse-okp groups)
                 (fn-record-uint32p (nth 10 v)))
            (list :hybrid-author (nth 0 v) (nth 1 v) (nth 2 v)
                  (nth 3 v) (nth 4 v) (nth 5 v)
                  (fn-record-parse-value groups) (nth 7 v) (nth 8 v)
                  (nth 9 v) (nth 10 v)) nil)))))
