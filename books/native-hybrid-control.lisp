(in-package "ACL2")
(include-book "native-control")
(include-book "hybrid-lifecycle")
(include-book "native-admin-shape")

(defconst *fn-nhctrl-enroll-kind* 4)
(defconst *fn-nhctrl-author-kind* 5)
(defconst *fn-nhctrl-revoke-kind* 6)
; PRF-098: the next-generation requests.  The operator names no generation;
; the owner asks ACL2 for it (books/hybrid-lifecycle.lisp
; fn-hl-next-generation) under its serialized Store coordinates.  Kinds 4
; and 6 keep their explicit generation, and 0 there means nothing.
(defconst *fn-nhctrl-enroll-next-kind* 7)
(defconst *fn-nhctrl-revoke-next-kind* 8)
; Field widths are the exact values each field carries (D27): the enrolment
; keys (32, 32 and 1 952 octets), the v1 authored source (at most
; `*fn-hsig-v1-max-source*'), the Ed25519 and ML-DSA signatures (64 and 3 309)
; and the principal (32).  A value of those sizes encodes to the same octets
; as under the earlier `:blob' specs, and the decoders still check each size.
(defconst *fn-nhctrl-enroll-spec*
  '(:nat (:blob . 32) (:blob . 32) (:blob . 1952)))
(defconst *fn-nhctrl-author-spec*
  (list :nat (cons :blob *fn-hsig-v1-max-source*) '(:blob . 64)
        '(:blob . 3309) :text))
(defconst *fn-nhctrl-revoke-spec* '(:nat (:blob . 32)))
(defconst *fn-nhctrl-enroll-next-spec*
  '((:blob . 32) (:blob . 32) (:blob . 1952)))
(defconst *fn-nhctrl-revoke-next-spec* '((:blob . 32)))
; The hybrid payload cap is its widest spec's width, the author request at
; the v1 source ceiling (a codec width; before D27 a fixed 65 536, which
; refused a v1 source above about 62 000 octets).
(defconst *fn-nhctrl-max-payload*
  (max (fn-frame-specs-width *fn-nhctrl-author-spec*)
       (max (fn-frame-specs-width *fn-nhctrl-enroll-spec*)
            (fn-frame-specs-width *fn-nhctrl-revoke-spec*))))

; The owner's read bound for one control connection when hybrid control is
; loaded: an ordinary FNCT request under the profile's A and G, or a hybrid
; request (host/native/control.lisp `fnn-control-start').  Before D27 the
; hybrid bound replaced the ordinary one, which capped `operator post' at
; 65 536 octets whenever hybrid control was built in.
(defun fn-nhctrl-read-bound-for (a g)
  (declare (xargs :guard t))
  (max (fn-nctrl-read-bound-for a g)
       (+ *fn-frame-overhead-octets* *fn-nhctrl-max-payload*)))

(defthm fn-nhctrl-read-bound-covers-both
  (and (<= (fn-nctrl-read-bound-for a g) (fn-nhctrl-read-bound-for a g))
       (<= (+ *fn-frame-overhead-octets* *fn-nhctrl-max-payload*)
           (fn-nhctrl-read-bound-for a g)))
  :rule-classes nil)

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
                (consp source) (<= (len source) *fn-hsig-v1-max-source*)
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
             (fn-cbor-at-mostp (nth 1 v) *fn-hsig-v1-max-source*)
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

(defun fn-native-hybrid-control-enroll-next-encode (principal ed-key ml-key)
  (declare (xargs :guard t))
  (if (not (and (fn-hsig-exact-octets-p principal 32)
                (fn-hsig-exact-octets-p ed-key 32)
                (fn-hsig-exact-octets-p ml-key 1952))) :bad
    (fn-nhctrl-seal *fn-nhctrl-enroll-next-kind* *fn-nhctrl-enroll-next-spec*
                    (list principal ed-key ml-key))))

(defun fn-native-hybrid-control-enroll-next-decode (octets)
  (declare (xargs :guard t))
  (let ((v (fn-nhctrl-open-values octets *fn-nhctrl-enroll-next-kind*
                                  *fn-nhctrl-enroll-next-spec*)))
    (if (and (true-listp v)
             (equal (len v) 3)
             (fn-hsig-exact-octets-p (nth 0 v) 32)
             (fn-hsig-exact-octets-p (nth 1 v) 32)
             (fn-hsig-exact-octets-p (nth 2 v) 1952))
        (cons :hybrid-enroll-next v) nil)))

(defun fn-native-hybrid-control-revoke-next-encode (principal)
  (declare (xargs :guard t))
  (if (not (fn-hsig-exact-octets-p principal 32)) :bad
    (fn-nhctrl-seal *fn-nhctrl-revoke-next-kind* *fn-nhctrl-revoke-next-spec*
                    (list principal))))

(defun fn-native-hybrid-control-revoke-next-decode (octets)
  (declare (xargs :guard t))
  (let ((v (fn-nhctrl-open-values octets *fn-nhctrl-revoke-next-kind*
                                  *fn-nhctrl-revoke-next-spec*)))
    (if (and (true-listp v)
             (equal (len v) 1)
             (fn-hsig-exact-octets-p (nth 0 v) 32))
        (cons :hybrid-revoke-next v) nil)))

; The owner's events for the two requests: the lifecycle constructors at
; ACL2's next generation.  host/native/hybrid-control.lisp calls these
; through host/native-hybrid-control-host.lisp.
(defun fn-native-hybrid-control-enroll-next-event
    (sequence txid store-generation principal keys snapshots)
  (declare (xargs :guard t))
  (fn-hl-enroll-event sequence txid store-generation
                      (fn-hl-next-generation snapshots) principal keys
                      snapshots))

(defun fn-native-hybrid-control-revoke-next-event
    (sequence txid store-generation principal snapshots)
  (declare (xargs :guard t))
  (fn-hl-revoke-event sequence txid store-generation
                      (fn-hl-next-generation snapshots) principal snapshots))

; The request is ACL2's: an event it builds is at exactly the generation
; after the Store's newest snapshot (1 for an empty keyring).
(defthm fn-native-hybrid-control-enroll-next-event-is-at-the-next-generation
  (let ((e (fn-native-hybrid-control-enroll-next-event
            sequence txid store-generation principal keys snapshots)))
    (implies e
             (equal (fn-stxk-keyring-generation e)
                    (fn-hl-next-generation snapshots))))
  :hints (("Goal" :in-theory (disable fn-hl-enroll-event fn-hl-next-generation)
           :use ((:instance fn-hl-enroll-event-enrolls-its-keys
                            (keyring-generation (fn-hl-next-generation snapshots)))))))

(defthm fn-native-hybrid-control-revoke-next-event-is-at-the-next-generation
  (let ((e (fn-native-hybrid-control-revoke-next-event
            sequence txid store-generation principal snapshots)))
    (implies e
             (equal (fn-stxk-keyring-generation e)
                    (fn-hl-next-generation snapshots))))
  :hints (("Goal" :in-theory (disable fn-hl-revoke-event fn-hl-next-generation)
           :use ((:instance fn-hl-revoke-event-is-the-principals-tombstone
                            (keyring-generation (fn-hl-next-generation snapshots)))))))
