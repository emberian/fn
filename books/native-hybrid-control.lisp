(in-package "ACL2")
(include-book "native-control")
(include-book "hybrid-lifecycle")
(include-book "native-admin-shape")
(include-book "consumer-position")

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
; keys (32, 32 and 1 952 octets), the authored source, the Ed25519 and ML-DSA
; signatures (64 and 3 309) and the principal (32).  A value of those sizes
; encodes to the same octets as under the earlier `:blob' specs, and the
; decoders still check each size.
(defconst *fn-nhctrl-enroll-spec*
  '(:nat (:blob . 32) (:blob . 32) (:blob . 1952)))
; PKT-codex-003 (Mini/DREGG's upstream request, 2026-09-27): the author
; request's source field was the v1 carrier's (`*fn-hsig-v1-max-source*',
; 65 535), so a v2 source the served POST accepts (Mini's 191 283-octet grain
; origin) was refused here.  The field is now as wide as the frame's u32
; payload leaves beside the other four fields: a codec width, not a policy.
; Whether the node takes the article is its profile's A, decided at
; injection, exactly as for `operator post'.
(defun fn-nhctrl-author-spec-at (width)
  (declare (xargs :guard t))
  (list :nat (cons :blob width) '(:blob . 64) '(:blob . 3309) :text))
; The author payload's octets outside its source: the generation (8), the
; source's u32 length (4), the two signatures with theirs (68 and 3 313) and
; the key path's text (2 + 512).
(defconst *fn-nhctrl-author-fixed-width*
  (+ 8 4 (+ 4 64) (+ 4 3309) (+ 2 *fn-frame-max-text*)))
(defconst *fn-nhctrl-max-source*
  (- *fn-frame-max-payload* *fn-nhctrl-author-fixed-width*))
(defconst *fn-nhctrl-author-spec*
  (fn-nhctrl-author-spec-at *fn-nhctrl-max-source*))
(defconst *fn-nhctrl-revoke-spec* '(:nat (:blob . 32)))
(defconst *fn-nhctrl-enroll-next-spec*
  '((:blob . 32) (:blob . 32) (:blob . 1952)))
(defconst *fn-nhctrl-revoke-next-spec* '((:blob . 32)))
; The frame decoder's cap is the widest spec's width: the author request at
; its widest source, which is the frame's own u32 payload width.
(defconst *fn-nhctrl-max-payload*
  (max (fn-frame-specs-width *fn-nhctrl-author-spec*)
       (max (fn-frame-specs-width *fn-nhctrl-enroll-spec*)
            (fn-frame-specs-width *fn-nhctrl-revoke-spec*))))
; The widest request other than an author request (enrolment is the widest).
(defconst *fn-nhctrl-key-payload*
  (max (fn-frame-specs-width *fn-nhctrl-enroll-spec*)
       (max (fn-frame-specs-width *fn-nhctrl-revoke-spec*)
            (max (fn-frame-specs-width *fn-nhctrl-enroll-next-spec*)
                 (fn-frame-specs-width *fn-nhctrl-revoke-next-spec*)))))

(defthm fn-nhctrl-author-spec-width
  (implies (and (posp width) (<= width *fn-cbor-max-uint*))
           (equal (fn-frame-specs-width (fn-nhctrl-author-spec-at width))
                  (+ *fn-nhctrl-author-fixed-width* width)))
  :hints (("Goal" :in-theory (enable fn-frame-specs-width fn-frame-field-width
                                     fn-frame-wide-blob-specp))))

(defthm fn-nhctrl-max-payload-is-the-frame-width
  (equal *fn-nhctrl-max-payload* *fn-frame-max-payload*)
  :rule-classes nil)

; Every source a Store could hold fits the request: the stored carrier ends
; with the exact source (books/hybrid-store-invariants.lisp), and no article
; is longer than `*fn-article-max-octets*'.
(defthm fn-nhctrl-author-request-covers-every-storable-article
  (< *fn-article-max-octets* *fn-nhctrl-max-source*)
  :rule-classes nil)

; The owner's read bound for one control connection when hybrid control is
; loaded: an ordinary FNCT request under the profile's A and G, a key
; request, or an author request whose source is at most A octets (a longer
; source makes a carrier past A, which injection refuses by name).  Before
; D27 the hybrid bound replaced the ordinary one, which capped `operator
; post' at 65 536 octets whenever hybrid control was built in.
(defun fn-nhctrl-author-frame-for (a)
  (declare (xargs :guard t))
  (+ *fn-frame-overhead-octets* *fn-nhctrl-author-fixed-width*
     (min (nfix a) *fn-nhctrl-max-source*)))

(defun fn-nhctrl-read-bound-for (a g)
  (declare (xargs :guard t))
  (max (fn-nctrl-read-bound-for a g)
       (max (+ *fn-frame-overhead-octets* *fn-nhctrl-key-payload*)
            (fn-nhctrl-author-frame-for a))))

(defthm fn-nhctrl-read-bound-covers-both
  (and (<= (fn-nctrl-read-bound-for a g) (fn-nhctrl-read-bound-for a g))
       (<= (+ *fn-frame-overhead-octets* *fn-nhctrl-key-payload*)
           (fn-nhctrl-read-bound-for a g))
       (<= (fn-nhctrl-author-frame-for a) (fn-nhctrl-read-bound-for a g)))
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
                (consp source) (<= (len source) *fn-nhctrl-max-source*)
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
             (fn-cbor-at-mostp (nth 1 v) *fn-nhctrl-max-source*)
             (consp (nth 1 v))
             (fn-hsig-exact-octets-p (nth 2 v) 64)
             (fn-hsig-exact-octets-p (nth 3 v) 3309))
        (cons :hybrid-author v) nil)))

;; ---------------------------------------------------------------------------
;; PKT-codex-003: the author request the owner's read bound admits.
(local
 (defthm fn-nhctrl-seal-length
   (implies (and (fn-cbor-octetp kind)
                 (not (equal (fn-nhctrl-seal kind specs values) :bad)))
            (equal (len (fn-nhctrl-seal kind specs values))
                   (+ *fn-frame-overhead-octets*
                      (len (fn-frame-fields-octets specs values)))))
   :hints (("Goal"
            :do-not-induct t
            :in-theory (e/d (fn-nhctrl-seal fn-frame-protected
                             fn-frame-digestp fn-frame-magicp
                             fn-frame-len-of-append)
                            (fn-frame-fields-octets fn-frame-values-okp
                             fn-frame-spec-listp))
            :use ((:instance fn-frame-fields-octets-are-octets)
                  (:instance fn-frame-header-octets
                             (magic *fn-nctrl-magic*)
                             (version *fn-nctrl-version*)
                             (length (len (fn-frame-fields-octets specs values))))
                  (:instance fn-frame-trailer-is-a-digest
                             (octets
                              (fn-frame-protected
                               *fn-nctrl-magic* *fn-nctrl-version*
                               kind (fn-frame-fields-octets specs values)))))))))

(local
 (defthm fn-nhctrl-seal-checks-its-values
   (implies (not (equal (fn-nhctrl-seal kind specs values) :bad))
            (fn-frame-values-okp specs values))
   :hints (("Goal" :in-theory (e/d (fn-nhctrl-seal)
                                   (fn-frame-values-okp fn-frame-protected
                                    fn-frame-trailer))))))

(local
 (defthm fn-nhctrl-at-mostp-len
   (implies (and (fn-cbor-at-mostp xs n) (natp n))
            (<= (len xs) n))
   :rule-classes :linear
   :hints (("Goal" :induct (fn-cbor-at-mostp xs n)
            :in-theory (enable fn-cbor-at-mostp)))))

(local
 (defthm fn-nhctrl-author-fields-length
   (implies (fn-frame-values-okp *fn-nhctrl-author-spec* (list g s e m p))
            (<= (len (fn-frame-fields-octets *fn-nhctrl-author-spec*
                                             (list g s e m p)))
                (+ *fn-nhctrl-author-fixed-width* (len s))))
   :rule-classes :linear
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-frame-textp-len-bound (value p)))
            :in-theory (e/d (fn-frame-fields-octets fn-frame-field-octets
                             fn-frame-values-okp fn-frame-field-okp
                             fn-frame-wide-blob-specp fn-frame-len-of-append
                             fn-frame-u32-bytes-len fn-frame-u16-bytes-len
                             fn-frame-u64-bytes-len fn-frame-blob-withinp)
                            (fn-cbor-u32-bytes fn-cbor-u16-bytes
                             fn-frame-u64-bytes fn-frame-textp))))))

;  KEYSTONE (the hybrid read bound admits every author request its profile
; admits).  Under a profile whose article bound is A, every author request
; (`fn-native-hybrid-control-author-encode', which the client calls through
; `fn-native-hybrid-control-host-author-encode' in host/native/hybrid-control.lisp
; `fnn-command-hybrid-author') whose source is at most A octets is at most
; `fn-nhctrl-read-bound-for A G' octets, the bound the owner reads a control
; connection under (host/native/control.lisp `fnn-control-start' through
; `fn-native-hybrid-control-host-read-bound').  So a v2 source (past 65 535
; octets) reaches the owner whole, and the injection decision is what
; refuses a carrier past A.
(defthm fn-native-hybrid-control-author-request-within-read-bound
  (let ((request (fn-native-hybrid-control-author-encode
                  keyring-generation source ed-signature ml-signature ml-path)))
    (implies (and (natp a)
                  (<= (len source) a)
                  (not (equal request :bad)))
             (<= (len request) (fn-nhctrl-read-bound-for a g))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-native-hybrid-control-author-encode)
                           (fn-nhctrl-seal fn-frame-fields-octets
                            fn-frame-values-okp fn-nctrl-read-bound-for))
           :use ((:instance fn-nhctrl-seal-checks-its-values
                            (kind *fn-nhctrl-author-kind*)
                            (specs *fn-nhctrl-author-spec*)
                            (values (list keyring-generation source ed-signature
                                          ml-signature ml-path)))
                 (:instance fn-nhctrl-seal-length
                            (kind *fn-nhctrl-author-kind*)
                            (specs *fn-nhctrl-author-spec*)
                            (values (list keyring-generation source ed-signature
                                          ml-signature ml-path)))
                 (:instance fn-nhctrl-author-fields-length
                            (g keyring-generation) (s source) (e ed-signature)
                            (m ml-signature) (p ml-path))))))

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

;; ---------------------------------------------------------------------------
;; PKT-147 (control-across-peers, PRF-170): the signed-author ingress names
;; every refusal.  host/native/hybrid-control.lisp `fnn-hybrid-control-author'
;; answers each refusing arm with this word: ARM names the arm and REASON is
;; the ACL2 reason that arm's decision returned (the carrier plan's,
;; books/hybrid-store-injected.lisp `fn-hsig-injected-carrier-reason'; the
;; filing plan's, books/peer-authored-accept.lisp `fn-pa-filing-plan'), or
;; nil where the decision answers only nil (no current enrolment, no source
;; fields, no signed Store event).  The words are control statuses
;; (`*fn-nctrl-statuses*'), each a refusal (exit 1).
(defun fn-nhc-author-refusal (arm reason)
  (declare (xargs :guard t))
  (cond ((equal arm :enrollment) :author-not-enrolled)
        ((equal arm :source) :source-malformed)
        ((equal arm :carrier)
         (cond ((equal reason :unknown-group) :unknown-group)
               ((equal reason :oversize) :article-exceeds-profile-bound)
               (t :carrier-refused)))
        ((equal arm :filing)
         (if (member-equal reason '(:control-not-filed :control-malformed))
             reason
           :refused))
        ((equal arm :event) :signed-event-not-formed)
        (t :refused)))

(defthm fn-nhc-author-refusal-is-a-named-refusal
  (let ((word (fn-nhc-author-refusal arm reason)))
    (and (member-equal word *fn-nctrl-statuses*)
         (equal (fn-native-control-status-class word) :refused)
         (equal (fn-native-control-status-exit-code word) 1)))
  :rule-classes nil)

;; The carrier's :unknown-group (a named newsgroup is not served here) is
;; answered as itself, never as the plain refusal.
(defthm fn-nhc-author-refusal-names-an-unserved-group
  (equal (equal (fn-nhc-author-refusal :carrier reason) :unknown-group)
         (equal reason :unknown-group)))
