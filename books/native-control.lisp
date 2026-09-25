; fn: bounded local-control framing for exact authored article submission.
;
; One Unix-stream connection carries one sealed request, then one sealed reply.
; The host may bound and transport these octets; ACL2 owns their grammar, field
; validation, result vocabulary and CLI exit projection.

(in-package "ACL2")
(include-book "frame-trailer")
(include-book "frame-invariants")
(include-book "records-invariants")
(include-book "injection")
(include-book "native-config")
(include-book "native-admin-shape")

(defconst *fn-nctrl-magic* '(70 78 67 84)) ; FNCT
(defconst *fn-nctrl-version* 1)
(defconst *fn-nctrl-request-kind* 1)
(defconst *fn-nctrl-reply-kind* 2)
(defconst *fn-nctrl-admin-kind* 3)
(defconst *fn-nctrl-request-spec* '(:blob :text :blob))
(defconst *fn-nctrl-statuses*
  '(:accepted :duplicate :refused :clock-unusable :busy :uncertain :fault))
(defconst *fn-nctrl-reply-spec* (list (cons :enum *fn-nctrl-statuses*)))

; The FNCT request payload at its field widths (`*fn-nctrl-request-spec*'):
; the article blob, the Message-ID text and the CBOR group list blob, each
; with its length head.  These are the FNCT codec's widths, not the article
; bound: the owner applies the profile's article bound to the decoded article,
; as every served path does.  The article field is a frame blob, so the
; control socket carries at most `*fn-frame-max-blob*' octets of article
; whatever the profile allows (design 2026-09-25-bounds §2.3 row "Frame
; :blob", open: a per-schema blob width).  This is also the work bound of one
; control read: the owner reads at most this frame from a client.
(defconst *fn-nctrl-max-payload*
  (+ 4 *fn-frame-max-blob*
     2 *fn-frame-max-text*
     4 *fn-frame-max-blob*))
(defconst *fn-nctrl-max-frame*
  (+ *fn-frame-overhead-octets* *fn-nctrl-max-payload*))
; The article parser's ceiling is the record codec's payload ceiling: an
; article the parser can accept is a payload the record can carry.
(defthm fn-nctrl-article-ceiling-is-the-record-payload-ceiling
  (equal *fn-article-max-octets* *fn-record-max-payload*)
  :rule-classes nil)

(defthm fn-nctrl-max-frame-within-frame-width
  (<= *fn-nctrl-max-payload* *fn-frame-max-payload*)
  :rule-classes nil)
; Work bound: concurrent control clients the owner serves.
(defconst *fn-nctrl-max-active-clients* 16)
(defconst *fn-nctrl-lease-suffix* '(46 108 111 99 107)) ; .lock
(defconst *fn-nctrl-max-lease-path* (+ *fn-ncfg-max-path* 5))

(defun fn-native-control-lease-path (control-path)
  "Derive the one adjacent lease name before raw code opens any path."
  (declare (xargs :guard t))
  (if (and (fn-cbor-octet-listp control-path)
           (consp control-path)
           (<= (len control-path) *fn-ncfg-max-path*))
      (append control-path *fn-nctrl-lease-suffix*)
    :bad))

(defun fn-nctrl-group-strings (groups)
  (declare (xargs :guard t))
  (if (consp groups)
      (cons (fn-record-octets-string (car groups))
            (fn-nctrl-group-strings (cdr groups)))
    nil))

(defun fn-nctrl-group-octets (groups)
  (declare (xargs :guard t))
  (if (consp groups)
      (cons (fn-record-string-octets (car groups))
            (fn-nctrl-group-octets (cdr groups)))
    nil))

(defun fn-nctrl-requestp (msgid groups article)
  (declare (xargs :guard t))
  (let ((names (fn-nctrl-group-strings groups)))
    (and (fn-af-message-idp msgid)
         (fn-inj-group-namesp groups)
         (consp groups)
         (fn-record-groupsp names)
         (fn-cbor-octet-listp article)
         (consp article)
         (<= (len article) *fn-article-max-octets*))))

(defun fn-nctrl-groups-encode (groups)
  (declare (xargs :guard t))
  (let ((names (fn-nctrl-group-strings groups)))
    (if (not (fn-record-groupsp names))
        nil
      (append (fn-cbor-encode (cons :uint (len names)))
              (fn-record-encode-groups names)))))

(defun fn-nctrl-groups-decode (octets)
  (declare (xargs :guard t))
  (if (not (fn-cbor-octet-listp octets))
      (fn-record-parse-error :groups)
    (let ((counted (fn-record-read-uint octets)))
      (if (not (fn-record-parse-okp counted))
          (fn-record-parse-error :groups)
        (let ((count (fn-record-parse-value counted)))
          (if (or (not (natp count)) (zp count)
                  (< *fn-record-max-groups* count))
              (fn-record-parse-error :groups)
            (let ((rest (fn-record-parse-rest counted)))
              (if (not (fn-cbor-octet-listp rest))
                  (fn-record-parse-error :groups)
                (let ((parsed (fn-record-parse-groups count rest)))
                  (if (or (not (fn-record-parse-okp parsed))
                          (consp (fn-record-parse-rest parsed)))
                      (fn-record-parse-error :groups)
                    (fn-record-parse-ok
                     (fn-nctrl-group-octets (fn-record-parse-value parsed))
                     nil)))))))))))

; Administrative argv is its own ordered vector grammar.  It shares the
; count-plus-bytes representation with group lists, but deliberately does not
; inherit group-name width or uniqueness rules: an argv word is an ASCII,
; nonempty octet list of at most 512 octets, and repeated words are ordinary.
(defun fn-nctrl-admin-words-encode (argv)
  (declare (xargs :guard t))
  (if (not (fn-native-admin-argvp argv))
      nil
    (if (consp argv)
        (append (fn-cbor-encode (cons :bytes (car argv)))
                (fn-nctrl-admin-words-encode (cdr argv)))
      nil)))

(defun fn-nctrl-admin-argv-encode (argv)
  (declare (xargs :guard t))
  (if (not (fn-native-admin-argvp argv))
      nil
    (append (fn-cbor-encode (cons :uint (len argv)))
            (fn-nctrl-admin-words-encode argv))))

(defun fn-nctrl-admin-words-decode (count octets)
  (declare (xargs :guard t))
  (if (not (and (natp count) (fn-cbor-octet-listp octets)))
      (fn-record-parse-error :arguments)
    (if (zp count)
        (fn-record-parse-ok nil octets)
      (let ((first (fn-record-read-bytes octets)))
        (if (not (fn-record-parse-okp first))
            first
          (let ((word (fn-record-parse-value first)))
            (if (not (and (consp word)
                          (<= (len word) *fn-native-admin-max-argument-octets*)
                          (fn-record-ascii-octet-listp word)))
                (fn-record-parse-error :argument)
              (let ((tail (fn-nctrl-admin-words-decode
                           (1- count) (fn-record-parse-rest first))))
                (if (not (fn-record-parse-okp tail))
                    tail
                  (fn-record-parse-ok
                   (cons word (fn-record-parse-value tail))
                   (fn-record-parse-rest tail)))))))))))

(defun fn-nctrl-admin-argv-decode (octets)
  ; `zp' of the decoded count needs the count to be a natural.  The bounded
  ; record codec (2026-09-21) no longer yields that by opening, and the
  ; `natp' rewrite rule does not match the (integerp ...) and (<= 0 ...)
  ; halves the guard conjecture asks for, so the domain lemma from
  ; books/records is used closed, with the parser accessors disabled.
  (declare (xargs :guard t
                  :guard-hints
                  (("Goal"
                    :use ((:instance fn-record-read-uint-success-domain
                                     (octets octets)))
                    :in-theory (disable fn-record-read-uint
                                        fn-record-parse-okp
                                        fn-record-parse-value
                                        fn-record-parse-rest)))))
  (if (not (fn-cbor-octet-listp octets))
      (fn-record-parse-error :arguments)
    (let ((counted (fn-record-read-uint octets)))
      (if (not (fn-record-parse-okp counted))
          (fn-record-parse-error :arguments)
        (let ((count (fn-record-parse-value counted)))
          (if (or (zp count) (< *fn-native-admin-max-arguments* count))
              (fn-record-parse-error :arguments)
            (let ((parsed (fn-nctrl-admin-words-decode
                           count (fn-record-parse-rest counted))))
              (if (or (not (fn-record-parse-okp parsed))
                      (consp (fn-record-parse-rest parsed)))
                  (fn-record-parse-error :arguments)
                parsed))))))))

(defun fn-nctrl-seal (kind payload)
  (declare (xargs :guard t))
  (if (not (and (fn-cbor-octetp kind)
                (fn-cbor-octet-listp payload)
                (<= (len payload) *fn-nctrl-max-payload*)))
      :bad
    (let ((protected (fn-frame-protected *fn-nctrl-magic*
                                         *fn-nctrl-version* kind payload)))
      (append protected (fn-frame-trailer protected)))))

(defun fn-native-control-request-encode (msgid groups article)
  (declare (xargs :guard t))
  (if (not (fn-nctrl-requestp msgid groups article))
      :bad
    (let ((values (list article msgid (fn-nctrl-groups-encode groups))))
      (if (not (fn-frame-values-okp *fn-nctrl-request-spec* values))
          :bad
        (let ((payload
               (fn-frame-fields-octets *fn-nctrl-request-spec* values)))
          (fn-nctrl-seal *fn-nctrl-request-kind* payload))))))

(defun fn-native-control-admin-encode (argv)
  ; The argv budget is one bound, applied on both sides: `fn-native-admin-plan'
  ; refuses more than *fn-native-admin-max-arguments* with :argv and
  ; `fn-nctrl-admin-argv-decode' refuses the count, so an encoder without it
  ; emits a frame its own decoder must refuse.
  (declare (xargs :guard t))
  (if (or (not (fn-native-admin-argvp argv)) (not (consp argv))
          (< *fn-native-admin-max-arguments* (len argv)))
      :bad
    (let ((payload (fn-nctrl-admin-argv-encode argv)))
      (if payload (fn-nctrl-seal *fn-nctrl-admin-kind* payload) :bad))))

(defun fn-nctrl-open (octets expected-kind)
  (declare (xargs :guard t))
  (if (not (fn-cbor-octet-listp octets))
      (fn-frame-error :malformed)
    (let ((opened
           (fn-frame-decode octets
                            (fn-frame-trailer
                             (fn-frame-protected-prefix octets))
                            *fn-nctrl-max-payload*)))
      (if (and (fn-frame-result-okp opened)
               (equal (fn-frame-result-magic opened) *fn-nctrl-magic*)
               (equal (fn-frame-result-version opened) *fn-nctrl-version*)
               (equal (fn-frame-result-kind opened) expected-kind))
          opened
        (fn-frame-error :control-frame)))))

(defun fn-native-control-request-decode (octets)
  (declare (xargs :guard t))
  (let ((opened (fn-nctrl-open octets *fn-nctrl-request-kind*)))
    (if (not (fn-frame-result-okp opened))
        (list :refused :frame)
      (let ((payload (fn-frame-result-payload opened)))
        (if (not (fn-cbor-octet-listp payload))
            (list :refused :frame)
          (let ((fields (fn-frame-fields-parse
                         *fn-nctrl-request-spec* payload)))
            (if (not (fn-frame-parse-okp fields))
                (list :refused :fields)
              (let ((values (fn-frame-parse-value fields)))
            (if (not (and (true-listp values) (equal (len values) 3)))
                (list :refused :fields)
              (let* ((article (nth 0 values))
                     (msgid (nth 1 values))
                     (groups-result (fn-nctrl-groups-decode (nth 2 values)))
                     (groups (and (fn-record-parse-okp groups-result)
                                  (fn-record-parse-value groups-result))))
                (if (not (and groups
                              (fn-nctrl-requestp msgid groups article)))
                    (list :refused :request)
                  (list :request msgid groups article))))))))))))

(defun fn-native-control-admin-decode (octets)
  (declare (xargs :guard t))
  (let ((opened (fn-nctrl-open octets *fn-nctrl-admin-kind*)))
    (if (not (fn-frame-result-okp opened))
        (list :refused :frame)
      (let ((parsed (fn-nctrl-admin-argv-decode
                     (fn-frame-result-payload opened))))
        (if (not (fn-record-parse-okp parsed))
            (list :refused :arguments)
          (let ((argv (fn-record-parse-value parsed)))
            (if (and (consp argv) (fn-native-admin-argvp argv))
                (list :admin argv)
              (list :refused :arguments))))))))

(defun fn-native-control-reply-encode (status)
  (declare (xargs :guard t))
  (if (not (member-equal status *fn-nctrl-statuses*))
      :bad
    (let ((values (list status)))
      (if (not (fn-frame-values-okp *fn-nctrl-reply-spec* values))
          :bad
        (fn-nctrl-seal
         *fn-nctrl-reply-kind*
         (fn-frame-fields-octets *fn-nctrl-reply-spec* values))))))

(defun fn-native-control-reply-decode (octets)
  (declare (xargs :guard t))
  (let ((opened (fn-nctrl-open octets *fn-nctrl-reply-kind*)))
    (if (not (fn-frame-result-okp opened))
        :bad
      (let ((payload (fn-frame-result-payload opened)))
        (if (not (fn-cbor-octet-listp payload))
            :bad
          (let ((fields (fn-frame-fields-parse
                         *fn-nctrl-reply-spec* payload)))
            (if (not (fn-frame-parse-okp fields))
                :bad
              (let ((values (fn-frame-parse-value fields)))
                (if (consp values) (car values) :bad)))))))))

(defun fn-native-control-status-class (status)
  (declare (xargs :guard t))
  (cond ((member-equal status '(:accepted :duplicate)) :accepted)
        ((member-equal status '(:refused :clock-unusable :busy)) :refused)
        ((equal status :uncertain) :uncertain)
        (t :fault)))

(defun fn-native-control-status-exit-code (status)
  (declare (xargs :guard t))
  (case (fn-native-control-status-class status)
    (:accepted 0)
    (:refused 1)
    (:uncertain 3)
    (otherwise 4)))

(defun fn-native-control-transport-outcome (stage)
  "Conservative result when no authenticated reply can be decoded.

Before any request octet is handed to the socket the owner cannot have acted.
After the complete sealed request is handed off, a lost connection cannot
distinguish an unobserved refusal from a durable acceptance."
  (declare (xargs :guard t))
  (case stage
    (:before-submission :refused)
    (:after-submission :uncertain)
    (otherwise :fault)))

(defun fn-native-control-max-active-clients ()
  "The fixed local transport worker ceiling selected by ACL2 policy."
  (declare (xargs :guard t))
  *fn-nctrl-max-active-clients*)

(defthm fn-native-control-max-active-clients-is-positive
  (and (posp (fn-native-control-max-active-clients))
       (<= (fn-native-control-max-active-clients) 64)))

; The generic frame library deliberately exports its ten-octet header and
; 32-octet digest facts separately.  Close that arithmetic here so the reader
; bound below is visibly the actual sealed-frame size, not an unexplained
; larger allowance.
(local
 (defthm fn-nctrl-seal-length
   (implies (and (fn-cbor-octetp kind)
                 (fn-cbor-octet-listp payload)
                 (<= (len payload) *fn-nctrl-max-payload*))
            (equal (len (fn-nctrl-seal kind payload))
                   (+ *fn-frame-overhead-octets* (len payload))))
   :hints (("Goal"
            :do-not-induct t
            :in-theory (enable fn-nctrl-seal fn-frame-protected
                               fn-frame-digestp fn-frame-magicp
                               fn-frame-len-of-append)
            :use ((:instance fn-frame-header-octets
                             (magic *fn-nctrl-magic*)
                             (version *fn-nctrl-version*)
                             (length (len payload)))
                  (:instance fn-frame-trailer-is-a-digest
                             (octets
                              (fn-frame-protected
                               *fn-nctrl-magic* *fn-nctrl-version*
                               kind payload))))))))

(local
 (defthm fn-nctrl-seal-is-bounded
   (<= (len (fn-nctrl-seal kind payload)) *fn-nctrl-max-frame*)
   :hints (("Goal"
            :in-theory (enable fn-nctrl-seal)
            :use ((:instance fn-nctrl-seal-length))))
   :rule-classes :linear))

; The raw reader allocates at most this many octets before ACL2 sees the frame.
(defthm fn-native-control-encoded-request-is-bounded
  (<= (len (fn-native-control-request-encode msgid groups article))
      *fn-nctrl-max-frame*)
  :hints (("Goal" :in-theory (disable fn-nctrl-seal)))
  :rule-classes :linear)

(defthm fn-native-control-lease-path-is-bounded
  (implies (not (equal (fn-native-control-lease-path control-path) :bad))
           (and (fn-cbor-octet-listp
                 (fn-native-control-lease-path control-path))
                (<= (len (fn-native-control-lease-path control-path))
                    *fn-nctrl-max-lease-path*)))
  :hints (("Goal"
           :in-theory (e/d (fn-native-control-lease-path
                            fn-frame-len-of-append)
                           (binary-append len fn-cbor-octet-listp))
           :use ((:instance fn-frame-octet-listp-of-append
                            (a control-path)
                            (b *fn-nctrl-lease-suffix*))))))

(in-theory (disable (:d fn-nctrl-group-strings)
                    (:d fn-nctrl-group-octets)
                    (:d fn-nctrl-requestp)
                    (:d fn-nctrl-groups-encode)
                    (:d fn-nctrl-groups-decode)
                    (:d fn-nctrl-admin-words-encode)
                    (:d fn-nctrl-admin-argv-encode)
                    (:d fn-nctrl-admin-words-decode)
                    (:d fn-nctrl-admin-argv-decode)
                    (:d fn-nctrl-seal)
                    (:d fn-nctrl-open)
                    (:d fn-native-control-lease-path)
                    (:d fn-native-control-request-encode)
                    (:d fn-native-control-request-decode)
                    (:d fn-native-control-reply-encode)
                    (:d fn-native-control-reply-decode)))
