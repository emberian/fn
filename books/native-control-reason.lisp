; fn: the refusal reason on the FNCT wire (PKT-453 (a), PRF-172).
;
; The FNCT reply (books/native-control.lisp) is one enumeration field, and
; its payload is exactly its fields (`fn-frame-fields-parse' refuses a
; trailing octet), so a reason appended to that reply would turn every old
; client's refusal into :bad, which it reports uncertain.  The reason
; therefore travels only to a client that asks for it: the request kinds
; below carry the payloads of kinds 1 and 3 unchanged, and the owner answers
; them, and only them, with the reasoned reply (kind 18: the status, then
; the reason word).  An old client never sends them and never receives one.
; A new client that meets an old owner gets that owner's plain reply to a
; frame it could not decode, `refused', and resends the plain request
; (`fn-native-control-reasoned-reply-read' names that case :legacy).
;
; FNCT kinds: 1 request, 2 reply, 3 admin (native-control), 4-8 hybrid
; (native-hybrid-control), 9-12 and 14 peer invitation and bindings
; (peer-invite); this book takes 13, 17 and 18; 15 and 16 are the live
; `bp-obligation status' and `store retention' requests; 19 and 20 the TLS
; reload; 21 the moderation request (books/moderation-verbs.lisp).

(in-package "ACL2")
(include-book "native-control")

(defconst *fn-nctrl-reasoned-request-kind* 13)
(defconst *fn-nctrl-reasoned-admin-kind* 17)
(defconst *fn-nctrl-reasoned-reply-kind* 18)
; PKT-657/PKT-575 (lane moderation-verbs): the moderation and withdrawal
; request (`fn-native-control-moderation-encode', below; decided by
; books/moderation-verbs.lisp); a new
; request answered only with the reasoned reply.  Kinds 19 and 20 are
; books/tls-reload.lisp's.
(defconst *fn-nctrl-moderation-request-kind* 21)

; The reason field: one word of printable ASCII, at most this many octets
; (a vocabulary word, not operator data: every reason ACL2 names is a
; keyword a few words long).
(defconst *fn-nctrl-max-reason-octets* 512)
(defconst *fn-nctrl-reasoned-reply-spec*
  (list (cons :enum *fn-nctrl-statuses*)
        (cons :blob *fn-nctrl-max-reason-octets*)))

; `NONE' is upper case, which no rendered symbol name is
; (`fn-nctrl-word-chars-octets' folds A-Z), so it never names a reason.
(defconst *fn-nctrl-no-reason-word* '(78 79 78 69))                ; NONE
(defconst *fn-nctrl-unnamed-reason-word* '(117 110 110 97 109 101 100)) ; unnamed

; A symbol name's characters as the word's octets: lower case, printable
; ASCII only, else :bad.
(defun fn-nctrl-word-chars-octets (chars)
  (declare (xargs :guard t))
  (if (consp chars)
      (let ((rest (fn-nctrl-word-chars-octets (cdr chars))))
        (if (and (characterp (car chars)) (not (equal rest :bad)))
            (let ((n (char-code (car chars))))
              (cond ((and (<= 65 n) (<= n 90)) (cons (+ n 32) rest))
                    ((and (<= 33 n) (<= n 126)) (cons n rest))
                    (t :bad)))
          :bad))
    nil))

; The word for a decision's reason: its name for a reason ACL2 named with a
; symbol (`:no-such-grant' is no-such-grant), `NONE' for no reason, and
; `unnamed' for a value that is no printable word (the injection decision's
; open-ended parser words are symbols; anything else is not rendered).
(defun fn-nctrl-reason-word (reason)
  (declare (xargs :guard t))
  (if (null reason)
      *fn-nctrl-no-reason-word*
    (let ((octets (and (symbolp reason)
                       (fn-nctrl-word-chars-octets
                        (coerce (symbol-name reason) 'list)))))
      (if (and (consp octets)
               (fn-cbor-octet-listp octets)
               (<= (len octets) *fn-nctrl-max-reason-octets*))
          octets
        *fn-nctrl-unnamed-reason-word*))))

(defthm fn-nctrl-reason-word-is-a-field
  (let ((w (fn-nctrl-reason-word reason)))
    (and (consp w)
         (fn-cbor-octet-listp w)
         (<= (len w) *fn-nctrl-max-reason-octets*)
         (fn-cbor-at-mostp w *fn-nctrl-max-reason-octets*)))
  :hints (("Goal" :in-theory (enable fn-nctrl-reason-word)
           :use ((:instance fn-cbor-at-mostp-from-length
                            (xs (fn-nctrl-reason-word reason))
                            (bound *fn-nctrl-max-reason-octets*))))))

(in-theory (disable fn-nctrl-reason-word))

; -----------------------------------------------------------------------------
; The requests: kinds 1 and 3's payloads in the reasoned frames.

(defun fn-native-control-reasoned-request-encode (msgid groups article)
  (declare (xargs :guard t))
  (if (not (fn-nctrl-requestp msgid groups article))
      :bad
    (let ((values (list article msgid (fn-nctrl-groups-encode groups))))
      (if (not (fn-frame-values-okp *fn-nctrl-request-spec* values))
          :bad
        (fn-nctrl-seal *fn-nctrl-reasoned-request-kind*
                       (fn-frame-fields-octets *fn-nctrl-request-spec* values))))))

(defun fn-native-control-reasoned-request-decode (octets)
  (declare (xargs :guard t))
  (fn-nctrl-request-payload-decode
   (fn-nctrl-open octets *fn-nctrl-reasoned-request-kind*)))

(defun fn-native-control-reasoned-admin-encode (argv)
  (declare (xargs :guard t))
  (if (or (not (fn-native-admin-argvp argv)) (not (consp argv))
          (not (fn-nctrl-admin-words-widthp argv))
          ; the count is a u32 codec field (a width, not a bound)
          (< *fn-cbor-max-uint* (len argv)))
      :bad
    (let ((payload (fn-nctrl-admin-argv-encode argv)))
      (if payload (fn-nctrl-seal *fn-nctrl-reasoned-admin-kind* payload) :bad))))

(defun fn-native-control-reasoned-admin-decode (octets)
  (declare (xargs :guard t))
  (fn-nctrl-admin-payload-decode
   (fn-nctrl-open octets *fn-nctrl-reasoned-admin-kind*)))

; Whether a frame asked for the reasoned reply: the owner answers such a
; frame, however its handling ends (a refusal, a store error, a fault), with
; kind 18, so a new client reads kind 2 only from an old owner.
(defun fn-native-control-reasoned-framep (octets)
  (declare (xargs :guard t))
  (or (fn-frame-result-okp (fn-nctrl-open octets *fn-nctrl-reasoned-request-kind*))
      (fn-frame-result-okp (fn-nctrl-open octets *fn-nctrl-reasoned-admin-kind*))
      (fn-frame-result-okp (fn-nctrl-open octets
                                          *fn-nctrl-moderation-request-kind*))))

; -----------------------------------------------------------------------------
; The moderation request (PKT-657, PKT-575): FNCT kind 21, (enum OP, bytes
; LOGIN, bytes ID, bytes REASON), decided by books/moderation-verbs.lisp
; `fn-mvb-plan'; answered with the reasoned reply.

(defconst *fn-nctrl-moderation-ops* '(:approve :reject :withdraw))
; LOGIN, ID and REASON may be empty (a withdrawal names no login, an
; approval no reason) and a frame field is never empty, so each travels
; after one octet 1: the field is (1 . OCTETS).
; PKT-867: a field's width is the least control read bound (a field never
; outgrows the frame that carries it; the owner reads the frame under the
; profile's bound), not an argv word bound.
(defconst *fn-nctrl-moderation-field-octets* *fn-nctrl-max-command-frame*)
(defconst *fn-nctrl-moderation-spec*
  (list (cons :enum *fn-nctrl-moderation-ops*)
        (cons :blob *fn-nctrl-moderation-field-octets*)
        (cons :blob *fn-nctrl-moderation-field-octets*)
        (cons :blob *fn-nctrl-moderation-field-octets*)))

(defun fn-native-control-moderation-encode (op login id reason)
  (declare (xargs :guard t))
  (let ((values (list op (cons 1 login) (cons 1 id) (cons 1 reason))))
    (if (not (and (member-equal op *fn-nctrl-moderation-ops*)
                  (true-listp login) (true-listp id) (true-listp reason)
                  (fn-frame-values-okp *fn-nctrl-moderation-spec* values)))
        :bad
      (fn-nctrl-seal *fn-nctrl-moderation-request-kind*
                     (fn-frame-fields-octets *fn-nctrl-moderation-spec* values)))))

(defun fn-nctrl-moderation-field (x)
  (declare (xargs :guard t))
  (if (and (consp x) (equal (car x) 1)) (cdr x) :bad))

(defun fn-native-control-moderation-decode (octets)
  (declare (xargs :guard t))
  (let ((opened (fn-nctrl-open octets *fn-nctrl-moderation-request-kind*)))
    (if (not (fn-frame-result-okp opened))
        :bad
      (let ((payload (fn-frame-result-payload opened)))
        (if (not (fn-cbor-octet-listp payload))
            :bad
          (let ((fields (fn-frame-fields-parse *fn-nctrl-moderation-spec* payload)))
            (if (not (fn-frame-parse-okp fields))
                :bad
              (let ((v (fn-frame-parse-value fields)))
                (if (and (true-listp v) (equal (len v) 4)
                         (not (equal (fn-nctrl-moderation-field (cadr v)) :bad))
                         (not (equal (fn-nctrl-moderation-field (caddr v)) :bad))
                         (not (equal (fn-nctrl-moderation-field (cadddr v)) :bad)))
                    (list :moderation (car v)
                          (fn-nctrl-moderation-field (cadr v))
                          (fn-nctrl-moderation-field (caddr v))
                          (fn-nctrl-moderation-field (cadddr v)))
                  :bad)))))))))

; -----------------------------------------------------------------------------
; The reply

(defun fn-native-control-reasoned-reply-encode (status reason)
  (declare (xargs :guard t))
  (let ((values (list status (fn-nctrl-reason-word reason))))
    (if (not (and (member-equal status *fn-nctrl-statuses*)
                  (fn-frame-values-okp *fn-nctrl-reasoned-reply-spec* values)))
        :bad
      (fn-nctrl-seal *fn-nctrl-reasoned-reply-kind*
                     (fn-frame-fields-octets *fn-nctrl-reasoned-reply-spec*
                                             values)))))

(defun fn-nctrl-reasoned-reply-payload-decode (opened)
  (declare (xargs :guard t))
  (if (not (fn-frame-result-okp opened))
      :bad
    (let ((payload (fn-frame-result-payload opened)))
      (if (not (fn-cbor-octet-listp payload))
          :bad
        (let ((fields (fn-frame-fields-parse *fn-nctrl-reasoned-reply-spec*
                                             payload)))
          (if (not (fn-frame-parse-okp fields))
              :bad
            (let ((values (fn-frame-parse-value fields)))
              (if (and (consp values) (consp (cdr values)))
                  (list (car values) (cadr values))
                :bad))))))))

; What a new client reads after a reasoned request: (STATUS WORD) from a
; reasoned reply, (:legacy STATUS) from an old owner's plain reply (kind 2),
; else :bad.
(defun fn-native-control-reasoned-reply-read (octets)
  (declare (xargs :guard t))
  (let ((reasoned (fn-nctrl-reasoned-reply-payload-decode
                   (fn-nctrl-open octets *fn-nctrl-reasoned-reply-kind*))))
    (if (not (equal reasoned :bad))
        reasoned
      (let ((plain (fn-native-control-reply-decode octets)))
        (if (member-equal plain *fn-nctrl-statuses*)
            (list :legacy plain)
          :bad)))))

; The client's next step for what it read: (:status STATUS WORD) to report,
; (:resend) to send the plain request once (an old owner refused a frame it
; could not decode, before acting on anything), or (:transport) for the
; transport outcome of the stage reached.
(defun fn-native-control-reasoned-client-step (read)
  (declare (xargs :guard t))
  (cond ((and (consp read) (equal (car read) :legacy) (consp (cdr read)))
         (if (equal (cadr read) :refused)
             (list :resend)
           (list :status (cadr read) *fn-nctrl-no-reason-word*)))
        ((and (consp read) (consp (cdr read))
              (member-equal (car read) *fn-nctrl-statuses*))
         (list :status (car read) (cadr read)))
        (t (list :transport))))

; The word the operator's line carries after the status: the reason of a
; refusal, nothing for any other class or for no reason.
(defun fn-native-control-reply-detail (status word)
  (declare (xargs :guard t))
  (if (and (equal (fn-native-control-status-class status) :refused)
           (not (equal word *fn-nctrl-no-reason-word*)))
      word
    nil))

; The reason word of an exchange no reply ended (host/native/control.lisp
; fnn-control-reasoned-exchange): before submission the connect itself
; failed, so no owner answers at the configured control path, and the
; refusal (fn-native-control-transport-outcome) says so: `no-owner'.  After
; submission the outcome is uncertain and names nothing.  Before this an
; operator verb against a stopped node printed `refused ... REFUSED' with no
; reason (lane ops-fixes).
(defun fn-native-control-transport-word (stage)
  (declare (xargs :guard t))
  (if (equal stage :before-submission)
      (fn-nctrl-reason-word :no-owner)
    nil))

(defthm fn-native-control-transport-word-names-the-refusal
  (equal (fn-native-control-reply-detail
          (fn-native-control-transport-outcome stage)
          (fn-native-control-transport-word stage))
         (if (equal stage :before-submission)
             (fn-nctrl-reason-word :no-owner)
           nil)))

; -----------------------------------------------------------------------------
; The exchange, proved

(encapsulate ()
(local
 (defthm fn-nctrl-protected-is-octets
   (implies (and (fn-frame-magicp magic)
                 (fn-cbor-octetp version)
                 (fn-cbor-octetp kind)
                 (fn-cbor-octet-listp payload)
                 (<= (len payload) *fn-cbor-max-uint*))
            (fn-cbor-octet-listp (fn-frame-protected magic version kind payload)))
   :hints (("Goal" :in-theory (e/d (fn-frame-protected fn-frame-header-octets)
                                   (fn-frame-header))))))
(defthm fn-nctrl-open-of-seal
  (implies (and (fn-cbor-octetp kind)
                (fn-cbor-octet-listp payload)
                (<= (len payload) *fn-nctrl-max-payload*))
           (equal (fn-nctrl-open (fn-nctrl-seal kind payload) kind)
                  (fn-frame-ok *fn-nctrl-magic* *fn-nctrl-version* kind payload)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-frame-decode-of-host-framing
                            (magic *fn-nctrl-magic*) (version *fn-nctrl-version*)
                            (max-payload *fn-nctrl-max-payload*))
                 (:instance fn-frame-trailer-is-a-digest
                            (octets (fn-frame-protected *fn-nctrl-magic* *fn-nctrl-version*
                                                        kind payload))))
           :in-theory (e/d (fn-nctrl-open fn-nctrl-seal fn-frame-inputp fn-frame-magicp
                            fn-frame-result-okp fn-frame-ok fn-frame-result-magic
                            fn-frame-result-version fn-frame-result-kind)
                           (fn-frame-decode-of-host-framing fn-frame-decode
                            fn-frame-trailer-is-a-digest
                            fn-frame-protected fn-frame-trailer
                            fn-frame-protected-prefix))))))

(local
 (defthm fn-nctrl-word-chars-octets-first-is-not-upper
   (implies (consp (fn-nctrl-word-chars-octets chars))
            (not (equal (car (fn-nctrl-word-chars-octets chars)) 78)))
   :hints (("Goal" :in-theory (enable fn-nctrl-word-chars-octets)))))

; A decision that named a reason is never rendered as no reason.
(defthm fn-nctrl-reason-word-of-a-reason-is-not-none
  (implies reason
           (not (equal (fn-nctrl-reason-word reason) *fn-nctrl-no-reason-word*)))
  :hints (("Goal" :in-theory (enable fn-nctrl-reason-word)
           :use ((:instance fn-nctrl-word-chars-octets-first-is-not-upper
                            (chars (coerce (symbol-name reason) 'list)))))))

(defthm fn-nctrl-reasoned-reply-values-ok
  (implies (member-equal status *fn-nctrl-statuses*)
           (fn-frame-values-okp *fn-nctrl-reasoned-reply-spec*
                                (list status (fn-nctrl-reason-word reason))))
  :hints (("Goal" :in-theory (e/d (fn-frame-values-okp fn-frame-field-okp
                                   fn-frame-blob-withinp)
                                  (fn-cbor-at-mostp)))))

(defthm fn-nctrl-reasoned-reply-payload-width
  (implies (member-equal status *fn-nctrl-statuses*)
           (<= (len (fn-frame-fields-octets *fn-nctrl-reasoned-reply-spec*
                                            (list status (fn-nctrl-reason-word reason))))
               *fn-nctrl-max-payload*))
  :hints (("Goal" :use ((:instance fn-frame-fields-octets-within-width
                                   (specs *fn-nctrl-reasoned-reply-spec*)
                                   (values (list status (fn-nctrl-reason-word reason))))
                        (:instance fn-nctrl-reasoned-reply-values-ok))
           :in-theory (disable fn-frame-fields-octets-within-width
                               fn-nctrl-reasoned-reply-values-ok
                               fn-frame-fields-octets fn-frame-values-okp)))
  :rule-classes :linear)

; The client reads back the status and the word the owner sealed.
(defthm fn-nctrl-reasoned-read-of-encode
  (implies (member-equal status *fn-nctrl-statuses*)
           (equal (fn-native-control-reasoned-reply-read
                   (fn-native-control-reasoned-reply-encode status reason))
                  (list status (fn-nctrl-reason-word reason))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-nctrl-open-of-seal
                            (kind *fn-nctrl-reasoned-reply-kind*)
                            (payload (fn-frame-fields-octets
                                      *fn-nctrl-reasoned-reply-spec*
                                      (list status (fn-nctrl-reason-word reason)))))
                 (:instance fn-frame-fields-parse-of-octets
                            (specs *fn-nctrl-reasoned-reply-spec*)
                            (values (list status (fn-nctrl-reason-word reason))))
                 (:instance fn-frame-fields-octets-are-octets
                            (specs *fn-nctrl-reasoned-reply-spec*)
                            (values (list status (fn-nctrl-reason-word reason))))
                 (:instance fn-nctrl-reasoned-reply-values-ok)
                 (:instance fn-nctrl-reasoned-reply-payload-width))
           :in-theory (e/d (fn-native-control-reasoned-reply-read
                            fn-native-control-reasoned-reply-encode
                            fn-nctrl-reasoned-reply-payload-decode
                            fn-frame-result-okp fn-frame-ok fn-frame-result-payload
                            fn-frame-parse-okp fn-frame-parse-ok fn-frame-parse-value)
                           (fn-nctrl-open-of-seal fn-frame-fields-parse-of-octets
                            fn-frame-fields-octets-are-octets
                            fn-nctrl-reasoned-reply-values-ok
                            fn-nctrl-reasoned-reply-payload-width
                            member-equal (:e member-equal)
                            fn-nctrl-open fn-nctrl-seal (:e fn-nctrl-seal)
                            (:e fn-nctrl-open) (:e fn-frame-fields-octets)
                            fn-frame-fields-parse
                            fn-frame-fields-octets fn-frame-values-okp
                            fn-native-control-reply-decode)))))

;; KEYSTONE (PKT-867, D27: no argv word count or word length bound).  An
;; administrative argv the client can seal -- any number of ASCII words, each
;; of any length up to the record codec's byte-string width -- is the argv
;; the owner decodes.  Subjects: the client seals with
;; fn-native-control-host-admin-encode / -reasoned-admin-encode and the owner
;; opens with fn-native-control-host-admin-decode / -reasoned-admin-decode
;; (host/native-control-host.lisp, called by host/native/control.lisp
;; fnn-control-admin and the owner's request read).  What bounds one
;; command is the frame, read under the profile's bound; nothing counts words.
;; Teeth: tests/acl2/native-control-tests.lisp (200 words; a 70,000-octet
;; word, past the narrow codec's 65,535; an unsealable argv is :bad).
(defthm fn-native-control-admin-decode-of-encode
  (implies (not (equal (fn-native-control-admin-encode argv) :bad))
           (equal (fn-native-control-admin-decode (fn-native-control-admin-encode argv))
                  (list :admin argv)))
  :hints (("Goal" :do-not-induct t
                  :cases ((and (fn-cbor-octet-listp (fn-nctrl-admin-argv-encode argv))
                               (<= (len (fn-nctrl-admin-argv-encode argv))
                                   *fn-nctrl-max-payload*))))
          ("Subgoal 2" :in-theory (e/d (fn-native-control-admin-encode fn-nctrl-seal)
                                       (fn-nctrl-admin-argv-encode))
                       :expand ((fn-native-control-admin-encode argv)))
          ("Subgoal 1"
           :use ((:instance fn-nctrl-open-of-seal
                            (kind *fn-nctrl-admin-kind*)
                            (payload (fn-nctrl-admin-argv-encode argv)))
                 (:instance fn-nctrl-admin-argv-decode-of-encode))
           :in-theory (e/d (fn-native-control-admin-encode fn-native-control-admin-decode
                            fn-nctrl-admin-payload-decode
                            fn-frame-result-okp fn-frame-ok fn-frame-result-payload
                            fn-record-parse-okp fn-record-parse-value fn-record-parse-ok)
                           (fn-nctrl-open-of-seal fn-nctrl-admin-argv-decode-of-encode
                            fn-nctrl-admin-argv-encode fn-nctrl-admin-argv-decode
                            fn-nctrl-open fn-nctrl-seal (:e fn-nctrl-seal)
                            fn-native-admin-argvp fn-nctrl-admin-words-widthp)))))

(defthm fn-native-control-reasoned-admin-decode-of-encode
  (implies (not (equal (fn-native-control-reasoned-admin-encode argv) :bad))
           (equal (fn-native-control-reasoned-admin-decode (fn-native-control-reasoned-admin-encode argv))
                  (list :admin argv)))
  :hints (("Goal" :do-not-induct t
                  :cases ((and (fn-cbor-octet-listp (fn-nctrl-admin-argv-encode argv))
                               (<= (len (fn-nctrl-admin-argv-encode argv))
                                   *fn-nctrl-max-payload*))))
          ("Subgoal 2" :in-theory (e/d (fn-native-control-reasoned-admin-encode fn-nctrl-seal)
                                       (fn-nctrl-admin-argv-encode))
                       :expand ((fn-native-control-reasoned-admin-encode argv)))
          ("Subgoal 1"
           :use ((:instance fn-nctrl-open-of-seal
                            (kind *fn-nctrl-reasoned-admin-kind*)
                            (payload (fn-nctrl-admin-argv-encode argv)))
                 (:instance fn-nctrl-admin-argv-decode-of-encode))
           :in-theory (e/d (fn-native-control-reasoned-admin-encode fn-native-control-reasoned-admin-decode
                            fn-nctrl-admin-payload-decode
                            fn-frame-result-okp fn-frame-ok fn-frame-result-payload
                            fn-record-parse-okp fn-record-parse-value fn-record-parse-ok)
                           (fn-nctrl-open-of-seal fn-nctrl-admin-argv-decode-of-encode
                            fn-nctrl-admin-argv-encode fn-nctrl-admin-argv-decode
                            fn-nctrl-open fn-nctrl-seal (:e fn-nctrl-seal)
                            fn-native-admin-argvp fn-nctrl-admin-words-widthp)))))

(defthm fn-nctrl-legacy-is-no-status
  (implies (member-equal s *fn-nctrl-statuses*) (not (equal s :legacy)))
  :rule-classes nil)

; KEYSTONE (PKT-453 (a): the printed word is the decision's reason).  The
; owner seals the refusal it decided with the reason its decision named
; (host/native/control.lisp fnn-control-reply-octets through
; `fn-native-control-host-reasoned-reply-encode'); the client reads that
; frame (`fn-native-control-reasoned-reply-read'), steps
; (`fn-native-control-reasoned-client-step', host/native/control.lisp
; fnn-control-reasoned-exchange) and prints the detail
; (`fn-native-control-reply-detail', host/native/operator.lisp
; fnn-operator-execute-post and fnn-operator-execute-admin).  For every
; status the client reports the owner's status and word, and for a refusal
; that named a reason the printed word is exactly
; `fn-nctrl-reason-word' of that reason: no host string stands between.
(defthm fn-native-control-printed-reason-is-the-decisions
  (implies (member-equal status *fn-nctrl-statuses*)
           (let ((step (fn-native-control-reasoned-client-step
                        (fn-native-control-reasoned-reply-read
                         (fn-native-control-reasoned-reply-encode status reason)))))
             (and (equal step (list :status status (fn-nctrl-reason-word reason)))
                  (implies (and (equal (fn-native-control-status-class status)
                                       :refused)
                                reason)
                           (equal (fn-native-control-reply-detail
                                   (cadr step) (caddr step))
                                  (fn-nctrl-reason-word reason))))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-nctrl-reasoned-read-of-encode)
                 (:instance fn-nctrl-reason-word-of-a-reason-is-not-none)
                 (:instance fn-nctrl-legacy-is-no-status (s status)))
           :in-theory (e/d (fn-native-control-reasoned-client-step
                            fn-native-control-reply-detail)
                           (fn-nctrl-reasoned-read-of-encode
                            fn-nctrl-reason-word-of-a-reason-is-not-none
                            fn-native-control-reasoned-reply-read
                            fn-native-control-reasoned-reply-encode
                            fn-native-control-status-class
                            member-equal (:e member-equal))))))

(in-theory (disable fn-native-control-reasoned-reply-encode
                    fn-native-control-reasoned-reply-read
                    fn-nctrl-reasoned-reply-payload-decode
                    fn-native-control-reasoned-client-step
                    fn-native-control-reply-detail))

; -----------------------------------------------------------------------------
; PKT-472 (e): the refusals the host observes as a condition class.  A store,
; OS or socket error inside a control request's handling (host/native/
; control.lisp fnn-control-handle-client) is a refusal the host classifies,
; with no ACL2 decision behind it; ACL2 names the class as its reason, so a
; reasoned frame's reply says which refusal it was instead of NONE.

(defconst *fn-nctrl-host-refusal-classes* '(:store-error :os-error :socket-error))

(defun fn-native-control-host-refusal-reason (class)
  (declare (xargs :guard t))
  (if (member-equal class *fn-nctrl-host-refusal-classes*) class nil))

(defthm fn-native-control-host-refusal-reason-of-a-class
  (implies (member-equal class *fn-nctrl-host-refusal-classes*)
           (equal (fn-native-control-host-refusal-reason class) class)))

; KEYSTONE (PKT-472 (e)).  Over the reply the host writes for such a refusal
; (fn-native-control-reasoned-reply-encode :refused REASON) and the client's
; read of it: the printed detail is the class's own word, never NONE; a
; class outside the three names no reason.
(defthm fn-native-control-host-refusal-names-its-class
  (let* ((reason (fn-native-control-host-refusal-reason class))
         (step (fn-native-control-reasoned-client-step
                (fn-native-control-reasoned-reply-read
                 (fn-native-control-reasoned-reply-encode :refused reason)))))
    (implies (member-equal class *fn-nctrl-host-refusal-classes*)
             (and (equal reason class)
                  (equal (fn-native-control-reply-detail (cadr step) (caddr step))
                         (fn-nctrl-reason-word class))
                  (not (equal (fn-nctrl-reason-word class)
                              *fn-nctrl-no-reason-word*)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-native-control-host-refusal-reason-of-a-class)
                 (:instance fn-native-control-printed-reason-is-the-decisions
                            (status :refused) (reason class))
                 (:instance fn-nctrl-reason-word-of-a-reason-is-not-none
                            (reason class)))
           :in-theory (disable fn-native-control-printed-reason-is-the-decisions
                               fn-nctrl-reason-word-of-a-reason-is-not-none
                               fn-native-control-host-refusal-reason-of-a-class
                               fn-native-control-host-refusal-reason
                               fn-nctrl-reason-word
                               member-equal))))

(defthm fn-native-control-host-refusal-reason-outside-is-none
  (implies (not (member-equal class *fn-nctrl-host-refusal-classes*))
           (equal (fn-native-control-host-refusal-reason class) nil)))
