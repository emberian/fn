; fn -- the reasoned reply with a line (row S1, lane limits-live-4).
;
; The reasoned reply (books/native-control-reason.lisp, FNCT kind 18) carries
; a status and a reason WORD: fn-nctrl-reason-word renders a symbol's name,
; folded, printable and without spaces.  A decision that owes the operator a
; sentence (a live limit change: what was applied, what the next start
; reserves) was squeezed into one colon-joined word.  The frame's field is a
; blob; the one-word rule is the renderer's, not the protocol's.  This book
; adds reply kind 23: the status, the reason word, and a LINE ACL2 decided
; (printable ASCII, spaces allowed), which the client prints after the
; status.  A reply with no line is kind 18, unchanged.

(in-package "ACL2")
(include-book "native-control-reason")

(defconst *fn-ncline-reply-kind* 23)
(defconst *fn-ncline-max-line-octets* 1024)
(defconst *fn-ncline-reply-spec*
  (list (cons :enum *fn-nctrl-statuses*)
        (cons :blob *fn-nctrl-max-reason-octets*)
        (cons :blob *fn-ncline-max-line-octets*)))

; A line's characters as octets: printable ASCII, the space included, else :bad.
(defun fn-ncline-chars-octets (chars)
  (declare (xargs :guard t))
  (if (consp chars)
      (let ((rest (fn-ncline-chars-octets (cdr chars))))
        (if (and (characterp (car chars)) (not (equal rest :bad)))
            (let ((n (char-code (car chars))))
              (if (and (<= 32 n) (<= n 126)) (cons n rest) :bad))
          :bad))
    nil))

(defthm fn-ncline-chars-octets-are-octets
  (implies (not (equal (fn-ncline-chars-octets chars) :bad))
           (fn-cbor-octet-listp (fn-ncline-chars-octets chars)))
  :hints (("Goal" :in-theory (enable fn-ncline-chars-octets fn-cbor-octet-listp
                                     fn-cbor-octetp))))

; The line a reply carries: LINE's octets when it is a non-empty printable
; string within the bound, else nil (no line: the reply is kind 18).
(defun fn-ncline-line (line)
  (declare (xargs :guard t))
  (let ((octets (and (stringp line)
                     (fn-ncline-chars-octets (coerce line 'list)))))
    (if (and (consp octets)
             (fn-cbor-octet-listp octets)
             (<= (len octets) *fn-ncline-max-line-octets*))
        octets
      nil)))

(defthm fn-ncline-line-is-a-field
  (let ((l (fn-ncline-line line)))
    (implies l
             (and (consp l)
                  (fn-cbor-octet-listp l)
                  (<= (len l) *fn-ncline-max-line-octets*)
                  (fn-cbor-at-mostp l *fn-ncline-max-line-octets*))))
  :hints (("Goal" :in-theory (enable fn-ncline-line)
           :use ((:instance fn-cbor-at-mostp-from-length
                            (xs (fn-ncline-line line))
                            (bound *fn-ncline-max-line-octets*))))))

(in-theory (disable fn-ncline-line))

(defun fn-native-control-lined-reply-encode (status reason line)
  (declare (xargs :guard t))
  (let ((octets (fn-ncline-line line)))
    (if (not octets)
        (fn-native-control-reasoned-reply-encode status reason)
      (let ((values (list status (fn-nctrl-reason-word reason) octets)))
        (if (not (and (member-equal status *fn-nctrl-statuses*)
                      (fn-frame-values-okp *fn-ncline-reply-spec* values)))
            :bad
          (fn-nctrl-seal *fn-ncline-reply-kind*
                         (fn-frame-fields-octets *fn-ncline-reply-spec* values)))))))

(defun fn-ncline-reply-payload-decode (opened)
  (declare (xargs :guard t))
  (if (not (fn-frame-result-okp opened))
      :bad
    (let ((payload (fn-frame-result-payload opened)))
      (if (not (fn-cbor-octet-listp payload))
          :bad
        (let ((fields (fn-frame-fields-parse *fn-ncline-reply-spec* payload)))
          (if (not (fn-frame-parse-okp fields))
              :bad
            (let ((values (fn-frame-parse-value fields)))
              (if (and (consp values) (consp (cdr values)) (consp (cddr values)))
                  (list (car values) (cadr values) (caddr values))
                :bad))))))))

; What a new client reads: (STATUS WORD LINE) from a lined reply, else what
; fn-native-control-reasoned-reply-read reads.
(defun fn-native-control-lined-reply-read (octets)
  (declare (xargs :guard t))
  (let ((lined (fn-ncline-reply-payload-decode
                (fn-nctrl-open octets *fn-ncline-reply-kind*))))
    (if (not (equal lined :bad))
        lined
      (fn-native-control-reasoned-reply-read octets))))

; The client's step: (:status STATUS WORD LINE) for a lined reply, else
; fn-native-control-reasoned-client-step's.
(defun fn-native-control-lined-client-step (read)
  (declare (xargs :guard t))
  (let ((step (fn-native-control-reasoned-client-step read)))
    (if (and (consp step) (equal (car step) :status)
             (consp read) (consp (cdr read)) (consp (cddr read))
             (member-equal (car read) *fn-nctrl-statuses*))
        (list :status (car read) (cadr read) (caddr read))
      step)))

; What the operator's line carries after the status: the owner's line when
; it sent one, else the refusal's word (fn-native-control-reply-detail).
(defun fn-native-control-lined-detail (step)
  (declare (xargs :guard t))
  (if (and (consp step) (equal (car step) :status)
           (consp (cdr step)) (consp (cddr step)) (consp (cdddr step)))
      (cadddr step)
    (and (consp step) (equal (car step) :status) (consp (cdr step)) (consp (cddr step))
         (fn-native-control-reply-detail (cadr step) (caddr step)))))

; -----------------------------------------------------------------------------
; The round trip

(defthm fn-ncline-reply-values-ok
  (implies (and (member-equal status *fn-nctrl-statuses*)
                (fn-ncline-line line))
           (fn-frame-values-okp *fn-ncline-reply-spec*
                                (list status (fn-nctrl-reason-word reason)
                                      (fn-ncline-line line))))
  :hints (("Goal" :use ((:instance fn-ncline-line-is-a-field))
           :in-theory (e/d (fn-frame-values-okp fn-frame-field-okp
                                                fn-frame-blob-withinp)
                           (fn-cbor-at-mostp fn-ncline-line-is-a-field)))))

(defthm fn-ncline-reply-payload-width
  (implies (and (member-equal status *fn-nctrl-statuses*)
                (fn-ncline-line line))
           (<= (len (fn-frame-fields-octets *fn-ncline-reply-spec*
                                            (list status (fn-nctrl-reason-word reason)
                                                  (fn-ncline-line line))))
               *fn-nctrl-max-payload*))
  :hints (("Goal" :use ((:instance fn-frame-fields-octets-within-width
                                   (specs *fn-ncline-reply-spec*)
                                   (values (list status (fn-nctrl-reason-word reason)
                                                 (fn-ncline-line line))))
                        (:instance fn-ncline-reply-values-ok))
           :in-theory (disable fn-frame-fields-octets-within-width
                               fn-ncline-reply-values-ok
                               fn-frame-fields-octets fn-frame-values-okp)))
  :rule-classes :linear)

; The client reads back the status, the word and the line the owner sealed.
(defthm fn-ncline-read-of-encode
  (implies (and (member-equal status *fn-nctrl-statuses*)
                (fn-ncline-line line))
           (equal (fn-native-control-lined-reply-read
                   (fn-native-control-lined-reply-encode status reason line))
                  (list status (fn-nctrl-reason-word reason) (fn-ncline-line line))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-nctrl-open-of-seal
                            (kind *fn-ncline-reply-kind*)
                            (payload (fn-frame-fields-octets
                                      *fn-ncline-reply-spec*
                                      (list status (fn-nctrl-reason-word reason)
                                            (fn-ncline-line line)))))
                 (:instance fn-frame-fields-parse-of-octets
                            (specs *fn-ncline-reply-spec*)
                            (values (list status (fn-nctrl-reason-word reason)
                                          (fn-ncline-line line))))
                 (:instance fn-frame-fields-octets-are-octets
                            (specs *fn-ncline-reply-spec*)
                            (values (list status (fn-nctrl-reason-word reason)
                                          (fn-ncline-line line))))
                 (:instance fn-ncline-reply-values-ok)
                 (:instance fn-ncline-reply-payload-width))
           :in-theory (e/d (fn-native-control-lined-reply-read
                            fn-native-control-lined-reply-encode
                            fn-ncline-reply-payload-decode
                            fn-frame-result-okp fn-frame-ok fn-frame-result-payload
                            fn-frame-parse-okp fn-frame-parse-ok fn-frame-parse-value)
                           (fn-nctrl-open-of-seal fn-frame-fields-parse-of-octets
                            fn-frame-fields-octets-are-octets
                            fn-ncline-reply-values-ok
                            fn-ncline-reply-payload-width
                            member-equal (:e member-equal)
                            fn-nctrl-open fn-nctrl-seal (:e fn-nctrl-seal)
                            (:e fn-nctrl-open) (:e fn-frame-fields-octets)
                            fn-frame-fields-parse)))))

; KEYSTONE (row S1: the operator reads ACL2's sentence).  The owner seals the
; line its decision rendered (host/native/control.lisp fnn-control-reply-octets
; through fn-native-control-host-lined-reply-encode); the client reads it
; (fn-native-control-lined-reply-read), steps
; (fn-native-control-lined-client-step) and prints the detail
; (fn-native-control-lined-detail, host/native/operator-live.lisp
; fnn-operator-live-admin): for every status, the printed text is exactly
; the line's octets -- no host string stands between.
(defthm fn-native-control-printed-line-is-the-decisions
  (implies (and (member-equal status *fn-nctrl-statuses*)
                (fn-ncline-line line))
           (let ((step (fn-native-control-lined-client-step
                        (fn-native-control-lined-reply-read
                         (fn-native-control-lined-reply-encode status reason line)))))
             (and (equal step (list :status status (fn-nctrl-reason-word reason)
                                    (fn-ncline-line line)))
                  (equal (fn-native-control-lined-detail step)
                         (fn-ncline-line line)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-ncline-read-of-encode)
                 (:instance fn-nctrl-legacy-is-no-status (s status)))
           :in-theory (e/d (fn-native-control-lined-client-step
                            fn-native-control-reasoned-client-step
                            fn-native-control-lined-detail)
                           (fn-ncline-read-of-encode
                            fn-native-control-lined-reply-read
                            fn-native-control-lined-reply-encode
                            member-equal (:e member-equal))))))

;; A reply with no line is the reasoned reply, read as before: a kind-18
;; frame never opens as kind 23.
(defthm fn-ncline-open-names-one-kind
  (implies (and (fn-frame-result-okp (fn-nctrl-open x k))
                (not (equal j k)))
           (not (fn-frame-result-okp (fn-nctrl-open x j))))
  :hints (("Goal" :in-theory (e/d (fn-nctrl-open) (fn-frame-decode))))
  :rule-classes nil)

(defthm fn-ncline-no-line-in-a-reasoned-reply
  (equal (fn-ncline-reply-payload-decode
          (fn-nctrl-open (fn-native-control-reasoned-reply-encode status reason)
                         *fn-ncline-reply-kind*))
         :bad)
  :hints (("Goal" :do-not-induct t
           :cases ((member-equal status *fn-nctrl-statuses*))
           :use ((:instance fn-nctrl-open-of-seal
                            (kind *fn-nctrl-reasoned-reply-kind*)
                            (payload (fn-frame-fields-octets
                                      *fn-nctrl-reasoned-reply-spec*
                                      (list status (fn-nctrl-reason-word reason)))))
                 (:instance fn-frame-fields-octets-are-octets
                            (specs *fn-nctrl-reasoned-reply-spec*)
                            (values (list status (fn-nctrl-reason-word reason))))
                 (:instance fn-nctrl-reasoned-reply-values-ok)
                 (:instance fn-nctrl-reasoned-reply-payload-width)
                 (:instance fn-ncline-open-names-one-kind
                            (x (fn-native-control-reasoned-reply-encode status reason))
                            (k *fn-nctrl-reasoned-reply-kind*) (j *fn-ncline-reply-kind*)))
           :in-theory (e/d (fn-native-control-reasoned-reply-encode fn-frame-result-okp
                                                                    fn-frame-ok)
                           (fn-nctrl-open-of-seal fn-frame-fields-octets-are-octets
                            fn-nctrl-reasoned-reply-values-ok
                            fn-nctrl-reasoned-reply-payload-width
                            member-equal (:e member-equal) fn-nctrl-seal (:e fn-nctrl-seal)
                            (:e fn-frame-fields-octets))))
          ("Subgoal 1" :in-theory (enable fn-nctrl-open
                                          fn-native-control-reasoned-reply-encode))))

(defthm fn-ncline-read-of-a-lineless-encode
  (implies (not (fn-ncline-line line))
           (equal (fn-native-control-lined-reply-read
                   (fn-native-control-lined-reply-encode status reason line))
                  (fn-native-control-reasoned-reply-read
                   (fn-native-control-reasoned-reply-encode status reason))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-native-control-lined-reply-read
                            fn-native-control-lined-reply-encode)
                           (fn-nctrl-open fn-native-control-reasoned-reply-read
                            fn-native-control-reasoned-reply-encode)))))

(in-theory (disable fn-native-control-lined-reply-encode
                    fn-native-control-lined-reply-read
                    fn-ncline-reply-payload-decode
                    fn-native-control-lined-client-step
                    fn-native-control-lined-detail))
