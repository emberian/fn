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
(include-book "native-admin")

(defconst *fn-nctrl-magic* '(70 78 67 84)) ; FNCT
(defconst *fn-nctrl-version* 1)
(defconst *fn-nctrl-request-kind* 1)
(defconst *fn-nctrl-reply-kind* 2)
(defconst *fn-nctrl-admin-kind* 3)
(defconst *fn-nctrl-request-spec* '(:blob :text :blob))
(defconst *fn-nctrl-statuses*
  '(:accepted :duplicate :refused :busy :uncertain :fault))
(defconst *fn-nctrl-reply-spec* (list (cons :enum *fn-nctrl-statuses*)))

; Article plus its blob head, Message-ID plus its text head, and the CBOR group
; count/list.  The final slack is deliberately pessimistic and remains below
; the generic frame ceiling.
(defconst *fn-nctrl-max-groups-octets*
  (+ 5 (* 131 *fn-record-max-groups*)))
(defconst *fn-nctrl-max-payload*
  (+ 4 *fn-article-max-octets*
     2 *fn-frame-max-text*
     4 *fn-nctrl-max-groups-octets*))
(defconst *fn-nctrl-max-frame*
  (+ *fn-frame-overhead-octets* *fn-nctrl-max-payload*))
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
  (declare (xargs :guard t))
  (if (or (not (fn-native-admin-argvp argv)) (not (consp argv)))
      :bad
    (let ((payload (fn-nctrl-groups-encode argv)))
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
      (let ((parsed (fn-nctrl-groups-decode (fn-frame-result-payload opened))))
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
        ((member-equal status '(:refused :busy)) :refused)
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
                    (:d fn-nctrl-seal)
                    (:d fn-nctrl-open)
                    (:d fn-native-control-lease-path)
                    (:d fn-native-control-request-encode)
                    (:d fn-native-control-request-decode)
                    (:d fn-native-control-reply-encode)
                    (:d fn-native-control-reply-decode)))
