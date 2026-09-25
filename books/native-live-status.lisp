; fn: the operator's status report, one renderer for the offline store and
; the running owner, and the local-control exchange that carries it.
;
; `operator CONFIG status' (and `pins', `obligations', `peer list') used to
; open the Store, so while an owner held it the answer was `store is already
; locked' (planning/evidence/spike-operator-2026-09-25.md).  The report is
; now one ACL2 function of the Store state, the carried profile, the
; configuration, the open connections' configuration pins and the host's
; open-time observations (`fn-nls-report').  The offline command applies it
; to the state it just replayed (`fn-nls-offline-report'); the running owner
; applies it to the state it carries (`fn-nls-live-report') and sends it
; over the control socket in pages (`fn-nls-reply'), which the client joins
; (`fn-nls-client-step').  The two keystones:
;
;   fn-nls-live-report-is-the-offline-report   the owner's words are the
;       offline words of the same state (carried octet sum valid, no open
;       connection);
;   fn-nls-client-step-of-owner-reply          every page the owner answers
;       extends the client's prefix of the one report, to the whole report.
;
; Answering changes no state: the owner's entry (host/native-live-status-
; host.lisp `fn-native-live-status-host-reply') takes `state' and returns a
; single value, so ACL2 admits no update of it, and unlike
; `fn-owner-headroom' it extends the carried octet sum without storing it.
;
; Representation (D27): the report and both frames are octet lists, like the
; rest of the FNCT control codec; the concrete twin is open.
;
; This book owns the prefix `fn-nls-' (docs/prefixes.md).

(in-package "ACL2")
(include-book "native-control")
(include-book "native-admin")
(include-book "store-budget")
(include-book "owner-config")

; -----------------------------------------------------------------------------
; Words

(defun fn-nls-text (text)
  (declare (xargs :guard t))
  (fn-record-string-octets text))

(defun fn-nls-nat (n)
  (declare (xargs :guard t))
  (fn-nntp-decimal-field (nfix n)))

(defconst *fn-nls-lf* '(10))

(defun fn-nls-field (name n)
  "` NAME=N'."
  (declare (xargs :guard t))
  (append (fn-nls-text " ") (fn-nls-text name) (fn-nls-text "=") (fn-nls-nat n)))

(defun fn-nls-profile-words (report)
  "The `fn-bs-profile-report' pairs as ` NAME=VALUE' words, in its order."
  (declare (xargs :guard t))
  (if (consp report)
      (append (if (consp (car report))
                  (fn-nls-field (car (car report)) (cdr (car report)))
                nil)
              (fn-nls-profile-words (cdr report)))
    nil))

(defun fn-nls-names (names)
  (declare (xargs :guard t))
  (if (consp names)
      (append (fn-nls-text (car names))
              (if (consp (cdr names)) (fn-nls-text " ") nil)
              (fn-nls-names (cdr names)))
    nil))

; OBS is the host's observation at its own open, carried unchanged:
;   (ORPHANS MOREP MODE), ORPHANS the staging names the sweep found, MOREP
;   whether it stopped at its bound, MODE (:checkpoint G S) or
;   (:full-replay REASON).
(defun fn-nls-obs-orphans (obs) (declare (xargs :guard t)) (fn-ag-car obs))
(defun fn-nls-obs-morep (obs) (declare (xargs :guard t)) (fn-ag-car (fn-ag-cdr obs)))
(defun fn-nls-obs-mode (obs)
  (declare (xargs :guard t))
  (fn-ag-car (fn-ag-cdr (fn-ag-cdr obs))))

(defun fn-nls-orphan-words (obs)
  "`staging-orphans=N[+] [NAME ...]', or `staging-orphans=0'."
  (declare (xargs :guard t))
  (let ((names (fn-nls-obs-orphans obs)))
    (if (consp names)
        (append (fn-nls-text "staging-orphans=") (fn-nls-nat (len names))
                (if (fn-nls-obs-morep obs) (fn-nls-text "+") nil)
                (fn-nls-text " [") (fn-nls-names names) (fn-nls-text "]"))
      (fn-nls-text "staging-orphans=0"))))

(defun fn-nls-reason-words (reason)
  (declare (xargs :guard t))
  (if (and (symbolp reason)
           (standard-char-listp (coerce (symbol-name reason) 'list)))
      (fn-nls-text (string-downcase (symbol-name reason)))
    (fn-nls-text "unknown")))

(defun fn-nls-open-words (obs)
  "`open=checkpoint:G suffix=S' or `open=full-replay reason=R'."
  (declare (xargs :guard t))
  (let ((mode (fn-nls-obs-mode obs)))
    (if (equal (fn-ag-car mode) :checkpoint)
        (append (fn-nls-text "open=checkpoint:")
                (fn-nls-nat (fn-ag-car (fn-ag-cdr mode)))
                (fn-nls-field "suffix" (fn-ag-car (fn-ag-cdr (fn-ag-cdr mode)))))
      (append (fn-nls-text "open=full-replay reason=")
              (fn-nls-reason-words (fn-ag-car (fn-ag-cdr mode)))))))

; -----------------------------------------------------------------------------
; The report

(defun fn-nls-headroom-words (headroom)
  (declare (xargs :guard t))
  (append (fn-nls-text "headroom")
          (fn-nls-field "transactions-used" (fn-ag-car headroom))
          (fn-nls-field "transactions-budget" (fn-ag-car (fn-ag-cdr headroom)))
          (fn-nls-field "bytes-used" (fn-ag-car (fn-ag-cdr (fn-ag-cdr headroom))))
          (fn-nls-field "history-bound"
                        (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr headroom)))))
          (fn-nls-field "charge-reserved"
                        (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr headroom))))))
          (fn-nls-field "charge-capacity"
                        (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr
                                                                   (fn-ag-cdr headroom)))))))))

(defun fn-nls-connection-lines (pins)
  "One `connection id=I config-generation=G' line per open connection's pin
(books/owner-config.lisp: the generation it opened at, or advanced to)."
  (declare (xargs :guard t :verify-guards nil))
  (if (consp pins)
      (append (if (consp (car pins))
                  (append (fn-nls-text "connection")
                          (fn-nls-field "id" (car (car pins)))
                          (fn-nls-field "config-generation"
                                        (fn-cfg-generation (cdr (car pins))))
                          *fn-nls-lf*)
                nil)
              (fn-nls-connection-lines (cdr pins)))
    nil))

(defun fn-nls-kind-words (kind)
  (declare (xargs :guard t))
  (if (equal kind :forward) (fn-nls-text "forward") (fn-nls-text "archive")))

(defun fn-nls-obligation-lines (pins)
  "One line per held retention obligation, in the ledger's order."
  (declare (xargs :guard t :verify-guards nil))
  (if (consp pins)
      (let ((o (car pins)))
        (append (fn-nls-text "obligation id=")
                (fn-nls-text (fn-retain-obligation-id o))
                (fn-nls-text " kind=")
                (fn-nls-kind-words (fn-retain-obligation-kind o))
                (fn-nls-field "charge" (fn-retain-obligation-charge o))
                (fn-nls-text " subject=")
                (fn-nls-text (fn-retain-obligation-subject o))
                *fn-nls-lf*
                (fn-nls-obligation-lines (cdr pins))))
    nil))

(defun fn-nls-retention (s)
  (declare (xargs :guard t :verify-guards nil))
  (fn-node-retention (fn-sn-node s)))

(defun fn-nls-pins-line (s pins)
  (declare (xargs :guard t :verify-guards nil))
  (append (fn-nls-text "pins=")
          (fn-nls-nat (len (fn-retain-pins (fn-nls-retention s))))
          (fn-nls-field "reserved" (fn-retain-reserved (fn-nls-retention s)))
          (fn-nls-field "connections" (len pins))
          *fn-nls-lf*
          (fn-nls-connection-lines pins)))

(defconst *fn-nls-kinds* '(:status :pins :peers :obligations))

(defun fn-nls-report (kind profile s bytes cfg pins obs)
  "The octets `operator CONFIG KIND' prints.

S is the Store state, PROFILE its persisted profile, BYTES its committed
record octets, CFG the configuration, PINS the open connections'
configuration pins (nil with no owner), OBS the host's open observation."
  (declare (xargs :guard t :verify-guards nil))
  (cond
   ((equal kind :peers)
    (fn-native-admin-peer-report (fn-cfg-peers (fn-cfg-value cfg))))
   ((equal kind :pins) (fn-nls-pins-line s pins))
   ((equal kind :obligations)
    (append (fn-nls-text "obligations=")
            (fn-nls-nat (len (fn-retain-pins (fn-nls-retention s))))
            (fn-nls-field "reserved" (fn-retain-reserved (fn-nls-retention s)))
            *fn-nls-lf*
            (fn-nls-obligation-lines (fn-retain-pins (fn-nls-retention s)))))
   (t
    (append (fn-nls-text "transactions=") (fn-nls-nat (fn-sbud-used s))
            (fn-nls-field "articles"
                          (len (fn-state-articles (fn-node-acceptance (fn-sn-node s)))))
            (fn-nls-text " ") (fn-nls-orphan-words obs)
            (fn-nls-text " unsigned-legacy-experiment") *fn-nls-lf*
            (fn-nls-text "profile")
            (fn-nls-profile-words (fn-bs-profile-report profile)) *fn-nls-lf*
            (fn-nls-headroom-words (fn-sbud-headroom-at profile s bytes)) *fn-nls-lf*
            (fn-nls-open-words obs) *fn-nls-lf*
            (fn-nls-pins-line s pins)))))

(defun fn-nls-offline-report (kind profile s cfg obs)
  "What the offline command prints over the state it replayed: every
committed record re-encoded once, and no connection."
  (declare (xargs :guard t :verify-guards nil))
  (fn-nls-report kind profile s (fn-sbud-bytes-used s) cfg nil obs))

(defun fn-nls-live-report (kind profile oc cache obs)
  "What the running owner answers over the configured owner OC it carries:
its Store, its configuration and its connections' pins, with the committed
record octets extended from the carried (K . SUM) CACHE, not stored."
  (declare (xargs :guard t :verify-guards nil))
  (let ((s (fn-own-store (fn-ocfg-owner oc))))
    (fn-nls-report kind profile s
                   (fn-sbud-bytes-extend cache (fn-sf-records (fn-sn-files s)))
                   (fn-ocfg-config oc) (fn-ocfg-pins oc) obs)))

; KEYSTONE (the live words are the offline words).  The subject is
; `fn-nls-live-report', which the owner's control handler reaches through
; host/native-live-status-host.lisp `fn-native-live-status-host-reply'
; (host/native/control.lisp `fnn-control-handle-client'), and
; `fn-nls-offline-report', which `fn-native-live-status-host-offline' calls
; (host/native/io.lisp `fnn-command-live-report').  With the carried octet
; sum valid for the carried records and no connection open, the owner's
; report of every KIND is the offline report of the same Store and
; configuration.  An open connection adds its line; a stale sum changes
; bytes-used (tests/acl2/native-live-status-tests.lisp).
(local
 (defthm fn-nls-report-without-connections
   (implies (not (consp pins))
            (equal (fn-nls-report kind profile s bytes cfg pins obs)
                   (fn-nls-report kind profile s bytes cfg nil obs)))
   :hints (("Goal" :expand ((fn-nls-connection-lines pins)
                            (fn-nls-connection-lines nil))
            :in-theory '(fn-nls-report fn-nls-pins-line len)))))

(defthm fn-nls-live-report-is-the-offline-report
  (implies (and (fn-sbud-octets-cache-validp
                 cache (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc)))))
                (not (consp (fn-ocfg-pins oc))))
           (equal (fn-nls-live-report kind profile oc cache obs)
                  (fn-nls-offline-report kind profile
                                         (fn-own-store (fn-ocfg-owner oc))
                                         (fn-ocfg-config oc) obs)))
  :hints (("Goal"
           :use ((:instance fn-sbud-bytes-used-is-kernel-sum
                            (s (fn-own-store (fn-ocfg-owner oc))))
                 (:instance fn-nls-report-without-connections
                            (s (fn-own-store (fn-ocfg-owner oc)))
                            (bytes (fn-sbud-bytes-used (fn-own-store (fn-ocfg-owner oc))))
                            (cfg (fn-ocfg-config oc))
                            (pins (fn-ocfg-pins oc))))
           :in-theory '(fn-nls-live-report fn-nls-offline-report))))

; -----------------------------------------------------------------------------
; The exchange: FNLS frames on the owner's control socket
;
; Request: uint KIND-CODE, uint OFFSET.  Reply: uint STATUS-CODE, uint TOTAL
; (the report's length), bytes DIGEST (the frame trailer over the whole
; report), bytes CHUNK (at most `*fn-nls-chunk-octets*' of the report from
; OFFSET).  The chunk width bounds the owner's reply and the client's read per
; request; it bounds no report: a longer report takes more requests.

(defconst *fn-nls-magic* '(70 78 76 83)) ; FNLS
(defconst *fn-nls-version* 1)
(defconst *fn-nls-request-kind* 1)
(defconst *fn-nls-reply-kind* 2)
; Work bound: report octets per reply.
(defconst *fn-nls-chunk-octets* 131072)
; Work bound: the pages of one report a client re-asks after the report
; changed under it before it answers uncertain.
(defconst *fn-nls-max-restarts* 8)
; Work bound: the reply payload's heads (two uints, two byte-string heads,
; the digest) past the chunk.
(defconst *fn-nls-max-payload* (+ *fn-nls-chunk-octets* 64))
(defconst *fn-nls-max-frame* (+ *fn-frame-overhead-octets* *fn-nls-max-payload*))

(defun fn-nls-kind-code (kind)
  (declare (xargs :guard t))
  (cond ((equal kind :status) 1) ((equal kind :pins) 2)
        ((equal kind :peers) 3) ((equal kind :obligations) 4) (t 0)))

(defun fn-nls-code-kind (code)
  (declare (xargs :guard t))
  (cond ((equal code 1) :status) ((equal code 2) :pins)
        ((equal code 3) :peers) ((equal code 4) :obligations) (t nil)))

(defun fn-nls-seal (kind payload)
  (declare (xargs :guard t))
  (if (not (and (fn-cbor-octetp kind)
                (fn-cbor-octet-listp payload)
                (<= (len payload) *fn-nls-max-payload*)))
      :bad
    (let ((protected (fn-frame-protected *fn-nls-magic* *fn-nls-version*
                                         kind payload)))
      (append protected (fn-frame-trailer protected)))))

(defun fn-nls-open (octets expected-kind)
  (declare (xargs :guard t))
  (if (not (fn-cbor-octet-listp octets))
      (fn-frame-error :malformed)
    (let ((opened (fn-frame-decode octets
                                   (fn-frame-trailer
                                    (fn-frame-protected-prefix octets))
                                   *fn-nls-max-payload*)))
      (if (and (fn-frame-result-okp opened)
               (equal (fn-frame-result-magic opened) *fn-nls-magic*)
               (equal (fn-frame-result-version opened) *fn-nls-version*)
               (equal (fn-frame-result-kind opened) expected-kind))
          opened
        (fn-frame-error :live-status-frame)))))

(defun fn-nls-request-encode (kind offset)
  (declare (xargs :guard t))
  (if (not (and (member-equal kind *fn-nls-kinds*) (fn-record-uint32p offset)))
      :bad
    (fn-nls-seal *fn-nls-request-kind*
                 (append (fn-cbor-encode (cons :uint (fn-nls-kind-code kind)))
                         (fn-cbor-encode (cons :uint offset))))))

(defun fn-nls-request-decode (octets)
  "(:live-status KIND OFFSET), or (:refused REASON)."
  (declare (xargs :guard t :verify-guards nil))
  (let ((opened (fn-nls-open octets *fn-nls-request-kind*)))
    (if (not (fn-frame-result-okp opened))
        (list :refused :frame)
      (let* ((payload (fn-frame-result-payload opened))
             (first (fn-record-read-uint payload)))
        (if (not (fn-record-parse-okp first))
            (list :refused :kind)
          (let ((second (fn-record-read-uint (fn-record-parse-rest first))))
            (if (not (and (fn-record-parse-okp second)
                          (fn-nls-code-kind (fn-record-parse-value first))
                          (natp (fn-record-parse-value second))
                          (null (fn-record-parse-rest second))))
                (list :refused :fields)
              (list :live-status (fn-nls-code-kind (fn-record-parse-value first))
                    (fn-record-parse-value second)))))))))

(defun fn-nls-status-code (status)
  (declare (xargs :guard t))
  (if (equal status :accepted) 1 2))

(defun fn-nls-reply-payload (status total digest chunk)
  (declare (xargs :guard t))
  (append (fn-cbor-encode (cons :uint (fn-nls-status-code status)))
          (fn-cbor-encode (cons :uint total))
          (fn-record-item-encode (cons :bytes digest))
          (fn-record-item-encode (cons :bytes chunk))))

(defun fn-nls-reply-encode (status total digest chunk)
  (declare (xargs :guard t))
  (fn-nls-seal *fn-nls-reply-kind*
               (fn-nls-reply-payload status total digest chunk)))

(defun fn-nls-reply-decode (octets)
  "(:reply STATUS TOTAL DIGEST CHUNK), or :bad."
  (declare (xargs :guard t :verify-guards nil))
  (let ((opened (fn-nls-open octets *fn-nls-reply-kind*)))
    (if (not (fn-frame-result-okp opened))
        :bad
      (let* ((r1 (fn-record-read-uint (fn-frame-result-payload opened)))
             (r2 (fn-record-read-uint (fn-record-parse-rest r1)))
             (r3 (fn-record-read-bytes (fn-record-parse-rest r2)))
             (r4 (fn-record-read-bytes (fn-record-parse-rest r3))))
        (if (not (and (fn-record-parse-okp r1) (fn-record-parse-okp r2)
                      (fn-record-parse-okp r3) (fn-record-parse-okp r4)
                      (null (fn-record-parse-rest r4))))
            :bad
          (list :reply
                (if (equal (fn-record-parse-value r1) 1) :accepted :refused)
                (fn-record-parse-value r2)
                (fn-record-parse-value r3)
                (fn-record-parse-value r4)))))))

(defun fn-nls-page-width (report offset)
  (declare (xargs :guard t))
  (min *fn-nls-chunk-octets* (nfix (- (len report) (nfix offset)))))

(defun fn-nls-reply (report offset)
  "The owner's page of REPORT from OFFSET."
  (declare (xargs :guard t :verify-guards nil))
  (if (and (fn-cbor-octet-listp report)
           (fn-record-uint32p (len report))
           (natp offset)
           (<= offset (len report)))
      (fn-nls-reply-encode :accepted (len report) (fn-frame-trailer report)
                           (take (fn-nls-page-width report offset)
                                 (nthcdr offset report)))
    (fn-nls-reply-encode :refused 0 nil nil)))

(defun fn-nls-client-step (acc total digest reply)
  "The client's word on one page, with ACC the report octets so far and
TOTAL and DIGEST the first page's: (:done REPORT), (:next ACC TOTAL DIGEST)
to ask from (len ACC), (:restart) when the report changed under the pages,
(:refused) when the owner refused, (:transport) for a malformed page."
  (declare (xargs :guard t :verify-guards nil))
  (let ((d (fn-nls-reply-decode reply)))
    (cond
     ((not (and (consp d) (equal (car d) :reply))) (list :transport))
     ((not (equal (nth 1 d) :accepted)) (list :refused))
     ((and (consp acc)
           (not (and (equal (nth 2 d) total) (equal (nth 3 d) digest))))
      (list :restart))
     (t (let ((next (append (true-list-fix acc) (nth 4 d))))
          (cond ((not (natp (nth 2 d))) (list :transport))
                ((< (nth 2 d) (len next)) (list :transport))
                ((equal (len next) (nth 2 d)) (list :done next))
                ((not (consp (nth 4 d))) (list :transport))
                (t (list :next next (nth 2 d) (nth 3 d)))))))))

; Which process answers.  The client asks the owner whose control socket the
; configuration names; an owner that is not there (no socket, or a socket
; nothing accepts on: the connection failed before anything was sent) leaves
; the offline command, whose shared lock refuses while any owner holds the
; Store.  Any other outcome is the owner's, or uncertain, and is reported as
; such: a status is never answered from the Store behind a live owner.
(defun fn-nls-route (socket-present outcome)
  (declare (xargs :guard t))
  (cond ((not socket-present) :offline)
        ((equal outcome :before-submission) :offline)
        ((equal outcome :refused) :refused)
        (t :uncertain)))

; -----------------------------------------------------------------------------
; The exchange, proved

(encapsulate ()
(local
 (defthm fn-nls-protected-is-octets
   (implies (and (fn-frame-magicp magic)
                 (fn-cbor-octetp version)
                 (fn-cbor-octetp kind)
                 (fn-cbor-octet-listp payload)
                 (<= (len payload) *fn-cbor-max-uint*))
            (fn-cbor-octet-listp (fn-frame-protected magic version kind payload)))
   :hints (("Goal" :in-theory (e/d (fn-frame-protected fn-frame-header-octets)
                                   (fn-frame-header))))))
(local
 (defthm fn-nls-digest-is-octets
   (implies (fn-frame-digestp d) (fn-cbor-octet-listp d))
   :hints (("Goal" :in-theory (enable fn-frame-digestp)))))
(defthm fn-nls-open-of-seal
  (implies (and (fn-cbor-octetp kind)
                (fn-cbor-octet-listp payload)
                (<= (len payload) *fn-nls-max-payload*))
           (equal (fn-nls-open (fn-nls-seal kind payload) kind)
                  (fn-frame-ok *fn-nls-magic* *fn-nls-version* kind payload)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-frame-decode-of-host-framing
                            (magic *fn-nls-magic*) (version *fn-nls-version*)
                            (max-payload *fn-nls-max-payload*))
                 (:instance fn-frame-trailer-is-a-digest
                            (octets (fn-frame-protected *fn-nls-magic* *fn-nls-version*
                                                        kind payload))))
           :in-theory (e/d (fn-nls-open fn-nls-seal fn-frame-inputp fn-frame-magicp
                            fn-frame-result-okp fn-frame-ok fn-frame-result-magic fn-frame-result-version fn-frame-result-kind)
                           (fn-frame-decode-of-host-framing fn-frame-decode
                            fn-frame-trailer-is-a-digest
                            fn-frame-protected fn-frame-trailer
                            fn-frame-protected-prefix))))))

(encapsulate ()
(local
 (defthm fn-nls-octets-of-append
   (implies (and (fn-cbor-octet-listp a) (fn-cbor-octet-listp b))
            (fn-cbor-octet-listp (append a b)))))
(local
 (defthm fn-nls-read-bytes-alone
   (implies (and (fn-cbor-octet-listp xs) (<= (len xs) *fn-record-max-octets*))
            (equal (fn-record-read-bytes (fn-record-item-encode (cons :bytes xs)))
                   (fn-record-parse-ok xs nil)))
   :hints (("Goal" :use ((:instance fn-record-read-bytes-of-item-encoding (rest nil))
                         (:instance fn-record-item-encode-true-list (value (cons :bytes xs))))
            :in-theory (disable fn-record-read-bytes-of-item-encoding fn-record-item-encode-true-list
                                fn-record-read-bytes fn-record-item-encode)))))
(local
 (defthm fn-nls-reply-payload-octets
   (fn-cbor-octet-listp (fn-nls-reply-payload status total digest chunk))
   :hints (("Goal" :in-theory (e/d (fn-nls-reply-payload) (fn-cbor-encode fn-record-item-encode (:e fn-cbor-encode)))))))
(local
 (defthm fn-nls-open-of-reply-encode
   (implies (<= (len (fn-nls-reply-payload status total digest chunk))
                *fn-nls-max-payload*)
            (equal (fn-nls-open (fn-nls-reply-encode status total digest chunk) 2)
                   (fn-frame-ok *fn-nls-magic* *fn-nls-version* 2
                                (fn-nls-reply-payload status total digest chunk))))
   :hints (("Goal" :use ((:instance fn-nls-open-of-seal
                                    (kind 2)
                                    (payload (fn-nls-reply-payload status total digest chunk))))
            :in-theory (e/d (fn-nls-reply-encode)
                            (fn-nls-open-of-seal fn-nls-reply-payload fn-nls-open fn-nls-seal))))))
; The client reads back the status, total, digest and chunk the owner framed.
(defthm fn-nls-reply-decode-of-encode
  (implies (and (fn-record-uint32p total)
                (fn-cbor-octet-listp digest)
                (fn-cbor-octet-listp chunk)
                (<= (len digest) *fn-record-max-octets*)
                (<= (len chunk) *fn-record-max-octets*)
                (<= (len (fn-nls-reply-payload status total digest chunk))
                    *fn-nls-max-payload*))
           (equal (fn-nls-reply-decode (fn-nls-reply-encode status total digest chunk))
                  (list :reply (if (equal status :accepted) :accepted :refused)
                        total digest chunk)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-nls-reply-decode fn-nls-reply-payload fn-nls-status-code
                            fn-record-read-uint-of-encoding fn-record-read-bytes-of-item-encoding fn-nls-octets-of-append fn-nls-read-bytes-alone fn-record-cbor-encode-octets fn-record-item-encode-octets
                            fn-frame-result-okp fn-frame-ok fn-frame-result-payload)
                           (fn-nls-reply-encode fn-nls-open fn-nls-seal fn-record-read-uint
                            fn-record-read-bytes (:e fn-cbor-encode)
                            fn-cbor-encode fn-record-item-encode))))))

(encapsulate ()
(local
 (defthm fn-nls-argument-length
   (<= (len (fn-cbor-encode-argument major n)) 5)
   :rule-classes :linear
   :hints (("Goal" :in-theory (enable fn-cbor-encode-argument fn-cbor-u16-bytes fn-cbor-u32-bytes)))))
(defthm fn-nls-bytes-item-length
  (<= (len (fn-record-item-encode (cons :bytes xs))) (+ 5 (len xs)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable fn-record-item-encode fn-cbor-encode-bounded)))))

(encapsulate ()
(local
 (defthm fn-nls-octets-of-append-r
   (implies (and (fn-cbor-octet-listp a) (fn-cbor-octet-listp b))
            (fn-cbor-octet-listp (append a b)))))
(local
 (defthm fn-nls-octets-true-listp
   (implies (fn-cbor-octet-listp r) (true-listp r))))
(local
 (defthm fn-nls-read-uint-alone
   (implies (fn-record-uint32p n)
            (equal (fn-record-read-uint (fn-cbor-encode (cons :uint n)))
                   (fn-record-parse-ok n nil)))
   :hints (("Goal" :use ((:instance fn-record-read-uint-of-encoding (rest nil))
                         (:instance fn-record-cbor-encode-octets (value (cons :uint n))))
            :in-theory (disable fn-record-cbor-encode-octets fn-record-read-uint-of-encoding fn-record-read-uint fn-cbor-encode)))))
(local
 (defthm fn-nls-len-append-r
   (equal (len (append a b)) (+ (len a) (len b)))))
(local
 (defthm fn-nls-open-of-request-encode
   (implies (and (member-equal kind *fn-nls-kinds*) (fn-record-uint32p offset))
            (equal (fn-nls-open (fn-nls-request-encode kind offset) 1)
                   (fn-frame-ok *fn-nls-magic* *fn-nls-version* 1
                                (append (fn-cbor-encode (cons :uint (fn-nls-kind-code kind)))
                                        (fn-cbor-encode (cons :uint offset))))))
   :hints (("Goal" :use ((:instance fn-nls-open-of-seal
                                    (kind 1)
                                    (payload (append (fn-cbor-encode (cons :uint (fn-nls-kind-code kind)))
                                                     (fn-cbor-encode (cons :uint offset))))))
            :in-theory (e/d (fn-nls-request-encode fn-record-cbor-encode-octets
                             fn-record-cbor-uint-encoding-bound)
                            (fn-nls-open-of-seal fn-nls-open fn-nls-seal fn-nls-kind-code
                             fn-cbor-encode (:e fn-cbor-encode)))))))
; The owner reads back the kind and offset the client framed.
(defthm fn-nls-request-decode-of-encode
  (implies (and (member-equal kind *fn-nls-kinds*) (fn-record-uint32p offset))
           (equal (fn-nls-request-decode (fn-nls-request-encode kind offset))
                  (list :live-status kind offset)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-nls-request-decode fn-nls-kind-code
                            fn-nls-code-kind fn-record-read-uint-of-encoding fn-nls-read-uint-alone
                            fn-record-cbor-encode-octets
                            fn-frame-result-okp fn-frame-ok fn-frame-result-payload)
                           (fn-nls-request-encode fn-nls-open fn-nls-seal fn-record-read-uint
                            fn-cbor-encode (:e fn-cbor-encode)))))))

(encapsulate ()
(local
 (defthm fn-nls-take-append-nthcdr
   (implies (and (natp off) (natp k) (<= (+ off k) (len r)))
            (equal (append (take off r) (take k (nthcdr off r)))
                   (take (+ off k) r)))
   :hints (("Goal" :induct (nthcdr off r) :in-theory (enable take nthcdr)))))
(local
 (defthm fn-nls-take-len
   (implies (true-listp r) (equal (take (len r) r) r))))
(local
 (defthm fn-nls-octet-list-true
   (implies (fn-cbor-octet-listp r) (true-listp r))
   :rule-classes :forward-chaining))
(local
 (defthm fn-nls-octets-of-take-nthcdr
   (implies (and (fn-cbor-octet-listp r) (natp off) (natp k) (<= (+ off k) (len r)))
            (fn-cbor-octet-listp (take k (nthcdr off r))))
   :hints (("Goal" :induct (nthcdr off r) :in-theory (enable take nthcdr)))))
(local
 (defthm fn-nls-trailer-octets
   (implies (fn-cbor-octet-listp r)
            (and (fn-cbor-octet-listp (fn-frame-trailer r))
                 (equal (len (fn-frame-trailer r)) 32)))
   :hints (("Goal" :use fn-frame-trailer-is-a-digest
            :in-theory (e/d (fn-frame-digestp) (fn-frame-trailer-is-a-digest fn-frame-trailer))))))
(local
 (defthm fn-nls-len-append
   (equal (len (append a b)) (+ (len a) (len b)))))
(local
 (defthm fn-nls-digest-octets
   (and (fn-cbor-octet-listp (fn-frame-digest r))
        (equal (len (fn-frame-digest r)) 32))
   :hints (("Goal" :use fn-frame-digestp-of-fn-frame-digest
            :in-theory (e/d (fn-frame-digestp) (fn-frame-digestp-of-fn-frame-digest))))))
(local
 (defthm fn-nls-len-take
   (implies (natp k) (equal (len (take k r)) k))))
(defthm fn-nls-reply-decode-of-reply
  (implies (and (fn-cbor-octet-listp report)
                (fn-record-uint32p (len report))
                (natp off) (<= off (len report)))
           (equal (fn-nls-reply-decode (fn-nls-reply report off))
                  (list :reply :accepted (len report) (fn-frame-trailer report)
                        (take (fn-nls-page-width report off) (nthcdr off report)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-nls-reply-decode-of-encode
                            (status :accepted) (total (len report))
                            (digest (fn-frame-trailer report))
                            (chunk (take (fn-nls-page-width report off) (nthcdr off report)))))
           :in-theory (e/d (fn-nls-reply fn-nls-page-width fn-nls-reply-payload
                            fn-record-cbor-uint-encoding-bound fn-nls-bytes-item-length
                            fn-frame-trailer)
                           (fn-nls-reply-decode-of-encode fn-nls-reply-encode
                            fn-nls-reply-decode take nthcdr fn-cbor-encode
                            fn-record-item-encode)))))
(local
 (defthm fn-nls-consp-take
   (implies (posp k) (consp (take k r)))
   :hints (("Goal" :use ((:instance fn-nls-len-take))
            :in-theory (disable take fn-nls-len-take)))))
(local
 (defthm fn-nls-nthcdr-0 (equal (nthcdr 0 r) r)))
(local
 (defthm fn-nls-take-0 (equal (take 0 r) nil)))
; KEYSTONE (the pages join to the report).  The subjects are
; `fn-nls-reply', which the owner answers with
; (host/native-live-status-host.lisp `fn-native-live-status-host-reply'), and
; `fn-nls-client-step', which the client folds every page through
; (host/native/control.lisp `fnn-control-live-status').  When the client
; holds a prefix ACC of an octet REPORT (and, past the first page, the
; report's total and digest), the owner's page from (len ACC) takes it to
; the whole report, or to the strictly longer prefix of one more chunk; so
; asking from (len ACC) until :done yields exactly REPORT.
(defthm fn-nls-client-step-of-owner-reply
  (implies (and (fn-cbor-octet-listp report)
                (fn-record-uint32p (len report))
                (<= (len acc) (len report))
                (equal acc (take (len acc) report))
                (or (not (consp acc))
                    (and (equal total (len report))
                         (equal digest (fn-frame-trailer report)))))
           (equal (fn-nls-client-step acc total digest (fn-nls-reply report (len acc)))
                  (if (<= (len report) (+ (len acc) *fn-nls-chunk-octets*))
                      (list :done report)
                    (list :next (take (+ (len acc) *fn-nls-chunk-octets*) report)
                          (len report) (fn-frame-trailer report)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-nls-client-step fn-nls-page-width fn-record-uint32p)
                           (fn-nls-reply fn-nls-reply-encode fn-nls-reply-decode fn-frame-trailer
                            take nthcdr fn-cbor-encode fn-record-item-encode))))))
