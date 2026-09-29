;; fn: `peer set NAME --FLAG VALUE ...' and `peer login NAME LOGIN'
;; (operability review drag 7, row S5: peering as a record, not thirteen
;; words).
;
; `peer add' writes a whole record from thirteen positional words and
; replaces the peer's row group, so changing one field (the streaming word,
; the TLS mode, the login file) meant `peer remove' and the thirteen words
; again, and lost the group's extension rows (`peer pull', `peer carries',
; `peer budget', `peer feed', `peer distributions').  `peer set' is a delta
; over the peer as the live table holds it: each named flag replaces one
; field of the typed record (books/peer-config.lisp), every other field and
; every extension row stays, and the result must be a record
; `fn-cfg-peerp' admits, or the request is refused by the name of what is
; wrong.
;
; `peer login NAME LOGIN' asks the password and writes the peer's FNAUTH1
; file; ACL2 renders its octets (`fn-pset-login-octets') and the reader
; (`fn-fap-decode', books/feed-auth-profile.lisp) gives back exactly the
; login and password it was made from (`fn-pset-login-octets-round-trip'),
; so a generated file is never one the connection refuses.
;
; Host callers: books/native-admin.lisp `fn-native-admin-plan-deltas-over'
; and `fn-native-admin-plan-refusal-over' (from host/native-admin-host.lisp
; `fn-native-admin-host-owner-reconfigure' live and `fn-native-admin-host-
; apply' offline); host/native/peer-invite.lisp `fnn-pinv-login' calls
; `fn-pset-login-file' and `fn-pset-login-argv'.

(in-package "ACL2")
(include-book "peer-config")
(include-book "peer-host")
(include-book "feed-auth-profile")
(include-book "native-config")
(include-book "identity")
(include-book "native-admin-shape")

(local (in-theory (disable (tau-system))))

;; ---------------------------------------------------------------------------
;; The flags

(defconst *fn-pset-flags*
  '("--host" "--port" "--take" "--send" "--streaming" "--tls" "--server-name"
    "--anchor" "--login" "--allow-clear" "--principal" "--source-address"))

; The slots `fn-cfg-peer-rows' writes: the record.  Every other row of a
; peer's group is an extension row, kept by `peer set'.
(defconst *fn-pset-record-slots*
  '("path-identity" "transport-nntp" "transport-bp" "transport-security"
    "transport-server-name" "transport-trust-anchor" "inbound-groups"
    "inbound-inflight" "outbound-groups" "outbound-streaming"
    "outbound-backoff" "outbound-auth-profile" "auth-source-address"
    "auth-principal"))

; (:ok ALIST) or (:refused REASON): the words after `peer set NAME', as
; flag/value pairs; a flag twice, an unknown flag or a flag with no value is
; refused by name.
(defun fn-pset-options (words acc)
  (declare (xargs :guard (alistp acc)))
  (cond ((atom words) (list :ok (reverse acc)))
        ((not (member-equal (car words) *fn-pset-flags*))
         (list :refused :unknown-flag))
        ((atom (cdr words)) (list :refused :flag-without-value))
        ((not (stringp (cadr words))) (list :refused :flag-without-value))
        ((assoc-equal (car words) acc) (list :refused :repeated-flag))
        (t (fn-pset-options (cddr words)
                            (cons (cons (car words) (cadr words)) acc)))))

(defun fn-pset-opt (flag opts)
  (declare (xargs :guard t))
  (if (alistp opts) (cdr (assoc-equal flag opts)) nil))

;; ---------------------------------------------------------------------------
;; The edit of one typed record

(defun fn-pset-decimal (word lo hi)
  ; WORD's value when it is a decimal of at most ten digits in [lo, hi].
  (declare (xargs :guard (and (natp lo) (natp hi))))
  (if (and (fn-native-admin-decimalp word)
           (<= (length word) 10))
      (let ((n (fn-native-admin-decimal-value (coerce word 'list))))
        (if (and (natp n) (<= lo n) (<= n hi)) n nil))
    nil))

(defun fn-pset-boolean (word)
  ; (:ok BOOLEAN) for "true" / "false", else nil.
  (declare (xargs :guard t))
  (cond ((equal word "true") (list :ok t))
        ((equal word "false") (list :ok nil))
        (t nil)))

; The TLS mode word of a security value.
(defun fn-pset-mode-word (sec)
  (declare (xargs :guard t))
  (cond ((equal sec '(:clear)) "clear")
        ((and (consp sec) (consp (cdr sec)) (equal (cadr sec) :implicit))
         "implicit")
        (t "starttls")))

; The words that reselect a TLS security value's check: its server name
; and its anchor ("-" for the system's public roots).
(defun fn-pset-tls-words (sec)
  (declare (xargs :guard t))
  (if (and (true-listp sec) (equal (len sec) 4) (equal (car sec) :tls))
      (list (caddr sec)
            (if (equal (cadddr sec) :system-roots) "-" (cadddr sec)))
    (list "-" "-")))

; (:ok TRANSPORT) or (:refused REASON).
(defun fn-pset-transport (transport opts)
  (declare (xargs :guard t))
  (let ((host-w (fn-pset-opt "--host" opts))
        (port-w (fn-pset-opt "--port" opts))
        (mode-w (fn-pset-opt "--tls" opts))
        (name-w (fn-pset-opt "--server-name" opts))
        (anchor-w (fn-pset-opt "--anchor" opts)))
    (cond
     ((not (or host-w port-w mode-w name-w anchor-w)) (list :ok transport))
     ((not (and (true-listp transport) (equal (car transport) :nntp)
                (member-equal (len transport) '(3 5))))
      (list :refused :not-an-nntp-peer))
     (t
      (let* ((five (equal (len transport) 5))
             (host0 (if five (caddr transport) (cadr transport)))
             (port0 (if five (cadddr transport) (caddr transport)))
             (sec0 (if five (car (cddddr transport)) '(:clear)))
             (host (or host-w host0))
             (port (if port-w (fn-pset-decimal port-w 1 65535) port0))
             (mode (or mode-w (fn-pset-mode-word sec0)))
             (words0 (fn-pset-tls-words sec0))
             (name (or name-w (car words0)))
             (anchor (or anchor-w (cadr words0))))
        (cond
         ((not (fn-peer-hostp (fn-record-string-octets host)))
          (list :refused :host))
         ((not port) (list :refused :port))
         ((not (member-equal mode '("clear" "implicit" "starttls")))
          (list :refused :tls-mode))
         ((equal mode "clear")
          (if (or name-w anchor-w)
              (list :refused :server-name-without-tls)
            (list :ok (list :nntp 1 host port '(:clear)))))
         (t
          (let ((sel (fn-peer-tls-select host name anchor)))
            (if sel
                (list :ok (list :nntp 1 host port
                                (list :tls (if (equal mode "implicit")
                                               :implicit :starttls)
                                      (car sel) (cadr sel))))
              ; A numeric host needs --server-name, the name on its
              ; certificate (books/peer-host.lisp
              ; fn-peer-tls-select-numeric-host-needs-a-name-by-definition).
              (list :refused :tls-needs-server-name))))))))))

(defun fn-pset-inbound (inbound opts)
  (declare (xargs :guard t))
  (let ((take (fn-pset-opt "--take" opts)))
    (cond ((not take) (list :ok inbound))
          ((equal take "-") (list :ok nil))
          ((not (fn-cfg-wildmatp take)) (list :refused :take))
          ((and (true-listp inbound) (equal (len inbound) 3))
           (list :ok (list take (cadr inbound) (caddr inbound))))
          (t (list :ok (list take *fn-record-max-payload* 16))))))

;; A total reader: the Nth element of X when X is a true list.
(defun fn-pset-at (n x)
  (declare (xargs :guard t))
  (if (and (natp n) (true-listp x)) (nth n x) nil))

; The outbound half: --send, then --streaming, --login and --allow-clear
; over what --send left.
(defun fn-pset-outbound (outbound opts)
  (declare (xargs :guard t))
  (let* ((send (fn-pset-opt "--send" opts))
         (stream-w (fn-pset-opt "--streaming" opts))
         (login (fn-pset-opt "--login" opts))
         (clear-w (fn-pset-opt "--allow-clear" opts))
         (shaped (and (true-listp outbound) (member-equal (len outbound) '(4 5))))
         (base (cond ((equal send "-") nil)
                     ((not send) (if shaped outbound nil))
                     (shaped (cons send (cdr outbound)))
                     (t (list send t 1024 1000))))
         (stream (fn-pset-boolean stream-w))
         (clear (fn-pset-boolean clear-w))
         (policy0 (fn-pset-at 4 base))
         (clear0 (fn-pset-at 2 policy0))
         (four (list (fn-pset-at 0 base)
                     (if stream (fn-pset-at 1 stream) (fn-pset-at 1 base))
                     (fn-pset-at 2 base) (fn-pset-at 3 base))))
    (cond
     ((and send (not (equal send "-")) (not (fn-cfg-wildmatp send)))
      (list :refused :send))
     ((and stream-w (not stream)) (list :refused :streaming))
     ((and clear-w (not clear)) (list :refused :allow-clear))
     ((and (or stream-w login clear-w) (not base))
      ; The login, the streaming word and the clear-text permission belong
      ; to the sending half: what it would take is `--send GROUPS'.
      (list :refused :needs-send))
     ((not base) (list :ok nil))
     ((equal login "-")
      (if clear-w (list :refused :allow-clear-needs-login)
        (list :ok four)))
     (login
      (list :ok (append four (list (list :authinfo login
                                         (if clear (fn-pset-at 1 clear)
                                           clear0))))))
     (clear
      (if policy0
          (list :ok (append four (list (list :authinfo (fn-pset-at 1 policy0)
                                             (fn-pset-at 1 clear)))))
        (list :refused :allow-clear-needs-login)))
     (t (list :ok (if policy0 (append four (list policy0)) four))))))

(defun fn-pset-auth (auth opts)
  (declare (xargs :guard t))
  (let ((principal (fn-pset-opt "--principal" opts))
        (source (fn-pset-opt "--source-address" opts)))
    (cond ((and principal source) (list :refused :auth-twice))
          (principal
           (if (and (stringp principal)
                    (equal (len (fn-record-string-octets principal)) 64)
                    (fn-id-hex-listp (fn-record-string-octets principal)))
               (list :ok (list :principal principal))
             (list :refused :principal)))
          (source
           (if (and (stringp source)
                    (not (equal (fn-native-config-ipv4-address
                                 (fn-record-string-octets source)) :bad)))
               (list :ok (list :source-address source))
             (list :refused :source-address)))
          (t (list :ok auth)))))

; (:ok RECORD) or (:refused REASON): P with the named fields replaced.
(defun fn-pset-edit (p opts)
  (declare (xargs :guard t))
  (let ((tr (fn-pset-transport (fn-cfg-peer-transport p) opts))
        (in (fn-pset-inbound (fn-cfg-peer-inbound p) opts))
        (out (fn-pset-outbound (fn-cfg-peer-outbound p) opts))
        (auth (fn-pset-auth (fn-cfg-peer-auth p) opts)))
    (cond ((not (equal (car tr) :ok)) tr)
          ((not (equal (car in) :ok)) in)
          ((not (equal (car out) :ok)) out)
          ((not (equal (car auth) :ok)) auth)
          (t (let ((q (fn-cfg-peer-make (fn-cfg-peer-name p)
                                        (fn-cfg-peer-path-identity p)
                                        (cadr tr) (cadr in) (cadr out)
                                        (cadr auth))))
               (if (fn-cfg-peerp q)
                   (list :ok q)
                 (list :refused :peer-record)))))))

;; ---------------------------------------------------------------------------
;; The delta over the live table

(defun fn-pset-extension-rows (rows)
  (declare (xargs :guard t))
  (if (consp rows)
      (if (member-equal (fn-cfg-row-b (car rows)) *fn-pset-record-slots*)
          (fn-pset-extension-rows (cdr rows))
        (cons (car rows) (fn-pset-extension-rows (cdr rows))))
    nil))

; (:ok DELTAS) or (:refused REASON), over the peers rows PEERS.
(defun fn-pset-plan (name opts peers)
  (declare (xargs :guard t :verify-guards nil))
  (let* ((rows (fn-cfg-rows-with-key peers name))
         (p (fn-cfg-peer-of-rows name rows)))
    (if (not p)
        (list :refused :no-such-peer)
      (let ((edit (fn-pset-edit p opts)))
        (if (equal (car edit) :ok)
            (list :ok (list (fn-cfg-set-peer
                             name
                             (append (fn-cfg-peer-rows (cadr edit))
                                     (fn-pset-extension-rows rows)))))
          edit)))))

;; ---------------------------------------------------------------------------
;; The login file

; The FNAUTH1 file for the login LOGIN (a string) and the password octets
; W, or nil when the reader would refuse either (a token of printable
; octets, 33 to 126, at most 494 octets; the whole file at most 1,024).
(defun fn-pset-login-octets (login w)
  (declare (xargs :guard t))
  (let ((u (if (stringp login) (fn-record-string-octets login) nil)))
    (if (and (fn-fap-tokenp u) (fn-fap-tokenp w) (true-listp w)
             (<= (+ (len *fn-fap-magic*) (len u) 1 (len w) 1) *fn-fap-max-octets*))
        (append *fn-fap-magic* u (list 10) w (list 10))
      nil)))

; `peer login NAME LOGIN FILE': the two password entries the host read
; (octet lists, never an argv word), decided here: (:ok OCTETS) or
; (:refused REASON).  host/native/peer-invite.lisp `fnn-pinv-login'.
(defun fn-pset-login-file (login password confirm)
  (declare (xargs :guard t))
  (cond ((not (equal password confirm)) (list :refused :passwords-differ))
        ((not (and (stringp login) (fn-fap-tokenp (fn-record-string-octets login))))
         (list :refused :login))
        ((not (fn-pset-login-octets login password)) (list :refused :password))
        (t (list :ok (fn-pset-login-octets login password)))))

; The administrative words the login's file then sets on the peer, live or
; offline: `peer set NAME --login FILE', as the argv octets the plan reads.
(defun fn-pset-login-argv (name file)
  (declare (xargs :guard t))
  (list (fn-record-string-octets "peer") (fn-record-string-octets "set")
        (fn-record-string-octets (if (stringp name) name ""))
        (fn-record-string-octets "--login")
        (fn-record-string-octets (if (stringp file) file ""))))

;; ---------------------------------------------------------------------------
;; What `peer set' changes, and what it keeps

(defthm fn-pset-edit-is-a-peer-record
  (implies (equal (car (fn-pset-edit p opts)) :ok)
           (fn-cfg-peerp (cadr (fn-pset-edit p opts))))
  :hints (("Goal" :in-theory (disable fn-cfg-peerp fn-pset-transport
                                      fn-pset-inbound fn-pset-outbound
                                      fn-pset-auth))))

; The peer's name and path identity are never a flag: the record stays the
; same peer.
(defthm fn-pset-edit-keeps-the-peer
  (implies (equal (car (fn-pset-edit p opts)) :ok)
           (and (equal (fn-cfg-peer-name (cadr (fn-pset-edit p opts)))
                       (fn-cfg-peer-name p))
                (equal (fn-cfg-peer-path-identity (cadr (fn-pset-edit p opts)))
                       (fn-cfg-peer-path-identity p))))
  :hints (("Goal" :in-theory (disable fn-cfg-peerp fn-pset-transport
                                      fn-pset-inbound fn-pset-outbound
                                      fn-pset-auth))))

;; A field no flag names keeps its value (the frame), for a live record.
(local (defthm fn-pset-len-equal-const
  (implies (and (syntaxp (quotep k)) (natp k))
           (equal (equal (len x) k)
                  (if (zp k) (not (consp x))
                    (and (consp x) (equal (len (cdr x)) (+ -1 k))))))))

(defthm fn-pset-transport-unnamed
  (implies (not (or (fn-pset-opt "--host" opts) (fn-pset-opt "--port" opts)
                    (fn-pset-opt "--tls" opts) (fn-pset-opt "--server-name" opts)
                    (fn-pset-opt "--anchor" opts)))
           (equal (fn-pset-transport transport opts) (list :ok transport)))
  :hints (("Goal" :in-theory (disable fn-pset-opt))))

(defthm fn-pset-inbound-unnamed
  (implies (not (fn-pset-opt "--take" opts))
           (equal (fn-pset-inbound inbound opts) (list :ok inbound)))
  :hints (("Goal" :in-theory (disable fn-pset-opt))))

(defthm fn-pset-auth-unnamed
  (implies (not (or (fn-pset-opt "--principal" opts)
                    (fn-pset-opt "--source-address" opts)))
           (equal (fn-pset-auth auth opts) (list :ok auth)))
  :hints (("Goal" :in-theory (disable fn-pset-opt))))

(defthm fn-pset-outbound-unnamed
  (implies (and (fn-cfg-peer-outboundp outbound)
                (not (or (fn-pset-opt "--send" opts)
                         (fn-pset-opt "--streaming" opts)
                         (fn-pset-opt "--login" opts)
                         (fn-pset-opt "--allow-clear" opts))))
           (equal (fn-pset-outbound outbound opts) (list :ok outbound)))
  :hints (("Goal" :in-theory (e/d (fn-pset-at fn-cfg-peer-outboundp) (fn-pset-opt fn-cfg-wildmatp
                                                 fn-record-uint32p fn-cfg-cstringp)))))

(defthm fn-pset-edit-keeps-unnamed-fields
  (implies (and (fn-cfg-peerp p)
                (equal (car (fn-pset-edit p opts)) :ok))
           (let ((q (cadr (fn-pset-edit p opts))))
             (and (implies (not (or (fn-pset-opt "--host" opts)
                                    (fn-pset-opt "--port" opts)
                                    (fn-pset-opt "--tls" opts)
                                    (fn-pset-opt "--server-name" opts)
                                    (fn-pset-opt "--anchor" opts)))
                           (equal (fn-cfg-peer-transport q)
                                  (fn-cfg-peer-transport p)))
                  (implies (not (fn-pset-opt "--take" opts))
                           (equal (fn-cfg-peer-inbound q)
                                  (fn-cfg-peer-inbound p)))
                  (implies (not (or (fn-pset-opt "--send" opts)
                                    (fn-pset-opt "--streaming" opts)
                                    (fn-pset-opt "--login" opts)
                                    (fn-pset-opt "--allow-clear" opts)))
                           (equal (fn-cfg-peer-outbound q)
                                  (fn-cfg-peer-outbound p)))
                  (implies (not (or (fn-pset-opt "--principal" opts)
                                    (fn-pset-opt "--source-address" opts)))
                           (equal (fn-cfg-peer-auth q)
                                  (fn-cfg-peer-auth p))))))
  :hints (("Goal" :in-theory (e/d (fn-cfg-peerp)
                                  (fn-pset-opt fn-pset-transport fn-pset-inbound
                                   fn-pset-outbound fn-pset-auth
                                   fn-cfg-peer-shapep fn-cfg-labelp
                                   fn-path-identityp fn-cfg-peer-transportp
                                   fn-cfg-peer-inboundp fn-cfg-peer-authp))
           :cases ((fn-pset-opt "--host" opts)))))

;; A named field takes the flag's value: the groups sent and the login file.
(defthm fn-pset-outbound-sets-the-named-send-and-login
  (implies (equal (car (fn-pset-outbound out opts)) :ok)
           (let ((o (cadr (fn-pset-outbound out opts)))
                 (send (fn-pset-opt "--send" opts))
                 (login (fn-pset-opt "--login" opts)))
             (and (implies (and send (not (equal send "-")))
                           (equal (car o) send))
                  (implies (equal send "-") (equal o nil))
                  (implies (and login (not (equal login "-")))
                           (equal (cadr (nth 4 o)) login)))))
  :hints (("Goal" :in-theory (e/d (fn-pset-at) (fn-pset-opt fn-cfg-wildmatp)))))

(defthm fn-pset-edit-sets-the-named-send-and-login
  (implies (equal (car (fn-pset-edit p opts)) :ok)
           (let ((q (cadr (fn-pset-edit p opts)))
                 (send (fn-pset-opt "--send" opts))
                 (login (fn-pset-opt "--login" opts)))
             (and (implies (and send (not (equal send "-")))
                           (equal (fn-cfg-peer-outbound-groups q) send))
                  (implies (equal send "-")
                           (equal (fn-cfg-peer-outbound q) nil))
                  (implies (and login (not (equal login "-")))
                           (equal (cadr (nth 4 (fn-cfg-peer-outbound q))) login)))))
  :hints (("Goal" :in-theory (e/d (fn-cfg-ag-car fn-cfg-peer-outbound-groups)
                                  (fn-cfg-peerp fn-pset-opt fn-pset-outbound
                                   fn-pset-transport fn-pset-inbound fn-pset-auth))
           :use ((:instance fn-pset-outbound-sets-the-named-send-and-login
                            (out (fn-cfg-peer-outbound p)))))))

(local (defthm fn-pset-rows-with-key-is-keyed
  (fn-cfg-rows-keyed-p (fn-cfg-rows-with-key rows a) a)
  :hints (("Goal" :in-theory (enable fn-cfg-rows-with-key fn-cfg-rows-keyed-p)))))

(local (defthm fn-pset-extension-rows-keep-the-key
  (implies (fn-cfg-rows-keyed-p rows a)
           (fn-cfg-rows-keyed-p (fn-pset-extension-rows rows) a))
  :hints (("Goal" :in-theory (enable fn-cfg-rows-keyed-p)))))

(local (defthm fn-pset-peer-of-rows-name
  (implies (fn-cfg-peer-of-rows name rows)
           (equal (fn-cfg-peer-name (fn-cfg-peer-of-rows name rows)) name))
  :hints (("Goal" :in-theory (e/d (fn-cfg-peer-of-rows) (fn-cfg-peerp fn-cfg-peer-slot))))))

(local (defthm fn-pset-record-rows-keyed
  (fn-cfg-rows-keyed-p (fn-cfg-peer-rows p) (fn-cfg-peer-name p))
  :hints (("Goal" :in-theory (e/d (fn-cfg-peer-rows fn-cfg-rows-keyed-p)
                                  ((:d fn-cfg-ag-car) (:d fn-cfg-ag-cdr)
                                   (:d fn-cfg-peer-outbound-auth)))))))

(local (defthm fn-pset-record-rows-keyed-by-name
  (implies (equal (fn-cfg-peer-name p) k)
           (fn-cfg-rows-keyed-p (fn-cfg-peer-rows p) k))))

(local (defthm fn-pset-rows-with-key-of-append
  (equal (fn-cfg-rows-with-key (append a b) k)
         (append (fn-cfg-rows-with-key a k) (fn-cfg-rows-with-key b k)))
  :hints (("Goal" :in-theory (enable fn-cfg-rows-with-key)))))

(local (defthm fn-pset-rows-with-key-of-without-key
  (equal (fn-cfg-rows-with-key (fn-cfg-rows-without-key rows k) k) nil)
  :hints (("Goal" :in-theory (enable fn-cfg-rows-with-key fn-cfg-rows-without-key)))))

(local (defthm fn-pset-rows-with-key-of-keyed
  (implies (fn-cfg-rows-keyed-p rows k)
           (equal (fn-cfg-rows-with-key rows k) (true-list-fix rows)))
  :hints (("Goal" :in-theory (enable fn-cfg-rows-with-key fn-cfg-rows-keyed-p)))))

(local (defthm fn-pset-true-listp-of-record-rows
  (true-listp (fn-cfg-peer-rows p))
  :hints (("Goal" :in-theory (e/d (fn-cfg-peer-rows)
                                  ((:d fn-cfg-ag-car) (:d fn-cfg-ag-cdr)
                                   (:d fn-cfg-peer-outbound-auth)))))))

(verify-guards fn-pset-plan
  :hints (("Goal" :in-theory (disable fn-pset-edit fn-cfg-peer-of-rows
                                      fn-cfg-peer-rows))))

;  KEYSTONE (row S5).  An accepted `peer set' leaves the peer's row group
; exactly the edited record's rows followed by the extension rows the group
; held (pull, catch-up, carries, budget, feed pause, distributions), and the
; edited record is the live record with only the named fields replaced
; (fn-pset-edit-keeps-unnamed-fields) and a record `fn-cfg-peerp' admits
; (fn-pset-edit-is-a-peer-record).  The subject is the delta the host
; applies: host/native-admin-host.lisp reaches it through
; books/native-admin.lisp `fn-native-admin-plan-deltas-over'.
(defthm fn-pset-plan-sets-the-record-and-keeps-the-extensions
  (implies (equal (car (fn-pset-plan name opts peers)) :ok)
           (equal (fn-cfg-rows-with-key
                   (fn-cfg-peers (fn-cfg-apply-delta
                                  v gen stamp
                                  (car (cadr (fn-pset-plan name opts peers)))))
                   name)
                  (append (fn-cfg-peer-rows
                           (cadr (fn-pset-edit (fn-cfg-peer-find name peers) opts)))
                          (fn-pset-extension-rows
                           (fn-cfg-rows-with-key peers name)))))
  :hints (("Goal" :in-theory (e/d (fn-cfg-apply-delta fn-cfg-set-peer
                                   fn-cfg-peer-find)
                                  (fn-pset-edit fn-cfg-peer-of-rows
                                   fn-cfg-peer-rows)))))

;; ---------------------------------------------------------------------------
;; The login file round trip

(local (defthm fn-pset-printable-has-no-newline
  (implies (fn-nntp-printable-tokenp xs)
           (not (member-equal 10 xs)))
  :hints (("Goal" :in-theory (enable fn-nntp-printable-tokenp)))))

(local (defthm fn-pset-reverse-aux-is-revappend
  (equal (fn-fap-reverse-aux xs out) (revappend xs out))
  :hints (("Goal" :in-theory (enable fn-fap-reverse-aux)))))

(local (defthm fn-pset-line-aux-of-token
  (implies (and (not (member-equal 10 u)) (true-listp u))
           (equal (fn-fap-line-aux (append u (cons 10 rest)) rev)
                  (list :ok (revappend (revappend u rev) nil) rest)))
  :hints (("Goal" :in-theory (enable fn-fap-line-aux fn-fap-reverse)
           :induct (fn-fap-line-aux u rev)))))

(local (defthm fn-pset-revappend-revappend
  (implies (true-listp u)
           (equal (revappend (revappend u nil) nil) u))))

(local (defthm fn-pset-printable-octets
  (implies (and (fn-nntp-printable-tokenp xs) (true-listp xs))
           (fn-wire-octet-listp xs))
  :hints (("Goal" :in-theory (enable fn-nntp-printable-tokenp fn-wire-octet-listp)))))

(local (defthm fn-pset-append-octets
  (implies (true-listp a)
           (equal (fn-wire-octet-listp (append a b))
                  (and (fn-wire-octet-listp a) (fn-wire-octet-listp b))))
  :hints (("Goal" :in-theory (enable fn-wire-octet-listp)))))

(local (defthm fn-pset-decode-of-login-lines
  (implies (and (fn-fap-tokenp u) (fn-fap-tokenp w)
                (true-listp u) (true-listp w)
                (<= (+ 10 (len u) (len w)) *fn-fap-max-octets*))
           (equal (fn-fap-decode (append *fn-fap-magic* u (list 10) w (list 10)))
                  (list :ok u w)))
  :hints (("Goal" :in-theory (e/d (fn-fap-decode fn-fap-line fn-fap-drop
                                   fn-fap-prefixp fn-fap-tokenp fn-wire-octet-listp
                                   fn-wire-octetp)
                                  (fn-nntp-printable-tokenp))))))

;  KEYSTONE (row S5).  The file `peer login' writes is one the connection
; reads back as exactly the login and password it was made from.  The
; reader is the function the owner calls on the file's bytes
; (host/native/feed-service.lisp `fnn-feed-auth-profile').
(defthm fn-pset-login-octets-round-trip
  (implies (fn-pset-login-octets login password)
           (equal (fn-fap-decode (fn-pset-login-octets login password))
                  (list :ok (fn-record-string-octets login) password)))
  :hints (("Goal" :in-theory (disable fn-fap-decode fn-fap-tokenp
                                      fn-record-string-octets)
           :use ((:instance fn-pset-decode-of-login-lines
                            (u (fn-record-string-octets login))
                            (w password))))))

; The file `peer login' writes (fn-pset-login-file's :ok octets) is the
; round trip's: the reader gives back the login and the password entered.
(defthm fn-pset-login-file-reads-back
  (implies (equal (car (fn-pset-login-file login password confirm)) :ok)
           (equal (fn-fap-decode (cadr (fn-pset-login-file login password confirm)))
                  (list :ok (fn-record-string-octets login) password)))
  :hints (("Goal" :in-theory (disable fn-pset-login-octets fn-fap-decode
                                      fn-fap-tokenp fn-record-string-octets))))

; The value an accepted `peer set' plan carries in the administrative
; result (books/native-admin-peer.lisp): (:peer-set OPTIONS).
(defun fn-pset-plan-valuep (value)
  (declare (xargs :guard t))
  (and (true-listp value) (equal (len value) 2) (equal (car value) :peer-set)))
