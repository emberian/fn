; fn: bounded native AUTHINFO credential profile.
;
; The deployed credential file is a deliberately small TOML subset emitted by
; `fn principal set-password`: comments/blank lines and repeated
; [login."NAME"] tables with principal, salt, digest and posting fields.
; This book owns every interpretation.  The raw native host supplies bounded
; file octets and the policy bits already normalized by books/native-config;
; it never decodes hex, builds a verifier, assigns posting permission or
; decides whether a profile is usable.

(in-package "ACL2")
(include-book "native-config")
(include-book "nntp-auth")
(include-book "identity")

; D27, PRF-102.  The number of credentials is the operator's: the store
; profile's `max-credentials' (books/byte-store-frame.lisp field 12,
; `fn-bs-profile-max-credentials'), which the host reads from the store and
; passes as MAX-CREDENTIALS (pre-D27: 128).  The file's octet and line
; bounds follow it.  The two constants below bound work per credential, not
; data: one canonical table (`fn-native-auth-admin-serialize-cred') is six
; lines and under 320 octets, and the per-credential figure leaves room for
; the operator's comments; one extra unit covers the writer's header.
(defconst *fn-native-auth-octets-per-credential* 512)
(defconst *fn-native-auth-lines-per-credential* 8)

(defun fn-native-auth-max-octets (max-credentials)
  (declare (xargs :guard t))
  (* *fn-native-auth-octets-per-credential* (+ 1 (nfix max-credentials))))

(defun fn-native-auth-max-lines (max-credentials)
  (declare (xargs :guard t))
  (* *fn-native-auth-lines-per-credential* (+ 1 (nfix max-credentials))))

(defun fn-native-auth-line-count (xs)
  ; Count conventional text lines: every LF ends one line, and nonempty bytes
  ; after the final LF form one more.  fn-ncfg-lines deliberately retains a
  ; terminal empty segment for parsing; that segment is not a 1,025th line in
  ; a file containing exactly 1,024 newline-terminated lines.
  (declare (xargs :guard t))
  (if (consp xs)
      (if (consp (cdr xs))
          (+ (if (equal (car xs) 10) 1 0)
             (fn-native-auth-line-count (cdr xs)))
        1)
    0))

(defun fn-native-auth-prefixp (prefix xs)
  (declare (xargs :guard t))
  (if (consp prefix)
      (and (consp xs) (equal (car prefix) (car xs))
           (fn-native-auth-prefixp (cdr prefix) (cdr xs)))
    t))

(defun fn-native-auth-drop (n xs)
  (declare (xargs :guard t))
  (if (and (natp n) (not (zp n)) (consp xs))
      (fn-native-auth-drop (1- n) (cdr xs))
    xs))

(defun fn-native-auth-last-two-p (xs a b)
  (declare (xargs :guard t))
  (and (true-listp xs) (<= 2 (len xs))
       (equal (nth (- (len xs) 2) xs) a)
       (equal (nth (1- (len xs)) xs) b)))

(defun fn-native-auth-butlast-two (xs)
  (declare (xargs :guard t))
  (if (and (consp xs) (consp (cdr xs)) (consp (cdr (cdr xs))))
      (cons (car xs) (fn-native-auth-butlast-two (cdr xs)))
    nil))

(defun fn-native-auth-login-namep (name)
  ; The canonical writer emits NAME through bin/fn's toml_quote: an NNTP
  ; printable token with neither TOML quote nor backslash.  Reusing both
  ; predicates keeps the file grammar and the served USER token identical.
  (declare (xargs :guard t))
  (and (consp name) (true-listp name)
       (<= (len name) *fn-auth-max-name-octets*)
       (fn-nntp-printable-tokenp name)
       (fn-ncfg-printablep name)))

(defun fn-native-auth-table-name (line)
  ; Exact canonical table syntax: [login."printable-token"].
  (declare (xargs :guard t))
  (let* ((trimmed (fn-ncfg-trim line))
         (prefix '(91 108 111 103 105 110 46 34)))
    (if (and (fn-native-auth-prefixp prefix trimmed)
             (fn-native-auth-last-two-p trimmed 34 93))
        (let ((name (fn-native-auth-butlast-two
                     (fn-native-auth-drop (len prefix) trimmed))))
          (if (fn-native-auth-login-namep name)
              name
            :bad))
      :bad)))

(defun fn-native-auth-hex (value width)
  (declare (xargs :guard t))
  (let ((octets (if (stringp value) (fn-record-string-octets value) :bad)))
    (if (and (true-listp octets) (natp width)
             (equal (len octets) (* 2 width))
             (fn-id-hex-listp octets))
        (fn-id-unhex octets)
      :bad)))

(defun fn-native-auth-field (line)
  ; Reuse native-config's bounded `key = value' tokenizer and quoted/bool
  ; values.  Auth adds no second whitespace, quoting or boolean grammar.
  (declare (xargs :guard t))
  (let ((split (fn-ncfg-split-equals (fn-ncfg-trim line) nil)))
    (if (equal split :bad)
        :bad
      (let* ((key-octets (fn-ncfg-trim (fn-ncfg-first split)))
             (key (fn-record-octets-string key-octets))
             (value (fn-ncfg-parse-value
                     (fn-ncfg-trim (fn-ncfg-second split)))))
        (if (and (fn-ncfg-identp key-octets)
                 (member-equal key '("principal" "salt" "digest" "posting"
                                     "secret"))
                 (not (equal value :bad)))
            (list key value)
          :bad)))))

(defun fn-native-auth-assoc (key fields)
  (declare (xargs :guard t))
  (if (consp fields)
      (if (equal key (fn-ncfg-first (fn-ncfg-first fields)))
          (fn-ncfg-first fields)
        (fn-native-auth-assoc key (cdr fields)))
    nil))

(defun fn-native-auth-string-field (key fields)
  (declare (xargs :guard t))
  (let* ((pair (fn-native-auth-assoc key fields))
         (value (fn-ncfg-second pair)))
    (if (equal (fn-ncfg-first value) :string)
        (fn-ncfg-second value)
      :bad)))

(defun fn-native-auth-bool-field (key fields)
  (declare (xargs :guard t))
  (let* ((pair (fn-native-auth-assoc key fields))
         (value (fn-ncfg-second pair)))
    (if (equal (fn-ncfg-first value) :bool)
        (fn-ncfg-second value)
      :bad)))

(defun fn-native-auth-finish (name fields)
  (declare (xargs :guard t))
  (if (null name)
      (if (null fields) (list :empty) (list :refused :field-before-table))
    (if (fn-native-auth-assoc "secret" fields)
        (list :refused :cleartext-credential)
      (let* ((principal-text (fn-native-auth-string-field "principal" fields))
             (salt-text (fn-native-auth-string-field "salt" fields))
             (digest-text (fn-native-auth-string-field "digest" fields))
             (posting (fn-native-auth-bool-field "posting" fields))
             (principal (fn-native-auth-hex principal-text 32))
             (salt (fn-native-auth-hex salt-text 16))
             (digest (fn-native-auth-hex digest-text 32)))
        (if (or (equal principal :bad) (equal salt :bad) (equal digest :bad)
                (equal posting :bad))
            (list :refused :credential-shape)
          (let ((cred (fn-auth-make-cred
                       name principal (fn-authsec-verifier salt digest) posting)))
            (if (fn-auth-credp cred) (list :credential cred)
              (list :refused :credential-shape))))))))

(defun fn-native-auth-name-memberp (name creds)
  (declare (xargs :guard t))
  (if (consp creds)
      (or (equal name (fn-auth-cred-name (car creds)))
          (fn-native-auth-name-memberp name (cdr creds)))
    nil))

(defun fn-native-auth-parse-lines (lines name fields creds max-credentials)
  (declare (xargs :guard t
                  :measure (acl2-count lines)))
  (if (consp lines)
      (let ((line (fn-ncfg-trim (car lines))))
        (cond
         ((or (null line) (equal (car line) 35))
          (fn-native-auth-parse-lines (cdr lines) name fields creds max-credentials))
         ((equal (car line) 91)
          (let ((next-name (fn-native-auth-table-name line))
                (done (fn-native-auth-finish name fields)))
            (cond ((equal next-name :bad) (list :refused :table))
                  ((equal (fn-ncfg-first done) :refused) done)
                  ((fn-native-auth-name-memberp next-name creds)
                   (list :refused :duplicate-login))
                  (t (let ((next-creds
                            (if (equal (fn-ncfg-first done) :credential)
                                (cons (fn-ncfg-second done) creds) creds)))
                       (cond
                        ((fn-native-auth-name-memberp next-name next-creds)
                         (list :refused :duplicate-login))
                        ((<= (nfix max-credentials) (len next-creds))
                         (list :refused :too-many-credentials))
                        (t (fn-native-auth-parse-lines
                            (cdr lines) next-name nil next-creds
                            max-credentials))))))))
         (t
          (let ((field (fn-native-auth-field line)))
            (cond ((equal field :bad) (list :refused :field))
                  ((null name) (list :refused :field-before-table))
                  ((fn-native-auth-assoc (fn-ncfg-first field) fields)
                   (list :refused :duplicate-field))
                  (t (fn-native-auth-parse-lines
                      (cdr lines) name (cons field fields) creds
                      max-credentials)))))))
    (let ((done (fn-native-auth-finish name fields)))
      (cond ((equal (fn-ncfg-first done) :refused) done)
            ((equal (fn-ncfg-first done) :credential)
             (cond
              ((fn-native-auth-name-memberp
                (fn-auth-cred-name (fn-ncfg-second done)) creds)
               (list :refused :duplicate-login))
              ((<= (nfix max-credentials) (len creds))
               (list :refused :too-many-credentials))
              (t (list :accepted
                       (fn-ncfg-reverse (cons (fn-ncfg-second done) creds))))))
            (t (list :accepted (fn-ncfg-reverse creds)))))))

(defun fn-native-auth-load (octets presentp requiredp protected-onlyp tls-availablep
                                   max-credentials)
  ; The host-called semantic subject.  A missing file is the existing empty
  ; credential registry.  Protected-only without a real TLS facility refuses
  ; the profile before any connection can be opened.
  (declare (xargs :guard t))
  (cond ((and protected-onlyp (not tls-availablep))
         (list :refused :protected-transport-unavailable))
        ((not presentp)
         (list :accepted
               (fn-auth-make-config (and requiredp t) (and protected-onlyp t)
                                    (and tls-availablep t) nil)))
        ((or (not (fn-ncfg-ascii-octetsp octets))
             (< (fn-native-auth-max-octets max-credentials) (len octets)))
         (list :refused :bounds-or-encoding))
        (t (let ((lines (fn-ncfg-lines octets)))
             (if (< (fn-native-auth-max-lines max-credentials)
                    (fn-native-auth-line-count octets))
                 (list :refused :bounds-or-encoding)
               (let ((parsed (fn-native-auth-parse-lines lines nil nil nil
                                                         max-credentials)))
                 (if (not (equal (fn-ncfg-first parsed) :accepted)) parsed
                   (let ((config
                          (fn-auth-make-config
                           (and requiredp t) (and protected-onlyp t)
                           (and tls-availablep t) (fn-ncfg-second parsed))))
                     (if (fn-auth-configp config) (list :accepted config)
                       (list :refused :credential-shape))))))))))

(defun fn-native-auth-result-status (result)
  (declare (xargs :guard t))
  (if (consp result) (fn-ncfg-first result) :refused))

(defun fn-native-auth-result-reason (result)
  (declare (xargs :guard t))
  (if (and (consp result) (consp (cdr result))
           (equal (fn-ncfg-first result) :refused))
      (fn-ncfg-second result) nil))

(defun fn-native-auth-result-config (result)
  (declare (xargs :guard t))
  (if (and (consp result) (consp (cdr result))
           (equal (fn-ncfg-first result) :accepted))
      (fn-ncfg-second result) (fn-auth-open-config)))

(defthm fn-native-auth-load-protected-without-tls-refuses
  (equal (fn-native-auth-load octets presentp requiredp t nil max-credentials)
         '(:refused :protected-transport-unavailable)))

(defthm fn-native-auth-load-accepted-is-config
  (implies (equal (fn-native-auth-result-status
                   (fn-native-auth-load octets presentp requiredp protected tls max-credentials))
                  :accepted)
           (fn-auth-configp
            (fn-native-auth-result-config
             (fn-native-auth-load octets presentp requiredp protected tls max-credentials))))
  ; The loader checks fn-auth-configp before it accepts; the parser, the
  ; line count and the octet bound are not needed (5.6 s -> 0.1 s).
  :hints (("Goal" :in-theory (disable fn-native-auth-parse-lines fn-native-auth-max-octets
                                      fn-native-auth-max-lines fn-native-auth-line-count
                                      fn-ncfg-lines fn-ncfg-ascii-octetsp))))

; Local projection fact: when the parser accepts, its model result carries the
; caller's three normalized policy observations exactly.  Host installation
; correspondence is a separate boundary and this theorem is not a registry
; event.
(defthm fn-native-auth-load-accepted-pins-policy
  (implies
   (equal (fn-native-auth-result-status
           (fn-native-auth-load octets presentp requiredp protected tls max-credentials))
          :accepted)
   (let ((config
          (fn-native-auth-result-config
           (fn-native-auth-load octets presentp requiredp protected tls max-credentials))))
     (and (equal (fn-auth-config-requiredp config) (and requiredp t))
          (equal (fn-auth-config-protected-onlyp config) (and protected t))
          (equal (fn-auth-config-tls-availablep config) (and tls t)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-native-auth-parse-lines fn-native-auth-max-octets
                                      fn-native-auth-max-lines fn-native-auth-line-count
                                      fn-ncfg-lines fn-ncfg-ascii-octetsp fn-auth-configp))))

(local
 (defthm fn-native-auth-len-of-reverse-aux
   (equal (len (fn-ncfg-reverse-aux xs acc)) (+ (len xs) (len acc)))))

; A refused finish carries its reason, a symbol, never a credential list.
(local
 (defthm fn-native-auth-finish-refusal-has-no-credentials
   (implies (equal (car (fn-native-auth-finish name fields)) :refused)
            (equal (len (cadr (fn-native-auth-finish name fields))) 0))
   :hints (("Goal" :in-theory (e/d (fn-native-auth-finish)
                                   (fn-native-auth-string-field fn-native-auth-bool-field
                                    fn-native-auth-hex fn-native-auth-assoc
                                    fn-auth-credp fn-auth-make-cred fn-authsec-verifier))))))

; KEYSTONE (D27, PRF-102: the credential count is refused exactly past the
; operator's bound).  The parser the host-called loader runs
; (`fn-native-auth-load', host/native-auth-host.lisp
; `fn-native-auth-host-load', called by host/native/auth.lisp
; `fnn-native-auth-install' with the store profile's `max-credentials')
; never accepts more than MAX-CREDENTIALS credentials, whatever lines it is
; given.  (A refusal's second element is its reason, a symbol, so the
; statement needs no acceptance hypothesis.)  (The loader
; calls it with no credentials collected, so the hypothesis on CREDS holds
; there for every bound, 0 included.)
(defthm fn-native-auth-parse-lines-within-the-operator-bound
  (implies (<= (len creds) (nfix max-credentials))
           (<= (len (fn-ncfg-second
                     (fn-native-auth-parse-lines lines name fields creds
                                                 max-credentials)))
               (nfix max-credentials)))
  :rule-classes nil
  :hints (("Goal" :induct (fn-native-auth-parse-lines lines name fields creds
                                                      max-credentials)
           :in-theory (e/d (fn-native-auth-parse-lines)
                           (fn-native-auth-finish fn-native-auth-table-name
                            fn-native-auth-field fn-native-auth-name-memberp
                            fn-native-auth-assoc fn-ncfg-trim)))))

; The same bound at the loader the host calls: the configuration the host
; installs (`fn-native-auth-result-config', an accepted file's or the open
; configuration of a refused one) holds at most MAX-CREDENTIALS credentials.
; It needs no hypothesis: a refusal installs no credential.
(defthm fn-native-auth-load-within-the-operator-bound
  (<= (len (fn-auth-config-creds
            (fn-native-auth-result-config
             (fn-native-auth-load octets presentp requiredp protected tls
                                  max-credentials))))
      (nfix max-credentials))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn-native-auth-parse-lines-within-the-operator-bound
                                   (lines (fn-ncfg-lines octets))
                                   (name nil) (fields nil) (creds nil)))
           :in-theory (e/d (fn-native-auth-load fn-native-auth-result-status
                            fn-native-auth-result-config fn-auth-open-config)
                           (fn-native-auth-parse-lines fn-ncfg-lines
                            fn-auth-configp fn-native-auth-line-count
                            fn-ncfg-ascii-octetsp)))))
