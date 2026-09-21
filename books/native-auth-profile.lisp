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

(defconst *fn-native-auth-max-octets* 65536)
(defconst *fn-native-auth-max-lines* 1024)
(defconst *fn-native-auth-max-credentials* 128)

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

(defun fn-native-auth-table-name (line)
  ; Exact canonical table syntax: [login."printable-token"].
  (declare (xargs :guard t))
  (let* ((trimmed (fn-ncfg-trim line))
         (prefix '(91 108 111 103 105 110 46 34)))
    (if (and (fn-native-auth-prefixp prefix trimmed)
             (fn-native-auth-last-two-p trimmed 34 93))
        (let ((name (fn-native-auth-butlast-two
                     (fn-native-auth-drop (len prefix) trimmed))))
          (if (and (consp name) (true-listp name)
                   (<= (len name) *fn-auth-max-name-octets*)
                   (fn-nntp-printable-tokenp name))
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

(defun fn-native-auth-parse-lines (lines name fields creds)
  (declare (xargs :guard t
                  :measure (acl2-count lines)))
  (if (consp lines)
      (let ((line (fn-ncfg-trim (car lines))))
        (cond
         ((or (null line) (equal (car line) 35))
          (fn-native-auth-parse-lines (cdr lines) name fields creds))
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
                        ((<= *fn-native-auth-max-credentials* (len next-creds))
                         (list :refused :too-many-credentials))
                        (t (fn-native-auth-parse-lines
                            (cdr lines) next-name nil next-creds))))))))
         (t
          (let ((field (fn-native-auth-field line)))
            (cond ((equal field :bad) (list :refused :field))
                  ((null name) (list :refused :field-before-table))
                  ((fn-native-auth-assoc (fn-ncfg-first field) fields)
                   (list :refused :duplicate-field))
                  (t (fn-native-auth-parse-lines
                      (cdr lines) name (cons field fields) creds)))))))
    (let ((done (fn-native-auth-finish name fields)))
      (cond ((equal (fn-ncfg-first done) :refused) done)
            ((equal (fn-ncfg-first done) :credential)
             (cond
              ((fn-native-auth-name-memberp
                (fn-auth-cred-name (fn-ncfg-second done)) creds)
               (list :refused :duplicate-login))
              ((<= *fn-native-auth-max-credentials* (len creds))
               (list :refused :too-many-credentials))
              (t (list :accepted
                       (fn-ncfg-reverse (cons (fn-ncfg-second done) creds))))))
            (t (list :accepted (fn-ncfg-reverse creds)))))))

(defun fn-native-auth-load (octets presentp requiredp protected-onlyp tls-availablep)
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
             (< *fn-native-auth-max-octets* (len octets)))
         (list :refused :bounds-or-encoding))
        (t (let ((lines (fn-ncfg-lines octets)))
             (if (< *fn-native-auth-max-lines* (len lines))
                 (list :refused :bounds-or-encoding)
               (let ((parsed (fn-native-auth-parse-lines lines nil nil nil)))
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
  (equal (fn-native-auth-load octets presentp requiredp t nil)
         '(:refused :protected-transport-unavailable)))

(defthm fn-native-auth-load-accepted-is-config
  (implies (equal (fn-native-auth-result-status
                   (fn-native-auth-load octets presentp requiredp protected tls))
                  :accepted)
           (fn-auth-configp
            (fn-native-auth-result-config
             (fn-native-auth-load octets presentp requiredp protected tls)))))

; Keystone for the startup boundary: when the parser accepts, the config the
; host installs carries the caller's three normalized policy observations
; exactly.  Raw Lisp cannot silently drop REQUIRED, enable TLS, or weaken
; PROTECTED-ONLY while transporting the credential file.
(defthm fn-native-auth-load-accepted-pins-policy
  (implies
   (equal (fn-native-auth-result-status
           (fn-native-auth-load octets presentp requiredp protected tls))
          :accepted)
   (let ((config
          (fn-native-auth-result-config
           (fn-native-auth-load octets presentp requiredp protected tls))))
     (and (equal (fn-auth-config-requiredp config) (and requiredp t))
          (equal (fn-auth-config-protected-onlyp config) (and protected t))
          (equal (fn-auth-config-tls-availablep config) (and tls t)))))
  :rule-classes nil)
