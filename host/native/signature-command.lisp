;;; Supplied-key CLI for the selected D09 hybrid profile.
(in-package "ACL2")

(defun fnn-hsig-command-read-exact (path width label)
  (let ((octets (fnn-read-regular-bounded path width)))
    (unless (= (length octets) width)
      (error 'fnn-usage-error
             :message (format nil "~a must contain exactly ~d octets"
                              label width)))
    (fnn-octet-list octets)))

(defun fnn-hsig-command-sign-material (args)
  "Return the exact source, ordered public key set and both checked signatures."
  (destructuring-bind (principal-path ed-public-path ed-secret-path ml-public-path
                       ml-private-path source-path) args
    (let* ((principal
            (fnn-hsig-command-read-exact principal-path 32 "principal"))
           (ed-public
            (fnn-hsig-command-read-exact ed-public-path 32 "Ed25519 public key"))
           (ed-secret
            (fnn-hsig-command-read-exact ed-secret-path 64 "Ed25519 secret key"))
           (ml-public (coerce (fnn-hsig-ml-dsa-65-public-key ml-public-path)
                              'list))
           (source (fnn-octet-list
                    (fnn-read-regular-bounded source-path 32768)))
           (keys (list (cons :ed25519 ed-public)
                       (cons :ml-dsa-65 ml-public)))
           (preimage (fnn-core 'fn-hsig-host-preimage principal keys source)))
      (unless preimage
        (fnn-refuse "hybrid signing subject is outside the selected profile"))
      (let* ((ed-signature
              (fnn-hsig-ed25519-sign (fnn-octets ed-secret) preimage))
             (ml-signature
              (fnn-hsig-ml-dsa-65-sign ml-private-path preimage))
             (signatures
              (list (cons :ed25519 (fnn-octet-list ed-signature))
                    (cons :ml-dsa-65 (fnn-octet-list ml-signature)))))
        ;; Detect mismatched supplied private/public material before emitting
        ;; an unusable artifact.  ACL2 still owns the final conjunction.
        (unless (fnn-hsig-authorize-profile principal keys source signatures
                                            ml-public-path)
          (fnn-refuse "supplied keys do not produce the enrolled hybrid profile"))
        (values source principal keys signatures)))))

(defun fnn-command-hybrid-sign (args)
  "Sign exact source bytes with caller-supplied independent key material.
Output is two algorithm-tagged lowercase hexadecimal lines."
  (unless (= (length args) 6)
    (error 'fnn-usage-error
           :message
           "usage: fn hybrid-sign PRINCIPAL ED-PUBLIC ED-SECRET ML-PUBLIC-PEM ML-PRIVATE-PEM SOURCE"))
  (multiple-value-bind (source principal keys signatures)
      (fnn-hsig-command-sign-material args)
    (declare (ignore source principal keys))
    (fnn-out "ed25519 ~a" (fnn-hex (cdr (first signatures))))
    (fnn-out "ml-dsa-65 ~a" (fnn-hex (cdr (second signatures))))
    0))

(defun fnn-command-hybrid-sign-carrier (args)
  "Write an ACL2-rendered portable FN-Authorship article to a new file."
  (unless (= (length args) 7)
    (error 'fnn-usage-error
           :message
           "usage: fn hybrid-sign-carrier PRINCIPAL ED-PUBLIC ED-SECRET ML-PUBLIC-PEM ML-PRIVATE-PEM SOURCE OUTPUT"))
  (multiple-value-bind (source principal keys signatures)
      (fnn-hsig-command-sign-material (subseq args 0 6))
    (let* ((rendered (fnn-core 'fn-hsig-host-render-carrier
                               source principal keys signatures))
           (output (seventh args)))
      (unless (and (fnn-octet-list-p rendered) (consp rendered))
        (fnn-refuse "source is outside the portable FN-Authorship profile"))
      (unless (eq (first (fnn-hsig-verify-received-carrier rendered
                                                            (fourth args)))
                  :verified)
        (fnn-refuse "rendered FN-Authorship failed independent verification"))
      (with-open-file (stream output :direction :output
                              :element-type '(unsigned-byte 8)
                              :if-exists :error :if-does-not-exist :create)
        (write-sequence (fnn-octets rendered) stream))
      0)))

(defun fnn-command-hybrid-verify-carrier (args)
  "Check a received article's exact-source carrier with both native suites."
  (unless (= (length args) 2)
    (error 'fnn-usage-error
           :message "usage: fn hybrid-verify-carrier ARTICLE ML-PUBLIC-PEM"))
  (let* ((received (fnn-octet-list
                    (fnn-read-regular-bounded
                     (first args) (fnn-core 'fn-hsig-host-max-received-octets))))
         (result (fnn-hsig-verify-received-carrier received (second args))))
    (if (eq (first result) :verified)
        (progn (fnn-out "verified ~a" (fnn-hex (third result))) 0)
      (progn (fnn-out "unverified ~a" (second result)) 1))))

(defun fnn-command-hybrid-verify-source (args)
  "Export only an independently verified carrier's exact authored source.
The versioned line is a bounded portable-authorship result, never a Store
acceptance or historical-verdict statement."
  (unless (= (length args) 2)
    (error 'fnn-usage-error
           :message "usage: fn hybrid-verify-source ARTICLE ML-PUBLIC-PEM"))
  (let* ((received (fnn-octet-list
                    (fnn-read-regular-bounded
                     (first args) (fnn-core 'fn-hsig-host-max-received-octets))))
         (result (fnn-hsig-verify-received-carrier received (second args))))
    (if (not (eq (first result) :verified))
        (progn (fnn-out "unverified ~a" (second result)) 1)
      (let* ((source (second result))
             (principal (third result))
             (keys (fourth result))
             (source-id (fnn-core 'fn-hsig-host-authored-source-id source)))
        (unless (and (fnn-octet-list-p source)
                     (fnn-octet-list-p principal) (= (length principal) 32)
                     (fnn-octet-list-p source-id) (= (length source-id) 48)
                     (equal (caar keys) :ed25519)
                     (fnn-octet-list-p (cdar keys)) (= (length (cdar keys)) 32)
                     (equal (caadr keys) :ml-dsa-65)
                     (fnn-octet-list-p (cdadr keys))
                     (= (length (cdadr keys)) +fnn-hsig-ml-public-key-octets+))
          (fnn-fault "verified carrier has an invalid portable source projection"))
        (fnn-out "fn-portable-v1 ~a ~a ~a ~a ~a"
                 (fnn-hex principal) (fnn-hex source-id)
                 (fnn-hex (cdar keys)) (fnn-hex (cdadr keys))
                 (fnn-hex source))
        0))))

(defun fnn-command-topic-inspect-carrier (args)
  "Inspect exact authored FN-Topic metadata after checking the carrier.
A valid carrier does not establish topic anchoring or report admission."
  (unless (= (length args) 2)
    (error 'fnn-usage-error
           :message "usage: fn topic-inspect-carrier ARTICLE ML-PUBLIC-PEM"))
  (let* ((received (fnn-octet-list
                    (fnn-read-regular-bounded
                     (first args) (fnn-core 'fn-hsig-host-max-received-octets))))
         (carrier (fnn-hsig-verify-received-carrier received (second args))))
    (if (not (eq (first carrier) :verified))
        (progn (fnn-out "topic=unverified carrier=~a" (second carrier)) 1)
      (let ((projection (fnn-core 'fn-th-select-verified-source
                                  (second carrier) (third carrier)
                                  (fourth carrier))))
        (if (eq (first projection) :ok)
            (progn
              (fnn-out "topic=candidate carrier=authenticated kind=~(~a~) metadata=~s author-principal=~a author-keyset=~a binding=~(~a~) admission=unestablished"
                       (first (first (second projection)))
                       (first (second projection))
                       (fnn-hex (first (second (second projection))))
                       (fnn-hex (second (second (second projection))))
                       (third (second projection)))
              0)
          (progn (fnn-out "topic=unsupported carrier=authenticated reason=~a admission=unestablished"
                          (second projection)) 1))))))

(fnn-register-verb "topic-inspect-carrier"
                   (lambda (first rest)
                     (fnn-command-topic-inspect-carrier (cons first rest))))

(fnn-register-verb "hybrid-sign"
                   (lambda (first rest)
                     (fnn-command-hybrid-sign (cons first rest))))
(fnn-register-verb "hybrid-sign-carrier"
                   (lambda (first rest)
                     (fnn-command-hybrid-sign-carrier (cons first rest))))
(fnn-register-verb "hybrid-verify-carrier"
                   (lambda (first rest)
                     (fnn-command-hybrid-verify-carrier (cons first rest))))
(fnn-register-verb "hybrid-verify-source"
                   (lambda (first rest)
                     (fnn-command-hybrid-verify-source (cons first rest))))

(defun fnn-command-consumer-project (args)
  "Project exact poll output with ACL2. Supplied files alone do not prove Store provenance."
  (unless (= (length args) 2)
    (error 'fnn-usage-error
           :message "usage: fn consumer-project CURSOR.fncu ACCEPTED.fn-e"))
  (let* ((cursor (fnn-octet-list (fnn-read-regular-bounded (first args) 346)))
         (event (fnn-octet-list
                 (fnn-read-regular-bounded (second args) 196608)))
         (projected (fnn-core 'fn-cpj-project cursor event)))
    (unless (eq (first projected) :ok)
      (fnn-out "fn-consumer-project-refused-v1 ~(~a~)" (second projected))
      (return-from fnn-command-consumer-project 1))
    (destructuring-bind (tag scope sequence txid source-id msgid source
                         received verdict-principal verdict) projected
      (declare (ignore tag))
      (fnn-out "fn-consumer-project-v1 ~{~a~^ ~} ~d ~d ~a ~a ~a ~a ~a ~a"
               (append (mapcar #'fnn-hex (subseq scope 0 5))
                       (mapcar #'identity (subseq scope 5)))
               sequence txid (fnn-hex source-id) (fnn-hex msgid)
               (fnn-hex source) (fnn-hex received)
               (fnn-hex verdict-principal) (fnn-hex verdict))
      0)))

(fnn-register-verb "consumer-project"
                   (lambda (first rest)
                     (fnn-command-consumer-project (cons first rest))))
