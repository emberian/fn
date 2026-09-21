(in-package "ACL2")

(defun fnn-hybrid-control-enroll (service request)
  (destructuring-bind (tag keyring-generation principal ed-key ml-key) request
    (declare (ignore tag))
    (fnn-owner-serialized
     service nil
     (lambda ()
       (destructuring-bind (sequence txid generation)
           (fnn-owner-core 'fn-owner-next-store-coordinates)
         (let* ((keys (list (cons :ed25519 ed-key) (cons :ml-dsa-65 ml-key)))
                (event (fnn-core 'fn-hsig-host-keyring-event
                                 sequence txid generation keyring-generation
                                 principal keys)))
           (if event
               (progn (fnn-owner-identity-commit service event) :accepted)
             :refused)))))))

(defun fnn-hybrid-control-author (service request)
  (destructuring-bind
      (tag keyring-generation source ed-signature ml-signature ml-path) request
    (declare (ignore tag))
    (fnn-owner-serialized
     service nil
     (lambda ()
       (let* ((snapshot
               (fnn-owner-core 'fn-owner-keyring-snapshot keyring-generation))
              (enrollment
               (and snapshot
                    (fnn-core 'fn-hsig-host-keyring-snapshot-value snapshot))))
         (unless (and snapshot enrollment) (return-from fnn-hybrid-control-author :refused))
         (let* ((fields (fnn-core 'fn-hsig-host-authored-source-fields source)))
           (unless fields (return-from fnn-hybrid-control-author :refused))
           (let* ((msgid (fnn-octets (fnn-string-octets (first fields))))
                (groups (mapcar (lambda (g) (fnn-octets (fnn-string-octets g)))
                                (second fields)))
                (principal (first enrollment))
                (keys (second enrollment))
                (signatures
                 (list (cons :ed25519 ed-signature)
                       (cons :ml-dsa-65 ml-signature)))
                (coordinates (fnn-owner-core 'fn-owner-next-store-coordinates))
                (charge (fnn-charge (length source)))
                (metadata (multiple-value-list (fnn-metadata msgid (fnn-octets source))))
                (obligation (first metadata))
                (subject (second metadata))
                (release (third metadata))
                (event
                 (fnn-hsig-authorized-submission-event
                  coordinates keyring-generation
                  (fnn-core 'fn-hsig-host-keyring-snapshot-octets snapshot)
                  (fn-record-octets-string (fnn-octet-list msgid)) source
                  (mapcar (lambda (g) (fn-record-octets-string (fnn-octet-list g))) groups)
                  (fn-record-octets-string (fnn-octet-list obligation))
                  (fn-record-octets-string (fnn-octet-list subject))
                  (fn-record-octets-string (fnn-octet-list release)) charge
                  principal keys signatures (fn-record-octets-string ml-path))))
           (if event
               (let* ((evidence (fnn-octets (fnn-owner-core 'fn-owner-prov-post)))
                      (generation
                       (fnn-nat (fnn-owner-core 'fn-owner-config-generation)))
                      (txid (second coordinates)))
                 (fnn-owner-complete-bound-submission
                  service
                  (lambda ()
                    (fnn-owner-action 'fn-owner-control-submit
                                      (fnn-octet-list msgid)
                                      (mapcar #'fnn-octet-list groups) source))
                  msgid (fnn-octets source) groups evidence generation txid
                  (lambda ()
                    (handler-case (fnn-owner-identity-commit service event)
                      (fnn-store-indeterminate () :uncertain)
                      (fnn-store-fault (e) (error e))
                      (fnn-store-error () :refused)
                      (fnn-os-error () :refused)))))
             :refused))))))))

(defun fnn-hybrid-control-handle (service frame)
  (when (typep frame 'fnn-octets)
    (let* ((octets (fnn-octet-list frame))
           (enroll (fnn-core 'fn-native-hybrid-control-host-enroll-decode octets))
           (author (fnn-core 'fn-native-hybrid-control-host-author-decode octets)))
      (cond (enroll (fnn-hybrid-control-enroll service enroll))
            (author (fnn-hybrid-control-author service author))
            (t nil)))))

(setq *fnn-hybrid-control-handler* #'fnn-hybrid-control-handle)

(defun fnn-hybrid-control-send (control-path request)
  (unless (fnn-octet-list-p request) (fnn-fault "ACL2 refused hybrid control request"))
  (let ((socket nil) (stage :before-submission))
    (unwind-protect
         (handler-case
             (progn
               (setq socket (fnn-control-connect control-path))
               (let ((fd (fnn-socket-fd socket)))
                 (setq stage :after-submission)
                 (fnn-send-all fd (fnn-octets request) +fnn-control-io-seconds+)
                 (sb-bsd-sockets:socket-shutdown socket :direction :output)
                 (let* ((reply (fnn-control-read-frame
                                socket (fnn-core 'fn-native-control-host-max-frame)))
                        (status (and (typep reply 'fnn-octets)
                                     (fnn-core 'fn-native-control-host-reply-decode
                                               (fnn-octet-list reply)))))
                   (if (member status '(:accepted :duplicate :refused :busy
                                        :uncertain :fault)) status
                     (fnn-control-transport-outcome stage)))))
           (error () (fnn-control-transport-outcome stage)))
      (when socket (fnn-socket-shut socket)))))

(defun fnn-command-hybrid-enroll (args)
  (unless (= (length args) 5)
    (error 'fnn-usage-error
           :message "hybrid-enroll CONTROL GENERATION PRINCIPAL ED-PUBLIC ML-PUBLIC-PEM"))
  (destructuring-bind (control generation principal-path ed-path ml-path) args
    (let* ((generation-value
            (fnn-core 'fn-native-hybrid-control-host-uint32 generation))
           (request
           (fnn-core
            'fn-native-hybrid-control-host-enroll-encode
            generation-value
            (fnn-hsig-command-read-exact principal-path 32 "principal")
            (fnn-hsig-command-read-exact ed-path 32 "Ed25519 public key")
            (coerce (fnn-hsig-ml-dsa-65-public-key ml-path) 'list))))
      (fnn-core 'fn-native-control-host-status-exit-code
                (fnn-hybrid-control-send control request)))))

(defun fnn-command-hybrid-author (args)
  (unless (= (length args) 6)
    (error 'fnn-usage-error
           :message "hybrid-author CONTROL GENERATION SOURCE ED-SIGNATURE ML-SIGNATURE ML-PUBLIC-PEM"))
  (destructuring-bind
      (control generation source-path ed-path ml-path ml-public) args
    (let* ((generation-value
            (fnn-core 'fn-native-hybrid-control-host-uint32 generation))
           (request
           (fnn-core
            'fn-native-hybrid-control-host-author-encode
            generation-value
            (fnn-octet-list (fnn-read-regular-bounded source-path 32768))
            (fnn-hsig-command-read-exact ed-path 64 "Ed25519 signature")
            (fnn-hsig-command-read-exact ml-path 3309 "ML-DSA-65 signature")
            (fnn-octet-list (fnn-string-octets ml-public)))))
      (fnn-core 'fn-native-control-host-status-exit-code
                (fnn-hybrid-control-send control request)))))

(fnn-register-verb "hybrid-enroll"
                   (lambda (first rest)
                     (fnn-command-hybrid-enroll (cons first rest))))
(fnn-register-verb "hybrid-author"
                   (lambda (first rest)
                     (fnn-command-hybrid-author (cons first rest))))
