;;; Supplied-key CLI for the selected D09 hybrid profile.
(in-package "ACL2")

(defun fnn-hsig-command-read-exact (path width label)
  (let ((octets (fnn-read-regular-bounded path width)))
    (unless (= (length octets) width)
      (error 'fnn-usage-error
             :message (format nil "~a must contain exactly ~d octets"
                              label width)))
    (fnn-octet-list octets)))

(defun fnn-command-hybrid-sign (args)
  "Sign exact source bytes with caller-supplied independent key material.
Output is two algorithm-tagged lowercase hexadecimal lines."
  (unless (= (length args) 6)
    (error 'fnn-usage-error
           :message
           "usage: fn hybrid-sign PRINCIPAL ED-PUBLIC ED-SECRET ML-PUBLIC-PEM ML-PRIVATE-PEM SOURCE"))
  (destructuring-bind
      (principal-path ed-public-path ed-secret-path ml-public-path
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
        (fnn-out "ed25519 ~a" (fnn-hex ed-signature))
        (fnn-out "ml-dsa-65 ~a" (fnn-hex ml-signature))
        0))))

(fnn-register-verb "hybrid-sign" #'fnn-command-hybrid-sign)

