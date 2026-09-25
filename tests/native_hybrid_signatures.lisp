;;; Component interoperability test for host/native/signatures.lisp.
(unless (find-package "ACL2") (make-package "ACL2" :use '("COMMON-LISP")))
(load "host/native/crypto.lisp")
(load "host/native/tls.lisp")
(load "host/native/signatures.lisp")
(in-package "ACL2")

(defun fnn-hsig-test-hex (text)
  (let ((answer (make-array (/ (length text) 2)
                            :element-type '(unsigned-byte 8))))
    (dotimes (i (length answer) answer)
      (setf (aref answer i)
            (parse-integer text :start (* i 2) :end (+ (* i 2) 2) :radix 16)))))

(defun fnn-hsig-check (value description)
  (unless value (error "hybrid signature test failed: ~a" description)))

(defvar *fnn-hsig-test-preimage* nil)
(defvar *fnn-hsig-test-authorize-args* nil)
(defvar *fnn-hsig-test-carrier-plan* nil)
(defun fnn-core (name &rest args)
  "The production call convention: one scalar value, unlike FNN-CALL's list."
  (case name
    (fn-hsig-host-preimage *fnn-hsig-test-preimage*)
    ;; The production value: host/hybrid-signature-host.lisp over the v2
    ;; layout (2054 fixed octets) and the u32 source width.
    (fn-hsig-host-max-preimage-octets (+ 2054 4294967295))
    (fn-hsig-host-received-carrier-plan *fnn-hsig-test-carrier-plan*)
    (fn-hsig-host-authorize
     (setq *fnn-hsig-test-authorize-args* args)
     (and (equalp (fifth args) (cdr (second (second args))))
          (eq (sixth args) :verified) (eq (seventh args) :verified)))
    (otherwise (error "unexpected core call ~s" name))))

(let* ((private (or (sb-ext:posix-getenv "FN_TEST_ML_DSA_PRIVATE")
                    (error "FN_TEST_ML_DSA_PRIVATE is required")))
       (public (or (sb-ext:posix-getenv "FN_TEST_ML_DSA_PUBLIC")
                   (error "FN_TEST_ML_DSA_PUBLIC is required")))
       (private-b (or (sb-ext:posix-getenv "FN_TEST_ML_DSA_PRIVATE_B")
                      (error "FN_TEST_ML_DSA_PRIVATE_B is required")))
       (public-b (or (sb-ext:posix-getenv "FN_TEST_ML_DSA_PUBLIC_B")
                     (error "FN_TEST_ML_DSA_PUBLIC_B is required")))
       (message #(102 110 45 116 101 115 116 45 112 114 101 105 109 97 103 101))
       ;; RFC 8032 test 1 seed || public key, libsodium's 64-octet secret form.
       (ed-public (fnn-hsig-test-hex
                   "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a"))
       (ed-secret (fnn-hsig-test-hex
                   (concatenate
                    'string
                    "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60"
                    "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a")))
       (ed-signature (fnn-hsig-ed25519-sign ed-secret message))
       (ml-public (fnn-hsig-ml-dsa-65-public-key public))
       (ml-signature (fnn-hsig-ml-dsa-65-sign private message))
       (ml-signature-b (fnn-hsig-ml-dsa-65-sign private-b message))
       (signatures (list (cons :ed25519 ed-signature)
                         (cons :ml-dsa-65 ml-signature))))
  (fnn-hsig-check (fnn-crypto-ed25519-verify ed-public message ed-signature)
                  "libsodium Ed25519 sign/verify")
  (let* ((large-message
          ;; A 200 KiB v2 source's preimage: over the old 34820-octet cap.
          (make-array (+ 2054 (* 200 1024))
                      :element-type '(unsigned-byte 8) :initial-element 42))
         (large-signature (fnn-hsig-ed25519-sign ed-secret large-message)))
    (fnn-hsig-check
     (eq (fnn-crypto-ed25519-observe
          ed-public large-message large-signature
          (fnn-hsig-max-message-octets))
         :verified)
     "hybrid Ed25519 observation accepts a 200 KiB v2 preimage"))
  (fnn-hsig-check (fnn-hsig-ml-dsa-65-verify public message ml-signature)
                  "OpenSSL ML-DSA-65 sign/verify")
  (multiple-value-bind (verified observed)
      (fnn-hsig-ml-dsa-65-verify-raw ml-public message ml-signature)
    (fnn-hsig-check (and verified (equalp observed ml-public))
                    "receiver imports exact enrolled raw ML public key"))
  (multiple-value-bind (verified observed)
      (fnn-hsig-ml-dsa-65-verify-raw
       (fnn-hsig-ml-dsa-65-public-key public-b) message ml-signature)
    (fnn-hsig-check (and (not verified) (not (equalp observed ml-public)))
                    "receiver refuses signature under substituted raw key"))
  (let ((observations (fnn-hsig-observe-raw
                       ed-public ml-public message signatures)))
    (fnn-hsig-check
     (and (eq (first observations) :verified)
          (eq (first (second observations)) :verified)
          (equalp (second (second observations)) ml-public))
     "receiver keeps both independent raw-key observations"))
  (fnn-hsig-check
   (let ((observations (fnn-hsig-observe ed-public public message signatures)))
     (and (eq (first observations) :verified)
          (eq (first (second observations)) :verified)
          (equalp (second (second observations)) ml-public)))
                  "both observations remain distinct")
  (let ((bad (copy-seq ml-signature)))
    (setf (aref bad 0) (logxor 1 (aref bad 0)))
    (fnn-hsig-check (not (fnn-hsig-ml-dsa-65-verify public message bad))
                    "one bad ML-DSA component is refused"))
  (fnn-hsig-check
   (let ((observations (fnn-hsig-observe
                        ed-public public message
                        (list (cons :ed25519 ed-signature)))))
     (not (and (eq (first observations) :verified)
               (consp (second observations))
               (eq (first (second observations)) :verified))))
   "stripping ML-DSA never yields two verified observations")

  ;; Exercise the production entry, including its scalar FNN-CORE convention,
  ;; primitive calls, observed-key handoff and final ACL2 authorization call.
  (setq *fnn-hsig-test-preimage* message)
  (let ((keys (list (cons :ed25519 ed-public)
                    (cons :ml-dsa-65 (coerce ml-public 'list)))))
    (fnn-hsig-check
     (fnn-hsig-authorize-profile '(1 2 3) keys '(4 5) signatures public)
     "production authorization entry")
    (fnn-hsig-check (equal (fifth *fnn-hsig-test-authorize-args*)
                           (coerce ml-public 'list))
                    "production entry passes observed ML key to ACL2")
    (fnn-hsig-check
     (not (fnn-hsig-authorize-profile
           '(1 2 3) keys '(4 5)
           (list (cons :ed25519 ed-signature)
                 (cons :ml-dsa-65 ml-signature-b))
           public-b))
     "valid Ed25519 plus valid ML-DSA under substituted key B is rejected"))

  ;; The new received-carrier entry consumes ACL2's plan, performs both real
  ;; primitive checks, then asks ACL2 for the final conjunction.
  (let ((keys (list (cons :ed25519 ed-public)
                    (cons :ml-dsa-65 (coerce ml-public 'list)))))
    (setq *fnn-hsig-test-carrier-plan*
          (list :ok (list '(4 5) (list '(1 2 3) keys signatures))))
    (fnn-hsig-check
     (equal (fnn-hsig-verify-received-carrier '(7 8) public)
            (list :verified '(4 5) '(1 2 3) keys))
     "received carrier uses real dual verification")
    (setq *fnn-hsig-test-carrier-plan*
          (list :ok
                (list '(4 5) (list '(1 2 3) keys
                                    (list (cons :ed25519 ed-signature)
                                          (cons :ml-dsa-65 ml-signature-b))))))
    (fnn-hsig-check
     (equal (fnn-hsig-verify-received-carrier '(7 8) public-b)
            '(:unverified :signature (7 8)))
     "substituted key cannot authorize received carrier")
    (setq *fnn-hsig-test-carrier-plan* '(:unverified :carrier (7 8)))
    (fnn-hsig-check
     (equal (fnn-hsig-verify-received-carrier '(7 8) public)
            '(:unverified :carrier (7 8)))
     "malformed carrier remains unverified"))

  (handler-case
      (progn (fnn-hsig-ml-dsa-65-public-key
              (concatenate 'string public (string (code-char 0)) "suffix"))
             (error "NUL key path was accepted"))
    (fnn-hsig-fault () nil))
  (let ((pinned (copy-tree *fnn-tls-pinned-libraries*)))
    (fnn-tls-reset)
    (fnn-hsig-check (equal pinned *fnn-tls-pinned-libraries*)
                    "TLS reset preserves the selected library identity")
    (fnn-tls-initialize)
    (fnn-hsig-check (equal pinned *fnn-tls-libraries*)
                    "TLS restart revalidates the same library pair"))
  )

(format t "FN_NATIVE_HYBRID_SIGNATURE_TEST passed openssl=~s~%"
        *fnn-hsig-openssl-version*)
