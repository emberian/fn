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

(let* ((private (or (sb-ext:posix-getenv "FN_TEST_ML_DSA_PRIVATE")
                    (error "FN_TEST_ML_DSA_PRIVATE is required")))
       (public (or (sb-ext:posix-getenv "FN_TEST_ML_DSA_PUBLIC")
                   (error "FN_TEST_ML_DSA_PUBLIC is required")))
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
       (ml-signature (fnn-hsig-ml-dsa-65-sign private message))
       (signatures (list (cons :ed25519 ed-signature)
                         (cons :ml-dsa-65 ml-signature))))
  (fnn-hsig-check (fnn-crypto-ed25519-verify ed-public message ed-signature)
                  "libsodium Ed25519 sign/verify")
  (fnn-hsig-check (fnn-hsig-ml-dsa-65-verify public message ml-signature)
                  "OpenSSL ML-DSA-65 sign/verify")
  (fnn-hsig-check (equal (fnn-hsig-observe ed-public public message signatures)
                         '(:verified :verified))
                  "both observations remain distinct")
  (let ((bad (copy-seq ml-signature)))
    (setf (aref bad 0) (logxor 1 (aref bad 0)))
    (fnn-hsig-check (not (fnn-hsig-ml-dsa-65-verify public message bad))
                    "one bad ML-DSA component is refused"))
  (fnn-hsig-check
   (not (equal (fnn-hsig-observe ed-public public message
                                 (list (cons :ed25519 ed-signature)))
               '(:verified :verified)))
   "stripping ML-DSA never yields two verified observations"))

(format t "FN_NATIVE_HYBRID_SIGNATURE_TEST passed openssl=~s~%"
        *fnn-hsig-openssl-version*)
