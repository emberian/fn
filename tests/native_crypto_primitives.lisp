;;; Known-answer and negative vectors for host/native/crypto.lisp.

;; The production file is loaded into the ACL2 package by the saved image.
;; This component test intentionally needs only SBCL and libsodium.
(unless (find-package "ACL2") (make-package "ACL2" :use '("COMMON-LISP")))

(load "host/native/crypto.lisp")
(in-package "ACL2")

(defun fnn-crypto-test-hex (text)
  (let ((answer (make-array (/ (length text) 2)
                            :element-type '(unsigned-byte 8))))
    (dotimes (index (length answer) answer)
      (setf (aref answer index)
            (parse-integer text :start (* 2 index) :end (+ 2 (* 2 index))
                                :radix 16)))))

(defun fnn-crypto-test-check (truth description)
  (unless truth (error "native crypto test failed: ~a" description)))

;; RFC 8032 section 7.1, TEST 1 (empty message).
(let* ((public
         (fnn-crypto-test-hex
          "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a"))
       (signature
         (fnn-crypto-test-hex
          (concatenate
           'string
           "e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e06522490155"
           "5fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b")))
       (empty (make-array 0 :element-type '(unsigned-byte 8))))
  (fnn-crypto-test-check
   (eq (fnn-crypto-ed25519-observe public empty signature) :verified)
   "RFC 8032 valid signature")
  (let ((tampered (copy-seq signature)))
    (setf (aref tampered 0) (logxor 1 (aref tampered 0)))
    (fnn-crypto-test-check
     (eq (fnn-crypto-ed25519-observe public empty tampered) :refused)
     "tampered signature is refused"))
  (fnn-crypto-test-check
   (eq (fnn-crypto-ed25519-observe (subseq public 1) empty signature) :refused)
   "wrong public-key width is refused")
  (fnn-crypto-test-check
   (eq (fnn-crypto-ed25519-observe public empty (subseq signature 1)) :refused)
   "wrong signature width is refused")
  (fnn-crypto-test-check
   (eq (fnn-crypto-ed25519-observe public "not octets" signature) :fault)
   "malformed message is a host fault, not a signature refusal")
  (fnn-crypto-test-check
   (eq (fnn-crypto-ed25519-observe
        public (make-array 4097 :element-type '(unsigned-byte 8)) signature)
       :fault)
   "oversized message is a host fault before primitive entry"))

;; FIPS 180-4 SHA-512 example for the ASCII string "abc".
(fnn-crypto-test-check
 (equalp
  (fnn-crypto-sha512 #(97 98 99))
  (fnn-crypto-test-hex
   (concatenate
    'string
    "ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a"
    "2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f")))
 "FIPS SHA-512 abc")

;; The anchor helper owns only the leaf primitive and its fixed profile prefix.
(fnn-crypto-test-check
 (= (length (fnn-crypto-anchor-leaf (make-array 32 :initial-element 0))) 64)
 "Roughtime leaf width")

;; A captured one-nonce response from roughtime.int08h.com (2026-09-19).
;; These are primitive vectors only: production must obtain the two signed
;; subjects from ACL2, not copy this assembly into the host.
(let* ((key
         (fnn-crypto-test-hex
          "016e6e0284d24c37c6e4d7d8d5b4e1d3c1949ceaa545bf875616c9dce0c9bec1"))
       (delegate
         (fnn-crypto-test-hex
          "70e193129ae59d61a2ab6af599a245d654e7ec9542324af3ea3bdf6fcfd623b9"))
       (dele
         (fnn-crypto-test-hex
          (concatenate
           'string
           "0300000020000000280000005055424b4d494e544d415854"
           "70e193129ae59d61a2ab6af599a245d654e7ec9542324af3ea3bdf6fcfd623b9"
           "0000000000000000ffffffffffffffff")))
       (delegation-context
         (fnn-crypto-test-hex
          "526f75676854696d652076312064656c65676174696f6e207369676e61747572652d2d00"))
       (delegation-signature
         (fnn-crypto-test-hex
          (concatenate
           'string
           "57e121e0f150dce10196855752731c2187f475f76ac99acf98e2dde127a9a1721"
           "71373898674f68a349c360b3d075c90af58d8b62d2f0990618a9170085dcf0f")))
       (srep
         (fnn-crypto-test-hex
          (concatenate
           'string
           "03000000040000000c000000524144494d494450524f4f54404b4c00e1e2bf39d75b0600"
           "fe528747bdbb53ab0d04b5e62a7bf2e5c6db7189ce27c618be0f101e3bfeef32e9011c2d"
           "b03d4c53666c025323fb79521c1ca0f896972c95d478b5fc10aae47e")))
       (response-context
         (fnn-crypto-test-hex
          "526f75676854696d6520763120726573706f6e7365207369676e617475726500"))
       (signature
         (fnn-crypto-test-hex
          (concatenate
           'string
           "a7b00df8dc73597f85d9b95ffa3dd6d66f63b38af7e3bfabe79f776f13ded22a"
           "9b7bea3a201121071528529693e0e0e086e5d8ac2a600b9143aeca8cc1660503")))
       (nonce
         (fnn-crypto-test-hex
          "95b3b3f850df64275c8448d870a859fb1e4e690ac6b44e16d83c12d78aa3a2c1"))
       (root
         (fnn-crypto-test-hex
          (concatenate
           'string
           "fe528747bdbb53ab0d04b5e62a7bf2e5c6db7189ce27c618be0f101e3bfeef32"
           "e9011c2db03d4c53666c025323fb79521c1ca0f896972c95d478b5fc10aae47e"))))
  (fnn-crypto-test-check
   (fnn-crypto-ed25519-verify
    key (concatenate 'vector delegation-context dele) delegation-signature)
   "captured Roughtime delegation signature")
  (fnn-crypto-test-check
   (fnn-crypto-ed25519-verify
    delegate (concatenate 'vector response-context srep) signature)
   "captured Roughtime response signature")
  (fnn-crypto-test-check (equalp (fnn-crypto-anchor-leaf nonce) root)
                         "captured one-nonce root"))

(format t "FN_NATIVE_CRYPTO_TEST passed library=~s version=~s~%"
        *fnn-crypto-library* *fnn-crypto-version*)
