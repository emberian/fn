;;; Receiver primitive component tests; SBCL+the actual loaded libcrypto.
;;; No image, grant, backing issuer or application admission is exercised.
(require :sb-posix)
(unless (find-package "ACL2") (make-package "ACL2" :use '("COMMON-LISP")))
(handler-bind ((style-warning #'muffle-warning))
  (load "host/native/crypto.lisp")
  (load "host/native/tls.lisp")
  (load "host/native/bpsec-crypto.lisp"))
(in-package "ACL2")
(load "tests/fixtures/bpsec/nist-gcm-decrypt.lisp")
(defvar *fnn-bpsec-test-checks* 0)
(defun fnn-bpsec-test-check (p name)
  (incf *fnn-bpsec-test-checks*)
  (unless p (error "BPSec primitive check failed: ~a" name)))
(defun fnn-bpsec-test-hex (s)
  (let ((v (make-array (/ (length s) 2) :element-type '(unsigned-byte 8))))
    (dotimes (i (length v) v)
      (setf (aref v i) (parse-integer s :start (* i 2) :end (+ 2 (* i 2)) :radix 16)))))
(defun fnn-bpsec-test-feed (function handle bytes chunk)
  ;; TEST-ONLY chunk splitter. Production boundaries are selected by ACL2.
  (loop for at from 0 below (length bytes) by chunk do
    (fnn-bpsec-test-check
     (null (funcall function handle bytes at (min chunk (- (length bytes) at))))
     "update exposes no data")))
(defun fnn-bpsec-test-hmac (name digest key input expected)
  (dolist (chunk '(1 7 64))
    (let* ((descriptor (list :test-issued name chunk))
           (handle (fnn-bpsec-hmac-start descriptor digest key (max 64 (length key)))))
      (unwind-protect
           (progn
             (fnn-bpsec-test-feed #'fnn-bpsec-hmac-update handle input chunk)
             (let ((got (fnn-bpsec-hmac-final handle)))
               (fnn-bpsec-test-check (eq (first got) descriptor) "HMAC exact descriptor")
               (fnn-bpsec-test-check (eq (second got) :hmac-bytes) "HMAC is bytes, not verified")
               (fnn-bpsec-test-check (= (fourth got) (length expected)) name)
               (fnn-bpsec-test-check (equalp (subseq (third got) 0 (fourth got)) expected) name)
               (fnn-bpsec-cleanse (third got))))
        (fnn-bpsec-cancel handle)))))
(defun fnn-bpsec-test-gcm (name cipher key iv aad ciphertext tag expected)
  (dolist (chunk '(1 7 64))
    (let* ((descriptor (list :test-issued name chunk))
           (handle (fnn-bpsec-gcm-start descriptor cipher key iv 64))
           (outputs nil) (observed-windows nil)
           (original (symbol-function 'fnn-bpsec-%decrypt-update)))
      (unwind-protect
           (progn
             (fnn-bpsec-test-feed #'fnn-bpsec-gcm-aad handle aad chunk)
             ;; TEST-ONLY interception observes actual library output BEFORE
             ;; production cleanses it. No observer/callback exists in the
             ;; production module. It demonstrates literal decrypt bytes,
             ;; including speculative bytes on a failing authentication.
             (setf (symbol-function 'fnn-bpsec-%decrypt-update)
                   (lambda (ctx output written input count)
                     (let ((result (funcall original ctx output written input count)))
                       (unless (sb-alien:null-alien output)
                         (push (loop for i below (sb-alien:deref written)
                                     collect (sb-alien:deref output i)) outputs)
                         (push (fnn-bpsec-primitive-transient handle) observed-windows))
                       result)))
             (fnn-bpsec-test-feed #'fnn-bpsec-gcm-update handle ciphertext chunk)
             (setf (symbol-function 'fnn-bpsec-%decrypt-update) original)
             (fnn-bpsec-test-check (every (lambda (v) (every #'zerop v)) observed-windows)
                                  "every speculative window cleansed immediately")
             (fnn-bpsec-test-check (null (fnn-bpsec-primitive-transient handle)) "no whole plaintext RAM")
             (let ((got (fnn-bpsec-gcm-final handle tag)))
               (fnn-bpsec-test-check (eq (first got) descriptor) "GCM exact descriptor")
               (fnn-bpsec-test-check (null (fnn-bpsec-primitive-context handle)) "GCM final frees context")
               (fnn-bpsec-test-check (null (third got)) "GCM first pass publishes no plaintext")
               (if expected
                   (progn
                     (fnn-bpsec-test-check (eq (second got) :authenticated) name)
                     (fnn-bpsec-test-check
                      (equalp (coerce (apply #'append (nreverse outputs))
                                      '(simple-array (unsigned-byte 8) (*))) expected) name))
                 (fnn-bpsec-test-check (eq (second got) :bad-tag) name))))
        (setf (symbol-function 'fnn-bpsec-%decrypt-update) original)
        (fnn-bpsec-cancel handle)))))

;;; RFC4231 section4.2, Case1, independently cross-verified published bytes.
;;; Primitive-only short-key diagnostics, not normative BPSec key admission.
(let ((key (make-array 20 :element-type '(unsigned-byte 8) :initial-element 11))
      (input (fnn-bpsec-test-hex "4869205468657265")))
  (dolist (row '((:sha256 "b0344c61d8db38535ca8afceaf0bf12b881dc200c9833da726e9376c2e32cff7")
                 (:sha384 "afd03944d84895626b0825f4ab46907f15f9dadbe4101ec682aa034c7cebc59cfaea9ea9076ede7f4af152e8b2fa9cb6")
                 (:sha512 "87aa7cdea5ef619d4ff0b4241a1d6cb02379f4e2ce4ec2787ad0b30545e17cdedaa833b7d6b8a702038b274eaea3f4e4be9d914eeb61f1702e696c203a126854")))
    (fnn-bpsec-test-hmac "RFC4231 Case1" (first row) key input (fnn-bpsec-test-hex (second row)))))
;;; RFC4231 section4.7, long 131-byte key crosses both SHA block widths.
(let ((key (make-array 131 :element-type '(unsigned-byte 8) :initial-element 170))
      (input (fnn-bpsec-test-hex "54657374205573696e67204c6172676572205468616e20426c6f636b2d53697a65204b6579202d2048617368204b6579204669727374")))
  (dolist (row '((:sha256 "60e431591ee0b67f0d8a26aacbf5b77f8e0bc6213728c5140546040f0ee37f54")
                 (:sha384 "4ece084485813e9088d2c63a041bc5b44f9ef1012a2b588f3cd11f05033ac4c60c2ef6ab4030fe8296248df163f44952")
                 (:sha512 "80b24263c7c1a3ebb71493c1dd7be8b49b46d1f41b4aeec1121b013783f8f3526b56d037e05f2598bd0fd2215d6a1e5295e64f73f63f0aec8b915a985d786598")))
    (fnn-bpsec-test-hmac "RFC4231 Case6" (first row) key input (fnn-bpsec-test-hex (second row)))))
;;; RFC9173 Appendix A.1/A.3/A.4 exact frozen IPPT diagnostics. Short keys
;;; and A.3 primary bstr do NOT weaken normative key/canonical input rules.
(let ((key (fnn-bpsec-test-hex "1a2b1a2b1a2b1a2b1a2b1a2b1a2b1a2b")))
  (dolist (row
            '((:sha512 "005823526561647920746f2067656e657261746520612033322d62797465207061796c6f6164"
               "3bdc69b3a34a2b5d3a8554368bd1e808f606219d2a10a846eae3886ae4ecc83c4ee550fdfb1cc636b904e2f1a73e303dcd4b6ccece003e95e8164dcc89a156e1")
              (:sha256 "00581c88070000820282010282028202018202820201820018281a000f4240"
               "cac6ce8e4c5dae57988b757e49a6dd1431dc04763541b2845098265bc817241b")
              (:sha256 "004319012c" "3ed614c0d97f49b3633627779aa18a338d212bf3c92b97759d9739cd50725596")
              (:sha384 "0788070000820282010282028202018202820201820018281a000f42400101000b03005823526561647920746f2067656e657261746520612033322d62797465207061796c6f6164"
               "f75fe4c37f76f046165855bd5ff72fbfd4e3a64b4695c40e2b787da005ae819f0a2e30a2e8b325527de8aefb52e73d71")))
    (fnn-bpsec-test-hmac "RFC9173 diagnostic IPPT" (first row) key
                       (fnn-bpsec-test-hex (second row)) (fnn-bpsec-test-hex (third row)))))
;;; RFC9173 A.2/A.3 and A.4. Receiver diagnostics only; A.4 repeated key+IV
;;; must never be used as a production encryption recipe (erratum7002).
(dolist (row
          '((:aes128-gcm "71776572747975696f70617364666768" "00"
             "3a09c1e63fe23a7f66a59c7303837241e070b02619fc59c5214a22f08cd70795e73e9a"
             "efa4b5ac0108e3816c5606479801bc04"
             "526561647920746f2067656e657261746520612033322d62797465207061796c6f6164")
            (:aes256-gcm "71776572747975696f7061736466676871776572747975696f70617364666768"
             "0788070000820282010282028202018202820201820018281a000f42400101000c0201"
             "90eab6457593379298a8724e16e61f837488e127212b59ac91f8a86287b7d07630a122"
             "d2c51cb2481792dae8b21d848cede99b"
             "526561647920746f2067656e657261746520612033322d62797465207061796c6f6164")
            (:aes256-gcm "71776572747975696f7061736466676871776572747975696f70617364666768"
             "0788070000820282010282028202018202820201820018281a000f42400b03000c0201"
             "438ed6208eb1c1ffb94d952175167df0902902064a2983910c4fb2340790bf420a7d1921d5bf7c4721e02ab87a93ab1e0b75cf62e4948727c8b5dae46ed2af05439b88029191"
             "220ffc45c8a901999ecc60991dd78b29"
             "81010101820282020182820106820307818182015830f75fe4c37f76f046165855bd5ff72fbfd4e3a64b4695c40e2b787da005ae819f0a2e30a2e8b325527de8aefb52e73d71")))
  (let ((key (fnn-bpsec-test-hex (second row))) (iv (fnn-bpsec-test-hex "5477656c7665313231323132"))
        (aad (fnn-bpsec-test-hex (third row))) (ct (fnn-bpsec-test-hex (fourth row)))
        (tag (fnn-bpsec-test-hex (fifth row))) (pt (fnn-bpsec-test-hex (sixth row))))
    (fnn-bpsec-test-gcm "RFC9173 diagnostic GCM" (first row) key iv aad ct tag pt)
    (let ((bad (copy-seq tag)))
      (setf (aref bad 0) (logxor 1 (aref bad 0)))
      (fnn-bpsec-test-gcm "changed tag" (first row) key iv aad ct bad nil))
    (let ((bad (copy-seq aad)))
      (setf (aref bad 0) (logxor 1 (aref bad 0)))
      (fnn-bpsec-test-gcm "changed AAD" (first row) key iv bad ct tag nil))
    (fnn-bpsec-test-gcm "truncated ciphertext" (first row) key iv aad (subseq ct 1) tag nil)))
(dolist (row *fnn-bpsec-test-nist-gcm*)
  (destructuring-bind (name cipher key iv aad ct tag pt) row
    (fnn-bpsec-test-gcm name cipher (fnn-bpsec-test-hex key) (fnn-bpsec-test-hex iv)
                       (fnn-bpsec-test-hex aad) (fnn-bpsec-test-hex ct)
                       (fnn-bpsec-test-hex tag) (and pt (fnn-bpsec-test-hex pt)))))
;;; Negative facility/FFI/width/cancel paths are distinct from :bad-tag.
(defun fnn-bpsec-test-error (type thunk name)
  (let ((caught nil))
    (handler-case (funcall thunk)
      (error (condition) (setf caught condition)))
    (fnn-bpsec-test-check (typep caught type) name)))
(let ((key (fnn-bpsec-test-hex "71776572747975696f70617364666768"))
      (iv (fnn-bpsec-test-hex "5477656c7665313231323132"))
      (bytes (fnn-bpsec-test-hex "3a09c1e63fe23a7f66a59c7303837241")))
  (dolist (key-width '(0 15 17 31 33))
    (fnn-bpsec-test-error 'fnn-crypto-fault
      (lambda () (fnn-bpsec-gcm-start :issued :aes128-gcm
                  (make-array key-width :element-type '(unsigned-byte 8)) iv 64))
      "wrong physical key width is a fault, not bad-tag"))
  (dolist (iv-width '(0 7 17))
    (fnn-bpsec-test-error 'fnn-crypto-fault
      (lambda () (fnn-bpsec-gcm-start :issued :aes128-gcm key
                  (make-array iv-width :element-type '(unsigned-byte 8)) 64))
      "wrong physical IV width is a fault"))
  (dolist (tag-width '(0 15 17))
    (let ((handle (fnn-bpsec-gcm-start :issued :aes128-gcm key iv 64)))
      (fnn-bpsec-test-error 'fnn-crypto-fault
        (lambda () (fnn-bpsec-gcm-final handle
                    (make-array tag-width :element-type '(unsigned-byte 8))))
        "wrong physical tag width is a fault")
      (fnn-bpsec-test-check (null (fnn-bpsec-primitive-context handle)) "tag fault frees context")))
  (let ((handle (fnn-bpsec-gcm-start :issued :aes128-gcm key iv 64)))
    (fnn-bpsec-gcm-update handle bytes 0 (length bytes))
    (fnn-bpsec-cancel handle)
    (fnn-bpsec-cancel handle)
    (fnn-bpsec-test-check (null (fnn-bpsec-primitive-transient handle)) "cancel leaves no plaintext")
    (fnn-bpsec-test-check (null (fnn-bpsec-primitive-context handle)) "cancel frees context")
    (fnn-bpsec-test-error 'fnn-crypto-fault
      (lambda () (fnn-bpsec-gcm-update handle bytes 0 1)) "cancelled primitive cannot resume"))
  (let* ((handle (fnn-bpsec-gcm-start :issued :aes128-gcm key iv 64))
         (original (symbol-function 'fnn-bpsec-%decrypt-update))
         (observed nil))
    (unwind-protect
         (progn
           (setf (symbol-function 'fnn-bpsec-%decrypt-update)
                 (lambda (ctx out written input count)
                   (funcall original ctx out written input count)
                   (setf observed (fnn-bpsec-primitive-transient handle))
                   ;; Simulate a post-write FFI fault: speculative output exists.
                   0))
           (fnn-bpsec-test-error 'fnn-crypto-fault
             (lambda () (fnn-bpsec-gcm-update handle bytes 0 (length bytes))) "FFI failure is a fault")
           (fnn-bpsec-test-check (and observed (every #'zerop observed)) "FFI fault cleanses output")
           (fnn-bpsec-test-check (null (fnn-bpsec-primitive-context handle)) "FFI fault frees context"))
      (setf (symbol-function 'fnn-bpsec-%decrypt-update) original)
      (fnn-bpsec-cancel handle))))
(fnn-bpsec-test-error 'fnn-bpsec-unsupported
  (lambda () (fnn-bpsec-hmac-start :issued :sha1 (fnn-bpsec-test-hex "00") 64))
  "unsupported primitive stays unsupported")
(let ((saved *fnn-bpsec-required-symbols*))
  (unwind-protect
       (progn
         (setf *fnn-bpsec-required-symbols* '("fn_bps_missing_symbol_diagnostic"))
         (fnn-bpsec-test-error 'fnn-bpsec-unsupported
           (lambda () (fnn-bpsec-hmac-start :issued :sha1 (fnn-bpsec-test-hex "00") 64))
           "unsupported profile before facility lookup")
         (fnn-bpsec-test-error 'fnn-crypto-unavailable
           (lambda () (fnn-bpsec-hmac-start :issued :sha256 (fnn-bpsec-test-hex "00") 64))
           "missing primitive facility is unavailable, not bad-tag"))
    (setf *fnn-bpsec-required-symbols* saved)))
(dolist (row '((nil 0 0) (#(0) 0 1) (:not-bytes 0 1)))
  (let ((handle (fnn-bpsec-hmac-start :issued :sha256 (fnn-bpsec-test-hex "00") 64)))
    (fnn-bpsec-test-error 'fnn-crypto-fault
      (lambda () (apply #'fnn-bpsec-hmac-update handle row)) "invalid raw buffer faults")
    (fnn-bpsec-test-check (null (fnn-bpsec-primitive-context handle)) "raw buffer fault frees context")))
(let ((handle (fnn-bpsec-hmac-start :issued :sha256 (fnn-bpsec-test-hex "00") 1)))
  (fnn-bpsec-test-error 'fnn-crypto-fault
    (lambda () (fnn-bpsec-hmac-update handle (fnn-bpsec-test-hex "0000") 0 2))
    "per-call bound violation faults before primitive update")
  (fnn-bpsec-test-check (null (fnn-bpsec-primitive-context handle)) "bound fault closes context"))

;;; Changed/truncated HMAC input changes actual bytes; only core may compare.
(let* ((key (make-array 32 :element-type '(unsigned-byte 8) :initial-element 11))
       (input (fnn-bpsec-test-hex "4869205468657265"))
       (tags nil))
  (dolist (message (list input (fnn-bpsec-test-hex "4969205468657265") (subseq input 1)))
    (let ((handle (fnn-bpsec-hmac-start :same-issued :sha256 key 64)))
      (unwind-protect
           (progn
             (fnn-bpsec-test-feed #'fnn-bpsec-hmac-update handle message 1)
             (let ((got (fnn-bpsec-hmac-final handle)))
               (fnn-bpsec-test-check (eq (second got) :hmac-bytes) "changed HMAC is observation only")
               (push (subseq (third got) 0 (fourth got)) tags)
               (fnn-bpsec-cleanse (third got))))
        (fnn-bpsec-cancel handle))))
  (fnn-bpsec-test-check (and (not (equalp (first tags) (third tags)))
                          (not (equalp (second tags) (third tags))))
                      "changed/truncated HMAC does not equal original"))

;;; Nonlocal escape after an actual primitive write must also retire custody.
(let* ((key (fnn-bpsec-test-hex "71776572747975696f70617364666768"))
       (iv (fnn-bpsec-test-hex "5477656c7665313231323132"))
       (ct (fnn-bpsec-test-hex "3a09c1e63fe23a7f66a59c7303837241"))
       (handle (fnn-bpsec-gcm-start :issued :aes128-gcm key iv 64))
       (original (symbol-function 'fnn-bpsec-%decrypt-update))
       (window nil))
  (unwind-protect
       (progn
         (setf (symbol-function 'fnn-bpsec-%decrypt-update)
               (lambda (ctx out written input count)
                 (funcall original ctx out written input count)
                 (setf window (fnn-bpsec-primitive-transient handle))
                 (throw 'escaped :escaped)))
         (fnn-bpsec-test-check
          (eq (catch 'escaped (fnn-bpsec-gcm-update handle ct 0 (length ct))) :escaped)
          "actual post-write escape")
         (fnn-bpsec-test-check (and window (every #'zerop window)) "escape cleanses bounded window")
         (fnn-bpsec-test-check (null (fnn-bpsec-primitive-context handle)) "escape frees context"))
    (setf (symbol-function 'fnn-bpsec-%decrypt-update) original)
    (fnn-bpsec-cancel handle)))
;;; A negative primitive return WITH an error queue is a fault, not bad-tag.
(let* ((handle (fnn-bpsec-gcm-start :issued :aes128-gcm
                 (fnn-bpsec-test-hex "71776572747975696f70617364666768")
                 (fnn-bpsec-test-hex "5477656c7665313231323132") 64))
       (original (symbol-function 'fnn-bpsec-%decrypt-final))
       (queue (symbol-function 'fnn-%err-get-error))
       (stack (symbol-function 'fnn-tls-error-stack)))
  (unwind-protect
       (progn
         (setf (symbol-function 'fnn-bpsec-%decrypt-final) (lambda (&rest args) (declare (ignore args)) 0)
               (symbol-function 'fnn-%err-get-error) (lambda () 1234)
               (symbol-function 'fnn-tls-error-stack) (lambda () "injected primitive error"))
         (fnn-bpsec-test-error 'fnn-crypto-fault
           (lambda () (fnn-bpsec-gcm-final handle (make-array 16 :element-type '(unsigned-byte 8))))
           "queued-error final refusal is a fault")
         (fnn-bpsec-test-check (null (fnn-bpsec-primitive-context handle)) "final fault frees context"))
    (setf (symbol-function 'fnn-bpsec-%decrypt-final) original
          (symbol-function 'fnn-%err-get-error) queue
          (symbol-function 'fnn-tls-error-stack) stack)
    (fnn-bpsec-cancel handle)))

(format t "BPSec primitive vectors PASS checks=~d OpenSSL=~a pair=~s~%"
        *fnn-bpsec-test-checks* *fnn-tls-version* *fnn-tls-libraries*)
