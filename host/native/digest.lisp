;;; Native SHA-256 for the served images (lane digest-native, 2026-09-27).
;;;
;;; This raw-Lisp file is part of HST-004's trust boundary, beside
;;; host/native/crypto.lisp (libsodium) and host/native/tls.lisp (the system
;;; libcrypto/libssl pair).  It decides nothing.  ACL2 still decides which
;;; octets are digested, what a digest is compared with and what follows from
;;; the comparison; this file only computes FIPS 180-4 SHA-256 of octets ACL2
;;; handed over, faster.
;;;
;;; What it replaces.  `books/crypto-attach.lisp' attaches the constrained
;;; digests `fn-digest' and `fn-frame-digest' to `fn-sha256-stobj', and
;;; `books/frame-digest-buffer.lisp' attaches `fn-frame-digest-buffer' to
;;; `fn-sha256-of-prefixed-buffer-any'.  Those ACL2 functions are proved equal
;;; to the list model `fn-sha256' (`fn-sha256-stobj-is-sha256',
;;; `fn-sha256-of-prefixed-buffer-is-sha256') and run at about 70 MB/s.  In
;;; the saved image, after this file's start-up check passes, the raw Lisp
;;; definitions of the three executable entries
;;;
;;;   fn-sha256-stobj               (any object, read as an octet list)
;;;   fn-sha256-of-string           (a string's character codes)
;;;   fn-sha256-of-prefixed-buffer  (a list prefix, then an octet buffer)
;;;
;;; are replaced by calls to the libcrypto EVP SHA-256 of the pair tls.lisp
;;; pinned (OpenSSL 3.0+ or LibreSSL 3+; SHA-NI or the ARMv8 SHA2
;;; instructions where the CPU has them: 1.7 GB/s on hbox, 1.1-1.5 GB/s on
;;; an M2).  libsodium's crypto_hash_sha256 was measured and rejected: it is
;;; portable C (317 MB/s on hbox, 123 MB/s on the M2), no faster than the
;;; ACL2 stobj code at the record sizes fn digests.  Every caller -- the
;;; attachment dispatch, `fn-sha256-of-prefixed-buffer-any',
;;; `fn-shb-subject-id' -- reaches the replacement through the symbol, so no
;;; book changes.  The ACL2 definitions stay: they are the logic's subject,
;;; the reference the start-up check compares against, and the fallback for
;;; any argument outside the fast domain.
;;;
;;; The fast domain.  `fn-sha256-stobj' is total: it digests
;;; `(fn-sha256-fix-octets m)', which stops at the first non-cons tail and
;;; reduces a non-octet element.  The native path digests the conses' cars
;;; while every one is an (unsigned-byte 8); an improper tail ends the list
;;; exactly as the fixer does; at the first non-octet element it abandons
;;; the native digest and calls the ACL2 reference on the whole argument.
;;; So on every object the answer is the reference's answer, provided the
;;; primitive computes SHA-256: that proviso is the assumption A-CRYPTO-NATIVE
;;; (specs/failures.md), qualified by the known-answer vectors and the
;;; differential below at every start, and by tests/native_digest.lisp
;;; (100k inputs, every length 0..4200, random lengths to 1 MiB) per image.
;;;
;;; RFC 8315 Cancel-Lock and HKDF-SHA256 are untouched: they are separate
;;; ACL2 computations (books/cancel-lock*.lisp, books/hkdf*.lisp) and keep
;;; exactly their interop behaviour.
;;;
;;; Faults.  A libcrypto call that reports failure signals `fnn-digest-fault':
;;; the caller sees a host fault (uncertain), never a digest.  A start whose
;;; check fails refuses (io.lisp fnn-native-startup, exit 5), because a
;;; primitive that disagrees with the reference on a known answer is a
;;; broken library, not a slower one.

(in-package "ACL2")

(define-condition fnn-digest-error (error)
  ((detail :initarg :detail :reader fnn-digest-error-detail))
  (:report (lambda (condition stream)
             (format stream "native digest: ~a"
                     (fnn-digest-error-detail condition)))))

(define-condition fnn-digest-unavailable (fnn-digest-error) ())
(define-condition fnn-digest-fault (fnn-digest-error) ())

(defconstant +fnn-digest-octets+ 32)
;; The stack chunk a list or string is copied through: a work quantum per
;; foreign call, not a bound on the message (a message of any length is
;; digested chunk by chunk).
(defconstant +fnn-digest-chunk-octets+ 16384)

(sb-alien:define-alien-routine ("EVP_sha256" fnn-%evp-sha256)
    sb-sys:system-area-pointer)
(sb-alien:define-alien-routine ("EVP_MD_CTX_new" fnn-%evp-md-ctx-new)
    sb-sys:system-area-pointer)
(sb-alien:define-alien-routine ("EVP_MD_CTX_free" fnn-%evp-md-ctx-free)
    sb-alien:void
  (ctx sb-sys:system-area-pointer))
(sb-alien:define-alien-routine ("EVP_DigestInit_ex" fnn-%evp-digest-init-ex)
    sb-alien:int
  (ctx sb-sys:system-area-pointer)
  (type sb-sys:system-area-pointer)
  (engine sb-sys:system-area-pointer))
(sb-alien:define-alien-routine ("EVP_DigestUpdate" fnn-%evp-digest-update)
    sb-alien:int
  (ctx sb-sys:system-area-pointer)
  (data sb-sys:system-area-pointer)
  (count sb-alien:unsigned-long))
(sb-alien:define-alien-routine ("EVP_DigestFinal_ex" fnn-%evp-digest-final-ex)
    sb-alien:int
  (ctx sb-sys:system-area-pointer)
  (md sb-sys:system-area-pointer)
  (size sb-sys:system-area-pointer))
(sb-alien:define-alien-routine ("EVP_Digest" fnn-%evp-digest)
    sb-alien:int
  (data sb-sys:system-area-pointer)
  (count sb-alien:unsigned-long)
  (md sb-sys:system-area-pointer)
  (size sb-sys:system-area-pointer)
  (type sb-sys:system-area-pointer)
  (engine sb-sys:system-area-pointer))

(defparameter *fnn-digest-required-symbols*
  '("EVP_sha256" "EVP_MD_CTX_new" "EVP_MD_CTX_free" "EVP_DigestInit_ex"
    "EVP_DigestUpdate" "EVP_DigestFinal_ex" "EVP_Digest"))

;;; ---------------------------------------------------------------------------
;;; The primitive.

(declaim (inline fnn-digest-null))
(defun fnn-digest-null () (sb-sys:int-sap 0))

(defun fnn-digest-sap-octets (sap)
  (declare (type sb-sys:system-area-pointer sap))
  (let ((answer nil))
    (loop for index of-type fixnum from (1- +fnn-digest-octets+) downto 0
          do (push (sb-sys:sap-ref-8 sap index) answer))
    answer))

(defun fnn-digest-check (code what)
  (unless (eql code 1)
    (error 'fnn-digest-fault :detail (format nil "~a failed" what))))

(defmacro fnn-digest-with-context ((ctx) &body body)
  "One EVP SHA-256 context for BODY, freed on every exit."
  `(let ((,ctx (fnn-%evp-md-ctx-new)))
     (when (zerop (sb-sys:sap-int ,ctx))
       (error 'fnn-digest-fault :detail "EVP_MD_CTX_new failed"))
     (unwind-protect
          (progn
            (fnn-digest-check (fnn-%evp-digest-init-ex ,ctx (fnn-%evp-sha256)
                                                       (fnn-digest-null))
                              "EVP_DigestInit_ex")
            ,@body)
       (fnn-%evp-md-ctx-free ,ctx))))

(defun fnn-digest-update (ctx sap count)
  (declare (type (unsigned-byte 62) count))
  (when (plusp count)
    (fnn-digest-check (fnn-%evp-digest-update ctx sap count)
                      "EVP_DigestUpdate"))
  t)

(defun fnn-digest-final (ctx)
  (sb-alien:with-alien ((md (array (sb-alien:unsigned 8) 32)))
    (let ((sap (sb-alien:alien-sap md)))
      (fnn-digest-check (fnn-%evp-digest-final-ex ctx sap (fnn-digest-null))
                        "EVP_DigestFinal_ex")
      (fnn-digest-sap-octets sap))))

(defun fnn-digest-update-list (ctx m)
  "Feed the octets of the list M (up to its first non-cons tail) to CTX.
Return T, or NIL at the first element that is not an octet."
  (declare (optimize (speed 3) (safety 0)))
  (sb-alien:with-alien ((chunk (array (sb-alien:unsigned 8) 16384)))
    (let ((sap (sb-alien:alien-sap chunk))
          (fill 0))
      (declare (type (integer 0 16384) fill))
      (loop while (consp m)
            do (let ((x (car m)))
                 (unless (typep x '(unsigned-byte 8))
                   (return-from fnn-digest-update-list nil))
                 (setf (sb-sys:sap-ref-8 sap fill) x)
                 (incf fill)
                 (setq m (cdr m))
                 (when (= fill +fnn-digest-chunk-octets+)
                   (fnn-digest-update ctx sap fill)
                   (setq fill 0))))
      (fnn-digest-update ctx sap fill)
      t)))

(defun fnn-digest-update-string (ctx s)
  "Feed the character codes of the string S to CTX; NIL if one exceeds 255."
  (declare (optimize (speed 3) (safety 0)) (type string s))
  (sb-alien:with-alien ((chunk (array (sb-alien:unsigned 8) 16384)))
    (let ((sap (sb-alien:alien-sap chunk))
          (fill 0))
      (declare (type (integer 0 16384) fill))
      (dotimes (index (length s))
        (let ((code (char-code (char s index))))
          (unless (< code 256)
            (return-from fnn-digest-update-string nil))
          (setf (sb-sys:sap-ref-8 sap fill) code)
          (incf fill)
          (when (= fill +fnn-digest-chunk-octets+)
            (fnn-digest-update ctx sap fill)
            (setq fill 0))))
      (fnn-digest-update ctx sap fill)
      t)))

(defun fnn-digest-update-vector (ctx vector start end)
  (declare (type (simple-array (unsigned-byte 8) (*)) vector)
           (type fixnum start end))
  (sb-sys:with-pinned-objects (vector)
    (fnn-digest-update ctx (sb-sys:sap+ (sb-sys:vector-sap vector) start)
                       (- end start))))

(defun fnn-sha256-octet-range (vector start end)
  "SHA-256 of VECTOR[START, END) as a 32-octet list: the fast form, one
foreign call over the pinned vector, no copy.  VECTOR is a simple
(unsigned-byte 8) vector; the range is checked."
  (unless (and (typep vector '(simple-array (unsigned-byte 8) (*)))
               (typep start 'fixnum) (typep end 'fixnum)
               (<= 0 start end (length vector)))
    (error 'fnn-digest-fault :detail "octet range out of its vector"))
  (sb-alien:with-alien ((md (array (sb-alien:unsigned 8) 32)))
    (let ((out (sb-alien:alien-sap md)))
      (sb-sys:with-pinned-objects (vector)
        (fnn-digest-check
         (fnn-%evp-digest (sb-sys:sap+ (sb-sys:vector-sap vector) start)
                          (- end start) out (fnn-digest-null)
                          (fnn-%evp-sha256) (fnn-digest-null))
         "EVP_Digest"))
      (fnn-digest-sap-octets out))))

;;; ---------------------------------------------------------------------------
;;; The references and the replacements.
;;;
;;; The reference is the raw function ACL2 compiled from the book, captured
;;; when this file loads (before any replacement), so it survives
;;; installation and the save.

(defparameter *fnn-digest-entries*
  '(fn-sha256-stobj fn-sha256-of-string fn-sha256-of-prefixed-buffer))

(defvar *fnn-digest-references* nil
  "Alist: entry symbol -> the ACL2-compiled raw function.")
(defvar *fnn-digest-state* :reference
  "`:reference' (the ACL2 functions run) or `:native' (installed).")
(defvar *fnn-digest-version* nil)
(defvar *fnn-digest-lock* (sb-thread:make-mutex :name "fn native digest"))

(defun fnn-digest-capture-references ()
  (unless *fnn-digest-references*
    (setq *fnn-digest-references*
          (mapcar (lambda (entry)
                    (unless (fboundp entry)
                      (error 'fnn-digest-unavailable
                             :detail (format nil "~(~a~) is not defined; load the sha256 books first"
                                             entry)))
                    (cons entry (symbol-function entry)))
                  *fnn-digest-entries*)))
  t)

;; Captured on the first fnn-digest-initialize, before any install, not at
;; load: the references are ACL2's certified world (the sha256 books), which
;; a raw load of this file (host_check --load) does not have.  Nothing
;; installs a native entry before the capture, so what it captures is
;; always the ACL2 definition.

(defun fnn-digest-reference (entry)
  (fnn-digest-capture-references)
  (or (cdr (assoc entry *fnn-digest-references*))
      (error 'fnn-digest-unavailable
             :detail (format nil "no reference for ~(~a~)" entry))))

(defun fnn-digest-one-shot (sap count)
  (sb-alien:with-alien ((md (array (sb-alien:unsigned 8) 32)))
    (let ((out (sb-alien:alien-sap md)))
      (fnn-digest-check (fnn-%evp-digest sap count out (fnn-digest-null)
                                         (fnn-%evp-sha256) (fnn-digest-null))
                        "EVP_Digest")
      (fnn-digest-sap-octets out))))

(defun fnn-sha256-short-list (m)
  "A list of at most one chunk: copied to the stack and digested by one
EVP_Digest call (no context).  :LONG when M has more than a chunk, NIL at a
non-octet element."
  (declare (optimize (speed 3) (safety 0)))
  (sb-alien:with-alien ((chunk (array (sb-alien:unsigned 8) 16384)))
    (let ((sap (sb-alien:alien-sap chunk))
          (fill 0))
      (declare (type (integer 0 16384) fill))
      (loop while (consp m)
            do (let ((x (car m)))
                 (unless (typep x '(unsigned-byte 8))
                   (return-from fnn-sha256-short-list nil))
                 (when (= fill +fnn-digest-chunk-octets+)
                   (return-from fnn-sha256-short-list :long))
                 (setf (sb-sys:sap-ref-8 sap fill) x)
                 (incf fill)
                 (setq m (cdr m))))
      (fnn-digest-one-shot sap fill))))

(defun fnn-sha256-list-native (m)
  "`fn-sha256-stobj' natively: see the fast domain above."
  (let* ((short (fnn-sha256-short-list m))
         (answer (if (eq short :long)
                     (fnn-digest-with-context (ctx)
                       (and (fnn-digest-update-list ctx m)
                            (fnn-digest-final ctx)))
                   short)))
    (or answer
        (funcall (fnn-digest-reference 'fn-sha256-stobj) m))))

(defun fnn-sha256-string-native (s)
  "`fn-sha256-of-string' natively."
  (let ((answer (and (stringp s)
                     (fnn-digest-with-context (ctx)
                       (and (fnn-digest-update-string ctx s)
                            (fnn-digest-final ctx))))))
    (or answer
        (funcall (fnn-digest-reference 'fn-sha256-of-string) s))))

(defun fnn-digest-octet-buffer (stobj)
  "The raw octet array and fill of an fn-octets-congruent stobj (the
foundation fn-octets$c: slot 0 the (unsigned-byte 8) array, slot 1 the
fill), or NIL when the object is not that shape or the fill exceeds the
array."
  (and (simple-vector-p stobj)
       (= (length stobj) 2)
       (let ((buf (svref stobj 0))
             (fill (svref stobj 1)))
         (and (typep buf '(simple-array (unsigned-byte 8) (*)))
              (typep fill 'fixnum)
              (<= 0 fill (length buf))
              (cons buf fill)))))

(defun fnn-sha256-prefixed-buffer-native (prefix stobj)
  "`fn-sha256-of-prefixed-buffer' natively: PREFIX's octets, then the
buffer's octets [0, fill) read in place."
  (let* ((raw (fnn-digest-octet-buffer stobj))
         (answer (and raw
                      (fnn-digest-with-context (ctx)
                        (and (fnn-digest-update-list ctx prefix)
                             (fnn-digest-update-vector ctx (car raw) 0 (cdr raw))
                             (fnn-digest-final ctx))))))
    (or answer
        (funcall (fnn-digest-reference 'fn-sha256-of-prefixed-buffer)
                 prefix stobj))))

(defparameter *fnn-digest-natives*
  '((fn-sha256-stobj . fnn-sha256-list-native)
    (fn-sha256-of-string . fnn-sha256-string-native)
    (fn-sha256-of-prefixed-buffer . fnn-sha256-prefixed-buffer-native)))

;;; ---------------------------------------------------------------------------
;;; The start-up check: FIPS 180-4 / NIST CAVP known answers, then the
;;; native entries against the ACL2 references on every length 0..300
;;; (every block-boundary case of the padding: 55, 56, 63, 64, 119, 120, ...)
;;; and on a few longer messages.  About 30 ms.

(defparameter *fnn-digest-known-answers*
  '(("" . "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855")
    ("abc" . "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad")
    ("abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"
     . "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1")
    ("abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu"
     . "cf5b16a778af8380036ce59e7b0492370b249b11e8f07a51afac45037afee9d1")))

(defun fnn-digest-hex (octets)
  (format nil "~(~{~2,'0x~}~)" octets))

(defun fnn-digest-string-octets (s)
  (map 'list #'char-code s))

(defun fnn-digest-test-message (n seed)
  (let ((state seed) (answer nil))
    (dotimes (i n (nreverse answer))
      (setq state (logand (+ (* state 1103515245) 12345) #x7fffffff))
      (push (ldb (byte 8 16) state) answer))))

(defun fnn-digest-octets-stobj (octets)
  "A fresh fn-octets$c-shaped object holding OCTETS (for the check only)."
  (let ((buf (make-array (length octets) :element-type '(unsigned-byte 8)
                                         :initial-contents octets)))
    (vector buf (length octets))))

(defun fnn-digest-self-check ()
  "Signal `fnn-digest-fault' unless every native entry agrees with the
known answers and with its ACL2 reference.  Runs before installation."
  (flet ((fail (fmt &rest args)
           (error 'fnn-digest-fault :detail (apply #'format nil fmt args))))
    (dolist (pair *fnn-digest-known-answers*)
      (let* ((text (car pair))
             (octets (fnn-digest-string-octets text)))
        (dolist (got (list (fnn-sha256-list-native octets)
                           (fnn-sha256-string-native text)
                           (fnn-sha256-prefixed-buffer-native
                            nil (fnn-digest-octets-stobj octets))
                           (fnn-sha256-prefixed-buffer-native
                            (subseq octets 0 (floor (length octets) 2))
                            (fnn-digest-octets-stobj
                             (subseq octets (floor (length octets) 2))))
                           (let ((v (coerce octets '(simple-array (unsigned-byte 8) (*)))))
                             (fnn-sha256-octet-range v 0 (length v)))))
          (unless (string= (fnn-digest-hex got) (cdr pair))
            (fail "known answer for a ~d-octet message is ~a" (length octets)
                  (fnn-digest-hex got))))))
    (let ((list-ref (fnn-digest-reference 'fn-sha256-stobj))
          (buf-ref (fnn-digest-reference 'fn-sha256-of-prefixed-buffer)))
      (dolist (n (append (loop for n from 0 to 300 collect n) '(1000 4096 16383 16384 16385 40000)))
        (let* ((m (fnn-digest-test-message n (+ 7 n)))
               (want (funcall list-ref m)))
          (unless (equal (fnn-sha256-list-native m) want)
            (fail "list digest of ~d octets disagrees with fn-sha256-stobj" n))
          (let ((k (min n 3)))
            (unless (equal (fnn-sha256-prefixed-buffer-native
                            (subseq m 0 k) (fnn-digest-octets-stobj (nthcdr k m)))
                           (funcall buf-ref (subseq m 0 k)
                                    (fnn-digest-octets-stobj (nthcdr k m))))
              (fail "buffer digest of ~d octets disagrees with fn-sha256-of-prefixed-buffer" n))))))
    ;; The fast domain's edge: an improper tail ends the list; a non-octet
    ;; element falls back to the reference, which reduces it.
    (let ((ref (fnn-digest-reference 'fn-sha256-stobj)))
      (dolist (m (list '(97 98 99 . 7) '(97 300 99) '(97 -1) '(97 "x" 99) 42 nil))
        (unless (equal (fnn-sha256-list-native m) (funcall ref m))
          (fail "outside the fast domain the list digest of ~s disagrees" m)))))
  t)

;;; ---------------------------------------------------------------------------
;;; Installation.

(defun fnn-digest-install-natives ()
  (dolist (pair *fnn-digest-natives*)
    (setf (symbol-function (car pair)) (symbol-function (cdr pair)))))

(defun fnn-digest-restore-references ()
  (dolist (pair *fnn-digest-references*)
    (setf (symbol-function (car pair)) (cdr pair))))

(defun fnn-digest-reset ()
  "Run the ACL2 references again (before a save; before re-checking)."
  (sb-thread:with-mutex (*fnn-digest-lock*)
    (fnn-digest-restore-references)
    (setq *fnn-digest-state* :reference
          *fnn-digest-version* nil))
  t)

(defun fnn-digest-initialize ()
  "Check the libcrypto pair tls.lisp pinned (fnn-tls-initialize loads it),
then install the native entries.  Idempotent."
  (sb-thread:with-mutex (*fnn-digest-lock*)
    (unless (eq *fnn-digest-state* :native)
      (fnn-digest-capture-references)
      (fnn-digest-restore-references)
      (let ((missing (remove-if #'sb-sys:find-foreign-symbol-address
                                *fnn-digest-required-symbols*)))
        (when missing
          (error 'fnn-digest-unavailable
                 :detail (format nil "libcrypto lacks ~{~a~^, ~}" missing))))
      (fnn-digest-self-check)
      (fnn-digest-install-natives)
      (setq *fnn-digest-state* :native
            *fnn-digest-version* (and (boundp '*fnn-tls-version*)
                                      (symbol-value '*fnn-tls-version*)))))
  t)

(defun fnn-digest-startup ()
  "Re-check and re-install for this process incarnation (after tls).  A
developer image started with FN_NATIVE_DIGEST_TEST_OFF=1 keeps the ACL2
references (the matched measurement's reference arm)."
  (fnn-digest-reset)
  (unless (and (fboundp 'fnn-developer-selector)
               (equal (fnn-developer-selector "FN_NATIVE_DIGEST_TEST_OFF") "1"))
    (fnn-digest-initialize)))

(defun fnn-digest-status ()
  (list *fnn-digest-state* *fnn-digest-version*))

;;; ---------------------------------------------------------------------------
;;; The per-image differential (developer image only): `fn-host digest-check
;;; run COUNT SEED' digests COUNT inputs natively and by the ACL2 references
;;; and prints the first disagreement or the counts; `digest-check bench'
;;; prints MB/s of both.  tests/test_native_digest.py runs both.
;;;
;;; The inputs: every length 0..4200 (each padding case of 66 blocks), the
;;; edges k*64-1 .. k*64+1 and k*64+55, k*64+56 for k = 2^j up to 2^14
;;; blocks, the copy chunk's edges (16 KiB multiples +-1), then lengths
;;; log-uniform on [1, 2^20] to COUNT.  Each is checked in the list form,
;;; in the buffer form under a random prefix split (the reference run on
;;; every input up to 64 KiB and every eighth above), and, up to 4200, in the
;;; string form.

(defun fnn-digest-check-lengths (count random)
  (let ((lengths (loop for n from 0 to 4200 collect n)))
    (loop for j from 0 to 14
          for base = (* 64 (ash 1 j))
          do (dolist (d '(-1 0 1 55 56 63))
               (push (+ base d) lengths)))
    (loop for k from 1 to 8
          do (dolist (d '(-1 0 1))
               (push (+ (* k +fnn-digest-chunk-octets+) d) lengths)))
    (push (ash 1 20) lengths)
    (setq lengths (nreverse lengths))
    (let ((have (length lengths)))
      (append lengths
              (loop repeat (max 0 (- count have))
                    collect (min (ash 1 20)
                                 (floor (exp (* (random 1d0 random)
                                                (log (float (ash 1 20) 1d0)))))))))))

(defun fnn-digest-check-run (count seed)
  (let* ((random (sb-ext:seed-random-state seed))
         (lengths (fnn-digest-check-lengths count random))
         (list-ref (fnn-digest-reference 'fn-sha256-stobj))
         (buf-ref (fnn-digest-reference 'fn-sha256-of-prefixed-buffer))
         (str-ref (fnn-digest-reference 'fn-sha256-of-string))
         (checked 0) (buffer-checked 0) (string-checked 0) (octets 0))
    (fnn-digest-initialize)
    (dolist (n lengths)
      (let* ((m (loop repeat n collect (random 256 random)))
             (native (fnn-sha256-list-native m)))
        (unless (equal native (funcall list-ref m))
          (return-from fnn-digest-check-run (list :disagree :list n)))
        (let* ((k (random (1+ (min n 64)) random))
               (prefix (subseq m 0 k))
               (st (fnn-digest-octets-stobj (nthcdr k m))))
          (unless (equal (fnn-sha256-prefixed-buffer-native prefix st) native)
            (return-from fnn-digest-check-run (list :disagree :buffer-vs-list n k)))
          (when (or (<= n 65536) (zerop (random 8 random)))
            (incf buffer-checked)
            (unless (equal (funcall buf-ref prefix st) native)
              (return-from fnn-digest-check-run (list :disagree :buffer n k)))))
        (when (<= n 4200)
          (incf string-checked)
          (let ((s (map 'string #'code-char m)))
            (unless (and (equal (fnn-sha256-string-native s) native)
                         (equal (funcall str-ref s) native))
              (return-from fnn-digest-check-run (list :disagree :string n)))))
        (incf checked)
        (incf octets n)))
    (list :agree checked :buffer-reference buffer-checked
          :string-reference string-checked :octets octets)))

(defun fnn-digest-check-bench ()
  (flet ((rate (thunk octets reps)
           (let ((start (get-internal-real-time)))
             (dotimes (i reps) (funcall thunk))
             (let ((seconds (/ (float (- (get-internal-real-time) start) 1d0)
                               internal-time-units-per-second)))
               (round (/ (* octets reps) (max seconds 1d-9) 1d6))))))
    (fnn-digest-initialize)
    (let* ((n (ash 1 20))
           (m (fnn-digest-test-message n 3))
           (st (fnn-digest-octets-stobj m))
           (v (car (fnn-digest-octet-buffer st)))
           (page (fnn-digest-octets-stobj (fnn-digest-test-message 16384 4)))
           (rec (fnn-digest-test-message 200 5)))
      (list :mib-list-mbps
            (list :reference (rate (lambda () (funcall (fnn-digest-reference 'fn-sha256-stobj) m)) n 4)
                  :native (rate (lambda () (fnn-sha256-list-native m)) n 40))
            :mib-buffer-mbps
            (list :reference (rate (lambda () (funcall (fnn-digest-reference 'fn-sha256-of-prefixed-buffer) nil st)) n 4)
                  :native (rate (lambda () (fnn-sha256-prefixed-buffer-native nil st)) n 400)
                  :range (rate (lambda () (fnn-sha256-octet-range v 0 n)) n 400))
            :page-16k-mbps
            (list :reference (rate (lambda () (funcall (fnn-digest-reference 'fn-sha256-of-prefixed-buffer) nil page)) 16384 200)
                  :native (rate (lambda () (fnn-sha256-prefixed-buffer-native nil page)) 16384 20000))
            :record-200-mbps
            (list :reference (rate (lambda () (funcall (fnn-digest-reference 'fn-sha256-stobj) rec)) 200 20000)
                  :native (rate (lambda () (fnn-sha256-list-native rec)) 200 200000))))))

(defun fnn-command-digest-check (command rest)
  (unless (fnn-developer-image-p)
    (error 'fnn-usage-error
           :message "digest-check is available only in the developer image"))
  (cond ((string= command "run")
         (let* ((count (if rest (parse-integer (first rest)) 100000))
                (seed (if (cdr rest) (parse-integer (second rest)) 1))
                (result (fnn-digest-check-run count seed)))
           (let ((*print-pretty* nil)) (fnn-out "digest-check ~(~s~)" result))
           (if (eq (first result) :agree) +fnn-exit-ok+ 1)))
        ((string= command "bench")
         (let ((*print-pretty* nil)) (fnn-out "digest-bench ~(~s~)" (fnn-digest-check-bench)))
         +fnn-exit-ok+)
        (t (fnn-out "usage: digest-check run [COUNT [SEED]] | digest-check bench")
           +fnn-exit-ok+)))

(when (fboundp 'fnn-register-verb)
  (fnn-register-verb "digest-check" #'fnn-command-digest-check))
