;;; Native BLAKE3 for the served images (lane digest-native, 2026-09-27;
;;; BLAKE3 by lane blake3-digest, 2026-09-28).
;;;
;;; This raw-Lisp file is part of HST-004's trust boundary, beside
;;; host/native/crypto.lisp (libsodium), host/native/signatures.lisp
;;; (libfn-mldsa65) and host/native/tls.lisp (the system libcrypto/libssl
;;; pair).  It decides nothing.  ACL2 still decides which octets are
;;; digested, what a digest is compared with and what follows from the
;;; comparison; this file only computes BLAKE3 of octets ACL2 handed over,
;;; faster.
;;;
;;; What it replaces.  books/crypto-attach.lisp attaches the constrained
;;; digests `fn-digest' and `fn-frame-digest' to `fn-blake3-stobj', and
;;; books/frame-digest-buffer.lisp attaches `fn-frame-digest-buffer' and
;;; `fn-frame-digest-range' to the buffer and window forms.  Those ACL2
;;; functions (books/blake3-stobj.lisp) are proved equal to the definition
;;; `fn-blake3' (books/blake3.lisp; `fn-blake3-stobj-is-blake3',
;;; `fn-blake3-of-prefixed-buffer-is-blake3',
;;; `fn-blake3-of-prefixed-range-is-blake3') and run at about 12 MB/s.  In the
;;; saved image, after this file's start-up check passes, the raw Lisp
;;; definitions of the three executable entries
;;;
;;;   fn-blake3-stobj                (any object, read as an octet list)
;;;   fn-blake3-of-prefixed-buffer   (a list prefix, then an octet buffer)
;;;   fn-blake3-of-prefixed-range    (a list prefix, then a window of one)
;;;
;;; are replaced by calls to the vendored BLAKE3 1.8.7 C (third_party/blake3,
;;; built by tools/build_blake3.sh into lib/libfn-blake3 beside the core, as
;;; tools/build_mldsa65.sh builds libfn-mldsa65; run-time CPU dispatch to
;;; SSE2/SSE4.1/AVX2/AVX-512 or NEON: 3.0 GB/s on hbox's P-cores, 1.36 GB/s
;;; on an M2).  Every caller -- the attachment dispatch, the `-any'
;;; wrappers, `fn-sidb-subject-id' -- reaches the replacement through the
;;; symbol, so no book changes.  The ACL2 definitions stay: they are the
;;; logic's subject, the reference the start-up check compares against
;;; (`fn-b3x-hash', which nothing replaces), and the fallback for any
;;; argument outside the fast domain.  The keyed and derive_key modes
;;; (books/node-secret.lisp: 32-octet keys, short messages) are not replaced.
;;;
;;; The fast domain.  `fn-blake3-stobj' is total: it hashes
;;; `(fn-b3-fix-octets m)', which stops at the first non-cons tail and
;;; reduces a non-octet element.  The native path takes the conses' cars
;;; while every one is an (unsigned-byte 8); an improper tail ends the list
;;; exactly as the fixer does; at the first non-octet element it abandons the
;;; native hash and hashes the fixed list instead (every element of which is
;;; an octet).  The buffer forms read the foundation's array in place and
;;; fall back to the reference when the object is not the fn-octets$c shape
;;; or the window lies outside the fill.  So on every argument the answer is
;;; the reference's, provided the primitive computes BLAKE3: that proviso is
;;; the assumption A-CRYPTO-NATIVE (specs/failures.md), qualified by the
;;; official vectors and the reference comparison below at every start, and
;;; by `digest-check run' per image.
;;;
;;; SHA-256 is not here: fn's only SHA-256 is RFC 8315's Cancel-Lock hash
;;; (books/control-authority.lisp `fn-ctl-lock-of-key' over books/sha256.lisp,
;;; a 44-octet key per lock), which needs no native form.
;;;
;;; Faults.  A library that cannot be loaded, or whose hasher does not fit
;;; the stack block, signals `fnn-digest-unavailable'; a start whose check
;;; fails refuses (io.lisp fnn-native-startup, exit 5), because a primitive
;;; that disagrees with the reference on a known answer is a broken library,
;;; not a slower one.

(in-package "ACL2")

(define-condition fnn-digest-error (error)
  ((detail :initarg :detail :reader fnn-digest-error-detail))
  (:report (lambda (condition stream)
             (format stream "native digest: ~a"
                     (fnn-digest-error-detail condition)))))

(define-condition fnn-digest-unavailable (fnn-digest-error) ())
(define-condition fnn-digest-fault (fnn-digest-error) ())

(defconstant +fnn-digest-octets+ 32)
;; The stack chunk a list is copied through: a work quantum per foreign
;; call, not a bound on the message (a message of any length is hashed chunk
;; by chunk).
(defconstant +fnn-digest-chunk-octets+ 16384)
;; The stack block the C hasher lives in (sizeof(blake3_hasher) is 1912 on
;; LP64; checked against fn_b3_hasher_size at load).
(defconstant +fnn-digest-hasher-words+ 512)

(sb-alien:define-alien-routine ("fn_b3_hash" fnn-%b3-hash) sb-alien:void
  (data sb-sys:system-area-pointer) (count sb-alien:unsigned-long)
  (out sb-sys:system-area-pointer))
(sb-alien:define-alien-routine ("fn_b3_hasher_size" fnn-%b3-hasher-size)
    sb-alien:unsigned-long)
(sb-alien:define-alien-routine ("fn_b3_init" fnn-%b3-init) sb-alien:void
  (hasher sb-sys:system-area-pointer))
(sb-alien:define-alien-routine ("fn_b3_update" fnn-%b3-update) sb-alien:void
  (hasher sb-sys:system-area-pointer) (data sb-sys:system-area-pointer)
  (count sb-alien:unsigned-long))
(sb-alien:define-alien-routine ("fn_b3_final" fnn-%b3-final) sb-alien:void
  (hasher sb-sys:system-area-pointer) (out sb-sys:system-area-pointer))
(sb-alien:define-alien-routine ("fn_b3_version" fnn-%b3-version) sb-alien:c-string)

;;; ---------------------------------------------------------------------------
;;; The library: FN_BLAKE3_LIBRARY when the operator names one, else lib/
;;; beside the core (build/lib for a built image, the frozen or installed
;;; directory's lib/): the precedent of host/native/signatures.lisp.

(defun fnn-digest-library-name ()
  (if (member :darwin *features*) "libfn-blake3.dylib" "libfn-blake3.so"))

(defun fnn-digest-library-candidates ()
  (let ((named (sb-ext:posix-getenv "FN_BLAKE3_LIBRARY"))
        (core sb-ext:*core-pathname*))
    (cond ((and named (plusp (length named)))
           (if (find (code-char 0) named)
               (error 'fnn-digest-unavailable :detail "invalid FN_BLAKE3_LIBRARY")
             (list named)))
          (core
           (list (namestring
                  (merge-pathnames (concatenate 'string "lib/" (fnn-digest-library-name))
                                   (make-pathname :name nil :type nil :version nil
                                                  :defaults core)))))
          (t nil))))

(defun fnn-digest-load-library ()
  (let ((last-error nil))
    (dolist (candidate (fnn-digest-library-candidates))
      (handler-case
          (progn
            ;; Not serialized into the core: every start re-loads from the
            ;; restarted image's own lib/.
            (sb-alien:load-shared-object candidate :dont-save t)
            (return-from fnn-digest-load-library candidate))
        (error (condition) (setq last-error condition))))
    (error 'fnn-digest-unavailable
           :detail (if last-error
                       (format nil "the BLAKE3 library cannot be loaded: ~a" last-error)
                     "no BLAKE3 library candidate (lib/ beside the core)"))))

(defparameter *fnn-digest-required-symbols*
  '("fn_b3_hash" "fn_b3_hasher_size" "fn_b3_init" "fn_b3_update" "fn_b3_final"
    "fn_b3_version"))

;;; ---------------------------------------------------------------------------
;;; The primitive.

(defun fnn-digest-sap-octets (sap)
  (declare (type sb-sys:system-area-pointer sap))
  (let ((answer nil))
    (loop for index of-type fixnum from (1- +fnn-digest-octets+) downto 0
          do (push (sb-sys:sap-ref-8 sap index) answer))
    answer))

(defmacro fnn-digest-with-hasher ((hasher) &body body)
  "A C BLAKE3 hasher on the stack for BODY."
  (let ((block (gensym "BLOCK")))
    `(sb-alien:with-alien ((,block (array (sb-alien:unsigned 64) ,+fnn-digest-hasher-words+)))
       (let ((,hasher (sb-alien:alien-sap ,block)))
         (fnn-%b3-init ,hasher)
         ,@body))))

(defun fnn-digest-update (hasher sap count)
  (declare (type (unsigned-byte 62) count))
  (when (plusp count)
    (fnn-%b3-update hasher sap count))
  t)

(defun fnn-digest-final (hasher)
  (sb-alien:with-alien ((out (array (sb-alien:unsigned 8) 32)))
    (let ((sap (sb-alien:alien-sap out)))
      (fnn-%b3-final hasher sap)
      (fnn-digest-sap-octets sap))))

(defun fnn-digest-update-list (hasher m)
  "Feed the octets of the list M (up to its first non-cons tail) to HASHER.
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
                   (fnn-digest-update hasher sap fill)
                   (setq fill 0))))
      (fnn-digest-update hasher sap fill)
      t)))

(defun fnn-digest-update-vector (hasher vector start end)
  (declare (type (simple-array (unsigned-byte 8) (*)) vector)
           (type fixnum start end))
  (sb-sys:with-pinned-objects (vector)
    (fnn-digest-update hasher (sb-sys:sap+ (sb-sys:vector-sap vector) start)
                       (- end start))))

(defun fnn-blake3-octet-range (vector start end)
  "BLAKE3 of VECTOR[START, END) as a 32-octet list: one foreign call over
the pinned vector, no copy.  VECTOR is a simple (unsigned-byte 8) vector;
the range is checked."
  (unless (and (typep vector '(simple-array (unsigned-byte 8) (*)))
               (typep start 'fixnum) (typep end 'fixnum)
               (<= 0 start end (length vector)))
    (error 'fnn-digest-fault :detail "octet range out of its vector"))
  (sb-alien:with-alien ((out (array (sb-alien:unsigned 8) 32)))
    (let ((sap (sb-alien:alien-sap out)))
      (sb-sys:with-pinned-objects (vector)
        (fnn-%b3-hash (sb-sys:sap+ (sb-sys:vector-sap vector) start) (- end start) sap))
      (fnn-digest-sap-octets sap))))

;;; ---------------------------------------------------------------------------
;;; The references and the replacements.
;;;
;;; The references are the raw functions ACL2 compiled from the books,
;;; captured when this file loads (before any replacement), so they survive
;;; installation and the save.  `fn-b3x-hash' is the reference every check
;;; compares with: nothing replaces it, so it is ACL2's BLAKE3 in every state.

(defparameter *fnn-digest-entries*
  '(fn-blake3-stobj fn-blake3-of-prefixed-buffer fn-blake3-of-prefixed-range
    fn-b3x-hash fn-b3-fix-octets))

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
                             :detail (format nil "~(~a~) is not defined; load the blake3 books first"
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

(defparameter +fnn-b3-iv+
  '(1779033703 3144134277 1013904242 2773480762
    1359893119 2600822924 528734635 1541459225))

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

(defun fnn-digest-octets-stobj (octets)
  "A fresh fn-octets$c-shaped object holding OCTETS."
  (let ((buf (make-array (length octets) :element-type '(unsigned-byte 8)
                                         :initial-contents octets)))
    (vector buf (length octets))))

(defun fnn-b3-reference-range (prefix a wn stobj)
  "ACL2's BLAKE3 of PREFIX then STOBJ's octets [A, A+WN): `fn-b3x-hash'."
  (funcall (fnn-digest-reference 'fn-b3x-hash) +fnn-b3-iv+ 0 prefix a wn stobj))

(defun fnn-b3-reference-list (m)
  "ACL2's BLAKE3 of any object read as octets."
  (let ((fixed (funcall (fnn-digest-reference 'fn-b3-fix-octets) m)))
    (fnn-b3-reference-range nil 0 (length fixed) (fnn-digest-octets-stobj fixed))))

(defun fnn-blake3-list-native (m)
  "`fn-blake3-stobj' natively: see the fast domain above."
  (or (fnn-digest-with-hasher (h)
        (and (fnn-digest-update-list h m)
             (fnn-digest-final h)))
      ;; A non-octet element: hash what the fixer makes of M, every element
      ;; of which is an octet.
      (fnn-blake3-list-native (funcall (fnn-digest-reference 'fn-b3-fix-octets) m))))

(defun fnn-blake3-prefixed-range-native (prefix a wn stobj)
  "`fn-blake3-of-prefixed-range' natively: PREFIX's octets, then the
buffer's octets [A, A+WN) read in place."
  (let* ((raw (fnn-digest-octet-buffer stobj))
         (answer (and raw (typep a 'fixnum) (typep wn 'fixnum)
                      (<= 0 a) (<= 0 wn) (<= (+ a wn) (cdr raw))
                      (fnn-digest-with-hasher (h)
                        (and (fnn-digest-update-list h prefix)
                             (fnn-digest-update-vector h (car raw) a (+ a wn))
                             (fnn-digest-final h))))))
    (or answer
        (funcall (fnn-digest-reference 'fn-blake3-of-prefixed-range)
                 prefix a wn stobj))))

(defun fnn-blake3-prefixed-buffer-native (prefix stobj)
  "`fn-blake3-of-prefixed-buffer' natively: PREFIX's octets, then the
buffer's octets [0, fill) read in place."
  (let ((raw (fnn-digest-octet-buffer stobj)))
    (if raw
        (fnn-blake3-prefixed-range-native prefix 0 (cdr raw) stobj)
      (funcall (fnn-digest-reference 'fn-blake3-of-prefixed-buffer) prefix stobj))))

(defparameter *fnn-digest-natives*
  '((fn-blake3-stobj . fnn-blake3-list-native)
    (fn-blake3-of-prefixed-buffer . fnn-blake3-prefixed-buffer-native)
    (fn-blake3-of-prefixed-range . fnn-blake3-prefixed-range-native)))

;;; ---------------------------------------------------------------------------
;;; The start-up check: the official BLAKE3 vectors (test_vectors.json at
;;; tag 1.8.7; input i mod 251, the default 32-octet output) through every
;;; native form, then the native entries against ACL2's `fn-b3x-hash' on
;;; every length 0..300 and every chunk edge to 16 chunks and 40,000
;;; octets, and on the fast domain's edges.

(defparameter *fnn-digest-known-answers*
  '(
    (0 . "af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262")
    (1 . "2d3adedff11b61f14c886e35afa036736dcd87a74d27b5c1510225d0f592e213")
    (64 . "4eed7141ea4a5cd4b788606bd23f46e212af9cacebacdc7d1f4c6dc7f2511b98")
    (65 . "de1e5fa0be70df6d2be8fffd0e99ceaa8eb6e8c93a63f2d8d1c30ecb6b263dee")
    (1023 . "10108970eeda3eb932baac1428c7a2163b0e924c9a9e25b35bba72b28f70bd11")
    (1024 . "42214739f095a406f3fc83deb889744ac00df831c10daa55189b5d121c855af7")
    (1025 . "d00278ae47eb27b34faecf67b4fe263f82d5412916c1ffd97c8cb7fb814b8444")
    (2048 . "e776b6028c7cd22a4d0ba182a8bf62205d2ef576467e838ed6f2529b85fba24a")
    (2049 . "5f4d72f40d7a5f82b15ca2b2e44b1de3c2ef86c426c95c1af0b6879522563030")
    (8193 . "bab6c09cb8ce8cf459261398d2e7aef35700bf488116ceb94a36d0f5f1b7bc3b")
    (16384 . "f875d6646de28985646f34ee13be9a576fd515f76b5b0a26bb324735041ddde4")
    (31744 . "62b6960e1a44bcc1eb1a611a8d6235b6b4b78f32e7abc4fb4c6cdcce94895c47")
    (102400 . "bc3e3d41a1146b069abffad3c0d44860cf664390afce4d9661f7902e7943e085")))

(defun fnn-digest-hex (octets)
  (format nil "~(~{~2,'0x~}~)" octets))

(defun fnn-digest-vector-input (n)
  (loop for i below n collect (mod i 251)))

(defun fnn-digest-test-message (n seed)
  (let ((state seed) (answer nil))
    (dotimes (i n (nreverse answer))
      (setq state (logand (+ (* state 1103515245) 12345) #x7fffffff))
      (push (ldb (byte 8 16) state) answer))))

(defun fnn-digest-check-lengths-startup ()
  (append (loop for n from 0 to 300 collect n)
          (loop for k from 1 to 16 append (list (1- (* 1024 k)) (* 1024 k) (1+ (* 1024 k))))
          '(16383 16384 16385 40000)))

(defun fnn-digest-self-check ()
  "Signal `fnn-digest-fault' unless every native entry agrees with the
official vectors and with ACL2's `fn-b3x-hash'.  Runs before installation."
  (flet ((fail (fmt &rest args)
           (error 'fnn-digest-fault :detail (apply #'format nil fmt args))))
    (dolist (pair *fnn-digest-known-answers*)
      (let* ((n (car pair))
             (octets (fnn-digest-vector-input n))
             (half (floor n 2)))
        (dolist (got (list (fnn-blake3-list-native octets)
                           (fnn-blake3-prefixed-buffer-native nil (fnn-digest-octets-stobj octets))
                           (fnn-blake3-prefixed-buffer-native
                            (subseq octets 0 half)
                            (fnn-digest-octets-stobj (subseq octets half)))
                           (fnn-blake3-prefixed-range-native
                            (subseq octets 0 (min n 7)) 3 (- n (min n 7))
                            (fnn-digest-octets-stobj (append '(9 9 9) (nthcdr (min n 7) octets) '(9))))
                           (let ((v (coerce octets '(simple-array (unsigned-byte 8) (*)))))
                             (fnn-blake3-octet-range v 0 (length v)))))
          (unless (string= (fnn-digest-hex got) (cdr pair))
            (fail "known answer for the ~d-octet vector is ~a" n (fnn-digest-hex got))))))
    (dolist (n (fnn-digest-check-lengths-startup))
      (let* ((m (fnn-digest-test-message n (+ 7 n)))
             (want (fnn-b3-reference-range nil 0 n (fnn-digest-octets-stobj m))))
        (unless (equal (fnn-blake3-list-native m) want)
          (fail "list digest of ~d octets disagrees with fn-b3x-hash" n))
        (let ((k (min n 3)))
          (unless (equal (fnn-blake3-prefixed-buffer-native
                          (subseq m 0 k) (fnn-digest-octets-stobj (nthcdr k m)))
                         want)
            (fail "buffer digest of ~d octets disagrees with fn-b3x-hash" n)))))
    ;; The fast domain's edge: an improper tail ends the list; a non-octet
    ;; element is reduced as the fixer reduces it.
    (dolist (m (list '(97 98 99 . 7) '(97 300 99) '(97 -1) '(97 "x" 99) 42 nil))
      (unless (equal (fnn-blake3-list-native m) (fnn-b3-reference-list m))
        (fail "outside the fast domain the list digest of ~s disagrees" m))))
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
  "Load lib/libfn-blake3, check it, then install the native entries.
Idempotent."
  (sb-thread:with-mutex (*fnn-digest-lock*)
    (unless (eq *fnn-digest-state* :native)
      (fnn-digest-capture-references)
      (fnn-digest-restore-references)
      (let ((library (fnn-digest-load-library)))
        (let ((missing (remove-if #'sb-sys:find-foreign-symbol-address
                                  *fnn-digest-required-symbols*)))
          (when missing
            (error 'fnn-digest-unavailable
                   :detail (format nil "~a lacks ~{~a~^, ~}" library missing))))
        (unless (<= (fnn-%b3-hasher-size) (* 8 +fnn-digest-hasher-words+))
          (error 'fnn-digest-unavailable
                 :detail (format nil "the BLAKE3 hasher is ~d octets" (fnn-%b3-hasher-size))))
        (fnn-digest-self-check)
        (fnn-digest-install-natives)
        (setq *fnn-digest-state* :native
              *fnn-digest-version* (list library (fnn-%b3-version))))))
  t)

(defun fnn-digest-startup ()
  "Re-check and re-install for this process incarnation.  A developer image
started with FN_NATIVE_DIGEST_TEST_OFF=1 keeps the ACL2 references (the
matched measurement's reference arm)."
  (fnn-digest-reset)
  (unless (and (fboundp 'fnn-developer-selector)
               (equal (fnn-developer-selector "FN_NATIVE_DIGEST_TEST_OFF") "1"))
    (fnn-digest-initialize)))

(defun fnn-digest-status ()
  (list *fnn-digest-state* *fnn-digest-version*))

;;; ---------------------------------------------------------------------------
;;; The per-image differential (developer image only): `fn-host digest-check
;;; run COUNT SEED' hashes COUNT inputs natively and by ACL2's `fn-b3x-hash'
;;; and prints the first disagreement or the counts; `digest-check bench'
;;; prints MB/s of both.  tests/test_native_digest.py runs both.
;;;
;;; The inputs: every length 0..4200, the chunk edges k*1024-1 .. k*1024+1
;;; for k = 2^0..2^10 and the block edges inside the first chunk, the copy
;;; chunk's edges (16 KiB multiples +-1), then lengths log-uniform on
;;; [1, 2^20] to COUNT.  Each is checked in the list form, in the buffer
;;; form under a random prefix split and in the window form inside a longer
;;; buffer; the reference runs on every input up to 64 KiB and every eighth
;;; above.

(defun fnn-digest-check-lengths (count random)
  (let ((lengths (loop for n from 0 to 4200 collect n)))
    (loop for j from 0 to 10
          for base = (* 1024 (ash 1 j))
          do (dolist (d '(-1 0 1 63 64 65))
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
         (checked 0) (reference-checked 0) (octets 0))
    (fnn-digest-initialize)
    (dolist (n lengths)
      (let* ((m (loop repeat n collect (random 256 random)))
             (native (fnn-blake3-list-native m)))
        (when (or (<= n 65536) (zerop (random 8 random)))
          (incf reference-checked)
          (unless (equal native (fnn-b3-reference-range nil 0 n (fnn-digest-octets-stobj m)))
            (return-from fnn-digest-check-run (list :disagree :list n))))
        (let* ((k (random (1+ (min n 64)) random))
               (prefix (subseq m 0 k))
               (st (fnn-digest-octets-stobj (nthcdr k m))))
          (unless (equal (fnn-blake3-prefixed-buffer-native prefix st) native)
            (return-from fnn-digest-check-run (list :disagree :buffer-vs-list n k)))
          (let ((w (fnn-digest-octets-stobj (append '(1 2 3) (nthcdr k m) '(4 5)))))
            (unless (equal (fnn-blake3-prefixed-range-native prefix 3 (- n k) w) native)
              (return-from fnn-digest-check-run (list :disagree :range-vs-list n k)))))
        (incf checked)
        (incf octets n)))
    (list :agree checked :reference reference-checked :octets octets)))

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
            (list :reference (rate (lambda () (fnn-b3-reference-list m)) n 2)
                  :native (rate (lambda () (fnn-blake3-list-native m)) n 40))
            :mib-buffer-mbps
            (list :reference (rate (lambda () (fnn-b3-reference-range nil 0 n st)) n 2)
                  :native (rate (lambda () (fnn-blake3-prefixed-buffer-native nil st)) n 400)
                  :range (rate (lambda () (fnn-blake3-octet-range v 0 n)) n 400))
            :page-16k-mbps
            (list :reference (rate (lambda () (fnn-b3-reference-range nil 0 16384 page)) 16384 100)
                  :native (rate (lambda () (fnn-blake3-prefixed-buffer-native nil page)) 16384 20000))
            :record-200-mbps
            (list :reference (rate (lambda () (fnn-b3-reference-list rec)) 200 10000)
                  :native (rate (lambda () (fnn-blake3-list-native rec)) 200 200000))))))

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
