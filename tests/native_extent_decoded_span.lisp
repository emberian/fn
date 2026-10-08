;;; Host seam evidence, run in a warm developer core with this tree's native
;;; span functions loaded below. Uses real compressed bytes, private decoder
;;; jobs, file preads, ledger admission/cache transitions and slot lookup.
;;; No mocked realizer, decoder, hit decision, buffer or ledger operation.
(in-package "ACL2")

(load "tests/native_extent_span_loader.lisp")

(xc2-load-native "books/article-stream.lisp" '(fn-ast-span-want))
; The warm core owns its startup constant/layout. These cases are smaller
; than both the old 16 KiB span capacity and the current profile capacity;
; this fixture qualifies decoded bytes, not native startup/profile loading.
(defvar *fnn-extent-run-dst* nil)
(defvar *fnn-extent-xcw* nil)

; Extract the complete native function closure of these roots from the two
; extent files. Structs and the ACL2 world come from the required image; every
; external native function/macro must exist there. No derived stub can replace
; an image function. This is the closure harness form understood by harness_check.
(defparameter *roots*
  '(fn-durable-realize-lz-span fn-durable-realize-lz-octet
    fnn-extent-decoded-window-cache-insert))
(xc2-load-native-closure *roots*)

(defun xc2-read-octets (path)
  (with-open-file (in path :element-type '(unsigned-byte 8))
    (let ((v (make-array (file-length in) :element-type '(unsigned-byte 8))))
      (assert (= (read-sequence v in) (length v)))
      (coerce v 'list))))

(defun xc2-call (name &rest args)
  (values-list (apply #'fnn-call name args)))

(defun xc2-cache-decoded (fd ledger compressed decoded trailer position)
  (let* ((admit (multiple-value-list
                 (fn-pwz-admit ledger
                  (list 7 100 (+ 3 compressed) 102 compressed position trailer decoded 0)
                  '(0 0 0 1 1))))
         (token (second admit))
         (acquire (multiple-value-list (fn-pwx-acquire (third admit) (fn-pxe-new 0) token)))
         (worker (second acquire))
         (job (xc2-call 'fn-dwj-reserve (xc2-call 'create-fn-decoded-job))))
    (assert (eq (first admit) :admitted))
    (multiple-value-bind (word next)
        (xc2-call 'fn-dwj-assign (third acquire) worker token token 47 job)
      (assert (eq word :decoded-assigned)) (setf job next))
    (multiple-value-bind (word next) (xc2-call 'fn-dwj-begin token job)
      (assert (eq word :decoded-started)) (setf job next))
    (loop for visits below 1000000 do
      (multiple-value-bind (word effect next) (xc2-call 'fn-dwj-one token job)
        (setf job next)
        (cond ((eq word :ready) (return))
              ((member word '(:refused :stale-decoded-worker))
               (error "decoded fixture refused ~s ~s" word effect))
              ((eq word :read)
               (let ((status (fnn-extent-decoded-window-pread fd (svref job 1) token (fourth effect))))
                 (assert (eq status :ok))
                 (multiple-value-bind (answer next)
                     (xc2-call 'fn-dwj-read-observation token (third effect) status job)
                   (declare (ignore answer)) (setf job next))))))
      finally (error "decoded fixture exhausted its visits"))
    (let* ((returned (multiple-value-list (fn-pwx-return (third acquire) worker token)))
           (cached (multiple-value-list (xc2-call 'fn-dwj-cache (third returned) (second returned) token (fn-owner-page-window-cache-keep) job))))
      (assert (eq (first cached) :cached))
      (setf job (fourth cached))
      (update-fn-prp-data (list (third cached) 0 0 0 1) *fnn-page-read-pool*)
      (fnn-with-observed-mutex (*fnn-extent-lock* :extent)
        (assert (null (fnn-extent-decoded-window-cache-insert token (svref job 7)))))
      (third cached))))

(let* ((root (sb-ext:posix-getenv "FN_XC2_FIXTURE"))
       (compressed (xc2-read-octets (concatenate 'string root "/compressed")))
       (payload (xc2-read-octets (concatenate 'string root "/payload")))
       (message (append '(9 8) compressed '(7)))
       (digest (fn-blake3 message)) (trailer (fn-bch-pack digest))
       (path (concatenate 'string root "/extent"))
       (ledger (second (multiple-value-list
                        (fn-prl-register (fn-prl-make '(1000000 0 8 4 20)) 7 '(64 0 1 0 0)))))
       (*fnn-page-read-pool* (create-fn-page-read-pool))
       (*fnn-extent-xcs* nil) (*fnn-extent-xcc* nil) (*fnn-extent-slots* nil)
       (*fnn-extent-xcw* nil)
       (*fnn-extent-run-dst* nil)
       (*fnn-extent-window-mode* t) (*fnn-extent-window-worker* nil)
       (*fnn-extent-window-token* nil))
  (with-open-file (out path :direction :output :if-exists :supersede :element-type '(unsigned-byte 8))
    (write-sequence (coerce (append (make-list 100 :initial-element 0) message digest) '(vector (unsigned-byte 8))) out))
  (let ((fd (sb-posix:open path sb-posix:o-rdonly)))
    (unwind-protect
        (progn
          (setf ledger (xc2-cache-decoded fd ledger (length compressed) (length payload) trailer 0))
          (setf ledger (xc2-cache-decoded fd ledger (length compressed) (length payload) trailer 16384)))
      (sb-posix:close fd)))
  (dolist (range '((0 2048) (16380 16) (19990 10)))
    (destructuring-bind (at count) range
      (let ((span (fn-durable-realize-lz-span 7 100 (length message) 102 (length compressed)
                                             trailer (length payload) nil at count))
            (scalar (loop for i from at below (+ at count)
                          collect (fn-durable-realize-lz-octet 7 100 (length message) 102
                                   (length compressed) trailer (length payload) nil i))))
        (assert (equal span scalar))
        (assert (equal span (subseq payload at (+ at count)))))))
  (assert (null (fn-durable-realize-lz-span 7 100 (length message) 102 (length compressed)
                                         trailer (length payload) nil 0 0)))
  (format t "native_extent_decoded_span: PASS actual decoded/scalar spans; 2048 octets, window crossing, tail, zero~%"))
(sb-ext:exit :code 0)
