;;; Warm raw-cache host seam over actual file I/O and the authenticated plan.
;;; P's span export is admitted in the developer ACL2 session before this file.
(in-package "ACL2")
(load "tests/native_extent_span_loader.lisp")
(xc2-load-native "books/article-stream.lisp" '(fn-ast-span-want))
(defvar *fnn-extent-run-dst* nil)
(defvar *fnn-extent-xcw* nil)
(defparameter *roots*
  '(fnn-extent-window-realize-span fnn-extent-window-cache-insert
    fnn-extent-window-pread))
(xc2-load-native-closure *roots*)

(defun xcr-call (name &rest args) (values-list (apply #'fnn-call name args)))

(let* ((path (sb-ext:posix-getenv "FN_XC2_RAW_EXTENT"))
       (payload (loop for i below 2048 collect (mod i 251)))
       (digest (fn-blake3 payload)) (trailer (fn-bch-pack digest))
       (ledger (second (multiple-value-list
                        (fn-prl-register (fn-prl-make '(1000000 0 8 4 20)) 7 '(64 0 1 0 0)))))
       (admit (multiple-value-list (fn-prw-admit ledger (list 7 0 2048 0 2048 0 trailer)
                                                  '(500000 0 0 1 1))))
       (token (second admit))
       (acquire (multiple-value-list (fn-pwx-acquire (third admit) (fn-pxe-new 0) token)))
       (input (fn-octets$c-reserve 64 (create-fn-octets$c)))
       (hash (create-pgs-digest-state)) (window (create-fn-ew-buffer)) (plan nil)
       (*fnn-page-read-pool* (create-fn-page-read-pool))
       (*fnn-extent-xcs* nil) (*fnn-extent-xcc* nil) (*fnn-extent-slots* nil)
       (*fnn-extent-xcw* nil)
       (*fnn-extent-run-dst* nil)
       (*fnn-extent-window-worker* nil) (*fnn-extent-window-token* nil))
  (fnn-cold-guard-cache-prepare
   (fn-prstartup-plan (sb-ext:dynamic-space-size) 0 0 path 1 65536 0 0 8 0))
  (assert (eq (first admit) :admitted))
  (assert (eq (first acquire) :assigned))
  (with-open-file (out path :direction :output :if-exists :supersede :element-type '(unsigned-byte 8))
    (write-sequence (coerce (append payload digest) '(vector (unsigned-byte 8))) out))
  (multiple-value-setq (plan hash)
    (xcr-call 'fn-ews-begin 7 0 2048 0 2048 0 (second token) 47 token trailer hash))
  (let ((fd (sb-posix:open path sb-posix:o-rdonly)))
    (unwind-protect
        (loop for visits below 10000 do
          (multiple-value-bind (status next hash1) (xcr-call 'fn-ews-tick plan hash)
            (setq plan next hash hash1)
            (case status
              (:continue nil)
              (:read
               (let* ((effect (xcr-call 'fn-ews-effect plan hash))
                      (io (fnn-extent-window-pread fd input (fifth effect) (sixth effect))))
                 (multiple-value-bind (word next hash1 window1)
                     (xcr-call 'fn-ews-read effect io plan input hash window)
                   (declare (ignore word))
                   (setq plan next hash hash1 window window1))))
              (otherwise (return))))
          finally (error "raw window exhausted fixture visits"))
      (sb-posix:close fd)))
  (let* ((returned (multiple-value-list (fn-pwx-return (third acquire) (second acquire) token)))
         (cached (multiple-value-list
                   (fn-pwc-cache (third returned) (second returned) token plan
                                 (fn-owner-page-window-cache-keep)))))
    (assert (eq (fn-pwr-outcome (third returned) (second returned) token plan) :ready))
    (assert (eq (first cached) :cached))
    (update-fn-prp-data (list (third cached) 0 0 0 1) *fnn-page-read-pool*)
    (fnn-with-observed-mutex (*fnn-extent-lock* :extent)
      (multiple-value-bind (evicted cachedp) (fnn-extent-window-cache-insert token plan window)
        (assert cachedp) (assert (null evicted)))))
  ;; Observation only: forward every call and every value to the actual dispatcher.
  (let ((dispatch (symbol-function 'fnn-call)) (calls 0) (digest-steps 0))
    (unwind-protect
        (progn
          (setf (symbol-function 'fnn-call)
                (lambda (name &rest args)
                  (when (eq name 'fn-xc-span-at) (incf calls))
                  (when (member name '(fn-ews-begin fn-ews-tick fn-ews-read))
                    (incf digest-steps))
                  (apply dispatch name args)))
          (assert (equal (fnn-extent-window-realize-span 7 0 2048 0 2048 trailer 0 2048) payload))
          (assert (= calls 1))
          (assert (equal (fnn-extent-window-realize-span 7 0 2048 0 2048 trailer 2040 8)
                         (subseq payload 2040)))
          (assert (= calls 2))
          (assert (zerop digest-steps))
          (assert (null (fnn-extent-window-realize-span 7 0 2048 0 2048 trailer 0 0)))
          (assert (= calls 2))
          (assert (equal (catch 'fnn-extent-cold
                           (fnn-extent-window-realize-span 7 0 2048 0 2048 (1+ trailer) 0 2048))
                         (xcr-call 'fn-pwr-cold-descriptor 7 0 2048 0 2048 (1+ trailer) 0))))
      (setf (symbol-function 'fnn-call) dispatch)))
  (format t "native_extent_cache_span: PASS actual pread/digest/cache; 2048 octets in one span export; tail, zero, cold descriptor~%"))
