;;; A-ARENA-SPAN-INTO (books/assumptions-durable-spans.lisp), host side:
;;; fn-arena-get-span-into (host/native/extent.lisp) appends exactly the octets
;;; fn-arena-get-span answers.  The REAL forms of extent.lisp run (the run
;;; loop, its sink, the synchronous route, the span read they are compared
;;; with); only what needs the ACL2 image is replaced by a model of its
;;; documented answer: the arena accessors, the borrowed-window decision (it
;;; copies the asked range of a source vector into the fn-ew-span array), the
;;; trailer-verified entry, the octet writer, the stobj accessors.  The same
;;; comparison on the real image's arena (staged, paged, lz handles and
;;; durable files) is owed (step 3 READY): it needs a built developer image.
(require :sb-posix)
(defpackage "ACL2" (:use "CL"))
(defpackage "ACL2_*1*_ACL2" (:use "CL"))
(in-package "ACL2")

;;; ---- derived stubs: BEGIN (python3 tools/harness_check.py --write-stubs; do not edit) ----
(define-condition harness-stub-reached (serious-condition)
  ((name :initarg :name :reader harness-stub-reached-name)
   (source :initarg :source :reader harness-stub-reached-source))
  (:report (lambda (c s)
             (format s "harness: host function ~(~a~) (~a) was reached; this harness neither stubs nor extracts it"
                     (harness-stub-reached-name c) (harness-stub-reached-source c)))))
(defun harness-stub-reached (name source)
  (format *error-output* "harness: host function ~(~a~) (~a) was reached; this harness neither stubs nor extracts it~%"
          name source)
  (finish-output *error-output*)
  (error 'harness-stub-reached :name name :source source))
(defun fnn-make-octets (n)
  (declare (ignorable n))
  (harness-stub-reached 'fnn-make-octets "host/native/io.lisp"))
;;; ---- derived stubs: END ----
(deftype fnn-octets () '(simple-array (unsigned-byte 8) (*)))
(define-condition fnn-store-fault (error) ((message :initarg :message :reader fault-message)))
(defmacro fnn-with-observed-mutex ((lock label &rest options) &body body)
  (declare (ignore label))
  `(sb-thread:with-recursive-lock (,lock) (progn ,@options ,@body)))
(defvar *fnn-extent-lock* (sb-thread:make-mutex))
(defvar *wanted* '(fnn-extent-fault +fnn-extent-span-capacity+ *fnn-extent-window-mode*
  *fnn-extent-window-worker* *fnn-extent-window-token* *fnn-extent-window-cache*
  *fnn-extent-run-dst* fnn-extent-copy-span fnn-extent-window-run-at
  fnn-extent-window-cache-run fnn-extent-window-realize-run
  fnn-extent-window-realize-span fn-durable-realize-span fnn-ew-span-array fn-arena-get-span-into))
(with-open-file (in "host/native/extent.lisp")
  (loop for f = (read in nil :eof) until (eq f :eof)
        for name = (and (consp f) (consp (cdr f)) (if (consp (cadr f)) (caadr f) (cadr f)))
        when (and (member (car f) '(defun defvar defconstant define-condition))
                  (member name *wanted*))
          do (eval f) (setq *wanted* (remove name *wanted*))))
(when *wanted* (error "missing forms ~s" *wanted*))

;;; The image's side, modelled.
;;; ACL2 represents fn-ew-span (one array field) as the array itself.
(defun create-fn-ew-span () (make-array 16384 :element-type '(unsigned-byte 8)))
(declaim (inline fn-ew-span-bytesi))
(defun fn-ew-span-bytesi (k dst) (aref dst k))
(defstruct worker row result)
(defun fnn-cold-worker-row (w) (worker-row w))
(defun fnn-cold-worker-result (w) (worker-result w))
(defun fnn-extent-executor-observe-returned (w) (declare (ignore w)) t)
(defun fnn-live-page-read-pool () nil)
(defvar *source* nil)   ; the durable bytes the model's window decision copies from
(defvar *cold* nil)
(defvar *runs* 0)
(defvar *entry-reads* 0)
(defun fnn-core-cold-single (name &rest args)
  (cond ((eq name 'fn-pwx-boundp) t)
        ((eq name 'fn-owner-page-read-ledger) nil)
        (t (list name args))))
(defun fnn-core-page-read-pool (name &rest args)
  (ecase name
    (fn-owner-page-window-span-at
     (destructuring-bind (row token plan file eoff elen poff plen trailer i j window dst) args
       (declare (ignore row token plan file eoff elen plen trailer window))
       (incf *runs*)
       (replace dst *source* :start2 (+ poff i) :end2 (+ poff j))
       (list :span)))
    (fn-owner-page-window-cache-span-at
     (destructuring-bind (token plan file eoff elen poff plen trailer i j window dst) args
       (declare (ignore token plan file eoff elen plen trailer window))
       (incf *runs*)
       (replace dst *source* :start2 (+ poff i) :end2 (+ poff j))
       (list :span)))))
(defvar *fnn-extent-stats* (list 0 0 0))
(defun fnn-extent-entry (file eoff elen trailer)
  (declare (ignore file elen trailer))
  (incf *entry-reads*)
  (subseq *source* eoff))
(defun fn-arn-extentp (e) (and (consp e) (= (length e) 6)))
(defvar *arena* nil)   ; vector of entries: (file eoff elen poff plen trailer) | (:list octets)
(defun fn-arena$x-count (a) (length a))
(defun fn-arena$x-exti (h a) (let ((e (aref a h))) (if (eq (car e) :list) :other e)))
(defun fn-arena$x-payload-len (h a)
  (let ((e (aref a h))) (if (eq (car e) :list) (length (second e)) (nth 4 e))))
(defun fn-arena$x-get (h i a)
  (let ((e (aref a h)))
    (if (eq (car e) :list)
        (aref (second e) i)
      (let ((*fnn-extent-window-mode* nil)) (first (fn-durable-realize-span (nth 0 e) (nth 1 e) (nth 2 e) (nth 3 e) (nth 4 e) (nth 5 e) i 1))))))
(defun fn-arena$x-get-span (h at n a)
  (let ((e (aref a h)))
    (if (eq (car e) :list)
        (coerce (subseq (second e) at (+ at n)) 'list)
      (let ((*fnn-extent-window-mode* nil)) (fn-durable-realize-span (nth 0 e) (nth 1 e) (nth 2 e) (nth 3 e) (nth 4 e) (nth 5 e) at n)))))
(defun fn-octets$c-reserve (n st)
  (when (> n (length (svref st 0)))
    (setf (svref st 0) (replace (make-array n :element-type '(unsigned-byte 8)) (svref st 0))))
  st)
(defun fn-oct-write-list (xs st)
  (let ((fill (svref st 1)))
    (fn-octets$c-reserve (+ fill (length xs)) st)
    (dolist (x xs) (setf (aref (svref st 0) fill) x) (incf fill))
    (setf (svref st 1) fill) st))
(defun make-buf (&optional prefix)
  (let ((st (vector (make-array 0 :element-type '(unsigned-byte 8)) 0)))
    (fn-oct-write-list prefix st)))
(defun buf-list (st) (coerce (subseq (svref st 0) 0 (svref st 1)) 'list))

;;; Payloads: 3 extents in one source, (file eoff elen poff plen trailer).
(setq *source* (let ((v (make-array 70000 :element-type '(unsigned-byte 8))))
                 (dotimes (i 70000 v) (setf (aref v i) (mod (* 31 (+ i (floor i 251))) 256)))))
(setq *arena*
      (vector (list 1 0 50000 100 40000 :t0)       ; multi-run extent (40000 > 2 x 16384)
              (list 1 60000 9000 60010 8000 :t1)   ; second extent
              (list :list (coerce (loop for i below 300 collect (mod (* 7 i) 256)) 'vector))   ; staged/paged/lz stand-in
              (list :list (coerce (loop for i below 70000 collect (mod (* 13 i) 251)) 'vector)))) ; a long one (the image's per-octet span recursed)
(defun model-token () (list :window nil 1 0 50000 100 40000 0 :t0))
(defun check (h at n prefix mode)
  (let* ((*fnn-extent-window-mode* (not (eq mode :sync)))
         (*fnn-extent-window-worker* (and (eq mode :worker) (make-worker :row 0 :result (list (list 0 0 0 0 0 100000) nil))))
         (*fnn-extent-window-token* (model-token))
         (*fnn-extent-window-cache* (and (eq mode :cache) (list (list (model-token) (list 0 0 0 0 0 100000) nil))))
         (*fnn-extent-run-dst* nil)
         (expected (append prefix (let ((*fnn-extent-window-mode* nil)) (fn-arena$x-get-span h at n *arena*))))
         (buf (make-buf prefix))
         (extent-p (not (eq (car (aref *arena* h)) :list))))
    (setq *runs* 0 *entry-reads* 0)
    (fn-arena-get-span-into h at n *arena* buf)
    (unless (equal (buf-list buf) expected)
      (error "MISMATCH h=~a at=~a n=~a mode=~a" h at n mode))
    (when (and extent-p (> n 0) (member mode '(:worker :cache)))
      (assert (= *runs* (ceiling n 16384))))
    (when (and extent-p (> n 0) (eq mode :sync)) (assert (= *entry-reads* 1)))))
(dolist (mode '(:sync :worker :cache))
  (dolist (h (if (eq mode :cache) '(0 2 3) '(0 1 2 3)))   ; the cached window is extent 0's
    (let ((plen (fn-arena$x-payload-len h *arena*)))
      (dolist (prefix (list nil '(9 8 7)))
        (dolist (w (list (cons 0 plen) (cons 5 100) (cons 0 0) (cons plen 0) (cons (- plen 17) 17)
                         (cons 1 (min 16384 (1- plen))) (cons 16383 (min 16385 (- plen 16383)))
                         (cons 100 (- plen 100))))
          (when (and (<= 0 (car w)) (<= 0 (cdr w)) (<= (+ (car w) (cdr w)) plen))
            (check h (car w) (cdr w) prefix mode)))))))
;;; Past the payload end is refused and leaves the buffer as it was.
(dolist (bad '((0 0 40001) (0 40000 1) (1 8000 1) (2 299 2) (3 69999 2) (4 0 0) (0 -1 1)))
  (let ((buf (make-buf '(1 2 3))) (*fnn-extent-window-mode* nil))
    (handler-case (progn (fn-arena-get-span-into (first bad) (second bad) (third bad) *arena* buf)
                         (error "accepted ~s" bad))
      (fnn-extent-fault () nil))
    (assert (equal (buf-list buf) '(1 2 3)))))
;;; A cold throw leaves the fill where it was.
(let ((buf (make-buf '(1 2 3))) (*fnn-extent-window-mode* t) (*fnn-extent-window-worker* nil)
      (*fnn-extent-window-cache* nil))
  (catch 'fnn-extent-cold (fn-arena-get-span-into 0 0 100 *arena* buf))
  (assert (equal (buf-list buf) '(1 2 3))))
(format t "native_arena_span_into_raw: ok~%")
