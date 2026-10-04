;;; RS-01: a POST the catalog's seal gate refuses (books/catalog-may-seal.lisp
;;; fn-owner-cat-may-seal answers nil) is a refusal of that POST -- the
;;; reservation consumed, nothing sealed, the store open, the word :refused
;;; (books/nntp-post.lisp: "441 posting failed; ...") -- never a fault that
;;; fences the store and stops the owner (AGENTS.md: refused is not a fault).
;;;
;;; The host code under test is read from its files, unchanged: the Store
;;; conditions and fnn-refuse / fnn-fault / fnn-indeterminate
;;; (host/native/io.lisp), and fnn-owner-attempt-handlers,
;;; fnn-owner-prepare-refusal-word and fnn-owner-attempt
;;; (host/native/owner.lisp).  The ACL2 answers (group codes, boundary,
;;; existing action, prepare, the gate, the reservation's consumption) are
;;; made up here, hence -mock: this checks the host's routing of the gate's
;;; answer only.
(require :sb-posix)
(require :sb-bsd-sockets)
(defpackage "ACL2" (:use "CL"))
(in-package "ACL2")

(defun harness-forms (path)
  (with-open-file (in path)
    (let ((*package* (find-package "ACL2")) (*read-eval* nil))
      (loop for form = (read in nil in) until (eq form in) collect form))))

(defun harness-load (path pick)
  "Evaluate the top-level forms of PATH that PICK selects."
  (dolist (form (harness-forms path))
    (when (funcall pick form) (eval form))))

(harness-load "host/native/io.lisp"
  (lambda (f)
    (and (consp f)
         (or (and (eq (car f) 'define-condition)
                  (member (cadr f) '(fnn-store-error fnn-store-fault fnn-store-indeterminate
                                     fnn-store-io-refusal fnn-os-error)))
             (and (eq (car f) 'defun)
                  (member (cadr f) '(fnn-refuse fnn-fault fnn-indeterminate)))))))

(defstruct fnn-store fenced)
(defvar *store* (make-fnn-store))
(defun fnn-owner-service-store (service) (declare (ignore service)) *store*)

(defvar *calls* nil)
(defvar *gate* nil)
(defun note (x) (push x *calls*))
(defun fnn-owner-core (name &rest args)
  (declare (ignore args))
  (note name)
  (case name
    (fn-owner-group-codes (list 1))
    (fn-owner-post-boundary :ok)
    (fn-owner-cat-may-seal *gate*)
    (fn-owner-next-txid 7)
    (t (error "harness: unexpected core ~a" name))))
(defun fnn-owner-action (name &rest args)
  (declare (ignore args))
  (note name)
  (case name
    (fn-owner-refuse-reservation :refused)
    (fn-owner-cat-prepare-sealed :prepared)
    (t (error "harness: unexpected action ~a" name))))
(defun fnn-owner-buffer-arena-action (name &rest args)
  (declare (ignore args))
  (note name)
  (case name
    (fn-owner-existing-action-buffer :absent)
    (fn-owner-prepare-buffer :seal-buffer)
    (t (error "harness: unexpected arena action ~a" name))))
(defun fnn-charge (n) n)
(defun fnn-validate-post-boundary (b) b)
(defun fnn-octet-list (x) (coerce x 'list))
(defun fnn-nat (x) x)
(defun fnn-advance-frontier (store txid) (declare (ignore store txid)) nil)
(defun fnn-metadata-buffer (msgid) (values msgid msgid nil))
(defun fnn-developer-selector (name) (declare (ignore name)) nil)
(defun fnn-err (control &rest args) (declare (ignore control args)) (note :err))
(defun fnn-call (name &rest args) (declare (ignore name args)) (list 0))
(defun fnn-live-arena () nil)
(defun fnn-seal-live-buffer () (note :sealed))
(defun fnn-owner-publish-prepared (service label) (declare (ignore service label)) (note :published) :durable)
(defvar *fnn-observe-callback* nil)
(defvar *fnn-identity-reservation-callback* nil)
(defvar *fnn-finish-callback* nil)
(defun fnn-owner-observe (&rest x) x)
(defun fnn-owner-identity-reservation (&rest x) x)
(defun fnn-owner-finish-submission (&rest x) x)

(harness-load "host/native/owner.lisp"
  (lambda (f)
    (and (consp f) (member (car f) '(defun defmacro))
         (member (cadr f) '(fnn-owner-attempt-handlers fnn-owner-prepare-refusal-word
                            fnn-owner-attempt)))))

(defvar *failures* 0)
(defun check (ok fmt &rest args)
  (unless ok (incf *failures*) (format t "~&native_post_seal_gate_refusal_raw: FAIL ~?~%" fmt args)))

(defun attempt (gate)
  (setq *calls* nil *gate* gate)
  (setf (fnn-store-fenced *store*) nil)
  (handler-case (fnn-owner-attempt :service "<x@y>" "payload" '("fn.test") "e")
    (serious-condition (c) (list :signalled (type-of c) (princ-to-string c)))))

;; The gate refuses: a refusal, nothing sealed, the store open, the
;; reservation consumed exactly once.
(let ((word (attempt nil)))
  (check (eq word :refused) "gate refused: the attempt answered ~s, not :refused" word)
  (check (not (fnn-store-fenced *store*)) "gate refused: the store was left fenced")
  (check (not (member :sealed *calls*)) "gate refused: the payload was sealed")
  (check (= 1 (count 'fn-owner-refuse-reservation *calls*))
         "gate refused: the reservation was consumed ~d times" (count 'fn-owner-refuse-reservation *calls*)))

;; The gate admits: sealed once, prepared, published.
(let ((word (attempt t)))
  (check (eq word :durable) "gate admitted: the attempt answered ~s" word)
  (check (= 1 (count :sealed *calls*)) "gate admitted: sealed ~d times" (count :sealed *calls*)))

(if (zerop *failures*)
    (format t "~&native_post_seal_gate_refusal_raw: PASS~%")
  (progn (format t "~&native_post_seal_gate_refusal_raw: ~d failure~:p~%" *failures*)
         (sb-ext:exit :code 1)))
