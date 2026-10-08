;;; Evaluate the actual ACL2 configuration decisions used by the history-cost
;;; fixture. Delta admission/application are real; owner invariants and physical
;;; publication are outside this witness.
;;; ACL2's plumbing/primitive counterparts are the only raw runtime support;
;;; def-loop forms are expanded by the repository's generator.
(defpackage "ACL2" (:use "CL"))
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
(defun fnn-octet-list-p (x)
  (declare (ignorable x))
  (harness-stub-reached 'fnn-octet-list-p "host/native/io.lisp"))
(defun fnn-octets (sequence)
  (declare (ignorable sequence))
  (harness-stub-reached 'fnn-octets "host/native/io.lisp"))
;;; ---- derived stubs: END ----
(defmacro mv (&rest xs) `(values ,@xs))
(defmacro mv-let (vars form &body body) `(multiple-value-bind ,vars ,form ,@body))
(defun natp (x) (and (integerp x) (<= 0 x)))
(defun nfix (x) (if (natp x) x 0))
(defun len (xs) (if (consp xs) (1+ (len (cdr xs))) 0))
(defun true-listp (xs) (if (consp xs) (true-listp (cdr xs)) (null xs)))
(defun true-list-fix (xs) (if (consp xs) (cons (car xs) (true-list-fix (cdr xs))) nil))
(defun member-equal (x xs) (member x xs :test #'equal))
(load "tests/raw_def_loop.lisp")
(defun source-forms (path names)
  (let ((missing (copy-list names)))
    (handler-bind ((warning #'muffle-warning))
      (with-open-file (stream path)
        (loop for form = (read stream nil :eof) until (eq form :eof) do
          (when (and (consp form) (member (car form) '(defun defconst def-loop))
                     (member (cadr form) names))
            (case (car form)
              (defun (eval `(defun ,(cadr form) ,(caddr form) ,@(strip-xargs (cdddr form)))))
              (defconst (eval `(defparameter ,(cadr form) ,(caddr form))))
              (def-loop (raw-def-loop-load path (cadr form)))
              (otherwise (error "unsupported source form ~s" (car form))))
            (setf missing (remove (cadr form) missing)))))
      (assert (null missing) () "missing source forms ~s in ~a" missing path))))
(source-forms "books/cbor.lisp" '(*fn-cbor-max-uint* fn-cbor-octetp))
(source-forms "books/cbor-record-scalar.lisp" '(fn-record-uint32p))
(source-forms "books/records-shape.lisp"
              '(*fn-record-max-group-name* fn-record-string-octets-rev
                fn-record-string-octets-aux fn-record-string-octets
                fn-record-ascii-octetp fn-record-ascii-octet-listp
                fn-record-ascii-stringp fn-record-nonempty-at-mostp
                fn-record-group-component-octetp fn-record-group-name-octets-aux
                fn-record-group-name-octetsp fn-record-group-namep))
(source-forms "books/nntp-syntax.lisp" '(*fn-nntp-max-initial-line-octets*))
(source-forms "books/node-config.lisp" '(fn-cnode-line-ceiling))
(source-forms "books/owner-reconfig-phased.lisp" '(fn-orp-step))
(source-forms "books/config.lisp"
              '(*fn-cfg-max-label* *fn-cfg-max-rows* *fn-cfg-delta-kinds*
                *fn-cfg-default-policy-id* *fn-cfg-read-only-policy-id*
                fn-cfg-ag-car fn-cfg-ag-cdr fn-cfg-labelp fn-cfg-row-listp
                fn-cfg-group-name fn-cfg-group-created-gen fn-cfg-group-created-stamp
                fn-cfg-group-retired-gen fn-cfg-group-policy-id fn-cfg-group-next
                fn-cfg-group-authority fn-cfg-group-authority-gen
                fn-cfg-group-make-with-authority fn-cfg-group-make
                fn-cfg-group-find fn-cfg-entry-livep fn-cfg-live-names
                fn-cfg-groups fn-cfg-capacity fn-cfg-quotas fn-cfg-policies
                fn-cfg-listeners fn-cfg-peers fn-cfg-limits fn-cfg-authorities
                fn-cfg-invitations fn-cfg-accounts fn-cfg-descriptions
                fn-cfg-value-make-full fn-cfg-value-make fn-cfg-set-groups
                fn-cfg-empty-value fn-cfg-group-names fn-cfg-group-livep
                fn-cfg-delta-shapep fn-cfg-delta-kind fn-cfg-delta-a fn-cfg-delta-b
                fn-cfg-delta-n fn-cfg-delta-rows fn-cfg-delta-make fn-cfg-deltap
                fn-cfg-create-group fn-cfg-status-policy-id fn-cfg-set-group-status
                fn-cfg-group-status fn-cfg-groups-create fn-cfg-groups-set-policy
                fn-cfg-apply-delta fn-cfg-apply fn-cfg-name-line-octets
                fn-cfg-delta-reason fn-cfg-admissible-reason))

(defvar *fixture-value* nil)
(defvar *fixture-generation* 0)
(defun fixture-apply (delta)
  (let ((reason (fn-cfg-admissible-reason *fixture-value* (1+ *fixture-generation*)
                                          nil 0 (fn-cnode-line-ceiling) (list delta))))
    (unless reason
      (incf *fixture-generation*)
      (setf *fixture-value* (fn-cfg-apply *fixture-value* *fixture-generation* nil (list delta))))
    reason))
(defun fixture-create (name)
  (fixture-apply (fn-cfg-create-group name *fn-cfg-default-policy-id*)))
(defun fixture-shallow ()
  (setf *fixture-value* (fn-cfg-empty-value) *fixture-generation* 0)
  (assert (null (fixture-create "fn.test")))
  (dotimes (i 20)
    (assert (null (fixture-create (format nil "fn.shallow.~d" i))))))

;; Control: reproduce the original depth fixture, including the precise first
;; refused request. All size/count decisions below are ACL2's own functions.
(fixture-shallow)
(dotimes (i 20)
  (assert (null (fixture-create (format nil "fn.depth.~d" i)))))
(assert (= (fn-cfg-name-line-octets (fn-cfg-group-names *fixture-value* *fixture-generation*)) 508))
(assert (= (fn-cfg-name-line-octets (cons "fn.depth.20" (fn-cfg-group-names *fixture-value* *fixture-generation*))) 520))
(assert (eq (fixture-create "fn.depth.20") :group-table-unprojectable))
(multiple-value-bind (effects phase) (fn-orp-step :staging nil :refused)
  (assert (eq phase :done))
  (assert (equal effects '((:owner . :continue) (:owner . :refuse)))))
(assert (= *fixture-generation* 41))
(format t "original fixture: fn.depth.20 refused before authorization; projection 508 -> 520, ceiling ~d~%"
        (fn-cnode-line-ceiling))

;; Replacement: the Python cost test streams these exact delta inputs on stdin.
;; The fixture executes their real admissibility and application functions.
;; This ties the witness to the test's producer, rather than copying its loop.
(fixture-shallow)
(let ((before (fn-cfg-group-names *fixture-value* *fixture-generation*))
      (count 0))
  (loop for name = (read-line *standard-input* nil nil)
        for status = (read-line *standard-input* nil nil) while name do
    (assert (equal name "fn.test"))
    (assert (null (fixture-apply (fn-cfg-set-group-status name status))))
    (assert (equal (fn-cfg-group-status *fixture-value* *fixture-generation* "fn.test") status))
    (incf count))
  (assert (= count 500))
  (assert (= *fixture-generation* 521))
  (assert (equal (fn-cfg-group-names *fixture-value* *fixture-generation*) before)))
(dotimes (i 20)
  (assert (null (fixture-create (format nil "fn.deep.~d" i)))))
(assert (= *fixture-generation* 541))
;; The occupied-name witness must pass delta admission to reach window A.
(assert (null (fn-cfg-admissible-reason
               *fixture-value* (1+ *fixture-generation*) nil 0 (fn-cnode-line-ceiling)
               (list (fn-cfg-create-group "fn.occupied" *fn-cfg-default-policy-id*)))))
(format t "replacement fixture: 500 policy generations, 20 deep creates, occupied-name candidate admitted~%")

;; Round 5's occupied-name CLI request never reaches the owner: the heap
;; probe observes the entire configuration history for the limits overlay.
;; Reduce that observation to its decisive entry, the empty next-generation
;; file. These are the actual decoder, namespace decision and host bridge;
;; no decode/namespace verdict is mocked. Unused decoder branches are outside
;; this witness (undefined dependencies fail loudly if reached).
(source-forms "books/cbor.lisp"
              '(fn-cbor-octet-listp fn-cbor-ag-car fn-cbor-error
                fn-cbor-result-okp fn-cbor-decode-prechecked))
(source-forms "books/records-shape.lisp"
              '(*fn-record-max-octets* fn-record-parse-error fn-record-parse-okp
                fn-record-octets-chars-rev fn-record-octets-chars fn-record-octets-string))
(source-forms "books/records.lisp" '(fn-record-item-decode fn-record-read-bytes))
(source-forms "books/config.lisp" '(*fn-cfg-max-octets* fn-cfg-decode-exact))
(source-forms "books/rev-onto.lisp" '(fn-ag-rev-onto))
(source-forms "books/native-config-observation.lisp"
              '(fn-nco-result fn-nco-observed-entryp fn-nco-decode-entry
                fn-nco-decode-entries-loop fn-nco-decode-entries fn-nco-observe))
(source-forms "books/store-octet-entry.lisp" '(fn-store-octets->string))
(source-forms "host/store-node-host.lisp"
              '(fn-store-config-observation-entries-loop fn-store-config-observation-entries
                fn-store-config-observation))
(require :sb-posix)
(require :sb-bsd-sockets)
(source-forms "host/native/io.lisp" '(fnn-bridge-config-observation))
(define-condition fixture-namespace-fault (error) ((message :initarg :message :reader fault-message)))
(defun fnn-fault (message) (error 'fixture-namespace-fault :message message))
(defun fnn-string-octets (text) (map 'vector #'char-code text))
(defun fnn-octet-list (octets) (coerce octets 'list))
(defvar *namespace-decision* nil)
(defun fnn-core (name &rest args)
  (assert (eq name 'fn-store-config-observation))
  (setf *namespace-decision* (apply #'fn-store-config-observation args)))
(assert (equal (fn-cfg-decode-exact nil) '(:error :magic)))
(assert (equal (fn-nco-observe '(("00000542.cfg" nil)) 2048) '(:fault :decode nil)))
(assert
 (equal (handler-case
            (fnn-bridge-config-observation (list (cons "00000542.cfg" #())) 2048)
          (fixture-namespace-fault (condition) (fault-message condition)))
        "ACL2 refused configuration namespace observation"))
(assert (equal *namespace-decision* '(:fault :decode nil)))
(format t "occupied empty 00000542.cfg, limit 2048: ACL2 (:fault :decode nil), host namespace fault~%")
