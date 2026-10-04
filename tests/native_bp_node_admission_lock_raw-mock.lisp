;;; Exercise the shipped BP application entry with config changing before the
;;; serialized decision.  No Store/FNRJ mutation may follow a revoked trust.
(require :sb-posix)
(require :sb-bsd-sockets)
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
(defun fnn-core-state (name &rest args)
  (declare (ignorable name args))
  (harness-stub-reached 'fnn-core-state "host/native/io.lisp"))
(defun fnn-hsig-observe-raw (ed-public-key ml-public-key message signatures)
  (declare (ignorable ed-public-key ml-public-key message signatures))
  (harness-stub-reached 'fnn-hsig-observe-raw "host/native/signatures.lisp"))
(defun fnn-octet-list (octets)
  (declare (ignorable octets))
  (harness-stub-reached 'fnn-octet-list "host/native/io.lisp"))
(defun fnn-string-octets (string)
  (declare (ignorable string))
  (harness-stub-reached 'fnn-string-octets "host/native/io.lisp"))
(defun fnn-workflow-commit-receipt-intent (journal intent canonical-release-callback)
  (declare (ignorable journal intent canonical-release-callback))
  (harness-stub-reached 'fnn-workflow-commit-receipt-intent "host/native/workflow.lisp"))
;;; ---- derived stubs: END ----

(defvar *trusted* t)
(defvar *calls* nil)
(defvar *refusal-line* nil)
(defun fnn-owner-core (name &rest arguments)
  ;; The D23 decision line is printed, never branched on.
  (when (eq name 'fn-owner-bp-source-decision-line)
    (return-from fnn-owner-core "direct principal=stub"))
  ;; A bare receipt: nothing to observe; the release line and detail are
  ;; printed and recorded, never branched on by the host.
  (when (eq name 'fn-owner-bp-receipt-signature-plan)
    (return-from fnn-owner-core nil))
  (when (eq name 'fn-owner-bp-release-line)
    (return-from fnn-owner-core "issuer-not-released carrier=stub issuer=x"))
  (when (eq name 'fn-owner-bp-receipt-release-detail)
    (return-from fnn-owner-core '(0)))
  ;; A refused request's line (fnn-bpnode-refusal-line, mission-signed-2):
  ;; ACL2's text, printed and never branched on; the arguments are kept.
  (when (eq name 'fn-owner-bp-request-refusal-line)
    (setq *refusal-line* arguments)
    (return-from fnn-owner-core "request refused reason=stub"))
  (unless (member name '(fn-owner-bp-request-trustedp
                         fn-owner-bp-receipt-gatep))
    (error "unexpected core call ~s" name))
  (push :trust *calls*)
  *trusted*)
(defun fnn-section-run (owner class cid admits classes name thunk)
  (declare (ignore owner class cid admits classes name))
  ;; An admin changed the current owner config after outer preflight.
  (setq *trusted* nil)
  (push :lock *calls*)
  (funcall thunk))
(defun fnn-bpapp-open-journal (&rest arguments)
  (declare (ignore arguments))
  (push :open-request-journal *calls*)
  :journal)
(defun fnn-app-journal-close (journal)
  (declare (ignore journal))
  (push :close-request-journal *calls*))
(defun fnn-octets-string (octets) (declare (ignore octets)) "id")
(defun fnn-octets (octets) octets)
(defun fnn-core (name &rest arguments)
  (declare (ignore arguments))
  (unless (eq name 'fn-id-hex-octets) (error "unexpected core call ~s" name))
  '(49 100))
(defun fnn-bpapp-accept-locked (&rest arguments)
  (declare (ignore arguments))
  (push :request-publication *calls*)
  (values :accepted :receipt))
(defun fnn-app-open (&rest arguments)
  (declare (ignore arguments))
  (push :open-receipt-journal *calls*)
  :journal)
(defun fnn-owner-service-store (owner) (declare (ignore owner)) :store)
(defun fnn-bpo-canonical-release (&rest arguments)
  (declare (ignore arguments)) nil)
(defun fnn-octet-list-p (x) (listp x))
;; BP-R17's developer-image busy witness is off here.
(defun fnn-bpnode-test-busy-p () nil)
(defun fnn-fault (&rest arguments) (error "fault ~s" arguments))
(defun fnn-out (control &rest arguments)
  (apply #'format t control arguments) (terpri))

(defun load-shipped (path kinds names)
  "Evaluate PATH's top-level KINDS forms that define one of NAMES."
  (with-open-file (stream path)
    (dolist (wanted names)
      (file-position stream 0)
      (let ((found nil))
        (loop for form = (read stream nil :eof) until (eq form :eof)
              when (and (consp form) (member (car form) kinds)
                        (eq (cadr form) wanted))
                do (eval form) (setq found t) (return))
        (unless found (error "~a: ~s not found" path wanted))))))

;; The global the request entry clears and the refusal line reads is the
;; owner's own (mission-signed-2), not a stand-in.
(load-shipped "host/native/owner.lisp" '(defvar) '(*fnn-owner-transit-detail*))
;; The request entry takes the owner through the BP node's declared section
;; (def-section fnn-quantum-bp, the shipped declaration and generator); the
;; stubbed fnn-section-run above is the lock.  ACL2's acceptance of the
;; declaration (books/failure-scope.lisp fn-fs-section-declp) is not in a
;; raw image: the stand-in accepts it.
(defun fn-fs-section-declp (actors classes admits)
  (declare (ignore actors classes admits)) t)
(load-shipped "host/native/owner.lisp" '(defvar) '(*fnn-sections*))
(load-shipped "host/native/owner.lisp" '(defun) '(fnn-section-declare))
(load-shipped "host/native/owner.lisp" '(defmacro) '(def-section))
(load-shipped "host/native/owner.lisp" '(def-section) '(fnn-quantum-bp))
;; The receipt result's journal cleanup is the shipped unwind macro.
(load-shipped "host/native/io.lisp" '(defmacro) '(fnn-unwind-cleanups))
;; fnn-bpnode-request-result is the deployed wrapper; since mission-signed-2
;; the decision is fnn-bpnode-request-result-1 and a refusal prints ACL2's
;; line through fnn-bpnode-refusal-line: all three are the shipped bodies.
(load-shipped "host/native/bp-node.lisp" '(defun)
              '(fnn-bpnode-source-decision fnn-bpnode-request-result
                fnn-bpnode-request-result-1 fnn-bpnode-refusal-line
                fnn-bpnode-receipt-observations fnn-bpnode-release-line
                fnn-bpnode-receipt-detail fnn-bpnode-receipt-result))

(let ((view '(nil nil :request (1) :ingress (2) "source" "dest")))
  (setq *trusted* t *calls* nil)
  (unless (equal (multiple-value-list
                  (fnn-bpnode-request-result :owner :root :destination
                                             :policy :issuer view :node))
                 '(:request-refused (0)))
    (error "revoked request was not refused"))
  (unless (equal (reverse *calls*)
                 '(:trust :open-request-journal :lock :trust
                   :close-request-journal))
    (error "request authorization/publication order ~s" (reverse *calls*)))
  ;; The refusal line was asked of ACL2 for this view, as refused, with the
  ;; transit detail the entry cleared.
  (unless (equal *refusal-line* (list view :refused nil))
    (error "refusal line arguments ~s" *refusal-line*)))

(let ((view '(nil nil :receipt (1) :ingress (2) "source" "dest")))
  (setq *trusted* t *calls* nil)
  (unless (equal (multiple-value-list
                  (fnn-bpnode-receipt-result :owner :root view :peer))
                 '(:receipt-refused (0)))
    (error "revoked receipt was not refused"))
  (unless (equal (reverse *calls*) '(:trust :lock :trust))
    (error "receipt authorization/publication order ~s" (reverse *calls*))))

(format t "native BP serialized admission: PASS~%")
