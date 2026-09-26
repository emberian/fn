;;; Exercise the shipped BP application entry with config changing before the
;;; serialized decision.  No Store/FNRJ mutation may follow a revoked trust.
(require :sb-posix)
(require :sb-bsd-sockets)
(defpackage "ACL2" (:use "CL"))
(in-package "ACL2")

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
(defun fnn-owner-serialized (owner cid thunk)
  (declare (ignore owner cid))
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
(defun fnn-workflow-accept-receipt-octets (&rest arguments)
  (declare (ignore arguments))
  (push :receipt-publication *calls*)
  "receipt")
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
