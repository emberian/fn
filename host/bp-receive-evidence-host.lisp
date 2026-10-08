; Program bridge for native BP receive evidence allocation and recovery.
(in-package "ACL2")
(include-book "../books/bp-receive-evidence")
(include-book "../books/bp-evidence-host-names")

(defun fn-bpn-host-evidence-max-entries () (fn-bpn-evidence-max-entries))

(definterface fn-bpn-host-evidence-max-entries
  :class ::ideal)
(defun fn-bpn-host-evidence-directory-name () *fn-bpn-evidence-directory-name*)

(definterface fn-bpn-host-evidence-directory-name
  :class ::ideal)
(defun fn-bpn-host-evidence-recover (entries)
  (fn-bpn-evidence-recover entries))

(definterface fn-bpn-host-evidence-recover
  :class ::ideal)
(defun fn-bpn-host-evidence-readyp (st)
  (if (fn-bpn-evidence-statep st) t nil))

(definterface fn-bpn-host-evidence-readyp
  :class ::ideal)
(defun fn-bpn-host-evidence-authorize (st outcome lock-ownedp
                                             wire-absentp result-absentp)
  ; An exact alias (definterface :delegates): the decision is the books'.
  (declare (xargs :guard t))
  (fn-bpn-evidence-authorize st outcome lock-ownedp
                             wire-absentp result-absentp))

(definterface fn-bpn-host-evidence-authorize
  ; an exact alias; the callee's keystone is PRF-1007
  ; (fn-bpn-evidence-authorize-admits-exactly-the-locked-next-identity)
  :class :common-lisp-compliant
  :delegates fn-bpn-evidence-authorize)
(defun fn-bpn-host-evidence-next-wire-name (st)
  (if (fn-bpn-evidence-statep st)
      (fn-bpn-evidence-next-wire-name st)
    nil))

(definterface fn-bpn-host-evidence-next-wire-name
  :class ::ideal)
; fn-bpn-host-evidence-next-result-name is books/bp-evidence-host-names.lisp's
; (guard-verified, with the keystone PRF-1032).
(defun fn-bpn-host-evidence-operationp (operation)
  ; An exact alias (definterface :delegates); the recognizer is boolean.
  (fn-bpn-evidence-operationp operation))

(definterface fn-bpn-host-evidence-operationp
  ; an exact alias of the boolean recognizer; the keystone naming it is
  ; PRF-1007 (fn-bpn-evidence-authorize-admits-exactly-the-locked-next-identity)
  :class ::ideal
  :delegates fn-bpn-evidence-operationp)
(defun fn-bpn-host-evidence-operation-wire-name (operation)
  (fn-bpn-evidence-operation-wire-name operation))

(definterface fn-bpn-host-evidence-operation-wire-name
  :class ::ideal)
(defun fn-bpn-host-evidence-operation-result-name (operation)
  (fn-bpn-evidence-operation-result-name operation))

(definterface fn-bpn-host-evidence-operation-result-name
  :class ::ideal)
(defun fn-bpn-host-evidence-operation-wire-publication (operation)
  (fn-bpn-evidence-operation-wire-publication operation))

(definterface fn-bpn-host-evidence-operation-wire-publication
  :class ::ideal)
(defun fn-bpn-host-evidence-operation-result-publication (operation)
  (fn-bpn-evidence-operation-result-publication operation))

(definterface fn-bpn-host-evidence-operation-result-publication
  :class ::ideal)
(defun fn-bpn-host-evidence-operation-successor (operation)
  (fn-bpn-evidence-operation-successor operation))

(definterface fn-bpn-host-evidence-operation-successor
  :class ::ideal)
