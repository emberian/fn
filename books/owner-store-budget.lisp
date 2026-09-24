; fn: the served article prepare carries the Store's transaction budget (M5).
;
; host/owner-host.lisp `fn-owner-prepare' installs `fn-sbud-prepare' of the
; configured owner, the prepared record and the budget ACL2 derived at open
; from the persisted profile (`fn-sbud-budget', books/store-budget.lisp).  At
; or over the budget it is the identity and the owner answers :unaffordable
; (`fn-sbud-refusal-kind'), which `fn-post-store-refusal-line' renders as
; "441 posting failed; the store has no capacity for this article".  Below
; it, it is `fn-opc-prepare'.
(in-package "ACL2")
(include-book "store-budget")
(include-book "owner-prepare-correspondence")

(defun fn-sbud-oc-store (oc)
  (declare (xargs :guard t))
  (fn-own-store (fn-ocfg-owner oc)))

(defun fn-sbud-prepare (oc record budget)
  (declare (xargs :guard (fn-sn-statep (fn-sbud-oc-store oc))))
  (if (fn-sbud-admitp budget (fn-sbud-used (fn-sbud-oc-store oc)))
      (fn-opc-prepare oc record)
    oc))

; The word the owner reports for a prepare that left the owner unchanged.
(defun fn-sbud-refusal-kind (oc budget)
  (declare (xargs :guard t))
  (if (fn-sbud-admitp budget (fn-sbud-used (fn-sbud-oc-store oc)))
      :refused
    :unaffordable))


; -----------------------------------------------------------------------------
; Keystones over the called prepare

; At or over the budget the called prepare is the identity: nothing staged,
; nothing reserved, every other component of the configured owner kept.
(defthm fn-sbud-prepare-refuses-at-budget
  (implies (<= budget (fn-sbud-used (fn-sbud-oc-store oc)))
           (equal (fn-sbud-prepare oc record budget) oc)))

; Below the budget the gate is transparent: the called prepare is exactly the
; configured-owner prepare whose correspondence to the owner event is
; `fn-opc-prepare-equals-owner-event-under-relation'.
(defthm fn-sbud-prepare-below-budget-is-the-owner-prepare
  (implies (and (natp budget)
                (< (fn-sbud-used (fn-sbud-oc-store oc)) budget))
           (equal (fn-sbud-prepare oc record budget)
                  (fn-opc-prepare oc record))))

; The refusal names its reason: a budget refusal is :unaffordable, and the
; word is :refused only when the budget admitted the record.
(defthm fn-sbud-refusal-kind-at-budget-is-unaffordable
  (implies (<= budget (fn-sbud-used (fn-sbud-oc-store oc)))
           (equal (fn-sbud-refusal-kind oc budget) :unaffordable)))

(in-theory (disable fn-sbud-prepare fn-sbud-refusal-kind))
