(in-package "ACL2")
(include-book "../books/ninep-transport")
(include-book "../books/definterface")

; No parsed fields, message limit or cursor are supplied by native STEP.
; Provisioning is an internal constructor, separate from genuine admission.
(defun fn-ninep-transport-step (fn-ninep-transport fn-octets fn-ninep-session state)
 (declare (xargs :stobjs (fn-ninep-transport fn-octets fn-ninep-session state) :guard t))
 (mv-let (action fn-ninep-transport fn-ninep-session)
  (fn-9pt-current-step fn-ninep-transport fn-octets fn-ninep-session)
  (mv action fn-ninep-transport fn-ninep-session state)))

(defun fn-ninep-transport-reply-returned (fn-ninep-transport fn-octets fn-ninep-session state)
 (declare (xargs :stobjs (fn-ninep-transport fn-octets fn-ninep-session state) :guard t))
 (mv-let (word fn-ninep-transport fn-octets fn-ninep-session)
  (fn-9pt-current-reply-returned fn-ninep-transport fn-octets fn-ninep-session)
  (mv word fn-ninep-transport fn-octets fn-ninep-session state)))

(defthm fn-ninep-transport-step-complete-source-boundary
 (let ((result (fn-9pt-current-step fn-ninep-transport fn-octets fn-ninep-session)))
  (equal (fn-ninep-transport-step fn-ninep-transport fn-octets fn-ninep-session state)
         (list (mv-nth 0 result) (mv-nth 1 result) (mv-nth 2 result) state)))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d (fn-ninep-transport-step) (fn-9pt-current-step)))))

(defthm fn-ninep-transport-return-complete-source-boundary
 (let ((result (fn-9pt-current-reply-returned fn-ninep-transport fn-octets fn-ninep-session)))
  (equal (fn-ninep-transport-reply-returned fn-ninep-transport fn-octets fn-ninep-session state)
         (list (mv-nth 0 result) (mv-nth 1 result) (mv-nth 2 result) (mv-nth 3 result) state)))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d (fn-ninep-transport-reply-returned) (fn-9pt-current-reply-returned)))))

(definterface fn-ninep-transport-step :class :common-lisp-compliant)
(definterface fn-ninep-transport-reply-returned :class :common-lisp-compliant)
