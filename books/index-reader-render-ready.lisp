; Bounded readonly SAME-slot render-root presence, not source authorization.
; The full current-plan/initial-root trace frame is carried by actual producer
; and coupled driver theorems. No deep plan equality or host tuple setter.
(in-package "ACL2")
(include-book "index-backing-provider")
(include-book "served-render-holder")

(defun fn-irc-context-custody (context)
 (declare (xargs :guard t)) (fn-omk-at 9 context))


; The next actual driver requires the real installed root. This bounded gate
; reads fixed metadata only; the full current-plan/initial-trace correspondence
; is established by installation and preserved by coupled driver actions.
(defun fn-irc-slot-render-ready-p (token fn-ibp-query-segment fn-render-holder)
 (declare (xargs :stobjs (fn-ibp-query-segment fn-render-holder)
                 :guard (fn-ibp-query-tokenp token)))
 (let* ((slot (nth 3 token))
        (context (fn-ibp-qs-inputsi slot fn-ibp-query-segment))
        (row (fn-irc-context-custody context))
        (root (fn-omk-at 8 row))
        (control (fn-ibp-qs-controlsi slot fn-ibp-query-segment))
        (admission (fn-ibp-qs-admissionsi slot fn-ibp-query-segment)))
  (and (fn-ibp-query-slot-livep token fn-ibp-query-segment)
       (fn-omk-widthp context 10)
       (fn-omk-widthp row 12) (eq (fn-omk-at 0 row) :receiver-custody)
       (eq (fn-omk-at 6 row) :render-owned)
       (equal (fn-omk-at 7 row) token)
       (fn-omk-widthp root 7) (eq (fn-omk-at 0 root) :receiver-render-root)
       (fn-omk-at 1 root) (equal (fn-omk-at 4 root) token)
       (fn-rh-live fn-render-holder) (equal (fn-rh-query fn-render-holder) token)
       (fn-omk-widthp control 9) (eq (fn-omk-at 0 control) :fn-ibr)
       (equal (fn-omk-at 1 control) (nth 1 token))
       (equal (fn-omk-at 2 control) (nth 4 token))
       (eq (fn-omk-at 2 admission) :active))))

