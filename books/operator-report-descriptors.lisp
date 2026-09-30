; Fixed descriptor spines borrow frozen report strings; no line is rendered here.
; Output/runtime staging and retained graph lifetime funding remain separate.
(in-package "ACL2")
(include-book "operator-report-fields-native-reference")

(defun fn-ord-peer (name undelivered dropped)
  (declare (xargs :guard (and (stringp name) (natp undelivered) (natp dropped))))
  (list (list :text "retire peer=") (list :text name)
        (list :text " undelivered=") (list :nat undelivered)
        (list :text " dropped=") (list :nat dropped) (list :text "
")))

(defun fn-ord-header (held reserved)
  (declare (xargs :guard (and (natp held) (natp reserved))))
  (list (list :text "obligations=") (list :nat held)
        (list :text " reserved=") (list :nat reserved) (list :text "
")))

(defun fn-ord-obligation (id forwardp charge subject)
  (declare (xargs :guard (and (stringp id) (natp charge) (stringp subject))))
  (list (list :text "obligation id=") (list :text id)
        (list :text " kind=") (list :text (if forwardp "forward" "archive"))
        (list :text " charge=") (list :nat charge)
        (list :text " subject=") (list :text subject) (list :text "
")))

(defun fn-ord-end (drainedp undelivered held)
  (declare (xargs :guard (and (natp undelivered) (natp held))))
  (list (list :text "retired state=") (list :text (if drainedp "drained" "deadline"))
        (list :text " undelivered=") (list :nat undelivered)
        (list :text " obligations=") (list :nat held) (list :text "
")))

(defun fn-ord-release ()
  (declare (xargs :guard t))
  (list (list :text "retire release: what stays is released only by `carry drop WORK --abandon REASON' on the stopped store
")))

(defthm fn-ord-peer-fields-valid
  (implies (and (stringp name) (natp undelivered) (natp dropped))
           (fn-orf-fieldsp (fn-ord-peer name undelivered dropped))))
(defthm fn-ord-header-fields-valid
  (implies (and (natp held) (natp reserved))
           (fn-orf-fieldsp (fn-ord-header held reserved))))
(defthm fn-ord-obligation-fields-valid
  (implies (and (stringp id) (natp charge) (stringp subject))
           (fn-orf-fieldsp (fn-ord-obligation id forwardp charge subject))))
(defthm fn-ord-end-fields-valid
  (implies (and (natp undelivered) (natp held))
           (fn-orf-fieldsp (fn-ord-end drainedp undelivered held))))
(defthm fn-ord-release-fields-valid (fn-orf-fieldsp (fn-ord-release)))

(in-theory (disable fn-ord-peer fn-ord-header fn-ord-obligation fn-ord-end fn-ord-release))
