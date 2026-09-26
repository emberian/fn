; fn: `account list' names each row of the accounts slot by its kind (PKT-391).
;
; The accounts slot (books/config.lisp fn-cfg-accounts) holds three row
; kinds told apart by the row's mark alone: a pending invitation (mark 0,
; books/accounts.lisp), a redeemed account (mark 1) and a login binding
; (mark 2, PKT-221's rows, books/login-binding-live.lisp).
; books/accounts.lisp fn-acct-list-report printed every row that was not
; redeemed as `pending expires EXPIRY', so a binding row showed as a pending
; account with an empty expiry.  This book's report is the one
; books/native-live-status.lisp serves for `account list':
;
;   pending expires EXPIRY
;   redeemed LOGIN PRINCIPAL-HEX
;   binding LOGIN PRINCIPAL-HEX
;   unknown                         (a mark no writer makes)
;
; Never a digest or a verifier.  A book of its own so books/accounts.lisp
; (under books/owner's closure) does not change.
(in-package "ACL2")
(include-book "accounts")

(defun fn-acct-row-kind (row)
  (declare (xargs :guard t))
  (let ((mark (fn-cfg-row-n row)))
    (cond ((equal mark 0) :pending)
          ((equal mark 1) :redeemed)
          ((equal mark 2) :binding)
          (t :unknown))))

(defun fn-acct-kind-word (kind)
  (declare (xargs :guard t))
  (cond ((equal kind :pending) "pending ")
        ((equal kind :redeemed) "redeemed ")
        ((equal kind :binding) "binding ")
        (t "unknown")))

(defun fn-acct-list-text (x)
  (declare (xargs :guard t))
  (if (stringp x) x ""))

(defun fn-acct-list-fields (row kind)
  (declare (xargs :guard t))
  (cond ((equal kind :redeemed)
         (concatenate 'string (fn-acct-list-text (fn-cfg-row-b row)) " "
                      (fn-acct-hex-text
                       (fn-acct-local-principal
                        (fn-record-string-octets (fn-cfg-row-b row))))))
        ((equal kind :binding)
         (concatenate 'string (fn-acct-list-text (fn-cfg-row-a row)) " "
                      (fn-acct-list-text (fn-cfg-row-b row))))
        ((equal kind :pending)
         (concatenate 'string "expires " (fn-acct-list-text (fn-cfg-row-c row))))
        (t "")))

(defun fn-acct-list-line (row)
  (declare (xargs :guard t))
  (let ((kind (fn-acct-row-kind row)))
    (concatenate 'string (fn-acct-kind-word kind) (fn-acct-list-fields row kind)
                 (string #\Newline))))

(defun fn-acct-kinds-lines (rows)
  (declare (xargs :guard t))
  (if (consp rows)
      (concatenate 'string (fn-acct-list-line (car rows))
                   (fn-acct-kinds-lines (cdr rows)))
    ""))

(defun fn-acct-kinds-list-report (v)
  "The `account list' report over configuration value V."
  (declare (xargs :guard t))
  (fn-record-string-octets (fn-acct-kinds-lines (fn-cfg-accounts v))))

; The word each line starts with is its row's kind, decided by the mark
; alone: a binding row is listed as a binding, never as a pending account;
; only a mark-0 row is pending.
(defthm fn-acct-list-word-is-pending-only-for-a-pending-row
  (equal (equal (fn-acct-kind-word (fn-acct-row-kind row)) "pending ")
         (equal (fn-cfg-row-n row) 0)))
