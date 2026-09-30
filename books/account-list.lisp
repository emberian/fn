; fn: `account list' names each row of the accounts slot by its kind (PKT-391).
;
; The accounts slot (books/config.lisp fn-cfg-accounts) holds three row
; kinds told apart by the row's mark alone: a pending invitation (mark 0,
; books/accounts.lisp), a redeemed account (mark 1) and a login binding
; (mark 2, PKT-221's rows, books/login-binding-live.lisp).
; The older books/accounts.lisp fn-acct-list-report (removed, PKT-473)
; printed every row that was not redeemed as `pending expires EXPIRY', so a
; binding row showed as a pending account with an empty expiry.  This
; book's report is the one books/native-live-status.lisp serves for
; `account list':
;
;   pending expires EXPIRY          (EXPIRY an RFC 3339 UTC instant,
;                                    2026-10-06T12:00:00Z: row S6/Q10c,
;                                    the row keeps DTN milliseconds)
;   redeemed LOGIN PRINCIPAL-HEX
;   binding LOGIN PRINCIPAL-HEX
;   access LOGIN read READ post POST   (PRF-222, mark 3; LOGIN "" is
;                                       printed "(anonymous)")
;   moderator LOGIN GROUP           (P3: LOGIN moderates GROUP)
;   moderation GROUP QUEUE [ADDRESS]
;   consumer NAME account LOGIN     (PRF-234, mark 6)
;   deleted LOGIN                   (public-node-2, mark 7: the tombstone
;                                    `account delete' leaves)
;   unknown                         (a mark no writer makes)
;
; Never a digest or a verifier.
(in-package "ACL2")
(include-book "accounts")
(include-book "consumer-position")
; The DTN-millisecond civil conversion the DATE reply uses; every includer of
; this book (books/native-live-status.lisp) already has it in its world.
(include-book "nntp-responses")

(defun fn-acct-row-kind (row)
  (declare (xargs :guard t))
  (let ((mark (fn-cfg-row-n row)))
    (cond ((equal mark 0) :pending)
          ((equal mark 1) :redeemed)
          ((equal mark 2) :binding)
          ((equal mark 3) :access)
          ;; P3 (PRF-228): a moderator role and a group's moderation.
          ((equal mark 4) :moderator)
          ((equal mark 5) :moderation)
          ((equal mark 6) :consumer)
          ((equal mark 7) :deleted)
          (t :unknown))))

(defun fn-acct-kind-word (kind)
  (declare (xargs :guard t))
  (cond ((equal kind :pending) "pending ")
        ((equal kind :redeemed) "redeemed ")
        ((equal kind :binding) "binding ")
        ((equal kind :access) "access ")
        ((equal kind :moderator) "moderator ")
        ((equal kind :moderation) "moderation ")
        ((equal kind :consumer) "consumer ")
        ((equal kind :deleted) "deleted ")
        (t "unknown")))

(defun fn-acct-list-text (x)
  (declare (xargs :guard t))
  (if (stringp x) x ""))

; Row S6 / Q10c: a pending row's expiry printed as the RFC 3339 UTC instant
; (section 5.6's date-time with the Z offset) its DTN milliseconds name,
; seconds truncated.  A text that is not an expiry the configuration admits
; (fn-cfg-account-expiryp), or one past year 9999, prints as kept.
(defun fn-acct-expiry-utc-octets (ms)
  (declare (xargs :guard t))
  (let ((civil (fn-nntp-dtn-civil ms)))
    (append (fn-nntp-pad4 (fn-nntp-civil-year civil)) (list 45)
            (fn-nntp-pad2 (fn-nntp-civil-month civil)) (list 45)
            (fn-nntp-pad2 (fn-nntp-civil-day civil)) (list 84)
            (fn-nntp-pad2 (fn-nntp-civil-hour civil)) (list 58)
            (fn-nntp-pad2 (fn-nntp-civil-minute civil)) (list 58)
            (fn-nntp-pad2 (fn-nntp-civil-second civil)) (list 90))))

(defun fn-acct-expiry-text (text)
  (declare (xargs :guard t))
  (if (and (fn-cfg-account-expiryp text)
           (let ((year (fn-nntp-civil-year
                        (fn-nntp-dtn-civil (fn-cfg-account-expiry text)))))
             (and (natp year) (<= year *fn-nntp-max-rendered-year*))))
      (fn-record-octets-string
       (fn-acct-expiry-utc-octets (fn-cfg-account-expiry text)))
    (fn-acct-list-text text)))

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
         (concatenate 'string "expires " (fn-acct-expiry-text (fn-cfg-row-c row))))
        ((equal kind :access)
         (concatenate 'string
                      (if (equal (fn-cfg-row-a row) "")
                          "(anonymous)"
                        (fn-acct-list-text (fn-cfg-row-a row)))
                      " read " (fn-acct-list-text (fn-cfg-row-b row))
                      " post " (fn-acct-list-text (fn-cfg-row-c row))))
        ; moderator LOGIN GROUP
        ((equal kind :moderator)
         (concatenate 'string (fn-acct-list-text (fn-cfg-row-a row)) " "
                      (fn-acct-list-text (fn-cfg-row-b row))))
        ; moderation GROUP QUEUE [ADDRESS]
        ((equal kind :moderation)
         (concatenate 'string (fn-acct-list-text (fn-cfg-row-a row)) " "
                      (fn-acct-list-text (fn-cfg-row-b row))
                      (if (equal (fn-cfg-row-c row) "") ""
                        (concatenate 'string " "
                                     (fn-acct-list-text (fn-cfg-row-c row))))))
        ((equal kind :consumer)
         (concatenate 'string (fn-acct-list-text (fn-cfg-row-a row))
                      " account " (fn-acct-list-text (fn-cfg-row-b row))))
        ((equal kind :deleted) (fn-acct-list-text (fn-cfg-row-b row)))
        (t "")))

(defun fn-acct-list-line (row)
  (declare (xargs :guard t))
  (let ((kind (fn-acct-row-kind row)))
    (concatenate 'string (fn-acct-kind-word kind) (fn-acct-list-fields row kind)
                 (string #\Newline))))

; The report's walk over the accounts table executes by a loop (lane
; depth-debt, PRF-919): the table is operator data with no fixed cap (D27),
; and a recursion one control-stack frame per row could exhaust the
; 1,024 KiB stack.  The loop collects the lines' characters reversed onto
; ACC (each line copied once) and the :exec makes the string once.
(defun fn-acct-kinds-lines-loop (rows acc)
  (declare (xargs :guard t))
  (if (consp rows)
      (fn-acct-kinds-lines-loop
       (cdr rows)
       (fn-ag-rev-onto (coerce (fn-acct-list-line (car rows)) 'list) acc))
    (fn-ag-rev-onto acc nil)))

(defun fn-acct-kinds-lines (rows)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (if (consp rows)
                  (concatenate 'string (fn-acct-list-line (car rows))
                               (fn-acct-kinds-lines (cdr rows)))
                "")
       :exec (coerce (fn-acct-kinds-lines-loop rows nil) 'string)))

(local
 (defthm fn-acct-rev-onto-of-rev-onto
   (equal (fn-ag-rev-onto (fn-ag-rev-onto x acc) y)
          (fn-ag-rev-onto acc (append x y)))))

(defthm fn-acct-kinds-lines-loop-is-rev-onto
  (equal (fn-acct-kinds-lines-loop rows acc)
         (fn-ag-rev-onto acc (coerce (fn-acct-kinds-lines rows) 'list)))
  :hints (("Goal" :induct (fn-acct-kinds-lines-loop rows acc)
                  :in-theory (disable fn-acct-list-line))))

(local
 (defthm fn-acct-character-listp-of-rev-onto
   (implies (and (character-listp x) (character-listp acc))
            (character-listp (fn-ag-rev-onto x acc)))))

(verify-guards fn-acct-kinds-lines
  :hints (("Goal" :in-theory (disable fn-acct-list-line))))

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

; -----------------------------------------------------------------------------
; Row Q10c: `consumer show' lists the consumer bindings (mark 6) alone.  The
; review's walk found it printed the whole account list, pending expiries
; and redeemed principals included (the plan was `account list''s).  The
; report is the account list's own line for each consumer row, in row order,
; and nothing for any other row; it executes by the same loop as the account
; list (the table has no row cap, D27).

(defun fn-acct-consumer-rows (rows)
  "The consumer rows of ROWS, in order (the logical filter the report is of)."
  (declare (xargs :guard t))
  (if (consp rows)
      (if (equal (fn-acct-row-kind (car rows)) :consumer)
          (cons (car rows) (fn-acct-consumer-rows (cdr rows)))
        (fn-acct-consumer-rows (cdr rows)))
    nil))

(defun fn-acct-consumer-line (row)
  (declare (xargs :guard t))
  (if (equal (fn-acct-row-kind row) :consumer) (fn-acct-list-line row) ""))

(defun fn-acct-consumer-lines-loop (rows acc)
  (declare (xargs :guard t))
  (if (consp rows)
      (fn-acct-consumer-lines-loop
       (cdr rows)
       (fn-ag-rev-onto (coerce (fn-acct-consumer-line (car rows)) 'list) acc))
    (fn-ag-rev-onto acc nil)))

(defun fn-acct-consumer-lines (rows)
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic (if (consp rows)
                  (concatenate 'string (fn-acct-consumer-line (car rows))
                               (fn-acct-consumer-lines (cdr rows)))
                "")
       :exec (coerce (fn-acct-consumer-lines-loop rows nil) 'string)))

(defthm fn-acct-consumer-lines-loop-is-rev-onto
  (equal (fn-acct-consumer-lines-loop rows acc)
         (fn-ag-rev-onto acc (coerce (fn-acct-consumer-lines rows) 'list)))
  :hints (("Goal" :induct (fn-acct-consumer-lines-loop rows acc)
                  :in-theory (disable fn-acct-consumer-line))))

(verify-guards fn-acct-consumer-lines
  :hints (("Goal" :in-theory (disable fn-acct-consumer-line))))

(defun fn-acct-consumers-list-report (v)
  "The `consumer show' report over configuration value V."
  (declare (xargs :guard t))
  (fn-record-string-octets (fn-acct-consumer-lines (fn-cfg-accounts v))))

; KEYSTONE (row Q10c).  `consumer show' prints exactly the lines `account
; list' prints for the consumer rows, in order: the account list's report
; over the consumer rows alone.  No pending, redeemed, binding, access,
; moderation or deleted row reaches it.
(defthm fn-acct-consumer-lines-are-the-list-lines-of-the-consumer-rows
  (equal (fn-acct-consumer-lines rows)
         (fn-acct-kinds-lines (fn-acct-consumer-rows rows)))
  :hints (("Goal" :in-theory (disable fn-acct-list-line fn-acct-row-kind))))

(defthm fn-acct-consumers-list-report-is-the-list-report-of-the-consumer-rows
  (equal (fn-acct-consumers-list-report v)
         (fn-record-string-octets
          (fn-acct-kinds-lines (fn-acct-consumer-rows (fn-cfg-accounts v)))))
  :hints (("Goal" :in-theory '(fn-acct-consumers-list-report
                               fn-acct-consumer-lines-are-the-list-lines-of-the-consumer-rows))))

(defthm fn-acct-consumer-rows-are-consumers
  (implies (member-equal row (fn-acct-consumer-rows rows))
           (equal (fn-acct-row-kind row) :consumer)))

(defthm fn-acct-consumer-rows-keep-every-consumer
  (implies (and (member-equal row rows)
                (equal (fn-acct-row-kind row) :consumer))
           (member-equal row (fn-acct-consumer-rows rows))))
