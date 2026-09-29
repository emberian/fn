; Teeth for books/account-list.lisp (PKT-391): `account list' names a
; login-binding row (PKT-221, mark 2) as a binding, never as a pending
; account.  The fixture is tests/acl2/accounts-tests.lisp's: an invitation,
; its redemption by robin, then robin's binding published (code 17).
(in-package "ACL2")
(include-book "../../books/account-list")
(include-book "../../books/crypto-attach")

(defconst *alt-code* (fn-record-string-octets "k3y-friend-0001-7f3a"))
(defconst *alt-login* (fn-record-string-octets "robin"))
(defconst *alt-password* (fn-record-string-octets "correct horse"))
(defconst *alt-salt* (make-list 16 :initial-element 7))
(defconst *alt-stamp* (fn-clock-observation 5 1700000000 2 t))
(defmacro alt-v1 ()
  '(fn-cfg-apply-delta (fn-cfg-empty-value) 1 *alt-stamp*
                       (fn-cfg-account-invite (fn-acct-code-digest-text *alt-code*)
                                              "operator" "2000000000")))
(defmacro alt-v2 ()
  '(fn-cfg-apply-delta (alt-v1) 2 *alt-stamp*
                       (fn-acct-plan-delta
                        (fn-acct-redeem-plan (alt-v1) *alt-stamp* *alt-code*
                                             *alt-login* *alt-password*
                                             *alt-salt* nil))))
(defconst *alt-hex* (coerce (make-list 64 :initial-element #\a) 'string))
(defmacro alt-v3 ()
  '(fn-cfg-apply-delta (alt-v2) 3 *alt-stamp*
                       (fn-cfg-login-binding "robin" *alt-hex*)))
(assert-event (null (fn-cfg-delta-reason (alt-v2) 3 *alt-stamp* 0 0
                                         (fn-cfg-login-binding "robin" *alt-hex*))))

; The pending row, then after the redemption and the binding: one redeemed
; line and one binding line, no pending line, no digest.
(assert-event
 (equal (subseq (fn-record-octets-string (fn-acct-kinds-list-report (alt-v1))) 0 16)
        "pending expires "))
(assert-event
 (let ((text (fn-record-octets-string (fn-acct-kinds-list-report (alt-v3)))))
   (and (stringp text)
        (equal (subseq text 0 15) "redeemed robin ")
        (search (concatenate 'string "binding robin " *alt-hex* (string #\Newline))
                text)
        (not (search "pending" text))
        (not (search (fn-acct-code-digest-text *alt-code*) text)))))
; The older report (books/accounts.lisp fn-acct-list-report, removed by
; PKT-473) listed the binding row as `pending expires ' with an empty expiry;
; this report never does.
(assert-event
 (not (search (concatenate 'string "pending expires " (string #\Newline))
              (fn-record-octets-string (fn-acct-kinds-list-report (alt-v3))))))

; fn-acct-list-word-is-pending-only-for-a-pending-row, both sides.
(assert-event
 (let ((rows (fn-cfg-accounts (alt-v3))))
   (and (equal (len rows) 2)
        (equal (fn-cfg-row-n (cadr rows)) 2)
        (equal (fn-acct-kind-word (fn-acct-row-kind (cadr rows))) "binding "))))
(assert-event
 (let ((row (car (fn-cfg-accounts (alt-v1)))))
   (and (equal (fn-cfg-row-n row) 0)
        (equal (fn-acct-kind-word (fn-acct-row-kind row)) "pending "))))

; public-node-2: a tombstone (mark 7) is listed as `deleted LOGIN', never
; with its digest.
(assert-event (equal (fn-acct-list-line
                      (fn-cfg-row-make "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
                                       "robin" "" 7))
                     (concatenate 'string "deleted robin" (string #\Newline))))

; Row S6 / Q10c: a pending row's expiry is printed as the RFC 3339 UTC
; instant its DTN milliseconds name (2,000,000 s after 2000-01-01), never as
; the raw milliseconds.
(assert-event
 (equal (fn-record-octets-string (fn-acct-kinds-list-report (alt-v1)))
        (concatenate 'string "pending expires 2000-01-24T03:33:20Z"
                     (string #\Newline))))
(assert-event (equal (fn-acct-expiry-text "0") "2000-01-01T00:00:00Z"))
; 2000 is a leap year: 366 days after the epoch is 2001-01-01.
(assert-event (equal (fn-acct-expiry-text "31622400000") "2001-01-01T00:00:00Z"))
; A text the configuration would not admit as an expiry prints as kept.
(assert-event (equal (fn-acct-expiry-text "") ""))
(assert-event (equal (fn-acct-expiry-text "soon") "soon"))
; Past year 9999 the instant is not rendered (RFC 3339's four-digit year).
(assert-event (equal (fn-acct-expiry-text "99999999999999999999")
                     "99999999999999999999"))
