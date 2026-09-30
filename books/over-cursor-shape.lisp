; The original six-field range and fixed protocol framing vocabulary.
(in-package "ACL2")
(include-book "nntp-session")
(include-book "protocol-table")

(defun fn-ovw-status (text)
  (declare (xargs :guard t))
  (fn-nntp-crlf (fn-nntp-string-octets text)))

; (GROUP K TOP V LEGACYP OWEDP): the next number to probe, the range's last
; number (clamped once, at the start), the pinned view, XOVER or OVER, and
; whether the status line is still owed (no line sent yet).
(defun fn-ovw-cursor (group k top v legacyp owedp)
  (declare (xargs :guard t))
  (list group k top v legacyp owedp))

(defun fn-ovw-cursorp (cur)
  (declare (xargs :guard t))
  (and (true-listp cur) (natp (nth 3 cur))))

(defthm fn-ovw-cursor-fields
  (and (equal (nth 0 (fn-ovw-cursor group k top v legacyp owedp)) group)
       (equal (nth 1 (fn-ovw-cursor group k top v legacyp owedp)) k)
       (equal (nth 2 (fn-ovw-cursor group k top v legacyp owedp)) top)
       (equal (nth 3 (fn-ovw-cursor group k top v legacyp owedp)) v)
       (equal (nth 4 (fn-ovw-cursor group k top v legacyp owedp)) legacyp)
       (equal (nth 5 (fn-ovw-cursor group k top v legacyp owedp)) owedp)))

(defun fn-ovw-empty-text (legacyp)
  (declare (xargs :guard t))
  (if legacyp (fn-proto-text * :none-selected) (fn-proto-text * :empty-range)))

