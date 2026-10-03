(in-package "ACL2")
(include-book "../../books/bp-node-budget-input")
; Decimal octets supplied directly, including explicit UTF-8 non-ASCII digits.
(defconst *bpnb-backoff* '(111 119 110 101 114 45 98 97 99 107 111 102 102 32 53))
(defconst *bpnb-retry* '(114 101 116 114 121 45 98 117 100 103 101 116 32 51))
(assert-event (equal (fn-bpnb-read nil) '(:rows nil nil)))
(assert-event (equal (fn-bpnb-read *bpnb-backoff*) '(:rows 5 nil)))
(assert-event (equal (fn-bpnb-read (append *bpnb-retry* '(10) *bpnb-backoff* '(10))) '(:rows 5 3)))
(assert-event (equal (fn-bpnb-read '(10 10)) '(:rows nil nil)))
; Complete duplicate hypotheses and conclusion for both literal theorems.
(assert-event
 (let ((rows '(:rows 5 3)) (line *bpnb-backoff*))
  (and (true-listp rows) (second rows) (fn-bpnb-row line nil)
       (equal (car (fn-bpnb-row line nil))
              '(111 119 110 101 114 45 98 97 99 107 111 102 102))
       (not (fn-bpnb-install-row line rows)))))
(assert-event
 (let ((rows '(:rows 5 3)) (line *bpnb-retry*))
  (and (true-listp rows) (third rows) (fn-bpnb-row line nil)
       (equal (car (fn-bpnb-row line nil))
              '(114 101 116 114 121 45 98 117 100 103 101 116))
       (not (fn-bpnb-install-row line rows)))))
; Removal of the installed-row premise: all retained hypotheses hold and
; another first row is admitted, contradicting the refused conclusion.
(assert-event
 (let ((rows '(:rows nil 3)) (line *bpnb-backoff*))
  (and (true-listp rows) (not (second rows)) (fn-bpnb-row line nil)
       (equal (car (fn-bpnb-row line nil))
              '(111 119 110 101 114 45 98 97 99 107 111 102 102))
       (fn-bpnb-install-row line rows))))
(assert-event
 (let ((rows '(:rows 5 nil)) (line *bpnb-retry*))
  (and (true-listp rows) (not (third rows)) (fn-bpnb-row line nil)
       (equal (car (fn-bpnb-row line nil))
              '(114 101 116 114 121 45 98 117 100 103 101 116))
       (fn-bpnb-install-row line rows))))
(assert-event (not (fn-bpnb-read (append *bpnb-backoff* '(10) *bpnb-backoff*))))
(assert-event (not (fn-bpnb-read (append *bpnb-retry* '(10) *bpnb-retry*))))
(assert-event (not (fn-bpnb-read (append (butlast *bpnb-backoff* 1) '(217 165)))))
(assert-event (not (fn-bpnb-read (append *bpnb-backoff* '(13 10)))))
(assert-event (not (fn-bpnb-read '(102 111 111 32 53))))
(assert-event (not (fn-bpnb-read (append (butlast *bpnb-backoff* 1) '(45 49)))))
(assert-event (not (fn-bpnb-read (append (butlast *bpnb-backoff* 1) (make-list 21 :initial-element 48)))))
(assert-event
 (let ((octets (make-list 257 :initial-element 10)))
  (and (< 256 (len octets)) (not (fn-bpnb-read octets)))))

; Removing the named-key premise: the retained installed-value premise holds
; but the other row is admitted, so refusal fails.
(assert-event
 (let ((rows '(:rows 5 nil)) (line *bpnb-retry*))
  (and (second rows)
       (not (equal (car (fn-bpnb-row line nil))
                   '(111 119 110 101 114 45 98 97 99 107 111 102 102)))
       (fn-bpnb-install-row line rows))))
(assert-event
 (let ((rows '(:rows nil 3)) (line *bpnb-backoff*))
  (and (third rows)
       (not (equal (car (fn-bpnb-row line nil))
                   '(114 101 116 114 121 45 98 117 100 103 101 116)))
       (fn-bpnb-install-row line rows))))
; Removal of read bound: ordinary valid short file is accepted.
(assert-event (and (not (< 256 (len *bpnb-backoff*)))
                   (fn-bpnb-read *bpnb-backoff*)))
