; Teeth for books/native-admin-peer-budget.lisp (PRF-179, PKT-211): `peer
; list' renders a peer's carriage budget.  Per keystone a reachable witness
; asserting the antecedent and the conclusion, and one must-fail per
; hypothesis showing the conclusion failing without it.
(in-package "ACL2")
(include-book "../../books/native-admin")
(include-book "std/testing/must-fail" :dir :system)

(defun napbt-argv (words)
  (if (consp words)
      (cons (fn-record-string-octets (car words)) (napbt-argv (cdr words)))
    nil))

; The operator's words: `peer add far ...' then `peer budget far 1048576 16'.
(defconst *napbt-add*
  (fn-native-admin-plan
   (napbt-argv '("peer" "add" "far" "far.example" "192.0.2.44" "1119"
                 "fn.*" "fn.*" "192.0.2.44" "true" "starttls" "news.example"
                 "/etc/fn/peer-ca.pem"))))
(assert-event (equal (fn-native-admin-result-status *napbt-add*) :accepted))
(defconst *napbt-budget*
  (fn-native-admin-plan (napbt-argv '("peer" "budget" "far" "1048576" "16"))))
(assert-event (equal (fn-native-admin-result-status *napbt-budget*) :accepted))
(defconst *napbt-budget-rows* (fn-native-admin-result-value *napbt-budget*))
(defconst *napbt-peers*
  (append (fn-cfg-peer-rows (fn-native-admin-result-peer *napbt-add*))
          *napbt-budget-rows*))
(defconst *napbt-group* (fn-cfg-rows-with-key *napbt-peers* "far"))

; The report: the older line, then the two budget words, then the newline.
(assert-event
 (equal (fn-native-admin-peer-budget-report *napbt-peers*)
        (append (fn-record-string-octets
                 "far path-identity=far.example address=192.0.2.44 port=1119 security=starttls inbound=fn.* outbound=fn.* auth=source-address:192.0.2.44 budget-octets=1048576 budget-count=16")
                (list 10))))
; A peer without budget rows: exactly the older report.
(defconst *napbt-plain* (fn-cfg-peer-rows (fn-native-admin-result-peer *napbt-add*)))
(assert-event (equal (fn-native-admin-peer-budget-report *napbt-plain*)
                     (fn-native-admin-peer-report *napbt-plain*)))
; `peer list' is this report (the query plan of `peer list').
(assert-event
 (equal (fn-native-admin-query-report
         (fn-native-admin-plan (napbt-argv '("peer" "list")))
         (list nil nil nil nil nil *napbt-peers*))
        (fn-native-admin-peer-budget-report *napbt-peers*)))

; fn-native-admin-peer-budget-decode-reads-the-configured-budget: antecedent
; (a budget; a tail that is no digit) and conclusion.
(assert-event (equal (fn-pcb-budget-of-rows *napbt-group*) '(256 16)))
(assert-event (not (fn-napb-digitp 10)))
(assert-event
 (equal (fn-native-admin-peer-budget-decode
         (append (fn-native-admin-peer-budget-octets *napbt-group*) (list 10)))
        (list 1048576 16 (list 10))))
; Without a budget: the rows of the plain peer decode to no budget.
(assert-event (not (fn-pcb-budget-of-rows *napbt-plain*)))
(must-fail
 (assert-event
  (equal (fn-native-admin-peer-budget-decode
          (append (fn-native-admin-peer-budget-octets *napbt-plain*) (list 10)))
         (list (* *fn-id-charge-page-octets*
                  (car (fn-pcb-budget-of-rows *napbt-plain*)))
               (cadr (fn-pcb-budget-of-rows *napbt-plain*))
               (list 10)))))
; Without a non-digit tail: a digit after the count is read into it.
(assert-event (fn-napb-digitp 55))
(must-fail
 (assert-event
  (equal (fn-native-admin-peer-budget-decode
          (append (fn-native-admin-peer-budget-octets *napbt-group*) (list 55 10)))
         (list 1048576 16 (list 55 10)))))

; A large budget renders every digit (no field width): 4294967295 pages.
(defconst *napbt-big*
  (fn-native-admin-plan
   (napbt-argv '("peer" "budget" "far" "17592186040320" "4294967295"))))
(assert-event (equal (fn-native-admin-result-status *napbt-big*) :accepted))
(assert-event
 (equal (fn-native-admin-peer-budget-decode
         (append (fn-native-admin-peer-budget-octets
                  (fn-native-admin-result-value *napbt-big*))
                 (list 10)))
        (list 17592186040320 4294967295 (list 10))))

; fn-native-admin-peer-extra-decode-reads-past-the-budget: a clean group
; with a carried principal and a budget.
(defconst *napbt-carries*
  (fn-native-admin-plan (napbt-argv (list "peer" "carries" "far"
                                          (coerce (make-list 64 :initial-element #\a)
                                                  'string)))))
(assert-event (equal (fn-native-admin-result-status *napbt-carries*) :accepted))
(defconst *napbt-rich*
  (append *napbt-group* (fn-native-admin-result-value *napbt-carries*)))
(assert-event (fn-native-admin-peer-extra-cleanp *napbt-rich*))
(assert-event (consp (fn-native-admin-peer-slot-values *napbt-rich* "carries-principal")))
(assert-event
 (equal (fn-native-admin-peer-extra-decode
         (append (fn-native-admin-peer-extra-octets *napbt-rich*)
                 (fn-native-admin-peer-budget-octets *napbt-rich*)
                 (list 10)))
        (list (list (fn-record-string-octets
                     (coerce (make-list 64 :initial-element #\a) 'string)))
              nil nil
              (append (fn-native-admin-peer-budget-octets *napbt-rich*)
                      (list 10)))))
; Without a clean group: a carried value with a space in it (written by no
; verb) splits, and the reader no longer returns the rows' values.
(defconst *napbt-dirty*
  (append *napbt-group* (list (fn-cfg-row-make "far" "carries-principal" "a b" 0))))
(assert-event (not (fn-native-admin-peer-extra-cleanp *napbt-dirty*)))
(must-fail
 (assert-event
  (equal (fn-native-admin-peer-extra-decode
          (append (fn-native-admin-peer-extra-octets *napbt-dirty*)
                  (fn-native-admin-peer-budget-octets *napbt-dirty*)
                  (list 10)))
         (list (fn-native-admin-peer-label-octets-list
                (fn-native-admin-peer-slot-values *napbt-dirty* "carries-principal"))
               nil nil
               (append (fn-native-admin-peer-budget-octets *napbt-dirty*)
                       (list 10))))))

; fn-native-admin-peer-budget-row-octets-extends-the-older-line (no
; hypotheses): at the witness group.
(defconst *napbt-p* (fn-cfg-peer-find "far" *napbt-peers*))
(assert-event (consp *napbt-p*))
(assert-event
 (let ((older (fn-native-admin-peer-row-octets *napbt-p* *napbt-group*)))
   (equal (fn-native-admin-peer-budget-row-octets *napbt-p* *napbt-group*)
          (append (take (1- (len older)) older)
                  (fn-native-admin-peer-budget-octets *napbt-group*)
                  (list 10)))))
