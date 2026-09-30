(in-package "ACL2")
(include-book "../../books/owner-retire-settlement")

; Reachable scalar observations: timeout+queued work, definite writer/journal
; settlement with caller descriptor retained, then caller relinquishment.
(assert-event (and
 (equal (fn-ort-log-close-action :timeout 2 6 t) :held)
 (equal (fn-ort-store-close-action :held t nil) :held)
 (equal (fn-ort-service-start-action t t) :held)
 (equal (fn-ort-log-close-action :joined 0 0 nil) :joined)
 (equal (fn-ort-report-close-action :joined :closed) :joined)
 (equal (fn-ort-store-close-action :joined t t) :defer)
 (equal (fn-ort-store-close-action :joined t nil) :close)
 (equal (fn-ort-service-settlement-action :joined :closed) :joined)
 (equal (fn-ort-service-start-action nil nil) :start)))

; Complete antecedent and conclusion, per each new keystone.
(assert-event (let ((settlement :joined) (authority t) (caller nil))
 (and (equal (fn-ort-store-close-action settlement authority caller) :close)
      (equal settlement :joined) (not (equal authority nil)) (equal caller nil))))
(assert-event (let ((settlement :joined) (observation :closed))
 (and (equal (fn-ort-service-settlement-action settlement observation) :joined)
      (equal settlement :joined)
      (or (equal observation :closed) (equal observation :absent)))))
(assert-event (let ((writer nil) (authority nil))
 (and (equal (fn-ort-service-start-action writer authority) :start)
      (equal writer nil) (equal authority nil))))

; Removing the sole antecedent of each implication affirmatively makes it
; false and the conclusion false. These are scalar protocol witnesses, not
; installed producer graph or physical syscall claims.
(assert-event (let ((settlement :held) (authority t) (caller nil))
 (and (not (equal (fn-ort-store-close-action settlement authority caller) :close))
      (not (and (equal settlement :joined) (not (equal authority nil)) (equal caller nil))))))
(assert-event (let ((settlement :joined) (observation :uncertain))
 (and (not (equal (fn-ort-service-settlement-action settlement observation) :joined))
      (not (and (equal settlement :joined)
                (or (equal observation :closed) (equal observation :absent)))))))
(assert-event (let ((writer nil) (authority t))
 (and (not (equal (fn-ort-service-start-action writer authority) :start))
      (not (and (equal writer nil) (equal authority nil))))))

(assert-event (and
 (equal (fn-ort-service-claim-action nil nil nil) :start)
 (equal (fn-ort-service-claim-action nil t t) :start)
 (equal (fn-ort-service-claim-action nil t nil) :held)
 (equal (fn-ort-service-claim-action t t t) :held)))
(assert-event (let ((writer nil) (authority t) (owned t))
 (and (equal (fn-ort-service-claim-action writer authority owned) :start)
      (equal writer nil) (or (equal authority nil) (equal owned t)))))
(assert-event (let ((writer nil) (authority t) (owned nil))
 (and (not (equal (fn-ort-service-claim-action writer authority owned) :start))
      (not (and (equal writer nil) (or (equal authority nil) (equal owned t)))))))
