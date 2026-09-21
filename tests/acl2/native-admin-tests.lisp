; Teeth for the bounded native administrative command plan.
(in-package "ACL2")
(include-book "../../books/native-admin")

(defun fn-na-test-argv (words)
  (if (consp words)
      (cons (fn-record-string-octets (car words))
            (fn-na-test-argv (cdr words)))
    nil))

(defconst *fn-na-create*
  (fn-native-admin-plan (fn-na-test-argv '("group" "create" "fn.admin"))))
(assert-event (equal (fn-native-admin-result-status *fn-na-create*) :accepted))
(assert-event (equal (fn-native-admin-result-kind *fn-na-create*) :create-group))
(assert-event (equal (fn-native-admin-result-name *fn-na-create*)
                     (fn-record-string-octets "fn.admin")))

(defconst *fn-na-retire*
  (fn-native-admin-plan (fn-na-test-argv '("group" "retire" "fn.admin"))))
(assert-event (equal (fn-native-admin-result-status *fn-na-retire*) :accepted))
(assert-event (equal (fn-native-admin-result-kind *fn-na-retire*) :remove-group))

(defconst *fn-na-capacity*
  (fn-native-admin-plan (fn-na-test-argv '("capacity" "1048576"))))
(assert-event (equal (fn-native-admin-result-status *fn-na-capacity*) :accepted))
(assert-event (equal (fn-native-admin-result-capacity *fn-na-capacity*) 1048576))

; Leading zeroes, signs, overflow, malformed verbs, and non-group labels are
; all refusals before the physical adapter acquires a writable store.
(assert-event (equal (fn-native-admin-result-status
                      (fn-native-admin-plan (fn-na-test-argv '("capacity" "01"))))
                     :refused))
(assert-event (equal (fn-native-admin-result-status
                      (fn-native-admin-plan (fn-na-test-argv '("capacity" "+1"))))
                     :refused))
(assert-event (equal (fn-native-admin-result-status
                      (fn-native-admin-plan (fn-na-test-argv '("capacity" "4294967296"))))
                     :refused))
(assert-event (equal (fn-native-admin-result-status
                      (fn-native-admin-plan (fn-na-test-argv '("group" "create" ""))))
                     :refused))
(assert-event (equal (fn-native-admin-result-status
                      (fn-native-admin-plan (fn-na-test-argv '("group" "remove" "fn.admin"))))
                     :refused))

; The persistent generation namespace uses byte-store's ACL2 digit renderer;
; a raw `format' implementation cannot pass these fixed-name witnesses.
(assert-event (equal (fn-native-admin-config-name 1) "00000001.cfg"))
(assert-event (equal (fn-native-admin-config-name 99999999) "99999999.cfg"))
(assert-event (equal (fn-native-admin-config-name 100000000) nil))

; Candidate validation is the logical replay/open predicate the host wrapper
; calls after byte decoding.  The default durable record opens an empty image;
; an out-of-range frontier is a reachable differing observation and refuses.
(assert-event (fn-native-admin-candidate-openp nil 0 (list *fn-cfg-default-record*)))
(assert-event (not (fn-native-admin-candidate-openp nil 4294967296
                                                 (list *fn-cfg-default-record*))))
