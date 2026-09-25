; Teeth for books/control-exec.lisp (spike/control).  Witnesses over the
; decision functions the host calls; the must-fail cases show each
; hypothesis of the authority rule separates.
; SPIKE: defers the dev teeth over the host-called acceptance plan and the
; served port (proof owner tests/acl2/control-exec-tests.lisp on dev).
(in-package "ACL2")
(include-book "../../books/control-exec")
(include-book "std/testing/must-fail" :dir :system)

(defconst *cet-p* (make-list 64 :initial-element #\5))
(defconst *cet-p-hex* (coerce *cet-p* 'string))
(defconst *cet-q-hex* (coerce (make-list 64 :initial-element #\a) 'string))
(defconst *cet-grants*
  (list (list "fn.*" *cet-p-hex* '("cancel" "newgroup" "rmgroup" "checkgroups"))))

; Namespace coverage.
(assert-event (fn-ctl-ns-covers "fn.*" "fn.test"))
(assert-event (fn-ctl-ns-covers "fn.*" "fn"))
(assert-event (not (fn-ctl-ns-covers "fn.*" "fnord.test")))
(assert-event (fn-ctl-ns-covers "fn.test" "fn.test"))
(assert-event (not (fn-ctl-ns-covers "fn.test" "fn.test.x")))

; The authority decision: executes only for a verified principal with a
; covering grant.
(assert-event
 (equal (fn-ctl-authorize "newgroup" (list :verified *cet-p-hex*)
                          '("fn.new") *cet-grants* t)
        '(:execute "fn.*")))
; Rule 4: carried and unsigned never execute, whatever the grant.
(assert-event
 (equal (fn-ctl-authorize "newgroup" (list :carried *cet-p-hex*)
                          '("fn.new") *cet-grants* t)
        '(:decline "carried")))
(assert-event
 (equal (fn-ctl-authorize "newgroup" '(:unsigned) '("fn.new") *cet-grants* t)
        '(:decline "unsigned")))
; A grant is needed, and it must cover the named group.
(assert-event
 (equal (fn-ctl-authorize "newgroup" (list :verified *cet-q-hex*)
                          '("fn.new") *cet-grants* t)
        '(:decline "no-grant")))
(assert-event
 (equal (fn-ctl-authorize "newgroup" (list :verified *cet-p-hex*)
                          '("alt.new") *cet-grants* t)
        '(:decline "outside-namespace")))
; RFC 5537 section 5.2: a group control message without Approved.
(assert-event
 (equal (fn-ctl-authorize "rmgroup" (list :verified *cet-p-hex*)
                          '("fn.new") *cet-grants* nil)
        '(:decline "no-approved")))
; ihave from a granted principal is still declined.
(assert-event
 (equal (fn-ctl-authorize "ihave" (list :verified *cet-p-hex*)
                          '("fn.new") *cet-grants* t)
        '(:decline "unsupported-verb")))

; Teeth: without the verified token, or without the grant, the execute
; witness fails.
(must-fail
 (assert-event
  (equal (car (fn-ctl-authorize "newgroup" (list :carried *cet-p-hex*)
                                '("fn.new") *cet-grants* t))
         :execute)))
(must-fail
 (assert-event
  (equal (car (fn-ctl-authorize "newgroup" (list :verified *cet-p-hex*)
                                '("fn.new") nil t))
         :execute)))

; Grants parse from the operator's rows; a revoked row grants nothing.
(assert-event
 (equal (fn-ctl-grants
         (list (fn-cfg-row-make (concatenate 'string "ctl-grant fn.* " *cet-p-hex*)
                                "cancel,newgroup" "" 0)
               (fn-cfg-row-make (concatenate 'string "ctl-grant alt.* " *cet-q-hex*)
                                "revoked" "" 0)))
        (list (list "fn.*" *cet-p-hex* '("cancel" "newgroup")))))

; The admin plan: grant and revoke are :set-policy rows on the pair.
(assert-event
 (equal (fn-native-admin-result-kind
         (fn-native-admin-plan
          (list (fn-record-string-octets "control")
                (fn-record-string-octets "grant")
                (fn-record-string-octets "fn.*")
                (fn-record-string-octets *cet-p-hex*)
                (fn-record-string-octets "cancel"))))
        :set-policy))
(assert-event
 (equal (fn-native-admin-result-status
         (fn-native-admin-plan
          (list (fn-record-string-octets "control")
                (fn-record-string-octets "grant")
                (fn-record-string-octets "fn.*")
                (fn-record-string-octets "XYZ")
                (fn-record-string-octets "cancel"))))
        :refused))
