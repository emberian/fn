; Teeth for books/consumer-remote-bound.lisp (D48 / PKT-673): the remote
; consumer is the account's bound consumer.  The fixture is consumer-bound-tests'
; (two groups, four consumers: "1" and "2" bound to bob, "3" unbound, "4"
; bound to alice; bob's password "correct-horse").  Every answer below is
; fn-crbd-route's, which host/consumer-remote-host.lisp
; fn-owner-consumer-remote-route returns to the native listener.
(in-package "ACL2")
(include-book "must-fail-checked")
(include-book "../../books/consumer-remote-bound")

; --- the Store -------------------------------------------------------------
(defun cbt-reserve (s)
  (fn-sn-io (fn-sn-io (fn-sn-io (fn-sn-io s :start-frontier nil)
                                :frontier-file :ok)
                      :frontier-replace :ok)
            :frontier-directory :ok))
(defun cbt-commit (s event)
  (fn-sn-finish
   (fn-sn-io
    (fn-sn-io
     (fn-sn-io (fn-sn-prepare-consumer (cbt-reserve s) event)
               :record-file :ok)
     :record-link :ok)
    :record-directory :ok)))
(defun cbt-article (s record)
  (fn-sn-finish
   (fn-sn-io
    (fn-sn-io
     (fn-sn-io (fn-sn-prepare (cbt-reserve s) record) :record-file :ok)
     :record-link :ok)
    :record-directory :ok)))
(defun cbt-register (s id group)
  (let ((d (fn-col-register (fn-own-start s 2) 256 id group)))
    (if (eq (car d) :write) (cbt-commit s (cadr d)) s)))

(defconst *cbt-public* '(102 110 46 112 117 98 108 105 99))           ; fn.public
(defconst *cbt-private* '(102 110 46 112 114 105 118 97 116 101 46 120)) ; fn.private.x
(defconst *cbt-c1* '(49))
(defconst *cbt-c2* '(50))
(defconst *cbt-c3* '(51))
(defconst *cbt-c4* '(52))

(defconst *cbt-boot*
  (cbt-commit (fn-sn-initial '("fn.public" "fn.private.x") 16)
              (fn-cpe-make 0 0 0 '(:bootstrap (1) (2)))))
(defconst *cbt-registered*
  (cbt-register
   (cbt-register
    (cbt-register (cbt-register *cbt-boot* *cbt-c1* *cbt-private*)
                  *cbt-c2* *cbt-public*)
    *cbt-c3* *cbt-private*)
   *cbt-c4* *cbt-private*))
(defconst *cbt-secret-record*
  (fn-record-make 5 5 5 "<secret@fn.test>" '(83)
                  '("fn.private.x") "secret-pin" "secret-content"
                  "secret-release" 1 841000000))
(defconst *cbt-public-record*
  (fn-record-make 6 6 6 "<public@fn.test>" '(80)
                  '("fn.public") "public-pin" "public-content"
                  "public-release" 1 841000001))
; The Store retains HELD rows (records-flip): each wire record at its arena
; handle (fn-held-plain; the poll reads the row's groups, never its bytes).
(defconst *cbt-store*
  (cbt-article (cbt-article *cbt-registered* (fn-held-plain *cbt-secret-record* 0))
               (fn-held-plain *cbt-public-record* 1)))
(defconst *cbt-o* (fn-own-start *cbt-store* 2))
; Every registration and both articles committed: frontier 7.
(assert-event (equal (fn-cp-nth 3 (fn-sn-consumer *cbt-store*)) 7))

; --- the configuration: bob's rule and three bindings ------------------------
(defconst *cbt-deltas*
  (list (fn-cfg-account-access "bob" "fn.*,!fn.private.*" "fn.*")
        (fn-cfg-consumer-bind "1" "bob")
        (fn-cfg-consumer-bind "2" "bob")
        (fn-cfg-consumer-bind "4" "alice")))
(assert-event (equal (fn-cfg-kind-code :consumer-bind) 24))
(assert-event (equal (fn-cfg-code-kind 24) :consumer-bind))
(assert-event (fn-cfg-delta-listp *cbt-deltas*))
(assert-event (null (fn-cfg-consumer-bind-reason (fn-cfg-consumer-bind "1" "bob"))))
(assert-event (null (fn-cfg-consumer-bind-reason (fn-cfg-consumer-bind "1" ""))))
(assert-event (equal (fn-cfg-consumer-bind-reason (fn-cfg-consumer-bind "" "bob"))
                     :consumer-name))
(assert-event (equal (fn-cfg-consumer-bind-reason (fn-cfg-consumer-bind "1" "a b"))
                     :consumer-login))
;; The configuration values below are spelled by their accounts rows
;; (`cbt-with-accounts') and each is asserted equal to the value the
;; configuration's own fold (`fn-cfg-apply-delta') produces from the deltas.
(defun cbt-with-accounts (rows)
  (let ((v (fn-cfg-value (fn-cfg-initial))))
    (fn-cfg-value-make-full (fn-cfg-groups v) (fn-cfg-capacity v)
                            (fn-cfg-quotas v) (fn-cfg-policies v)
                            (fn-cfg-listeners v) (fn-cfg-peers v)
                            (fn-cfg-limits v) (fn-cfg-authorities v)
                            (fn-cfg-invitations v) rows
                            (fn-cfg-descriptions v))))
(defun cbt-apply (v gen ds)
  (if (consp ds)
      (cbt-apply (fn-cfg-apply-delta v gen 0 (car ds)) (1+ gen) (cdr ds))
    v))
(defconst *cbt-rows*
  (list (fn-cfg-row-make "bob" "fn.*,!fn.private.*" "fn.*" 3)
        (fn-cfg-row-make "1" "bob" "" 6)
        (fn-cfg-row-make "2" "bob" "" 6)
        (fn-cfg-row-make "4" "alice" "" 6)))
(defconst *cbt-v* (cbt-with-accounts *cbt-rows*))
(assert-event
 (equal (cbt-apply (fn-cfg-value (fn-cfg-initial)) 1 *cbt-deltas*) *cbt-v*))
; A rebind replaces the row; the unbind removes it.
(assert-event
 (equal (fn-cfg-accounts
         (fn-cfg-apply-delta *cbt-v* 9 0 (fn-cfg-consumer-bind "1" "alice")))
        (list (fn-cfg-row-make "bob" "fn.*,!fn.private.*" "fn.*" 3)
              (fn-cfg-row-make "2" "bob" "" 6)
              (fn-cfg-row-make "4" "alice" "" 6)
              (fn-cfg-row-make "1" "alice" "" 6))))
(assert-event
 (equal (fn-cfg-accounts
         (fn-cfg-apply-delta *cbt-v* 9 0 (fn-cfg-consumer-bind "1" "")))
        (list (fn-cfg-row-make "bob" "fn.*,!fn.private.*" "fn.*" 3)
              (fn-cfg-row-make "2" "bob" "" 6)
              (fn-cfg-row-make "4" "alice" "" 6))))

(defconst *cbt-oc* (fn-ocfg-make *cbt-o* (fn-cfg-make 4 *cbt-v*) nil nil))
; The operator's view: no binding row, no rule.
(defconst *cbt-oc-none*
  (fn-ocfg-make *cbt-o* (fn-cfg-make 0 (fn-cfg-value (fn-cfg-initial))) nil nil))

; --- credentials (books/nntp-auth-teeth-tests' verifier literal) -------------
(defconst *cbt-secret* (fn-nntp-string-octets "correct-horse"))
(defconst *cbt-wrong* (fn-nntp-string-octets "wrong-horse"))
(defconst *cbt-salt* (make-list 16 :initial-element 3))
(defconst *cbt-verifier*
  (fn-authsec-verifier
   *cbt-salt*
   '(42 82 187 10 181 221 230 125 199 188 135 91 193 55 205 245
     177 50 208 139 71 236 67 86 54 24 223 76 55 144 61 51)
   (car (fn-scram-keys (fn-nntp-string-octets "correct-horse")
                                   (make-list 16 :initial-element 3) 4096))
   (cadr (fn-scram-keys (fn-nntp-string-octets "correct-horse")
                                    (make-list 16 :initial-element 3) 4096))))
(assert-event (equal *cbt-verifier* (fn-authsec-enrol *cbt-salt* *cbt-secret*)))
(defconst *cbt-acfg*
  (fn-auth-make-config
   t nil t
   (list (fn-auth-make-cred (fn-nntp-string-octets "alice")
                            (make-list 32 :initial-element 7) *cbt-verifier* t)
         (fn-auth-make-cred (fn-nntp-string-octets "bob")
                            (make-list 32 :initial-element 8) *cbt-verifier* t))))
(assert-event (fn-auth-configp *cbt-acfg*))


; --- the routes ----------------------------------------------------------------
(defconst *crbt-bob* (fn-nntp-string-octets "bob"))
(defconst *crbt-alice* (fn-nntp-string-octets "alice"))
(defun crbt-req (op login secret consumer cursor seconds)
  (list :remote-consumer op login secret consumer nil cursor seconds))
(defun crbt-route (op login secret consumer)
  (fn-crbd-route (crbt-req op login secret consumer nil 0) *cbt-oc* *cbt-acfg*))

; Satisfiable: bob's own bound consumer "2" (fn.public, readable under bob's
; rule) is served each served operation, as the bound local operation.
(assert-event (equal (crbt-route :poll *crbt-bob* *cbt-secret* *cbt-c2*)
                     (list :bound-poll *cbt-c2* *cbt-secret*)))
(assert-event (equal (fn-crbd-route (crbt-req :wait *crbt-bob* *cbt-secret* *cbt-c2* nil 30)
                                    *cbt-oc* *cbt-acfg*)
                     (list :bound-wait *cbt-c2* (list 30 *cbt-secret*))))
(assert-event (equal (crbt-route :position *crbt-bob* *cbt-secret* *cbt-c2*)
                     (list :position *cbt-c2* nil)))
(assert-event (equal (crbt-route :status *crbt-bob* *cbt-secret* *cbt-c2*)
                     (list :status *cbt-c2* nil)))

; Teeth.  Operator controls stay private, even with the right password.
(assert-event (equal (crbt-route :register *crbt-bob* *cbt-secret* *cbt-c2*)
                     '(:refused :operator-control)))
(assert-event (equal (crbt-route :unregister *crbt-bob* *cbt-secret* *cbt-c2*)
                     '(:refused :operator-control)))
(assert-event (equal (crbt-route :rebase *crbt-bob* *cbt-secret* *cbt-c2*)
                     '(:refused :operator-control)))
; The wrong password.
(assert-event (equal (crbt-route :poll *crbt-bob* *cbt-wrong* *cbt-c2*)
                     '(:refused :credential)))
; Another account's consumer, even with that account's... own password:
; "4" is alice's; bob naming it is refused before any gate.
(assert-event (equal (crbt-route :poll *crbt-bob* *cbt-secret* *cbt-c4*)
                     '(:refused :credential)))
; The operator's unbound consumer "3" is never served remotely.
(assert-event (equal (crbt-route :poll *crbt-bob* *cbt-secret* *cbt-c3*)
                     '(:refused :credential)))
; Bob's consumer "1" queries fn.private.x, which bob's rule does not read:
; the bound gate's own refusal.
(assert-event (equal (crbt-route :poll *crbt-bob* *cbt-secret* *cbt-c1*)
                     '(:refused :access)))
(assert-event (equal (crbt-route :position *crbt-bob* *cbt-secret* *cbt-c1*)
                     '(:refused :access)))
; With no binding in the configuration (the operator's view), nothing is served.
(assert-event (equal (fn-crbd-route (crbt-req :poll *crbt-bob* *cbt-secret* *cbt-c2* nil 0)
                                    *cbt-oc-none* *cbt-acfg*)
                     '(:refused :credential)))

; ACK: the cursor names the consumer.  Bob's own cursor for "2" is the bound
; ack; a request naming "2" that carries "1"'s cursor is refused :scope.
(defconst *crbt-c2-cursor* (cadr (fn-col-position *cbt-o* *cbt-c2*)))
(defconst *crbt-c1-cursor* (cadr (fn-col-position *cbt-o* *cbt-c1*)))
(assert-event (equal (fn-cbind-cursor-consumer *crbt-c2-cursor*) *cbt-c2*))
(assert-event (equal (fn-crbd-route (crbt-req :ack *crbt-bob* *cbt-secret* *cbt-c2* *crbt-c2-cursor* 0)
                                    *cbt-oc* *cbt-acfg*)
                     (list :bound-ack *crbt-c2-cursor* *cbt-secret*)))
(assert-event (equal (fn-crbd-route (crbt-req :ack *crbt-bob* *cbt-secret* *cbt-c2* *crbt-c1-cursor* 0)
                                    *cbt-oc* *cbt-acfg*)
                     '(:refused :scope)))
