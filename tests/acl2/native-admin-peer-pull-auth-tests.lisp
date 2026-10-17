; Actual operator parsing and live delta witnesses for PKT-431.
(in-package "ACL2")
(include-book "../../books/native-admin-peer")

(defun napat-argv (words)
  (if (consp words)
      (cons (fn-record-string-octets (car words)) (napat-argv (cdr words)))
    nil))
(defun napat-plan (words) (fn-native-admin-peer-extend-plan words))
(defconst *napat-login*
  (napat-plan '("peer" "pull-login" "far" "reader.fnauth" "false")))
(assert-event (equal (fn-native-admin-result-status *napat-login*) :accepted))
(assert-event (equal (fn-native-admin-result-kind *napat-login*) :extend-peer))
(assert-event (equal (fn-native-admin-result-name *napat-login*)
                     (fn-record-string-octets "far")))
(assert-event (equal (fn-native-admin-result-value *napat-login*)
                     (list (fn-pull-auth-row "far" "reader.fnauth" nil))))
(assert-event
 (equal (fn-native-admin-result-value
         (napat-plan '("peer" "pull-login" "far" "-" "true")))
        (list (fn-pull-auth-row "far" "" t))))
(assert-event
 (equal (fn-native-admin-result-status
         (napat-plan '("peer" "pull-login" "far" "reader.fnauth" "yes")))
        :refused))
(assert-event
 (equal (fn-native-admin-result-status
         (napat-plan '("peer" "pull-login" "far" "" "false"))) :refused))
(assert-event
 (equal (fn-native-admin-result-status
         (napat-plan '("peer" "pull-login" "far" "reader.fnauth"))) :refused))
(assert-event
 (equal (fn-native-admin-result-status
         (napat-plan '("peer" "pull-login" "far" "reader.fnauth" "false" "extra")))
        :refused))
(assert-event
 (equal (fn-native-admin-result-status
         (napat-plan (list "peer" "pull-login" "far"
                           (coerce (list #\a (code-char 0)) 'string) "false")))
        :refused))
(defconst *napat-add*
  (fn-native-admin-peer-plan '("peer" "add" "far" "far.example" "192.0.2.44" "1119"
                "fn.*" "fn.*" "192.0.2.44" "false")))
(assert-event (equal (fn-native-admin-result-status *napat-add*) :accepted))
(defconst *napat-peers* (fn-cfg-peer-rows (fn-native-admin-result-peer *napat-add*)))
; A peer edit keeps the pull slot as a named extension.
(defconst *napat-extended*
  (fn-pcb-extend-rows *napat-peers* (fn-native-admin-result-value *napat-login*)))
(defconst *napat-edit* (fn-pset-plan "far" '(("--send" . "-")) *napat-extended*))
(assert-event (equal (car *napat-edit*) :ok))
(assert-event
 (equal (fn-pull-auth-of-rows (fn-cfg-delta-rows (car (cadr *napat-edit*))))
        '(:authinfo "reader.fnauth" nil)))
(assert-event
 (not (fn-cfg-peer-outbound
       (fn-cfg-peer-of-rows "far" (fn-cfg-delta-rows (car (cadr *napat-edit*)))))))
