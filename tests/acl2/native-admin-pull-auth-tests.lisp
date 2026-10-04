; Full dispatch and live-table delta witnesses for PKT-431.
(in-package "ACL2")
(include-book "../../books/native-admin")
(include-book "native-admin-peer-pull-auth-tests")
(defconst *napat-dispatch*
  (fn-native-admin-plan
   (napat-argv '("peer" "pull-login" "far" "reader.fnauth" "false"))))
(assert-event (equal *napat-dispatch* *napat-login*))
; Host-called delta selector over the live peer group is nonempty and is
; exactly the ACL2 extension's incremental publication.
(assert-event (consp (fn-native-admin-plan-deltas-over *napat-login* *napat-peers*)))
(assert-event
 (equal (fn-native-admin-plan-deltas-over *napat-login* *napat-peers*)
        (fn-pcb-extend-deltas "far"
                              (fn-native-admin-result-value *napat-login*)
                              *napat-peers*)))
(assert-event (equal (fn-native-admin-plan-refusal-over *napat-login* nil)
                     :no-such-peer))
