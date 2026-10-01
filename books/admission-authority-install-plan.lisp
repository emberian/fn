; Fixed-field semantic assembly after the actual authority node/account step.
; This function issues no token and grants no installation authority. The
; registered producer supplies its retained base and actual AfterNode result.
(in-package "ACL2")
(include-book "store-node")
(include-book "node-config")
(include-book "stx-keyring-records")
(include-book "snapshot-source-token")

(defun fn-aip-authority-store-fields (base produced next-cn next-cp)
 (declare (xargs :guard t))
 (list :history-store-fields
       (fn-sn-groups base) (fn-sn-capacity base) (fn-cnode-node next-cn)
       (fn-sn-keyring base) (fn-sn-index base)
       (fn-sn-keyring-generation base) (fn-sn-verdicts base)
       (fn-sn-keyring-snapshots base)
       (fn-stxk-context-next (fn-omk-at 0 produced))
       (fn-sn-config-history base) next-cp
       (fn-sn-topic base) (fn-sn-event-index base)))

(defun fn-aip-authority-reader-view (old-view count frontier)
 (declare (xargs :guard t))
 (list count frontier (fn-omk-at 2 old-view) (fn-omk-at 3 old-view)
       (fn-omk-at 4 old-view) (fn-omk-at 5 old-view)
       (fn-omk-at 6 old-view) (fn-omk-at 7 old-view)
       (fn-omk-at 8 old-view) (fn-omk-at 9 old-view)))

(defun fn-aip-authority-install-plan (base produced next-cn next-cp
                                          old-view count frontier posting)
 (declare (xargs :guard t))
 (list :history-install-plan :E
       (fn-aip-authority-store-fields base produced next-cn next-cp)
       (fn-aip-authority-reader-view old-view count frontier)
       (fn-cnode-config next-cn) posting))
