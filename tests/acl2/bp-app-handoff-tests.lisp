(in-package "ACL2")
(include-book "../../books/bp-app-handoff")
(include-book "../../books/codec-attach")
(include-book "std/testing/must-fail" :dir :system)

(defconst *bpah-local* (cons :dtn '(47 47 114 101 99 101 105 118 101 114 47)))
(defconst *bpah-peer* (cons :dtn '(47 47 115 101 110 100 101 114 47)))
(defconst *bpah-config* (fn-bpn-config *bpah-peer* 3600000 2 32 1048576))
(defconst *bpah-obs* (fn-clock-observation 1000 0 0 nil))
(defconst *bpah-adu* (fn-bpa-encode
  (fn-bpa-make-request "w" "s" "dtn://sender/" "dtn://receiver/"
                       "p" "i" "c" "t" '(88 13 10))))
(defconst *bpah-bundle*
  (fn-bpn-send-bundle *bpah-config* *bpah-local* *bpah-adu* 7 *bpah-obs*))
(defconst *bpah-ingress*
  (list :cl (cons 1 1) 1 *bpah-peer*
        (fn-record-string-octets "dtn://sender/") 0))
(defconst *bpah-held*
  (fn-bpnf-held (fn-bpnf-ingress-principal *bpah-ingress*)
                 (fn-bpb-bundle-id *bpah-bundle*) 0 *bpah-ingress*
                 nil nil *bpah-bundle* (fn-bpb-encode *bpah-bundle*)
                 nil nil nil '(:dispatch-pending) nil nil 0))
(defconst *bpah-state*
  (fn-bpnf-state (fn-bpn-initial-machine-state *bpah-config* 4 1048576)
                 (list *bpah-held*) nil nil nil nil nil 1 1))

(assert-event (fn-bpnf-heldp *bpah-held*))
(assert-event (equal (fn-bpah-held-class *bpah-held*) :request))
(assert-event (equal (fn-bpah-view-class
                      (fn-bpah-pending-view *bpah-state* *bpah-local*))
                     :request))
(assert-event (null (fn-bpah-pending-view *bpah-state* *bpah-peer*)))
(assert-event (null (fn-bpah-pending-view
                     (fn-bpnf-state (fn-bpnf-base *bpah-state*) nil nil nil
                                    nil nil nil 1 1)
                     *bpah-local*)))
(must-fail
 (assert-event (fn-bpah-local-pendingp *bpah-held* *bpah-peer*)))

; The receipt names the remote work peer, while its return carrier is
; addressed to the local node.  Requiring the receipt peer field to equal
; the return carrier destination would refuse an authorized two-node reply.
(defconst *bpah-receipt-adu*
  (fn-bpa-encode
   (fn-bpa-make-receipt "r" "w" "s" "dtn://receiver/"
                        "dtn://receiver/" "p" "i" "c" "t")))
(defconst *bpah-receipt-view*
  (list :delivery '("principal" "bundle") :receipt *bpah-receipt-adu*
        (list :cl (cons 2 1) 1 *bpah-local*
              (fn-record-string-octets "dtn://receiver/") 0)
        nil "dtn://receiver/" "dtn://sender/"))
(assert-event
 (fn-bpah-receipt-trustedp *bpah-receipt-view* "dtn://receiver/"))
(must-fail
 (assert-event
  (fn-bpah-receipt-trustedp *bpah-receipt-view* "dtn://sender/")))
(must-fail
 (assert-event
  (fn-bpah-receipt-trustedp
   (update-nth 6 "dtn://other/" *bpah-receipt-view*)
   "dtn://receiver/")))
