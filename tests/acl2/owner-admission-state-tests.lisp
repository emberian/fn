(in-package "ACL2")
(include-book "../../books/owner-admission-recovery")
(include-book "../../books/defkeystone")

(defteeth fn-oadm-configure-reclaim-requires-opt-in
  :claim (((disabled (not live)))
          (not (fn-oadm-reclaim-live (fn-oadm-configure-reclaim live))))
  :subject fn-oadm-configure-reclaim
  :witness ((live nil))
  :breaks ((disabled ((live t))))
  :mutations ((default-on (:conclusion
                (fn-oadm-reclaim-live (fn-oadm-configure-reclaim live)))
              ((live nil)) :fault "a disabled opt-in becomes enabled")))

(defteeth fn-oadm-configured-request-composition-by-definition
  :claim (() (equal (fn-orcp-request-word mode
                       (fn-oadm-reclaim-live (fn-oadm-configure-reclaim live)) word)
                    (fn-orcp-request-word mode (and live t) word)))
  :subject fn-oadm-configure-reclaim
  :witness ((mode :reclaim) (live t) (word :ready))
  :breaks ()
  :mutations ((stale-enabled-record (:conclusion
                (equal (fn-orcp-request-word mode (fn-oadm-reclaim-live '(t)) word)
                       (fn-orcp-request-word mode (and live t) word)))
              ((mode :reclaim) (live nil) (word :ready))
              :fault "reading the previous enabled record permits a disabled reclaim")))

(assert-event (equal (fn-orcp-request-word :reclaim (fn-oadm-reclaim-live (fn-oadm-initial)) :ready)
                     :offline-only))
(assert-event (equal (fn-orcp-request-word :recorded (fn-oadm-reclaim-live (fn-oadm-configure-reclaim nil)) :ready)
                     :offline-only))
(assert-event (equal (fn-orcp-request-word :dry-run (fn-oadm-reclaim-live (fn-oadm-initial)) :ready)
                     :ready))
(assert-event (equal (fn-orcp-request-word :reclaim (fn-oadm-reclaim-live (fn-oadm-configure-reclaim t)) :busy)
                     :busy))
(defteeth-check (fn-oadm-configure-reclaim-requires-opt-in
                fn-oadm-configured-request-composition-by-definition))
