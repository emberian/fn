(in-package "ACL2")
(include-book "../../books/owner-retain-transitions")
(include-book "../../books/config-observed")

(defconst *owb-k1-config*
 (fn-config-replay 0 (fn-cnode-line-ceiling) (list *fn-cfg-default-record*)))
(defconst *owb-k1-opened* (fn-cpo-open-observed (list *fn-cfg-default-record*) 0 nil))
(defconst *owb-k1-store*
 (fn-sn-io (fn-sn-io (fn-sn-io (fn-sn-open-state *owb-k1-opened*)
  :recovery-barrier :ok) :recovery-barrier :ok) :recovery-barrier :ok))
(defconst *owb-k1-oc*
 (fn-ocfg-make (fn-own-start *owb-k1-store* 4) *owb-k1-config* nil nil))
(defconst *owb-k1-view* (fn-own-view (fn-ocfg-owner *owb-k1-oc*)))
(assert-event (and (fn-lgoc-invariantp *owb-k1-oc*)
 (fn-captured-views-follow-ocfg (fn-ordr-views (fn-ordr-initial)) *owb-k1-oc*)
 (fn-captured-views-follow-ocfg
  (fn-ordr-views (fn-ordr-capture (fn-ordr-initial) :start *owb-k1-view*))
  *owb-k1-oc*)))
(defconst *owb-k1-frontier-ahead*
 (update-nth 1 (1+ (fn-sf-frontier (fn-sn-files *owb-k1-store*))) *owb-k1-view*))
(assert-event (and (fn-own-view-shapep *owb-k1-frontier-ahead*)
 (not (fn-captured-views-follow-ocfg
  (fn-ordr-views (fn-ordr-capture (fn-ordr-initial) :start *owb-k1-frontier-ahead*))
  *owb-k1-oc*))))

