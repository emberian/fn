(in-package "ACL2")
(include-book "owner-store-indexed-tests")
(include-book "../../books/defkeystone")
;; Change the visible article list alone: replay still names the old list.
(defun pivt-bad-view (v)
 (fn-own-view-make-visible
  (fn-own-view-version v) (fn-own-view-frontier v)
  (fn-ctl-visible-state-of (fn-own-view-archive v) nil)
  (fn-own-view-verdicts v) (fn-own-view-group-index v) (fn-own-view-withdrawals v)
  (fn-own-view-raw v) (fn-own-view-withdrawn v) (fn-own-view-keyring v)))
(defun pivt-publish-stale (oc)
 (let ((o (fn-ocfg-owner oc)))
  (fn-ocfg-with-owner oc
   (fn-own-make (fn-own-store o) (pivt-bad-view (fn-own-view o)) (fn-own-conns o)
    (fn-own-next-id o) (fn-own-max-conns o) (fn-own-pending o) (fn-own-ledger-field o)
    (fn-own-clock o) (fn-own-facts o) (fn-own-config o) (fn-own-queue o)
    (fn-own-inflight o) (fn-own-feeds o) (fn-own-node-secret o) (fn-own-refused o)))))
(defteeth fn-pidx-view-okp-of-live-owner
 :subject fn-pidx-view-okp
 :claim (((relation (fn-ocl-relation oc)))
         (fn-pidx-view-okp (fn-own-view (fn-ocfg-owner oc))))
 :witness ((oc *osi-open*))
 :breaks ((relation ((oc (pivt-publish-stale *osi-open*))) :logical "corrupted visible archive"))
 :mutations ((stale-visible
  (:conclusion (fn-pidx-view-okp (fn-own-view (fn-ocfg-owner (pivt-publish-stale oc)))))
  () :fault "owner publishes the empty visible list while retaining the committed raw list")))
(defteeth-check (fn-pidx-view-okp-of-live-owner))
