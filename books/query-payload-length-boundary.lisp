; Actual selected scalar length boundary; source component only.
(in-package "ACL2")
(include-book "../host/query-payload-scalar-host")

(defthm fn-qpl-node-query-read-not-ready
  (not (equal (car (fn-ibp-node-query-read token fuel slot depth fn-ibp-node)) :ready))
  :hints (("Goal" :induct (fn-ibp-node-query-read token fuel slot depth fn-ibp-node)
                  :in-theory (e/d (fn-ibp-node-query-read)
                                  (fn-ibp-node-children-get fn-ibp-node-children-boundp
                                   fn-ibp-query-slot-livep create-fn-ibp-query-segment
                                   create-fn-ibp-node-left create-fn-ibp-node-right)))))

(defthm fn-qpl-selected-observation-not-ready
  (not (equal (car (fn-ibp-selected-observation selected query capture borrow)) :ready))
  :hints (("Goal" :in-theory (enable fn-ibp-selected-observation))))

(defthm fn-qpl-selected-read-not-ready
  (not (equal (car (fn-ibp-selected-read selected fuel fn-index-backing)) :ready))
  :hints (("Goal" :in-theory (e/d (fn-ibp-selected-read)
                                  (fn-ibp-node-query-read fn-ibp-selected-observation
                                   fn-miq-selected-tokenp)))))

(defthm fn-qpl-node-grant-read-not-ready
  (not (equal (car (fn-ibp-node-query-grant-read token mode fuel slot depth fn-ibp-node)) :ready))
  :hints (("Goal" :induct (fn-ibp-node-query-grant-read token mode fuel slot depth fn-ibp-node)
                  :in-theory (e/d (fn-ibp-node-query-grant-read)
                                  (fn-ibp-node-children-get fn-ibp-node-children-boundp
                                   fn-ibp-query-slot-livep create-fn-ibp-query-segment
                                   create-fn-ibp-node-left create-fn-ibp-node-right)))))

(defthm fn-qpl-node-authorization-not-ready
  (not (equal (car (fn-ibp-node-query-authorization token fuel slot depth fn-ibp-node)) :ready))
  :hints (("Goal" :in-theory (e/d (fn-ibp-node-query-authorization)
                                  (fn-ibp-node-query-grant-read)))))

(defthm fn-qpl-node-payload-live-not-ready
  (not (equal (car (fn-ibp-node-payload-live token grant fuel slot depth fn-ibp-node)) :ready))
  :hints (("Goal" :induct (fn-ibp-node-payload-live token grant fuel slot depth fn-ibp-node)
                  :in-theory (e/d (fn-ibp-node-payload-live)
                                  (fn-ibp-node-children-get fn-ibp-node-children-boundp
                                   fn-qpg-livep create-fn-query-payload-grants
                                   create-fn-ibp-node-left create-fn-ibp-node-right)))))

(defthm fn-qpl-provider-selected-read-not-ready
  (not (equal (car (fn-miq-selected-read selected fuel fn-mio$c)) :ready))
  :hints (("Goal" :in-theory (e/d (fn-miq-selected-read)
                                  (fn-ibp-selected-read fn-ibp-node-query-authorization
                                   fn-ibp-node-payload-live fn-miq-selected-tokenp)))))

(defthm fn-miq-ready-payload-length-denotes-selected-arena
  (implies
   (equal (car (fn-miq-selected-payload-length selected fuel fn-mio$c fn-arena state)) :ready)
   (let ((held (mv-nth 1 (fn-miq-selected-read selected fuel fn-mio$c)))
         (grant (mv-nth 2 (fn-miq-selected-read selected fuel fn-mio$c)))
         (left (mv-nth 3 (fn-miq-selected-read selected fuel fn-mio$c))))
     (equal (mv-list 3 (fn-miq-selected-payload-length selected fuel fn-mio$c fn-arena state))
            (list :ready
                  (list :payload-length selected grant (fn-held-payload held)
                        (len (nth (fn-held-payload held) fn-arena)))
                  (- left 1)))))
  :hints (("Goal" :in-theory (e/d (fn-miq-selected-payload-length fn-qps-selected-length)
                                  (fn-miq-selected-read fn-qps-eligiblep
                                   fn-owner-query-payload-ledger))))
  :rule-classes nil)
