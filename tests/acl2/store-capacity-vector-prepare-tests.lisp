; The served prepare's vector keystone (fn-cvec-prepare-keeps-the-vector),
; apart from store-capacity-vector-tests: its witness is owner-store-budget-
; tests' held row *osbt-second* on its owner *osbt-reserved* (one committed
; record, so the prepare stages), the row the host stages, its payload field
; the arena handle; that book defines the arena-lift constant *sr-arena*,
; which other includers of store-capacity-vector-tests define too
; (store-carried-folds-tests through owner-store-indexed-tests).
(in-package "ACL2")
(include-book "store-capacity-vector-tests")
(include-book "owner-store-budget-tests")
(include-book "../../books/defkeystone")

(defconst *cvt-row-gate*
  (fn-sbud-article-gate-figure (len (fn-record-payload *osbt-second*))
                               (len (fn-record-groups *osbt-second*))))
(defconst *cvt-row-safe* (- (- *cvt-h* *cvt-row-gate*) (* 2 *cvt-r*)))

(defteeth fn-cvec-prepare-keeps-the-vector
  :claim (((staged (not (equal (fn-sbud-prepare
                                oc record
                                (fn-cvec-article-budget-for
                                 profile (fn-sbud-used (fn-sbud-oc-store oc))
                                 bytes-used record debt))
                               oc))))
          (and (fn-cvec-roomp profile
                              (+ 1 (fn-sbud-used (fn-sbud-oc-store oc)))
                              (+ bytes-used (len (fn-record-payload record)))
                              debt)
               (fn-profile-replay-within-boundp
                profile (+ bytes-used (len (fn-record-payload record))))))
  :subject fn-sbud-prepare
  :witness ((oc *osbt-reserved*) (record *osbt-second*) (profile *cvt-p*)
            (bytes-used *cvt-row-safe*) (debt 1))
  :breaks ((staged ((oc *osbt-reserved*) (record *osbt-second*) (profile *cvt-p*)
                    (bytes-used (+ *cvt-row-safe* *cvt-r*)) (debt 1))))
  :mutations ((prepare-forgets-an-open-undertaking
               (:conclusion (and (fn-cvec-roomp profile
                                                (+ 1 (fn-sbud-used (fn-sbud-oc-store oc)))
                                                (+ bytes-used (len (fn-record-payload record)))
                                                (+ 1 debt))
                                 (fn-profile-replay-within-boundp
                                  profile (+ bytes-used (len (fn-record-payload record))))))
               ((oc *osbt-reserved*) (record *osbt-second*) (profile *cvt-p*)
                (bytes-used *cvt-row-safe*) (debt 1))
               :fault "a staged row leaving the vector one open undertaking short")))
