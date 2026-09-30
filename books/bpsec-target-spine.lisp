; Carried fixed-record invariant for the actual bounded target cursor.
; Ghost representation predicate from ASB book; no served revalidation.
(in-package "ACL2")
(include-book "bpsec-asb-spine")
(include-book "bpsec-target-cursor")

(defconst *fn-bps-target-spine*
  '(:status :reason :stage :bundle :bindings :opaque :limits :todo :targets
    :count :bound :pairs :encrypted :current :security-block :target
    :target-block :scan :needle :search-mode :hit :miss))

(local
 (defthm fn-bps-target-put-preserves-spine-by-definition
   (implies (fn-bps-cursor-spinep keys cursor)
            (fn-bps-cursor-spinep keys (fn-bps-put key value cursor)))
   :hints (("Goal" :induct (fn-bps-cursor-spinep keys cursor)))))

(local
 (defthm fn-bps-stop-preserves-target-spine-by-definition
   (implies (fn-bps-cursor-spinep keys cursor)
            (fn-bps-cursor-spinep keys (fn-bps-stop status reason cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-stop) (fn-bps-cursor-spinep fn-bps-put fn-bps-get fn-bps-field fn-bpb-bundle-blocks fn-bpb-bundle-payload fn-bpb-block-type fn-bpb-block-number fn-bpb-block-flags fn-bps-graph-target-reason fn-bps-graph-search-matchp fn-bps-graph-stage fn-bps-graph-count fn-bps-graph-action fn-bps-graph-search fn-bps-target-unit (:definition nfix)))))))

(local
 (defthm fn-bps-graph-stage-preserves-target-spine-by-definition
   (implies (fn-bps-cursor-spinep keys cursor)
            (fn-bps-cursor-spinep keys (fn-bps-graph-stage stage cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-graph-stage) (fn-bps-cursor-spinep fn-bps-put fn-bps-get fn-bps-field fn-bpb-bundle-blocks fn-bpb-bundle-payload fn-bpb-block-type fn-bpb-block-number fn-bpb-block-flags fn-bps-graph-target-reason fn-bps-graph-search-matchp fn-bps-stop fn-bps-graph-count fn-bps-graph-action fn-bps-graph-search fn-bps-target-unit (:definition nfix)))))))

(local
 (defthm fn-bps-graph-count-preserves-target-spine-by-definition
   (implies (fn-bps-cursor-spinep keys cursor)
            (fn-bps-cursor-spinep keys (fn-bps-graph-count cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-graph-count) (fn-bps-cursor-spinep fn-bps-put fn-bps-get fn-bps-field fn-bpb-bundle-blocks fn-bpb-bundle-payload fn-bpb-block-type fn-bpb-block-number fn-bpb-block-flags fn-bps-graph-target-reason fn-bps-graph-search-matchp fn-bps-stop fn-bps-graph-stage fn-bps-graph-action fn-bps-graph-search fn-bps-target-unit (:definition nfix)))))))

(local
 (defthm fn-bps-graph-action-preserves-target-spine-by-definition
   (implies (fn-bps-cursor-spinep keys cursor)
            (fn-bps-cursor-spinep keys (fn-bps-graph-action action cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-graph-action) (fn-bps-cursor-spinep fn-bps-put fn-bps-get fn-bps-field fn-bpb-bundle-blocks fn-bpb-bundle-payload fn-bpb-block-type fn-bpb-block-number fn-bpb-block-flags fn-bps-graph-target-reason fn-bps-graph-search-matchp fn-bps-stop fn-bps-graph-stage fn-bps-graph-count fn-bps-graph-search fn-bps-target-unit (:definition nfix)))))))

(local
 (defthm fn-bps-graph-search-preserves-target-spine-by-definition
   (implies (fn-bps-cursor-spinep keys cursor)
            (fn-bps-cursor-spinep keys (fn-bps-graph-search needle values mode hit miss cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-graph-search) (fn-bps-cursor-spinep fn-bps-put fn-bps-get fn-bps-field fn-bpb-bundle-blocks fn-bpb-bundle-payload fn-bpb-block-type fn-bpb-block-number fn-bpb-block-flags fn-bps-graph-target-reason fn-bps-graph-search-matchp fn-bps-stop fn-bps-graph-stage fn-bps-graph-count fn-bps-graph-action fn-bps-target-unit (:definition nfix)))))))

(local
 (defthm fn-bps-target-unit-preserves-target-spine-by-definition
   (implies (fn-bps-cursor-spinep keys cursor)
            (fn-bps-cursor-spinep keys (fn-bps-target-unit cursor)))
   :hints (("Goal" :in-theory (e/d (fn-bps-target-unit) (fn-bps-cursor-spinep fn-bps-put fn-bps-get fn-bps-field fn-bpb-bundle-blocks fn-bpb-bundle-payload fn-bpb-block-type fn-bpb-block-number fn-bpb-block-flags fn-bps-graph-target-reason fn-bps-graph-search-matchp fn-bps-stop fn-bps-graph-stage fn-bps-graph-count fn-bps-graph-action fn-bps-graph-search (:definition nfix)))))))

(local
 (defthm fn-bps-target-spine-cons-by-definition
   (equal (fn-bps-cursor-spinep (cons key keys) (cons (cons key value) cursor))
          (fn-bps-cursor-spinep keys cursor))))

(defthm fn-bps-target-start-establishes-fixed-spine
  (fn-bps-cursor-spinep *fn-bps-target-spine*
                        (fn-bps-target-start bundle bindings opaque limits))
  :hints (("Goal" :in-theory (e/d (fn-bps-target-start) (fn-bps-cursor-spinep)))))

(defthm fn-bps-target-drive-preserves-cursor-spine
  (implies (fn-bps-cursor-spinep keys cursor)
           (fn-bps-cursor-spinep keys (car (fn-bps-target-drive cursor quantum))))
  :hints (("Goal" :induct (fn-bps-target-drive cursor quantum)
           :in-theory (e/d (fn-bps-target-drive fn-bps-field)
                           (fn-bps-cursor-spinep fn-bps-target-unit fn-bps-get)))))

(defthm fn-bps-target-step-preserves-cursor-spine
  (implies (fn-bps-cursor-spinep keys cursor)
           (fn-bps-cursor-spinep keys (fn-bps-field 2 (fn-bps-target-step cursor quantum))))
  :hints (("Goal" :in-theory (e/d (fn-bps-target-step fn-bps-field)
                                 (fn-bps-cursor-spinep fn-bps-get fn-bps-target-drive)))))
