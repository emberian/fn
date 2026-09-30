; Exact scheduling cuts of the actual ASB drive. This is independent of
; whole-window/provider refinement and proves no grammar invariant by itself.
(in-package "ACL2")
(include-book "bpsec-asb")

(defthm fn-bps-asb-drive-consumed-is-natural
  (natp (fn-bps-field 1 (fn-bps-asb-drive cursor octets quantum)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :induct (fn-bps-asb-drive cursor octets quantum)
           :in-theory (e/d (fn-bps-asb-drive fn-bps-field)
                           (fn-bps-get fn-bps-stop fn-bps-internal-stagep fn-bps-internal-step
                            fn-bps-stage fn-bps-asb-octet)))))

(defthm fn-bps-asb-drive-normalizes-quantum
  (equal (fn-bps-asb-drive cursor octets (nfix quantum))
         (fn-bps-asb-drive cursor octets quantum))
  :hints (("Goal" :expand ((fn-bps-asb-drive cursor octets (nfix quantum))
                          (fn-bps-asb-drive cursor octets quantum))
           :in-theory (disable fn-bps-get fn-bps-stop fn-bps-internal-stagep fn-bps-internal-step
                               fn-bps-stage fn-bps-asb-octet))))

(local
 (defthm fn-bps-asb-drive-three-fields-by-definition
   (equal (list (fn-bps-field 0 (fn-bps-asb-drive cursor octets quantum))
                (fn-bps-field 1 (fn-bps-asb-drive cursor octets quantum))
                (fn-bps-field 2 (fn-bps-asb-drive cursor octets quantum)))
          (fn-bps-asb-drive cursor octets quantum))
   :hints (("Goal" :induct (fn-bps-asb-drive cursor octets quantum)
            :in-theory (e/d (fn-bps-asb-drive fn-bps-field)
                            (fn-bps-get fn-bps-stop fn-bps-internal-stagep fn-bps-internal-step
                             fn-bps-stage fn-bps-asb-octet))))
   :rule-classes nil))

(local
 (defthm fn-bps-get-of-other-put-by-definition
   (implies (not (equal wanted changed))
            (equal (fn-bps-get wanted (fn-bps-put changed value cursor))
                   (fn-bps-get wanted cursor)))
   :hints (("Goal" :induct (fn-bps-put changed value cursor)))))

(local
 (defthm fn-bps-get-of-terminal-put-by-definition
   (implies (not (equal status :more))
            (not (equal (fn-bps-get :status (fn-bps-put :status status cursor)) :more)))
   :hints (("Goal" :induct (fn-bps-put :status status cursor)))))

(local
 (defthm fn-bps-stop-is-terminal-by-definition
   (implies (not (equal status :more))
            (not (equal (fn-bps-get :status (fn-bps-stop status reason cursor)) :more)))
   :hints (("Goal" :in-theory (e/d (fn-bps-stop) (fn-bps-get fn-bps-put))))))

(local
 (defthm fn-bps-nfix-natural-scheduling-by-definition
   (implies (natp x) (equal (nfix x) x))))

(defthm fn-bps-asb-drive-composes-quanta
  (let* ((first (fn-bps-asb-drive cursor octets q1))
         (second (fn-bps-asb-drive (fn-bps-field 0 first) (fn-bps-field 2 first) q2)))
    (equal (fn-bps-asb-drive cursor octets (+ (nfix q1) (nfix q2)))
           (list (fn-bps-field 0 second)
                 (+ (fn-bps-field 1 first) (fn-bps-field 1 second))
                 (fn-bps-field 2 second))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-bps-asb-drive cursor octets q1)
           :expand ((fn-bps-asb-drive cursor octets q1)
                    (fn-bps-asb-drive cursor octets (+ (nfix q1) (nfix q2))))
           :in-theory (e/d (fn-bps-asb-drive fn-bps-field)
                           (fn-bps-get fn-bps-stop fn-bps-internal-stagep fn-bps-internal-step
                            fn-bps-stage fn-bps-asb-octet
                            fn-bps-asb-drive-rest-is-exact-unconsumed-suffix
                            (:definition nfix))))
          ("Subgoal *1/1" :use ((:instance fn-bps-asb-drive-three-fields-by-definition
                                          (quantum q2))))
          ("Subgoal *1/2" :use ((:instance fn-bps-asb-drive-three-fields-by-definition
                                          (quantum q2))))))
