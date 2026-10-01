; Logical first-match observation of the actual bounded current-C producer.
(in-package "ACL2")
(include-book "consumer-remote-query-profile")

(defun fn-crpm-observe (s)
 (declare (xargs :guard t))
 (case (fn-cp-nth 4 s)
  (:lookup
   (let ((row (fn-cfg-row-lookup (fn-cp-nth 2 s) *fn-crp-limit-slot*)))
    (if (consp row) (fn-crp-policy-verdict (fn-cfg-limit-value row) (fn-cp-nth 3 s))
      '(:unavailable :consumer-query-limit))))
  (:ready (fn-cp-nth 5 s))
  (otherwise '(:refused :query-policy-phase))))

(defun fn-crpm-answer (answer)
 (declare (xargs :guard t))
 (if (member-eq (fn-cp-nth 0 answer) '(:yield :ready))
     (fn-crpm-observe (fn-cp-nth 1 answer)) answer))

(local
 (defthm fn-crpm-policy-is-final
  (not (member-eq (car (fn-crp-policy-verdict g r)) '(:yield :ready)))
  :hints (("Goal" :in-theory (e/d (fn-crp-policy-verdict fn-cp-nth)
                 (fn-crp-event-ceiling fn-frame-specs-width fn-cr-spec fn-cr-read-bound fn-cp-uintp))))))

(defthm fn-crp-tick-is-current-config-query-limit-lookup
 (implies (and (equal key (fn-cp-nth 1 s)) (equal record-ceiling (fn-cp-nth 3 s)))
          (equal (fn-crpm-answer (fn-crp-tick s key record-ceiling)) (fn-crpm-observe s)))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
          :use ((:instance fn-crpm-policy-is-final
                   (g (fn-cfg-limit-value (car (fn-cp-nth 2 s)))) (r (fn-cp-nth 3 s))))
          :expand ((fn-cfg-row-lookup (fn-cp-nth 2 s) *fn-crp-limit-slot*))
          :in-theory (e/d (fn-crp-tick fn-crp-state fn-crpm-answer fn-crpm-observe
                          fn-cfg-limit-slot fn-cp-nth fn-cfg-row-a fn-cfg-ag-car)
                         (fn-crpm-policy-is-final fn-crp-policy-verdict fn-cfg-row-lookup fn-cfg-limit-value)))))

(defthm fn-crp-query-policy-is-codec-and-record-representable
 (implies (eq (fn-cp-nth 0 (fn-crp-policy-verdict groups record-ceiling)) :query-policy)
          (and (posp groups) (fn-cp-uintp groups) (fn-frame-spec-listp (fn-cr-spec groups))
               (<= (fn-frame-specs-width (fn-cr-spec groups)) *fn-frame-max-payload*)
               (natp record-ceiling) (fn-crr-profilep record-ceiling) (<= (fn-crp-event-ceiling groups) record-ceiling)
               (equal (fn-cp-nth 1 (fn-crp-policy-verdict groups record-ceiling)) groups)
               (equal (fn-cp-nth 2 (fn-crp-policy-verdict groups record-ceiling)) (fn-cr-read-bound groups))))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d (fn-crp-policy-verdict fn-cp-nth)
                               (fn-cr-spec fn-cr-read-bound fn-frame-spec-listp fn-frame-specs-width fn-crp-event-ceiling fn-cp-uintp fn-crr-profilep)))))

(in-theory (disable fn-crpm-observe fn-crpm-answer))
