; Field scratch provenance carried by the actual frozen report cursor.
; This is a source relation, not a runtime/profile or lifetime grant.
(in-package "ACL2")
(include-book "owner-retire-stream")
(include-book "operator-report-fields-space")

(defun fn-orr-space-relationp (cursor)
  (declare (xargs :guard t))
  (and (fn-orr-invariant cursor)
       (if (equal (nth 0 cursor) :emit)
           (fn-orf-space-relationp (nth 8 cursor))
         t)))

(defthm fn-orr-space-start
  (fn-orr-space-relationp (fn-orr-start outcome oc))
  :hints (("Goal" :in-theory
           (enable fn-orr-space-relationp fn-orr-start))))

(defthm fn-orr-space-schedule
  (implies (and (fn-orf-fieldsp fields) (natp u) (natp held) (natp reserved)
                (member-eq resume '(:peers :obligations :release :done)))
           (fn-orr-space-relationp
            (fn-orr-schedule fields resume feeds pins root u held reserved outcome)))
  :hints (("Goal" :use ((:instance fn-orf-space-start))
           :in-theory
           (e/d (fn-orr-space-relationp fn-orr-invariant fn-orr-schedule
                 fn-orr-cursor)
                (fn-orf-start fn-orf-space-relationp fn-orf-invariant)))))

(defthm fn-orr-space-step
  (implies (fn-orr-space-relationp cursor)
           (fn-orr-space-relationp (mv-nth 0 (fn-orr-step cursor))))
  :hints (("Goal"
           :use ((:instance fn-orr-step-preserves-invariant)
                 (:instance fn-orf-space-step (c (nth 8 cursor))))
           :in-theory
           (e/d (fn-orr-space-relationp fn-orr-step fn-orr-cursor
                 fn-orr-invariant)
                (fn-orf-step fn-orf-start fn-orf-invariant
                 fn-orf-space-relationp fn-orf-space-step
                 fn-orr-step-preserves-invariant fn-orr-schedule
                 fn-ord-peer fn-ord-header fn-ord-obligation fn-ord-end)))))
