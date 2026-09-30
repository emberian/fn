; Conditional operational representation join, not allocation attestation.
; Installation must bind the capacity in the carried plan to the actual raw
; backing and establish the observed runtime coordinate before activation.
(in-package "ACL2")
(include-book "../host/page-read-host")
(include-book "selected-runtime-representation")
(defthm fn-owner-incoming-copy-next-returned-span-domain
 (let* ((plan (fn-input-copy-view fn-input-copy))
        (result (fn-owner-incoming-copy-next token fn-input-copy fn-page-read-pool)))
  (implies (and (fn-isr-planp plan)
                (natp dimension-limit) (natp total-limit)
                (< (fn-prl-nth 2 plan) dimension-limit)
                (< (fn-prl-nth 2 plan) total-limit)
)
           (and (fn-srr-backing-span-domain-p
                  (mv-nth 1 result) (mv-nth 2 result) (mv-nth 3 result)
                  (fn-prl-nth 1 plan) (fn-prl-nth 2 plan)
                  dimension-limit total-limit)
                (<= (mv-nth 2 result) *fn-cbud-read-quantum*))))
 :rule-classes nil
 :hints (("Goal" :in-theory
          (enable fn-owner-incoming-copy-next fn-input-copy-next fn-icc$a-next
                  fn-input-copy-view fn-icc$a-view fn-isr-next fn-isr-planp
                  fn-isr-grantp fn-isr-plan fn-isr-tail fn-prl-nth
                  fn-srr-backing-span-domain-p))))
(defthm fn-owner-incoming-copy-next-returned-scalars-fit
 (let* ((plan (fn-input-copy-view fn-input-copy))
        (result (fn-owner-incoming-copy-next token fn-input-copy fn-page-read-pool)))
  (implies (and (fn-isr-planp plan)
                (equal (fn-srr-observed-limits-status positive-fixnum dimension-limit total-limit)
                       :compatible)
                (< (fn-prl-nth 2 plan) dimension-limit)
)
           (fn-srr-span-scalars-fit-p
             (mv-nth 1 result) (mv-nth 2 result) (mv-nth 3 result)
             (fn-prl-nth 1 plan) (fn-prl-nth 2 plan) positive-fixnum)))
 :rule-classes nil
 :hints (("Goal" :use
          ((:instance fn-owner-incoming-copy-next-returned-span-domain)
           (:instance fn-srr-compatible-backed-span-scalars-by-definition
                      (start (mv-nth 1 (fn-owner-incoming-copy-next token fn-input-copy fn-page-read-pool)))
                      (count (mv-nth 2 (fn-owner-incoming-copy-next token fn-input-copy fn-page-read-pool)))
                      (end (mv-nth 3 (fn-owner-incoming-copy-next token fn-input-copy fn-page-read-pool)))
                      (total (fn-prl-nth 1 (fn-input-copy-view fn-input-copy)))
                      (capacity (fn-prl-nth 2 (fn-input-copy-view fn-input-copy)))))
          :in-theory (enable fn-srr-observed-limits-status))))
