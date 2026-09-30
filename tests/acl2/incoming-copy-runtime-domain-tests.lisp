(in-package "ACL2")
(include-book "../../books/incoming-copy-runtime-domain")
(include-book "incoming-pool-holder-tests")
(defun icrd-observe-in (dimension-limit total-limit positive-fixnum fn-input-copy fn-page-read-pool)
 (declare (xargs :stobjs (fn-input-copy fn-page-read-pool) :verify-guards nil))
 (mv-let (word fn-page-read-pool)
  (fn-owner-page-read-install '(8192 0 0 0 8) 0 0 0 8 fn-page-read-pool)
  (declare (ignore word))
  (mv-let (word fn-page-read-pool) (iohp-install-backing fn-page-read-pool)
   (declare (ignore word))
   (mv-let (word token fn-page-read-pool)
    (fn-owner-incoming-reserve '(256 0 0 0 1) fn-page-read-pool)
    (declare (ignore word))
    (mv-let (word fn-input-copy fn-page-read-pool)
     (fn-owner-incoming-copy-start token 20 nil fn-input-copy fn-page-read-pool)
     (declare (ignore word))
     (let ((plan (fn-input-copy-view fn-input-copy)))
      (mv-let (word start count end fn-input-copy fn-page-read-pool)
       (fn-owner-incoming-copy-next token fn-input-copy fn-page-read-pool)
       (mv (list (fn-isr-planp plan) (natp dimension-limit) (natp total-limit)
                 (< (fn-prl-nth 2 plan) dimension-limit) (< (fn-prl-nth 2 plan) total-limit)
                 (equal (fn-srr-observed-limits-status positive-fixnum dimension-limit total-limit)
                        :compatible)
                 (fn-srr-backing-span-domain-p start count end
                   (fn-prl-nth 1 plan) (fn-prl-nth 2 plan) dimension-limit total-limit)
                 (fn-srr-span-scalars-fit-p start count end
                   (fn-prl-nth 1 plan) (fn-prl-nth 2 plan) positive-fixnum)
                 word start count end)
           fn-input-copy fn-page-read-pool))))))))
(defun icrd-observe (dimension-limit total-limit positive-fixnum)
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn-input-copy
  (mv-let (result fn-input-copy)
   (with-local-stobj fn-page-read-pool
    (mv-let (result fn-input-copy fn-page-read-pool)
     (icrd-observe-in dimension-limit total-limit positive-fixnum fn-input-copy fn-page-read-pool)
     (mv result fn-input-copy))) result)))
; Complete positive antecedents and conclusions for both literal theorems.
(assert-event (equal (icrd-observe 17592186044416 17592186044416 4611686018427387903)
                     '(t t t t t t t t :copy 0 20 20)))
; Hypothesis removals for the span-domain theorem affirm every retained
; hypothesis. These runtime-limit mutations are not actual startup observations.
(assert-event (equal (icrd-observe 129/2 65 4611686018427387903)
                     '(t nil t t t nil nil t :copy 0 20 20)))
(assert-event (equal (icrd-observe 65 129/2 4611686018427387903)
                     '(t t nil t t nil nil t :copy 0 20 20)))
(assert-event (equal (icrd-observe 64 65 4611686018427387903)
                     '(t t t nil t nil nil t :copy 0 20 20)))
(assert-event (equal (icrd-observe 65 64 4611686018427387903)
                     '(t t t t nil nil nil t :copy 0 20 20)))
; Compatible-runtime premise removal for scalar fit: actual returned capacity
; exceeds the mutated fixnum boundary, while plan and dimension bound remain.
(assert-event (equal (icrd-observe 17592186044416 17592186044416 0)
                     '(t t t t t nil t nil :copy 0 20 20)))

; Corrupted logical controller states, not reachable guarded/native packets.
; The removed plan invariant is false; both retained strict capacity bounds,
; natural limits and the actual callback's failed span conclusion are checked.
(defthm icrd-plan-removal-mutated-logical-state
 (let* ((bad '((:incoming 1) 20 64 4096 0 (:incoming-copy (:incoming 1) 100 1) :copying))
        (pool '(nil :served ((:input-backing 0 64)
                     ((:incoming 1) :setup (256 0 0 0 1) (:incoming-controller (:incoming 1))))))
        (result (fn-owner-incoming-copy-next '(:incoming 1) bad pool)))
  (and (not (fn-isr-planp bad)) (natp 65) (natp 65)
       (< (fn-prl-nth 2 bad) 65) (< (fn-prl-nth 2 bad) 65)
       (not (fn-srr-backing-span-domain-p
              (mv-nth 1 result) (mv-nth 2 result) (mv-nth 3 result)
              (fn-prl-nth 1 bad) (fn-prl-nth 2 bad) 65 65))))
 :rule-classes nil
 :hints (("Goal" :in-theory
          (enable fn-owner-incoming-copy-next fn-owner-incoming-copy-associatedp
                  fn-owner-incoming-row fn-owner-incoming-keep-row fn-ibc-carrier-row
                  fn-ioh-matches fn-input-copy-next fn-icc$a-next fn-input-copy-token fn-icc$a-token
                  fn-isr-next fn-isr-planp fn-isr-grantp fn-isr-plan fn-isr-tail fn-prl-nth
                  fn-srr-backing-span-domain-p))))
(defthm icrd-fit-plan-removal-mutated-logical-state
 (let* ((bad '((:incoming 1) 20 64 4096 0
               (:incoming-copy (:incoming 1) 4611686018427387903 1) :copying))
        (pool '(nil :served ((:input-backing 0 64)
                     ((:incoming 1) :setup (256 0 0 0 1) (:incoming-controller (:incoming 1))))))
        (result (fn-owner-incoming-copy-next '(:incoming 1) bad pool)))
  (and (not (fn-isr-planp bad))
       (equal (fn-srr-observed-limits-status 4611686018427387903 17592186044416 17592186044416)
              :compatible)
       (< (fn-prl-nth 2 bad) 17592186044416)
       (not (fn-srr-span-scalars-fit-p
              (mv-nth 1 result) (mv-nth 2 result) (mv-nth 3 result)
              (fn-prl-nth 1 bad) (fn-prl-nth 2 bad) 4611686018427387903))))
 :rule-classes nil
 :hints (("Goal" :in-theory
          (enable fn-owner-incoming-copy-next fn-owner-incoming-copy-associatedp
                  fn-owner-incoming-row fn-ibc-carrier-row fn-ioh-matches
                  fn-input-copy-next fn-icc$a-next fn-input-copy-token fn-icc$a-token
                  fn-isr-next fn-isr-planp fn-isr-grantp fn-isr-plan fn-isr-tail fn-prl-nth
                  fn-srr-observed-limits-status fn-srr-span-scalars-fit-p))))
(defthm icrd-fit-capacity-removal-mutated-logical-state
 (let* ((plan '((:incoming 1) 20 4611686018427387904 4096 0 nil :copying))
        (pool '(nil :served ((:input-backing 0 4611686018427387904)
                     ((:incoming 1) :setup (256 0 0 0 1) (:incoming-controller (:incoming 1))))))
        (result (fn-owner-incoming-copy-next '(:incoming 1) plan pool)))
  (and (fn-isr-planp plan)
       (equal (fn-srr-observed-limits-status 4611686018427387903 17592186044416 17592186044416)
              :compatible)
       (not (< (fn-prl-nth 2 plan) 17592186044416))
       (not (fn-srr-span-scalars-fit-p
              (mv-nth 1 result) (mv-nth 2 result) (mv-nth 3 result)
              (fn-prl-nth 1 plan) (fn-prl-nth 2 plan) 4611686018427387903))))
 :rule-classes nil
 :hints (("Goal" :in-theory
          (enable fn-owner-incoming-copy-next fn-owner-incoming-copy-associatedp
                  fn-owner-incoming-row fn-ibc-carrier-row fn-ioh-matches
                  fn-input-copy-next fn-icc$a-next fn-input-copy-token fn-icc$a-token
                  fn-isr-next fn-isr-planp fn-isr-grantp fn-isr-plan fn-isr-tail fn-prl-nth
                  fn-srr-observed-limits-status fn-srr-span-scalars-fit-p))))
