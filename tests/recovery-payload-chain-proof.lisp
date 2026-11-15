; SOURCE-ONLY theorem obligations: not admitted, proved or certified.
; These statements name the served helpers and the actual claim result;
; they do not substitute an independent list/allocator model.
(in-package "ACL2")
(include-book "../books/assembly")

; Every successful step consumes a positive bounded rank. At rank one
; exactly, the returned link is zero. Repeated successful steps with the
; caller decrementing rank therefore terminate without a whole-store scan.
(defthm fn2-recovery-payload-node-bounded-descent
 (implies
  (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
       (eq (mv-nth 0 (fn2-recovery-payload-node journal commit je ja token remaining fn2-core)) :ok))
  (and (posp remaining)
       (unsigned-byte-p 32 remaining)
       (<= remaining (mv-nth 0 (fn2-recovery-geometry fn2-core)))
       (equal (equal (mv-nth 6 (fn2-recovery-payload-node journal commit je ja token remaining fn2-core)) 0)
              (equal remaining 1))
       (< (nfix (- remaining 1)) remaining)))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn2-recovery-payload-node fn2-recovery-payload-head
  fn2-recovery-payload-journal fn2-recovery-payload-linkp fn2-recovery-payload-stepp))))

; Successful actual mutation prepends one unique physical position, keeps
; the exact mapped journal identity, and increases its bounded cardinality.
; Node refusal for already claimed positions is part of CLAIM, not a premise
; allowing the theorem to forget duplicate ownership.
(defthm fn2-recovery-claim-prepends-counted-node
 (implies
  (and (fn2-corep fn2-core) (fn2-core-wfp fn2-core)
       (eq (mv-nth 0 (fn2-recovery-payload-head journal commit je ja fn2-core)) :ok)
       (eq (mv-nth 0 (fn2-recovery-claim p epoch allocation kind owner commit fn2-core)) :ok))
  (let ((after (mv-nth 2 (fn2-recovery-claim p epoch allocation kind owner commit fn2-core))))
   (and (eq (mv-nth 0 (fn2-recovery-payload-head journal commit je ja after)) :ok)
        (equal (mv-nth 1 (fn2-recovery-payload-head journal commit je ja after)) (+ 1 p))
        (equal (mv-nth 2 (fn2-recovery-payload-head journal commit je ja after))
               (+ 1 (mv-nth 2 (fn2-recovery-payload-head journal commit je ja fn2-core))))
        (<= (mv-nth 2 (fn2-recovery-payload-head journal commit je ja after))
            (mv-nth 0 (fn2-recovery-geometry after)))
        (equal (fn2-recovery-payload-node journal commit je ja (+ 1 p)
                 (mv-nth 2 (fn2-recovery-payload-head journal commit je ja after)) after)
               (list :ok p epoch allocation kind owner
                     (mv-nth 1 (fn2-recovery-payload-head journal commit je ja fn2-core)))))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn2-recovery-claim fn2-recovery-payload-node
  fn2-recovery-payload-head fn2-recovery-payload-journal
  fn2-recovery-payload-linkp fn2-recovery-payload-stepp))))
