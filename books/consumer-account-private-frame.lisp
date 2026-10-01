; Actual full7 private stage frame, lifted from the existing logical authority
; keystone through the carried producer, binding and config-preparation arms.
(in-package "ACL2")
(include-book "consumer-configured-authority-finish")

(local
 (defthm fn-acj-config-preparation-tick-is-never-ok
  (not (equal (car (fn-bcp-tick preparation rowcarry)) :ok))
  :hints (("Goal" :in-theory
           (e/d (fn-bcp-tick fn-cp-nth)
                (fn-bcp-with fn-cait-size fn-caac-list-cons
                 fn-bcp-intent-lookup fn-cfg-accounts fn-cfg-value))))))

(defthm fn-acj-private-stage-preserves-current-authority
 (let* ((one (fn-acj-stage cp metadata preparation config event expected rowcarry))
        (before (fn-cp-nth 6 cp)) (after (fn-cp-nth 6 (fn-cp-nth 1 one))))
  (implies (eq (fn-cp-nth 0 one) :ok)
   (and (equal (fn-cp-nth 1 after) (fn-cp-nth 1 before))
        (equal (fn-cp-nth 2 after) (fn-cp-nth 2 before))
        (equal (fn-cp-nth 3 after) (fn-cp-nth 3 before))
        (equal (fn-cp-nth 4 after) (fn-cp-nth 4 before)))))
 :hints (("Goal"
          :use ((:instance fn-caa-stages-preserve-current-authority (s cp)))
          :in-theory
          (e/d (fn-acj-stage fn-acj-stage-advance fn-caa-authority-pending
                 fn-cp-state-carry fn-cp-nth)
               (fn-caac-step fn-caa-step fn-caac-metadata fn-acj-metadata5
                fn-bcp-stage fn-bcp-tick fn-bcp-expect fn-bcp-begin fn-bcp-seal
                fn-cab-eventp fn-cac-eventp fn-caa-matching-pendingp
                fn-caa-stages-preserve-current-authority)))))
