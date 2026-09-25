;; fn: the frontier program's root barrier, by the step (lane k0-cuts, PKT-083).
;;
;; fn-bs-k0-frontier-durable-cut-relation-by-step: the frontier program's
;; pair 13 (after fsync_dir(root), run_store.py:891) is related, by the
;; keystone fn-bs-step-preserves-k0-coverage at pair 11, whose root barrier
;; is now a step kind (the :ok arm; fn-bs-k0s-root-fence-preserves-relation).
;; fn-bs-k0-frontier-reserved-cut-relation-by-step (moved here from
;; byte-store-k0-step-bridge) now takes its predecessor from it, so the whole
;; frontier chain is derived from the entry pair by the keystone.
(in-package "ACL2")
(include-book "byte-store-k0-step-bridge")

(defthm fn-bs-k0f-frontier-program-root-barrier
  (let ((prog (fn-bs-frontier-program stage octets)))
    (and (equal (nth 12 prog) '(:fsync-dir :root))
         (consp (nthcdr 13 prog))))
  :hints (("Goal" :in-theory (enable fn-bs-frontier-program))))
(defthm fn-bs-k0-frontier-durable-cut-relation-by-step
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-frontier-inputp ks stage octets)
                (not (fn-bs-lookup bs :staging stage)))
           (let ((p (nth 13 (fn-bs-run bs ks (fn-bs-frontier-program stage octets) nil groups capacity))))
             (fn-bs-store-relation (car p) (cdr p))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-k0-frontier-attempted-cut-relation-by-step
                 fn-bs-k0-frontier-dir-cut-kernel-candidate-and-phase
                 (:instance fn-bs-k0c-related-pair-is-consp
                  (x (nth 11 (fn-bs-run bs ks (fn-bs-frontier-program stage octets) nil groups capacity))))
                 (:instance fn-bs-k0b-cut-after-step
                  (k 11) (steps (fn-bs-frontier-program stage octets)) (g groups) (c capacity))
                 (:instance fn-bs-k0b-cut-after-step-pair
                  (k 11) (steps (fn-bs-frontier-program stage octets)) (g groups) (c capacity))
                 (:instance fn-bs-k0b-run-consp-backward (k 12) (steps (fn-bs-frontier-program stage octets)) (outs nil) (g groups) (c capacity))
                 (:instance fn-bs-k0b-syscall-carries-kernel (k 11) (steps (fn-bs-frontier-program stage octets)) (g groups) (c capacity))
                 (:instance fn-bs-k0b-relation-has-no-root-marker
                  (b (car (nth 11 (fn-bs-run bs ks (fn-bs-frontier-program stage octets) nil groups capacity))))
                  (k (cdr (nth 11 (fn-bs-run bs ks (fn-bs-frontier-program stage octets) nil groups capacity)))))
                 (:instance fn-bs-k0b-covered-without-root-marker-is-related
                  (b (car (nth 13 (fn-bs-run bs ks (fn-bs-frontier-program stage octets) nil groups capacity))))
                  (k (cdr (nth 13 (fn-bs-run bs ks (fn-bs-frontier-program stage octets) nil groups capacity))))))
           :in-theory (e/d (fn-bs-k0b-frontier-program-steps fn-bs-k0f-frontier-program-root-barrier fn-bs-k0-step-inputp
                            fn-bs-replay-visiblep fn-bs-k0c-ok-kinds-return-ok fn-bs-k0b-fsync-ok-results
                            fn-bs-k0s-fsync-dir-ok-is-fence fn-bs-k0b-fence-dir-keeps-no-root-marker)
                           (fn-bs-run fn-bs-store-relation fn-bs-frontier-program nth nthcdr fn-bs-frontier-inputp
                            fn-bs-lookup fn-sf-statep fn-bs-statep fn-bs-k0-coveredp fn-bs-fence-dir
                            fn-bs-k0m-has-root-marker fn-bs-k0s-marker-pendingp)))
          (and stable-under-simplificationp
               '(:in-theory (e/d (fn-bs-k0b-frontier-program-steps fn-bs-k0f-frontier-program-root-barrier
                                  fn-bs-replay-visiblep fn-bs-k0c-ok-kinds-return-ok fn-bs-k0b-fsync-ok-results
                                  fn-bs-k0s-fsync-dir-ok-is-fence fn-bs-k0b-fence-dir-keeps-no-root-marker fn-bs-step fn-bs-fsync-dir)
                           (fn-bs-run fn-bs-store-relation fn-bs-frontier-program nth nthcdr fn-bs-frontier-inputp
                            fn-bs-lookup fn-sf-statep fn-bs-statep fn-bs-k0-coveredp fn-bs-fence-dir
                            fn-bs-k0m-has-root-marker fn-bs-k0s-marker-pendingp))))))
(defthm fn-bs-k0-frontier-reserved-cut-relation-by-step
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-frontier-inputp ks stage octets)
                (not (fn-bs-lookup bs :staging stage)))
           (let ((p (nth 15 (fn-bs-run bs ks (fn-bs-frontier-program stage octets) nil groups capacity))))
             (fn-bs-store-relation (car p) (cdr p))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-k0-frontier-durable-cut-relation-by-step fn-bs-k0-frontier-dir-cut-kernel-candidate-and-phase
                 fn-bs-k0-frontier-dir-cut-committedp
                 (:instance fn-bs-k0c-related-pair-is-consp
                  (x (nth 13 (fn-bs-run bs ks (fn-bs-frontier-program stage octets) nil groups capacity))))
                 (:instance fn-bs-k0c-cut-pair-is-previous-pair
                  (k 12) (steps (fn-bs-frontier-program stage octets)) (outs nil) (g groups) (c capacity))
                 (:instance fn-bs-k0b-cut-after-step
                  (k 13) (steps (fn-bs-frontier-program stage octets)) (g groups) (c capacity))
                 (:instance fn-bs-k0b-cut-after-step-pair
                  (k 13) (steps (fn-bs-frontier-program stage octets)) (g groups) (c capacity))
                 (:instance fn-bs-k0b-relation-has-no-root-marker
                  (b (car (nth 13 (fn-bs-run bs ks (fn-bs-frontier-program stage octets) nil groups capacity))))
                  (k (cdr (nth 13 (fn-bs-run bs ks (fn-bs-frontier-program stage octets) nil groups capacity)))))
                 (:instance fn-bs-k0b-covered-without-root-marker-is-related
                  (b (car (nth 15 (fn-bs-run bs ks (fn-bs-frontier-program stage octets) nil groups capacity))))
                  (k (cdr (nth 15 (fn-bs-run bs ks (fn-bs-frontier-program stage octets) nil groups capacity))))))
           :in-theory (e/d (fn-bs-k0b-frontier-program-steps fn-bs-k0-step-inputp fn-bs-k0-observation-inputp
                            fn-bs-replay-visiblep fn-bs-k0c-ok-kinds-return-ok)
                           (fn-bs-run fn-bs-store-relation fn-bs-frontier-program nth nthcdr fn-bs-frontier-inputp
                            fn-bs-lookup fn-sf-statep fn-bs-statep fn-bs-step fn-bs-k0-coveredp
                            fn-bs-frontier-directory-committedp fn-bs-frontier-noncommit-observationp)))))
