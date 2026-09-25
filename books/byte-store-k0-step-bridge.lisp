; fn: the per-cut K0 theorems as corollaries of the general step
; (lane k0-corollaries, T16 model side).
;
; Keystone: fn-bs-step-preserves-k0-coverage (byte-store-k0-step).  Each
; `-by-step' theorem below restates a per-cut theorem of byte-store-k0,
; -k0-staging or -k0-marker (which stay in place; the registry cites them)
; and proves it by instantiating the keystone at the pair before the cut's
; step, after discharging fn-bs-k0-step-inputp there.  A covered pair with
; no committed-history rename pending is related
; (fn-bs-k0b-covered-without-root-rename-is-related).
;
; Marker program (in byte-store-k0-step-bridge-marker): every pair is derived from the entry pair by the keystone
; alone (fn-bs-k0b-marker-pairs-by-step), then
;   fn-bs-k0-marker-cuts-relation-by-step, fn-bs-k0-marker-replaced-cut-relation-by-step.
; Marker error arms: fn-bs-step-at-marker-pairs-preserves-k0-coverage, at
; each of the five marker steps, for every outcome (the file barrier's with
; a well-formed crash selection), the result is covered and the kernel is
; the entry kernel, still :completing: no :emit-success has happened, so
; the transaction stays fenced.
; Frontier: replaced (from fn-bs-k0-frontier-staged-durable-cut-relation-by-step)
; and attempted; the durable and reserved cuts are in
; byte-store-k0-step-bridge-frontier.  Record: attempted (from
; fn-bs-k0-record-linked-cut-relation-by-step), durable, completing and the
; two cleanup cuts.  The prefix cuts of both programs and the generic run
; lemmas are in byte-store-k0-step-bridge-prefix (lane k0-cuts), so every
; frontier and record corollary is chained from the entry pair by the
; keystone.
(in-package "ACL2")
(include-book "byte-store-k0-step-bridge-prefix")

(defthm fn-bs-k0b-rename-keeps-root-rename-status
  (implies (or (not (equal ddir :root)) (equal dname *fn-bs-scan-frontier-name*))
           (equal (fn-bs-k0m-has-root-rename (fn-bs-pending (mv-nth 1 (fn-bs-rename b sdir sname ddir dname outcome))))
                  (fn-bs-k0m-has-root-rename (fn-bs-pending b))))
  :hints (("Goal" :in-theory (enable fn-bs-rename fn-bs-k0m-has-root-rename))))
(defthm fn-bs-k0b-frontier-program-steps
  (let ((prog (fn-bs-frontier-program stage octets)))
    (and (equal (car (nth 7 prog)) :cut)
         (equal (nth 8 prog) (list :rename :staging stage :root *fn-bs-frontier-name*))
         (equal (car (nth 9 prog)) :cut)
         (consp (nthcdr 9 prog))
         (equal (nth 10 prog) '(:observe (:frontier-replace :ok)))
         (equal (car (nth 11 prog)) :cut)
         (consp (nthcdr 11 prog))
         (equal (car (nth 13 prog)) :cut)
         (equal (nth 14 prog) '(:observe (:frontier-dir :ok)))
         (equal (car (nth 15 prog)) :cut)
         (consp (nthcdr 15 prog))))
  :hints (("Goal" :in-theory (enable fn-bs-frontier-program))))
(defthm fn-bs-k0b-rename-ok-result
  (implies (fn-bs-inop (fn-bs-lookup b sdir sname))
           (equal (mv-nth 0 (fn-bs-rename b sdir sname ddir dname :ok)) :ok))
  :hints (("Goal" :in-theory (e/d (fn-bs-rename) (fn-bs-lookup fn-bs-inop)))))
(defthm fn-bs-k0-frontier-replaced-cut-relation-by-step
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-frontier-inputp ks stage octets)
                (not (fn-bs-lookup bs :staging stage)))
           (let ((p (nth 9 (fn-bs-run bs ks (fn-bs-frontier-program stage octets) nil groups capacity))))
             (fn-bs-store-relation (car p) (cdr p))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-k0-frontier-staged-durable-cut-relation-by-step
                 fn-bs-k0-frontier-observation-pair-facts
                 fn-bs-k0-frontier-file-observation-new-inode-fenced
                 fn-bs-k0-frontier-file-observation-has-new-inode
                 fn-bs-store-relation-unfolds
                 (:instance fn-bs-k0c-related-pair-is-consp
                  (x (nth 7 (fn-bs-run bs ks (fn-bs-frontier-program stage octets) nil groups capacity))))
                 (:instance fn-bs-k0c-cut-pair-is-previous-pair
                  (k 6) (steps (fn-bs-frontier-program stage octets)) (outs nil) (g groups) (c capacity))
                 (:instance fn-bs-k0b-cut-after-step
                  (k 7) (steps (fn-bs-frontier-program stage octets)) (g groups) (c capacity))
                 (:instance fn-bs-k0b-cut-after-step-pair
                  (k 7) (steps (fn-bs-frontier-program stage octets)) (g groups) (c capacity))
                 (:instance fn-bs-k0b-relation-has-no-root-rename
                  (b (car (nth 7 (fn-bs-run bs ks (fn-bs-frontier-program stage octets) nil groups capacity))))
                  (k (cdr (nth 7 (fn-bs-run bs ks (fn-bs-frontier-program stage octets) nil groups capacity)))))
                 (:instance fn-bs-k0b-covered-without-root-rename-is-related
                  (b (car (nth 9 (fn-bs-run bs ks (fn-bs-frontier-program stage octets) nil groups capacity))))
                  (k (cdr (nth 9 (fn-bs-run bs ks (fn-bs-frontier-program stage octets) nil groups capacity))))))
           :in-theory (e/d (fn-bs-frontier-inputp fn-bs-k0-step-inputp fn-bs-step
                            fn-bs-replay-visiblep fn-sf-frontier-new-visiblep fn-sf-record-present-visiblep
                            fn-bs-dir-idp fn-bs-inop)
                           (fn-bs-frontier-program nth nthcdr fn-bs-run fn-bs-store-relation fn-sf-statep fn-bs-statep fn-bs-durable-frontier
                            fn-bs-durable-records fn-bs-durable-content fn-bs-lookup fn-bs-fencedp
                            fn-bs-make fn-bs-rename fn-bs-k0-coveredp fn-bs-k0m-has-root-rename
                            fn-bs-k0s-root-rename-targetp fn-bs-k0s-root-rename-pendingp fn-bs-crash-choicesp)))))
(defthm fn-bs-k0b-frontier-attempted-kernel
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-frontier-inputp ks stage octets)
                (not (fn-bs-lookup bs :staging stage)))
           (let ((run (fn-bs-run bs ks (fn-bs-frontier-program stage octets) nil groups capacity)))
             (equal (fn-sf-phase (cdr (nth 9 run))) :frontier-data-durable)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-k0-frontier-replaced-cut-relation-by-step fn-bs-k0-frontier-observation-pair-facts
                 (:instance fn-bs-k0c-related-pair-is-consp
                  (x (nth 9 (fn-bs-run bs ks (fn-bs-frontier-program stage octets) nil groups capacity))))
                 (:instance fn-bs-k0b-run-consp-backward (k 8) (steps (fn-bs-frontier-program stage octets)) (outs nil) (g groups) (c capacity))
                 (:instance fn-bs-k0b-run-consp-backward (k 7) (steps (fn-bs-frontier-program stage octets)) (outs nil) (g groups) (c capacity))
                 (:instance fn-bs-k0b-syscall-carries-kernel (k 8) (steps (fn-bs-frontier-program stage octets)) (g groups) (c capacity))
                 (:instance fn-bs-k0b-syscall-carries-kernel (k 7) (steps (fn-bs-frontier-program stage octets)) (g groups) (c capacity))
                 (:instance fn-bs-k0b-syscall-carries-kernel (k 6) (steps (fn-bs-frontier-program stage octets)) (g groups) (c capacity)))
           :in-theory (e/d (fn-bs-k0b-frontier-program-steps)
                           (fn-bs-run fn-bs-store-relation fn-bs-frontier-program nth nthcdr fn-bs-frontier-inputp
                            fn-bs-lookup fn-sf-statep fn-bs-statep)))))
(defthm fn-bs-k0-frontier-attempted-cut-relation-by-step
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-frontier-inputp ks stage octets)
                (not (fn-bs-lookup bs :staging stage)))
           (let ((p (nth 11 (fn-bs-run bs ks (fn-bs-frontier-program stage octets) nil groups capacity))))
             (fn-bs-store-relation (car p) (cdr p))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-k0-frontier-replaced-cut-relation-by-step fn-bs-k0b-frontier-attempted-kernel
                 (:instance fn-bs-k0c-related-pair-is-consp
                  (x (nth 9 (fn-bs-run bs ks (fn-bs-frontier-program stage octets) nil groups capacity))))
                 (:instance fn-bs-k0b-cut-after-step
                  (k 9) (steps (fn-bs-frontier-program stage octets)) (g groups) (c capacity))
                 (:instance fn-bs-k0b-cut-after-step-pair
                  (k 9) (steps (fn-bs-frontier-program stage octets)) (g groups) (c capacity))
                 (:instance fn-bs-k0b-relation-has-no-root-rename
                  (b (car (nth 9 (fn-bs-run bs ks (fn-bs-frontier-program stage octets) nil groups capacity))))
                  (k (cdr (nth 9 (fn-bs-run bs ks (fn-bs-frontier-program stage octets) nil groups capacity)))))
                 (:instance fn-bs-k0b-covered-without-root-rename-is-related
                  (b (car (nth 11 (fn-bs-run bs ks (fn-bs-frontier-program stage octets) nil groups capacity))))
                  (k (cdr (nth 11 (fn-bs-run bs ks (fn-bs-frontier-program stage octets) nil groups capacity))))))
           :in-theory (e/d (fn-bs-k0b-frontier-program-steps fn-bs-k0-step-inputp fn-bs-k0-observation-inputp
                            fn-bs-frontier-noncommit-observationp fn-bs-replay-visiblep fn-bs-k0c-ok-kinds-return-ok)
                           (fn-bs-run fn-bs-store-relation fn-bs-frontier-program nth nthcdr fn-bs-frontier-inputp
                            fn-bs-lookup fn-sf-statep fn-bs-statep fn-bs-step fn-bs-k0-coveredp)))))
(defthm fn-bs-k0b-unlink-ok-result
  (implies (fn-bs-lookup b dir name)
           (equal (mv-nth 0 (fn-bs-unlink b dir name :ok)) :ok))
  :hints (("Goal" :in-theory (e/d (fn-bs-unlink) (fn-bs-lookup)))))
(defthm fn-bs-k0b-unlink-keeps-root-rename-status
  (equal (fn-bs-k0m-has-root-rename (fn-bs-pending (mv-nth 1 (fn-bs-unlink b dir name outcome))))
         (fn-bs-k0m-has-root-rename (fn-bs-pending b)))
  :hints (("Goal" :in-theory (enable fn-bs-unlink fn-bs-k0m-has-root-rename))))
(defthm fn-bs-k0b-first-syscall-keeps-kernel
  (implies (and (consp steps) (not (equal (car (car steps)) :observe)))
           (equal (cdr (nth 0 (fn-bs-run bs ks steps nil g c))) ks))
  :hints (("Goal" :expand ((fn-bs-run bs ks steps nil g c))
           :use ((:instance fn-bs-k0s-syscall-step-keeps-kernel (step (car steps)) (outcome :ok)))
           :in-theory (e/d () (fn-bs-step fn-bs-run)))))
(defthm fn-bs-k0b-cdr-of-cons-pair
  (implies (equal p (cons a b)) (equal (cdr p) b))
  :rule-classes nil)
(defthm fn-bs-k0b-observe-kernel-in-run
  (implies (and (natp k) (consp (nth (1+ k) (fn-bs-run bs ks steps nil g c)))
                (equal (car (nth (1+ k) steps)) :observe))
           (equal (cdr (nth (1+ k) (fn-bs-run bs ks steps nil g c)))
                  (fn-sf-dispatch (cdr (nth k (fn-bs-run bs ks steps nil g c))) (nth 1 (nth (1+ k) steps)) g c)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-k0c-nth-succ
                 (:instance fn-bs-k0s-observe-step-any
                  (bs (car (nth k (fn-bs-run bs ks steps nil g c))))
                  (ks (cdr (nth k (fn-bs-run bs ks steps nil g c))))
                  (step (nth (1+ k) steps)) (outcome :ok))
                 (:instance fn-bs-k0b-cdr-of-cons-pair
                  (p (nth (1+ k) (fn-bs-run bs ks steps nil g c)))
                  (a (mv-nth 1 (fn-bs-step (car (nth k (fn-bs-run bs ks steps nil g c)))
                                           (cdr (nth k (fn-bs-run bs ks steps nil g c)))
                                           (nth (1+ k) steps) :ok g c)))
                  (b (mv-nth 2 (fn-bs-step (car (nth k (fn-bs-run bs ks steps nil g c)))
                                           (cdr (nth k (fn-bs-run bs ks steps nil g c)))
                                           (nth (1+ k) steps) :ok g c)))))
           :in-theory (e/d () (fn-bs-run fn-bs-step nth fn-sf-dispatch)))))
(defthm fn-bs-k0b-record-linked-kernel
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-record-inputp ks stage name frame)
                (not (fn-bs-lookup bs :staging stage)))
           (let ((run (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity)))
             (equal (cdr (nth 8 run)) (fn-sf-record-file-result ks :ok))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-k0-record-linked-cut-relation-by-step
                 (:instance fn-bs-k0b-first-syscall-keeps-kernel (steps (fn-bs-record-program stage name frame)) (g groups) (c capacity))
                 (:instance fn-bs-k0c-related-pair-is-consp
                  (x (nth 8 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity))))
                 (:instance fn-bs-k0b-observe-kernel-in-run (k 4) (steps (fn-bs-record-program stage name frame)) (g groups) (c capacity))
                 (:instance fn-bs-k0b-run-consp-backward (k 0) (steps (fn-bs-record-program stage name frame)) (outs nil) (g groups) (c capacity))
                 (:instance fn-bs-k0b-run-consp-backward (k 1) (steps (fn-bs-record-program stage name frame)) (outs nil) (g groups) (c capacity))
                 (:instance fn-bs-k0b-run-consp-backward (k 2) (steps (fn-bs-record-program stage name frame)) (outs nil) (g groups) (c capacity))
                 (:instance fn-bs-k0b-run-consp-backward (k 3) (steps (fn-bs-record-program stage name frame)) (outs nil) (g groups) (c capacity))
                 (:instance fn-bs-k0b-run-consp-backward (k 4) (steps (fn-bs-record-program stage name frame)) (outs nil) (g groups) (c capacity))
                 (:instance fn-bs-k0b-run-consp-backward (k 5) (steps (fn-bs-record-program stage name frame)) (outs nil) (g groups) (c capacity))
                 (:instance fn-bs-k0b-run-consp-backward (k 6) (steps (fn-bs-record-program stage name frame)) (outs nil) (g groups) (c capacity))
                 (:instance fn-bs-k0b-run-consp-backward (k 7) (steps (fn-bs-record-program stage name frame)) (outs nil) (g groups) (c capacity))
                 (:instance fn-bs-k0b-syscall-carries-kernel (k 0) (steps (fn-bs-record-program stage name frame)) (g groups) (c capacity))
                 (:instance fn-bs-k0b-syscall-carries-kernel (k 1) (steps (fn-bs-record-program stage name frame)) (g groups) (c capacity))
                 (:instance fn-bs-k0b-syscall-carries-kernel (k 2) (steps (fn-bs-record-program stage name frame)) (g groups) (c capacity))
                 (:instance fn-bs-k0b-syscall-carries-kernel (k 3) (steps (fn-bs-record-program stage name frame)) (g groups) (c capacity))
                 (:instance fn-bs-k0b-syscall-carries-kernel (k 5) (steps (fn-bs-record-program stage name frame)) (g groups) (c capacity))
                 (:instance fn-bs-k0b-syscall-carries-kernel (k 6) (steps (fn-bs-record-program stage name frame)) (g groups) (c capacity))
                 (:instance fn-bs-k0b-syscall-carries-kernel (k 7) (steps (fn-bs-record-program stage name frame)) (g groups) (c capacity)))
           :in-theory (e/d (fn-bs-k0b-record-program-steps fn-bs-k0b-first-syscall-keeps-kernel fn-sf-dispatch)
                           (fn-bs-run fn-bs-store-relation fn-bs-record-program nth nthcdr fn-bs-record-inputp
                            fn-bs-lookup fn-sf-statep fn-bs-statep fn-sf-record-file-result fn-bs-step)))))
(defthm fn-bs-k0-record-attempted-cut-relation-by-step
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-record-inputp ks stage name frame)
                (not (fn-bs-lookup bs :staging stage)))
           (let ((p (nth 10 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity))))
             (fn-bs-store-relation (car p) (cdr p))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-k0-record-linked-cut-relation-by-step fn-bs-k0b-record-linked-kernel
                 (:instance fn-bs-store-relation-unfolds)
                 (:instance fn-sf-record-file-result-preserves-state (s ks) (result :ok))
                 (:instance fn-bs-k0c-related-pair-is-consp
                  (x (nth 8 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity))))
                 (:instance fn-bs-k0b-cut-after-step
                  (k 8) (steps (fn-bs-record-program stage name frame)) (g groups) (c capacity))
                 (:instance fn-bs-k0b-cut-after-step-pair
                  (k 8) (steps (fn-bs-record-program stage name frame)) (g groups) (c capacity))
                 (:instance fn-bs-k0b-relation-has-no-root-rename
                  (b (car (nth 8 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity))))
                  (k (cdr (nth 8 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity)))))
                 (:instance fn-bs-k0b-covered-without-root-rename-is-related
                  (b (car (nth 10 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity))))
                  (k (cdr (nth 10 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity))))))
           :in-theory (e/d (fn-bs-k0b-record-program-steps fn-bs-k0-step-inputp fn-bs-k0-observation-inputp
                            fn-bs-replay-visiblep fn-bs-k0c-ok-kinds-return-ok fn-bs-record-inputp
                            fn-sf-record-file-result)
                           (fn-bs-run fn-bs-store-relation fn-bs-record-program nth nthcdr
                            fn-bs-lookup fn-sf-statep fn-bs-statep fn-bs-step fn-bs-k0-coveredp
                            fn-bs-frontier-noncommit-observationp)))))
(defthm fn-bs-k0b-ops-not-for-dir-keeps-no-root-rename
  (implies (not (fn-bs-k0m-has-root-rename ops))
           (not (fn-bs-k0m-has-root-rename (fn-bs-ops-not-for-dir ops d))))
  :hints (("Goal" :in-theory (enable fn-bs-k0m-has-root-rename fn-bs-ops-not-for-dir))))
(defthm fn-bs-k0b-fence-dir-keeps-no-root-rename
  (implies (not (fn-bs-k0m-has-root-rename (fn-bs-pending b)))
           (not (fn-bs-k0m-has-root-rename (fn-bs-pending (fn-bs-fence-dir b d)))))
  :hints (("Goal" :in-theory (enable fn-bs-fence-dir))))
(defthm fn-bs-k0-record-durable-cut-relation-by-step
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-record-inputp ks stage name frame)
                (not (fn-bs-lookup bs :staging stage)))
           (let ((p (nth 12 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity))))
             (fn-bs-store-relation (car p) (cdr p))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-k0-record-attempted-cut-relation-by-step
                 fn-bs-k0-record-attempted-cut-kernel-is-link-observation
                 fn-bs-k0-attempted-cut-has-one-issued-transaction-link
                 fn-bs-k0-record-attempted-kernel-phase
                 (:instance fn-bs-store-relation-unfolds)
                 (:instance fn-bs-k0c-related-pair-is-consp
                  (x (nth 10 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity))))
                 (:instance fn-bs-k0b-cut-after-step
                  (k 10) (steps (fn-bs-record-program stage name frame)) (g groups) (c capacity))
                 (:instance fn-bs-k0b-cut-after-step-pair
                  (k 10) (steps (fn-bs-record-program stage name frame)) (g groups) (c capacity))
                 (:instance fn-bs-k0b-relation-has-no-root-rename
                  (b (car (nth 10 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity))))
                  (k (cdr (nth 10 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity)))))
                 (:instance fn-bs-k0b-covered-without-root-rename-is-related
                  (b (car (nth 12 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity))))
                  (k (cdr (nth 12 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity))))))
           :in-theory (e/d (fn-bs-k0b-record-program-steps fn-bs-k0-step-inputp
                            fn-bs-replay-visiblep fn-bs-k0c-ok-kinds-return-ok fn-bs-k0b-fsync-ok-results)
                           (fn-bs-run fn-bs-store-relation fn-bs-record-program nth nthcdr fn-bs-record-inputp
                            fn-bs-lookup fn-sf-statep fn-bs-statep fn-bs-k0-coveredp fn-bs-fence-dir
                            fn-sf-record-file-result fn-sf-record-link-result)))
          (and stable-under-simplificationp
               '(:in-theory (e/d (fn-bs-step fn-bs-fsync-dir fn-bs-k0s-fsync-dir-ok-is-fence)
                                 (fn-bs-run fn-bs-store-relation fn-bs-record-program nth nthcdr fn-bs-record-inputp
                                  fn-bs-lookup fn-sf-statep fn-bs-statep fn-bs-k0-coveredp fn-bs-fence-dir fn-bs-k0m-has-root-rename))))))
(defthm fn-bs-k0b-fence-dir-quiets-its-dir
  (fn-bs-dir-quietp (fn-bs-fence-dir b d) d)
  :hints (("Goal" :in-theory (enable fn-bs-dir-quietp fn-bs-fence-dir fn-bs-ops-for-dir-of-ops-not-for-dir))))
(defthm fn-bs-k0b-record-durable-pair-facts
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-record-inputp ks stage name frame)
                (not (fn-bs-lookup bs :staging stage)))
           (let ((run (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity)))
             (and (equal (cdr (nth 12 run)) (cdr (nth 10 run)))
                  (equal (car (nth 12 run)) (fn-bs-fence-dir (car (nth 10 run)) :transactions))
                  (equal (fn-sf-phase (cdr (nth 10 run))) :record-attempted)
                  (fn-bs-record-directory-committedp (car (nth 12 run)) (cdr (nth 12 run))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-k0-record-durable-cut-relation-by-step fn-bs-k0-record-pair-11-is-transaction-fence
                 fn-bs-k0-record-attempted-cut-relation-by-step
                 fn-bs-k0-record-attempted-cut-kernel-is-link-observation
                 fn-bs-k0-attempted-cut-has-one-issued-transaction-link
                 fn-bs-k0-record-attempted-kernel-phase
                 fn-bs-store-relation-unfolds
                 (:instance fn-bs-k0c-related-pair-is-consp (x (nth 12 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity))))
                 (:instance fn-bs-k0c-cut-pair-is-previous-pair (k 11) (steps (fn-bs-record-program stage name frame)) (g groups) (c capacity) (outs nil))
                 (:instance fn-bs-k0b-fence-dir-quiets-its-dir (b (car (nth 10 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity)))) (d :transactions))
                 (:instance fn-bs-store-relation-window-unfolds (bs (car (nth 10 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity)))) (ks (cdr (nth 10 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity)))))
                 (:instance fn-bs-pending-matches-phase-unfolds (bs (car (nth 10 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity)))) (ks (cdr (nth 10 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity)))))
                 (:instance fn-bs-k8-pending-link-fence-durable-records (bs (car (nth 10 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity)))) (ks (cdr (nth 10 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity))))))
           :in-theory (e/d (fn-bs-k0b-record-program-steps fn-bs-record-directory-committedp fn-bs-replay-visiblep)
                           (fn-bs-run fn-bs-store-relation fn-bs-record-program nth nthcdr fn-bs-record-inputp fn-bs-lookup fn-sf-statep fn-bs-statep fn-bs-k0-coveredp fn-bs-fence-dir fn-bs-k0m-has-root-rename fn-sf-record-file-result fn-sf-record-link-result fn-sf-record-dir-result fn-bs-durable-records fn-bs-apply-ops fn-bs-unlink fn-bs-pending-matches-phase
                            fn-bs-k0s-root-rename-targetp fn-bs-k0s-root-rename-pendingp fn-bs-crash-choicesp)))))
(defthm fn-bs-k0-record-completing-cut-relation-by-step
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-record-inputp ks stage name frame)
                (not (fn-bs-lookup bs :staging stage)))
           (let ((p (nth 14 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity))))
             (and (fn-bs-store-relation (car p) (cdr p))
                  (equal (fn-sf-phase (cdr p)) :completing))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-k0-record-durable-cut-relation-by-step fn-bs-k0b-record-durable-pair-facts
                 fn-bs-store-relation-unfolds
                 (:instance fn-bs-k0c-related-pair-is-consp (x (nth 12 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity))))
                 (:instance fn-bs-k0b-cut-after-step (k 12) (steps (fn-bs-record-program stage name frame)) (g groups) (c capacity))
                 (:instance fn-bs-k0b-cut-after-step-pair (k 12) (steps (fn-bs-record-program stage name frame)) (g groups) (c capacity))
                 (:instance fn-bs-k0b-observe-kernel-in-run (k 12) (steps (fn-bs-record-program stage name frame)) (g groups) (c capacity))
                 (:instance fn-bs-record-directory-commit-observation-preserves-relation
                  (bs (car (nth 12 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity)))) (ks (cdr (nth 12 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity)))))
                 (:instance fn-bs-k0b-relation-has-no-root-rename (b (car (nth 12 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity)))) (k (cdr (nth 12 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity)))))
                 (:instance fn-bs-k0b-covered-without-root-rename-is-related (b (car (nth 14 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity)))) (k (cdr (nth 14 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity))))))
           :in-theory (e/d (fn-bs-k0b-record-program-steps fn-bs-k0-step-inputp fn-bs-k0-observation-inputp
                            fn-bs-replay-visiblep fn-bs-k0c-ok-kinds-return-ok fn-sf-dispatch)
                           (fn-bs-run fn-bs-store-relation fn-bs-record-program nth nthcdr fn-bs-record-inputp fn-bs-lookup fn-sf-statep fn-bs-statep fn-bs-k0-coveredp fn-bs-fence-dir fn-bs-k0m-has-root-rename fn-sf-record-file-result fn-sf-record-link-result fn-sf-record-dir-result fn-bs-durable-records fn-bs-apply-ops fn-bs-unlink fn-bs-pending-matches-phase fn-bs-step fn-bs-record-directory-committedp fn-bs-frontier-noncommit-observationp)))))
(defthm fn-bs-k0b-next-ino-natp
  (implies (fn-bs-statep b) (natp (fn-bs-next-ino b)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-bs-statep))))
(defthm fn-bs-k0b-cleanup-step-facts
  (and (implies (fn-bs-lookup b d n)
                (equal (mv-nth 0 (fn-bs-step b k (list :unlink d n) :ok g c)) :ok))
       (equal (fn-bs-k0m-has-root-rename (fn-bs-pending (mv-nth 1 (fn-bs-step b k (list :unlink d n) o g c))))
              (fn-bs-k0m-has-root-rename (fn-bs-pending b)))
       (equal (mv-nth 0 (fn-bs-step b k '(:fsync-dir :staging) :ok g c)) :ok)
       (implies (not (fn-bs-k0m-has-root-rename (fn-bs-pending b)))
                (not (fn-bs-k0m-has-root-rename
                      (fn-bs-pending (mv-nth 1 (fn-bs-step b k '(:fsync-dir :staging) :ok g c)))))))
  :hints (("Goal" :in-theory (e/d (fn-bs-step fn-bs-fsync-dir) (fn-bs-unlink fn-bs-lookup fn-bs-fence-dir fn-bs-k0m-has-root-rename)))))
(defthm fn-bs-k0-record-cleanup-cut-relation-by-step
  (implies (and (fn-bs-store-relation bs ks)
                (fn-bs-record-inputp ks stage name frame)
                (not (fn-bs-lookup bs :staging stage)))
           (let ((run (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity)))
             (and (fn-bs-store-relation (car (nth 16 run)) (cdr (nth 16 run)))
                  (fn-bs-store-relation (car (nth 18 run)) (cdr (nth 18 run))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn-bs-k0-record-completing-cut-relation-by-step fn-bs-k0-record-completing-stage-lookup
                 (:instance fn-bs-k0b-next-ino-natp (b bs))
                 fn-bs-store-relation-unfolds
                 (:instance fn-bs-k0c-related-pair-is-consp (x (nth 14 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity))))
                 (:instance fn-bs-k0b-cut-after-step (k 14) (steps (fn-bs-record-program stage name frame)) (g groups) (c capacity))
                 (:instance fn-bs-k0b-cut-after-step-pair (k 14) (steps (fn-bs-record-program stage name frame)) (g groups) (c capacity))
                 (:instance fn-bs-k0b-cut-after-step (k 16) (steps (fn-bs-record-program stage name frame)) (g groups) (c capacity))
                 (:instance fn-bs-k0b-cut-after-step-pair (k 16) (steps (fn-bs-record-program stage name frame)) (g groups) (c capacity))
                 (:instance fn-bs-k0b-relation-has-no-root-rename (b (car (nth 14 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity)))) (k (cdr (nth 14 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity)))))
                 (:instance fn-bs-k0b-covered-without-root-rename-is-related (b (car (nth 16 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity)))) (k (cdr (nth 16 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity)))))
                 (:instance fn-bs-k0b-covered-without-root-rename-is-related (b (car (nth 18 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity)))) (k (cdr (nth 18 (fn-bs-run bs ks (fn-bs-record-program stage name frame) nil groups capacity))))))
           :in-theory (e/d (fn-bs-k0b-record-program-steps fn-bs-k0-step-inputp
                            fn-bs-replay-visiblep fn-bs-k0c-ok-kinds-return-ok fn-bs-k0b-fsync-ok-results
                            fn-bs-k0s-syscall-step-keeps-kernel fn-bs-k0b-cleanup-step-facts)
                           (fn-bs-run fn-bs-store-relation fn-bs-record-program nth nthcdr fn-bs-record-inputp fn-bs-lookup fn-sf-statep fn-bs-statep fn-bs-k0-coveredp fn-bs-fence-dir fn-bs-k0m-has-root-rename fn-sf-record-file-result fn-sf-record-link-result fn-sf-record-dir-result fn-bs-durable-records fn-bs-apply-ops fn-bs-unlink fn-bs-pending-matches-phase
                            fn-bs-k0s-root-rename-targetp fn-bs-k0s-root-rename-pendingp fn-bs-crash-choicesp)))))
