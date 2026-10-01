; Actual bounded stored windows to the existing canonical decoder answer.
; All support predicates/observers are proof-only. Runtime bodies are unchanged.
; The final boundary uses actual initialization, full stored wrapper effects and
; global scheduling-budget carry. It does not fund or activate native decoding.
(in-package "ACL2")

(include-book "decoded-window-stored-trajectory")
(include-book "decoded-window-finite-output-trajectory")

(local (include-book "arithmetic-5/top" :dir :system))

(local
 (defthm fn-pwzc-canonical-initialize-tout-zero
  (equal (fn-zin-tout (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out))) 0)
  :hints (("Goal" :in-theory (enable fn-pzw-initialize fn-zin-reset fn-zin-reset-loop)))))

(local
 (defthm fn-pwzc-canonical-initialize-tin-zero
  (equal (fn-zin-tin (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out))) 0)
  :hints (("Goal" :in-theory (enable fn-pzw-initialize fn-zin-reset fn-zin-reset-loop)))))

(local
 (defthm fn-pwzc-actual-payload-buffers-initializer-by-definition
  (let* ((init (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out))
         (c (nfix (- end start)))
         (credited (fn-zin-set 7 c (car init)))
         (r (fn-zin-feed b credited start end (fn-zin-stored-limit c lim)
                         fn-octets (mv-nth 1 init) (mv-nth 2 init) (mv-nth 3 init))))
   (equal (fn-zin-payload-bufs b dict start end lim fn-octets fn-zin-win fn-zin-tab fn-zin-out)
          (list (fn-zin-stored-status (car r) c (mv-nth 3 r)) (mv-nth 4 r) (mv-nth 5 r) (mv-nth 6 r))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-zin-payload-bufs fn-pzw-initialize fn-zin-feed fn-zin-stored-status)
                           (fn-zin-loop fn-zin-payload-ready fn-zin-reset fn-zin-stored-terminalp fn-zin-stored-allowance nfix))))))

(local
 (defthm fn-pwzc-empty-proper-list-is-nil
  (implies (and (true-listp x) (equal (len x) 0)) (equal x nil))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable len true-listp)))))

(local
 (defthm fn-pwzc-proper-pair-expansion
  (implies (and (true-listp x) (equal (len x) 2))
   (equal x (list (car x) (cadr x))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable len true-listp)))))

(local
 (defthm fn-pwzc-reset-and-replace-preset-whole-state
  (implies (and (true-listp fn-zin-st) (equal (len fn-zin-st) 1)
                (true-listp (car fn-zin-st)) (equal (len (car fn-zin-st)) 20))
   (equal (fn-zin-set 18 h (fn-zin-reset fn-zin-st))
          (fn-zin-set 18 h (fn-zin-reset (create-fn-zin-st)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-pwzc-proper-pair-expansion (x (nthcdr 18 (car fn-zin-st))))
                 (:instance fn-pwzc-empty-proper-list-is-nil (x (cdr fn-zin-st))))
           :expand ((:free (x) (nthcdr 18 x)) (:free (x) (nthcdr 17 x)) (:free (x) (nthcdr 16 x)) (:free (x) (nthcdr 15 x)) (:free (x) (nthcdr 14 x)) (:free (x) (nthcdr 13 x)) (:free (x) (nthcdr 12 x)) (:free (x) (nthcdr 11 x)) (:free (x) (nthcdr 10 x)) (:free (x) (nthcdr 9 x)) (:free (x) (nthcdr 8 x)) (:free (x) (nthcdr 7 x)) (:free (x) (nthcdr 6 x)) (:free (x) (nthcdr 5 x)) (:free (x) (nthcdr 4 x)) (:free (x) (nthcdr 3 x)) (:free (x) (nthcdr 2 x)) (:free (x) (nthcdr 1 x)) (:free (x) (nthcdr 0 x)) (:free (s) (fn-zin-reset-loop 0 s)) (:free (s) (fn-zin-reset-loop 1 s)) (:free (s) (fn-zin-reset-loop 2 s)) (:free (s) (fn-zin-reset-loop 3 s)) (:free (s) (fn-zin-reset-loop 4 s)) (:free (s) (fn-zin-reset-loop 5 s)) (:free (s) (fn-zin-reset-loop 6 s)) (:free (s) (fn-zin-reset-loop 7 s)) (:free (s) (fn-zin-reset-loop 8 s)) (:free (s) (fn-zin-reset-loop 9 s)) (:free (s) (fn-zin-reset-loop 10 s)) (:free (s) (fn-zin-reset-loop 11 s)) (:free (s) (fn-zin-reset-loop 12 s)) (:free (s) (fn-zin-reset-loop 13 s)) (:free (s) (fn-zin-reset-loop 14 s)) (:free (s) (fn-zin-reset-loop 15 s)) (:free (s) (fn-zin-reset-loop 16 s)) (:free (s) (fn-zin-reset-loop 17 s)) (:free (s) (fn-zin-reset-loop 18 s)))
           :in-theory (enable fn-zin-reset fn-zin-reset-loop fn-zin-set$inline)))))

(local
 (defthm fn-pwzc-register-array-recognizer-implies-proper
  (implies (fn-zin-regsp x) (true-listp x))
  :hints (("Goal" :induct (fn-zin-regsp x) :in-theory (enable fn-zin-regsp)))))

(local
 (defthm fn-pwzc-genuine-register-stobj-has-fixed-shape
  (implies (fn-zin-stp fn-zin-st)
   (and (true-listp fn-zin-st) (equal (len fn-zin-st) 1)
        (true-listp (car fn-zin-st)) (equal (len (car fn-zin-st)) 20)))
  :hints (("Goal" :in-theory (enable fn-zin-stp fn-zin-regsp)))))

(local
 (defthm fn-pwzc-actual-initializer-canonical-whole-state
  (implies (and (true-listp fn-zin-st) (equal (len fn-zin-st) 1)
                (true-listp (car fn-zin-st)) (equal (len (car fn-zin-st)) 20))
   (equal (fn-pzw-initialize dict fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
          (fn-pzw-initialize dict (create-fn-zin-st) nil nil nil)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-pzw-initialize)
                           (fn-zin-reset fn-zin-payload-ready fn-zin-set$inline nfix))))))

(local
 (defthm fn-pwzc-stored-status-unaffected-by-tin-credit
  (equal (fn-zin-stored-status status c (fn-zin-set 7 credit fn-zin-st))
         (fn-zin-stored-status status c fn-zin-st))
  :hints (("Goal" :in-theory (enable fn-zin-stored-status fn-zin-stored-terminalp)))))

(local
 (defthm fn-pwzc-canonical-initialize-progress-controls
  (let ((s (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out))))
   (and (fn-pwz-progress-statep s) (equal (fn-pwz-progress-phase s) -2)
        (equal (fn-zin-nbits s) 0) (equal (fn-zin-tout s) 0)))
  :hints (("Goal" :in-theory (enable fn-pzw-initialize fn-zin-reset fn-pwz-progress-statep fn-pwz-progress-phase)))))

(local
 (defthm fn-pwzc-actual-loop-input-position-upper-bound
  (implies (and (natp ip) (<= ip (nfix end)))
   (<= (mv-nth 2 (fn-zin-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)) (nfix end)))
  :hints (("Goal" :induct (fn-zin-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
           :in-theory (e/d (fn-zin-loop)
                           (fn-zin-step fn-zin-act fn-zin-pull fn-zin-need fn-zin-loop-counts fn-zin-step-out-free))))))

(local
 (defthm fn-pwzc-progress-controls-unaffected-by-credit
  (and (equal (fn-pwz-progress-statep (fn-zin-set 7 credit fn-zin-st)) (fn-pwz-progress-statep fn-zin-st))
       (equal (fn-pwz-progress-phase (fn-zin-set 7 credit fn-zin-st)) (fn-pwz-progress-phase fn-zin-st)))
  :hints (("Goal" :in-theory (enable fn-pwz-progress-statep fn-pwz-progress-phase)))))

(local
 (defthm fn-pwzc-canonical-output-frontier-bounds
  (let ((lim (fn-zin-stored-limit c (+ 1 (nfix n)))))
   (and (natp lim) (< 0 lim) (<= lim (+ 1 (nfix n)))))
  :rule-classes (:rewrite (:linear :corollary (<= (fn-zin-stored-limit c (+ 1 (nfix n))) (+ 1 (nfix n)))))
  :hints (("Goal" :in-theory (enable fn-zin-stored-limit fn-zin-stored-allowance nfix min)))))

(local
 (defthm fn-pwzc-canonical-nfix-natural
  (implies (natp x) (equal (nfix x) x))
  :hints (("Goal" :in-theory (enable nfix)))))

(local
 (defthm fn-pwzc-actual-canonical-feed-budget-margin
 (let* ((init (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out))
        (c (len fn-octets)) (credited (fn-zin-set 7 c (car init)))
        (r (fn-zin-feed (fn-pzd-budget c n) credited 0 c (fn-zin-stored-limit c (+ 1 (nfix n)))
                        fn-octets (mv-nth 1 init) (mv-nth 2 init) nil)))
  (<= (+ 3837 (* 7 c)) (mv-nth 1 r)))
 :rule-classes nil
 :hints (("Goal"
          :use ((:instance fn-pwz-actual-loop-charge-bound
                 (b (fn-pzd-budget (len fn-octets) n)) (ip 0) (end (len fn-octets))
                 (lim (fn-zin-stored-limit (len fn-octets) (+ 1 (nfix n))))
                 (fn-zin-st (fn-zin-set 7 (len fn-octets) (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out))))
                 (fn-zin-win (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)))
                 (fn-zin-tab (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)))
                 (fn-zin-out nil))
                (:instance fn-zin-loop-counts
                 (b (fn-pzd-budget (len fn-octets) n)) (ip 0) (end (len fn-octets))
                 (lim (fn-zin-stored-limit (len fn-octets) (+ 1 (nfix n))))
                 (fn-zin-st (fn-zin-set 7 (len fn-octets) (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out))))
                 (fn-zin-win (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)))
                 (fn-zin-tab (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)))
                 (fn-zin-out nil))
                (:instance fn-pwzc-actual-loop-input-position-upper-bound
                 (b (fn-pzd-budget (len fn-octets) n)) (ip 0) (end (len fn-octets))
                 (lim (fn-zin-stored-limit (len fn-octets) (+ 1 (nfix n))))
                 (fn-zin-st (fn-zin-set 7 (len fn-octets) (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out))))
                 (fn-zin-win (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)))
                 (fn-zin-tab (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)))
                 (fn-zin-out nil))
                (:instance fn-zin-feed-out-bound
                 (b (fn-pzd-budget (len fn-octets) n)) (start 0) (end (len fn-octets))
                 (lim (fn-zin-stored-limit (len fn-octets) (+ 1 (nfix n))))
                 (fn-zin-st (fn-zin-set 7 (len fn-octets) (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out))))
                 (fn-zin-win (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)))
                 (fn-zin-tab (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)))
                 (fn-zin-out nil)))
          :in-theory (e/d (fn-zin-feed fn-pzd-budget)
                          (fn-zin-loop fn-zin-step fn-zin-act fn-zin-pull fn-zin-need
                           fn-pzw-initialize fn-zin-reset create-fn-zin-st fn-zin-bomb-okp fn-zin-stored-limit fn-zin-stored-allowance
                           fn-pwz-progress-statep fn-pwz-progress-phase
                           fn-zin-loop-counts fn-zin-feed-out-bound nfix min))))))

(local
 (defthm fn-pwzc-actual-feed-yield-exhausts-charge
  (let ((r (fn-zin-feed b fn-zin-st start end lim fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
   (implies (equal (car r) :yield) (equal (mv-nth 1 r) 0)))
  :hints (("Goal" :in-theory (e/d (fn-zin-feed) (fn-zin-loop))))))

(local
 (defthm fn-pwzc-actual-canonical-feed-never-yields
 (let* ((init (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out))
        (c (len fn-octets)) (credited (fn-zin-set 7 c (car init)))
        (r (fn-zin-feed (fn-pzd-budget c n) credited 0 c (fn-zin-stored-limit c (+ 1 (nfix n)))
                        fn-octets (mv-nth 1 init) (mv-nth 2 init) nil)))
  (not (equal (car r) :yield)))
 :rule-classes nil
 :hints (("Goal" :use fn-pwzc-actual-canonical-feed-budget-margin
          :in-theory (disable fn-pzw-initialize create-fn-zin-st fn-zin-feed fn-zin-loop
                              fn-pzd-budget fn-zin-stored-limit fn-pwz-progress-statep fn-pwz-progress-phase)))))

(local
 (defthm fn-pwzd-atomic-output-proper-and-monotone
  (implies (true-listp fn-zin-out)
   (let ((r (fn-pwz-atomic-output-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
    (and (true-listp (mv-nth 6 r)) (<= (len fn-zin-out) (len (mv-nth 6 r))))))
  :rule-classes (:rewrite (:linear :corollary
   (implies (true-listp fn-zin-out)
    (<= (len fn-zin-out) (len (mv-nth 6 (fn-pwz-atomic-output-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))))))
  :hints (("Goal" :induct (fn-pwz-atomic-output-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
           :in-theory (e/d (fn-pwz-atomic-output-loop)
                           (fn-zin-act fn-zin-pull fn-zin-need fn-zin-act-counts))))))

(local
 (defthm fn-pwzd-atomic-yield-prefix-can-extend-frontier
  (let ((r (fn-pwz-atomic-output-loop b ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
   (implies (and (true-listp fn-zin-out) (equal (car r) :yield)
                 (< (len (mv-nth 6 r)) (nfix lim)))
    (equal (fn-pwz-atomic-output-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out) r)))
  :rule-classes nil
  :hints (("Goal" :induct (fn-pwz-atomic-output-loop b ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
           :in-theory (e/d (fn-pwz-atomic-output-loop)
                           (fn-zin-act fn-zin-pull fn-zin-need fn-zin-act-counts))))))

(local
 (defthm fn-pwz-atomic-output-loop-split-budget
  (implies (and (natp b1) (natp b2)
                (equal (car (fn-pwz-atomic-output-loop b1 ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab
                                         fn-zin-out))
                       :yield))
           (equal (fn-pwz-atomic-output-loop (+ b1 b2) ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
                  (let ((r (fn-pwz-atomic-output-loop b1 ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab
                                        fn-zin-out)))
                    (fn-pwz-atomic-output-loop b2 (mv-nth 2 r) end lim (mv-nth 3 r) fn-octets
                                 (mv-nth 4 r) (mv-nth 5 r) (mv-nth 6 r)))))
  :hints (("Goal" :in-theory (e/d (fn-pwz-atomic-output-loop) (fn-zin-act fn-zin-pull fn-zin-need)) :induct (fn-pwz-atomic-output-loop b1 ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab
                                       fn-zin-out)))))

(local
 (defun-nx fn-pwz-atomic-fuel-pair-induction
 (b1 b2 ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
 (declare (xargs :measure (nfix b1)))
 (cond ((or (zp b1) (zp b2) (<= (nfix lim) (len fn-zin-out))) nil)
       ((< (fn-zin-nbits fn-zin-st) (fn-zin-need fn-zin-st))
        (if (and (natp ip) (< ip (min (nfix end) (fn-octets-len fn-octets))))
         (fn-pwz-atomic-fuel-pair-induction (1- b1) (1- b2) (1+ ip) end lim
           (fn-zin-pull ip fn-zin-st fn-octets) fn-octets fn-zin-win fn-zin-tab fn-zin-out)
         nil))
       (t (let ((r (fn-zin-act fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
            (if (car r) nil
             (fn-pwz-atomic-fuel-pair-induction (1- b1) (1- b2) ip end lim
               (mv-nth 1 r) fn-octets (mv-nth 2 r) (mv-nth 3 r) (mv-nth 4 r))))))))

(local
 (defthm fn-pwz-atomic-terminal-observation-fuel-independent
 (let ((r1 (fn-pwz-atomic-output-loop b1 ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))
       (r2 (fn-pwz-atomic-output-loop b2 ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
  (implies (and (not (equal (car r1) :yield)) (not (equal (car r2) :yield)))
   (equal (list (car r1) (mv-nth 2 r1) (mv-nth 3 r1) (mv-nth 4 r1) (mv-nth 5 r1) (mv-nth 6 r1))
          (list (car r2) (mv-nth 2 r2) (mv-nth 3 r2) (mv-nth 4 r2) (mv-nth 5 r2) (mv-nth 6 r2)))))
 :rule-classes nil
 :hints (("Goal" :induct (fn-pwz-atomic-fuel-pair-induction b1 b2 ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
          :in-theory (e/d (fn-pwz-atomic-output-loop fn-pwz-atomic-fuel-pair-induction)
                          (fn-zin-act fn-zin-pull fn-zin-need fn-zin-act-counts
                           fn-pwz-atomic-output-loop-split-budget))))))

(local
 (defthm fn-pwz-output-emit-prefix
  (implies (and (syntaxp (not (equal fn-zin-out ''nil))) (true-listp fn-zin-out))
           (equal (fn-zin-emit o fn-zin-st fn-zin-win fn-zin-out)
                  (let ((r (fn-zin-emit o fn-zin-st fn-zin-win nil)))
                   (mv (car r) (mv-nth 1 r) (mv-nth 2 r)
                       (append fn-zin-out (mv-nth 3 r))))))
  :hints (("Goal" :in-theory (enable fn-zin-emit)))))

(local
 (defthm fn-pwz-output-action-prefix
  (implies (and (syntaxp (not (equal fn-zin-out ''nil))) (true-listp fn-zin-out))
           (equal (fn-zin-act fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
                  (let ((r (fn-zin-act fn-zin-st fn-zin-win fn-zin-tab nil)))
                   (mv (car r) (mv-nth 1 r) (mv-nth 2 r) (mv-nth 3 r)
                       (append fn-zin-out (mv-nth 4 r))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-zin-act) (fn-zin-act-counts fn-zin-emit-out))))))

(local
 (defthm fn-pwzd-output-prefix-append-length
  (equal (len (append p o)) (+ (len p) (len o)))
  :hints (("Goal" :induct (append p o) :in-theory (enable append)))))

(local
 (defthm fn-pwzd-output-prefix-append-associative
  (equal (append (append p o) z) (append p (append o z)))
  :hints (("Goal" :induct (append p o) :in-theory (enable append)))))

(local
 (defthm fn-pwzd-output-prefix-append-proper
  (implies (true-listp o) (true-listp (append p o)))
  :hints (("Goal" :induct (append p o) :in-theory (enable append)))))

(local
 (defthm fn-pwzd-atomic-output-prefix
  (implies (and (true-listp p) (true-listp fn-zin-out))
   (equal (fn-pwz-atomic-output-loop b ip end (+ (len p) (nfix lim)) fn-zin-st fn-octets fn-zin-win fn-zin-tab (append p fn-zin-out))
          (let ((r (fn-pwz-atomic-output-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
           (list (car r) (mv-nth 1 r) (mv-nth 2 r) (mv-nth 3 r) (mv-nth 4 r) (mv-nth 5 r)
                 (append p (mv-nth 6 r))))))
  :hints (("Goal" :induct (fn-pwz-atomic-output-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
           :in-theory (e/d (fn-pwz-atomic-output-loop)
                           (fn-zin-act fn-zin-pull fn-zin-need fn-zin-act-counts nfix min fn-pwz-atomic-output-loop-split-budget))))))

(local
 (defthm fn-pwzd-atomic-yield-cleared-window-exact
  (let* ((r1 (fn-pwz-atomic-output-loop b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))
         (r2 (fn-pwz-atomic-output-loop b2 (mv-nth 2 r1) end l (mv-nth 3 r1) fn-octets (mv-nth 4 r1) (mv-nth 5 r1) nil)))
   (implies (and (natp b1) (natp b2) (true-listp fn-zin-out) (equal (car r1) :yield) (posp (nfix l)))
    (equal (fn-pwz-atomic-output-loop (+ b1 b2) ip end (+ (len (mv-nth 6 r1)) (nfix l)) fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
           (list (car r2) (mv-nth 1 r2) (mv-nth 2 r2) (mv-nth 3 r2) (mv-nth 4 r2) (mv-nth 5 r2)
                 (append (mv-nth 6 r1) (mv-nth 6 r2))))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance fn-pwzd-atomic-yield-prefix-can-extend-frontier
                  (b b1) (lim (+ (len (mv-nth 6 (fn-pwz-atomic-output-loop b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))) (nfix l))))
                 (:instance fn-pwz-atomic-output-loop-split-budget
                  (lim (+ (len (mv-nth 6 (fn-pwz-atomic-output-loop b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))) (nfix l))))
                 (:instance fn-pwzd-atomic-output-prefix (b b2) (lim l) (fn-zin-out nil)
                  (p (mv-nth 6 (fn-pwz-atomic-output-loop b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
                  (ip (mv-nth 2 (fn-pwz-atomic-output-loop b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
                  (fn-zin-st (mv-nth 3 (fn-pwz-atomic-output-loop b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
                  (fn-zin-win (mv-nth 4 (fn-pwz-atomic-output-loop b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
                  (fn-zin-tab (mv-nth 5 (fn-pwz-atomic-output-loop b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))))
           :in-theory (disable fn-pwz-atomic-output-loop fn-zin-act fn-zin-pull fn-zin-need
                               fn-pwzd-atomic-output-prefix fn-pwz-atomic-output-loop-split-budget nfix min)))))

(local
 (defthm fn-pwz-loop-semantic-fuel-natural
  (natp (fn-pwz-actual-loop-semantic-fuel b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))
  :rule-classes :type-prescription
  :hints (("Goal" :induct (fn-pwz-actual-loop-semantic-fuel b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
           :in-theory (e/d (fn-pwz-actual-loop-semantic-fuel) (fn-zin-act fn-zin-step fn-zin-pull fn-pwz-step-action-count))))))

(local
 (defthm fn-pwzd-actual-basic-loop-yield-cleared-windows
 (let* ((r1 (fn-zin-loop b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))
        (r2 (fn-zin-loop b2 (mv-nth 2 r1) end l (mv-nth 3 r1) fn-octets (mv-nth 4 r1) (mv-nth 5 r1) nil))
        (whole (fn-zin-loop b0 ip end (+ (len (mv-nth 6 r1)) (nfix l)) fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
  (implies (and (true-listp fn-zin-out) (equal (car r1) :yield) (posp (nfix l))
                (not (equal (car r2) :yield)) (not (equal (car whole) :yield)))
   (equal (fn-pwz-semantic-observation whole)
          (list (car r2) (mv-nth 2 r2) (mv-nth 3 r2) (mv-nth 4 r2) (mv-nth 5 r2)
                (append (mv-nth 6 r1) (mv-nth 6 r2))))))
 :rule-classes nil
 :hints (("Goal"
 :use ((:instance fn-pwz-actual-basic-loop-is-atomic-unconditionally (b b1) (lim m))
       (:instance fn-pwz-actual-basic-loop-is-atomic-unconditionally (b b2) (lim l) (ip (mv-nth 2 (fn-zin-loop b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))) (fn-zin-st (mv-nth 3 (fn-zin-loop b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))) (fn-zin-win (mv-nth 4 (fn-zin-loop b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))) (fn-zin-tab (mv-nth 5 (fn-zin-loop b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))) (fn-zin-out nil))
       (:instance fn-pwz-actual-basic-loop-is-atomic-unconditionally (b b0) (lim (+ (len (mv-nth 6 (fn-zin-loop b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))) (nfix l))))
       (:instance fn-pwzd-atomic-yield-cleared-window-exact (b1 (fn-pwz-actual-loop-semantic-fuel b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)) (b2 (fn-pwz-actual-loop-semantic-fuel b2 (mv-nth 2 (fn-zin-loop b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)) end l (mv-nth 3 (fn-zin-loop b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)) fn-octets (mv-nth 4 (fn-zin-loop b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 5 (fn-zin-loop b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)) nil)))
       (:instance fn-pwz-atomic-terminal-observation-fuel-independent (b1 (+ (fn-pwz-actual-loop-semantic-fuel b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out) (fn-pwz-actual-loop-semantic-fuel b2 (mv-nth 2 (fn-zin-loop b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)) end l (mv-nth 3 (fn-zin-loop b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)) fn-octets (mv-nth 4 (fn-zin-loop b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 5 (fn-zin-loop b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)) nil))) (b2 (fn-pwz-actual-loop-semantic-fuel b0 ip end (+ (len (mv-nth 6 (fn-zin-loop b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))) (nfix l)) fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)) (lim (+ (len (mv-nth 6 (fn-zin-loop b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))) (nfix l)))))
 :in-theory (e/d (fn-pwz-semantic-observation)
                 (fn-zin-loop fn-pwz-atomic-output-loop fn-pwz-actual-loop-semantic-fuel
                  fn-zin-act fn-zin-step fn-zin-pull fn-zin-need fn-zin-loop-counts
                  fn-zin-step-out-free fn-pwz-output-action-prefix fn-pwzd-atomic-output-prefix
                  fn-pwz-atomic-output-loop-split-budget nfix min))))))

(local
 (defthm fn-pwzd-actual-basic-loop-cleared-quantum-or-full-windows
 (let* ((r1 (fn-zin-loop b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))
        (r2 (fn-zin-loop b2 (mv-nth 2 r1) end l (mv-nth 3 r1) fn-octets
                        (mv-nth 4 r1) (mv-nth 5 r1) nil))
        (whole (fn-zin-loop b0 ip end (+ (len (mv-nth 6 r1)) (nfix l))
                           fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
  (implies (and (true-listp fn-zin-out) (member-equal (car r1) '(:yield :full)) (posp (nfix l))
                (not (equal (car r2) :yield)) (not (equal (car whole) :yield)))
   (equal (fn-pwz-semantic-observation whole)
          (list (car r2) (mv-nth 2 r2) (mv-nth 3 r2) (mv-nth 4 r2) (mv-nth 5 r2)
                (append (mv-nth 6 r1) (mv-nth 6 r2))))))
 :rule-classes nil
 :hints (("Goal" :use (fn-pwzd-actual-basic-loop-yield-cleared-windows
                        fn-pwz-actual-basic-loop-general-cleared-windows)
           :in-theory (e/d (member-equal)
                           (fn-zin-loop fn-pwz-semantic-observation nfix min))))))

(local
 (defthm fn-pwzc-update-octet-retains-length
  (implies (and (natp i) (< i (len x)))
   (equal (len (fn-oct-update i o x)) (len x)))
  :hints (("Goal" :induct (fn-oct-update i o x) :in-theory (enable fn-oct-update)))))

(local
 (defthm fn-pwzc-table-length-word-write
  (implies (and (natp e) (< e *fn-zin-tab-entries*)
                (equal (len fn-zin-tab) *fn-zin-tab-octets*))
   (equal (len (fn-zin-tput e v fn-zin-tab)) *fn-zin-tab-octets*))
  :hints (("Goal" :in-theory (e/d (fn-zin-tput) (fn-oct-update))))))

(local
 (defthm fn-pwzc-code-length-bounds-unconditional
  (and (natp (fn-zin-len-of e fn-zin-tab)) (<= (fn-zin-len-of e fn-zin-tab) 15))
  :rule-classes ((:rewrite) (:type-prescription :corollary (natp (fn-zin-len-of e fn-zin-tab))) (:linear :corollary (<= (fn-zin-len-of e fn-zin-tab) 15)))
  :hints (("Goal" :in-theory (enable fn-zin-len-of)))))

(local
 (defthm fn-pwzc-zero-counts-retains-table-length
  (implies (equal (len fn-zin-tab) *fn-zin-tab-octets*)
   (equal (len (fn-zin-zero-counts k cb fn-zin-tab)) *fn-zin-tab-octets*))
  :hints (("Goal" :induct (fn-zin-zero-counts k cb fn-zin-tab)
           :in-theory (e/d (fn-zin-zero-counts) (fn-zin-tput fn-oct-update fn-zin-len-of))))))

(local
 (defthm fn-pwzc-count-lens-retains-table-length
  (implies (equal (len fn-zin-tab) *fn-zin-tab-octets*)
   (equal (len (fn-zin-count-lens s n lb cb fn-zin-tab)) *fn-zin-tab-octets*))
  :hints (("Goal" :induct (fn-zin-count-lens s n lb cb fn-zin-tab)
           :in-theory (e/d (fn-zin-count-lens) (fn-zin-tput fn-oct-update fn-zin-len-of))))))

(local
 (defthm fn-pwzc-offsets-retains-table-length
  (implies (equal (len fn-zin-tab) *fn-zin-tab-octets*)
   (equal (len (fn-zin-offsets len off cb fn-zin-tab)) *fn-zin-tab-octets*))
  :hints (("Goal" :induct (fn-zin-offsets len off cb fn-zin-tab)
           :in-theory (e/d (fn-zin-offsets) (fn-zin-tput fn-oct-update fn-zin-len-of))))))

(local
 (defthm fn-pwzc-place-syms-retains-table-length
  (implies (equal (len fn-zin-tab) *fn-zin-tab-octets*)
   (equal (len (fn-zin-place-syms s n lb sb smax fn-zin-tab)) *fn-zin-tab-octets*))
  :hints (("Goal" :induct (fn-zin-place-syms s n lb sb smax fn-zin-tab)
           :in-theory (e/d (fn-zin-place-syms) (fn-zin-tput fn-oct-update fn-zin-len-of))))))

(local
 (defthm fn-pwzc-zero-range-retains-table-length
  (implies (equal (len fn-zin-tab) *fn-zin-tab-octets*)
   (equal (len (fn-zin-zero-range e k fn-zin-tab)) *fn-zin-tab-octets*))
  :hints (("Goal" :induct (fn-zin-zero-range e k fn-zin-tab)
           :in-theory (e/d (fn-zin-zero-range) (fn-zin-tput fn-oct-update fn-zin-len-of))))))

(local
 (defthm fn-pwzc-next-codes-retains-table-length
  (implies (equal (len fn-zin-tab) *fn-zin-tab-octets*)
   (equal (len (fn-zin-next-codes len code cb fn-zin-tab)) *fn-zin-tab-octets*))
  :hints (("Goal" :induct (fn-zin-next-codes len code cb fn-zin-tab)
           :in-theory (e/d (fn-zin-next-codes) (fn-zin-tput fn-oct-update fn-zin-len-of))))))

(local
 (defthm fn-pwzc-replicate-retains-table-length
  (implies (equal (len fn-zin-tab) *fn-zin-tab-octets*)
   (equal (len (fn-zin-replicate e step k v fn-zin-tab)) *fn-zin-tab-octets*))
  :hints (("Goal" :induct (fn-zin-replicate e step k v fn-zin-tab)
           :in-theory (e/d (fn-zin-replicate) (fn-zin-tput fn-oct-update fn-zin-len-of))))))

(local
 (defthm fn-pwzc-fill-lookup-retains-table-length
  (implies (equal (len fn-zin-tab) *fn-zin-tab-octets*)
   (equal (len (fn-zin-fill-lookup s n lb base fn-zin-tab)) *fn-zin-tab-octets*))
  :hints (("Goal" :induct (fn-zin-fill-lookup s n lb base fn-zin-tab)
           :in-theory (e/d (fn-zin-fill-lookup) (fn-zin-tput fn-oct-update fn-zin-len-of))))))

(local
 (defthm fn-pwzc-fill-retains-table-length
  (implies (equal (len fn-zin-tab) *fn-zin-tab-octets*)
   (equal (len (fn-zin-fill e k v fn-zin-tab)) *fn-zin-tab-octets*))
  :hints (("Goal" :induct (fn-zin-fill e k v fn-zin-tab)
           :in-theory (e/d (fn-zin-fill) (fn-zin-tput fn-oct-update fn-zin-len-of))))))

(local
 (defthm fn-pwzc-zero-cl-retains-table-length
  (implies (equal (len fn-zin-tab) *fn-zin-tab-octets*)
   (equal (len (fn-zin-zero-cl i fn-zin-tab)) *fn-zin-tab-octets*))
  :hints (("Goal" :induct (fn-zin-zero-cl i fn-zin-tab)
           :in-theory (e/d (fn-zin-zero-cl) (fn-zin-tput fn-oct-update fn-zin-len-of))))))

(local
 (defthm fn-pwzc-construct-retains-table-length
  (implies (equal (len fn-zin-tab) *fn-zin-tab-octets*)
   (equal (len (mv-nth 1 (fn-zin-construct tb lb n fn-zin-tab))) *fn-zin-tab-octets*))
  :hints (("Goal" :in-theory (e/d (fn-zin-construct)
                           (fn-zin-tput fn-zin-zero-range fn-zin-zero-counts fn-zin-count-lens
                            fn-zin-offsets fn-zin-place-syms fn-zin-next-codes fn-zin-fill-lookup))))))

(local
 (defthm fn-pwzc-fixed-retains-table-length
  (implies (equal (len fn-zin-tab) *fn-zin-tab-octets*)
   (equal (len (fn-zin-fixed-tables fn-zin-tab)) *fn-zin-tab-octets*))
  :hints (("Goal" :in-theory (e/d (fn-zin-fixed-tables) (fn-zin-fill fn-zin-construct))))))

(local
 (defthm fn-pwzc-dynamic-retains-table-length
  (implies (equal (len fn-zin-tab) *fn-zin-tab-octets*)
   (equal (len (mv-nth 1 (fn-zin-dynamic-tables hlit hdist fn-zin-tab))) *fn-zin-tab-octets*))
  :hints (("Goal" :in-theory (e/d (fn-zin-dynamic-tables) (fn-zin-construct))))))

(local
 (defthm fn-pwzc-emit-retains-history-length
  (implies (equal (len fn-zin-win) *fn-zin-win-octets*)
   (equal (len (mv-nth 2 (fn-zin-emit o fn-zin-st fn-zin-win fn-zin-out))) *fn-zin-win-octets*))
  :hints (("Goal" :in-theory (e/d (fn-zin-emit) (fn-oct-update fn-zin-emit-out))))))

(local
 (defthm fn-pwzc-actual-action-keeps-buffer-lengths
  (implies (and (equal (len fn-zin-win) *fn-zin-win-octets*)
                (equal (len fn-zin-tab) *fn-zin-tab-octets*))
   (let ((r (fn-zin-act fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
    (and (equal (len (mv-nth 2 r)) *fn-zin-win-octets*)
         (equal (len (mv-nth 3 r)) *fn-zin-tab-octets*))))
  :hints (("Goal" :do-not-induct t :in-theory (e/d (fn-zin-act)
           (fn-zin-emit fn-zin-emit-out fn-zin-construct fn-zin-fixed-tables fn-zin-dynamic-tables fn-zin-fill fn-zin-zero-cl fn-zin-tput))))))

(local
 (defthm fn-pwzc-copy-retains-history-length
  (implies (equal (len fn-zin-win) *fn-zin-win-octets*)
   (equal (len (mv-nth 1 (fn-zin-copy k w d tout h fn-zin-win fn-zin-out))) *fn-zin-win-octets*))
  :hints (("Goal" :induct (fn-zin-copy k w d tout h fn-zin-win fn-zin-out)
           :in-theory (e/d (fn-zin-copy) (fn-oct-update))))))

(local
 (defthm fn-pwzc-match-retains-history-length
  (implies (equal (len fn-zin-win) *fn-zin-win-octets*)
   (equal (len (mv-nth 2 (fn-zin-match room fn-zin-st fn-zin-win fn-zin-out))) *fn-zin-win-octets*))
  :hints (("Goal" :in-theory (e/d (fn-zin-match) (fn-zin-copy))))))

(local
 (defthm fn-pwzc-literal-loop-retains-history-length
  (implies (equal (len fn-zin-win) *fn-zin-win-octets*)
   (equal (len (mv-nth 4 (fn-zin-lit-loop k bits nbits w tout limit fn-zin-tab fn-zin-win fn-zin-out))) *fn-zin-win-octets*))
  :hints (("Goal" :induct (fn-zin-lit-loop k bits nbits w tout limit fn-zin-tab fn-zin-win fn-zin-out)
           :in-theory (e/d (fn-zin-lit-loop) (fn-oct-update))))))

(local
 (defthm fn-pwzc-literals-retain-history-length
  (implies (equal (len fn-zin-win) *fn-zin-win-octets*)
   (equal (len (mv-nth 2 (fn-zin-lits room fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))) *fn-zin-win-octets*))
  :hints (("Goal" :in-theory (e/d (fn-zin-lits) (fn-zin-lit-loop))))))

(local
 (defthm fn-pwzc-actual-step-keeps-buffer-lengths
  (implies (and (equal (len fn-zin-win) *fn-zin-win-octets*)
                (equal (len fn-zin-tab) *fn-zin-tab-octets*))
   (let ((r (fn-zin-step room fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
    (and (equal (len (mv-nth 2 r)) *fn-zin-win-octets*)
         (equal (len (mv-nth 3 r)) *fn-zin-tab-octets*))))
  :hints (("Goal" :in-theory (e/d (fn-zin-step)
           (fn-zin-act fn-zin-match fn-zin-lits fn-zin-step-out-free))))))

(local
 (defthm fn-pwzc-actual-loop-keeps-buffer-lengths
  (implies (and (equal (len fn-zin-win) *fn-zin-win-octets*)
                (equal (len fn-zin-tab) *fn-zin-tab-octets*))
   (let ((r (fn-zin-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
    (and (equal (len (mv-nth 4 r)) *fn-zin-win-octets*)
         (equal (len (mv-nth 5 r)) *fn-zin-tab-octets*))))
  :hints (("Goal" :induct (fn-zin-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
           :in-theory (e/d (fn-zin-loop)
           (fn-zin-act fn-zin-step fn-zin-pull fn-zin-need fn-zin-step-out-free fn-zin-loop-counts))))))

(local
 (defthm fn-pwzd-actual-feed-cleared-quantum-or-full-windows
 (let* ((r1 (fn-zin-feed b1 fn-zin-st ip end m fn-octets fn-zin-win fn-zin-tab nil))
        (r2 (fn-zin-feed b2 (mv-nth 3 r1) (mv-nth 2 r1) end l fn-octets
                        (mv-nth 4 r1) (mv-nth 5 r1) nil))
        (whole (fn-zin-feed b0 fn-zin-st ip end (+ (len (mv-nth 6 r1)) (nfix l))
                           fn-octets fn-zin-win fn-zin-tab nil)))
  (implies (and (member-equal (car r1) '(:yield :full)) (posp (nfix l)) (not (equal (car r2) :yield))
                (not (equal (car whole) :yield)))
   (equal (fn-pwz-semantic-observation whole)
          (list (car r2) (mv-nth 2 r2) (mv-nth 3 r2) (mv-nth 4 r2) (mv-nth 5 r2)
                (append (mv-nth 6 r1) (mv-nth 6 r2))))))
 :rule-classes nil
 :hints (("Goal"
          :use ((:instance fn-pwzd-actual-basic-loop-cleared-quantum-or-full-windows (fn-zin-out nil))
                (:instance fn-pwzc-actual-loop-keeps-buffer-lengths (b b1) (lim m) (fn-zin-out nil)))
          :in-theory (e/d (fn-zin-feed fn-zin-window-ready-p fn-zin-tab-okp)
                          (fn-zin-loop fn-pwz-semantic-observation fn-zin-loop-keeps fn-zin-feed-unfolds fn-pwzc-actual-loop-keeps-buffer-lengths
                           nfix))))))

(local
 (defthm fn-pwzd-actual-stored-room-positive
  (posp (nfix (fn-pzw-room bound tout)))
  :hints (("Goal" :in-theory (enable fn-pzw-room)))))

(local
 (defthm fn-pwzd-actual-stored-two-quantum-or-full-windows
 (let* ((r1 (fn-pzw-stored-chunk requested1 remaining1 start end compressed expected
                                fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))
        (r2 (fn-pzw-stored-chunk requested2 remaining2 (mv-nth 2 r1) end compressed expected
                                (mv-nth 3 r1) fn-octets (mv-nth 4 r1) (mv-nth 5 r1) (mv-nth 6 r1)))
        (credited (fn-zin-set 7 (+ (nfix compressed) (fn-zin-tin fn-zin-st)) fn-zin-st))
        (bound (min (nfix expected) (fn-pzw-stored-allowance compressed)))
        (l (fn-pzw-room bound (fn-zin-tout (mv-nth 3 r1))))
        (whole (fn-zin-feed b0 credited start end (+ (len (mv-nth 6 r1)) (nfix l))
                           fn-octets fn-zin-win fn-zin-tab nil)))
  (implies (and (member-equal (car r1) '(:yield :full)) (not (equal (car r2) :yield))
                (not (equal (car whole) :yield)))
   (equal (fn-pwz-semantic-observation whole)
          (list (car r2) (mv-nth 2 r2)
                (fn-zin-set 7 (+ (nfix compressed) (fn-zin-tin (mv-nth 3 r2))) (mv-nth 3 r2))
                (mv-nth 4 r2) (mv-nth 5 r2)
                (append (mv-nth 6 r1) (mv-nth 6 r2))))))
 :rule-classes nil
 :hints (("Goal"
          :use ((:instance fn-pwzc-actual-stored-chunk-recredited-full-tuple (requested requested1) (remaining remaining1))
                (:instance fn-pwzc-actual-two-stored-chunks-full-tuple)
                (:instance fn-pwzd-actual-feed-cleared-quantum-or-full-windows
                 (b1 (fn-pzw-quantum requested1 remaining1)) (b2 (fn-pzw-quantum requested2 remaining2))
                 (ip start) (fn-zin-st (fn-zin-set 7 (+ (nfix compressed) (fn-zin-tin fn-zin-st)) fn-zin-st))
                 (m (fn-pzw-room (min (nfix expected) (fn-pzw-stored-allowance compressed)) (fn-zin-tout fn-zin-st)))
                 (l (fn-pzw-room (min (nfix expected) (fn-pzw-stored-allowance compressed))
                       (fn-zin-tout (mv-nth 3 (fn-pzw-stored-chunk requested1 remaining1 start end compressed expected fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))))))
          :in-theory (e/d (fn-pwz-semantic-observation)
                          (fn-pzw-stored-chunk fn-pzw-chunk fn-zin-feed fn-zin-loop
                           fn-pzw-room fn-pzw-quantum fn-pzw-stored-allowance nfix min
                           fn-zin-feed-unfolds fn-zin-loop-counts fn-zin-loop-keeps
                           ))))))

(local
 (defthm fn-pwzd-atomic-nonfull-prefix-can-change-frontier
  (let ((r (fn-pwz-atomic-output-loop b ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
   (implies (and (true-listp fn-zin-out) (not (equal (car r) :full))
                 (< (len (mv-nth 6 r)) (nfix lim)))
    (equal (fn-pwz-atomic-output-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out) r)))
  :rule-classes nil
  :hints (("Goal" :induct (fn-pwz-atomic-output-loop b ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
           :in-theory (e/d (fn-pwz-atomic-output-loop)
                           (fn-zin-act fn-zin-pull fn-zin-need fn-zin-act-counts))))))

(local
 (defthm fn-pwzd-actual-basic-loop-terminal-frontier-independent
 (let ((r1 (fn-zin-loop b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))
       (r2 (fn-zin-loop b2 ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
  (implies (and (true-listp fn-zin-out) (not (equal (car r1) :full))
                (not (equal (car r1) :yield)) (not (equal (car r2) :yield))
                (< (len (mv-nth 6 r1)) (nfix lim)))
   (equal (fn-pwz-semantic-observation r1) (fn-pwz-semantic-observation r2))))
 :rule-classes nil
 :hints (("Goal"
           :use ((:instance fn-pwz-actual-basic-loop-is-atomic-unconditionally (b b1) (lim m))
                 (:instance fn-pwz-actual-basic-loop-is-atomic-unconditionally (b b2))
                 (:instance fn-pwzd-atomic-nonfull-prefix-can-change-frontier (b (fn-pwz-actual-loop-semantic-fuel b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
                 (:instance fn-pwz-atomic-terminal-observation-fuel-independent (b1 (fn-pwz-actual-loop-semantic-fuel b1 ip end m fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)) (b2 (fn-pwz-actual-loop-semantic-fuel b2 ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))))
           :in-theory (e/d (fn-pwz-semantic-observation)
                           (fn-zin-loop fn-pwz-atomic-output-loop fn-pwz-actual-loop-semantic-fuel
                            fn-zin-act fn-zin-step fn-zin-pull fn-zin-need fn-zin-loop-counts
                            fn-zin-step-out-free fn-pwz-output-action-prefix nfix min))))))

(local
 (defthm fn-pwzd-actual-feed-terminal-frontier-independent
 (let ((r1 (fn-zin-feed b1 fn-zin-st ip end m fn-octets fn-zin-win fn-zin-tab nil))
       (r2 (fn-zin-feed b2 fn-zin-st ip end lim fn-octets fn-zin-win fn-zin-tab nil)))
  (implies (and (not (equal (car r1) :full))
                (not (equal (car r1) :yield)) (not (equal (car r2) :yield))
                (< (len (mv-nth 6 r1)) (nfix lim)))
   (equal (fn-pwz-semantic-observation r1) (fn-pwz-semantic-observation r2))))
 :rule-classes nil
 :hints (("Goal" :use (:instance fn-pwzd-actual-basic-loop-terminal-frontier-independent (fn-zin-out nil))
           :in-theory (e/d (fn-zin-feed fn-zin-window-ready-p fn-zin-tab-okp fn-pwz-semantic-observation)
                           (fn-zin-loop fn-zin-feed-unfolds nfix min))))))

(local
 (defthm fn-pwzd-actual-initialize-output-empty
  (equal (mv-nth 3 (fn-pzw-initialize dict fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)) nil)
  :hints (("Goal" :in-theory (e/d (fn-pzw-initialize) (fn-zin-reset fn-zin-payload-ready))))))

(local
 (defthm fn-pwzd-actual-bounded-frontier-feed-budget-margin
 (let* ((init (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out))
        (c (len fn-octets)) (credited (fn-zin-set 7 c (car init)))
        (r (fn-zin-feed (fn-pzd-budget c n) credited 0 c m
                        fn-octets (mv-nth 1 init) (mv-nth 2 init) nil)))
  (implies (<= (nfix m) (+ 1 (nfix n)))
   (<= (+ 3837 (* 7 c)) (mv-nth 1 r))))
 :rule-classes nil
 :hints (("Goal"
          :use ((:instance fn-pwz-actual-loop-charge-bound
                 (b (fn-pzd-budget (len fn-octets) n)) (ip 0) (end (len fn-octets))
                 (lim m)
                 (fn-zin-st (fn-zin-set 7 (len fn-octets) (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out))))
                 (fn-zin-win (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)))
                 (fn-zin-tab (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)))
                 (fn-zin-out nil))
                (:instance fn-zin-loop-counts
                 (b (fn-pzd-budget (len fn-octets) n)) (ip 0) (end (len fn-octets))
                 (lim m)
                 (fn-zin-st (fn-zin-set 7 (len fn-octets) (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out))))
                 (fn-zin-win (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)))
                 (fn-zin-tab (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)))
                 (fn-zin-out nil))
                (:instance fn-pwzc-actual-loop-input-position-upper-bound
                 (b (fn-pzd-budget (len fn-octets) n)) (ip 0) (end (len fn-octets))
                 (lim m)
                 (fn-zin-st (fn-zin-set 7 (len fn-octets) (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out))))
                 (fn-zin-win (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)))
                 (fn-zin-tab (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)))
                 (fn-zin-out nil))
                (:instance fn-zin-feed-out-bound
                 (b (fn-pzd-budget (len fn-octets) n)) (start 0) (end (len fn-octets))
                 (lim m)
                 (fn-zin-st (fn-zin-set 7 (len fn-octets) (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out))))
                 (fn-zin-win (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)))
                 (fn-zin-tab (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)))
                 (fn-zin-out nil)))
          :in-theory (e/d (fn-zin-feed fn-pzd-budget)
                          (fn-zin-loop fn-zin-step fn-zin-act fn-zin-pull fn-zin-need
                           fn-pzw-initialize fn-zin-reset create-fn-zin-st fn-zin-bomb-okp fn-zin-stored-limit fn-zin-stored-allowance
                           fn-pwz-progress-statep fn-pwz-progress-phase
                           fn-zin-loop-counts fn-zin-feed-out-bound nfix min))))))

(local
 (defthm fn-pwzd-actual-bounded-frontier-feed-never-yields
 (let* ((init (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out))
        (c (len fn-octets)) (credited (fn-zin-set 7 c (car init)))
        (r (fn-zin-feed (fn-pzd-budget c n) credited 0 c m
                        fn-octets (mv-nth 1 init) (mv-nth 2 init) nil)))
  (implies (<= (nfix m) (+ 1 (nfix n)))
   (not (equal (car r) :yield))))
 :rule-classes nil
 :hints (("Goal" :use fn-pwzd-actual-bounded-frontier-feed-budget-margin
          :in-theory (disable fn-pzw-initialize create-fn-zin-st fn-zin-feed fn-zin-loop
                              fn-pzd-budget fn-zin-stored-limit fn-pwz-progress-statep fn-pwz-progress-phase)))))

(local
 (defthm fn-pwzd-stored-global-frontier-bound
  (implies (and (natp produced) (<= produced (nfix expected)))
   (<= (+ produced (fn-pzw-room (min (nfix expected) allowance) produced)) (+ 1 (nfix expected))))
  :hints (("Goal" :in-theory (enable fn-pzw-room min nfix)))))

(local
 (defthm fn-pwzd-actual-initialize-ignores-buffers
  (implies (syntaxp (not (and (equal fn-zin-win ''nil) (equal fn-zin-tab ''nil) (equal fn-zin-out ''nil))))
   (equal (fn-pzw-initialize dict fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
          (fn-pzw-initialize dict fn-zin-st nil nil nil)))
  :hints (("Goal" :in-theory (e/d (fn-pzw-initialize) (fn-zin-reset fn-zin-payload-ready))))))

(local
 (defthm fn-pwzd-actual-canonical-decode-feed-unrestricted-input
 (let* ((init (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out))
        (c (len fn-octets))
        (r (fn-zin-feed (fn-pzd-budget c n) (fn-zin-set 7 c (car init)) 0 c
                       (fn-zin-stored-limit c (+ 1 (nfix n)))
                       fn-octets (mv-nth 1 init) (mv-nth 2 init) (mv-nth 3 init))))
  (equal (fn-pzd-decode dict fn-octets n)
          (if (and (zp n) (atom fn-octets)) (list :ok nil)
            (fn-pzd-answer (fn-zin-stored-status (car r) c (mv-nth 3 r)) (mv-nth 6 r) n))))
 :rule-classes nil
 :hints (("Goal"
           :in-theory (e/d (fn-pzd-decode fn-zin-payload-with fn-octets-from-list fn-zin-out-list)
                           (fn-zin-payload-bufs fn-pzw-initialize create-fn-zin-st
                            fn-zin-feed fn-zin-stored-limit fn-zin-stored-status fn-pzd-answer
                            fn-pzd-budget fn-zin-payload-bufs-is-payload-with nfix min))))))

(local
 (defthm fn-pwzd-actual-canonical-decode-terminal-unrestricted-input
 (let* ((init (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out))
        (c (len fn-octets))
        (credited (fn-zin-set 7 c (car init)))
        (r (fn-zin-feed b credited 0 c m fn-octets (mv-nth 1 init) (mv-nth 2 init) nil)))
  (implies (and (not (equal (car r) :full)) (not (equal (car r) :yield))
                (< (len (mv-nth 6 r)) (fn-zin-stored-limit c (+ 1 (nfix n)))))
   (equal (fn-pzd-decode dict fn-octets n)
          (if (and (zp n) (atom fn-octets)) (list :ok nil)
            (fn-pzd-answer (fn-zin-stored-status (car r) c (mv-nth 3 r)) (mv-nth 6 r) n)))))
 :rule-classes nil
 :hints (("Goal"
           :use ((:instance fn-pwzd-actual-canonical-decode-feed-unrestricted-input)
                 (:instance fn-pwzc-actual-canonical-feed-never-yields)
                 (:instance fn-pwzd-actual-feed-terminal-frontier-independent
                  (b1 b) (b2 (fn-pzd-budget (len fn-octets) n))
                  (ip 0) (end (len fn-octets)) (lim (fn-zin-stored-limit (len fn-octets) (+ 1 (nfix n))))
                  (fn-zin-st (fn-zin-set 7 (len fn-octets) (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)))) (fn-zin-win (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out))) (fn-zin-tab (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)))))
           :in-theory (e/d (fn-pwz-semantic-observation)
                           (fn-pzd-decode fn-pzd-answer fn-pzd-budget fn-zin-feed fn-zin-loop
                            fn-zin-stored-status fn-zin-stored-limit fn-pzw-initialize create-fn-zin-st
                            nfix min))))))

(local
 (defthm fn-pwzd-logical-snoc-length
  (equal (len (fn-oct-snoc xs o)) (+ 1 (len xs)))
  :hints (("Goal" :induct (fn-oct-snoc xs o) :in-theory (enable fn-oct-snoc)))))

(local
 (defthm fn-pwzd-logical-back-copy-length
   (implies (and (posp off) (<= off (len xs)))
            (equal (len (fn-oct-back-copy off n xs)) (+ (len xs) (nfix n))))
   :hints (("Goal" :induct (fn-oct-back-copy off n xs)))))

(local
 (defthm fn-pwzd-logical-nthcdr-length
  (equal (len (nthcdr n x)) (nfix (- (len x) (nfix n))))
  :hints (("Goal" :induct (nthcdr n x) :in-theory (enable nthcdr nfix len)))))

(local
 (defthm fn-pwzd-actual-payload-ready-buffer-lengths-unconditional
  (let ((r (fn-zin-payload-ready dict fn-zin-win fn-zin-tab)))
   (and (equal (len (mv-nth 1 r)) 65536) (equal (len (mv-nth 2 r)) 3494)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-zin-payload-ready)
                           (fn-oct-back-copy (:e fn-oct-back-copy)
                            (:e fn-zin-win-append-back) (:e fn-zin-tab-append-back)
                            (:e fn-octets$a-append-back)))))))

(local
 (defthm fn-pwzd-actual-initialize-buffer-lengths-unconditional
  (let ((r (fn-pzw-initialize dict fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))
   (and (equal (len (mv-nth 1 r)) 65536) (equal (len (mv-nth 2 r)) 3494)))
  :hints (("Goal" :in-theory (e/d (fn-pzw-initialize) (fn-zin-reset fn-zin-payload-ready))))))

(local
 (defthm fn-pwzd-actual-initialized-stored-output-count-unconditional
  (let* ((init (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out))
         (r (fn-pzw-stored-chunk requested remaining 0 end compressed expected (car init)
                                 fn-octets (mv-nth 1 init) (mv-nth 2 init) nil)))
   (equal (fn-zin-tout (mv-nth 3 r)) (len (mv-nth 6 r))))
  :hints (("Goal" :use (:instance fn-pzw-stored-chunk-counts-real-input (start 0)
                        (fn-zin-st (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out))) (fn-zin-win (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)))
                        (fn-zin-tab (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out))) (fn-zin-out nil))
           :in-theory (disable fn-pzw-stored-chunk fn-pzw-initialize create-fn-zin-st
                               fn-pzw-stored-chunk-counts-real-input fn-zin-loop-counts)))))

(defthm fn-pwzd-actual-two-stored-windows-canonical-answer
 (let* ((init (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (c (len fn-octets)) (budget (fn-pzd-budget c n))
        (r1 (fn-pzw-stored-chunk requested1 budget 0 c c n (car init) fn-octets (mv-nth 1 init) (mv-nth 2 init) nil))
        (remaining2 (fn-pzw-budget-left requested1 budget (mv-nth 1 r1)))
        (r2 (fn-pzw-stored-chunk requested2 remaining2 (mv-nth 2 r1) c c n (mv-nth 3 r1) fn-octets
                                (mv-nth 4 r1) (mv-nth 5 r1) (mv-nth 6 r1)))
        (output (append (mv-nth 6 r1) (mv-nth 6 r2))))
  (implies (and (member-equal (car r1) '(:yield :full))
                (not (equal (car r2) :yield)) (not (equal (car r2) :full))
                (< (len output) (fn-zin-stored-limit c (+ 1 (nfix n)))))
   (equal (fn-pzd-decode dict fn-octets n)
          (if (and (zp n) (atom fn-octets)) (list :ok nil)
            (fn-pzd-answer (fn-zin-stored-status (car r2) c (mv-nth 3 r2)) output n)))))
 :rule-classes nil
 :hints (("Goal"
 :use ((:instance fn-pwzc-canonical-output-frontier-bounds (c (len fn-octets)))
       (:instance fn-pwzd-actual-stored-two-quantum-or-full-windows
         (remaining1 (fn-pzd-budget (len fn-octets) n)) (remaining2 (fn-pzw-budget-left requested1 (fn-pzd-budget (len fn-octets) n) (mv-nth 1 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len fn-octets) n) 0 (len fn-octets) (len fn-octets) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) fn-octets (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil)))) (start 0) (end (len fn-octets)) (compressed (len fn-octets)) (expected n) (b0 (fn-pzd-budget (len fn-octets) n)) (fn-zin-st (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out))) (fn-zin-win (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out))) (fn-zin-tab (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out))) (fn-zin-out nil))
       (:instance fn-pwzd-actual-initialized-stored-output-count-unconditional (requested requested1) (remaining (fn-pzd-budget (len fn-octets) n)) (end (len fn-octets)) (compressed (len fn-octets)) (expected n))
       (:instance fn-pwzd-stored-global-frontier-bound (produced (len (mv-nth 6 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len fn-octets) n) 0 (len fn-octets) (len fn-octets) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) fn-octets (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil)))) (expected n) (allowance (fn-pzw-stored-allowance (len fn-octets))))
       (:instance fn-pwzd-actual-bounded-frontier-feed-never-yields (m (+ (len (mv-nth 6 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len fn-octets) n) 0 (len fn-octets) (len fn-octets) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) fn-octets (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil))) (fn-pzw-room (min (nfix n) (fn-pzw-stored-allowance (len fn-octets))) (fn-zin-tout (mv-nth 3 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len fn-octets) n) 0 (len fn-octets) (len fn-octets) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) fn-octets (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil)))))))
       (:instance fn-pwzd-actual-canonical-decode-terminal-unrestricted-input (b (fn-pzd-budget (len fn-octets) n)) (m (+ (len (mv-nth 6 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len fn-octets) n) 0 (len fn-octets) (len fn-octets) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) fn-octets (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil))) (fn-pzw-room (min (nfix n) (fn-pzw-stored-allowance (len fn-octets))) (fn-zin-tout (mv-nth 3 (fn-pzw-stored-chunk requested1 (fn-pzd-budget (len fn-octets) n) 0 (len fn-octets) (len fn-octets) n (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) fn-octets (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil))))))))
 :in-theory (e/d (fn-pwz-semantic-observation)
                 (fn-pzd-decode fn-pzd-answer fn-pzd-budget fn-pzw-stored-chunk fn-pzw-budget-left
                  fn-pzw-quantum fn-pzw-room fn-pzw-stored-allowance fn-zin-feed fn-zin-loop
                  fn-zin-stored-status fn-zin-stored-limit fn-pzw-initialize create-fn-zin-st
                  fn-zin-loop-counts fn-pzw-stored-chunk-counts-real-input fn-pzw-stored-chunk-is-resumable-run
                  fn-zin-feed-unfolds fn-zin-loop-stops fn-pwzc-actual-loop-keeps-buffer-lengths
                  fn-pwzd-stored-global-frontier-bound fn-pwzc-canonical-output-frontier-bounds
                  fn-pwzd-actual-initialized-stored-output-count-unconditional nfix min)))))

(local
 (defthm fn-pwfc-cancel-prefix-fuel
  (equal (+ x (- x) y) (fix y))
  :hints (("Goal" :use (:instance associativity-of-+ (x x) (y (- x)) (z y))
   :in-theory (disable associativity-of-+)))))

(local
 (defthm fn-pwfc-actual-loop-semantic-fuel-funds-step-budget
  (<= (nfix b) (fn-pwz-actual-loop-semantic-fuel b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))
  :rule-classes :linear
  :hints (("Goal" :induct (fn-pwz-actual-loop-semantic-fuel b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
   :in-theory (e/d (fn-pwz-actual-loop-semantic-fuel)
    (fn-zin-act fn-zin-step fn-zin-pull fn-pwz-step-action-count))))))

(local
 (defthm fn-pwfc-loop-semantic-fuel-natural
  (natp (fn-pwz-actual-loop-semantic-fuel b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))
  :rule-classes :type-prescription
  :hints (("Goal" :induct (fn-pwz-actual-loop-semantic-fuel b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
   :in-theory (e/d (fn-pwz-actual-loop-semantic-fuel) (fn-zin-act fn-zin-step fn-zin-pull fn-pwz-step-action-count))))))


(local
 (defthm fn-pwfc-atomic-completed-budget-padding
 (let ((r (fn-pwz-atomic-output-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
  (implies (and (natp b) (natp extra) (not (equal (car r) :yield)))
   (equal (fn-pwz-atomic-output-loop (+ b extra) ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
          (mv (car r) (+ extra (mv-nth 1 r)) (mv-nth 2 r) (mv-nth 3 r)
              (mv-nth 4 r) (mv-nth 5 r) (mv-nth 6 r)))))
 :rule-classes nil
 :hints (("Goal" :induct (fn-pwz-atomic-output-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
          :in-theory (e/d (fn-pwz-atomic-output-loop)
                          (fn-zin-act fn-zin-pull fn-zin-need fn-zin-act-counts
                           fn-pwfc-actual-loop-semantic-fuel-funds-step-budget))))))


(local
 (defthm fn-pwfc-completed-atomic-budget-positive
  (implies (not (equal (car (fn-pwz-atomic-output-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)) :yield))
           (posp b))
  :hints (("Goal" :expand ((fn-pwz-atomic-output-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))
   :in-theory (disable fn-pwz-atomic-output-loop fn-zin-act fn-zin-pull fn-zin-need)))))

(local
 (defthm fn-pwfc-completed-atomic-funds-actual-loop-effects
  (let ((r (fn-pwz-atomic-output-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))
        (actual (fn-zin-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
   (implies (and (natp b) (not (equal (car r) :yield)))
    (and (not (equal (car actual) :yield))
         (equal (fn-pwz-semantic-observation actual) (fn-pwz-semantic-observation r)))))
  :rule-classes nil
  :hints (("Goal"
   :use ((:instance fn-pwz-actual-basic-loop-is-atomic-unconditionally)
         (:instance fn-pwfc-atomic-completed-budget-padding
          (extra (- (fn-pwz-actual-loop-semantic-fuel b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out) b))))
   :in-theory (e/d (fn-pwz-semantic-observation)
    (fn-zin-loop fn-pwz-actual-loop-semantic-fuel fn-pwz-atomic-output-loop))))))

(local
 (defthm fn-pwfc-atomic-output-prefix-and-length
  (implies (true-listp fn-zin-out)
   (let ((out (mv-nth 6 (fn-pwz-atomic-output-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))))
    (and (true-listp out) (<= (len fn-zin-out) (len out)))))
  :rule-classes ((:rewrite :corollary
    (implies (true-listp fn-zin-out)
     (true-listp (mv-nth 6 (fn-pwz-atomic-output-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))))
   (:linear :corollary
    (implies (true-listp fn-zin-out)
     (<= (len fn-zin-out) (len (mv-nth 6 (fn-pwz-atomic-output-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))))))
  :hints (("Goal" :induct (fn-pwz-atomic-output-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
   :in-theory (e/d (fn-pwz-atomic-output-loop) (fn-zin-act fn-zin-pull fn-zin-need))))))

(local
 (defthm fn-pwfc-atomic-full-has-reached-frontier
  (let ((r (fn-pwz-atomic-output-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
   (implies (equal (car r) :full) (<= (nfix lim) (len (mv-nth 6 r)))))
  :rule-classes :linear
  :hints (("Goal" :induct (fn-pwz-atomic-output-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
   :in-theory (e/d (fn-pwz-atomic-output-loop) (fn-zin-act fn-zin-pull fn-zin-need))))))

(local
 (defthm fn-pwfc-atomic-terminal-starts-below-frontier
  (let ((r (fn-pwz-atomic-output-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
   (implies (and (not (equal (car r) :full)) (not (equal (car r) :yield)))
    (< (len fn-zin-out) (nfix lim))))
  :rule-classes :linear
  :hints (("Goal" :expand ((fn-pwz-atomic-output-loop b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))
   :in-theory (disable fn-pwz-atomic-output-loop fn-zin-act fn-zin-pull fn-zin-need)))))

(local
 (defthm fn-pwfc-yield-turns-atomic-rewrite
  (equal (mv-nth 0 (fn-pwy-actual-loop-turns quanta ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))
   (fn-pwz-atomic-output-loop
    (mv-nth 1 (fn-pwy-actual-loop-turns quanta ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))
    ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))
  :hints (("Goal" :use fn-pwy-actual-finite-yield-turns-complete-effects
   :in-theory (disable fn-pwy-actual-loop-turns fn-pwz-atomic-output-loop)))))

(local
 (defthm fn-pwfc-terminal-finite-output-establishes-frontier-condition
  (let* ((s (fn-pwf-actual-output-turns turns ip end fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out))
         (r (mv-nth 0 s)))
   (implies (and (true-listp fn-zin-out) (not (equal (car r) :full)) (not (equal (car r) :yield)))
    (and (mv-nth 3 s) (< (len fn-zin-out) (mv-nth 2 s)))))
  :hints (("Goal" :induct (fn-pwf-actual-output-turns turns ip end fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)
   :in-theory (e/d (fn-pwf-actual-output-turns)
    (fn-pwy-actual-loop-turns fn-pwz-atomic-output-loop))))))

; Actual initialization/dictionary and arbitrary finite output/yield turns.
; No native tariff; the original canonical answer remains the reference.
(defthm fn-pwfc-actual-finite-initialized-output-windows-canonical-answer
 (let* ((init (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (c (len fn-octets))
        (s (fn-pwf-actual-output-turns turns 0 c (fn-zin-set 7 c (car init))
                  fn-octets (mv-nth 1 init) (mv-nth 2 init) nil))
        (r (mv-nth 0 s)))
  (implies (and (not (equal (car r) :full)) (not (equal (car r) :yield))
                (< (len (mv-nth 6 r)) (fn-zin-stored-limit c (+ 1 (nfix n)))))
   (equal (fn-pzd-decode dict fn-octets n)
    (if (and (zp n) (atom fn-octets)) (list :ok nil)
     (fn-pzd-answer (fn-zin-stored-status (car r) c (mv-nth 3 r)) (mv-nth 6 r) n)))))
 :rule-classes nil
 :hints (("Goal"
  :use ((:instance fn-pwfc-terminal-finite-output-establishes-frontier-condition
          (ip 0) (end (len fn-octets)) (fn-zin-st (fn-zin-set 7 (len fn-octets) (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)))) (fn-zin-win (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out))) (fn-zin-tab (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out))) (fn-zin-out nil))
        (:instance fn-pwf-actual-finite-output-yields-complete-effects
          (ip 0) (end (len fn-octets)) (fn-zin-st (fn-zin-set 7 (len fn-octets) (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)))) (fn-zin-win (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out))) (fn-zin-tab (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out))) (fn-zin-out nil))
        (:instance fn-pwfc-completed-atomic-budget-positive
          (b (mv-nth 1 (fn-pwf-actual-output-turns turns 0 (len fn-octets) (fn-zin-set 7 (len fn-octets) (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out))) fn-octets (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil))) (ip 0) (end (len fn-octets)) (lim (mv-nth 2 (fn-pwf-actual-output-turns turns 0 (len fn-octets) (fn-zin-set 7 (len fn-octets) (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out))) fn-octets (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil))) (fn-zin-st (fn-zin-set 7 (len fn-octets) (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)))) (fn-zin-win (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out))) (fn-zin-tab (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out))) (fn-zin-out nil))
        (:instance fn-pwfc-completed-atomic-funds-actual-loop-effects
          (b (mv-nth 1 (fn-pwf-actual-output-turns turns 0 (len fn-octets) (fn-zin-set 7 (len fn-octets) (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out))) fn-octets (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil))) (ip 0) (end (len fn-octets)) (lim (mv-nth 2 (fn-pwf-actual-output-turns turns 0 (len fn-octets) (fn-zin-set 7 (len fn-octets) (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out))) fn-octets (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil))) (fn-zin-st (fn-zin-set 7 (len fn-octets) (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)))) (fn-zin-win (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out))) (fn-zin-tab (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out))) (fn-zin-out nil))
        (:instance fn-pwzd-actual-canonical-decode-terminal-unrestricted-input
          (b (mv-nth 1 (fn-pwf-actual-output-turns turns 0 (len fn-octets) (fn-zin-set 7 (len fn-octets) (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out))) fn-octets (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil))) (m (mv-nth 2 (fn-pwf-actual-output-turns turns 0 (len fn-octets) (fn-zin-set 7 (len fn-octets) (car (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out))) fn-octets (mv-nth 1 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) (mv-nth 2 (fn-pzw-initialize dict (create-fn-zin-st) fn-zin-win fn-zin-tab fn-zin-out)) nil)))))
  :in-theory (e/d (fn-pwz-semantic-observation fn-zin-feed fn-zin-window-ready-p fn-zin-tab-okp)
   (fn-pwf-actual-output-turns fn-pwy-actual-loop-turns fn-pwz-atomic-output-loop
    fn-zin-loop fn-zin-feed-unfolds fn-pwz-actual-loop-semantic-fuel
    fn-pzd-decode fn-pzd-answer fn-zin-stored-status fn-zin-stored-limit
    fn-pzw-initialize create-fn-zin-st nfix min)))))
