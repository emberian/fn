; Actual based-provider observation trajectory. These are proof-only folds;
; the host still calls the single existing provider tick. No reader oracle or
; authentication premise is manufactured by this book.
(in-package "ACL2")
(include-book "snapshot-based-provider-decoder-lineage")
(local (include-book "arithmetic/top" :dir :system))

(defun-nx fn-obpt-decode-consumesp (c observation)
  (and (equal (fn-omk-at 0 c) :decode)
       (equal (car (fn-hdc-result (fn-omk-at 7 c))) :yield)
       (fn-obp-byte-matchp observation c)))
(defun-nx fn-obpt-replay (observations c)
  (declare (xargs :measure (acl2-count observations)))
  (if (consp observations)
      (fn-obpt-replay (cdr observations)
        (fn-obpl-next (fn-obp-tick c (car observations))))
    c))
(defun-nx fn-obpt-decode-count (observations c)
  (declare (xargs :measure (acl2-count observations)))
  (if (consp observations)
      (+ (if (fn-obpt-decode-consumesp c (car observations)) 1 0)
         (fn-obpt-decode-count (cdr observations)
           (fn-obpl-next (fn-obp-tick c (car observations)))))
    0))
(defun-nx fn-obpt-observation-tracep (observations c pool)
  (declare (xargs :measure (acl2-count observations)))
  (and (fn-obp-cursorp c)
       (member-eq (fn-omk-at 0 c) '(:decode :padding :key :done :refused))
       (if (consp observations)
           (and (implies (fn-obpt-decode-consumesp c (car observations))
                  (fn-obpl-exact-decode-bytep (car observations) c pool))
                (fn-obpt-observation-tracep (cdr observations)
                  (fn-obpl-next (fn-obp-tick c (car observations))) pool))
         (null observations))))

(local
 (defthm fn-obpt-at-cons-unfolds
   (equal (fn-omk-at n (cons a d))
          (if (zp n) a (fn-omk-at (1- n) d)))
   :hints (("Goal" :expand ((fn-omk-at n (cons a d)))
     :in-theory (union-theories
       (union-theories (theory 'minimal-theory) (executable-counterpart-theory :here))
       '(car-cons cdr-cons))))))
(local
 (defthm fn-obpt-match-implies-nonempty-unfolds
   (implies (fn-obp-byte-matchp observation c) (consp observation))
   :hints (("Goal" :do-not-induct t
     :in-theory (union-theories
       (union-theories (theory 'minimal-theory) (executable-counterpart-theory :here))
       '(fn-obp-byte-matchp fn-omk-widthp eq not))))))
(local
 (defthm fn-obpt-terminal-feed-freezes-unfolds
   (implies (member-eq (nth 0 s) '(:done :refused))
            (equal (fn-hdc-feed byte s) s))
   :hints (("Goal" :do-not-induct t
     :in-theory (union-theories
       (union-theories (theory 'minimal-theory) (executable-counterpart-theory :here))
       '(fn-hdc-feed fn-hdc-feed-raw member-equal nth car-cons cdr-cons eq not))))))
(local
 (defthm fn-obpt-yield-is-nonterminal-unfolds
   (implies (equal (car (fn-hdc-result s)) :yield)
            (not (member-eq (nth 0 s) '(:done :refused))))
   :hints (("Goal" :in-theory (enable fn-hdc-result)))))

(local
 (defthm fn-obpt-no-consume-preserves-actual-parser-unfolds
   (implies (and (member-eq (fn-omk-at 0 c) '(:decode :padding :key :done :refused))
                 (not (fn-obpt-decode-consumesp c observation)))
            (equal (fn-omk-at 7 (fn-obpl-next (fn-obp-tick c observation)))
                   (fn-omk-at 7 c)))
   :hints (("Goal" :do-not-induct t
     :use fn-obpt-match-implies-nonempty-unfolds
     :in-theory (union-theories
       (union-theories (theory 'minimal-theory) (executable-counterpart-theory :here))
       '(fn-obp-tick fn-obpl-next fn-obpt-decode-consumesp fn-obp-demand binary-append
         fn-obp-with fn-obp-state fn-obp-refuse fn-obpt-at-cons-unfolds
         car-cons cdr-cons member-equal nth mv-nth eq not))))))
(local
 (defthm fn-obpt-consume-is-actual-pool-feed-unfolds
   (implies (and (fn-obpt-decode-consumesp c observation)
                 (fn-obpl-exact-decode-bytep observation c pool))
            (equal (fn-omk-at 7 (fn-obpl-next (fn-obp-tick c observation)))
                   (fn-hdc-feed (nth (nth 7 (fn-omk-at 7 c)) pool)
                                (fn-omk-at 7 c))))
   :hints (("Goal" :use fn-obpl-matched-decode-step-consumes-exact-pool-byte
     :in-theory (e/d (fn-obpt-decode-consumesp)
       (fn-obp-tick fn-obpl-next fn-obp-byte-matchp fn-obpl-exact-decode-bytep
        fn-omk-at fn-hdc-result fn-hdc-feed))))))
(local
 (defthm fn-obpt-decode-count-is-natural-unfolds
   (natp (fn-obpt-decode-count observations c))
   :hints (("Goal" :induct (fn-obpt-decode-count observations c)
     :in-theory (e/d (fn-obpt-decode-count)
       (fn-obpt-decode-consumesp fn-obp-tick fn-obpl-next))))))
(local
 (defthm fn-obpt-model-run-one-source-step-unfolds
   (implies (natp n)
     (equal (fn-hdc-model-run (+ 1 n) s pool)
            (fn-hdc-model-run n (fn-hdc-feed (nth (nth 7 s) pool) s) pool)))
   :hints (("Goal" :do-not-induct t
     :expand ((fn-hdc-model-run (+ 1 n) s pool))
     :in-theory (e/d (fn-hdc-model-run fn-obpt-terminal-feed-freezes-unfolds)
       (fn-hdc-feed))))))

(local
 (defthm fn-obpt-model-run-zero-unfolds
   (equal (fn-hdc-model-run 0 s pool) s)
   :hints (("Goal" :expand ((fn-hdc-model-run 0 s pool))
     :in-theory (union-theories (theory 'minimal-theory)
       (executable-counterpart-theory :here))))))

(defthm fn-obpt-actual-observation-replay-is-decoder-model-run
  (implies (fn-obpt-observation-tracep observations c pool)
    (equal (fn-omk-at 7 (fn-obpt-replay observations c))
           (fn-hdc-model-run (fn-obpt-decode-count observations c)
                            (fn-omk-at 7 c) pool)))
  :rule-classes nil
  :hints (("Goal" :induct (fn-obpt-replay observations c)
    :in-theory (union-theories
      (union-theories (theory 'minimal-theory) (executable-counterpart-theory :here))
      '(fn-obpt-replay fn-obpt-observation-tracep fn-obpt-decode-count
        fn-obpt-no-consume-preserves-actual-parser-unfolds
        fn-obpt-consume-is-actual-pool-feed-unfolds
        fn-obpt-decode-count-is-natural-unfolds
        fn-obpt-model-run-one-source-step-unfolds fn-obpt-model-run-zero-unfolds
        car-cons cdr-cons eq not unicity-of-0 fix natp
        rationalp-implies-acl2-numberp commutativity-of-+)))))

(local
 (defthm fn-obpt-carry-step-unfolds
   (implies (and (fn-obp-cursorp c) (fn-obpl-source-lineagep c pool))
            (fn-obpl-source-lineagep (fn-obpl-next (fn-obp-tick c observation)) pool))
   :hints (("Goal" :use fn-obpl-tick-preserves-source-lineage
     :in-theory (theory 'minimal-theory)))))
(defthm fn-obpt-actual-observation-replay-preserves-source-lineage
  (implies (and (fn-obpt-observation-tracep observations c pool)
                (fn-obpl-source-lineagep c pool))
           (fn-obpl-source-lineagep (fn-obpt-replay observations c) pool))
  :rule-classes nil
  :hints (("Goal" :induct (fn-obpt-replay observations c)
    :in-theory (union-theories
      (union-theories (theory 'minimal-theory) (executable-counterpart-theory :here))
      '(fn-obpt-replay fn-obpt-observation-tracep fn-obpt-carry-step-unfolds
        car-cons cdr-cons eq not)))))

(local
 (defthm fn-obpt-size-begin-parser-car-unfolds
   (equal (car (fn-hds-begin offset length epoch lease))
          (fn-hdc-begin offset length epoch lease))
   :hints (("Goal" :use fn-hds-begin-parser-is-actual-by-definition
     :in-theory (union-theories
       (union-theories (theory 'minimal-theory) (executable-counterpart-theory :here))
       '(mv-nth))))))
; Constructor projection support; the initial decoder is the actual CHECK tick.
(defthm fn-obpt-check-initializes-actual-decoder-unfolds
  (implies (and (equal (fn-omk-at 0 c) :check)
                (equal (fn-omk-at 0 (fn-obpl-next (fn-obp-tick c nil))) :decode))
    (equal (fn-omk-at 7 (fn-obpl-next (fn-obp-tick c nil)))
           (fn-hdc-begin (fn-obpl-offset c) (fn-obpl-count c)
                        (fn-omk-at 0 (fn-omk-at 1 c))
                        (fn-omk-at 1 (fn-omk-at 1 c)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
    :in-theory (union-theories
      (union-theories (theory 'minimal-theory) (executable-counterpart-theory :here))
      '(fn-obp-tick fn-obpl-next fn-obp-refuse fn-obp-with fn-obp-state fn-obp-size-with
        fn-obpl-offset fn-obpl-count fn-obpt-at-cons-unfolds
        fn-obpt-size-begin-parser-car-unfolds
        car-cons cdr-cons eq not nth mv-nth)))))

(defthm fn-obpt-successful-replay-retains-exact-decoder-result
  (let ((final (fn-obpt-replay observations c)))
    (implies (and (fn-obpt-observation-tracep observations c pool)
                  (fn-obpl-source-lineagep c pool)
                  (equal (fn-omk-at 0 final) :done))
      (let ((r (fn-hdc-result
                 (fn-hdc-model-run (fn-obpt-decode-count observations c)
                                   (fn-omk-at 7 c) pool))))
        (and (equal (car r) :ok)
             (equal (fn-omk-at 8 final) (cadr r))
             (fn-hrcur-cold-domainp (fn-omk-at 8 final) pool)
             (fn-hdc-node-in-poolp (fn-omk-at 8 final) (fn-obpl-end final))))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
    :use (fn-obpt-actual-observation-replay-is-decoder-model-run
          fn-obpt-actual-observation-replay-preserves-source-lineage
          (:instance fn-obpl-successful-completion-is-cold-codec-source
            (c (fn-obpt-replay observations c))))
    :in-theory (e/d (fn-obpl-source-lineagep)
      (fn-obpt-replay fn-obpt-observation-tracep fn-obpt-decode-count fn-obpl-end
       fn-obpl-offset fn-omk-at fn-hdc-result fn-hdc-model-run fn-hrcur-cold-domainp
       fn-hdc-node-in-poolp fn-hdcl-source-statep)))))

(in-theory (disable fn-obpt-decode-consumesp fn-obpt-replay fn-obpt-decode-count
                    fn-obpt-observation-tracep))
