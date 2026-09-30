; Actual based-source decoder carry. This immutable-pool proof model is not
; authentication or a native/root-pin claim. Existing provider runtime is shared.
(in-package "ACL2")
(include-book "snapshot-based-provider")
(include-book "history-cold-source-lineage")
(local (include-book "arithmetic/top" :dir :system))

(defun-nx fn-obpl-offset (c)
  (nfix (fn-omk-at 2 (fn-omk-at 6 c))))
(defun-nx fn-obpl-count (c)
  (nfix (fn-omk-at 1 (fn-omk-at 6 c))))
(defun-nx fn-obpl-end (c)
  (+ (fn-obpl-offset c) (fn-obpl-count c)))
(defun-nx fn-obpl-next (r)
  (case (car r)
    ((:yield :stale) (cadr r))
    (:need-byte (nth 6 r))
    (:refused (caddr r))
    (:decoded (nth 4 r))
    (otherwise nil)))

; Pool length is a source-level logical relation. No runtime LEN or node scan.
(defun-nx fn-obpl-source-lineagep (c pool)
  (let ((phase (fn-omk-at 0 c)) (parser (fn-omk-at 7 c)))
    (and (<= (nfix (fn-omk-at 4 (fn-omk-at 5 (fn-omk-at 2 c)))) (len pool))
      (implies (member-eq phase '(:decode :padding :key :done))
        (and (fn-hdcl-source-statep parser (fn-obpl-offset c))
             (equal (nth 8 parser) (fn-obpl-end c))
             (< (fn-obpl-end c) *fn-hrcur-u64-bound*)
             (<= (fn-obpl-end c) (len pool))
             (implies (not (eq phase :decode))
               (and (equal (car (fn-hdc-result parser)) :ok)
                    (equal (fn-omk-at 8 c) (cadr (fn-hdc-result parser))))))))))

; The reader/physical bridge must establish this equation separately.
(defun-nx fn-obpl-exact-decode-bytep (observation c pool)
  (equal (fn-omk-at 6 observation)
         (nth (nth 7 (fn-omk-at 7 c)) pool)))

(local
 (defthm fn-obpl-matching-byte-is-octet-unfolds
   (implies (fn-obp-byte-matchp observation c)
            (fn-scc-octetp (fn-omk-at 6 observation)))
   :hints (("Goal" :in-theory
     (e/d (fn-obp-byte-matchp fn-scc-octetp unsigned-byte-p integer-range-p)
          (fn-obp-demand fn-omk-at fn-omk-token-matchp fn-omk-widthp))))))

(local
 (defthm fn-obpl-matching-byte-is-nonempty-unfolds
   (implies (fn-obp-byte-matchp observation c) (consp observation))
   :hints (("Goal" :do-not-induct t
     :in-theory (union-theories
       (union-theories (theory 'minimal-theory) (executable-counterpart-theory :here))
       '(fn-obp-byte-matchp fn-omk-widthp eq not))))))
(local
 (defthm fn-obpl-size-feed-parser-car-unfolds
   (equal (car (fn-hds-feed byte s sizes nil-prefix usable)) (fn-hdc-feed byte s))
   :hints (("Goal" :use fn-hds-feed-parser-is-actual-by-definition
     :in-theory (union-theories
       (union-theories (theory 'minimal-theory) (executable-counterpart-theory :here))
       '(mv-nth))))))

(local
 (defthm fn-obpl-terminal-decoder-feed-is-unchanged-unfolds
   (implies (not (equal (car (fn-hdc-result s)) :yield))
            (equal (fn-hdc-feed byte s) s))
   :hints (("Goal" :do-not-induct t
     :in-theory (union-theories
       (union-theories (theory 'minimal-theory) (executable-counterpart-theory :here))
       '(fn-hdc-result fn-hdc-feed fn-hdc-feed-raw member-equal nth
         car-cons cdr-cons eq not))))))

; Actual supplied decoder transition; no twin provider or assumed parser call.
(defthm fn-obpl-matched-decode-step-consumes-exact-pool-byte
  (implies (and (equal (fn-omk-at 0 c) :decode)
                (fn-obp-byte-matchp observation c)
                (fn-obpl-exact-decode-bytep observation c pool))
           (equal (fn-omk-at 7 (fn-obpl-next (fn-obp-tick c observation)))
                  (fn-hdc-feed (nth (nth 7 (fn-omk-at 7 c)) pool)
                               (fn-omk-at 7 c))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
    :use fn-obpl-matching-byte-is-nonempty-unfolds
    :in-theory (union-theories
      (union-theories (theory 'minimal-theory) (executable-counterpart-theory :here))
      '(fn-obp-tick fn-obpl-next fn-obpl-exact-decode-bytep
        fn-obp-size-with fn-obp-with fn-obp-state fn-obp-refuse fn-omk-at
        fn-obpl-terminal-decoder-feed-is-unchanged-unfolds
        fn-obpl-size-feed-parser-car-unfolds fn-hds-feed-parser-is-actual-by-definition
        car-cons cdr-cons eq not member-equal nth mv-nth)))))

(defthm fn-obpl-begin-establishes-source-lineage
  (implies (<= (nfix (fn-omk-at 4 (fn-omk-at 5 handle))) (len pool))
           (fn-obpl-source-lineagep (fn-obp-begin handle token resource) pool))
  :rule-classes nil
  :hints (("Goal" :in-theory
    (e/d (fn-obp-begin fn-obp-state fn-obpl-source-lineagep fn-omk-at)
      (fn-obp-headerp fn-omk-tokenp fn-hdcl-source-statep fn-obpl-end fn-obpl-offset)))))

(local
 (defthm fn-obpl-size-begin-parser-car-unfolds
   (equal (car (fn-hds-begin offset length epoch lease))
          (fn-hdc-begin offset length epoch lease))
   :hints (("Goal" :use fn-hds-begin-parser-is-actual-by-definition
     :in-theory (union-theories
       (union-theories (theory 'minimal-theory) (executable-counterpart-theory :here))
       '(mv-nth))))))
(local
 (defthm fn-obpl-header-has-bounded-pool-unfolds
   (implies (fn-obp-headerp h)
            (< (nfix (fn-omk-at 4 (fn-omk-at 5 h))) *fn-hrcur-u64-bound*))
   :hints (("Goal" :do-not-induct t
     :in-theory (union-theories
       (union-theories (theory 'minimal-theory) (executable-counterpart-theory :here))
       '(fn-obp-headerp fn-obp-u64s fn-omk-at nfix natp unsigned-byte-p integer-range-p
         eq not car-cons cdr-cons))))))
(local
 (defthm fn-obpl-cursor-has-bounded-pool-unfolds
   (implies (fn-obp-cursorp c)
            (< (nfix (fn-omk-at 4 (fn-omk-at 5 (fn-omk-at 2 c)))) *fn-hrcur-u64-bound*))
   :hints (("Goal" :use (:instance fn-obpl-header-has-bounded-pool-unfolds
     (h (fn-omk-at 2 c)))
     :in-theory (e/d (fn-obp-cursorp) (fn-obp-headerp fn-omk-at))))))

(local
 (defthm fn-obpl-cursor-fixed-scalar-fields-unfolds
   (implies (fn-obp-cursorp c)
     (and (natp (fn-omk-at 3 c)) (natp (fn-omk-at 4 c))
          (natp (fn-omk-at 5 c)) (natp (fn-omk-at 9 c)) (natp (fn-omk-at 13 c))
          (natp (fn-omk-at 0 (fn-omk-at 6 c)))
          (natp (fn-omk-at 1 (fn-omk-at 6 c)))
          (natp (fn-omk-at 2 (fn-omk-at 6 c)))
          (natp (fn-omk-at 3 (fn-omk-at 6 c)))))
   :hints (("Goal" :do-not-induct t
     :expand ((:free (xs) (fn-obp-u64s 4 xs)) (:free (xs) (fn-obp-u64s 3 xs))
              (:free (xs) (fn-obp-u64s 2 xs)) (:free (xs) (fn-obp-u64s 1 xs)))
     :in-theory (union-theories
       (union-theories (theory 'minimal-theory) (executable-counterpart-theory :here))
       '(fn-obp-cursorp fn-obp-u64s fn-omk-at natp unsigned-byte-p integer-range-p
         eq not car-cons cdr-cons))))))

(local
 (defthm fn-obpl-at-cons-unfolds
   (equal (fn-omk-at n (cons a d))
          (if (zp n) a (fn-omk-at (1- n) d)))
   :hints (("Goal" :expand ((fn-omk-at n (cons a d)))
     :in-theory (union-theories
       (union-theories (theory 'minimal-theory) (executable-counterpart-theory :here))
       '(car-cons cdr-cons))))))

(local
 (defthm fn-obpl-result-node-unfolds
   (equal (fn-omk-at 1 (fn-hdc-result parser)) (cadr (fn-hdc-result parser)))
   :hints (("Goal" :expand ((:free (x) (fn-omk-at 1 x)) (:free (x) (fn-omk-at 0 x)))
     :in-theory (e/d (fn-omk-at) (fn-hdc-result))))))

; One actual tick carries the decoder proof relation. Exact source-byte equality
; is not a premise: carried numeric/size/span bounds need only an octet. This
; law alone does not claim source denotation or authenticated reader lineage.
(defthm fn-obpl-tick-preserves-source-lineage
  (implies (and (fn-obp-cursorp c) (fn-obpl-source-lineagep c pool))
           (fn-obpl-source-lineagep (fn-obpl-next (fn-obp-tick c observation)) pool))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
    :use ((:instance fn-hdcl-feed-preserves-source-lineage
            (s (fn-omk-at 7 c)) (offset (fn-obpl-offset c))
            (byte (fn-omk-at 6 observation)))
          (:instance fn-hdcl-begin-establishes-source-lineage
            (offset (fn-obpl-offset c)) (count (fn-obpl-count c))
            (epoch (fn-omk-at 0 (fn-omk-at 1 c)))
            (lease (fn-omk-at 1 (fn-omk-at 1 c))))
          fn-obpl-matching-byte-is-octet-unfolds
          fn-obpl-cursor-has-bounded-pool-unfolds
          fn-obpl-cursor-fixed-scalar-fields-unfolds)
    :in-theory (union-theories
      (union-theories (theory 'minimal-theory) (executable-counterpart-theory :here))
      '(fn-obp-tick fn-obpl-next fn-obpl-source-lineagep
        fn-obpl-offset fn-obpl-count fn-obpl-end
        fn-obp-size-with fn-obp-with fn-obp-state fn-obp-refuse fn-obpl-at-cons-unfolds fn-obpl-result-node-unfolds
        fn-obp-demand binary-append
        fn-obpl-size-feed-parser-car-unfolds fn-hds-feed-parser-is-actual-by-definition
        fn-obpl-size-begin-parser-car-unfolds fn-hds-begin-parser-is-actual-by-definition
        fn-hdc-feed-preserves-lifetime
        fn-hdc-begin fn-hdc-state car-cons cdr-cons eq not member-equal nth mv-nth
        natp nfix rationalp-implies-acl2-numberp)))) )

(defthm fn-obpl-successful-completion-is-cold-codec-source
  (implies (and (fn-obpl-source-lineagep c pool)
                (equal (fn-omk-at 0 c) :done))
           (and (fn-hrcur-cold-domainp (fn-omk-at 8 c) pool)
                (fn-hdc-node-in-poolp (fn-omk-at 8 c) (fn-obpl-end c))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
    :use ((:instance fn-hdcl-successful-source-result-is-cold-codec-domain
      (s (fn-omk-at 7 c)) (offset (fn-obpl-offset c)))
      (:instance fn-hdcl-successful-source-result-retains-node-bounds
        (s (fn-omk-at 7 c)) (offset (fn-obpl-offset c))))
    :in-theory (e/d (fn-obpl-source-lineagep)
      (fn-omk-at fn-obpl-end fn-obpl-offset fn-hdc-result fn-hdcl-source-statep
       fn-hrcur-cold-domainp fn-hdc-node-in-poolp)))))

(in-theory (disable fn-obpl-offset fn-obpl-count fn-obpl-end fn-obpl-next
                    fn-obpl-source-lineagep fn-obpl-exact-decode-bytep))
