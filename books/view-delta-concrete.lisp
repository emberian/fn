; W9's keyed aggregate, stored in the existing string-indexed radix trie.
; The reconstruction oracle stays in view-delta; no served read walks facts.
; Zero entries keep their trie path: representation charge includes historical
; subjects until the separately budgeted initialization/reclaim rebuild.
(in-package "ACL2")
(include-book "view-delta")
(include-book "msgid-index-concrete")
(local (include-book "arithmetic/top" :dir :system))

(defun fn-vdc-get (key trie)
  (declare (xargs :guard t))
  (let ((r (fn-mxc-lookup key trie)))
    (if (fn-vd-pairp r) r *fn-vd-zero*)))

(defun fn-vdc-put (key pair trie)
  (declare (xargs :guard t))
  (if (stringp key) (fn-midx-put-chars (coerce key 'list) pair trie) trie))

(defthm fn-vdc-get-pairp
  (fn-vd-pairp (fn-vdc-get key trie))
  :hints (("Goal" :in-theory (enable fn-vd-pairp))))

(defthm fn-vdc-count-natp
  (natp (car (fn-vdc-get key trie))) :rule-classes :type-prescription
  :hints (("Goal" :use fn-vdc-get-pairp
           :in-theory (e/d (fn-vd-pairp) (fn-vdc-get-pairp)))))
(defthm fn-vdc-sum-natp
  (natp (cdr (fn-vdc-get key trie))) :rule-classes :type-prescription
  :hints (("Goal" :use fn-vdc-get-pairp
           :in-theory (e/d (fn-vd-pairp) (fn-vdc-get-pairp)))))
(defthm fn-vdc-consp
  (consp (fn-vdc-get key trie)) :rule-classes :type-prescription
  :hints (("Goal" :use fn-vdc-get-pairp
           :in-theory (e/d (fn-vd-pairp) (fn-vdc-get-pairp)))))

(defthm fn-vdc-get-of-put
  (implies (and (stringp key) (stringp wanted) (fn-vd-pairp pair))
           (equal (fn-vdc-get wanted (fn-vdc-put key pair trie))
                  (if (equal wanted key) pair (fn-vdc-get wanted trie))))
  :hints (("Goal" :in-theory (enable fn-mxc-lookup
                                     fn-midx-key-chars fn-vd-pairp)
           :use ((:instance fn-midx-get-chars-of-put-chars
                    (wanted (coerce wanted 'list)) (characters (coerce key 'list))
                    (article pair))))))

(defun fn-vdc-bump (key weight trie)
  (declare (xargs :guard t :verify-guards nil))
  (let ((r (fn-vdc-get key trie)))
    (fn-vdc-put key (cons (+ 1 (car r)) (+ (nfix weight) (cdr r))) trie)))

(defun fn-vdc-unbump (key weight trie)
  (declare (xargs :guard t :verify-guards nil))
  (let ((r (fn-vdc-get key trie)))
    (fn-vdc-put key (if (<= (car r) 1) *fn-vd-zero*
                     (cons (- (car r) 1) (nfix (- (cdr r) (nfix weight))))) trie)))

(verify-guards fn-vdc-bump
  :hints (("Goal" :use fn-vdc-get-pairp
           :in-theory (e/d (fn-vd-pairp) (fn-vdc-get-pairp)))))
(verify-guards fn-vdc-unbump
  :hints (("Goal" :use fn-vdc-get-pairp
           :in-theory (e/d (fn-vd-pairp) (fn-vdc-get-pairp)))))

(defun fn-vdc-contribsp (cs)
  (declare (xargs :guard t))
  (if (consp cs)
      (and (consp (car cs)) (stringp (caar cs)) (fn-vdc-contribsp (cdr cs)))
    (equal cs nil)))

(defun-sk fn-vdc-correspondp (trie cs)
  (forall (key) (implies (stringp key)
                        (equal (fn-vdc-get key trie) (fn-vd-oracle-at key cs)))))
(in-theory (disable fn-vdc-correspondp))

(defthm fn-vdc-get-of-bump-is-oracle
  (implies (and (consp c) (stringp (car c)) (stringp key)
                (equal (fn-vdc-get key trie) (fn-vd-oracle-at key cs)))
           (equal (fn-vdc-get key (fn-vdc-bump (car c) (cdr c) trie))
                  (fn-vd-oracle-at key (cons c cs))))
  :hints (("Goal" :expand ((fn-vd-oracle-at key (cons c cs)))
           :in-theory (e/d (fn-vdc-bump fn-vd-pairp)
                           (fn-vdc-get fn-vdc-put fn-vd-oracle-at)))))

(defthm fn-vdc-get-of-unbump-is-oracle
  (implies (and (consp c) (stringp (car c)) (stringp key) (member-equal c cs)
                (equal (fn-vdc-get key trie) (fn-vd-oracle-at key cs))
                (equal (fn-vdc-get (car c) trie) (fn-vd-oracle-at (car c) cs)))
           (equal (fn-vdc-get key (fn-vdc-unbump (car c) (cdr c) trie))
                  (fn-vd-oracle-at key (remove1-equal c cs))))
  :hints (("Goal" :in-theory (e/d (fn-vdc-unbump fn-vd-pairp)
                     (fn-vdc-get fn-vdc-put fn-vd-oracle-at fn-vd-oracle-at-of-remove1))
           :use ((:instance fn-vd-oracle-at-of-remove1 (k key))
                 (:instance fn-vd-oracle-at-member-bounds (k (car c)))
                 (:instance fn-vd-oracle-at-count-one-is-the-member (k (car c)))))))

(defthm fn-vdc-correspondp-of-nil
  (fn-vdc-correspondp nil nil)
  :hints (("Goal" :in-theory (enable fn-vdc-correspondp fn-vdc-get
                                     fn-mxc-lookup fn-mxc-get fn-vd-pairp
                                     fn-vd-oracle-at))))

(in-theory (disable fn-vdc-get fn-vdc-put fn-vdc-bump fn-vdc-unbump fn-vdc-correspondp-necc))

(defthm fn-vdc-correspondp-of-bump
  (implies (and (consp c) (stringp (car c)) (fn-vdc-correspondp trie cs))
           (fn-vdc-correspondp (fn-vdc-bump (car c) (cdr c) trie) (cons c cs)))
  :hints (("Goal"
           :expand ((fn-vdc-correspondp (fn-vdc-bump (car c) (cdr c) trie) (cons c cs)))
           :use ((:instance fn-vdc-correspondp-necc
                   (key (fn-vdc-correspondp-witness
                         (fn-vdc-bump (car c) (cdr c) trie) (cons c cs))))))))

(defthm fn-vdc-correspondp-of-unbump
  (implies (and (consp c) (stringp (car c)) (member-equal c cs)
                (fn-vdc-correspondp trie cs))
           (fn-vdc-correspondp (fn-vdc-unbump (car c) (cdr c) trie) (remove1-equal c cs)))
  :hints (("Goal"
           :expand ((fn-vdc-correspondp (fn-vdc-unbump (car c) (cdr c) trie)
                                         (remove1-equal c cs)))
           :use ((:instance fn-vdc-correspondp-necc
                   (key (fn-vdc-correspondp-witness
                         (fn-vdc-unbump (car c) (cdr c) trie) (remove1-equal c cs))))
                 (:instance fn-vdc-correspondp-necc (key (car c)))))))

(defun fn-vdc-build-loop (cs trie)
  (declare (xargs :guard (fn-vdc-contribsp cs)))
  (if (consp cs)
      (fn-vdc-build-loop (cdr cs) (fn-vdc-bump (caar cs) (cdar cs) trie))
    trie))

(in-theory (disable fn-vdc-get fn-vdc-put fn-vdc-bump fn-vdc-unbump))

(local
 (defthm fn-vdc-put-nonstring-key-is-unchanged
   (implies (not (stringp key)) (equal (fn-vdc-put key pair trie) trie))
   :hints (("Goal" :in-theory (enable fn-vdc-put)))))

(defthm fn-vdc-get-of-build-loop
  (implies (stringp key)
           (equal (fn-vdc-get key (fn-vdc-build-loop cs trie))
                  (cons (+ (car (fn-vd-oracle-at key cs)) (car (fn-vdc-get key trie)))
                        (+ (cdr (fn-vd-oracle-at key cs)) (cdr (fn-vdc-get key trie))))))
  :hints (("Goal" :induct (fn-vdc-build-loop cs trie)
           :in-theory (e/d (fn-vdc-build-loop fn-vdc-bump fn-vd-oracle-at fn-vd-pairp)
                           (fn-vdc-get fn-vdc-put)))
          ("Subgoal *1/1" :cases ((stringp (caar cs))))))

(defun fn-vdc-build (cs)
  (declare (xargs :guard (fn-vdc-contribsp cs)))
  (fn-vdc-build-loop cs nil))

(defthm fn-vdc-build-corresponds
  (fn-vdc-correspondp (fn-vdc-build cs) cs)
  :hints (("Goal"
           :in-theory (e/d (fn-vdc-correspondp fn-vdc-build fn-vdc-get
                            fn-mxc-lookup fn-vd-pairp)
                           (fn-vdc-build-loop fn-vdc-get-of-build-loop))
           :use ((:instance fn-vdc-get-of-build-loop (trie nil)
                   (key (fn-vdc-correspondp-witness (fn-vdc-build cs) cs)))))))

(in-theory (disable fn-vdc-build fn-vdc-build-loop fn-vdc-contribsp))

(defthm fn-vdc-put-preserves-unique-branches
  (implies (fn-midx-unique-branchesp trie)
           (fn-midx-unique-branchesp (fn-vdc-put key pair trie)))
  :hints (("Goal" :in-theory (enable fn-vdc-put))))
(defthm fn-vdc-bump-preserves-unique-branches
  (implies (fn-midx-unique-branchesp trie)
           (fn-midx-unique-branchesp (fn-vdc-bump key weight trie)))
  :hints (("Goal" :in-theory (enable fn-vdc-bump))))
(defthm fn-vdc-unbump-preserves-unique-branches
  (implies (fn-midx-unique-branchesp trie)
           (fn-midx-unique-branchesp (fn-vdc-unbump key weight trie)))
  :hints (("Goal" :in-theory (enable fn-vdc-unbump))))
(defthm fn-vdc-build-loop-preserves-unique-branches
  (implies (fn-midx-unique-branchesp trie)
           (fn-midx-unique-branchesp (fn-vdc-build-loop cs trie)))
  :hints (("Goal" :induct (fn-vdc-build-loop cs trie)
           :in-theory (enable fn-vdc-build-loop))))
(defthm fn-vdc-build-has-unique-branches
  (fn-midx-unique-branchesp (fn-vdc-build cs))
  :hints (("Goal" :in-theory (enable fn-vdc-build))))
