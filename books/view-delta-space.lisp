; Logical cons-cell accounting for the exact radix updater used by W9.
; This excludes integer payload sizes, allocator headers and collector lifetimes.
(in-package "ACL2")
(include-book "view-delta-concrete")
(local (include-book "arithmetic/top" :dir :system))

(defun fn-vcs-conses (x)
  (declare (xargs :guard t))
  (if (consp x) (+ 1 (fn-vcs-conses (car x)) (fn-vcs-conses (cdr x))) 0))
(defthm fn-vcs-conses-natural
  (natp (fn-vcs-conses x)) :rule-classes :type-prescription)

; The old branch's subtree is replaced, not retained in the result. Count
; it on the left so the path induction accounts for sharing exactly once.
(defthm fn-vcs-branch-put-space
  (<= (+ (fn-vcs-conses (fn-midx-branch-put key value branches))
         (fn-vcs-conses (fn-midx-branch-get key branches)))
      (+ 2 (fn-vcs-conses branches) (fn-vcs-conses key) (fn-vcs-conses value)))
  :hints (("Goal" :induct (fn-midx-branch-put key value branches)
           :in-theory (enable fn-midx-branch-put fn-midx-branch-get fn-vcs-conses
                              fn-ag-car fn-ag-cdr))))

(defthm fn-vcs-put-chars-space
  (implies (character-listp characters)
           (<= (fn-vcs-conses (fn-midx-put-chars characters value trie))
               (+ (* 2 (len characters)) 2 (fn-vcs-conses value)
                  (fn-vcs-conses trie))))
  :hints (("Goal" :induct (fn-midx-put-chars characters value trie)
           :in-theory (e/d (fn-midx-put-chars character-listp)
                            (fn-midx-branch-put fn-midx-branch-get fn-vcs-branch-put-space)))
          ("Subgoal *1/1" :use ((:instance fn-vcs-branch-put-space
                    (key (car characters))
                    (value (fn-midx-put-chars (cdr characters) value
                             (fn-midx-branch-get (car characters) trie)))
                    (branches trie))))
          ("Subgoal *1/2" :use ((:instance fn-vcs-branch-put-space
                    (key *fn-midx-value-key*) (branches trie))))))

(defthm fn-vdc-put-cons-growth
  (implies (fn-vd-pairp pair)
           (<= (fn-vcs-conses (fn-vdc-put key pair trie))
               (+ (* 2 (length (if (stringp key) key ""))) 3
                  (fn-vcs-conses trie))))
  :hints (("Goal" :in-theory (e/d (fn-vdc-put fn-vd-pairp length)
                           (fn-midx-put-chars))
           :use ((:instance fn-vcs-put-chars-space
                    (characters (coerce key 'list)) (value pair))))))

(defthm fn-vdc-bump-cons-growth
  (<= (fn-vcs-conses (fn-vdc-bump key weight trie))
      (+ (* 2 (length (if (stringp key) key ""))) 3 (fn-vcs-conses trie)))
  :hints (("Goal" :in-theory (e/d (fn-vdc-bump fn-vd-pairp)
                                  (fn-vdc-put fn-vdc-get))
           :use ((:instance fn-vdc-put-cons-growth
                   (pair (cons (+ 1 (car (fn-vdc-get key trie)))
                               (+ (nfix weight) (cdr (fn-vdc-get key trie))))))))))

(defun fn-vcs-key-characters (cs)
  (declare (xargs :guard (fn-vdc-contribsp cs)
                  :guard-hints (("Goal" :in-theory (enable fn-vdc-contribsp)))))
  (if (consp cs)
      (+ (length (caar cs)) (fn-vcs-key-characters (cdr cs))) 0))

(defthm fn-vdc-build-loop-cons-growth
  (<= (fn-vcs-conses (fn-vdc-build-loop cs trie))
      (+ (* 2 (fn-vcs-key-characters cs)) (* 3 (len cs))
         (fn-vcs-conses trie)))
  :hints (("Goal" :induct (fn-vdc-build-loop cs trie)
           :in-theory (e/d (fn-vdc-build-loop fn-vcs-key-characters length)
                            (fn-vdc-bump fn-vdc-bump-cons-growth)))
          ("Subgoal *1/1" :use ((:instance fn-vdc-bump-cons-growth
                                  (key (caar cs)) (weight (cdar cs)))))))

(in-theory (disable fn-vcs-conses fn-vcs-key-characters))
