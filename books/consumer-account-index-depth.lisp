; Proof-only maintained depth bound for genuine authority intent tries.
; This predicate is never executed by a served lookup or final fence.
(in-package "ACL2")
(include-book "consumer-account-index")

(defun fn-cakd-domainp (trie depth)
 (declare (xargs :guard t))
 (if (consp trie)
  (let* ((entry (car trie)) (key (fn-ag-car entry)))
   (and (consp entry)
        (if (characterp key)
            (and (posp depth) (fn-cakd-domainp (cdr entry) (1- depth)))
          (equal key *fn-midx-value-key*))
        (fn-cakd-domainp (cdr trie) depth)))
  (null trie)))

(defthm fn-cakd-get-child
 (implies (and (fn-cakd-domainp trie depth) (characterp key))
          (and (fn-cakd-domainp (fn-midx-branch-get key trie) (1- (nfix depth)))
               (implies (not (posp depth))
                        (not (fn-midx-branch-get key trie)))))
 :hints (("Goal" :induct (fn-midx-branch-get key trie)
          :in-theory (enable fn-cakd-domainp fn-midx-branch-get))))

(defthm fn-cakd-put-branch
 (implies (and (fn-cakd-domainp trie depth)
               (if (characterp key)
                   (and (posp depth) (fn-cakd-domainp value (1- depth)))
                 (equal key *fn-midx-value-key*)))
          (fn-cakd-domainp (fn-midx-branch-put key value trie) depth))
 :hints (("Goal" :induct (fn-midx-branch-put key value trie)
          :in-theory (enable fn-cakd-domainp fn-midx-branch-put))))

(local
 (defthm fn-cakd-empty-get
  (not (fn-cai-get-octets name nil))
  :hints (("Goal" :induct (fn-cai-get-octets name nil)
           :in-theory (e/d (fn-cai-get-octets fn-midx-branch-get)
                            (fn-cai-get-is-existing-trie-get))))))

(defun fn-cakd-path-induct (name trie depth)
 (declare (xargs :guard t :measure (len name)))
 (if (consp name)
  (fn-cakd-path-induct (cdr name)
     (fn-midx-branch-get (fn-cai-key-character (car name)) trie)
     (1- (nfix depth)))
  (list trie depth)))

(defthm fn-cakd-put-preserves-domain
 (implies (and (natp depth) (fn-cakd-domainp trie depth)
               (<= (len name) depth))
          (fn-cakd-domainp (fn-cai-put-octets name value trie) depth))
 :hints (("Goal" :induct (fn-cakd-path-induct name trie depth)
          :in-theory (e/d (fn-cakd-path-induct fn-cai-put-octets)
                           (fn-midx-branch-get fn-midx-branch-put
                            fn-cai-key-character fn-cakd-domainp
                            fn-cai-put-is-existing-trie-put)))
         ("Subgoal *1/1"
          :use ((:instance fn-cakd-get-child (key (fn-cai-key-character (car name)))))
          :in-theory (e/d (fn-cakd-path-induct fn-cai-put-octets)
                           (fn-cakd-get-child fn-midx-branch-get fn-midx-branch-put
                            fn-cai-key-character fn-cakd-domainp
                            fn-cai-put-is-existing-trie-put)))))

(defthm fn-cakd-long-key-has-no-binding
 (implies (and (natp depth) (fn-cakd-domainp trie depth)
               (< depth (len name)))
          (not (fn-cai-get-octets name trie)))
 :hints (("Goal" :induct (fn-cakd-path-induct name trie depth)
          :in-theory (e/d (fn-cakd-path-induct fn-cai-get-octets)
                           (fn-midx-branch-get fn-cai-key-character
                            fn-cakd-domainp fn-cai-get-is-existing-trie-get)))
         ("Subgoal *1/1"
          :use ((:instance fn-cakd-get-child (key (fn-cai-key-character (car name)))))
          :in-theory (e/d (fn-cakd-path-induct fn-cai-get-octets)
                           (fn-cakd-get-child fn-midx-branch-get fn-cai-key-character
                            fn-cakd-domainp fn-cai-get-is-existing-trie-get)))))

(in-theory (disable fn-cakd-domainp fn-cakd-path-induct))
