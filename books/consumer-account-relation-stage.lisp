; Producer establishment for the complete account representation relation.
; All scans below are proof abstractions, never served-path validation.
(in-package "ACL2")
(include-book "consumer-account-relation")

(defun fn-caas-names-beforep (rows name)
  (declare (xargs :guard t))
  (if (consp rows)
      (and (fn-caa-name-lessp (fn-cp-nth 1 (car rows)) name)
           (fn-caas-names-beforep (cdr rows) name))
    t))

(defun fn-caas-last-relp (reversed last)
  (declare (xargs :guard t))
  (if (consp reversed)
      (and (consp last) (equal last (fn-cp-nth 1 (car reversed)))
           (fn-caas-names-beforep (cdr reversed) last))
    (null last)))

(defun fn-caas-merge-relp (p)
  (declare (xargs :guard t :verify-guards nil))
  (let ((prep (fn-cp-nth 5 p)))
    (and (true-listp p) (equal (len p) 9) (equal (car p) :adoption)
         (fn-caar-preparation-relp prep)
         (equal (fn-cp-nth 1 prep) :merge)
         (natp (fn-cp-nth 4 p))
         (equal (fn-cp-nth 4 p) (fn-cp-nth 7 prep))
         (equal (fn-cp-nth 3 p) (len (fn-cp-nth 3 prep)))
         (fn-caas-last-relp (fn-cp-nth 3 prep) (fn-cp-nth 6 p)))))

(local
 (defun fn-caas-order-induct (a b c)
   (if (and (consp a) (consp b) (consp c))
       (fn-caas-order-induct (cdr a) (cdr b) (cdr c))
     (list a b c))))

(local
 (defthm fn-caas-name-order-irreflexive
   (not (fn-caa-name-lessp name name))
   :hints (("Goal" :in-theory (enable fn-caa-name-lessp)))))

(local
 (defthm fn-caas-name-order-transitive
   (implies (and (fn-caa-name-lessp a b) (fn-caa-name-lessp b c))
            (fn-caa-name-lessp a c))
   :hints (("Goal" :induct (fn-caas-order-induct a b c)
            :in-theory (enable fn-caa-name-lessp)))))

(local
 (defthm fn-caas-before-transitive
   (implies (and (fn-caas-names-beforep rows a) (fn-caa-name-lessp a b))
            (fn-caas-names-beforep rows b))
   :hints (("Goal" :induct (fn-caas-names-beforep rows a)
            :in-theory (enable fn-caas-names-beforep)))))

(local
 (defthm fn-caas-before-of-append
   (equal (fn-caas-names-beforep (append xs ys) name)
          (and (fn-caas-names-beforep xs name) (fn-caas-names-beforep ys name)))
   :hints (("Goal" :in-theory (enable fn-caas-names-beforep)))))

(local
 (defthm fn-caas-before-of-revappend
   (equal (fn-caas-names-beforep (revappend xs ys) name)
          (and (fn-caas-names-beforep xs name) (fn-caas-names-beforep ys name)))
   :hints (("Goal" :induct (revappend xs ys)
            :in-theory (e/d (fn-caas-names-beforep revappend) (revappend-removal))))))

(local
 (defthm fn-caas-binding-watermark-monotone
   (implies (and (fn-caar-bindingp row binding old)
                 (<= (nfix old) (nfix new)))
            (fn-caar-bindingp row binding new))
   :hints (("Goal" :in-theory
            (e/d (fn-caar-bindingp fn-cp-authority-rowp fn-cp-account-creationp)
                 (fn-cp-nth fn-cp-creation-coordinate fn-auth-credp
                  fn-cai-namep fn-caar-credential-descriptor))))))

(local
 (defthm fn-caas-rows-watermark-monotone
   (implies (and (fn-caar-rowsp rows index old)
                 (<= (nfix old) (nfix new)))
            (fn-caar-rowsp rows index new))
   :hints (("Goal" :induct (fn-caar-rowsp rows index old)
            :in-theory
            (e/d (fn-caar-rowsp fn-caar-bindingp fn-cp-authority-rowp
                  fn-cp-account-creationp)
                 (fn-caas-binding-watermark-monotone fn-cp-nth
                  fn-cp-creation-coordinate fn-auth-credp fn-cai-namep
                  fn-caar-credential-descriptor fn-cai-get-is-existing-trie-get))))))

; A strictly later key cannot alter any existing row binding.
(local
 (defthm fn-caas-fresh-update-preserves-old-rows
   (implies (and (fn-caar-rowsp rows index watermark)
                 (fn-caas-names-beforep rows name)
                 (fn-cbor-octet-listp name))
            (fn-caar-rowsp rows (fn-cai-put-octets name binding index) watermark))
   :hints (("Goal" :induct (fn-caar-rowsp rows index watermark)
            :in-theory
            (e/d (fn-caar-rowsp fn-caar-bindingp fn-cai-namep fn-caas-names-beforep)
                 (fn-cp-nth fn-cp-authority-rowp fn-auth-credp
                  fn-cai-get-is-existing-trie-get fn-cai-put-is-existing-trie-put))))))

(local
 (defthm fn-caas-rowsp-head-octets
   (implies (and (fn-caar-rowsp rows index watermark) (consp rows))
            (fn-cbor-octet-listp (fn-cp-nth 1 (car rows))))
   :hints (("Goal" :in-theory
            (e/d (fn-caar-rowsp fn-caar-bindingp fn-cai-namep)
                 (fn-cp-authority-rowp fn-auth-credp fn-cp-nth
                  fn-cai-get-is-existing-trie-get))))))

(local
 (defthm fn-caas-binding-name-octets
   (implies (fn-caar-bindingp row binding watermark)
            (fn-cbor-octet-listp (fn-cp-nth 1 row)))
   :hints (("Goal" :in-theory
            (e/d (fn-caar-bindingp fn-cai-namep)
                 (fn-cp-authority-rowp fn-auth-credp fn-cp-nth))))))

(local
 (defthm fn-caas-rebuild-empty
   (implies (not (consp rows)) (equal (fn-caar-rebuild rows index acc) acc))
   :hints (("Goal" :in-theory (enable fn-caar-rebuild)))))

(local
 (defthm fn-caas-fresh-update-preserves-rebuild
   (implies (and (fn-caar-rowsp rows index watermark)
                 (fn-caas-names-beforep rows name)
                 (fn-cbor-octet-listp name))
            (equal (fn-caar-rebuild rows (fn-cai-put-octets name binding index) acc)
                   (fn-caar-rebuild rows index acc)))
   :hints (("Goal" :induct (fn-caar-rebuild rows index acc)
            :expand ((fn-caar-rebuild rows (fn-cai-put-octets name binding index) acc)
                     (fn-caar-rebuild rows index acc))
            :in-theory
            (e/d (fn-caar-rowsp fn-caas-names-beforep (:induction fn-caar-rebuild))
                 ((:definition fn-caar-rebuild) fn-caar-bindingp fn-cp-nth
                  fn-cai-get-is-existing-trie-get fn-cai-put-is-existing-trie-put))))))

(local
 (defthm fn-caas-rebuild-of-append
   (equal (fn-caar-rebuild (append xs ys) source acc)
          (fn-caar-rebuild ys source (fn-caar-rebuild xs source acc)))
   :hints (("Goal" :induct (fn-caar-rebuild xs source acc)
            :in-theory (enable fn-caar-rebuild)))))

(local
 (defthm fn-caas-rowsp-append-new-row
   (implies (and (fn-caar-rowsp rows index watermark)
                 (fn-caar-bindingp row
                   (fn-cai-get-octets (fn-cp-nth 1 row) index) watermark)
                 (fn-caas-names-beforep rows (fn-cp-nth 1 row)))
            (fn-caar-rowsp (append rows (list row)) index watermark))
   :hints (("Goal" :induct (fn-caar-rowsp rows index watermark)
            :in-theory (enable fn-caar-rowsp fn-caas-names-beforep)))))

(local
 (defthm fn-caas-rebuild-singleton
   (equal (fn-caar-rebuild (list row) source acc)
          (fn-cai-put-octets (fn-cp-nth 1 row)
                             (fn-cai-get-octets (fn-cp-nth 1 row) source) acc))
   :hints (("Goal" :in-theory (enable fn-caar-rebuild)))))

(local
 (defthm fn-caas-append-establishes-complete-index
  (implies
   (and (fn-caar-index-relp rows index old)
        (<= (nfix old) (nfix new))
        (fn-caar-bindingp row (list :account-binding row credential) new)
        (fn-caas-names-beforep rows (fn-cp-nth 1 row)))
   (fn-caar-index-relp
    (append rows (list row))
    (fn-cai-put-octets (fn-cp-nth 1 row) (list :account-binding row credential) index)
    new))
  :hints (("Goal"
           :use ((:instance fn-caas-rows-watermark-monotone)
                 (:instance fn-caas-fresh-update-preserves-old-rows
                            (watermark new) (name (fn-cp-nth 1 row))
                            (binding (list :account-binding row credential)))
                 (:instance fn-caas-fresh-update-preserves-rebuild
                            (watermark old) (name (fn-cp-nth 1 row))
                            (binding (list :account-binding row credential)) (acc nil))
                 (:instance fn-caas-rowsp-append-new-row
                            (watermark new)
                            (index (fn-cai-put-octets (fn-cp-nth 1 row)
                                   (list :account-binding row credential) index))))
           :in-theory
           (e/d (fn-caar-index-relp)
                (fn-caar-rowsp fn-caar-bindingp fn-caar-rebuild fn-caas-names-beforep
                 binary-append fn-cp-nth fn-caas-rows-watermark-monotone
                 fn-caas-fresh-update-preserves-old-rows
                 fn-caas-fresh-update-preserves-rebuild fn-caas-rowsp-append-new-row
                 fn-cai-get-is-existing-trie-get fn-cai-put-is-existing-trie-put))))))

(local
 (defthm fn-caas-last-implies-fresh-order
   (implies (and (fn-caas-last-relp reversed last)
                 (or (not last) (fn-caa-name-lessp last name)))
            (fn-caas-names-beforep reversed name))
   :hints (("Goal" :in-theory
            (enable fn-caas-last-relp fn-caas-names-beforep)))))

(local
 (defthm fn-caas-revappend-singleton
   (equal (revappend xs (list row))
          (append (revappend xs nil) (list row)))
   :hints (("Goal" :in-theory (enable revappend-removal)))))

(defthm fn-caas-begin-establishes-merge-relation
  (implies (and (natp (fn-cp-nth 2 a))
                (natp (fn-cp-nth 4 op)) (<= (fn-cp-nth 4 op) 7)
                (equal (car (fn-caa-begin s a event op)) :ok))
           (fn-caas-merge-relp
            (fn-cp-nth 5 (fn-cp-nth 6
             (fn-cp-nth 1 (fn-caa-begin s a event op))))))
  :hints (("Goal" :in-theory
           (e/d (fn-caas-merge-relp fn-caas-last-relp fn-caar-preparation-relp
                 fn-caar-root-shapep fn-caar-index-relp fn-caar-rowsp
                 fn-caar-rebuild fn-caar-credentials fn-caa-begin
                 fn-caa-preparation fn-caa-pending fn-caa-root
                 fn-caa-success fn-caa-authority-pending fn-cp-state-carry fn-cp-nth)
                (fn-caa-namespace fn-cp-authority-namespacep fn-sha256 fn-cac-encode)))))

(local
 (defthm fn-caas-binding-name-consp
   (implies (fn-caar-bindingp row binding watermark)
            (consp (fn-cp-nth 1 row)))
   :hints (("Goal" :in-theory
            (e/d (fn-caar-bindingp fn-cai-namep)
                 (fn-cp-authority-rowp fn-auth-credp fn-cp-nth))))))

(local
 (defthm fn-caas-before-empty
   (fn-caas-names-beforep nil name)
   :hints (("Goal" :in-theory (enable fn-caas-names-beforep)))))
(local
 (defthm fn-caas-before-cons
   (equal (fn-caas-names-beforep (cons row rows) name)
          (and (fn-caa-name-lessp (fn-cp-nth 1 row) name)
               (fn-caas-names-beforep rows name)))
   :hints (("Goal" :in-theory (enable fn-caas-names-beforep)))))

(defthm fn-caas-selected-stage-preserves-complete-merge
  (implies
   (and (fn-caas-merge-relp (fn-cp-nth 5 a))
        (or (not (fn-cp-nth 6 (fn-cp-nth 5 a)))
            (fn-caa-name-lessp (fn-cp-nth 6 (fn-cp-nth 5 a)) (fn-cp-nth 1 row)))
        (fn-caar-bindingp
         row (list :account-binding row credential)
         (max (nfix (fn-cp-nth 4 (fn-cp-nth 5 a)))
              (1+ (nfix (fn-cp-nth 2 event))))))
   (fn-caas-merge-relp
    (fn-cp-nth 5 (fn-cp-nth 6
     (fn-cp-nth 1 (fn-caa-stage-selected s a event row credential old-rest))))))
  :hints (("Goal"
           :use
           ((:instance fn-caas-last-implies-fresh-order
                       (reversed (fn-cp-nth 3 (fn-cp-nth 5 (fn-cp-nth 5 a))))
                       (last (fn-cp-nth 6 (fn-cp-nth 5 a))) (name (fn-cp-nth 1 row)))
            (:instance fn-caas-append-establishes-complete-index
                       (rows (revappend (fn-cp-nth 3 (fn-cp-nth 5 (fn-cp-nth 5 a))) nil))
                       (index (fn-cp-nth 2 (fn-cp-nth 5 (fn-cp-nth 5 (fn-cp-nth 5 a)))))
                       (old (fn-cp-nth 7 (fn-cp-nth 5 (fn-cp-nth 5 a))))
                       (new (max (nfix (fn-cp-nth 4 (fn-cp-nth 5 a)))
                                 (1+ (nfix (fn-cp-nth 2 event)))))))
           :in-theory
           (e/d (fn-caas-merge-relp fn-caas-last-relp fn-caar-preparation-relp
                 fn-caar-root-shapep fn-caar-credentials fn-caa-stage-selected
                 fn-caa-stage-indexed fn-caa-root fn-caa-preparation fn-caa-pending
                 fn-caa-success fn-caa-authority-pending fn-cp-state-carry fn-cp-nth
                 revappend)
                (fn-caar-index-relp fn-caar-rowsp fn-caar-bindingp
                 fn-caar-rebuild fn-caas-names-beforep fn-caa-name-lessp
                 fn-sha256 fn-cac-encode fn-cai-get-is-existing-trie-get
                 fn-cai-put-is-existing-trie-put revappend-removal
                 fn-caas-append-establishes-complete-index
                 fn-caas-binding-watermark-monotone fn-caas-last-implies-fresh-order)))))

(in-theory (disable fn-caas-names-beforep fn-caas-last-relp fn-caas-merge-relp))
