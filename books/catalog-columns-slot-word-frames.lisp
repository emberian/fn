; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-slot-escape-frames")

(local (defthm fn-lbsw-nfix-natural
 (implies (natp x) (equal (nfix x) x))
 :hints (("Goal" :in-theory (enable nfix)))))

(local (defthm fn-lbsw-len-in-bounds-update
 (implies (and (natp i) (< i (len rows))) (equal (len (update-nth i value rows)) (len rows)))
 :hints (("Goal" :induct (update-nth i value rows) :in-theory (enable update-nth len)))))

(defthm fn-lbc-word-handle-of-in-bounds-set-flags
 (implies (and (natp j) (< j (fn-lbc-count fn-lbc)))
  (equal (fn-lbc-word :handle i (update-fn-lbc-row-store
           (fn-lbc-rowwords-set-flags j flags (fn-lbc-row-store fn-lbc)) fn-lbc))
         (fn-lbc-word :handle i fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory
  (set-difference-theories (union-theories (theory 'ground-zero)
   '(fn-lbc-word-handle-by-definition fn-lbc-count fn-lbc-row-store update-fn-lbc-row-store
     fn-lbc-rowwords-count-is-len fn-lbc-rowwords-set-flags fn-lbc-rowwords$a-set-flags
     adt-set-a fn-dm-nth-update-nth fn-lbsw-len-in-bounds-update fn-lbsw-nfix-natural))
   '((:definition nfix) (tau-system))))))

(defthm fn-lbc-word-loc0-of-in-bounds-set-flags
 (implies (and (natp j) (< j (fn-lbc-count fn-lbc)))
  (equal (fn-lbc-word :loc0 i (update-fn-lbc-row-store
           (fn-lbc-rowwords-set-flags j flags (fn-lbc-row-store fn-lbc)) fn-lbc))
         (fn-lbc-word :loc0 i fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory
  (set-difference-theories (union-theories (theory 'ground-zero)
   '(fn-lbc-word-loc0-by-definition fn-lbc-count fn-lbc-row-store update-fn-lbc-row-store
     fn-lbc-rowwords-count-is-len fn-lbc-rowwords-set-flags fn-lbc-rowwords$a-set-flags
     adt-set-a fn-dm-nth-update-nth fn-lbsw-len-in-bounds-update fn-lbsw-nfix-natural))
   '((:definition nfix) (tau-system))))))

(defthm fn-lbc-word-loc1-of-in-bounds-set-flags
 (implies (and (natp j) (< j (fn-lbc-count fn-lbc)))
  (equal (fn-lbc-word :loc1 i (update-fn-lbc-row-store
           (fn-lbc-rowwords-set-flags j flags (fn-lbc-row-store fn-lbc)) fn-lbc))
         (fn-lbc-word :loc1 i fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory
  (set-difference-theories (union-theories (theory 'ground-zero)
   '(fn-lbc-word-loc1-by-definition fn-lbc-count fn-lbc-row-store update-fn-lbc-row-store
     fn-lbc-rowwords-count-is-len fn-lbc-rowwords-set-flags fn-lbc-rowwords$a-set-flags
     adt-set-a fn-dm-nth-update-nth fn-lbsw-len-in-bounds-update fn-lbsw-nfix-natural))
   '((:definition nfix) (tau-system))))))

(defthm fn-lbc-word-head-length-of-in-bounds-set-flags
 (implies (and (natp j) (< j (fn-lbc-count fn-lbc)))
  (equal (fn-lbc-word :head-length i (update-fn-lbc-row-store
           (fn-lbc-rowwords-set-flags j flags (fn-lbc-row-store fn-lbc)) fn-lbc))
         (fn-lbc-word :head-length i fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory
  (set-difference-theories (union-theories (theory 'ground-zero)
   '(fn-lbc-word-head-length-by-definition fn-lbc-count fn-lbc-row-store update-fn-lbc-row-store
     fn-lbc-rowwords-count-is-len fn-lbc-rowwords-set-flags fn-lbc-rowwords$a-set-flags
     adt-set-a fn-dm-nth-update-nth fn-lbsw-len-in-bounds-update fn-lbsw-nfix-natural))
   '((:definition nfix) (tau-system))))))

(defthm fn-lbc-word-stamp-of-in-bounds-set-flags
 (implies (and (natp j) (< j (fn-lbc-count fn-lbc)))
  (equal (fn-lbc-word :stamp i (update-fn-lbc-row-store
           (fn-lbc-rowwords-set-flags j flags (fn-lbc-row-store fn-lbc)) fn-lbc))
         (fn-lbc-word :stamp i fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory
  (set-difference-theories (union-theories (theory 'ground-zero)
   '(fn-lbc-word-stamp-by-definition fn-lbc-count fn-lbc-row-store update-fn-lbc-row-store
     fn-lbc-rowwords-count-is-len fn-lbc-rowwords-set-flags fn-lbc-rowwords$a-set-flags
     adt-set-a fn-dm-nth-update-nth fn-lbsw-len-in-bounds-update fn-lbsw-nfix-natural))
   '((:definition nfix) (tau-system))))))

(defthm fn-lbc-word-prefix-max-of-in-bounds-set-flags
 (implies (and (natp j) (< j (fn-lbc-count fn-lbc)))
  (equal (fn-lbc-word :prefix-max i (update-fn-lbc-row-store
           (fn-lbc-rowwords-set-flags j flags (fn-lbc-row-store fn-lbc)) fn-lbc))
         (fn-lbc-word :prefix-max i fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory
  (set-difference-theories (union-theories (theory 'ground-zero)
   '(fn-lbc-word-prefix-max-by-definition fn-lbc-count fn-lbc-row-store update-fn-lbc-row-store
     fn-lbc-rowwords-count-is-len fn-lbc-rowwords-set-flags fn-lbc-rowwords$a-set-flags
     adt-set-a fn-dm-nth-update-nth fn-lbsw-len-in-bounds-update fn-lbsw-nfix-natural))
   '((:definition nfix) (tau-system))))))

(defthm fn-lbc-word-txid-of-in-bounds-set-flags
 (implies (and (natp j) (< j (fn-lbc-count fn-lbc)))
  (equal (fn-lbc-word :txid i (update-fn-lbc-row-store
           (fn-lbc-rowwords-set-flags j flags (fn-lbc-row-store fn-lbc)) fn-lbc))
         (fn-lbc-word :txid i fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory
  (set-difference-theories (union-theories (theory 'ground-zero)
   '(fn-lbc-word-txid-by-definition fn-lbc-count fn-lbc-row-store update-fn-lbc-row-store
     fn-lbc-rowwords-count-is-len fn-lbc-rowwords-set-flags fn-lbc-rowwords$a-set-flags
     adt-set-a fn-dm-nth-update-nth fn-lbsw-len-in-bounds-update fn-lbsw-nfix-natural))
   '((:definition nfix) (tau-system))))))

(defthm fn-lbc-word-generation-of-in-bounds-set-flags
 (implies (and (natp j) (< j (fn-lbc-count fn-lbc)))
  (equal (fn-lbc-word :generation i (update-fn-lbc-row-store
           (fn-lbc-rowwords-set-flags j flags (fn-lbc-row-store fn-lbc)) fn-lbc))
         (fn-lbc-word :generation i fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory
  (set-difference-theories (union-theories (theory 'ground-zero)
   '(fn-lbc-word-generation-by-definition fn-lbc-count fn-lbc-row-store update-fn-lbc-row-store
     fn-lbc-rowwords-count-is-len fn-lbc-rowwords-set-flags fn-lbc-rowwords$a-set-flags
     adt-set-a fn-dm-nth-update-nth fn-lbsw-len-in-bounds-update fn-lbsw-nfix-natural))
   '((:definition nfix) (tau-system))))))

(defthm fn-lbc-word-charge-of-in-bounds-set-flags
 (implies (and (natp j) (< j (fn-lbc-count fn-lbc)))
  (equal (fn-lbc-word :charge i (update-fn-lbc-row-store
           (fn-lbc-rowwords-set-flags j flags (fn-lbc-row-store fn-lbc)) fn-lbc))
         (fn-lbc-word :charge i fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory
  (set-difference-theories (union-theories (theory 'ground-zero)
   '(fn-lbc-word-charge-by-definition fn-lbc-count fn-lbc-row-store update-fn-lbc-row-store
     fn-lbc-rowwords-count-is-len fn-lbc-rowwords-set-flags fn-lbc-rowwords$a-set-flags
     adt-set-a fn-dm-nth-update-nth fn-lbsw-len-in-bounds-update fn-lbsw-nfix-natural))
   '((:definition nfix) (tau-system))))))

(defthm fn-lbc-word-msgid-hash-of-in-bounds-set-flags
 (implies (and (natp j) (< j (fn-lbc-count fn-lbc)))
  (equal (fn-lbc-word :msgid-hash i (update-fn-lbc-row-store
           (fn-lbc-rowwords-set-flags j flags (fn-lbc-row-store fn-lbc)) fn-lbc))
         (fn-lbc-word :msgid-hash i fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory
  (set-difference-theories (union-theories (theory 'ground-zero)
   '(fn-lbc-word-msgid-hash-by-definition fn-lbc-count fn-lbc-row-store update-fn-lbc-row-store
     fn-lbc-rowwords-count-is-len fn-lbc-rowwords-set-flags fn-lbc-rowwords$a-set-flags
     adt-set-a fn-dm-nth-update-nth fn-lbsw-len-in-bounds-update fn-lbsw-nfix-natural))
   '((:definition nfix) (tau-system))))))

(defthm fn-lbc-word-msgid-offset-of-in-bounds-set-flags
 (implies (and (natp j) (< j (fn-lbc-count fn-lbc)))
  (equal (fn-lbc-word :msgid-offset i (update-fn-lbc-row-store
           (fn-lbc-rowwords-set-flags j flags (fn-lbc-row-store fn-lbc)) fn-lbc))
         (fn-lbc-word :msgid-offset i fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory
  (set-difference-theories (union-theories (theory 'ground-zero)
   '(fn-lbc-word-msgid-offset-by-definition fn-lbc-count fn-lbc-row-store update-fn-lbc-row-store
     fn-lbc-rowwords-count-is-len fn-lbc-rowwords-set-flags fn-lbc-rowwords$a-set-flags
     adt-set-a fn-dm-nth-update-nth fn-lbsw-len-in-bounds-update fn-lbsw-nfix-natural))
   '((:definition nfix) (tau-system))))))

(defthm fn-lbc-word-msgid-length-of-in-bounds-set-flags
 (implies (and (natp j) (< j (fn-lbc-count fn-lbc)))
  (equal (fn-lbc-word :msgid-length i (update-fn-lbc-row-store
           (fn-lbc-rowwords-set-flags j flags (fn-lbc-row-store fn-lbc)) fn-lbc))
         (fn-lbc-word :msgid-length i fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory
  (set-difference-theories (union-theories (theory 'ground-zero)
   '(fn-lbc-word-msgid-length-by-definition fn-lbc-count fn-lbc-row-store update-fn-lbc-row-store
     fn-lbc-rowwords-count-is-len fn-lbc-rowwords-set-flags fn-lbc-rowwords$a-set-flags
     adt-set-a fn-dm-nth-update-nth fn-lbsw-len-in-bounds-update fn-lbsw-nfix-natural))
   '((:definition nfix) (tau-system))))))

(defthm fn-lbc-word-withdrawal-at-of-in-bounds-set-flags
 (implies (and (natp j) (< j (fn-lbc-count fn-lbc)))
  (equal (fn-lbc-word :withdrawal-at i (update-fn-lbc-row-store
           (fn-lbc-rowwords-set-flags j flags (fn-lbc-row-store fn-lbc)) fn-lbc))
         (fn-lbc-word :withdrawal-at i fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory
  (set-difference-theories (union-theories (theory 'ground-zero)
   '(fn-lbc-word-withdrawal-at-by-definition fn-lbc-count fn-lbc-row-store update-fn-lbc-row-store
     fn-lbc-rowwords-count-is-len fn-lbc-rowwords-set-flags fn-lbc-rowwords$a-set-flags
     adt-set-a fn-dm-nth-update-nth fn-lbsw-len-in-bounds-update fn-lbsw-nfix-natural))
   '((:definition nfix) (tau-system))))))

(defthm fn-lbc-word-withdrawal-by-of-in-bounds-set-flags
 (implies (and (natp j) (< j (fn-lbc-count fn-lbc)))
  (equal (fn-lbc-word :withdrawal-by i (update-fn-lbc-row-store
           (fn-lbc-rowwords-set-flags j flags (fn-lbc-row-store fn-lbc)) fn-lbc))
         (fn-lbc-word :withdrawal-by i fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory
  (set-difference-theories (union-theories (theory 'ground-zero)
   '(fn-lbc-word-withdrawal-by-by-definition fn-lbc-count fn-lbc-row-store update-fn-lbc-row-store
     fn-lbc-rowwords-count-is-len fn-lbc-rowwords-set-flags fn-lbc-rowwords$a-set-flags
     adt-set-a fn-dm-nth-update-nth fn-lbsw-len-in-bounds-update fn-lbsw-nfix-natural))
   '((:definition nfix) (tau-system))))))

(defthm fn-lbc-word-overview-offset-of-in-bounds-set-flags
 (implies (and (natp j) (< j (fn-lbc-count fn-lbc)))
  (equal (fn-lbc-word :overview-offset i (update-fn-lbc-row-store
           (fn-lbc-rowwords-set-flags j flags (fn-lbc-row-store fn-lbc)) fn-lbc))
         (fn-lbc-word :overview-offset i fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory
  (set-difference-theories (union-theories (theory 'ground-zero)
   '(fn-lbc-word-overview-offset-by-definition fn-lbc-count fn-lbc-row-store update-fn-lbc-row-store
     fn-lbc-rowwords-count-is-len fn-lbc-rowwords-set-flags fn-lbc-rowwords$a-set-flags
     adt-set-a fn-dm-nth-update-nth fn-lbsw-len-in-bounds-update fn-lbsw-nfix-natural))
   '((:definition nfix) (tau-system))))))

(defthm fn-lbc-word-of-in-bounds-set-flags-other-field
 (implies (and (natp j) (< j (fn-lbc-count fn-lbc)) (not (equal field :flags)))
  (equal (fn-lbc-word field i (update-fn-lbc-row-store
           (fn-lbc-rowwords-set-flags j flags (fn-lbc-row-store fn-lbc)) fn-lbc))
         (fn-lbc-word field i fn-lbc)))
 :hints (("Goal" :do-not-induct t :cases ((equal field :handle) (equal field :loc0) (equal field :loc1) (equal field :head-length) (equal field :stamp) (equal field :prefix-max) (equal field :txid) (equal field :generation) (equal field :charge) (equal field :msgid-hash) (equal field :msgid-offset) (equal field :msgid-length) (equal field :withdrawal-at) (equal field :withdrawal-by) (equal field :overview-offset))
  :use ((:instance fn-lbc-word-handle-of-in-bounds-set-flags) (:instance fn-lbc-word-loc0-of-in-bounds-set-flags) (:instance fn-lbc-word-loc1-of-in-bounds-set-flags) (:instance fn-lbc-word-head-length-of-in-bounds-set-flags) (:instance fn-lbc-word-stamp-of-in-bounds-set-flags) (:instance fn-lbc-word-prefix-max-of-in-bounds-set-flags) (:instance fn-lbc-word-txid-of-in-bounds-set-flags) (:instance fn-lbc-word-generation-of-in-bounds-set-flags) (:instance fn-lbc-word-charge-of-in-bounds-set-flags) (:instance fn-lbc-word-msgid-hash-of-in-bounds-set-flags) (:instance fn-lbc-word-msgid-offset-of-in-bounds-set-flags) (:instance fn-lbc-word-msgid-length-of-in-bounds-set-flags) (:instance fn-lbc-word-withdrawal-at-of-in-bounds-set-flags) (:instance fn-lbc-word-withdrawal-by-of-in-bounds-set-flags) (:instance fn-lbc-word-overview-offset-of-in-bounds-set-flags)) :in-theory (union-theories (theory 'minimal-theory)
   '(fn-lbc-word (:executable-counterpart equal))))))
