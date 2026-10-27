; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-row-write-composition")

(local (defthm fn-lbridx-row-setter-is-update-nth
 (equal (update-fn-lbc-row-store value fn-lbc) (update-nth 0 value fn-lbc))
 :hints (("Goal" :in-theory (enable update-fn-lbc-row-store update-nth)))))

(defthm fn-lbc-nth-of-other-row-store-update-by-definition
 (implies (and (natp k) (not (equal k 0)))
  (equal (nth k (update-fn-lbc-row-store value fn-lbc)) (nth k fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory
  (set-difference-theories (union-theories (theory 'ground-zero)
    '(fn-lbridx-row-setter-is-update-nth fn-dm-nth-update-nth)) '(update-nth)))))

(local (defthm fn-lbridx-directory-setter-is-update-nth
 (equal (update-fn-lbc-directory-store value fn-lbc) (update-nth 5 value fn-lbc))
 :hints (("Goal" :in-theory (enable update-fn-lbc-directory-store update-nth)))))

(defthm fn-lbc-nth-of-other-directory-store-update-by-definition
 (implies (and (natp k) (not (equal k 5)))
  (equal (nth k (update-fn-lbc-directory-store value fn-lbc)) (nth k fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory
  (set-difference-theories (union-theories (theory 'ground-zero)
    '(fn-lbridx-directory-setter-is-update-nth fn-dm-nth-update-nth)) '(update-nth)))))

(defthm fn-lbc-word-handle-of-store-append-at-index
 (implies (equal i (fn-lbc-count fn-lbc))
  (equal (fn-lbc-word :handle i (update-fn-lbc-row-store (fn-lbc-rowwords-append record (fn-lbc-row-store fn-lbc)) fn-lbc)) (nth 0 record)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-word-handle-of-store-append-new))
  :in-theory (theory 'minimal-theory))))

(defthm fn-lbc-word-loc0-of-store-append-at-index
 (implies (equal i (fn-lbc-count fn-lbc))
  (equal (fn-lbc-word :loc0 i (update-fn-lbc-row-store (fn-lbc-rowwords-append record (fn-lbc-row-store fn-lbc)) fn-lbc)) (nth 1 record)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-word-loc0-of-store-append-new))
  :in-theory (theory 'minimal-theory))))

(defthm fn-lbc-word-loc1-of-store-append-at-index
 (implies (equal i (fn-lbc-count fn-lbc))
  (equal (fn-lbc-word :loc1 i (update-fn-lbc-row-store (fn-lbc-rowwords-append record (fn-lbc-row-store fn-lbc)) fn-lbc)) (nth 2 record)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-word-loc1-of-store-append-new))
  :in-theory (theory 'minimal-theory))))

(defthm fn-lbc-word-head-length-of-store-append-at-index
 (implies (equal i (fn-lbc-count fn-lbc))
  (equal (fn-lbc-word :head-length i (update-fn-lbc-row-store (fn-lbc-rowwords-append record (fn-lbc-row-store fn-lbc)) fn-lbc)) (nth 3 record)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-word-head-length-of-store-append-new))
  :in-theory (theory 'minimal-theory))))

(defthm fn-lbc-word-stamp-of-store-append-at-index
 (implies (equal i (fn-lbc-count fn-lbc))
  (equal (fn-lbc-word :stamp i (update-fn-lbc-row-store (fn-lbc-rowwords-append record (fn-lbc-row-store fn-lbc)) fn-lbc)) (nth 4 record)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-word-stamp-of-store-append-new))
  :in-theory (theory 'minimal-theory))))

(defthm fn-lbc-word-prefix-max-of-store-append-at-index
 (implies (equal i (fn-lbc-count fn-lbc))
  (equal (fn-lbc-word :prefix-max i (update-fn-lbc-row-store (fn-lbc-rowwords-append record (fn-lbc-row-store fn-lbc)) fn-lbc)) (nth 5 record)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-word-prefix-max-of-store-append-new))
  :in-theory (theory 'minimal-theory))))

(defthm fn-lbc-word-txid-of-store-append-at-index
 (implies (equal i (fn-lbc-count fn-lbc))
  (equal (fn-lbc-word :txid i (update-fn-lbc-row-store (fn-lbc-rowwords-append record (fn-lbc-row-store fn-lbc)) fn-lbc)) (nth 6 record)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-word-txid-of-store-append-new))
  :in-theory (theory 'minimal-theory))))

(defthm fn-lbc-word-generation-of-store-append-at-index
 (implies (equal i (fn-lbc-count fn-lbc))
  (equal (fn-lbc-word :generation i (update-fn-lbc-row-store (fn-lbc-rowwords-append record (fn-lbc-row-store fn-lbc)) fn-lbc)) (nth 7 record)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-word-generation-of-store-append-new))
  :in-theory (theory 'minimal-theory))))

(defthm fn-lbc-word-charge-of-store-append-at-index
 (implies (equal i (fn-lbc-count fn-lbc))
  (equal (fn-lbc-word :charge i (update-fn-lbc-row-store (fn-lbc-rowwords-append record (fn-lbc-row-store fn-lbc)) fn-lbc)) (nth 8 record)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-word-charge-of-store-append-new))
  :in-theory (theory 'minimal-theory))))

(defthm fn-lbc-word-msgid-hash-of-store-append-at-index
 (implies (equal i (fn-lbc-count fn-lbc))
  (equal (fn-lbc-word :msgid-hash i (update-fn-lbc-row-store (fn-lbc-rowwords-append record (fn-lbc-row-store fn-lbc)) fn-lbc)) (nth 9 record)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-word-msgid-hash-of-store-append-new))
  :in-theory (theory 'minimal-theory))))

(defthm fn-lbc-word-msgid-offset-of-store-append-at-index
 (implies (equal i (fn-lbc-count fn-lbc))
  (equal (fn-lbc-word :msgid-offset i (update-fn-lbc-row-store (fn-lbc-rowwords-append record (fn-lbc-row-store fn-lbc)) fn-lbc)) (nth 10 record)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-word-msgid-offset-of-store-append-new))
  :in-theory (theory 'minimal-theory))))

(defthm fn-lbc-word-msgid-length-of-store-append-at-index
 (implies (equal i (fn-lbc-count fn-lbc))
  (equal (fn-lbc-word :msgid-length i (update-fn-lbc-row-store (fn-lbc-rowwords-append record (fn-lbc-row-store fn-lbc)) fn-lbc)) (nth 11 record)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-word-msgid-length-of-store-append-new))
  :in-theory (theory 'minimal-theory))))

(defthm fn-lbc-word-withdrawal-at-of-store-append-at-index
 (implies (equal i (fn-lbc-count fn-lbc))
  (equal (fn-lbc-word :withdrawal-at i (update-fn-lbc-row-store (fn-lbc-rowwords-append record (fn-lbc-row-store fn-lbc)) fn-lbc)) (nth 12 record)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-word-withdrawal-at-of-store-append-new))
  :in-theory (theory 'minimal-theory))))

(defthm fn-lbc-word-withdrawal-by-of-store-append-at-index
 (implies (equal i (fn-lbc-count fn-lbc))
  (equal (fn-lbc-word :withdrawal-by i (update-fn-lbc-row-store (fn-lbc-rowwords-append record (fn-lbc-row-store fn-lbc)) fn-lbc)) (nth 13 record)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-word-withdrawal-by-of-store-append-new))
  :in-theory (theory 'minimal-theory))))

(defthm fn-lbc-word-overview-offset-of-store-append-at-index
 (implies (equal i (fn-lbc-count fn-lbc))
  (equal (fn-lbc-word :overview-offset i (update-fn-lbc-row-store (fn-lbc-rowwords-append record (fn-lbc-row-store fn-lbc)) fn-lbc)) (nth 14 record)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-word-overview-offset-of-store-append-new))
  :in-theory (theory 'minimal-theory))))

(defthm fn-lbc-word-flags-of-store-append-at-index
 (implies (equal i (fn-lbc-count fn-lbc))
  (equal (fn-lbc-word :flags i (update-fn-lbc-row-store (fn-lbc-rowwords-append record (fn-lbc-row-store fn-lbc)) fn-lbc)) (nth 15 record)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-word-flags-of-store-append-new))
  :in-theory (theory 'minimal-theory))))

(defthm fn-lbc-directory-field-sequence-of-store-append-at-index
 (implies (equal i (len (nth *fn-lbc-directory-store* fn-lbc)))
  (equal (fn-lbc-directory-field :sequence i (update-fn-lbc-directory-store (fn-lbc-directory-append record (fn-lbc-directory-store fn-lbc)) fn-lbc)) (nth 0 record)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-directory-field-sequence-of-store-append-new))
  :in-theory (theory 'minimal-theory))))

(defthm fn-lbc-directory-field-facts-octets-of-store-append-at-index
 (implies (equal i (len (nth *fn-lbc-directory-store* fn-lbc)))
  (equal (fn-lbc-directory-field :facts-octets i (update-fn-lbc-directory-store (fn-lbc-directory-append record (fn-lbc-directory-store fn-lbc)) fn-lbc)) (nth 1 record)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-directory-field-facts-octets-of-store-append-new))
  :in-theory (theory 'minimal-theory))))

(defthm fn-lbc-directory-field-body-start-of-store-append-at-index
 (implies (equal i (len (nth *fn-lbc-directory-store* fn-lbc)))
  (equal (fn-lbc-directory-field :body-start i (update-fn-lbc-directory-store (fn-lbc-directory-append record (fn-lbc-directory-store fn-lbc)) fn-lbc)) (nth 2 record)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-directory-field-body-start-of-store-append-new))
  :in-theory (theory 'minimal-theory))))

(defthm fn-lbc-directory-field-body-start-present-of-store-append-at-index
 (implies (equal i (len (nth *fn-lbc-directory-store* fn-lbc)))
  (equal (fn-lbc-directory-field :body-start-present i (update-fn-lbc-directory-store (fn-lbc-directory-append record (fn-lbc-directory-store fn-lbc)) fn-lbc)) (nth 3 record)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-directory-field-body-start-present-of-store-append-new))
  :in-theory (theory 'minimal-theory))))

(defthm fn-lbc-directory-field-body-lines-of-store-append-at-index
 (implies (equal i (len (nth *fn-lbc-directory-store* fn-lbc)))
  (equal (fn-lbc-directory-field :body-lines i (update-fn-lbc-directory-store (fn-lbc-directory-append record (fn-lbc-directory-store fn-lbc)) fn-lbc)) (nth 4 record)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-directory-field-body-lines-of-store-append-new))
  :in-theory (theory 'minimal-theory))))

(defthm fn-lbc-directory-field-nov-start-of-store-append-at-index
 (implies (equal i (len (nth *fn-lbc-directory-store* fn-lbc)))
  (equal (fn-lbc-directory-field :nov-start i (update-fn-lbc-directory-store (fn-lbc-directory-append record (fn-lbc-directory-store fn-lbc)) fn-lbc)) (nth 5 record)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-directory-field-nov-start-of-store-append-new))
  :in-theory (theory 'minimal-theory))))

(defthm fn-lbc-directory-field-nov-length-of-store-append-at-index
 (implies (equal i (len (nth *fn-lbc-directory-store* fn-lbc)))
  (equal (fn-lbc-directory-field :nov-length i (update-fn-lbc-directory-store (fn-lbc-directory-append record (fn-lbc-directory-store fn-lbc)) fn-lbc)) (nth 6 record)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-directory-field-nov-length-of-store-append-new))
  :in-theory (theory 'minimal-theory))))

(defthm fn-lbc-directory-field-render-nov-start-of-store-append-at-index
 (implies (equal i (len (nth *fn-lbc-directory-store* fn-lbc)))
  (equal (fn-lbc-directory-field :render-nov-start i (update-fn-lbc-directory-store (fn-lbc-directory-append record (fn-lbc-directory-store fn-lbc)) fn-lbc)) (nth 7 record)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-directory-field-render-nov-start-of-store-append-new))
  :in-theory (theory 'minimal-theory))))

(defthm fn-lbc-directory-field-render-nov-length-of-store-append-at-index
 (implies (equal i (len (nth *fn-lbc-directory-store* fn-lbc)))
  (equal (fn-lbc-directory-field :render-nov-length i (update-fn-lbc-directory-store (fn-lbc-directory-append record (fn-lbc-directory-store fn-lbc)) fn-lbc)) (nth 8 record)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-directory-field-render-nov-length-of-store-append-new))
  :in-theory (theory 'minimal-theory))))

(defthm fn-lbc-directory-field-groups-start-of-store-append-at-index
 (implies (equal i (len (nth *fn-lbc-directory-store* fn-lbc)))
  (equal (fn-lbc-directory-field :groups-start i (update-fn-lbc-directory-store (fn-lbc-directory-append record (fn-lbc-directory-store fn-lbc)) fn-lbc)) (nth 9 record)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-directory-field-groups-start-of-store-append-new))
  :in-theory (theory 'minimal-theory))))

(defthm fn-lbc-directory-field-groups-count-of-store-append-at-index
 (implies (equal i (len (nth *fn-lbc-directory-store* fn-lbc)))
  (equal (fn-lbc-directory-field :groups-count i (update-fn-lbc-directory-store (fn-lbc-directory-append record (fn-lbc-directory-store fn-lbc)) fn-lbc)) (nth 10 record)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-directory-field-groups-count-of-store-append-new))
  :in-theory (theory 'minimal-theory))))

(defthm fn-lbc-directory-field-numbers-start-of-store-append-at-index
 (implies (equal i (len (nth *fn-lbc-directory-store* fn-lbc)))
  (equal (fn-lbc-directory-field :numbers-start i (update-fn-lbc-directory-store (fn-lbc-directory-append record (fn-lbc-directory-store fn-lbc)) fn-lbc)) (nth 11 record)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-directory-field-numbers-start-of-store-append-new))
  :in-theory (theory 'minimal-theory))))

(defthm fn-lbc-directory-field-numbers-count-of-store-append-at-index
 (implies (equal i (len (nth *fn-lbc-directory-store* fn-lbc)))
  (equal (fn-lbc-directory-field :numbers-count i (update-fn-lbc-directory-store (fn-lbc-directory-append record (fn-lbc-directory-store fn-lbc)) fn-lbc)) (nth 12 record)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-directory-field-numbers-count-of-store-append-new))
  :in-theory (theory 'minimal-theory))))

(defthm fn-lbc-directory-field-article-ok-of-store-append-at-index
 (implies (equal i (len (nth *fn-lbc-directory-store* fn-lbc)))
  (equal (fn-lbc-directory-field :article-ok i (update-fn-lbc-directory-store (fn-lbc-directory-append record (fn-lbc-directory-store fn-lbc)) fn-lbc)) (nth 13 record)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-directory-field-article-ok-of-store-append-new))
  :in-theory (theory 'minimal-theory))))

(defthm fn-lbc-directory-field-head-ok-of-store-append-at-index
 (implies (equal i (len (nth *fn-lbc-directory-store* fn-lbc)))
  (equal (fn-lbc-directory-field :head-ok i (update-fn-lbc-directory-store (fn-lbc-directory-append record (fn-lbc-directory-store fn-lbc)) fn-lbc)) (nth 14 record)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-directory-field-head-ok-of-store-append-new))
  :in-theory (theory 'minimal-theory))))

(defthm fn-lbc-directory-field-body-ok-of-store-append-at-index
 (implies (equal i (len (nth *fn-lbc-directory-store* fn-lbc)))
  (equal (fn-lbc-directory-field :body-ok i (update-fn-lbc-directory-store (fn-lbc-directory-append record (fn-lbc-directory-store fn-lbc)) fn-lbc)) (nth 15 record)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-directory-field-body-ok-of-store-append-new))
  :in-theory (theory 'minimal-theory))))

(defthm fn-lbc-directory-field-raw-head-length-of-store-append-at-index
 (implies (equal i (len (nth *fn-lbc-directory-store* fn-lbc)))
  (equal (fn-lbc-directory-field :raw-head-length i (update-fn-lbc-directory-store (fn-lbc-directory-append record (fn-lbc-directory-store fn-lbc)) fn-lbc)) (nth 16 record)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-directory-field-raw-head-length-of-store-append-new))
  :in-theory (theory 'minimal-theory))))

(defthm fn-lbc-directory-field-framed-of-store-append-at-index
 (implies (equal i (len (nth *fn-lbc-directory-store* fn-lbc)))
  (equal (fn-lbc-directory-field :framed i (update-fn-lbc-directory-store (fn-lbc-directory-append record (fn-lbc-directory-store fn-lbc)) fn-lbc)) (nth 17 record)))
 :hints (("Goal" :do-not-induct t
  :use ((:instance fn-lbc-directory-field-framed-of-store-append-new))
  :in-theory (theory 'minimal-theory))))
