; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-row-reader-frames")

(local (defthm fn-lbrse-count-by-store
 (equal (fn-lbc-count fn-lbc) (len (nth *fn-lbc-row-store* fn-lbc)))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
  '(fn-lbc-count fn-lbc-row-store fn-lbc-rowwords-count-is-len))))))

(local (defthm fn-lbrse-len-append-one
 (equal (len (append xs (list x))) (+ 1 (len xs)))
 :hints (("Goal" :induct (len xs) :in-theory (enable binary-append len)))))

(local (defthm fn-lbrse-nth-append-at-length
 (equal (nth (len xs) (append xs (list x))) x)
 :hints (("Goal" :induct (len xs) :in-theory (enable binary-append len nth)))))

(local (defthm fn-lbrse-nth-append-prefix
 (implies (and (natp i) (< i (len xs)))
  (equal (nth i (append xs ys)) (nth i xs)))
 :hints (("Goal" :induct (nth i xs) :in-theory (enable binary-append len nth)))))

(defthm fn-lbc-word-handle-of-store-append-new
 (equal (fn-lbc-word :handle (fn-lbc-count fn-lbc) (update-fn-lbc-row-store (fn-lbc-rowwords-append record (fn-lbc-row-store fn-lbc)) fn-lbc)) (nth 0 record))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-word-handle-by-definition update-fn-lbc-row-store fn-lbc-row-store fn-lbc-rowwords-append-is-append fn-dm-nth-update-nth fn-lbrse-count-by-store fn-lbrse-len-append-one fn-lbrse-nth-append-at-length fn-lbrse-nth-append-prefix nth)))))

(defthm fn-lbc-word-handle-of-store-append-old
 (implies (and (natp i) (< i (fn-lbc-count fn-lbc)))
  (equal (fn-lbc-word :handle i (update-fn-lbc-row-store (fn-lbc-rowwords-append record (fn-lbc-row-store fn-lbc)) fn-lbc)) (fn-lbc-word :handle i fn-lbc)))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-word-handle-by-definition update-fn-lbc-row-store fn-lbc-row-store fn-lbc-rowwords-append-is-append fn-dm-nth-update-nth fn-lbrse-count-by-store fn-lbrse-len-append-one fn-lbrse-nth-append-at-length fn-lbrse-nth-append-prefix nth)))))

(defthm fn-lbc-word-loc0-of-store-append-new
 (equal (fn-lbc-word :loc0 (fn-lbc-count fn-lbc) (update-fn-lbc-row-store (fn-lbc-rowwords-append record (fn-lbc-row-store fn-lbc)) fn-lbc)) (nth 1 record))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-word-loc0-by-definition update-fn-lbc-row-store fn-lbc-row-store fn-lbc-rowwords-append-is-append fn-dm-nth-update-nth fn-lbrse-count-by-store fn-lbrse-len-append-one fn-lbrse-nth-append-at-length fn-lbrse-nth-append-prefix nth)))))

(defthm fn-lbc-word-loc0-of-store-append-old
 (implies (and (natp i) (< i (fn-lbc-count fn-lbc)))
  (equal (fn-lbc-word :loc0 i (update-fn-lbc-row-store (fn-lbc-rowwords-append record (fn-lbc-row-store fn-lbc)) fn-lbc)) (fn-lbc-word :loc0 i fn-lbc)))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-word-loc0-by-definition update-fn-lbc-row-store fn-lbc-row-store fn-lbc-rowwords-append-is-append fn-dm-nth-update-nth fn-lbrse-count-by-store fn-lbrse-len-append-one fn-lbrse-nth-append-at-length fn-lbrse-nth-append-prefix nth)))))

(defthm fn-lbc-word-loc1-of-store-append-new
 (equal (fn-lbc-word :loc1 (fn-lbc-count fn-lbc) (update-fn-lbc-row-store (fn-lbc-rowwords-append record (fn-lbc-row-store fn-lbc)) fn-lbc)) (nth 2 record))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-word-loc1-by-definition update-fn-lbc-row-store fn-lbc-row-store fn-lbc-rowwords-append-is-append fn-dm-nth-update-nth fn-lbrse-count-by-store fn-lbrse-len-append-one fn-lbrse-nth-append-at-length fn-lbrse-nth-append-prefix nth)))))

(defthm fn-lbc-word-loc1-of-store-append-old
 (implies (and (natp i) (< i (fn-lbc-count fn-lbc)))
  (equal (fn-lbc-word :loc1 i (update-fn-lbc-row-store (fn-lbc-rowwords-append record (fn-lbc-row-store fn-lbc)) fn-lbc)) (fn-lbc-word :loc1 i fn-lbc)))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-word-loc1-by-definition update-fn-lbc-row-store fn-lbc-row-store fn-lbc-rowwords-append-is-append fn-dm-nth-update-nth fn-lbrse-count-by-store fn-lbrse-len-append-one fn-lbrse-nth-append-at-length fn-lbrse-nth-append-prefix nth)))))

(defthm fn-lbc-word-head-length-of-store-append-new
 (equal (fn-lbc-word :head-length (fn-lbc-count fn-lbc) (update-fn-lbc-row-store (fn-lbc-rowwords-append record (fn-lbc-row-store fn-lbc)) fn-lbc)) (nth 3 record))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-word-head-length-by-definition update-fn-lbc-row-store fn-lbc-row-store fn-lbc-rowwords-append-is-append fn-dm-nth-update-nth fn-lbrse-count-by-store fn-lbrse-len-append-one fn-lbrse-nth-append-at-length fn-lbrse-nth-append-prefix nth)))))

(defthm fn-lbc-word-head-length-of-store-append-old
 (implies (and (natp i) (< i (fn-lbc-count fn-lbc)))
  (equal (fn-lbc-word :head-length i (update-fn-lbc-row-store (fn-lbc-rowwords-append record (fn-lbc-row-store fn-lbc)) fn-lbc)) (fn-lbc-word :head-length i fn-lbc)))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-word-head-length-by-definition update-fn-lbc-row-store fn-lbc-row-store fn-lbc-rowwords-append-is-append fn-dm-nth-update-nth fn-lbrse-count-by-store fn-lbrse-len-append-one fn-lbrse-nth-append-at-length fn-lbrse-nth-append-prefix nth)))))

(defthm fn-lbc-word-stamp-of-store-append-new
 (equal (fn-lbc-word :stamp (fn-lbc-count fn-lbc) (update-fn-lbc-row-store (fn-lbc-rowwords-append record (fn-lbc-row-store fn-lbc)) fn-lbc)) (nth 4 record))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-word-stamp-by-definition update-fn-lbc-row-store fn-lbc-row-store fn-lbc-rowwords-append-is-append fn-dm-nth-update-nth fn-lbrse-count-by-store fn-lbrse-len-append-one fn-lbrse-nth-append-at-length fn-lbrse-nth-append-prefix nth)))))

(defthm fn-lbc-word-stamp-of-store-append-old
 (implies (and (natp i) (< i (fn-lbc-count fn-lbc)))
  (equal (fn-lbc-word :stamp i (update-fn-lbc-row-store (fn-lbc-rowwords-append record (fn-lbc-row-store fn-lbc)) fn-lbc)) (fn-lbc-word :stamp i fn-lbc)))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-word-stamp-by-definition update-fn-lbc-row-store fn-lbc-row-store fn-lbc-rowwords-append-is-append fn-dm-nth-update-nth fn-lbrse-count-by-store fn-lbrse-len-append-one fn-lbrse-nth-append-at-length fn-lbrse-nth-append-prefix nth)))))

(defthm fn-lbc-word-prefix-max-of-store-append-new
 (equal (fn-lbc-word :prefix-max (fn-lbc-count fn-lbc) (update-fn-lbc-row-store (fn-lbc-rowwords-append record (fn-lbc-row-store fn-lbc)) fn-lbc)) (nth 5 record))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-word-prefix-max-by-definition update-fn-lbc-row-store fn-lbc-row-store fn-lbc-rowwords-append-is-append fn-dm-nth-update-nth fn-lbrse-count-by-store fn-lbrse-len-append-one fn-lbrse-nth-append-at-length fn-lbrse-nth-append-prefix nth)))))

(defthm fn-lbc-word-prefix-max-of-store-append-old
 (implies (and (natp i) (< i (fn-lbc-count fn-lbc)))
  (equal (fn-lbc-word :prefix-max i (update-fn-lbc-row-store (fn-lbc-rowwords-append record (fn-lbc-row-store fn-lbc)) fn-lbc)) (fn-lbc-word :prefix-max i fn-lbc)))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-word-prefix-max-by-definition update-fn-lbc-row-store fn-lbc-row-store fn-lbc-rowwords-append-is-append fn-dm-nth-update-nth fn-lbrse-count-by-store fn-lbrse-len-append-one fn-lbrse-nth-append-at-length fn-lbrse-nth-append-prefix nth)))))

(defthm fn-lbc-word-txid-of-store-append-new
 (equal (fn-lbc-word :txid (fn-lbc-count fn-lbc) (update-fn-lbc-row-store (fn-lbc-rowwords-append record (fn-lbc-row-store fn-lbc)) fn-lbc)) (nth 6 record))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-word-txid-by-definition update-fn-lbc-row-store fn-lbc-row-store fn-lbc-rowwords-append-is-append fn-dm-nth-update-nth fn-lbrse-count-by-store fn-lbrse-len-append-one fn-lbrse-nth-append-at-length fn-lbrse-nth-append-prefix nth)))))

(defthm fn-lbc-word-txid-of-store-append-old
 (implies (and (natp i) (< i (fn-lbc-count fn-lbc)))
  (equal (fn-lbc-word :txid i (update-fn-lbc-row-store (fn-lbc-rowwords-append record (fn-lbc-row-store fn-lbc)) fn-lbc)) (fn-lbc-word :txid i fn-lbc)))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-word-txid-by-definition update-fn-lbc-row-store fn-lbc-row-store fn-lbc-rowwords-append-is-append fn-dm-nth-update-nth fn-lbrse-count-by-store fn-lbrse-len-append-one fn-lbrse-nth-append-at-length fn-lbrse-nth-append-prefix nth)))))

(defthm fn-lbc-word-generation-of-store-append-new
 (equal (fn-lbc-word :generation (fn-lbc-count fn-lbc) (update-fn-lbc-row-store (fn-lbc-rowwords-append record (fn-lbc-row-store fn-lbc)) fn-lbc)) (nth 7 record))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-word-generation-by-definition update-fn-lbc-row-store fn-lbc-row-store fn-lbc-rowwords-append-is-append fn-dm-nth-update-nth fn-lbrse-count-by-store fn-lbrse-len-append-one fn-lbrse-nth-append-at-length fn-lbrse-nth-append-prefix nth)))))

(defthm fn-lbc-word-generation-of-store-append-old
 (implies (and (natp i) (< i (fn-lbc-count fn-lbc)))
  (equal (fn-lbc-word :generation i (update-fn-lbc-row-store (fn-lbc-rowwords-append record (fn-lbc-row-store fn-lbc)) fn-lbc)) (fn-lbc-word :generation i fn-lbc)))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-word-generation-by-definition update-fn-lbc-row-store fn-lbc-row-store fn-lbc-rowwords-append-is-append fn-dm-nth-update-nth fn-lbrse-count-by-store fn-lbrse-len-append-one fn-lbrse-nth-append-at-length fn-lbrse-nth-append-prefix nth)))))

(defthm fn-lbc-word-charge-of-store-append-new
 (equal (fn-lbc-word :charge (fn-lbc-count fn-lbc) (update-fn-lbc-row-store (fn-lbc-rowwords-append record (fn-lbc-row-store fn-lbc)) fn-lbc)) (nth 8 record))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-word-charge-by-definition update-fn-lbc-row-store fn-lbc-row-store fn-lbc-rowwords-append-is-append fn-dm-nth-update-nth fn-lbrse-count-by-store fn-lbrse-len-append-one fn-lbrse-nth-append-at-length fn-lbrse-nth-append-prefix nth)))))

(defthm fn-lbc-word-charge-of-store-append-old
 (implies (and (natp i) (< i (fn-lbc-count fn-lbc)))
  (equal (fn-lbc-word :charge i (update-fn-lbc-row-store (fn-lbc-rowwords-append record (fn-lbc-row-store fn-lbc)) fn-lbc)) (fn-lbc-word :charge i fn-lbc)))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-word-charge-by-definition update-fn-lbc-row-store fn-lbc-row-store fn-lbc-rowwords-append-is-append fn-dm-nth-update-nth fn-lbrse-count-by-store fn-lbrse-len-append-one fn-lbrse-nth-append-at-length fn-lbrse-nth-append-prefix nth)))))

(defthm fn-lbc-word-msgid-hash-of-store-append-new
 (equal (fn-lbc-word :msgid-hash (fn-lbc-count fn-lbc) (update-fn-lbc-row-store (fn-lbc-rowwords-append record (fn-lbc-row-store fn-lbc)) fn-lbc)) (nth 9 record))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-word-msgid-hash-by-definition update-fn-lbc-row-store fn-lbc-row-store fn-lbc-rowwords-append-is-append fn-dm-nth-update-nth fn-lbrse-count-by-store fn-lbrse-len-append-one fn-lbrse-nth-append-at-length fn-lbrse-nth-append-prefix nth)))))

(defthm fn-lbc-word-msgid-hash-of-store-append-old
 (implies (and (natp i) (< i (fn-lbc-count fn-lbc)))
  (equal (fn-lbc-word :msgid-hash i (update-fn-lbc-row-store (fn-lbc-rowwords-append record (fn-lbc-row-store fn-lbc)) fn-lbc)) (fn-lbc-word :msgid-hash i fn-lbc)))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-word-msgid-hash-by-definition update-fn-lbc-row-store fn-lbc-row-store fn-lbc-rowwords-append-is-append fn-dm-nth-update-nth fn-lbrse-count-by-store fn-lbrse-len-append-one fn-lbrse-nth-append-at-length fn-lbrse-nth-append-prefix nth)))))

(defthm fn-lbc-word-msgid-offset-of-store-append-new
 (equal (fn-lbc-word :msgid-offset (fn-lbc-count fn-lbc) (update-fn-lbc-row-store (fn-lbc-rowwords-append record (fn-lbc-row-store fn-lbc)) fn-lbc)) (nth 10 record))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-word-msgid-offset-by-definition update-fn-lbc-row-store fn-lbc-row-store fn-lbc-rowwords-append-is-append fn-dm-nth-update-nth fn-lbrse-count-by-store fn-lbrse-len-append-one fn-lbrse-nth-append-at-length fn-lbrse-nth-append-prefix nth)))))

(defthm fn-lbc-word-msgid-offset-of-store-append-old
 (implies (and (natp i) (< i (fn-lbc-count fn-lbc)))
  (equal (fn-lbc-word :msgid-offset i (update-fn-lbc-row-store (fn-lbc-rowwords-append record (fn-lbc-row-store fn-lbc)) fn-lbc)) (fn-lbc-word :msgid-offset i fn-lbc)))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-word-msgid-offset-by-definition update-fn-lbc-row-store fn-lbc-row-store fn-lbc-rowwords-append-is-append fn-dm-nth-update-nth fn-lbrse-count-by-store fn-lbrse-len-append-one fn-lbrse-nth-append-at-length fn-lbrse-nth-append-prefix nth)))))

(defthm fn-lbc-word-msgid-length-of-store-append-new
 (equal (fn-lbc-word :msgid-length (fn-lbc-count fn-lbc) (update-fn-lbc-row-store (fn-lbc-rowwords-append record (fn-lbc-row-store fn-lbc)) fn-lbc)) (nth 11 record))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-word-msgid-length-by-definition update-fn-lbc-row-store fn-lbc-row-store fn-lbc-rowwords-append-is-append fn-dm-nth-update-nth fn-lbrse-count-by-store fn-lbrse-len-append-one fn-lbrse-nth-append-at-length fn-lbrse-nth-append-prefix nth)))))

(defthm fn-lbc-word-msgid-length-of-store-append-old
 (implies (and (natp i) (< i (fn-lbc-count fn-lbc)))
  (equal (fn-lbc-word :msgid-length i (update-fn-lbc-row-store (fn-lbc-rowwords-append record (fn-lbc-row-store fn-lbc)) fn-lbc)) (fn-lbc-word :msgid-length i fn-lbc)))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-word-msgid-length-by-definition update-fn-lbc-row-store fn-lbc-row-store fn-lbc-rowwords-append-is-append fn-dm-nth-update-nth fn-lbrse-count-by-store fn-lbrse-len-append-one fn-lbrse-nth-append-at-length fn-lbrse-nth-append-prefix nth)))))

(defthm fn-lbc-word-withdrawal-at-of-store-append-new
 (equal (fn-lbc-word :withdrawal-at (fn-lbc-count fn-lbc) (update-fn-lbc-row-store (fn-lbc-rowwords-append record (fn-lbc-row-store fn-lbc)) fn-lbc)) (nth 12 record))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-word-withdrawal-at-by-definition update-fn-lbc-row-store fn-lbc-row-store fn-lbc-rowwords-append-is-append fn-dm-nth-update-nth fn-lbrse-count-by-store fn-lbrse-len-append-one fn-lbrse-nth-append-at-length fn-lbrse-nth-append-prefix nth)))))

(defthm fn-lbc-word-withdrawal-at-of-store-append-old
 (implies (and (natp i) (< i (fn-lbc-count fn-lbc)))
  (equal (fn-lbc-word :withdrawal-at i (update-fn-lbc-row-store (fn-lbc-rowwords-append record (fn-lbc-row-store fn-lbc)) fn-lbc)) (fn-lbc-word :withdrawal-at i fn-lbc)))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-word-withdrawal-at-by-definition update-fn-lbc-row-store fn-lbc-row-store fn-lbc-rowwords-append-is-append fn-dm-nth-update-nth fn-lbrse-count-by-store fn-lbrse-len-append-one fn-lbrse-nth-append-at-length fn-lbrse-nth-append-prefix nth)))))

(defthm fn-lbc-word-withdrawal-by-of-store-append-new
 (equal (fn-lbc-word :withdrawal-by (fn-lbc-count fn-lbc) (update-fn-lbc-row-store (fn-lbc-rowwords-append record (fn-lbc-row-store fn-lbc)) fn-lbc)) (nth 13 record))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-word-withdrawal-by-by-definition update-fn-lbc-row-store fn-lbc-row-store fn-lbc-rowwords-append-is-append fn-dm-nth-update-nth fn-lbrse-count-by-store fn-lbrse-len-append-one fn-lbrse-nth-append-at-length fn-lbrse-nth-append-prefix nth)))))

(defthm fn-lbc-word-withdrawal-by-of-store-append-old
 (implies (and (natp i) (< i (fn-lbc-count fn-lbc)))
  (equal (fn-lbc-word :withdrawal-by i (update-fn-lbc-row-store (fn-lbc-rowwords-append record (fn-lbc-row-store fn-lbc)) fn-lbc)) (fn-lbc-word :withdrawal-by i fn-lbc)))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-word-withdrawal-by-by-definition update-fn-lbc-row-store fn-lbc-row-store fn-lbc-rowwords-append-is-append fn-dm-nth-update-nth fn-lbrse-count-by-store fn-lbrse-len-append-one fn-lbrse-nth-append-at-length fn-lbrse-nth-append-prefix nth)))))

(defthm fn-lbc-word-overview-offset-of-store-append-new
 (equal (fn-lbc-word :overview-offset (fn-lbc-count fn-lbc) (update-fn-lbc-row-store (fn-lbc-rowwords-append record (fn-lbc-row-store fn-lbc)) fn-lbc)) (nth 14 record))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-word-overview-offset-by-definition update-fn-lbc-row-store fn-lbc-row-store fn-lbc-rowwords-append-is-append fn-dm-nth-update-nth fn-lbrse-count-by-store fn-lbrse-len-append-one fn-lbrse-nth-append-at-length fn-lbrse-nth-append-prefix nth)))))

(defthm fn-lbc-word-overview-offset-of-store-append-old
 (implies (and (natp i) (< i (fn-lbc-count fn-lbc)))
  (equal (fn-lbc-word :overview-offset i (update-fn-lbc-row-store (fn-lbc-rowwords-append record (fn-lbc-row-store fn-lbc)) fn-lbc)) (fn-lbc-word :overview-offset i fn-lbc)))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-word-overview-offset-by-definition update-fn-lbc-row-store fn-lbc-row-store fn-lbc-rowwords-append-is-append fn-dm-nth-update-nth fn-lbrse-count-by-store fn-lbrse-len-append-one fn-lbrse-nth-append-at-length fn-lbrse-nth-append-prefix nth)))))

(defthm fn-lbc-word-flags-of-store-append-new
 (equal (fn-lbc-word :flags (fn-lbc-count fn-lbc) (update-fn-lbc-row-store (fn-lbc-rowwords-append record (fn-lbc-row-store fn-lbc)) fn-lbc)) (nth 15 record))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-word-flags-by-definition update-fn-lbc-row-store fn-lbc-row-store fn-lbc-rowwords-append-is-append fn-dm-nth-update-nth fn-lbrse-count-by-store fn-lbrse-len-append-one fn-lbrse-nth-append-at-length fn-lbrse-nth-append-prefix nth)))))

(defthm fn-lbc-word-flags-of-store-append-old
 (implies (and (natp i) (< i (fn-lbc-count fn-lbc)))
  (equal (fn-lbc-word :flags i (update-fn-lbc-row-store (fn-lbc-rowwords-append record (fn-lbc-row-store fn-lbc)) fn-lbc)) (fn-lbc-word :flags i fn-lbc)))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-word-flags-by-definition update-fn-lbc-row-store fn-lbc-row-store fn-lbc-rowwords-append-is-append fn-dm-nth-update-nth fn-lbrse-count-by-store fn-lbrse-len-append-one fn-lbrse-nth-append-at-length fn-lbrse-nth-append-prefix nth)))))

(defthm fn-lbc-directory-field-sequence-of-store-append-new
 (equal (fn-lbc-directory-field :sequence (len (nth *fn-lbc-directory-store* fn-lbc)) (update-fn-lbc-directory-store (fn-lbc-directory-append record (fn-lbc-directory-store fn-lbc)) fn-lbc)) (nth 0 record))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-directory-field-sequence-by-definition update-fn-lbc-directory-store fn-lbc-directory-store fn-lbc-directory-append-is-append fn-dm-nth-update-nth fn-lbrse-count-by-store fn-lbrse-len-append-one fn-lbrse-nth-append-at-length fn-lbrse-nth-append-prefix nth)))))

(defthm fn-lbc-directory-field-sequence-of-store-append-old
 (implies (and (natp i) (< i (len (nth *fn-lbc-directory-store* fn-lbc))))
  (equal (fn-lbc-directory-field :sequence i (update-fn-lbc-directory-store (fn-lbc-directory-append record (fn-lbc-directory-store fn-lbc)) fn-lbc)) (fn-lbc-directory-field :sequence i fn-lbc)))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-directory-field-sequence-by-definition update-fn-lbc-directory-store fn-lbc-directory-store fn-lbc-directory-append-is-append fn-dm-nth-update-nth fn-lbrse-count-by-store fn-lbrse-len-append-one fn-lbrse-nth-append-at-length fn-lbrse-nth-append-prefix nth)))))

(defthm fn-lbc-directory-field-facts-octets-of-store-append-new
 (equal (fn-lbc-directory-field :facts-octets (len (nth *fn-lbc-directory-store* fn-lbc)) (update-fn-lbc-directory-store (fn-lbc-directory-append record (fn-lbc-directory-store fn-lbc)) fn-lbc)) (nth 1 record))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-directory-field-facts-octets-by-definition update-fn-lbc-directory-store fn-lbc-directory-store fn-lbc-directory-append-is-append fn-dm-nth-update-nth fn-lbrse-count-by-store fn-lbrse-len-append-one fn-lbrse-nth-append-at-length fn-lbrse-nth-append-prefix nth)))))

(defthm fn-lbc-directory-field-facts-octets-of-store-append-old
 (implies (and (natp i) (< i (len (nth *fn-lbc-directory-store* fn-lbc))))
  (equal (fn-lbc-directory-field :facts-octets i (update-fn-lbc-directory-store (fn-lbc-directory-append record (fn-lbc-directory-store fn-lbc)) fn-lbc)) (fn-lbc-directory-field :facts-octets i fn-lbc)))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-directory-field-facts-octets-by-definition update-fn-lbc-directory-store fn-lbc-directory-store fn-lbc-directory-append-is-append fn-dm-nth-update-nth fn-lbrse-count-by-store fn-lbrse-len-append-one fn-lbrse-nth-append-at-length fn-lbrse-nth-append-prefix nth)))))

(defthm fn-lbc-directory-field-body-start-of-store-append-new
 (equal (fn-lbc-directory-field :body-start (len (nth *fn-lbc-directory-store* fn-lbc)) (update-fn-lbc-directory-store (fn-lbc-directory-append record (fn-lbc-directory-store fn-lbc)) fn-lbc)) (nth 2 record))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-directory-field-body-start-by-definition update-fn-lbc-directory-store fn-lbc-directory-store fn-lbc-directory-append-is-append fn-dm-nth-update-nth fn-lbrse-count-by-store fn-lbrse-len-append-one fn-lbrse-nth-append-at-length fn-lbrse-nth-append-prefix nth)))))

(defthm fn-lbc-directory-field-body-start-of-store-append-old
 (implies (and (natp i) (< i (len (nth *fn-lbc-directory-store* fn-lbc))))
  (equal (fn-lbc-directory-field :body-start i (update-fn-lbc-directory-store (fn-lbc-directory-append record (fn-lbc-directory-store fn-lbc)) fn-lbc)) (fn-lbc-directory-field :body-start i fn-lbc)))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-directory-field-body-start-by-definition update-fn-lbc-directory-store fn-lbc-directory-store fn-lbc-directory-append-is-append fn-dm-nth-update-nth fn-lbrse-count-by-store fn-lbrse-len-append-one fn-lbrse-nth-append-at-length fn-lbrse-nth-append-prefix nth)))))

(defthm fn-lbc-directory-field-body-start-present-of-store-append-new
 (equal (fn-lbc-directory-field :body-start-present (len (nth *fn-lbc-directory-store* fn-lbc)) (update-fn-lbc-directory-store (fn-lbc-directory-append record (fn-lbc-directory-store fn-lbc)) fn-lbc)) (nth 3 record))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-directory-field-body-start-present-by-definition update-fn-lbc-directory-store fn-lbc-directory-store fn-lbc-directory-append-is-append fn-dm-nth-update-nth fn-lbrse-count-by-store fn-lbrse-len-append-one fn-lbrse-nth-append-at-length fn-lbrse-nth-append-prefix nth)))))

(defthm fn-lbc-directory-field-body-start-present-of-store-append-old
 (implies (and (natp i) (< i (len (nth *fn-lbc-directory-store* fn-lbc))))
  (equal (fn-lbc-directory-field :body-start-present i (update-fn-lbc-directory-store (fn-lbc-directory-append record (fn-lbc-directory-store fn-lbc)) fn-lbc)) (fn-lbc-directory-field :body-start-present i fn-lbc)))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-directory-field-body-start-present-by-definition update-fn-lbc-directory-store fn-lbc-directory-store fn-lbc-directory-append-is-append fn-dm-nth-update-nth fn-lbrse-count-by-store fn-lbrse-len-append-one fn-lbrse-nth-append-at-length fn-lbrse-nth-append-prefix nth)))))

(defthm fn-lbc-directory-field-body-lines-of-store-append-new
 (equal (fn-lbc-directory-field :body-lines (len (nth *fn-lbc-directory-store* fn-lbc)) (update-fn-lbc-directory-store (fn-lbc-directory-append record (fn-lbc-directory-store fn-lbc)) fn-lbc)) (nth 4 record))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-directory-field-body-lines-by-definition update-fn-lbc-directory-store fn-lbc-directory-store fn-lbc-directory-append-is-append fn-dm-nth-update-nth fn-lbrse-count-by-store fn-lbrse-len-append-one fn-lbrse-nth-append-at-length fn-lbrse-nth-append-prefix nth)))))

(defthm fn-lbc-directory-field-body-lines-of-store-append-old
 (implies (and (natp i) (< i (len (nth *fn-lbc-directory-store* fn-lbc))))
  (equal (fn-lbc-directory-field :body-lines i (update-fn-lbc-directory-store (fn-lbc-directory-append record (fn-lbc-directory-store fn-lbc)) fn-lbc)) (fn-lbc-directory-field :body-lines i fn-lbc)))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-directory-field-body-lines-by-definition update-fn-lbc-directory-store fn-lbc-directory-store fn-lbc-directory-append-is-append fn-dm-nth-update-nth fn-lbrse-count-by-store fn-lbrse-len-append-one fn-lbrse-nth-append-at-length fn-lbrse-nth-append-prefix nth)))))

(defthm fn-lbc-directory-field-nov-start-of-store-append-new
 (equal (fn-lbc-directory-field :nov-start (len (nth *fn-lbc-directory-store* fn-lbc)) (update-fn-lbc-directory-store (fn-lbc-directory-append record (fn-lbc-directory-store fn-lbc)) fn-lbc)) (nth 5 record))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-directory-field-nov-start-by-definition update-fn-lbc-directory-store fn-lbc-directory-store fn-lbc-directory-append-is-append fn-dm-nth-update-nth fn-lbrse-count-by-store fn-lbrse-len-append-one fn-lbrse-nth-append-at-length fn-lbrse-nth-append-prefix nth)))))

(defthm fn-lbc-directory-field-nov-start-of-store-append-old
 (implies (and (natp i) (< i (len (nth *fn-lbc-directory-store* fn-lbc))))
  (equal (fn-lbc-directory-field :nov-start i (update-fn-lbc-directory-store (fn-lbc-directory-append record (fn-lbc-directory-store fn-lbc)) fn-lbc)) (fn-lbc-directory-field :nov-start i fn-lbc)))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-directory-field-nov-start-by-definition update-fn-lbc-directory-store fn-lbc-directory-store fn-lbc-directory-append-is-append fn-dm-nth-update-nth fn-lbrse-count-by-store fn-lbrse-len-append-one fn-lbrse-nth-append-at-length fn-lbrse-nth-append-prefix nth)))))

(defthm fn-lbc-directory-field-nov-length-of-store-append-new
 (equal (fn-lbc-directory-field :nov-length (len (nth *fn-lbc-directory-store* fn-lbc)) (update-fn-lbc-directory-store (fn-lbc-directory-append record (fn-lbc-directory-store fn-lbc)) fn-lbc)) (nth 6 record))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-directory-field-nov-length-by-definition update-fn-lbc-directory-store fn-lbc-directory-store fn-lbc-directory-append-is-append fn-dm-nth-update-nth fn-lbrse-count-by-store fn-lbrse-len-append-one fn-lbrse-nth-append-at-length fn-lbrse-nth-append-prefix nth)))))

(defthm fn-lbc-directory-field-nov-length-of-store-append-old
 (implies (and (natp i) (< i (len (nth *fn-lbc-directory-store* fn-lbc))))
  (equal (fn-lbc-directory-field :nov-length i (update-fn-lbc-directory-store (fn-lbc-directory-append record (fn-lbc-directory-store fn-lbc)) fn-lbc)) (fn-lbc-directory-field :nov-length i fn-lbc)))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-directory-field-nov-length-by-definition update-fn-lbc-directory-store fn-lbc-directory-store fn-lbc-directory-append-is-append fn-dm-nth-update-nth fn-lbrse-count-by-store fn-lbrse-len-append-one fn-lbrse-nth-append-at-length fn-lbrse-nth-append-prefix nth)))))

(defthm fn-lbc-directory-field-render-nov-start-of-store-append-new
 (equal (fn-lbc-directory-field :render-nov-start (len (nth *fn-lbc-directory-store* fn-lbc)) (update-fn-lbc-directory-store (fn-lbc-directory-append record (fn-lbc-directory-store fn-lbc)) fn-lbc)) (nth 7 record))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-directory-field-render-nov-start-by-definition update-fn-lbc-directory-store fn-lbc-directory-store fn-lbc-directory-append-is-append fn-dm-nth-update-nth fn-lbrse-count-by-store fn-lbrse-len-append-one fn-lbrse-nth-append-at-length fn-lbrse-nth-append-prefix nth)))))

(defthm fn-lbc-directory-field-render-nov-start-of-store-append-old
 (implies (and (natp i) (< i (len (nth *fn-lbc-directory-store* fn-lbc))))
  (equal (fn-lbc-directory-field :render-nov-start i (update-fn-lbc-directory-store (fn-lbc-directory-append record (fn-lbc-directory-store fn-lbc)) fn-lbc)) (fn-lbc-directory-field :render-nov-start i fn-lbc)))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-directory-field-render-nov-start-by-definition update-fn-lbc-directory-store fn-lbc-directory-store fn-lbc-directory-append-is-append fn-dm-nth-update-nth fn-lbrse-count-by-store fn-lbrse-len-append-one fn-lbrse-nth-append-at-length fn-lbrse-nth-append-prefix nth)))))

(defthm fn-lbc-directory-field-render-nov-length-of-store-append-new
 (equal (fn-lbc-directory-field :render-nov-length (len (nth *fn-lbc-directory-store* fn-lbc)) (update-fn-lbc-directory-store (fn-lbc-directory-append record (fn-lbc-directory-store fn-lbc)) fn-lbc)) (nth 8 record))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-directory-field-render-nov-length-by-definition update-fn-lbc-directory-store fn-lbc-directory-store fn-lbc-directory-append-is-append fn-dm-nth-update-nth fn-lbrse-count-by-store fn-lbrse-len-append-one fn-lbrse-nth-append-at-length fn-lbrse-nth-append-prefix nth)))))

(defthm fn-lbc-directory-field-render-nov-length-of-store-append-old
 (implies (and (natp i) (< i (len (nth *fn-lbc-directory-store* fn-lbc))))
  (equal (fn-lbc-directory-field :render-nov-length i (update-fn-lbc-directory-store (fn-lbc-directory-append record (fn-lbc-directory-store fn-lbc)) fn-lbc)) (fn-lbc-directory-field :render-nov-length i fn-lbc)))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-directory-field-render-nov-length-by-definition update-fn-lbc-directory-store fn-lbc-directory-store fn-lbc-directory-append-is-append fn-dm-nth-update-nth fn-lbrse-count-by-store fn-lbrse-len-append-one fn-lbrse-nth-append-at-length fn-lbrse-nth-append-prefix nth)))))

(defthm fn-lbc-directory-field-groups-start-of-store-append-new
 (equal (fn-lbc-directory-field :groups-start (len (nth *fn-lbc-directory-store* fn-lbc)) (update-fn-lbc-directory-store (fn-lbc-directory-append record (fn-lbc-directory-store fn-lbc)) fn-lbc)) (nth 9 record))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-directory-field-groups-start-by-definition update-fn-lbc-directory-store fn-lbc-directory-store fn-lbc-directory-append-is-append fn-dm-nth-update-nth fn-lbrse-count-by-store fn-lbrse-len-append-one fn-lbrse-nth-append-at-length fn-lbrse-nth-append-prefix nth)))))

(defthm fn-lbc-directory-field-groups-start-of-store-append-old
 (implies (and (natp i) (< i (len (nth *fn-lbc-directory-store* fn-lbc))))
  (equal (fn-lbc-directory-field :groups-start i (update-fn-lbc-directory-store (fn-lbc-directory-append record (fn-lbc-directory-store fn-lbc)) fn-lbc)) (fn-lbc-directory-field :groups-start i fn-lbc)))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-directory-field-groups-start-by-definition update-fn-lbc-directory-store fn-lbc-directory-store fn-lbc-directory-append-is-append fn-dm-nth-update-nth fn-lbrse-count-by-store fn-lbrse-len-append-one fn-lbrse-nth-append-at-length fn-lbrse-nth-append-prefix nth)))))

(defthm fn-lbc-directory-field-groups-count-of-store-append-new
 (equal (fn-lbc-directory-field :groups-count (len (nth *fn-lbc-directory-store* fn-lbc)) (update-fn-lbc-directory-store (fn-lbc-directory-append record (fn-lbc-directory-store fn-lbc)) fn-lbc)) (nth 10 record))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-directory-field-groups-count-by-definition update-fn-lbc-directory-store fn-lbc-directory-store fn-lbc-directory-append-is-append fn-dm-nth-update-nth fn-lbrse-count-by-store fn-lbrse-len-append-one fn-lbrse-nth-append-at-length fn-lbrse-nth-append-prefix nth)))))

(defthm fn-lbc-directory-field-groups-count-of-store-append-old
 (implies (and (natp i) (< i (len (nth *fn-lbc-directory-store* fn-lbc))))
  (equal (fn-lbc-directory-field :groups-count i (update-fn-lbc-directory-store (fn-lbc-directory-append record (fn-lbc-directory-store fn-lbc)) fn-lbc)) (fn-lbc-directory-field :groups-count i fn-lbc)))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-directory-field-groups-count-by-definition update-fn-lbc-directory-store fn-lbc-directory-store fn-lbc-directory-append-is-append fn-dm-nth-update-nth fn-lbrse-count-by-store fn-lbrse-len-append-one fn-lbrse-nth-append-at-length fn-lbrse-nth-append-prefix nth)))))

(defthm fn-lbc-directory-field-numbers-start-of-store-append-new
 (equal (fn-lbc-directory-field :numbers-start (len (nth *fn-lbc-directory-store* fn-lbc)) (update-fn-lbc-directory-store (fn-lbc-directory-append record (fn-lbc-directory-store fn-lbc)) fn-lbc)) (nth 11 record))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-directory-field-numbers-start-by-definition update-fn-lbc-directory-store fn-lbc-directory-store fn-lbc-directory-append-is-append fn-dm-nth-update-nth fn-lbrse-count-by-store fn-lbrse-len-append-one fn-lbrse-nth-append-at-length fn-lbrse-nth-append-prefix nth)))))

(defthm fn-lbc-directory-field-numbers-start-of-store-append-old
 (implies (and (natp i) (< i (len (nth *fn-lbc-directory-store* fn-lbc))))
  (equal (fn-lbc-directory-field :numbers-start i (update-fn-lbc-directory-store (fn-lbc-directory-append record (fn-lbc-directory-store fn-lbc)) fn-lbc)) (fn-lbc-directory-field :numbers-start i fn-lbc)))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-directory-field-numbers-start-by-definition update-fn-lbc-directory-store fn-lbc-directory-store fn-lbc-directory-append-is-append fn-dm-nth-update-nth fn-lbrse-count-by-store fn-lbrse-len-append-one fn-lbrse-nth-append-at-length fn-lbrse-nth-append-prefix nth)))))

(defthm fn-lbc-directory-field-numbers-count-of-store-append-new
 (equal (fn-lbc-directory-field :numbers-count (len (nth *fn-lbc-directory-store* fn-lbc)) (update-fn-lbc-directory-store (fn-lbc-directory-append record (fn-lbc-directory-store fn-lbc)) fn-lbc)) (nth 12 record))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-directory-field-numbers-count-by-definition update-fn-lbc-directory-store fn-lbc-directory-store fn-lbc-directory-append-is-append fn-dm-nth-update-nth fn-lbrse-count-by-store fn-lbrse-len-append-one fn-lbrse-nth-append-at-length fn-lbrse-nth-append-prefix nth)))))

(defthm fn-lbc-directory-field-numbers-count-of-store-append-old
 (implies (and (natp i) (< i (len (nth *fn-lbc-directory-store* fn-lbc))))
  (equal (fn-lbc-directory-field :numbers-count i (update-fn-lbc-directory-store (fn-lbc-directory-append record (fn-lbc-directory-store fn-lbc)) fn-lbc)) (fn-lbc-directory-field :numbers-count i fn-lbc)))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-directory-field-numbers-count-by-definition update-fn-lbc-directory-store fn-lbc-directory-store fn-lbc-directory-append-is-append fn-dm-nth-update-nth fn-lbrse-count-by-store fn-lbrse-len-append-one fn-lbrse-nth-append-at-length fn-lbrse-nth-append-prefix nth)))))

(defthm fn-lbc-directory-field-article-ok-of-store-append-new
 (equal (fn-lbc-directory-field :article-ok (len (nth *fn-lbc-directory-store* fn-lbc)) (update-fn-lbc-directory-store (fn-lbc-directory-append record (fn-lbc-directory-store fn-lbc)) fn-lbc)) (nth 13 record))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-directory-field-article-ok-by-definition update-fn-lbc-directory-store fn-lbc-directory-store fn-lbc-directory-append-is-append fn-dm-nth-update-nth fn-lbrse-count-by-store fn-lbrse-len-append-one fn-lbrse-nth-append-at-length fn-lbrse-nth-append-prefix nth)))))

(defthm fn-lbc-directory-field-article-ok-of-store-append-old
 (implies (and (natp i) (< i (len (nth *fn-lbc-directory-store* fn-lbc))))
  (equal (fn-lbc-directory-field :article-ok i (update-fn-lbc-directory-store (fn-lbc-directory-append record (fn-lbc-directory-store fn-lbc)) fn-lbc)) (fn-lbc-directory-field :article-ok i fn-lbc)))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-directory-field-article-ok-by-definition update-fn-lbc-directory-store fn-lbc-directory-store fn-lbc-directory-append-is-append fn-dm-nth-update-nth fn-lbrse-count-by-store fn-lbrse-len-append-one fn-lbrse-nth-append-at-length fn-lbrse-nth-append-prefix nth)))))

(defthm fn-lbc-directory-field-head-ok-of-store-append-new
 (equal (fn-lbc-directory-field :head-ok (len (nth *fn-lbc-directory-store* fn-lbc)) (update-fn-lbc-directory-store (fn-lbc-directory-append record (fn-lbc-directory-store fn-lbc)) fn-lbc)) (nth 14 record))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-directory-field-head-ok-by-definition update-fn-lbc-directory-store fn-lbc-directory-store fn-lbc-directory-append-is-append fn-dm-nth-update-nth fn-lbrse-count-by-store fn-lbrse-len-append-one fn-lbrse-nth-append-at-length fn-lbrse-nth-append-prefix nth)))))

(defthm fn-lbc-directory-field-head-ok-of-store-append-old
 (implies (and (natp i) (< i (len (nth *fn-lbc-directory-store* fn-lbc))))
  (equal (fn-lbc-directory-field :head-ok i (update-fn-lbc-directory-store (fn-lbc-directory-append record (fn-lbc-directory-store fn-lbc)) fn-lbc)) (fn-lbc-directory-field :head-ok i fn-lbc)))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-directory-field-head-ok-by-definition update-fn-lbc-directory-store fn-lbc-directory-store fn-lbc-directory-append-is-append fn-dm-nth-update-nth fn-lbrse-count-by-store fn-lbrse-len-append-one fn-lbrse-nth-append-at-length fn-lbrse-nth-append-prefix nth)))))

(defthm fn-lbc-directory-field-body-ok-of-store-append-new
 (equal (fn-lbc-directory-field :body-ok (len (nth *fn-lbc-directory-store* fn-lbc)) (update-fn-lbc-directory-store (fn-lbc-directory-append record (fn-lbc-directory-store fn-lbc)) fn-lbc)) (nth 15 record))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-directory-field-body-ok-by-definition update-fn-lbc-directory-store fn-lbc-directory-store fn-lbc-directory-append-is-append fn-dm-nth-update-nth fn-lbrse-count-by-store fn-lbrse-len-append-one fn-lbrse-nth-append-at-length fn-lbrse-nth-append-prefix nth)))))

(defthm fn-lbc-directory-field-body-ok-of-store-append-old
 (implies (and (natp i) (< i (len (nth *fn-lbc-directory-store* fn-lbc))))
  (equal (fn-lbc-directory-field :body-ok i (update-fn-lbc-directory-store (fn-lbc-directory-append record (fn-lbc-directory-store fn-lbc)) fn-lbc)) (fn-lbc-directory-field :body-ok i fn-lbc)))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-directory-field-body-ok-by-definition update-fn-lbc-directory-store fn-lbc-directory-store fn-lbc-directory-append-is-append fn-dm-nth-update-nth fn-lbrse-count-by-store fn-lbrse-len-append-one fn-lbrse-nth-append-at-length fn-lbrse-nth-append-prefix nth)))))

(defthm fn-lbc-directory-field-raw-head-length-of-store-append-new
 (equal (fn-lbc-directory-field :raw-head-length (len (nth *fn-lbc-directory-store* fn-lbc)) (update-fn-lbc-directory-store (fn-lbc-directory-append record (fn-lbc-directory-store fn-lbc)) fn-lbc)) (nth 16 record))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-directory-field-raw-head-length-by-definition update-fn-lbc-directory-store fn-lbc-directory-store fn-lbc-directory-append-is-append fn-dm-nth-update-nth fn-lbrse-count-by-store fn-lbrse-len-append-one fn-lbrse-nth-append-at-length fn-lbrse-nth-append-prefix nth)))))

(defthm fn-lbc-directory-field-raw-head-length-of-store-append-old
 (implies (and (natp i) (< i (len (nth *fn-lbc-directory-store* fn-lbc))))
  (equal (fn-lbc-directory-field :raw-head-length i (update-fn-lbc-directory-store (fn-lbc-directory-append record (fn-lbc-directory-store fn-lbc)) fn-lbc)) (fn-lbc-directory-field :raw-head-length i fn-lbc)))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-directory-field-raw-head-length-by-definition update-fn-lbc-directory-store fn-lbc-directory-store fn-lbc-directory-append-is-append fn-dm-nth-update-nth fn-lbrse-count-by-store fn-lbrse-len-append-one fn-lbrse-nth-append-at-length fn-lbrse-nth-append-prefix nth)))))

(defthm fn-lbc-directory-field-framed-of-store-append-new
 (equal (fn-lbc-directory-field :framed (len (nth *fn-lbc-directory-store* fn-lbc)) (update-fn-lbc-directory-store (fn-lbc-directory-append record (fn-lbc-directory-store fn-lbc)) fn-lbc)) (nth 17 record))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-directory-field-framed-by-definition update-fn-lbc-directory-store fn-lbc-directory-store fn-lbc-directory-append-is-append fn-dm-nth-update-nth fn-lbrse-count-by-store fn-lbrse-len-append-one fn-lbrse-nth-append-at-length fn-lbrse-nth-append-prefix nth)))))

(defthm fn-lbc-directory-field-framed-of-store-append-old
 (implies (and (natp i) (< i (len (nth *fn-lbc-directory-store* fn-lbc))))
  (equal (fn-lbc-directory-field :framed i (update-fn-lbc-directory-store (fn-lbc-directory-append record (fn-lbc-directory-store fn-lbc)) fn-lbc)) (fn-lbc-directory-field :framed i fn-lbc)))
 :hints (("Goal" :do-not '(preprocess) :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero) '(fn-lbc-directory-field-framed-by-definition update-fn-lbc-directory-store fn-lbc-directory-store fn-lbc-directory-append-is-append fn-dm-nth-update-nth fn-lbrse-count-by-store fn-lbrse-len-append-one fn-lbrse-nth-append-at-length fn-lbrse-nth-append-prefix nth)))))

(defthm fn-lbc-loc0-is-word-by-definition
 (implies (and (natp i) (< i (fn-lbc-count fn-lbc)))
  (equal (fn-lbc-loc0 i fn-lbc) (fn-lbc-word :loc0 i fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
   '(fn-lbc-loc0 fn-lbc-row-store fn-lbc-rowwords-get-loc0 fn-lbc-rowwords$a-get-loc0
     fn-lbc-word-loc0-by-definition fn-lbrse-count-by-store)))))

(defthm fn-lbc-loc1-is-word-by-definition
 (implies (and (natp i) (< i (fn-lbc-count fn-lbc)))
  (equal (fn-lbc-loc1 i fn-lbc) (fn-lbc-word :loc1 i fn-lbc)))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
   '(fn-lbc-loc1 fn-lbc-row-store fn-lbc-rowwords-get-loc1 fn-lbc-rowwords$a-get-loc1
     fn-lbc-word-loc1-by-definition fn-lbrse-count-by-store)))))
