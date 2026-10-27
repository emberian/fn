; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-membership-row-types")

(defthm fn-lbc-word-handle-by-definition
 (equal (fn-lbc-word :handle i fn-lbc)
  (if (and (natp i) (< i (len (nth *fn-lbc-row-store* fn-lbc))))
      (nth 0 (nth i (nth *fn-lbc-row-store* fn-lbc))) nil))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
   '(fn-lbc-word fn-lbc-row-store fn-lbc-rowwords-count-is-len
     fn-lbc-rowwords-get-handle fn-lbc-rowwords$a-get-handle)))))

(defthm fn-lbc-word-loc0-by-definition
 (equal (fn-lbc-word :loc0 i fn-lbc)
  (if (and (natp i) (< i (len (nth *fn-lbc-row-store* fn-lbc))))
      (nth 1 (nth i (nth *fn-lbc-row-store* fn-lbc))) nil))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
   '(fn-lbc-word fn-lbc-row-store fn-lbc-rowwords-count-is-len
     fn-lbc-rowwords-get-loc0 fn-lbc-rowwords$a-get-loc0)))))

(defthm fn-lbc-word-loc1-by-definition
 (equal (fn-lbc-word :loc1 i fn-lbc)
  (if (and (natp i) (< i (len (nth *fn-lbc-row-store* fn-lbc))))
      (nth 2 (nth i (nth *fn-lbc-row-store* fn-lbc))) nil))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
   '(fn-lbc-word fn-lbc-row-store fn-lbc-rowwords-count-is-len
     fn-lbc-rowwords-get-loc1 fn-lbc-rowwords$a-get-loc1)))))

(defthm fn-lbc-word-head-length-by-definition
 (equal (fn-lbc-word :head-length i fn-lbc)
  (if (and (natp i) (< i (len (nth *fn-lbc-row-store* fn-lbc))))
      (nth 3 (nth i (nth *fn-lbc-row-store* fn-lbc))) nil))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
   '(fn-lbc-word fn-lbc-row-store fn-lbc-rowwords-count-is-len
     fn-lbc-rowwords-get-head-length fn-lbc-rowwords$a-get-head-length)))))

(defthm fn-lbc-word-stamp-by-definition
 (equal (fn-lbc-word :stamp i fn-lbc)
  (if (and (natp i) (< i (len (nth *fn-lbc-row-store* fn-lbc))))
      (nth 4 (nth i (nth *fn-lbc-row-store* fn-lbc))) nil))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
   '(fn-lbc-word fn-lbc-row-store fn-lbc-rowwords-count-is-len
     fn-lbc-rowwords-get-stamp fn-lbc-rowwords$a-get-stamp)))))

(defthm fn-lbc-word-prefix-max-by-definition
 (equal (fn-lbc-word :prefix-max i fn-lbc)
  (if (and (natp i) (< i (len (nth *fn-lbc-row-store* fn-lbc))))
      (nth 5 (nth i (nth *fn-lbc-row-store* fn-lbc))) nil))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
   '(fn-lbc-word fn-lbc-row-store fn-lbc-rowwords-count-is-len
     fn-lbc-rowwords-get-prefix-max fn-lbc-rowwords$a-get-prefix-max)))))

(defthm fn-lbc-word-txid-by-definition
 (equal (fn-lbc-word :txid i fn-lbc)
  (if (and (natp i) (< i (len (nth *fn-lbc-row-store* fn-lbc))))
      (nth 6 (nth i (nth *fn-lbc-row-store* fn-lbc))) nil))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
   '(fn-lbc-word fn-lbc-row-store fn-lbc-rowwords-count-is-len
     fn-lbc-rowwords-get-txid fn-lbc-rowwords$a-get-txid)))))

(defthm fn-lbc-word-generation-by-definition
 (equal (fn-lbc-word :generation i fn-lbc)
  (if (and (natp i) (< i (len (nth *fn-lbc-row-store* fn-lbc))))
      (nth 7 (nth i (nth *fn-lbc-row-store* fn-lbc))) nil))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
   '(fn-lbc-word fn-lbc-row-store fn-lbc-rowwords-count-is-len
     fn-lbc-rowwords-get-generation fn-lbc-rowwords$a-get-generation)))))

(defthm fn-lbc-word-charge-by-definition
 (equal (fn-lbc-word :charge i fn-lbc)
  (if (and (natp i) (< i (len (nth *fn-lbc-row-store* fn-lbc))))
      (nth 8 (nth i (nth *fn-lbc-row-store* fn-lbc))) nil))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
   '(fn-lbc-word fn-lbc-row-store fn-lbc-rowwords-count-is-len
     fn-lbc-rowwords-get-charge fn-lbc-rowwords$a-get-charge)))))

(defthm fn-lbc-word-msgid-hash-by-definition
 (equal (fn-lbc-word :msgid-hash i fn-lbc)
  (if (and (natp i) (< i (len (nth *fn-lbc-row-store* fn-lbc))))
      (nth 9 (nth i (nth *fn-lbc-row-store* fn-lbc))) nil))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
   '(fn-lbc-word fn-lbc-row-store fn-lbc-rowwords-count-is-len
     fn-lbc-rowwords-get-msgid-hash fn-lbc-rowwords$a-get-msgid-hash)))))

(defthm fn-lbc-word-msgid-offset-by-definition
 (equal (fn-lbc-word :msgid-offset i fn-lbc)
  (if (and (natp i) (< i (len (nth *fn-lbc-row-store* fn-lbc))))
      (nth 10 (nth i (nth *fn-lbc-row-store* fn-lbc))) nil))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
   '(fn-lbc-word fn-lbc-row-store fn-lbc-rowwords-count-is-len
     fn-lbc-rowwords-get-msgid-offset fn-lbc-rowwords$a-get-msgid-offset)))))

(defthm fn-lbc-word-msgid-length-by-definition
 (equal (fn-lbc-word :msgid-length i fn-lbc)
  (if (and (natp i) (< i (len (nth *fn-lbc-row-store* fn-lbc))))
      (nth 11 (nth i (nth *fn-lbc-row-store* fn-lbc))) nil))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
   '(fn-lbc-word fn-lbc-row-store fn-lbc-rowwords-count-is-len
     fn-lbc-rowwords-get-msgid-length fn-lbc-rowwords$a-get-msgid-length)))))

(defthm fn-lbc-word-withdrawal-at-by-definition
 (equal (fn-lbc-word :withdrawal-at i fn-lbc)
  (if (and (natp i) (< i (len (nth *fn-lbc-row-store* fn-lbc))))
      (nth 12 (nth i (nth *fn-lbc-row-store* fn-lbc))) nil))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
   '(fn-lbc-word fn-lbc-row-store fn-lbc-rowwords-count-is-len
     fn-lbc-rowwords-get-withdrawal-at fn-lbc-rowwords$a-get-withdrawal-at)))))

(defthm fn-lbc-word-withdrawal-by-by-definition
 (equal (fn-lbc-word :withdrawal-by i fn-lbc)
  (if (and (natp i) (< i (len (nth *fn-lbc-row-store* fn-lbc))))
      (nth 13 (nth i (nth *fn-lbc-row-store* fn-lbc))) nil))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
   '(fn-lbc-word fn-lbc-row-store fn-lbc-rowwords-count-is-len
     fn-lbc-rowwords-get-withdrawal-by fn-lbc-rowwords$a-get-withdrawal-by)))))

(defthm fn-lbc-word-overview-offset-by-definition
 (equal (fn-lbc-word :overview-offset i fn-lbc)
  (if (and (natp i) (< i (len (nth *fn-lbc-row-store* fn-lbc))))
      (nth 14 (nth i (nth *fn-lbc-row-store* fn-lbc))) nil))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
   '(fn-lbc-word fn-lbc-row-store fn-lbc-rowwords-count-is-len
     fn-lbc-rowwords-get-overview-offset fn-lbc-rowwords$a-get-overview-offset)))))

(defthm fn-lbc-word-flags-by-definition
 (equal (fn-lbc-word :flags i fn-lbc)
  (if (and (natp i) (< i (len (nth *fn-lbc-row-store* fn-lbc))))
      (nth 15 (nth i (nth *fn-lbc-row-store* fn-lbc))) nil))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
   '(fn-lbc-word fn-lbc-row-store fn-lbc-rowwords-count-is-len
     fn-lbc-rowwords-get-flags fn-lbc-rowwords$a-get-flags)))))

(defthm fn-lbc-directory-field-sequence-by-definition
 (equal (fn-lbc-directory-field :sequence i fn-lbc)
  (if (and (natp i) (< i (len (nth *fn-lbc-directory-store* fn-lbc))))
      (nth 0 (nth i (nth *fn-lbc-directory-store* fn-lbc))) nil))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
   '(fn-lbc-directory-field fn-lbc-directory-store fn-lbc-directory-count-is-len
     fn-lbc-directory-get-sequence fn-lbc-directory$a-get-sequence)))))

(defthm fn-lbc-directory-field-facts-octets-by-definition
 (equal (fn-lbc-directory-field :facts-octets i fn-lbc)
  (if (and (natp i) (< i (len (nth *fn-lbc-directory-store* fn-lbc))))
      (nth 1 (nth i (nth *fn-lbc-directory-store* fn-lbc))) nil))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
   '(fn-lbc-directory-field fn-lbc-directory-store fn-lbc-directory-count-is-len
     fn-lbc-directory-get-facts-octets fn-lbc-directory$a-get-facts-octets)))))

(defthm fn-lbc-directory-field-body-start-by-definition
 (equal (fn-lbc-directory-field :body-start i fn-lbc)
  (if (and (natp i) (< i (len (nth *fn-lbc-directory-store* fn-lbc))))
      (nth 2 (nth i (nth *fn-lbc-directory-store* fn-lbc))) nil))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
   '(fn-lbc-directory-field fn-lbc-directory-store fn-lbc-directory-count-is-len
     fn-lbc-directory-get-body-start fn-lbc-directory$a-get-body-start)))))

(defthm fn-lbc-directory-field-body-start-present-by-definition
 (equal (fn-lbc-directory-field :body-start-present i fn-lbc)
  (if (and (natp i) (< i (len (nth *fn-lbc-directory-store* fn-lbc))))
      (nth 3 (nth i (nth *fn-lbc-directory-store* fn-lbc))) nil))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
   '(fn-lbc-directory-field fn-lbc-directory-store fn-lbc-directory-count-is-len
     fn-lbc-directory-get-body-start-present fn-lbc-directory$a-get-body-start-present)))))

(defthm fn-lbc-directory-field-body-lines-by-definition
 (equal (fn-lbc-directory-field :body-lines i fn-lbc)
  (if (and (natp i) (< i (len (nth *fn-lbc-directory-store* fn-lbc))))
      (nth 4 (nth i (nth *fn-lbc-directory-store* fn-lbc))) nil))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
   '(fn-lbc-directory-field fn-lbc-directory-store fn-lbc-directory-count-is-len
     fn-lbc-directory-get-body-lines fn-lbc-directory$a-get-body-lines)))))

(defthm fn-lbc-directory-field-nov-start-by-definition
 (equal (fn-lbc-directory-field :nov-start i fn-lbc)
  (if (and (natp i) (< i (len (nth *fn-lbc-directory-store* fn-lbc))))
      (nth 5 (nth i (nth *fn-lbc-directory-store* fn-lbc))) nil))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
   '(fn-lbc-directory-field fn-lbc-directory-store fn-lbc-directory-count-is-len
     fn-lbc-directory-get-nov-start fn-lbc-directory$a-get-nov-start)))))

(defthm fn-lbc-directory-field-nov-length-by-definition
 (equal (fn-lbc-directory-field :nov-length i fn-lbc)
  (if (and (natp i) (< i (len (nth *fn-lbc-directory-store* fn-lbc))))
      (nth 6 (nth i (nth *fn-lbc-directory-store* fn-lbc))) nil))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
   '(fn-lbc-directory-field fn-lbc-directory-store fn-lbc-directory-count-is-len
     fn-lbc-directory-get-nov-length fn-lbc-directory$a-get-nov-length)))))

(defthm fn-lbc-directory-field-render-nov-start-by-definition
 (equal (fn-lbc-directory-field :render-nov-start i fn-lbc)
  (if (and (natp i) (< i (len (nth *fn-lbc-directory-store* fn-lbc))))
      (nth 7 (nth i (nth *fn-lbc-directory-store* fn-lbc))) nil))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
   '(fn-lbc-directory-field fn-lbc-directory-store fn-lbc-directory-count-is-len
     fn-lbc-directory-get-render-nov-start fn-lbc-directory$a-get-render-nov-start)))))

(defthm fn-lbc-directory-field-render-nov-length-by-definition
 (equal (fn-lbc-directory-field :render-nov-length i fn-lbc)
  (if (and (natp i) (< i (len (nth *fn-lbc-directory-store* fn-lbc))))
      (nth 8 (nth i (nth *fn-lbc-directory-store* fn-lbc))) nil))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
   '(fn-lbc-directory-field fn-lbc-directory-store fn-lbc-directory-count-is-len
     fn-lbc-directory-get-render-nov-length fn-lbc-directory$a-get-render-nov-length)))))

(defthm fn-lbc-directory-field-groups-start-by-definition
 (equal (fn-lbc-directory-field :groups-start i fn-lbc)
  (if (and (natp i) (< i (len (nth *fn-lbc-directory-store* fn-lbc))))
      (nth 9 (nth i (nth *fn-lbc-directory-store* fn-lbc))) nil))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
   '(fn-lbc-directory-field fn-lbc-directory-store fn-lbc-directory-count-is-len
     fn-lbc-directory-get-groups-start fn-lbc-directory$a-get-groups-start)))))

(defthm fn-lbc-directory-field-groups-count-by-definition
 (equal (fn-lbc-directory-field :groups-count i fn-lbc)
  (if (and (natp i) (< i (len (nth *fn-lbc-directory-store* fn-lbc))))
      (nth 10 (nth i (nth *fn-lbc-directory-store* fn-lbc))) nil))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
   '(fn-lbc-directory-field fn-lbc-directory-store fn-lbc-directory-count-is-len
     fn-lbc-directory-get-groups-count fn-lbc-directory$a-get-groups-count)))))

(defthm fn-lbc-directory-field-numbers-start-by-definition
 (equal (fn-lbc-directory-field :numbers-start i fn-lbc)
  (if (and (natp i) (< i (len (nth *fn-lbc-directory-store* fn-lbc))))
      (nth 11 (nth i (nth *fn-lbc-directory-store* fn-lbc))) nil))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
   '(fn-lbc-directory-field fn-lbc-directory-store fn-lbc-directory-count-is-len
     fn-lbc-directory-get-numbers-start fn-lbc-directory$a-get-numbers-start)))))

(defthm fn-lbc-directory-field-numbers-count-by-definition
 (equal (fn-lbc-directory-field :numbers-count i fn-lbc)
  (if (and (natp i) (< i (len (nth *fn-lbc-directory-store* fn-lbc))))
      (nth 12 (nth i (nth *fn-lbc-directory-store* fn-lbc))) nil))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
   '(fn-lbc-directory-field fn-lbc-directory-store fn-lbc-directory-count-is-len
     fn-lbc-directory-get-numbers-count fn-lbc-directory$a-get-numbers-count)))))

(defthm fn-lbc-directory-field-article-ok-by-definition
 (equal (fn-lbc-directory-field :article-ok i fn-lbc)
  (if (and (natp i) (< i (len (nth *fn-lbc-directory-store* fn-lbc))))
      (nth 13 (nth i (nth *fn-lbc-directory-store* fn-lbc))) nil))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
   '(fn-lbc-directory-field fn-lbc-directory-store fn-lbc-directory-count-is-len
     fn-lbc-directory-get-article-ok fn-lbc-directory$a-get-article-ok)))))

(defthm fn-lbc-directory-field-head-ok-by-definition
 (equal (fn-lbc-directory-field :head-ok i fn-lbc)
  (if (and (natp i) (< i (len (nth *fn-lbc-directory-store* fn-lbc))))
      (nth 14 (nth i (nth *fn-lbc-directory-store* fn-lbc))) nil))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
   '(fn-lbc-directory-field fn-lbc-directory-store fn-lbc-directory-count-is-len
     fn-lbc-directory-get-head-ok fn-lbc-directory$a-get-head-ok)))))

(defthm fn-lbc-directory-field-body-ok-by-definition
 (equal (fn-lbc-directory-field :body-ok i fn-lbc)
  (if (and (natp i) (< i (len (nth *fn-lbc-directory-store* fn-lbc))))
      (nth 15 (nth i (nth *fn-lbc-directory-store* fn-lbc))) nil))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
   '(fn-lbc-directory-field fn-lbc-directory-store fn-lbc-directory-count-is-len
     fn-lbc-directory-get-body-ok fn-lbc-directory$a-get-body-ok)))))

(defthm fn-lbc-directory-field-raw-head-length-by-definition
 (equal (fn-lbc-directory-field :raw-head-length i fn-lbc)
  (if (and (natp i) (< i (len (nth *fn-lbc-directory-store* fn-lbc))))
      (nth 16 (nth i (nth *fn-lbc-directory-store* fn-lbc))) nil))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
   '(fn-lbc-directory-field fn-lbc-directory-store fn-lbc-directory-count-is-len
     fn-lbc-directory-get-raw-head-length fn-lbc-directory$a-get-raw-head-length)))))

(defthm fn-lbc-directory-field-framed-by-definition
 (equal (fn-lbc-directory-field :framed i fn-lbc)
  (if (and (natp i) (< i (len (nth *fn-lbc-directory-store* fn-lbc))))
      (nth 17 (nth i (nth *fn-lbc-directory-store* fn-lbc))) nil))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
   '(fn-lbc-directory-field fn-lbc-directory-store fn-lbc-directory-count-is-len
     fn-lbc-directory-get-framed fn-lbc-directory$a-get-framed)))))
