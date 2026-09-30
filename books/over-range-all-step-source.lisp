; Logical old range decomposition including absent/unsupported selections.
; Never a second executable provider or range locator.
(in-package "ACL2")
(include-book "served-range-source")

(local
 (defthm fn-obgs-selected-sequence-in-bounds
  (implies (fn-cnx-view-seq group k v fn-cat)
   (and (natp (fn-cnx-view-seq group k v fn-cat))
        (< (fn-cnx-view-seq group k v fn-cat) (fn-cat-count fn-cat))))
  :hints (("Goal" :in-theory
   (e/d (fn-cnx-view-seq)
        (fn-cat-group-number fn-cat-visible-at fn-cat-count-is-len))))))

(local
 (defthm fn-obgs-number-seq-shift-gen
   (implies (and (natp i) (natp j))
            (equal (fn-cat-number-seq g n c (+ i j))
                   (let ((r (fn-cat-number-seq g n c j)))
                     (and r (+ i r)))))
   :hints (("Goal" :induct (fn-cat-number-seq g n c j)))))

(local
 (defthm fn-obgs-number-seq-shift
   (implies (and (natp i) (syntaxp (not (equal i ''0))))
            (equal (fn-cat-number-seq g n c i)
                   (let ((r (fn-cat-number-seq g n c 0)))
                     (and r (+ i r)))))
   :hints (("Goal" :use ((:instance fn-obgs-number-seq-shift-gen (j 0)))
            :in-theory (disable fn-obgs-number-seq-shift-gen)))))

(local
 (defthm fn-obgs-number-seq-natp
   (implies (fn-cat-number-seq g n c 0)
            (and (natp (fn-cat-number-seq g n c 0))
                 (< (fn-cat-number-seq g n c 0) (len c))))
   :rule-classes nil))

(local
 (defthm fn-obgs-number-seq-type
   (implies (natp i)
            (or (null (fn-cat-number-seq g n c i))
                (natp (fn-cat-number-seq g n c i))))
   :rule-classes :type-prescription))

(local
 (defthm fn-obgs-nth-of-1+
   (implies (natp r)
            (equal (nth (+ 1 r) c) (nth r (cdr c))))))

(local
 (defthm fn-obgs-number-seq-binds
   (implies (fn-cat-number-seq g n c 0)
            (equal (fn-held-number-in g (nth (fn-cat-number-seq g n c 0) c)) n))
   :rule-classes nil
   :hints (("Goal" :induct (len c) :expand ((fn-cat-number-seq g n c 0))))))

(local
 (defthm fn-obgs-selected-number-binds
  (implies (fn-cnx-view-seq group k v fn-cat)
   (equal (fn-held-number-in group
             (fn-cat-at (fn-cnx-view-seq group k v fn-cat) fn-cat)) k))
  :hints (("Goal" :use ((:instance fn-obgs-number-seq-binds
                          (g group) (n k) (c fn-cat)))
   :in-theory (e/d (fn-cnx-view-seq)
    (fn-cat-group-number fn-cat-visible-at fn-held-number-in fn-cat-number-seq))))))

(defthm fn-ovw-lines-current-number-all-branches-unfolds
 (let* ((seq (fn-cnx-view-seq group k v fn-cat))
        (row (fn-cat-at seq fn-cat))
        (article (fn-scat-available-article group k v fn-arena fn-cat)))
  (implies (and (natp k) (natp hi) (<= k hi))
   (equal (fn-ovw-lines group k hi v fn-arena fn-cat)
    (if (and seq (posp k) (<= k *fn-nntp-max-article-number*)
             (fn-scat-msgid-idp (fn-record-msgid row))
             (consp article)
             (not (fn-nntp-article-tombstonep article fn-arena))
             (fn-nov-okp (fn-nov-overview article fn-arena)))
        (cons (fn-nov-line k (fn-nov-overview article fn-arena))
              (fn-ovw-lines group (+ 1 k) hi v fn-arena fn-cat))
      (fn-ovw-lines group (+ 1 k) hi v fn-arena fn-cat)))))
 :rule-classes nil
 :hints (("Goal" :do-not-induct t
  :use (fn-obgs-selected-number-binds fn-obgs-selected-sequence-in-bounds)
  :expand ((fn-cnx-range-aux group k hi v fn-cat)
           (:free (rest) (fn-scat-range-keep group
                          (cons (fn-cnx-view-seq group k v fn-cat) rest) fn-cat))
           (:free (rest) (fn-nov-lines-for-numbers-cat group (cons k rest)
                           v fn-arena fn-cat)))
  :in-theory (e/d (fn-ovw-lines)
   (fn-cnx-view-seq fn-cnx-range-aux fn-scat-range-keep
    fn-cat-at fn-cat-count fn-held-number-in fn-scat-msgid-idp
    fn-record-msgid fn-scat-available-article fn-nov-line fn-nov-overview
    fn-nntp-article-tombstonep fn-nov-okp fn-nov-lines-for-numbers-cat)))))
