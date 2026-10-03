; Recovery availability facts refine rows without changing join metadata.
(in-package "ACL2")
(include-book "served-catalog-join-number")

(defun fn-scj-row-identity (h)
  (list (fn-record-sequence h) (fn-record-msgid h)
        (fn-record-payload h) (fn-record-groups h) (fn-record-stamp h)
        (fn-held-numbers h) (fn-held-withdrawn h)))

(defun fn-scj-catalog-identity (c)
  (if (consp c)
      (cons (fn-scj-row-identity (car c)) (fn-scj-catalog-identity (cdr c)))
    nil))

(defthm fn-scj-prepare-row-keeps-identity
  (equal (fn-scj-row-identity (fn-cat-prepare-row-availability h fn-arena))
         (fn-scj-row-identity h))
  :hints (("Goal" :in-theory (enable fn-scj-row-identity fn-cat-prepare-row-availability))))

(defthm fn-scj-identity-len
  (equal (len (fn-scj-catalog-identity c)) (len c)))

(defthm fn-scj-identity-of-append
  (equal (fn-scj-catalog-identity (append c d))
         (append (fn-scj-catalog-identity c) (fn-scj-catalog-identity d))))

(defthm fn-scj-identity-consp
  (equal (consp (fn-scj-catalog-identity c)) (consp c)))

(local (defun fn-scj-identity-pair-ind (c d)
  (if (and (consp c) (consp d))
      (fn-scj-identity-pair-ind (cdr c) (cdr d))
    (list c d))))

(defthm fn-scj-same-identity-high-ordered
  (implies (and (equal (fn-scj-catalog-identity c) (fn-scj-catalog-identity d))
                (syntaxp (lexorder c d)))
           (equal (fn-cat-group-high g c) (fn-cat-group-high g d)))
  :hints (("Goal" :induct (fn-scj-identity-pair-ind c d)
           :in-theory (enable fn-scj-row-identity fn-held-number-in))))

(defthm fn-scj-same-identity-numbers
  (implies (and (equal (fn-scj-catalog-identity c) (fn-scj-catalog-identity d))
                (syntaxp (lexorder c d)))
           (equal (fn-cat-assign-numbers gs c) (fn-cat-assign-numbers gs d))))

(defthm fn-scj-same-identity-assign
  (implies (and (equal (fn-scj-row-identity h) (fn-scj-row-identity k))
                (equal (fn-scj-catalog-identity c) (fn-scj-catalog-identity d))
                (syntaxp (lexorder (list h c) (list k d))))
           (equal (fn-scj-row-identity (fn-cat-assign h c))
                  (fn-scj-row-identity (fn-cat-assign k d))))
  :hints (("Goal" :in-theory (e/d (fn-scj-row-identity fn-cat-assign fn-held-with-numbers)
                                (fn-cat-assign-numbers fn-scj-catalog-identity))
           :use ((:instance fn-scj-same-identity-numbers (gs (fn-record-groups h)))))))

(defthm fn-scj-same-identity-commit
  (implies (and (equal (fn-scj-row-identity h) (fn-scj-row-identity k))
                (equal (fn-scj-catalog-identity c) (fn-scj-catalog-identity d))
                (syntaxp (lexorder (list h c) (list k d))))
           (equal (fn-scj-catalog-identity (fn-cat-commit h c))
                  (fn-scj-catalog-identity (fn-cat-commit k d))))
  :hints (("Goal" :in-theory (e/d (fn-cat-commit-is-append)
                                (fn-scj-row-identity fn-cat-assign))
           :use ((:instance fn-scj-same-identity-assign)))))

(defthm fn-scj-same-identity-withdrawn
  (implies (equal (fn-scj-row-identity h) (fn-scj-row-identity k))
           (equal (fn-scj-row-identity (fn-held-with-withdrawn h w))
                  (fn-scj-row-identity (fn-held-with-withdrawn k w))))
  :hints (("Goal" :in-theory (enable fn-scj-row-identity fn-held-with-withdrawn))))

(defthm fn-scj-same-identity-load-row
  (implies (and (equal (fn-scj-catalog-identity c) (fn-scj-catalog-identity d))
                (syntaxp (lexorder c d)))
           (equal (fn-scj-catalog-identity (fn-sca-load-held-available-row r idx fn-arena c))
                  (fn-scj-catalog-identity (fn-sca-load-held-row r idx d))))
  :hints (("Goal" :in-theory
           (e/d (fn-sca-load-held-available-row fn-sca-load-held-row)
                (fn-cat-commit-is-append fn-cat-assign fn-cat-prepare-row-availability
                 fn-cat-commit fn-scj-row-identity fn-scj-catalog-identity fn-midx-lookup
                 fn-scj-identity-len fn-scj-same-identity-commit fn-scj-same-identity-withdrawn))
           :use ((:instance fn-scj-identity-len)
                 (:instance fn-scj-identity-len (c d))
                 (:instance fn-scj-same-identity-commit (h (fn-cat-prepare-row-availability r fn-arena)) (k r))
                 (:instance fn-scj-same-identity-withdrawn (h (fn-cat-prepare-row-availability r fn-arena)) (k r) (w (cons (len c) 0)))
                 (:instance fn-scj-same-identity-commit (h (fn-held-with-withdrawn (fn-cat-prepare-row-availability r fn-arena) (cons (len c) 0))) (k (fn-held-with-withdrawn r (cons (len c) 0))))
                 (:instance fn-scj-same-identity-commit (h (fn-cat-prepare-row-availability (fn-hstxa-held r) fn-arena)) (k (fn-hstxa-held r)))
                 (:instance fn-scj-same-identity-withdrawn (h (fn-cat-prepare-row-availability (fn-hstxa-held r) fn-arena)) (k (fn-hstxa-held r)) (w (cons (len c) 0)))
                 (:instance fn-scj-same-identity-commit (h (fn-held-with-withdrawn (fn-cat-prepare-row-availability (fn-hstxa-held r) fn-arena) (cons (len c) 0))) (k (fn-held-with-withdrawn (fn-hstxa-held r) (cons (len c) 0))))))))

(local (defun-nx fn-scj-load-identity-ind (rows idx fn-arena c d)
  (if (consp rows)
      (fn-scj-load-identity-ind (cdr rows) idx fn-arena
         (fn-sca-load-held-available-row (car rows) idx fn-arena c)
         (fn-sca-load-held-row (car rows) idx d))
    (list c d))))

(defthm fn-scj-available-load-keeps-identity
  (implies (and (equal (fn-scj-catalog-identity c) (fn-scj-catalog-identity d))
                (syntaxp (lexorder c d)))
           (equal (fn-scj-catalog-identity (fn-sca-load-held-available-from rows idx fn-arena c))
                  (fn-scj-catalog-identity (fn-sca-load-held-rows-from rows idx d))))
  :hints (("Goal" :induct (fn-scj-load-identity-ind rows idx fn-arena c d)
           :in-theory (disable fn-scj-catalog-identity fn-sca-load-held-available-row
                               fn-sca-load-held-row))))

(defthm fn-scj-same-identity-arts-map
  (implies (and (equal (fn-scj-catalog-identity c) (fn-scj-catalog-identity d))
                (syntaxp (lexorder c d)))
           (equal (fn-scj-arts-map c) (fn-scj-arts-map d)))
  :hints (("Goal" :induct (fn-scj-identity-pair-ind c d)
           :in-theory (enable fn-scj-row-identity fn-scj-row-art))))

(defthm fn-scj-same-identity-keys
  (implies (and (equal (fn-scj-catalog-identity c) (fn-scj-catalog-identity d))
                (syntaxp (lexorder c d)))
           (equal (fn-scj-rows-keys-inp c gs) (fn-scj-rows-keys-inp d gs)))
  :hints (("Goal" :induct (fn-scj-identity-pair-ind c d)
           :in-theory (enable fn-scj-row-identity))))

(defthm fn-scj-same-identity-nexts
  (implies (and (equal (fn-scj-catalog-identity c) (fn-scj-catalog-identity d))
                (syntaxp (lexorder c d)))
           (equal (fn-scj-nexts-matchp gs ns c) (fn-scj-nexts-matchp gs ns d))))

(defthm fn-scj-same-identity-acc-rowsp
  (implies (and (equal (fn-scj-catalog-identity c) (fn-scj-catalog-identity d))
                (syntaxp (lexorder c d)))
           (equal (fn-scj-acc-rowsp acc c) (fn-scj-acc-rowsp acc d)))
  :hints (("Goal" :in-theory (enable fn-scj-acc-rowsp fn-scj-rows-arts))))

(defthm fn-scj-same-identity-seqs
  (implies (and (equal (fn-scj-catalog-identity c) (fn-scj-catalog-identity d))
                (syntaxp (lexorder c d)))
           (equal (fn-scj-seqs-below c v) (fn-scj-seqs-below d v)))
  :hints (("Goal" :induct (fn-scj-identity-pair-ind c d)
           :in-theory (enable fn-scj-row-identity))))

(defthm fn-scj-same-identity-marks
  (implies (and (equal (fn-scj-catalog-identity c) (fn-scj-catalog-identity d))
                (syntaxp (lexorder c d)))
           (equal (fn-scj-marks-below c v) (fn-scj-marks-below d v)))
  :hints (("Goal" :induct (fn-scj-identity-pair-ind c d)
           :in-theory (enable fn-scj-row-identity))))

(local (defun fn-scj-nth-identity-ind (k c d)
  (if (and (not (zp k)) (consp c) (consp d))
      (fn-scj-nth-identity-ind (1- k) (cdr c) (cdr d))
    (list c d))))

(defthm fn-scj-same-identity-nth
  (implies (equal (fn-scj-catalog-identity c) (fn-scj-catalog-identity d))
           (equal (fn-scj-row-identity (nth k c)) (fn-scj-row-identity (nth k d))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-scj-nth-identity-ind k c d)
           :in-theory (enable nth fn-scj-catalog-identity))))

(defthm fn-scj-load-held-rows-keeps-raw-identity
  (equal (fn-scj-catalog-identity (fn-sca-load-held-rows rows idx fn-arena fn-cat))
         (fn-scj-catalog-identity (fn-sca-load-held-rows-from rows idx nil)))
  :hints (("Goal" :in-theory (e/d (fn-sca-load-held-rows fn-cat-clear create-fn-cat)
                 (fn-sca-load-held-available-from fn-sca-load-held-rows-from
                  fn-scj-catalog-identity fn-scj-available-load-keeps-identity))
           :use ((:instance fn-scj-available-load-keeps-identity (c nil) (d nil))))))

(defthm fn-scj-arts-map-of-available-load
  (equal (fn-scj-arts-map (fn-sca-load-held-rows rows idx fn-arena fn-cat))
         (fn-scj-arts-map (fn-sca-load-held-rows-from rows idx nil)))
  :hints (("Goal" :in-theory (disable fn-scj-arts-map fn-sca-load-held-rows
                fn-sca-load-held-rows-from fn-scj-catalog-identity
                fn-scj-load-held-rows-keeps-raw-identity fn-scj-same-identity-arts-map)
           :use ((:instance fn-scj-load-held-rows-keeps-raw-identity)
                 (:instance fn-scj-same-identity-arts-map (c (fn-sca-load-held-rows rows idx fn-arena fn-cat)) (d (fn-sca-load-held-rows-from rows idx nil)))))))

(defthm fn-scj-acc-rowsp-of-available-load
  (equal (fn-scj-acc-rowsp acc (fn-sca-load-held-rows rows idx fn-arena fn-cat))
         (fn-scj-acc-rowsp acc (fn-sca-load-held-rows-from rows idx nil)))
  :hints (("Goal" :in-theory (disable fn-scj-acc-rowsp fn-sca-load-held-rows
                fn-sca-load-held-rows-from fn-scj-catalog-identity
                fn-scj-load-held-rows-keeps-raw-identity fn-scj-same-identity-acc-rowsp)
           :use ((:instance fn-scj-load-held-rows-keeps-raw-identity)
                 (:instance fn-scj-same-identity-acc-rowsp (c (fn-sca-load-held-rows rows idx fn-arena fn-cat)) (d (fn-sca-load-held-rows-from rows idx nil)))))))

(defthm fn-scj-seqs-below-of-available-load
  (equal (fn-scj-seqs-below (fn-sca-load-held-rows rows idx fn-arena fn-cat) v)
         (fn-scj-seqs-below (fn-sca-load-held-rows-from rows idx nil) v))
  :hints (("Goal" :in-theory (disable fn-scj-seqs-below fn-sca-load-held-rows
                fn-sca-load-held-rows-from fn-scj-catalog-identity
                fn-scj-load-held-rows-keeps-raw-identity fn-scj-same-identity-seqs)
           :use ((:instance fn-scj-load-held-rows-keeps-raw-identity)
                 (:instance fn-scj-same-identity-seqs (c (fn-sca-load-held-rows rows idx fn-arena fn-cat)) (d (fn-sca-load-held-rows-from rows idx nil)))))))

(defthm fn-scj-marks-below-of-available-load
  (equal (fn-scj-marks-below (fn-sca-load-held-rows rows idx fn-arena fn-cat) v)
         (fn-scj-marks-below (fn-sca-load-held-rows-from rows idx nil) v))
  :hints (("Goal" :in-theory (disable fn-scj-marks-below fn-sca-load-held-rows
                fn-sca-load-held-rows-from fn-scj-catalog-identity
                fn-scj-load-held-rows-keeps-raw-identity fn-scj-same-identity-marks)
           :use ((:instance fn-scj-load-held-rows-keeps-raw-identity)
                 (:instance fn-scj-same-identity-marks (c (fn-sca-load-held-rows rows idx fn-arena fn-cat)) (d (fn-sca-load-held-rows-from rows idx nil)))))))

(defthm fn-scj-len-of-available-load
  (equal (len (fn-sca-load-held-rows rows idx fn-arena fn-cat))
         (len (fn-sca-load-held-rows-from rows idx nil)))
  :hints (("Goal" :in-theory (disable fn-sca-load-held-rows fn-sca-load-held-rows-from
                  fn-scj-catalog-identity fn-scj-identity-len
                  fn-scj-load-held-rows-keeps-raw-identity)
           :use ((:instance fn-scj-load-held-rows-keeps-raw-identity)
                 (:instance fn-scj-identity-len (c (fn-sca-load-held-rows rows idx fn-arena fn-cat)))
                 (:instance fn-scj-identity-len (c (fn-sca-load-held-rows-from rows idx nil)))))))

(in-theory (disable fn-scj-row-identity fn-scj-catalog-identity))
