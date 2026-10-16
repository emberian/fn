; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-pool-establishment")

(defthm fn-lbc-nov-field-tomb-by-definition
 (equal (fn-lbc-nov-field :tomb i fn-lbc)
  (if (and (natp i) (< i (len (nth *fn-lbc-nov-store* fn-lbc))))
      (nth 0 (nth i (nth *fn-lbc-nov-store* fn-lbc))) nil))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
   '(fn-lbc-nov-field fn-lbc-nov-store fn-lbc-nov-count-is-len
     fn-lbc-nov-get-tomb fn-lbc-nov$a-get-tomb)))))

(defthm fn-lbc-nov-field-ok-by-definition
 (equal (fn-lbc-nov-field :ok i fn-lbc)
  (if (and (natp i) (< i (len (nth *fn-lbc-nov-store* fn-lbc))))
      (nth 1 (nth i (nth *fn-lbc-nov-store* fn-lbc))) nil))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
   '(fn-lbc-nov-field fn-lbc-nov-store fn-lbc-nov-count-is-len
     fn-lbc-nov-get-ok fn-lbc-nov$a-get-ok)))))

(defthm fn-lbc-nov-field-subject-start-by-definition
 (equal (fn-lbc-nov-field :subject-start i fn-lbc)
  (if (and (natp i) (< i (len (nth *fn-lbc-nov-store* fn-lbc))))
      (nth 2 (nth i (nth *fn-lbc-nov-store* fn-lbc))) nil))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
   '(fn-lbc-nov-field fn-lbc-nov-store fn-lbc-nov-count-is-len
     fn-lbc-nov-get-subject-start fn-lbc-nov$a-get-subject-start)))))

(defthm fn-lbc-nov-field-subject-length-by-definition
 (equal (fn-lbc-nov-field :subject-length i fn-lbc)
  (if (and (natp i) (< i (len (nth *fn-lbc-nov-store* fn-lbc))))
      (nth 3 (nth i (nth *fn-lbc-nov-store* fn-lbc))) nil))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
   '(fn-lbc-nov-field fn-lbc-nov-store fn-lbc-nov-count-is-len
     fn-lbc-nov-get-subject-length fn-lbc-nov$a-get-subject-length)))))

(defthm fn-lbc-nov-field-from-start-by-definition
 (equal (fn-lbc-nov-field :from-start i fn-lbc)
  (if (and (natp i) (< i (len (nth *fn-lbc-nov-store* fn-lbc))))
      (nth 4 (nth i (nth *fn-lbc-nov-store* fn-lbc))) nil))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
   '(fn-lbc-nov-field fn-lbc-nov-store fn-lbc-nov-count-is-len
     fn-lbc-nov-get-from-start fn-lbc-nov$a-get-from-start)))))

(defthm fn-lbc-nov-field-from-length-by-definition
 (equal (fn-lbc-nov-field :from-length i fn-lbc)
  (if (and (natp i) (< i (len (nth *fn-lbc-nov-store* fn-lbc))))
      (nth 5 (nth i (nth *fn-lbc-nov-store* fn-lbc))) nil))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
   '(fn-lbc-nov-field fn-lbc-nov-store fn-lbc-nov-count-is-len
     fn-lbc-nov-get-from-length fn-lbc-nov$a-get-from-length)))))

(defthm fn-lbc-nov-field-date-start-by-definition
 (equal (fn-lbc-nov-field :date-start i fn-lbc)
  (if (and (natp i) (< i (len (nth *fn-lbc-nov-store* fn-lbc))))
      (nth 6 (nth i (nth *fn-lbc-nov-store* fn-lbc))) nil))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
   '(fn-lbc-nov-field fn-lbc-nov-store fn-lbc-nov-count-is-len
     fn-lbc-nov-get-date-start fn-lbc-nov$a-get-date-start)))))

(defthm fn-lbc-nov-field-date-length-by-definition
 (equal (fn-lbc-nov-field :date-length i fn-lbc)
  (if (and (natp i) (< i (len (nth *fn-lbc-nov-store* fn-lbc))))
      (nth 7 (nth i (nth *fn-lbc-nov-store* fn-lbc))) nil))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
   '(fn-lbc-nov-field fn-lbc-nov-store fn-lbc-nov-count-is-len
     fn-lbc-nov-get-date-length fn-lbc-nov$a-get-date-length)))))

(defthm fn-lbc-nov-field-msgid-start-by-definition
 (equal (fn-lbc-nov-field :msgid-start i fn-lbc)
  (if (and (natp i) (< i (len (nth *fn-lbc-nov-store* fn-lbc))))
      (nth 8 (nth i (nth *fn-lbc-nov-store* fn-lbc))) nil))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
   '(fn-lbc-nov-field fn-lbc-nov-store fn-lbc-nov-count-is-len
     fn-lbc-nov-get-msgid-start fn-lbc-nov$a-get-msgid-start)))))

(defthm fn-lbc-nov-field-msgid-length-by-definition
 (equal (fn-lbc-nov-field :msgid-length i fn-lbc)
  (if (and (natp i) (< i (len (nth *fn-lbc-nov-store* fn-lbc))))
      (nth 9 (nth i (nth *fn-lbc-nov-store* fn-lbc))) nil))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
   '(fn-lbc-nov-field fn-lbc-nov-store fn-lbc-nov-count-is-len
     fn-lbc-nov-get-msgid-length fn-lbc-nov$a-get-msgid-length)))))

(defthm fn-lbc-nov-field-references-start-by-definition
 (equal (fn-lbc-nov-field :references-start i fn-lbc)
  (if (and (natp i) (< i (len (nth *fn-lbc-nov-store* fn-lbc))))
      (nth 10 (nth i (nth *fn-lbc-nov-store* fn-lbc))) nil))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
   '(fn-lbc-nov-field fn-lbc-nov-store fn-lbc-nov-count-is-len
     fn-lbc-nov-get-references-start fn-lbc-nov$a-get-references-start)))))

(defthm fn-lbc-nov-field-references-length-by-definition
 (equal (fn-lbc-nov-field :references-length i fn-lbc)
  (if (and (natp i) (< i (len (nth *fn-lbc-nov-store* fn-lbc))))
      (nth 11 (nth i (nth *fn-lbc-nov-store* fn-lbc))) nil))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
   '(fn-lbc-nov-field fn-lbc-nov-store fn-lbc-nov-count-is-len
     fn-lbc-nov-get-references-length fn-lbc-nov$a-get-references-length)))))

(defthm fn-lbc-membership-field-group-start-by-definition
 (equal (fn-lbc-membership-field :group-start i fn-lbc)
  (if (and (natp i) (< i (len (nth *fn-lbc-membership-store* fn-lbc))))
      (nth 0 (nth i (nth *fn-lbc-membership-store* fn-lbc))) nil))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
   '(fn-lbc-membership-field fn-lbc-membership-store fn-lbc-memberships-count-is-len
     fn-lbc-memberships-get-group-start fn-lbc-memberships$a-get-group-start)))))

(defthm fn-lbc-membership-field-group-length-by-definition
 (equal (fn-lbc-membership-field :group-length i fn-lbc)
  (if (and (natp i) (< i (len (nth *fn-lbc-membership-store* fn-lbc))))
      (nth 1 (nth i (nth *fn-lbc-membership-store* fn-lbc))) nil))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
   '(fn-lbc-membership-field fn-lbc-membership-store fn-lbc-memberships-count-is-len
     fn-lbc-memberships-get-group-length fn-lbc-memberships$a-get-group-length)))))

(defthm fn-lbc-membership-field-number-by-definition
 (equal (fn-lbc-membership-field :number i fn-lbc)
  (if (and (natp i) (< i (len (nth *fn-lbc-membership-store* fn-lbc))))
      (nth 2 (nth i (nth *fn-lbc-membership-store* fn-lbc))) nil))
 :hints (("Goal" :do-not-induct t :in-theory
  (union-theories (theory 'ground-zero)
   '(fn-lbc-membership-field fn-lbc-membership-store fn-lbc-memberships-count-is-len
     fn-lbc-memberships-get-number fn-lbc-memberships$a-get-number)))))
