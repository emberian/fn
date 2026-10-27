; Derived constructor support; local algebra does not escape this book.
(in-package "ACL2")
(include-book "catalog-columns-slot-type-preservation")

(defthm fn-lbc-word-of-slot-insert-other-field
 (implies (and (not (equal field :flags)))
  (equal (fn-lbc-word field read-i (fn-lbc-slot-insert j slot fuel fn-lbc))
         (fn-lbc-word field read-i fn-lbc)))
 :hints (("Goal" :induct (fn-lbc-slot-insert j slot fuel fn-lbc) :in-theory
  (union-theories (theory 'minimal-theory) '(fn-lbc-slot-insert fn-lbc-word-of-slot-put-other-field)))))

(defthm fn-lbc-escape-of-slot-insert-other-key
 (implies (and (not (equal field :msgid-slot)))
  (equal (fn-lbc-escape read-i field (fn-lbc-slot-insert j slot fuel fn-lbc))
         (fn-lbc-escape read-i field fn-lbc)))
 :hints (("Goal" :induct (fn-lbc-slot-insert j slot fuel fn-lbc) :in-theory
  (union-theories (theory 'minimal-theory) '(fn-lbc-slot-insert fn-lbc-escape-of-slot-put-other-key)))))

(defthm fn-lbc-value-of-slot-insert-other-field
 (implies (and (not (equal field :msgid-slot)) (not (equal field :flags)))
  (equal (fn-lbc-value read-i field (fn-lbc-slot-insert j slot fuel fn-lbc))
         (fn-lbc-value read-i field fn-lbc)))
 :hints (("Goal" :induct (fn-lbc-slot-insert j slot fuel fn-lbc) :in-theory
  (union-theories (theory 'minimal-theory) '(fn-lbc-slot-insert fn-lbc-value-of-slot-put-other-field)))))

(defthm fn-lbc-directory-value-of-slot-insert-other-field
 (implies (and (not (equal field :msgid-slot)))
  (equal (fn-lbc-directory-value read-i field (fn-lbc-slot-insert j slot fuel fn-lbc))
         (fn-lbc-directory-value read-i field fn-lbc)))
 :hints (("Goal" :induct (fn-lbc-slot-insert j slot fuel fn-lbc) :in-theory
  (union-theories (theory 'minimal-theory) '(fn-lbc-slot-insert fn-lbc-directory-value-of-slot-put-other-field)))))

(defthm fn-lbc-bit-0-of-slot-insert
 (implies (fn-lbc-p fn-lbc)
  (equal (fn-lbc-flag read-i 0 (fn-lbc-slot-insert j slot fuel fn-lbc))
         (fn-lbc-flag read-i 0 fn-lbc)))
 :hints (("Goal" :induct (fn-lbc-slot-insert j slot fuel fn-lbc) :in-theory
  (union-theories (theory 'minimal-theory)
   '(fn-lbc-slot-insert fn-lbc-bit-0-of-slot-put fn-lbc-p-of-slot-put)))))

(defthm fn-lbc-bit-1-of-slot-insert
 (implies (fn-lbc-p fn-lbc)
  (equal (fn-lbc-flag read-i 1 (fn-lbc-slot-insert j slot fuel fn-lbc))
         (fn-lbc-flag read-i 1 fn-lbc)))
 :hints (("Goal" :induct (fn-lbc-slot-insert j slot fuel fn-lbc) :in-theory
  (union-theories (theory 'minimal-theory)
   '(fn-lbc-slot-insert fn-lbc-bit-1-of-slot-put fn-lbc-p-of-slot-put)))))

(defthm fn-lbc-bit-2-of-slot-insert
 (implies (fn-lbc-p fn-lbc)
  (equal (fn-lbc-flag read-i 2 (fn-lbc-slot-insert j slot fuel fn-lbc))
         (fn-lbc-flag read-i 2 fn-lbc)))
 :hints (("Goal" :induct (fn-lbc-slot-insert j slot fuel fn-lbc) :in-theory
  (union-theories (theory 'minimal-theory)
   '(fn-lbc-slot-insert fn-lbc-bit-2-of-slot-put fn-lbc-p-of-slot-put)))))

(defthm fn-lbc-bit-4-of-slot-insert
 (implies (fn-lbc-p fn-lbc)
  (equal (fn-lbc-flag read-i 4 (fn-lbc-slot-insert j slot fuel fn-lbc))
         (fn-lbc-flag read-i 4 fn-lbc)))
 :hints (("Goal" :induct (fn-lbc-slot-insert j slot fuel fn-lbc) :in-theory
  (union-theories (theory 'minimal-theory)
   '(fn-lbc-slot-insert fn-lbc-bit-4-of-slot-put fn-lbc-p-of-slot-put)))))

(defthm fn-lbc-bit-5-of-slot-insert
 (implies (fn-lbc-p fn-lbc)
  (equal (fn-lbc-flag read-i 5 (fn-lbc-slot-insert j slot fuel fn-lbc))
         (fn-lbc-flag read-i 5 fn-lbc)))
 :hints (("Goal" :induct (fn-lbc-slot-insert j slot fuel fn-lbc) :in-theory
  (union-theories (theory 'minimal-theory)
   '(fn-lbc-slot-insert fn-lbc-bit-5-of-slot-put fn-lbc-p-of-slot-put)))))

(defthm fn-lbc-word-of-index-slots-other-field
 (implies (and (not (equal field :flags)))
  (equal (fn-lbc-word field read-i (fn-lbc-index-slots j n fn-lbc))
         (fn-lbc-word field read-i fn-lbc)))
 :hints (("Goal" :induct (fn-lbc-index-slots j n fn-lbc) :in-theory
  (union-theories (theory 'minimal-theory) '(fn-lbc-index-slots fn-lbc-word-of-slot-insert-other-field)))))

(defthm fn-lbc-escape-of-index-slots-other-key
 (implies (and (not (equal field :msgid-slot)))
  (equal (fn-lbc-escape read-i field (fn-lbc-index-slots j n fn-lbc))
         (fn-lbc-escape read-i field fn-lbc)))
 :hints (("Goal" :induct (fn-lbc-index-slots j n fn-lbc) :in-theory
  (union-theories (theory 'minimal-theory) '(fn-lbc-index-slots fn-lbc-escape-of-slot-insert-other-key)))))

(defthm fn-lbc-value-of-index-slots-other-field
 (implies (and (not (equal field :msgid-slot)) (not (equal field :flags)))
  (equal (fn-lbc-value read-i field (fn-lbc-index-slots j n fn-lbc))
         (fn-lbc-value read-i field fn-lbc)))
 :hints (("Goal" :induct (fn-lbc-index-slots j n fn-lbc) :in-theory
  (union-theories (theory 'minimal-theory) '(fn-lbc-index-slots fn-lbc-value-of-slot-insert-other-field)))))

(defthm fn-lbc-directory-value-of-index-slots-other-field
 (implies (and (not (equal field :msgid-slot)))
  (equal (fn-lbc-directory-value read-i field (fn-lbc-index-slots j n fn-lbc))
         (fn-lbc-directory-value read-i field fn-lbc)))
 :hints (("Goal" :induct (fn-lbc-index-slots j n fn-lbc) :in-theory
  (union-theories (theory 'minimal-theory) '(fn-lbc-index-slots fn-lbc-directory-value-of-slot-insert-other-field)))))

(defthm fn-lbc-bit-0-of-index-slots
 (implies (fn-lbc-p fn-lbc)
  (equal (fn-lbc-flag read-i 0 (fn-lbc-index-slots j n fn-lbc))
         (fn-lbc-flag read-i 0 fn-lbc)))
 :hints (("Goal" :induct (fn-lbc-index-slots j n fn-lbc) :in-theory
  (union-theories (theory 'minimal-theory)
   '(fn-lbc-index-slots fn-lbc-bit-0-of-slot-insert fn-lbc-p-of-slot-insert)))))

(defthm fn-lbc-bit-1-of-index-slots
 (implies (fn-lbc-p fn-lbc)
  (equal (fn-lbc-flag read-i 1 (fn-lbc-index-slots j n fn-lbc))
         (fn-lbc-flag read-i 1 fn-lbc)))
 :hints (("Goal" :induct (fn-lbc-index-slots j n fn-lbc) :in-theory
  (union-theories (theory 'minimal-theory)
   '(fn-lbc-index-slots fn-lbc-bit-1-of-slot-insert fn-lbc-p-of-slot-insert)))))

(defthm fn-lbc-bit-2-of-index-slots
 (implies (fn-lbc-p fn-lbc)
  (equal (fn-lbc-flag read-i 2 (fn-lbc-index-slots j n fn-lbc))
         (fn-lbc-flag read-i 2 fn-lbc)))
 :hints (("Goal" :induct (fn-lbc-index-slots j n fn-lbc) :in-theory
  (union-theories (theory 'minimal-theory)
   '(fn-lbc-index-slots fn-lbc-bit-2-of-slot-insert fn-lbc-p-of-slot-insert)))))

(defthm fn-lbc-bit-4-of-index-slots
 (implies (fn-lbc-p fn-lbc)
  (equal (fn-lbc-flag read-i 4 (fn-lbc-index-slots j n fn-lbc))
         (fn-lbc-flag read-i 4 fn-lbc)))
 :hints (("Goal" :induct (fn-lbc-index-slots j n fn-lbc) :in-theory
  (union-theories (theory 'minimal-theory)
   '(fn-lbc-index-slots fn-lbc-bit-4-of-slot-insert fn-lbc-p-of-slot-insert)))))

(defthm fn-lbc-bit-5-of-index-slots
 (implies (fn-lbc-p fn-lbc)
  (equal (fn-lbc-flag read-i 5 (fn-lbc-index-slots j n fn-lbc))
         (fn-lbc-flag read-i 5 fn-lbc)))
 :hints (("Goal" :induct (fn-lbc-index-slots j n fn-lbc) :in-theory
  (union-theories (theory 'minimal-theory)
   '(fn-lbc-index-slots fn-lbc-bit-5-of-slot-insert fn-lbc-p-of-slot-insert)))))
