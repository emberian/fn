(in-package "ACL2")

(include-book "../../books/post-identity-source-cursor-source-stamp")

(defthm fn-psc-source-stamp-full-literal
 (let* ((xs (append *fn-inj-injection-date-field* (append (make-list 31 :initial-element 48) '(13 10 97))))
        (j (fn-pbb-strip-at *fn-inj-injection-date-field* 0 xs))
        (date (fn-oct-slice-list j (min (+ j 31) (len xs)) xs)))
  (and (natp 0) (<= 0 (len xs)) (true-listp xs) (not (equal j :no))
       (equal (fn-pbb-strip-at (fn-inj-injection-date-line date) 0 xs) 49)
       (equal (fn-pbb-strip-at (fn-inj-injection-date-line date) 0 xs)
              (fn-pbb-strip-at '(13 10) (+ j 31) xs))))
 :rule-classes nil)

(defthm fn-psc-source-stamp-short-literal
 (let* ((xs (append *fn-inj-injection-date-field* '(48 48 13 10)))
        (j (fn-pbb-strip-at *fn-inj-injection-date-field* 0 xs))
        (date (fn-oct-slice-list j (min (+ j 31) (len xs)) xs)))
  (and (natp 0) (<= 0 (len xs)) (true-listp xs) (not (equal j :no))
       (equal (fn-pbb-strip-at (fn-inj-injection-date-line date) 0 xs) :no)
       (equal (fn-pbb-strip-at (fn-inj-injection-date-line date) 0 xs)
              (fn-pbb-strip-at '(13 10) (+ j 31) xs))))
 :rule-classes nil)

(defthm fn-psc-source-stamp-bad-crlf-literal
 (let* ((xs (append *fn-inj-injection-date-field* (append (make-list 31 :initial-element 48) '(13 11))))
        (j (fn-pbb-strip-at *fn-inj-injection-date-field* 0 xs))
        (date (fn-oct-slice-list j (min (+ j 31) (len xs)) xs)))
  (and (natp 0) (<= 0 (len xs)) (true-listp xs) (not (equal j :no))
       (equal (fn-pbb-strip-at (fn-inj-injection-date-line date) 0 xs) :no)
       (equal (fn-pbb-strip-at (fn-inj-injection-date-line date) 0 xs)
              (fn-pbb-strip-at '(13 10) (+ j 31) xs))))
 :rule-classes nil)

(defthm fn-psc-source-stamp-eof-literal
 (let* ((xs (append *fn-inj-injection-date-field* nil))
        (j (fn-pbb-strip-at *fn-inj-injection-date-field* 0 xs))
        (date (fn-oct-slice-list j (min (+ j 31) (len xs)) xs)))
  (and (natp 0) (<= 0 (len xs)) (true-listp xs) (not (equal j :no))
       (equal (fn-pbb-strip-at (fn-inj-injection-date-line date) 0 xs) :no)
       (equal (fn-pbb-strip-at (fn-inj-injection-date-line date) 0 xs)
              (fn-pbb-strip-at '(13 10) (+ j 31) xs))))
 :rule-classes nil)

(defthm fn-psc-source-stamp-incoming-capture-literal
 (let* ((xs (append '(97) (make-list 31 :initial-element 48) '(13 10)))
        (incoming (if (equal :source-incoming :source-incoming) xs '(97)))
        (held (if (equal :source-incoming :source-held) xs nil))
        (c (fn-psc-set date 1 (fn-psc-begin :source-incoming (len xs) "<a@b>" '(:agent 0 1) (len incoming))))
        (d (fn-psc-model-source-literal-complete 32 '(13 10) :source-stamp-tail c incoming held)))
  (and (fn-psc-source-contextp c incoming held) (natp 1) (equal (fn-psc-get date c) 1)
       (fn-psc-get ok d) (fn-psc-source-date-contextp d incoming held)))
 :rule-classes nil)

(defthm fn-psc-source-stamp-held-capture-literal
 (let* ((xs (append '(97) (make-list 31 :initial-element 48) '(13 10)))
        (incoming (if (equal :source-held :source-incoming) xs '(97)))
        (held (if (equal :source-held :source-held) xs nil))
        (c (fn-psc-set date 1 (fn-psc-begin :source-held (len xs) "<a@b>" '(:agent 0 1) (len incoming))))
        (d (fn-psc-model-source-literal-complete 32 '(13 10) :source-stamp-tail c incoming held)))
  (and (fn-psc-source-contextp c incoming held) (natp 1) (equal (fn-psc-get date c) 1)
       (fn-psc-get ok d) (fn-psc-source-date-contextp d incoming held)))
 :rule-classes nil)
(defthm fn-psc-source-stamp-capture-equality-removal
 (let* ((held (append '(97) (make-list 31 :initial-element 48) '(13 10)))
        (incoming '(97))
        (c (fn-psc-set date 999 (fn-psc-begin :source-held (len held) "<a@b>" '(:agent 0 1) (len incoming))))
        (d (fn-psc-model-source-literal-complete 32 '(13 10) :source-stamp-tail c incoming held)))
  (and (fn-psc-source-contextp c incoming held) (natp 1)
       (not (equal (fn-psc-get date c) 1)) (fn-psc-get ok d)
       (not (fn-psc-source-date-contextp d incoming held))))
 :rule-classes nil)
