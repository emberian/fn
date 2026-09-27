; served-catalog-join-number.lisp -- the catalog's rows against the store's
; acceptance (lane sca-join-2, 2026-09-27; PRF-302's row equation).
;
; The acceptance (books/acceptance.lisp) installs an article with the
; memberships fn-allocate-memberships allocates at the group watermarks; the
; catalog (books/catalog.lisp fn-cat-commit) numbers a committed row one
; past each group's high over ALL its rows.  They agree when every
; watermark of the allocation domain is one past the catalog's high in that
; group and no row binds a number outside the domain.  With the articles
; equation that is fn-scj-acc-rowsp: the acceptance's articles are the
; catalog's rows read as articles, newest first, withdrawn or not.
;
; It is established at every open (books/served-catalog-join-open.lisp),
; preserved by the article install (fn-scj-acc-rowsp-of-install, below) and
; by every step that keeps the acceptance's articles, watermarks and domain
; or only grows the domain (the configuration record:
; fn-scj-acc-rowsp-of-apply-config; the owner steps over fn-ocfg-step are
; OPEN, planning/evidence/sca-join-2026-09-27.md).

(in-package "ACL2")

(include-book "served-catalog-join")

; A row as an acceptance article (fn-cat-row-article's body over a row).
(defun fn-scj-row-art (h)
  (declare (xargs :guard t))
  (fn-make-article (fn-record-msgid h)
                   (fn-record-payload h)
                   (fn-record-groups h)
                   (fn-held-numbers h)
                   t
                   (fn-record-stamp h)))

; Every row as an article, oldest first; the acceptance holds them newest
; first (fn-install-pending conses).
(defun fn-scj-arts-map (c)
  (declare (xargs :guard t))
  (if (consp c)
      (cons (fn-scj-row-art (car c)) (fn-scj-arts-map (cdr c)))
    nil))

(defun fn-scj-rows-arts (c)
  (declare (xargs :guard t))
  (rev (fn-scj-arts-map c)))

; Every watermark of NAMES is one past the catalog's high in that group.
(defun fn-scj-nexts-matchp (names nexts c)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp names)
      (and (equal (fn-next-number (car names) nexts)
                  (+ 1 (fn-cat-group-high (car names) c)))
           (fn-scj-nexts-matchp (cdr names) nexts c))
    t))

; Every number a row binds is in a group of NAMES.
(defun fn-scj-keys-inp (numbers names)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp numbers)
      (and (or (not (consp (car numbers)))
               (member-equal (car (car numbers)) names))
           (fn-scj-keys-inp (cdr numbers) names))
    t))

(defun fn-scj-rows-keys-inp (c names)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp c)
      (and (fn-scj-keys-inp (fn-held-numbers (car c)) names)
           (fn-scj-rows-keys-inp (cdr c) names))
    t))

; THE ROW RELATION.  The acceptance's articles are the rows as articles,
; its watermarks one past the rows' highs, and no row outside its domain.
(defun-nx fn-scj-acc-rowsp (acc c)
  (and (equal (fn-state-articles acc) (fn-scj-rows-arts c))
       (fn-scj-nexts-matchp (fn-state-groups acc) (fn-state-nexts acc) c)
       (fn-scj-rows-keys-inp c (fn-state-groups acc))))

(defthm fn-scj-fields-of-with-numbers
  (and (equal (fn-held-numbers (fn-held-with-numbers h n)) n)
       (equal (fn-record-msgid (fn-held-with-numbers h n)) (fn-record-msgid h))
       (equal (fn-record-groups (fn-held-with-numbers h n)) (fn-record-groups h))
       (equal (fn-record-payload (fn-held-with-numbers h n)) (fn-record-payload h))
       (equal (fn-record-stamp (fn-held-with-numbers h n)) (fn-record-stamp h)))
  :hints (("Goal" :in-theory (enable fn-held-with-numbers fn-record-internals fn-held-internals))))

; -----------------------------------------------------------------------------
; The watermarks against the rows' highs.

(defthm fn-scj-next-of-bump-same
  (implies (not (equal (fn-next-number g nexts) 0))
           (equal (fn-next-number g (fn-bump-number g nexts))
                  (+ 1 (fn-next-number g nexts))))
  :hints (("Goal" :in-theory (enable fn-next-number fn-bump-number))))

(defthm fn-scj-next-of-bump-other
  (implies (not (equal a b))
           (equal (fn-next-number a (fn-bump-number b nexts))
                  (fn-next-number a nexts)))
  :hints (("Goal" :in-theory (enable fn-next-number fn-bump-number))))

(defthm fn-scj-nexts-matchp-of-bump-other
  (implies (not (member-equal g names))
           (equal (fn-scj-nexts-matchp names (fn-bump-number g nexts) c)
                  (fn-scj-nexts-matchp names nexts c))))

(defthm fn-scj-nexts-matchp-member
  (implies (and (fn-scj-nexts-matchp names nexts c) (member-equal g names))
           (equal (fn-next-number g nexts) (+ 1 (fn-cat-group-high g c)))))

(defthm fn-scj-nexts-matchp-of-subset
  (implies (and (fn-scj-nexts-matchp names nexts c) (fn-subsetp gs names))
           (fn-scj-nexts-matchp gs nexts c))
  :hints (("Goal" :induct (fn-subsetp gs names) :in-theory (enable fn-subsetp))))

(defthm fn-scj-allocate-is-assign-numbers
  (implies (and (fn-scj-nexts-matchp gs nexts c) (fn-no-duplicatesp gs))
           (equal (fn-allocate-memberships gs nexts) (fn-cat-assign-numbers gs c)))
  :hints (("Goal" :induct (fn-allocate-memberships gs nexts)
           :in-theory (enable fn-allocate-memberships fn-no-duplicatesp))))

(defthm fn-scj-group-high-of-append
  (equal (fn-cat-group-high g (append c d))
         (max (fn-cat-group-high g c) (fn-cat-group-high g d))))

(defthm fn-scj-assoc-of-assign-numbers
  (equal (fn-cat-assoc g (fn-cat-assign-numbers gs c))
         (if (member-equal g gs) (cons g (+ 1 (fn-cat-group-high g c))) nil)))

(defthm fn-scj-number-in-of-assign
  (equal (fn-held-number-in g (fn-cat-assign h c))
         (if (member-equal g (fn-record-groups h)) (+ 1 (fn-cat-group-high g c)) nil))
  :hints (("Goal" :in-theory (enable fn-held-number-in fn-cat-assign))))

(local (defthm fn-scj-member-not-member-differ
  (implies (and (member-equal g x) (not (member-equal a x)))
           (not (equal g a)))
  :rule-classes :forward-chaining))

(defthm fn-scj-next-of-advance
  (implies (and (fn-no-duplicatesp gs)
                (implies (member-equal g gs) (not (equal (fn-next-number g nexts) 0))))
           (equal (fn-next-number g (fn-advance-nexts gs nexts))
                  (if (member-equal g gs) (+ 1 (fn-next-number g nexts)) (fn-next-number g nexts))))
  :hints (("Goal" :induct (fn-advance-nexts gs nexts)
           :in-theory (e/d (fn-advance-nexts fn-no-duplicatesp) (fn-next-number fn-bump-number)))))

(defthm fn-scj-nexts-matchp-of-install
  (implies (and (fn-scj-nexts-matchp names nexts c)
                (fn-scj-nexts-matchp (fn-record-groups h) nexts c)
                (fn-no-duplicatesp (fn-record-groups h)))
           (fn-scj-nexts-matchp names (fn-advance-nexts (fn-record-groups h) nexts)
                                (append c (list (fn-cat-assign h c)))))
  :hints (("Goal" :induct (fn-scj-nexts-matchp names nexts c)
           :in-theory (disable fn-cat-assign))))

(defthm fn-scj-keys-inp-of-assign-numbers
  (implies (fn-subsetp gs names)
           (fn-scj-keys-inp (fn-cat-assign-numbers gs c) names))
  :hints (("Goal" :in-theory (enable fn-subsetp))))

(defthm fn-scj-rows-keys-inp-of-append
  (equal (fn-scj-rows-keys-inp (append c d) names)
         (and (fn-scj-rows-keys-inp c names) (fn-scj-rows-keys-inp d names))))

(defthm fn-scj-arts-map-of-append
  (equal (fn-scj-arts-map (append c d)) (append (fn-scj-arts-map c) (fn-scj-arts-map d))))

(defthm fn-scj-rows-arts-of-commit
  (equal (fn-scj-rows-arts (fn-cat-commit h c))
         (cons (fn-scj-row-art (fn-cat-assign h c)) (fn-scj-rows-arts c)))
  :hints (("Goal" :in-theory (e/d (fn-cat-commit-is-append) (fn-cat-assign fn-scj-row-art)))))

; -----------------------------------------------------------------------------
; The install.

(defthm fn-scj-row-art-of-assign
  (equal (fn-scj-row-art (fn-cat-assign h c))
         (fn-make-article (fn-record-msgid h) (fn-record-payload h) (fn-record-groups h)
                          (fn-cat-assign-numbers (fn-record-groups h) c) t (fn-record-stamp h)))
  :hints (("Goal" :in-theory (enable fn-cat-assign))))

(defthm fn-scj-rows-arts-of-snoc
  (equal (fn-scj-rows-arts (append c (list r)))
         (cons (fn-scj-row-art r) (fn-scj-rows-arts c))))

(defthm fn-scj-numbers-of-assign
  (equal (fn-held-numbers (fn-cat-assign h c))
         (fn-cat-assign-numbers (fn-record-groups h) c))
  :hints (("Goal" :in-theory (enable fn-cat-assign))))

; KEYSTONE (the row relation at an install).  An acceptance related to the
; catalog, that prepares the article of row H (its Message-ID, handle,
; groups and stamp) and installs it, is related to the catalog that commits
; H: the article the acceptance installs is the committed row read as an
; article, numbers included (fn-scj-allocate-is-assign-numbers).
(defthm fn-scj-acc-rowsp-of-install
  (let ((s2 (fn-accept-prepare s generation (fn-record-msgid h) (fn-record-payload h)
                               (fn-record-groups h) (fn-record-stamp h))))
    (implies (and (fn-scj-acc-rowsp s c)
                  (not (equal s2 s)))
             (fn-scj-acc-rowsp (fn-install-pending s2) (fn-cat-commit h c))))
  :hints (("Goal" :in-theory (e/d (fn-scj-acc-rowsp fn-accept-prepare fn-install-pending
                                   fn-article-from-pending fn-selection-validp
                                   fn-cat-commit-is-append)
                                  (fn-cat-assign fn-scj-rows-arts fn-scj-row-art))
           :use ((:instance fn-scj-nexts-matchp-of-subset (names (fn-state-groups s))
                            (nexts (fn-state-nexts s)) (gs (fn-record-groups h)))))))

(defthm fn-scj-fields-of-with-withdrawn
  (and (equal (fn-held-numbers (fn-held-with-withdrawn h w)) (fn-held-numbers h))
       (equal (fn-record-msgid (fn-held-with-withdrawn h w)) (fn-record-msgid h))
       (equal (fn-record-groups (fn-held-with-withdrawn h w)) (fn-record-groups h))
       (equal (fn-record-payload (fn-held-with-withdrawn h w)) (fn-record-payload h))
       (equal (fn-record-stamp (fn-held-with-withdrawn h w)) (fn-record-stamp h))
       (equal (fn-record-sequence (fn-held-with-withdrawn h w)) (fn-record-sequence h)))
  :hints (("Goal" :in-theory (enable fn-held-with-withdrawn fn-record-internals fn-held-internals))))

; The same for a row committed withdrawn (a hidden row at the load, R1 at
; the finish): the relation reads no withdrawal.
(defthm fn-scj-acc-rowsp-of-install-withdrawn
  (let ((s2 (fn-accept-prepare s generation (fn-record-msgid h) (fn-record-payload h)
                               (fn-record-groups h) (fn-record-stamp h))))
    (implies (and (fn-scj-acc-rowsp s c)
                  (not (equal s2 s)))
             (fn-scj-acc-rowsp (fn-install-pending s2)
                               (fn-cat-commit (fn-held-with-withdrawn h w) c))))
  :hints (("Goal" :in-theory (disable fn-scj-acc-rowsp fn-accept-prepare fn-install-pending
                                      fn-cat-commit-is-append fn-held-with-withdrawn)
           :use ((:instance fn-scj-acc-rowsp-of-install (h (fn-held-with-withdrawn h w)))))))
