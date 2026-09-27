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
; or only grows the domain (books/served-catalog-join-steps.lisp).

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
