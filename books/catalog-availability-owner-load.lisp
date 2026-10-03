; Recovery/reclaim catalog loader: classify legacy availability once.
(in-package "ACL2")
(include-book "catalog")
(include-book "catalog-availability-load")
(include-book "msgid-index")

(local (defthm fn-sca-load-held-p-of-with-withdrawn
  (implies (and (fn-held-p h) (fn-held-withdrawnp w))
           (fn-held-p (fn-held-with-withdrawn h w)))
  :hints (("Goal" :in-theory (enable fn-held-p fn-held-with-withdrawn)))))

; E over the rows.  The guard's domain: every row of the catalog's shape is
; a held record (the store's history is store events: fn-sf-record-valuesp,
; which implies it: fn-sca-held-rowsp-of-record-values).  The body dispatches
; on the digest-free shape fn-cat-rowp and never executes fn-held-p.
; A composite row (a signed article's atomic acceptance) by its shape: the
; held row inside it is a catalog row.  The loader dispatches on shapes and
; never executes fn-held-p or fn-hstxa-p (their delta checks digest).
(defun fn-sca-composite-shapep (r)
  (declare (xargs :guard t))
  (and (consp r) (eq (car r) :hstxa) (fn-cat-rowp (fn-hstxa-held r))))

(defun fn-sca-held-rowsp (rows)
  (declare (xargs :guard t))
  (if (consp rows)
      (and (or (not (fn-cat-rowp (car rows))) (fn-held-p (car rows)))
           (or (not (fn-sca-composite-shapep (car rows)))
               (fn-held-p (fn-hstxa-held (car rows))))
           (fn-sca-held-rowsp (cdr rows)))
    t))

; One row: an article row (by the digest-free shape) committed, visible when
; the view shows its Message-ID, else withdrawn at its own index as
; fn-cat-load-row-hidden commits it; a composite row's held article row
; committed the same way (a signed article: signed-post's red, the catalog
; had skipped it); any other event skipped.
(defun fn-sca-load-held-row (r view-index fn-cat)
  (declare (xargs :stobjs fn-cat
                  :guard (and (or (not (fn-cat-rowp r)) (fn-held-p r))
                              (or (not (fn-sca-composite-shapep r))
                                  (fn-held-p (fn-hstxa-held r))))
                  :guard-hints (("Goal" :in-theory (e/d (fn-held-withdrawnp) (fn-held-p))
                                 :use ((:instance fn-sca-load-held-p-of-with-withdrawn
                                                  (h r) (w (cons (fn-cat-count fn-cat) 0)))
                                       (:instance fn-sca-load-held-p-of-with-withdrawn
                                                  (h (fn-hstxa-held r))
                                                  (w (cons (fn-cat-count fn-cat) 0))))))))
  (let ((h (cond ((fn-cat-rowp r) r)
                 ((fn-sca-composite-shapep r) (fn-hstxa-held r))
                 (t nil))))
    (if h
        (if (fn-midx-lookup (fn-record-msgid h) view-index)
            (fn-cat-commit h fn-cat)
          (fn-cat-commit (fn-held-with-withdrawn h (cons (fn-cat-count fn-cat) 0)) fn-cat))
      fn-cat)))

(defun fn-sca-load-held-rows-from (rows view-index fn-cat)
  (declare (xargs :stobjs fn-cat :guard (fn-sca-held-rowsp rows)))
  (if (consp rows)
      (let ((fn-cat (fn-sca-load-held-row (car rows) view-index fn-cat)))
        (fn-sca-load-held-rows-from (cdr rows) view-index fn-cat))
    fn-cat))

; Recovery/reclaim folds classify legacy rows once from the same arena.
; The older held-row fold remains a raw-identity proof helper.
(defun fn-sca-load-held-available-row (r view-index fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat)
                  :guard (and (or (not (fn-cat-rowp r)) (fn-held-p r))
                              (or (not (fn-sca-composite-shapep r))
                                  (fn-held-p (fn-hstxa-held r))))
                  :guard-hints (("Goal" :in-theory
                    (disable fn-held-p fn-cat-prepare-row-availability fn-cat-rowp)))))
  (let ((h (cond ((fn-cat-rowp r) r)
                 ((fn-sca-composite-shapep r) (fn-hstxa-held r))
                 (t nil))))
    (if h
        (fn-sca-load-held-row (fn-cat-prepare-row-availability h fn-arena) view-index fn-cat)
      fn-cat)))

(defun fn-sca-load-held-available-from (rows view-index fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard (fn-sca-held-rowsp rows)))
  (if (consp rows)
      (let ((fn-cat (fn-sca-load-held-available-row (car rows) view-index fn-arena fn-cat)))
        (fn-sca-load-held-available-from (cdr rows) view-index fn-arena fn-cat))
    fn-cat))

(defun fn-sca-load-held-rows (rows view-index fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :guard (fn-sca-held-rowsp rows)))
  (let ((fn-cat (fn-cat-clear fn-cat)))
    (fn-sca-load-held-available-from rows view-index fn-arena fn-cat)))

