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


; Proof-only carried invariant. No served command evaluates these walks.
(defun fn-cat-rows-availability-decidedp (rows)
  (declare (xargs :guard t))
  (if (consp rows)
      (and (fn-cat-row-facts-decidedp (car rows))
           (fn-cat-rows-availability-decidedp (cdr rows)))
    t))

(defun-nx fn-cat-availability-decidedp (fn-cat)
  (fn-cat-rows-availability-decidedp fn-cat))

(defun-nx fn-sca-load-availability-ready-p (rows fn-arena)
  (if (consp rows)
      (let ((h (cond ((fn-cat-rowp (car rows)) (car rows))
                     ((fn-sca-composite-shapep (car rows)) (fn-hstxa-held (car rows)))
                     (t nil))))
        (and (or (not h) (fn-cat-row-facts-decidedp h)
                 (and (natp (fn-record-payload h))
                      (< (fn-record-payload h) (fn-arena-count fn-arena))))
             (fn-sca-load-availability-ready-p (cdr rows) fn-arena)))
    t))

(local (defthm fn-cat-decided-of-append
  (equal (fn-cat-rows-availability-decidedp (append a b))
         (and (fn-cat-rows-availability-decidedp a)
              (fn-cat-rows-availability-decidedp b)))))

(local (defthm fn-cat-decided-of-assign
  (equal (fn-cat-row-facts-decidedp (fn-cat-assign h c))
         (fn-cat-row-facts-decidedp h))
  :hints (("Goal" :in-theory
           (e/d (fn-cat-assign) (fn-held-with-numbers))))))

(defthm fn-cat-availability-decidedp-of-commit
  (implies (and (fn-cat-availability-decidedp fn-cat)
                (fn-cat-row-facts-decidedp h))
           (fn-cat-availability-decidedp (fn-cat-commit h fn-cat)))
  :hints (("Goal" :in-theory
           (e/d (fn-cat-availability-decidedp fn-cat-commit-is-append)
                (fn-cat-assign fn-held-with-numbers fn-cat-row-facts-decidedp)))))

(local (defthm fn-cat-prepare-keeps-decided
  (implies (fn-cat-row-facts-decidedp h)
           (equal (fn-cat-prepare-row-availability h fn-arena) h))
  :hints (("Goal" :in-theory (enable fn-cat-prepare-row-availability)))))

(local (defthm fn-cat-prepared-decided-if-ready
  (implies (or (fn-cat-row-facts-decidedp h)
               (and (natp (fn-record-payload h))
                    (< (fn-record-payload h) (fn-arena-count fn-arena))))
           (fn-cat-row-facts-decidedp (fn-cat-prepare-row-availability h fn-arena)))
  :hints (("Goal" :use ((:instance fn-cat-prepare-row-availability-decided))
           :in-theory (disable fn-cat-prepare-row-availability
                               fn-cat-row-facts-decidedp fn-areNA-count-is-len)))))

(local (defthm fn-sca-availability-decidedp-of-load-held-row
  (implies (and (fn-cat-availability-decidedp fn-cat)
                (fn-cat-rowp r)
                (fn-cat-row-facts-decidedp r))
           (fn-cat-availability-decidedp (fn-sca-load-held-row r view-index fn-cat)))
  :hints (("Goal" :in-theory
           (e/d (fn-sca-load-held-row fn-sca-composite-shapep)
                (fn-cat-availability-decidedp fn-cat-row-facts-decidedp
                 fn-cat-rowp fn-cat-commit fn-cat-commit-is-append fn-midx-lookup fn-held-with-withdrawn fn-cat-p-is-rowsp
                 fn-cat-count-is-len))))))

(local (defthm fn-sca-availability-decidedp-of-load-available-row
  (implies (and (fn-cat-availability-decidedp fn-cat)
                (fn-sca-held-rowsp (list r))
                (fn-sca-load-availability-ready-p (list r) fn-arena))
           (fn-cat-availability-decidedp
             (fn-sca-load-held-available-row r view-index fn-arena fn-cat)))
  :hints (("Goal" :in-theory
           (e/d (fn-sca-load-held-available-row fn-sca-load-availability-ready-p fn-sca-held-rowsp)
                (fn-cat-availability-decidedp fn-cat-row-facts-decidedp fn-cat-rowp
                 fn-sca-composite-shapep fn-cat-prepare-row-availability
                 fn-sca-load-held-row fn-hstxa-held))))))

(defthm fn-sca-load-held-available-from-keeps-decidedp
  (implies (and (fn-cat-availability-decidedp fn-cat)
                (fn-sca-held-rowsp rows)
                (fn-sca-load-availability-ready-p rows fn-arena))
           (fn-cat-availability-decidedp
             (fn-sca-load-held-available-from rows view-index fn-arena fn-cat)))
  :hints (("Goal" :induct (fn-sca-load-held-available-from rows view-index fn-arena fn-cat)
           :in-theory
           (e/d (fn-sca-load-held-available-from fn-sca-load-availability-ready-p fn-sca-held-rowsp)
                (fn-cat-availability-decidedp fn-sca-load-held-available-row fn-cat-rowp
                 fn-sca-composite-shapep fn-cat-row-facts-decidedp fn-cat-prepare-row-availability)))))

(local (defthm fn-cat-empty-availability-decidedp
  (fn-cat-availability-decidedp nil)))

; Actual public recovery/reclaim entry establishes carried classification.
; Ready is a producer condition, never a runtime command guard.
(defthm fn-sca-load-held-rows-establishes-availability-decidedp
  (implies (and (fn-sca-held-rowsp rows)
                (fn-sca-load-availability-ready-p rows fn-arena))
           (fn-cat-availability-decidedp
             (fn-sca-load-held-rows rows view-index fn-arena fn-cat)))
  :hints (("Goal" :use ((:instance fn-sca-load-held-available-from-keeps-decidedp
                                  (fn-cat nil)))
           :in-theory
           (e/d (fn-sca-load-held-rows)
                (fn-cat-availability-decidedp fn-cat-rows-availability-decidedp
                 fn-sca-load-held-available-from fn-sca-load-availability-ready-p
                 fn-sca-held-rowsp fn-sca-load-held-available-from-keeps-decidedp)))))

(local (defthm fn-cat-decided-at
  (implies (and (fn-cat-rows-availability-decidedp rows)
                (natp i) (< i (len rows)))
           (fn-cat-row-facts-decidedp (nth i rows)))))

(local (defthm fn-cat-decided-of-update-nth
  (implies (and (fn-cat-rows-availability-decidedp rows)
                (fn-cat-row-facts-decidedp h)
                (natp i) (< i (len rows)))
           (fn-cat-rows-availability-decidedp (update-nth i h rows)))
  :hints (("Goal" :induct (update-nth i h rows)
           :in-theory (disable fn-cat-row-facts-decidedp)))))

(defthm fn-cat-withdraw-keeps-availability-decidedp
  (implies (and (fn-cat-availability-decidedp fn-cat)
                (natp target) (< target (fn-cat-count fn-cat)))
           (fn-cat-availability-decidedp (fn-cat-withdraw target by fn-cat)))
  :hints (("Goal" :in-theory
           (e/d (fn-cat-availability-decidedp fn-cat-withdraw-is-mark fn-cat-mark-withdrawn)
                (fn-cat-row-facts-decidedp fn-held-with-withdrawn)))))

(defthm fn-cat-redecide-keeps-availability-decidedp
  (implies (and (fn-cat-availability-decidedp fn-cat)
                (natp seq) (< seq (fn-cat-count fn-cat)))
           (fn-cat-availability-decidedp (fn-cat-redecide seq context fn-cat)))
  :hints (("Goal" :in-theory
           (e/d (fn-cat-availability-decidedp fn-cat-redecide-is-update-nth)
                (fn-cat-row-facts-decidedp fn-held-with-context)))))

(defthm fn-cat-clear-establishes-availability-decidedp
  (and (fn-cat-availability-decidedp (fn-cat-clear fn-cat))
       (fn-cat-availability-decidedp (fn-cat-clear-keyed key fn-cat))))

(in-theory (disable fn-cat-availability-decidedp fn-cat-rows-availability-decidedp
                    fn-sca-load-availability-ready-p))

(local (defthm fn-cat-with-facts-held-shape
  (fn-held-shapep (fn-held-with-facts h facts))
  :hints (("Goal" :in-theory (enable fn-held-shapep fn-held-with-facts fn-held-make)))))

(defthm fn-cat-prepare-row-availability-keeps-cat-rowp
  (implies (fn-cat-rowp h)
           (fn-cat-rowp (fn-cat-prepare-row-availability h fn-arena)))
  :hints (("Goal" :in-theory
           (e/d (fn-cat-rowp fn-cat-prepare-row-availability)
                (fn-held-with-facts fn-held-facts-of)))))
