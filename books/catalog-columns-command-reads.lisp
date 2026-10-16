; Command reads use the resident number runs and overview/summary columns.
(in-package "ACL2")
(include-book "catalog-columns-served")
(include-book "def-loop")

(local (defthm fn-lbcc-escape-select
 (implies (and (natp start) (natp i) (<= start i)
               (< i (fn-lbc-count fn-lbc)) (fn-lbc-escape-cellsp start fn-lbc))
          (alistp (fn-lbc-escape-store-get i fn-lbc)))
 :hints (("Goal" :induct (fn-lbc-escape-cellsp start fn-lbc)
 :in-theory (e/d (fn-lbc-escape-cellsp)
  (fn-lbc-p fn-lbc-count fn-lbc-escape-store-get))))))

(local (defthm fn-lbcc-escape-select-zero
 (implies (and (natp i) (< i (fn-lbc-count fn-lbc))
               (fn-lbc-escape-cellsp 0 fn-lbc))
          (alistp (fn-lbc-escape-store-get i fn-lbc)))
 :hints (("Goal" :use ((:instance fn-lbcc-escape-select (start 0)))
 :in-theory (theory 'ground-zero)))))
(local (defthm fn-lbcc-visible-bounds
 (implies (fn-lbc-visiblep i v fn-lbc) (and (natp i) (< i (fn-lbc-count fn-lbc))))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(fn-lbc-visiblep))))))
(local (defthm fn-lbcc-escape-select-visible
 (implies (and (fn-lbc-visiblep i v fn-lbc) (fn-lbc-escape-cellsp 0 fn-lbc))
          (alistp (fn-lbc-escape-store-get i fn-lbc)))
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
 '(fn-lbc-visiblep fn-lbcc-escape-select-zero))))))

(defun fn-lbc-command-row (group number v fn-lbc)
 (declare (xargs :stobjs fn-lbc :guard (fn-lbc-escape-cellsp 0 fn-lbc)
                 :verify-guards nil))
 (let ((i (fn-lbc-number-get group number fn-lbc)))
  (and (posp number) (<= number *fn-nntp-max-article-number*)
       (natp i) (< i (fn-lbc-count fn-lbc))
       (fn-lbc-visiblep i v fn-lbc)
       (let ((escaped-nov (fn-lbc-escape i :nov fn-lbc)))
        (if escaped-nov
            (and (fn-hnov-p (fn-ag-cdr escaped-nov))
                 (not (fn-hnov-tomb (fn-ag-cdr escaped-nov))))
          (and (not (equal (fn-lbc-directory-value i :nov-length fn-lbc) 0))
               (not (fn-lbc-nov-field :tomb
                      (fn-lbc-directory-value i :nov-start fn-lbc) fn-lbc)))))
       (fn-nntp-article-idp (fn-lbc-id-article i fn-lbc)) i)))

(verify-guards fn-lbc-command-row
 :hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
  '(fn-lbcc-escape-select-zero fn-lbcc-escape-select-visible
    fn-lbcc-visible-bounds natp eqlablep)))))

(defthm fn-lbc-command-row-is-bounded
 (implies (fn-lbc-command-row group number v fn-lbc)
  (and (natp (fn-lbc-command-row group number v fn-lbc))
       (< (fn-lbc-command-row group number v fn-lbc) (fn-lbc-count fn-lbc))))
 :hints (("Goal" :in-theory '(fn-lbc-command-row))))

(local (in-theory (disable fn-lbc-command-row fn-lbc-escape-cellsp fn-lbc-p)))

(def-loop fn-lbc-over-eligible (group v lo hi fn-lbc)
 :shape :step :over lo :stobjs fn-lbc
 :done (not (and (natp lo) (natp hi) (<= lo hi)))
 :let ((i (fn-lbc-command-row group lo v fn-lbc)))
 :skip (not i) :body i :next (+ 1 lo) :skip-next (+ 1 lo)
 :measure (nfix (- (+ 1 (nfix hi)) (nfix lo)))
 :guard (and (natp lo) (natp hi) (fn-lbc-escape-cellsp 0 fn-lbc))
 :guard-hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
  '(natp eqlablep)))))

(def-loop fn-lbc-over (group v lo hi fn-lbc)
 :shape :step :over lo :stobjs fn-lbc
 :done (not (and (natp lo) (natp hi) (<= lo hi)))
 :let ((i (fn-lbc-command-row group lo v fn-lbc)))
 :skip (not i) :body (cons lo (fn-lbc-render-nov i fn-lbc))
 :next (+ 1 lo) :skip-next (+ 1 lo)
 :measure (nfix (- (+ 1 (nfix hi)) (nfix lo)))
 :guard (and (natp lo) (natp hi) (fn-lbc-escape-cellsp 0 fn-lbc))
 :guard-hints (("Goal" :use ((:instance fn-lbc-command-row-is-bounded (number lo)))
 :in-theory (union-theories (theory 'ground-zero)
  '(fn-lbcc-escape-select-zero natp eqlablep)))))

; Each LIST item reads one maintained summary, without reconstructing an article row.
(def-loop fn-lbc-list (groups fn-lbc)
 :shape :map :over groups :elt group :stobjs fn-lbc
 :body (cons group (fn-lbc-live-summary group fn-lbc))
 :guard t :guard-hints (("Goal" :in-theory (disable fn-lbc-live-summary))))

(defun fn-lbc-group-live (group fn-lbc)
 (declare (xargs :stobjs fn-lbc :guard t))
 (fn-lbc-live-summary group fn-lbc))

; The reply filters the dense requested range through resident availability columns.
(def-loop fn-lbc-listgroup (group v lo hi fn-lbc)
 :shape :step :over lo :stobjs fn-lbc
 :done (not (and (natp lo) (natp hi) (<= lo hi)))
 :let ((i (fn-lbc-command-row group lo v fn-lbc)))
 :skip (not i) :body lo :next (+ 1 lo) :skip-next (+ 1 lo)
 :measure (nfix (- (+ 1 (nfix hi)) (nfix lo)))
 :guard (and (natp lo) (natp hi) (fn-lbc-escape-cellsp 0 fn-lbc))
 :guard-hints (("Goal" :in-theory (union-theories (theory 'ground-zero)
  '(natp eqlablep)))))

; The requested array positions, before the command's visibility filter.
; LISTGROUP's emitted reply is fn-lbc-listgroup above; withdrawals still cost
; a candidate read and are intentionally present in this cost-domain list.
(def-loop fn-lbc-listgroup-requested-numbers (lo hi)
 :shape :step :over lo
 :done (not (and (natp lo) (natp hi) (<= lo hi)))
 :skip nil :body lo :next (+ 1 lo) :skip-next (+ 1 lo)
 :measure (nfix (- (+ 1 (nfix hi)) (nfix lo)))
 :guard (and (natp lo) (natp hi))
 :guard-hints (("Goal" :in-theory (union-theories (theory 'ground-zero) '(natp)))))

(defun fn-lbc-listgroup-numbers (group v lo hi fn-lbc)
 (declare (ignore group v fn-lbc)
          (xargs :stobjs fn-lbc :guard (and (natp lo) (natp hi))))
 (fn-lbc-listgroup-requested-numbers lo hi))
