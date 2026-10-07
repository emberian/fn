; Teeth and measurement for books/paged-checkpoint-host.lisp.
;
;   1. compaction: a floor taken as the MAX of the two slots' S is not the
;      keystone's floor: the same statement fails, and the witness is a log
;      whose older slot loses records;
;   2. publication: "every plan commits" fails (the refusal is real);
;   3. the catalog gate: adopting without the S match is not the load;
;   4. red-before / green-after (model level): the pages one publication
;      writes (fn-pck-dirty) against the pages of the whole image (what the
;      schema-3 file rewrote each time), over two publications of a growing
;      store.

(in-package "ACL2")
(include-book "../../books/paged-checkpoint-host")
(include-book "must-fail-checked")
(include-book "std/testing/assert-bang" :dir :system)

; 1. The max floor.
(defun pckh-max-floor (sa sb) (max (fn-pck-slot-s sa) (fn-pck-slot-s sb)))

(must-fail-checked
 (defthm pckh-compact-keeps-both-slots-at-max
   (implies (and (true-listp all) (consp log) (natp (car log)) (true-listp (cdr log))
                 (equal (nthcdr (car log) all) (cdr log))
                 (<= (car log) (pckh-max-floor sa sb))
                 (<= (pckh-max-floor sa sb) (len all)))
            (let ((log2 (fn-pck-compact-log log (pckh-max-floor sa sb))))
              (and (implies (natp sa) (fn-pck-log-retains log2 sa))
                   (implies (natp sb) (fn-pck-log-retains log2 sb)))))))

; The witness: slots at S = 1 and S = 3 over a log holding records 0..2.
(assert-event
 (let* ((log (cons 0 '(a b c)))
        (at-max (fn-pck-compact-log log (pckh-max-floor 1 3)))
        (at-min (fn-pck-compact-log log (fn-pck-compact-floor 1 3))))
   (and (not (fn-pck-log-retains at-max 1))        ; the older slot lost b, c
        (fn-pck-log-retains at-min 1)
        (fn-pck-log-retains at-min 3)
        (equal (cdr at-min) '(b c))
        (equal (fn-pck-compact-floor nil 5) 0)    ; an empty slot: nothing dropped
        (equal (fn-pck-compact-log log 0) log))))

; 2. Every plan commits.
(must-fail-checked
 (defthm pckh-plan-always-commits
   (equal (car (fn-pck-publish-plan configs prefix delta)) :commit)))

; 3. Adopt without the gate.
(defun-nx pckh-ungated-open (cat-s cat-pages recs idx)
  (declare (ignorable cat-s recs idx))
  (fn-pck-held-of-crow-rows (fn-crow-of-pages cat-pages)))

(must-fail-checked
 (defthm pckh-ungated-open-is-the-load
   (implies (and (true-listp recs) (natp cat-s) (<= cat-s (len recs))
                 (fn-cat-rowsp h) (fn-pck-carriedp h)
                 (equal h (fn-sca-load-held-rows-from (take cat-s recs) idx nil)))
            (equal (pckh-ungated-open cat-s (fn-pck-cat-pages h) recs idx)
                   (fn-sca-load-held-rows-from recs idx nil)))))

; 4. Pages written per publication, over two publications of a growing store.
(defun pckh-wide (seed n)
  (declare (xargs :guard (and (natp seed) (natp n))))
  (if (zp n) nil (cons (mod (* (+ seed n) 2654435761) 251) (pckh-wide (+ seed 7) (- n 1)))))
(defun pckh-recs (seed count)
  (declare (xargs :guard (and (natp seed) (natp count))))
  (if (zp count) nil (cons (pckh-wide (* seed count) 3000) (pckh-recs seed (- count 1)))))
(defconst *pckh-store0* (pckh-recs 1 300))
(defconst *pckh-d1* (pckh-recs 2 20))
(defconst *pckh-d2* (pckh-recs 3 20))

(defconst *pckh-full1* (len (fn-pck-pages nil (append *pckh-store0* *pckh-d1*))))
(defconst *pckh-full2* (len (fn-pck-pages nil (append *pckh-store0* *pckh-d1* *pckh-d2*))))
(defconst *pckh-dirty1* (len (cadr (fn-pck-publish-plan nil *pckh-store0* *pckh-d1*))))
(defconst *pckh-dirty2* (len (cadr (fn-pck-publish-plan nil (append *pckh-store0* *pckh-d1*) *pckh-d2*))))

(assert-event (and (equal (car (fn-pck-publish-plan nil *pckh-store0* *pckh-d1*)) :commit)
                   (equal (car (fn-pck-publish-plan nil (append *pckh-store0* *pckh-d1*) *pckh-d2*)) :commit)))
; red: a whole-image rewrite grows with the store; green: a publication writes K + delta pages.
(assert-event (< *pckh-full1* *pckh-full2*))
(assert-event (<= *pckh-dirty1* (+ *fn-pck-root-pages* (fn-pck-delta-page-bound *pckh-d1*))))
(assert-event (<= *pckh-dirty2* (+ *fn-pck-root-pages* (fn-pck-delta-page-bound *pckh-d2*))))
(assert-event (< *pckh-dirty2* *pckh-full2*))
(value-triple (cw "pages per publication: whole image ~x0 then ~x1; dirty ~x2 then ~x3~%"
                  *pckh-full1* *pckh-full2* *pckh-dirty1* *pckh-dirty2*))
