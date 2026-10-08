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

;; The constrained seams, attached: the log position F (any encodable tree) and
;; the frame trailer's words.
(defun pckh-f (configs recs) (declare (xargs :guard t) (ignore configs recs)) nil)
(defattach fn-pck-f pckh-f)
(defun pckh-trailer (p) (declare (xargs :guard t) (ignore p)) (list 11 22 33 44))
(defattach fn-cpl-trailer-words pckh-trailer)

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
; Real records, sequences consecutive from the fold seed (0, 1, ...).
(defun pckh-recs-from (first seed count)
  (declare (xargs :mode :program))
  (if (zp count) nil
    (cons (fn-record-make first (+ 1 first) 0 "<a@x>" (pckh-wide (+ seed first) 3000)
                          '("fn.test") "o" "s" "e" 1 5)
          (pckh-recs-from (+ 1 first) seed (- count 1)))))
(defconst *pckh-store0* (pckh-recs-from 0 1 300))
(defconst *pckh-d1* (pckh-recs-from 300 2 20))
(defconst *pckh-d2* (pckh-recs-from 320 3 20))
; Attachments are not callable in a defconst, hence functions.
(defun pckh-st0 () (declare (xargs :verify-guards nil)) (fn-pck-st-of (fn-pck-seed) *pckh-store0*))
(defun pckh-st1 () (declare (xargs :verify-guards nil)) (fn-pck-st-of (fn-pck-seed) (append *pckh-store0* *pckh-d1*)))

(defun pckh-full1 () (declare (xargs :verify-guards nil)) (len (fn-pck-pages nil (append *pckh-store0* *pckh-d1*))))
(defun pckh-full2 () (declare (xargs :verify-guards nil)) (len (fn-pck-pages nil (append *pckh-store0* *pckh-d1* *pckh-d2*))))
(defun pckh-dirty1 () (declare (xargs :verify-guards nil)) (len (cadr (fn-pck-publish-plan nil *pckh-store0* *pckh-d1*))))
(defun pckh-dirty2 () (declare (xargs :verify-guards nil)) (len (cadr (fn-pck-publish-plan nil (append *pckh-store0* *pckh-d1*) *pckh-d2*))))

(assert-event (and (equal (car (fn-pck-publish-plan nil *pckh-store0* *pckh-d1*)) :commit)
                   (equal (car (fn-pck-publish-plan nil (append *pckh-store0* *pckh-d1*) *pckh-d2*)) :commit)))
; red: a whole-image rewrite grows with the store; green: a publication writes K + delta pages.
(assert-event (and (fn-pck-sccb-listp (append *pckh-store0* *pckh-d1* *pckh-d2*) (fn-pck-seed))
                   (not (equal (pckh-st1) :bad))
                   (fn-pck-plen-okp (append *pckh-store0* *pckh-d1* *pckh-d2*))))
(assert-event (< (pckh-full1) (pckh-full2)))
(assert-event (<= (pckh-dirty1) (+ *fn-pck-root-pages* (fn-pck-delta-page-bound *pckh-d1* (fn-pck-plen *pckh-store0* 0) (pckh-st0)))))
(assert-event (<= (pckh-dirty2) (+ *fn-pck-root-pages* (fn-pck-delta-page-bound *pckh-d2* (fn-pck-plen (append *pckh-store0* *pckh-d1*) 0) (pckh-st1)))))
(assert-event (< (pckh-dirty2) (pckh-full2)))
(value-triple (cw "pages per publication: whole image ~x0 then ~x1; dirty ~x2 then ~x3~%"
                  (pckh-full1) (pckh-full2) (pckh-dirty1) (pckh-dirty2)))

; 5. The tail of dirty-at must come from page k = floor(cnt/2048).  Off by one
; page (the tail read from page k-1) is not adt-tp-dirty.
(defun pckh-iota (n)
  (declare (xargs :guard (natp n)))
  (if (zp n) nil (append (pckh-iota (1- n)) (list n))))

(defun pckh-wrong-tail-dirty (w n)
  (declare (xargs :guard t :verify-guards nil))
  ; the tail taken from page k-1 instead of page k
  (let* ((k (floor (len w) *pgs-page-words*))
         (tail (adt-tp-take (mod (len w) *pgs-page-words*) (nth (1- k) (adt-tp-pages w)))))
    (adt-tp-dirty-at (len w) tail n)))

(must-fail-checked
 (defthm pckh-dirty-at-from-previous-page
   (implies (and (true-listp w) (true-listp n) (< 1 (floor (len w) *pgs-page-words*)))
            (equal (pckh-wrong-tail-dirty w n) (adt-tp-dirty w n)))))

; The witness: a tape of 2 * 2048 + 5 words, appended with (9).  The right tail
; is words 4097..4101, which sit in page 2; page 1 holds 2049..2053 there.
(assert-event
 (let* ((w (pckh-iota 4101)))
   (and (equal (adt-tp-dirty-at (len w) (nthcdr 4096 w) '(9)) (adt-tp-dirty w '(9)))
        (not (equal (pckh-wrong-tail-dirty w '(9)) (adt-tp-dirty w '(9))))
        (equal (take 6 (cdar (adt-tp-dirty w '(9)))) '(4097 4098 4099 4100 4101 9))
        (equal (take 6 (cdar (pckh-wrong-tail-dirty w '(9)))) '(2049 2050 2051 2052 2053 9)))))

; 6. The open selection must see the log start.  The selection that ignores it
; (fn-pck-open-raw-selection, today's behaviour) can answer :checkpoint for a
; log that starts past the checkpoint's S.
(must-fail-checked
 (defthm pckh-raw-selection-retains
   (implies (equal (car (fn-pck-open-raw-selection filep disk r mode file count k)) :checkpoint)
            (fn-pck-log-retains log (cadr (fn-pck-open-raw-selection filep disk r mode file count k))))))

; The witness: a checkpoint of S = 2 records over a log that starts at 5.
(defun pckh-selection-of (s count k log)
  (let ((sel (fn-sco-select :ok s count k)))
    (if (and (equal (car sel) :checkpoint) (not (fn-pck-log-retains log (cadr sel))))
        (list :refused :log-past-checkpoint)
      sel)))
(assert-event
 (and (equal (fn-sco-select :ok 2 6 4) '(:checkpoint 2))
      (not (fn-pck-log-retains '(5 a) 2))
      (equal (pckh-selection-of 2 6 4 '(5 a)) '(:refused :log-past-checkpoint))
      (equal (pckh-selection-of 2 6 4 '(2 a b c d)) '(:checkpoint 2))))

; Recovery through the view with START > S is not the full recovery: the
; view of an S = 0 image (nothing checkpointed) over a log that starts at 1.
(defun pckh-ungated-recover-view (v file log configs frontier max-conns)
  (declare (xargs :guard t :verify-guards nil))
  (if (and v (consp log))
      (let ((c (fn-pck-capture-of-pages (cadr v) file)))
        (fn-ock-recover-extended
         (fn-sco-extend c configs (nthcdr (- (len (fn-sco-records c)) (nfix (car log))) (cdr log)))
         configs frontier max-conns))
    :fault))

(must-fail-checked
 (defthm pckh-ungated-recover-view-is-full
   (implies (and (true-listp recs) (true-listp suffix)
                 (fn-pck-recordsp configs recs) (fn-pck-root-fitsp configs recs) (fn-pck-resolvesp recs 0 file)
                 (consp log) (natp (car log))
                 (equal (nthcdr (car log) (append recs suffix)) (cdr log))
                 (equal v (list tx (fn-pck-pages configs recs))))
            (equal (pckh-ungated-recover-view v file log configs frontier max-conns)
                   (fn-ock-recover-full configs frontier (append recs suffix) max-conns)))))

(defthm pckh-recover-view-refuses-a-log-past-the-checkpoint
  (implies (and (consp log) (natp (car log))
                (< (len (fn-sco-records (fn-pck-capture-of-pages (cadr v) file))) (car log)))
           (equal (fn-pck-recover-view v file log configs frontier max-conns) :fault))
  :hints (("Goal" :in-theory (enable fn-pck-recover-view fn-pck-log-retains))))

; 7. The catalog root's write gate.  Writing always (the ungated plan) does not
; imply a carried catalog; with an overflow row the written root is not the
; catalog.
(defun pckh-ungated-catalog-plan (h s)
  (declare (xargs :guard t :verify-guards nil))
  (list :write (fn-pck-cat-pages h) s))

(must-fail-checked
 (defthm pckh-ungated-catalog-plan-writes-a-carried-catalog
   (implies (equal (car (pckh-ungated-catalog-plan h s)) :write)
            (fn-pck-carriedp h))))
