; Witnesses for books/native-status-columns.lisp (lane scale-reads, PRF-368).
;
; REACHABLE: the owner fixture's store (store-reclaim-holders-tests: the
; completing owner's one article and the arena its journal interned), its
; payloads interned in handle order into a cleared arena, each committed to a
; cleared catalog as the open does (fn-cat-intern-list: facts decided from the
; sealed bytes) under the article's Message-ID.  F's antecedent is checked
; (fn-arena-p and every row faithful, over the catalog's rows as a value), the
; column was the one read, and the one walk equals the four counts: under the
; releasing rule (three reclaimable), with a signed article, and with the
; article's handle holding its tombstone (one reclaimed, freed octets > 0).
; CORRUPTED-STATE (F removed): the arena holds the tombstone, the row's
; column is the original article's; F fails (checked), the walk answers
; reclaimable where the counts answer reclaimed (the conclusion fails), and
; the keystones without F must fail.
(in-package "ACL2")
(include-book "../../books/native-status-columns")
(include-book "store-reclaim-holders-tests")

; Handle I's Message-ID: the article's whose payload it is, else a filler.
(defun nsct-msgid-at (i articles)
  (declare (xargs :verify-guards nil))
  (if (atom articles)
      "<nsct-filler@example.invalid>"
    (if (equal (fn-article-payload (car articles)) i)
        (fn-article-msgid (car articles))
      (nsct-msgid-at i (cdr articles)))))

(defun nsct-w (i payload articles)
  (declare (xargs :verify-guards nil))
  (fn-record-make i (+ 1 i) 0 (nsct-msgid-at i articles) payload '("fn.test")
                  "o" "s" "e" 1 5))

; The open: every payload interned in handle order and its row committed.
(defun nsct-load (payloads i articles fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil))
  (if (atom payloads)
      (mv fn-arena fn-cat)
    (mv-let (row fn-arena)
      (fn-cat-intern-list (nsct-w i (car payloads) articles) nil 0 fn-arena)
      (let ((fn-cat (fn-cat-commit row fn-cat)))
        (nsct-load (cdr payloads) (+ 1 i) articles fn-arena fn-cat)))))

(defun nsct-rows-from (i fn-cat)
  (declare (xargs :stobjs fn-cat :verify-guards nil
                  :measure (nfix (- (fn-cat-count fn-cat) (nfix i)))))
  (if (and (natp i) (< i (fn-cat-count fn-cat)))
      (cons (fn-cat-at i fn-cat) (nsct-rows-from (+ 1 i) fn-cat))
    nil))

; (F-arena F-rows column-read tally counts-and-classes words-col words)
(defun nsct-run (payloads rule s cfg fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil))
  (let* ((fn-arena (fn-arena-clear fn-arena))
         (fn-cat (fn-cat-clear fn-cat))
         (articles (fn-state-articles (fn-node-acceptance (fn-sn-node s)))))
    (mv-let (fn-arena fn-cat)
      (nsct-load payloads 0 articles fn-arena fn-cat)
      (mv (list (fn-arena-p fn-arena)
                (fn-scol-rows-okp (nsct-rows-from 0 fn-cat) fn-arena)
                (and (fn-scol-facts (car articles) fn-cat) t)
                (fn-nsc-store-tally rule 0 s fn-arena fn-cat)
                (append (fn-rcl-store-counts rule 0 s fn-arena)
                        (fn-rcl-store-classes rule 0 s fn-arena))
                (fn-nsc-reclaim-words s cfg '(nil nil (:full-replay :absent) nil)
                                      fn-arena fn-cat)
                (fn-nls-reclaim-words s cfg '(nil nil (:full-replay :absent) nil)
                                      fn-arena))
          fn-arena fn-cat))))

(defun nsct-agrees (r)
  (declare (xargs :verify-guards nil))
  (and (nth 0 r) (nth 1 r) (nth 2 r)
       (equal (nth 3 r) (nth 4 r))
       (equal (nth 5 r) (nth 6 r))))

; Releasing rule, caught-up consumer: three reclaimable, their stored octets.
(assert-event
 (mv-let (r fn-arena fn-cat)
   (nsct-run *rht-payloads* *rht-rule* *rht-caught* *rht-release-cfg* fn-arena fn-cat)
   (mv (and (nsct-agrees r)
            (equal (nth 3 r) (list 3 374 0 0 0 0 0))
            (equal (nth 5 r)
                   (append (fn-record-string-octets "reclaim rule=released-by-all-holders reclaimable=3")
                           (fn-record-string-octets " reclaimable-octets=374")
                           (fn-record-string-octets " held=0 reclaimed=0 freed-octets=0 signed=0 kept=0"))))
       fn-arena fn-cat))
 :stobjs-out '(nil fn-arena fn-cat))

; A signed article and a lagging consumer: signed 1, held 2.
(assert-event
 (mv-let (r fn-arena fn-cat)
   (nsct-run *rht-payloads* *rht-rule* *rht-signed-lag* *rht-release-cfg* fn-arena fn-cat)
   (mv (and (nsct-agrees r)
            (equal (nth 4 (nth 3 r)) 2) (equal (nth 5 (nth 3 r)) 1))
       fn-arena fn-cat))
 :stobjs-out '(nil fn-arena fn-cat))

; The article's handle holds its tombstone: the column's tomb flag counts it
; reclaimed, with the octets its tombstone records as freed.
(assert-event
 (mv-let (r fn-arena fn-cat)
   (nsct-run *rht-tomb-payloads* *rht-rule* *rht-caught* *rht-release-cfg* fn-arena fn-cat)
   (mv (and (nsct-agrees r)
            (equal (nth 0 (nth 3 r)) 2) (equal (nth 2 (nth 3 r)) 1)
            (< 0 (nth 3 (nth 3 r))))
       fn-arena fn-cat))
 :stobjs-out '(nil fn-arena fn-cat))

; CORRUPTED-STATE witness (F removed): the arena holds the tombstone at the
; article's handle, the row's decided column is the original bytes'.
(defun nsct-corrupt (fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil))
  (let* ((articles (fn-state-articles (fn-node-acceptance (fn-sn-node *rht-caught*))))
         (fn-arena (fn-arena-clear fn-arena))
         (fn-cat (fn-cat-clear fn-cat)))
    (mv-let (fn-arena fn-cat)
      (nsct-load *rht-payloads* 0 articles fn-arena fn-cat)
      ;; the same rows over an arena whose handle holds the tombstone
      (let* ((fn-arena (fn-arena-clear fn-arena))
             (fn-arena (fn-arn-seal-many *rht-tomb-payloads* fn-arena)))
        (mv (list (fn-arena-p fn-arena)
                  (fn-scol-rows-okp (nsct-rows-from 0 fn-cat) fn-arena)
                  (fn-nsc-store-tally *rht-rule* 0 *rht-caught* fn-arena fn-cat)
                  (append (fn-rcl-store-counts *rht-rule* 0 *rht-caught* fn-arena)
                          (fn-rcl-store-classes *rht-rule* 0 *rht-caught* fn-arena)))
            fn-arena fn-cat)))))

(assert-event
 (mv-let (r fn-arena fn-cat)
   (nsct-corrupt fn-arena fn-cat)
   (mv (and (nth 0 r)                                  ; the other conjunct holds
            (not (nth 1 r))                            ; F fails
            (equal (nth 0 (nth 2 r)) 3)                ; the column: three reclaimable
            (equal (nth 2 (nth 2 r)) 0)
            (equal (nth 0 (nth 3 r)) 2)                ; the bytes: one reclaimed
            (equal (nth 2 (nth 3 r)) 1)
            (not (equal (nth 2 r) (nth 3 r))))         ; the conclusion fails
       fn-arena fn-cat))
 :stobjs-out '(nil fn-arena fn-cat))

; The keystones without F.
(must-fail-checked
 (defthm nsct-verdict-without-f
   (equal (fn-nsc-verdict rule now h verdicts a fn-arena fn-cat)
          (fn-rcl-verdict-in rule now h verdicts a fn-arena))))
(must-fail-checked
 (defthm nsct-tally-without-f
   (equal (fn-nsc-store-tally rule now s fn-arena fn-cat)
          (append (fn-rcl-store-counts rule now s fn-arena)
                  (fn-rcl-store-classes rule now s fn-arena)))))
(must-fail-checked
 (defthm nsct-answer-without-f
   (equal (fn-nsc-answer-report kind profile oc cache obs min fn-arena fn-cat)
          (fn-nh-answer-report kind profile oc cache obs min fn-arena))))
