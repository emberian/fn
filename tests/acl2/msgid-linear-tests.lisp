; Witnesses for books/msgid-linear.lisp (lane msgid-linear-hash, PRF-1218).
; Prefix mpxl-.
;
; The tag is attached to a COLLIDING function (the salted FNV hash modulo
; 3), so Message-IDs share tags and the confirmation, not the hash,
; decides: the property the keystone claims.
;
; REACHABLE: the four-row history of msgid-pages-tests (two rows under
; <a@x>, one under <b@x>, an event that commits no article) placed by the
; writer `fn-mpxl-put' into a two-page table (N = 2, S = 0); the keystone's
; complete antecedent (fn-mpxl-tabp, fn-mpxl-faithful) is checked and its
; conclusion for a Message-ID with two records (in history order), one, and
; none.  THE SPLIT: the split of page 0 (ok; the table has three pages,
; S = 1; every mover's address under mod 4 is 2; the root's next split ends
; the round: N = 4, S = 0) keeps fn-mpxl-tabp and fn-mpxl-faithful and the
; reader's answers; the three refusals: a split whose movers exceed a page
; is refused with the table unchanged, and a put onto a full home page goes
; to the next page with the flag set (and is found), else is refused by
; name with the table unchanged.
; HYPOTHESIS-REMOVAL: fn-mpxl-faithful-from dropped (an entry missing:
; tabp and okp hold, the conclusion fails on completeness).  fn-mpxl-okp
; and fn-mpxl-tabp: no removal witness found (a seq at or past the rows
; names no held article and the confirmation drops it; a non-natural seq
; is not evaluable under nth's guard); their redundancy for the keystone
; is a proof task on layer A (`fn-mpx-confirm-is-the-records-for' carries
; fn-mpx-below-p and nat-listp), not a counterexample, so they stay.
(in-package "ACL2")
(include-book "../../books/msgid-linear")

; ---------------------------------------------------------------------------
; The tag for these tests: FNV-32 modulo 3 (collisions on purpose).

(defun mpxl-tag (msgid)
  (declare (xargs :guard t))
  (if (stringp msgid) (mod (fn-hist-hash msgid 0) 3) 0))

(defthm mpxl-tag-natp
  (natp (mpxl-tag msgid))
  :rule-classes :type-prescription)

(defattach fn-mpx-tag mpxl-tag)

; ---------------------------------------------------------------------------
; Fixtures: the history-columns rows (seq 0 <a@x>, 1 <b@x>, 2 a retention
; event, 3 <a@x> again) and the writer.

; The held constructor's arity follows the acceptance-binding field (16
; formals with it, 15 without: stage 0 of the 2026-10-01 design reverts it);
; the fixture is built for whichever the world has.
(make-event
 (if (equal (len (formals 'fn-held-make (w state))) 16)
     '(defun mpxl-held (seq msgid octets)
        (declare (xargs :verify-guards nil))
        (fn-held-make seq (+ 1 seq) 0 msgid seq '("fn.test") "o" "s" "e" 1 5
                      (fn-hf-make octets 14 2 nil)
                      (fn-hc-make (fn-stx-make-verdict :unverified nil 0) nil 0)
                      nil nil
                      (fn-ab-make :post-d25 (append *fn-ab-subject-head* (make-list 32 :initial-element 0)))))
   '(defun mpxl-held (seq msgid octets)
      (declare (xargs :verify-guards nil))
      (fn-held-make seq (+ 1 seq) 0 msgid seq '("fn.test") "o" "s" "e" 1 5
                    (fn-hf-make octets 14 2 nil)
                    (fn-hc-make (fn-stx-make-verdict :unverified nil 0) nil 0)
                    nil nil))))

(defconst *mpxl-a* (mpxl-held 0 "<a@x>" 100))
(defconst *mpxl-b* (mpxl-held 1 "<b@x>" 200))
(defconst *mpxl-ret* '(:not-an-article 2))
(defconst *mpxl-a2* (mpxl-held 3 "<a@x>" 300))
(assert-event (and (fn-held-p *mpxl-a*) (fn-held-p *mpxl-b*) (fn-held-p *mpxl-a2*)
                   (not (fn-held-p (fn-cei-event-article *mpxl-ret*)))))

(defconst *mpxl-rows* (list *mpxl-a* *mpxl-b* *mpxl-ret* *mpxl-a2*))

; An empty table of NPAGES pages (N = NPAGES, S = 0).
(defun mpxl-empty (npages)
  (declare (xargs :guard (posp npages)))
  (fn-mpxl-make (make-list npages :initial-element (cons nil nil)) npages 0))

; The writer: every held row's (tag . seq) placed by `fn-mpxl-put', in
; history order; (mv all-placed tab).
(defun mpxl-build (seq rows tab)
  (declare (xargs :verify-guards nil))
  (if (consp rows)
      (let ((rec (fn-cei-event-article (car rows))))
        (if (fn-held-p rec)
            (mv-let (placed tab)
              (fn-mpxl-put (mpxl-tag (fn-record-msgid rec)) seq tab)
              (mv-let (rest tab)
                (mpxl-build (+ 1 seq) (cdr rows) tab)
                (mv (and placed rest) tab)))
          (mpxl-build (+ 1 seq) (cdr rows) tab)))
    (mv t tab)))

(defconst *mpxl-table*
  (mv-let (placed tab) (mpxl-build 0 *mpxl-rows* (mpxl-empty 2))
    (and placed tab)))

; ---------------------------------------------------------------------------
; REACHABLE: the keystone's antecedent and conclusion.

(assert-event (fn-mpxl-tabp *mpxl-table*))
(assert-event (fn-mpxl-faithful *mpxl-table* *mpxl-rows*))
; two records under <a@x>, in history order
(assert-event (equal (fn-mpxl-records "<a@x>" *mpxl-table* *mpxl-rows*)
                     (list *mpxl-a* *mpxl-a2*)))
(assert-event (equal (fn-mpxl-records "<a@x>" *mpxl-table* *mpxl-rows*)
                     (fn-cei-article-records-for "<a@x>" *mpxl-rows*)))
(assert-event (equal (fn-mpxl-records "<a@x>" *mpxl-table* *mpxl-rows*)
                     (fn-hist$a-msgid-records "<a@x>" *mpxl-rows*)))
; one record
(assert-event (equal (fn-mpxl-records "<b@x>" *mpxl-table* *mpxl-rows*)
                     (list *mpxl-b*)))
; none: a Message-ID no row has (its tag collides with one that does)
(assert-event (equal (fn-mpxl-records "<z@x>" *mpxl-table* *mpxl-rows*) nil))
(assert-event (equal (fn-cei-article-records-for "<z@x>" *mpxl-rows*) nil))
(assert-event (< (mpxl-tag "<a@x>") 3))

; ---------------------------------------------------------------------------
; THE SPLIT: ok; the root advances; the movers landed on the new page; the
; keystone's antecedent and conclusion hold after it (the split-
; preservation keystone's witness), and again after the round ends.

(defconst *mpxl-split-1*
  (mv-let (ok tab) (fn-mpxl-split *mpxl-table*) (and ok tab)))

(assert-event (fn-mpxl-tabp *mpxl-split-1*))
(assert-event (and (equal (fn-mpxl-n *mpxl-split-1*) 2)
                   (equal (fn-mpxl-s *mpxl-split-1*) 1)
                   (equal (len (fn-mpxl-pages *mpxl-split-1*)) 3)))
(assert-event (fn-mpxl-faithful *mpxl-split-1* *mpxl-rows*))
(assert-event (equal (fn-mpxl-records "<a@x>" *mpxl-split-1* *mpxl-rows*)
                     (fn-cei-article-records-for "<a@x>" *mpxl-rows*)))
(assert-event (equal (fn-mpxl-records "<b@x>" *mpxl-split-1* *mpxl-rows*)
                     (fn-cei-article-records-for "<b@x>" *mpxl-rows*)))
(assert-event (equal (fn-mpxl-records "<z@x>" *mpxl-split-1* *mpxl-rows*) nil))

; Every entry of the new page is a mover (its address under mod 4 is 2), and
; no mover stayed on page 0.
(defun mpxl-all-addr (ents m p)
  (declare (xargs :guard (and (fn-mpx-pagep ents) (posp m) (natp p))))
  (if (consp ents)
      (and (equal (mod (car (car ents)) m) p) (mpxl-all-addr (cdr ents) m p))
    t))
(assert-event (mpxl-all-addr (fn-mpxl-ents (fn-mpxl-page 2 (fn-mpxl-pages *mpxl-split-1*))) 4 2))
(assert-event (equal (fn-mpxl-movers (fn-mpxl-ents (fn-mpxl-page 0 (fn-mpxl-pages *mpxl-split-1*))) 2 2) nil))
; the entries moved: the tags under mod 3 are 0, 1, 2 and the home of tag 2
; under mod 2 is page 0, under mod 4 page 2 -- whichever rows carry it, the
; count of entries is conserved
(defun mpxl-count (pgs)
  (declare (xargs :guard (fn-mpxl-pagesp pgs)))
  (if (consp pgs) (+ (len (fn-mpxl-ents (car pgs))) (mpxl-count (cdr pgs))) 0))
(assert-event (equal (mpxl-count (fn-mpxl-pages *mpxl-split-1*)) 3))

; The round ends at the next split: N doubles, S returns to 0.
(defconst *mpxl-split-2*
  (mv-let (ok tab) (fn-mpxl-split *mpxl-split-1*) (and ok tab)))
(assert-event (and (fn-mpxl-tabp *mpxl-split-2*)
                   (equal (fn-mpxl-n *mpxl-split-2*) 4)
                   (equal (fn-mpxl-s *mpxl-split-2*) 0)
                   (equal (len (fn-mpxl-pages *mpxl-split-2*)) 4)))
(assert-event (fn-mpxl-faithful *mpxl-split-2* *mpxl-rows*))
(assert-event (equal (fn-mpxl-records "<a@x>" *mpxl-split-2* *mpxl-rows*)
                     (fn-cei-article-records-for "<a@x>" *mpxl-rows*)))
(assert-event (equal (fn-mpxl-records "<b@x>" *mpxl-split-2* *mpxl-rows*)
                     (fn-cei-article-records-for "<b@x>" *mpxl-rows*)))

; ---------------------------------------------------------------------------
; THE REFUSALS.

; K entries (TAG . I) for I from FROM.
(defun mpxl-same (tag k from)
  (declare (xargs :guard (and (natp tag) (natp k) (natp from))))
  (if (zp k) nil (cons (cons tag from) (mpxl-same tag (- k 1) (+ 1 from)))))

; A split whose movers exceed a page: one page (N = 1, S = 0) holding 1,025
; entries of tag 1 (address 1 under mod 2: all movers) -- refused, the
; table unchanged; with 1,024 it is taken.
(defconst *mpxl-crowded* (fn-mpxl-make (list (cons nil (mpxl-same 1 1025 0))) 1 0))
(defconst *mpxl-fits* (fn-mpxl-make (list (cons nil (mpxl-same 1 1024 0))) 1 0))
(assert-event (and (fn-mpxl-tabp *mpxl-crowded*) (fn-mpxl-tabp *mpxl-fits*)))
(assert-event (mv-let (ok tab) (fn-mpxl-split *mpxl-crowded*)
                (and (not ok) (equal tab *mpxl-crowded*))))
(assert-event (mv-let (ok tab) (fn-mpxl-split *mpxl-fits*)
                (and ok (fn-mpxl-tabp tab)
                     (equal (fn-mpxl-n tab) 2) (equal (fn-mpxl-s tab) 0)
                     (equal (len (fn-mpxl-ents (fn-mpxl-page 0 (fn-mpxl-pages tab)))) 0)
                     (equal (len (fn-mpxl-ents (fn-mpxl-page 1 (fn-mpxl-pages tab)))) 1024))))

; The put onto a full home page: N = 2, S = 0, page 0 full of tag 0 (home
; 0); an entry of tag 0 goes to page 1 with page 0's flag set, and the
; reader finds it; with page 1 full too, the put is refused by name and the
; table unchanged -- never a silent drop.
(defconst *mpxl-full-home*
  (fn-mpxl-make (list (cons nil (mpxl-same 0 1024 0)) (cons nil nil)) 2 0))
(assert-event (fn-mpxl-tabp *mpxl-full-home*))
(assert-event (not (fn-mpxl-saturatedp 0 *mpxl-full-home*)))
(assert-event (mv-let (placed tab) (fn-mpxl-put 0 5000 *mpxl-full-home*)
                (and placed (fn-mpxl-tabp tab)
                     (fn-mpxl-flag (fn-mpxl-page 0 (fn-mpxl-pages tab)))
                     (member-equal 5000 (fn-mpxl-cands 0 tab))
                     (equal (len (fn-mpxl-ents (fn-mpxl-page 1 (fn-mpxl-pages tab)))) 1))))
(defconst *mpxl-full-both*
  (fn-mpxl-make (list (cons t (mpxl-same 0 1024 0)) (cons nil (mpxl-same 0 1024 1024))) 2 0))
(assert-event (fn-mpxl-saturatedp 0 *mpxl-full-both*))
(assert-event (mv-let (placed tab) (fn-mpxl-put 0 5000 *mpxl-full-both*)
                (and (not placed) (equal tab *mpxl-full-both*))))
; the flag is what the reader follows: without it the overflow page is not read
(assert-event (member-equal 1500 (fn-mpxl-cands 0 *mpxl-full-both*)))
(assert-event (not (member-equal 1500 (fn-mpxl-cands 0 (fn-mpxl-make (list (cons nil (mpxl-same 0 1024 0)) (cons nil (mpxl-same 0 1024 1024))) 2 0)))))

; ---------------------------------------------------------------------------
; A MUTATED SPLIT (the 2026-10-01 review's witness for the split keystone):
; the reachable table N = 2, S = 0 with 1,024 entries of tag 2 on page 0
; (home 0 under mod 2) and then tag 0 at seq 1024, which overflows to page
; 1 and flags page 0.  The split of page 0 moves the 1,024 tag-2 movers to
; page 2 (address 2 under mod 4) and KEEPS page 0's flag, so seq 1024 is
; still found; a split that drops the flag (the one line books/msgid-linear
; must keep) loses it: fn-mpxl-faithful fails and the reader misses the row.
(defconst *mpxl-reach*
  (mv-let (placed tab) (fn-mpxl-put 0 1024 (fn-mpxl-make (list (cons nil (mpxl-same 2 1024 0)) (cons nil nil)) 2 0))
    (and placed tab)))
(assert-event (and (fn-mpxl-tabp *mpxl-reach*)
                   (fn-mpxl-flag (fn-mpxl-page 0 (fn-mpxl-pages *mpxl-reach*)))
                   (member-equal 1024 (fn-mpxl-cands 0 *mpxl-reach*))))
; rows: 1,024 rows under one Message-ID carrying tag 2, then one under tag 0
(defun mpxl-rows-under (k from msgid)
  (declare (xargs :verify-guards nil))
  (if (zp k) nil (cons (mpxl-held from msgid 100) (mpxl-rows-under (- k 1) (+ 1 from) msgid))))
; a Message-ID of each tag under the attached hash (found by search)
(defun mpxl-find-msgid (want i)
  (declare (xargs :verify-guards nil :measure (nfix (- 1000 (nfix i)))))
  (if (>= (nfix i) 1000) nil
    (let ((m (concatenate 'string "<" (coerce (explode-nonnegative-integer (nfix i) 10 nil) 'string) "@x>")))
      (if (equal (mpxl-tag m) want) m (mpxl-find-msgid want (1+ (nfix i)))))))
(defconst *mpxl-m2* (mpxl-find-msgid 2 0))
(defconst *mpxl-m0* (mpxl-find-msgid 0 0))
(assert-event (and (equal (mpxl-tag *mpxl-m2*) 2) (equal (mpxl-tag *mpxl-m0*) 0)))
(defconst *mpxl-reach-rows*
  (append (mpxl-rows-under 1024 0 *mpxl-m2*) (list (mpxl-held 1024 *mpxl-m0* 100))))
(assert-event (fn-mpxl-faithful *mpxl-reach* *mpxl-reach-rows*))
(assert-event (equal (fn-mpxl-records *mpxl-m0* *mpxl-reach* *mpxl-reach-rows*)
                     (fn-cei-article-records-for *mpxl-m0* *mpxl-reach-rows*)))
; the split, as the book defines it: faithful, and the row still found
(defconst *mpxl-reach-split*
  (mv-let (ok tab) (fn-mpxl-split *mpxl-reach*) (and ok tab)))
(assert-event (and (fn-mpxl-tabp *mpxl-reach-split*)
                   (equal (len (fn-mpxl-ents (fn-mpxl-page 2 (fn-mpxl-pages *mpxl-reach-split*)))) 1024)
                   (fn-mpxl-flag (fn-mpxl-page 0 (fn-mpxl-pages *mpxl-reach-split*)))
                   (fn-mpxl-faithful *mpxl-reach-split* *mpxl-reach-rows*)
                   (equal (fn-mpxl-records *mpxl-m0* *mpxl-reach-split* *mpxl-reach-rows*)
                          (fn-cei-article-records-for *mpxl-m0* *mpxl-reach-rows*))))
; THE MUTATION: the split with page S's flag dropped
(defun mpxl-split-noflag (tab)
  (declare (xargs :verify-guards nil))
  (mv-let (ok tab2) (fn-mpxl-split tab)
    (if ok
        (let* ((pgs (fn-mpxl-pages tab2))
               (s (fn-mpxl-s tab))
               (pg (fn-mpxl-page s pgs)))
          (fn-mpxl-make (update-nth s (cons nil (fn-mpxl-ents pg)) pgs) (fn-mpxl-n tab2) (fn-mpxl-s tab2)))
      tab)))
(defconst *mpxl-reach-mutated* (mpxl-split-noflag *mpxl-reach*))
(assert-event (fn-mpxl-tabp *mpxl-reach-mutated*))
(assert-event (not (fn-mpxl-faithful *mpxl-reach-mutated* *mpxl-reach-rows*)))
(assert-event (not (member-equal 1024 (fn-mpxl-cands 0 *mpxl-reach-mutated*))))
(assert-event (not (equal (fn-mpxl-records *mpxl-m0* *mpxl-reach-mutated* *mpxl-reach-rows*)
                          (fn-cei-article-records-for *mpxl-m0* *mpxl-reach-rows*))))

; ---------------------------------------------------------------------------
; HYPOTHESIS-REMOVAL.

; fn-mpxl-faithful-from REMOVED: row 3's entry missing (the writer skipped
; it); tabp and okp hold, faithful-from fails, the conclusion fails.
(defconst *mpxl-table-missing*
  (mv-let (placed tab) (mpxl-build 0 (list *mpxl-a* *mpxl-b* *mpxl-ret*) (mpxl-empty 2))
    (and placed tab)))
(assert-event (fn-mpxl-tabp *mpxl-table-missing*))
(assert-event (fn-mpxl-okp *mpxl-table-missing* (len *mpxl-rows*)))
(assert-event (not (fn-mpxl-faithful-from 0 *mpxl-table-missing* *mpxl-rows*)))
(assert-event (not (equal (fn-mpxl-records "<a@x>" *mpxl-table-missing* *mpxl-rows*)
                          (fn-cei-article-records-for "<a@x>" *mpxl-rows*))))

; fn-mpxl-tabp: no removal witness.  Dropping it admits an entry whose seq
; is no natural, and every such table either keeps the conclusion (the
; confirmation drops a seq no row has) or cannot be evaluated (nth's
; guard); its redundancy is a proof task (layer A's type side conditions),
; not a counterexample, so the hypothesis stays.
