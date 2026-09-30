; fn: teeth for books/msgid-pages-exec and the catalog's paged reader (lane
; paged-history-2, 2026-09-29; PRF-969, PRF-970).  Prefix mpxe-.
;
; The tables are built by the writer (`fn-mpxt-add': the tag of each row's
; Message-ID, the row's sequence) under `with-local-stobj', so they run on
; the live arrays; each driver returns the values the keystone names and an
; `assert-event' checks them at certification (the tag is keyed BLAKE3,
; `fn-ns-mac' under the table's key: so the witnesses are evaluations, as
; the -1 lane's teeth are).  The teeth:
;   1. POSITIVE: three rows, <a@x> at 0 and 2; the table is faithful; the
;      reader answers (0 2), (1) and nil, each the walk's answer.
;   2. GROW: 520 rows (the count passes half the slots at 512, so the table
;      grows to two pages); every row's own sequence is still found, the
;      table is faithful, and one key at the far end answers correctly.
;   3. faithful-from REMOVED (a mutation: a row the writer never indexed):
;      okp holds, faithful-from fails, the reader misses the row.
;   4. okp REMOVED (a stale entry: a sequence beyond the rows, under the
;      empty key's tag): faithful-from holds, okp fails, the reader answers
;      a sequence no row has.
;   5. The catalog bridge on the positive fixture: fn-cat$a-msgid-seqs of
;      the rows is the reader's answer.
;   6. PAGE NEED (W2b, PKT-774): on the grown table the counted reader's
;      pages are the need, 1 + the full run, at most the page count, at most
;      two under the condition, and no tag is skewed; SKEW: 2,048 entries
;      under one tag fill a home page and its overflow (a leaked key's
;      crafted tags): the tag is saturated, its need is two pages (the
;      structural bound), the condition fails, and the next placement is
;      refused with the table unchanged (never a dropped insert).

(in-package "ACL2")
(include-book "../../books/catalog")

; --- the rows: held rows as the catalog holds them (the -1 lane's fixture) ---

(defun mpxe-held (seq msgid octets)
  (declare (xargs :verify-guards nil))
  (fn-held-make seq (+ 1 seq) 0 msgid seq '("fn.test") "o" "s" "e" 1 5
                (fn-hf-make octets 14 2 nil)
                (fn-hc-make (fn-stx-make-verdict :unverified nil 0) nil 0)
                nil nil))

(defconst *mpxe-rows*
  (list (mpxe-held 0 "<a@x>" 100) (mpxe-held 1 "<b@x>" 200) (mpxe-held 2 "<a@x>" 300)))

(assert-event (and (equal (fn-record-msgid (nth 0 *mpxe-rows*)) "<a@x>")
                   (equal (fn-record-msgid (nth 1 *mpxe-rows*)) "<b@x>")
                   (equal (fn-record-msgid (nth 2 *mpxe-rows*)) "<a@x>")
                   (fn-cat-rowsp *mpxe-rows*)))

; The table's key in these witnesses: the purpose key of a node-secret entry
; (the ring's current one), as the open installs it.
(defconst *mpxe-entry* (fn-ns-create-entry '(116 101 115 116) (make-list 32 :initial-element 7)))
(defconst *mpxe-key* (fn-mpxt-key-of-entry *mpxe-entry*))

(assert-event ; mpxe-key-witness: 32 octets; a second entry's key differs, and so do the tags
  (and (equal (len *mpxe-key*) 32)
       (not (equal *mpxe-key* (fn-mpxt-key-of-entry (fn-ns-create-entry '(116 101 115 116) (make-list 32 :initial-element 8)))))
       (not (equal (fn-mpxt-tag "<a@x>" *mpxe-key*)
                   (fn-mpxt-tag "<a@x>" (fn-mpxt-key-of-entry (fn-ns-create-entry '(116 101 115 116) (make-list 32 :initial-element 8))))))
       (not (equal *mpxe-key* (fn-ns-cancel-lock-key *mpxe-entry*)))))

; One add with a fresh generation buffer (the catalog keeps one beside the
; table; a test allocates one per add): (mv outcome fn-mpxt).
(defthm mpxe-fresh-generation
  (fn-mpxtp (create-fn-mpxt2))
  :hints (("Goal" :in-theory (enable fn-mpxtp))))

(defun mpxe-add1 (tag seq fn-mpxt)
  (declare (xargs :stobjs fn-mpxt
                  :guard (and (natp tag) (< tag *fn-mpxt-word-limit*)
                              (natp seq) (< (+ 1 seq) *fn-mpxt-word-limit*) (fn-mpxt-wfp fn-mpxt))
                  :guard-hints (("Goal" :in-theory (disable fn-mpxt-add)))))
  (with-local-stobj fn-mpxt2
    (mv-let (outcome fn-mpxt fn-mpxt2)
      (fn-mpxt-add tag seq fn-mpxt fn-mpxt2)
      (mv outcome fn-mpxt))))

(defthm mpxe-add1-shape
  (implies (and (fn-mpxtp fn-mpxt) (fn-mpxt-wfp fn-mpxt) (natp tag) (< tag *fn-mpxt-word-limit*)
                (natp seq) (< (+ 1 seq) *fn-mpxt-word-limit*))
           (and (fn-mpxtp (mv-nth 1 (mpxe-add1 tag seq fn-mpxt)))
                (<= (* *fn-mpxt-page-words* (fn-mpxt-pages (mv-nth 1 (mpxe-add1 tag seq fn-mpxt))))
                    (fn-mpxt-w-length (mv-nth 1 (mpxe-add1 tag seq fn-mpxt))))))
  :hints (("Goal" :in-theory (disable fn-mpxt-add))))

(in-theory (disable mpxe-add1))

; The writer the host runs at load: add rows I.. under their own tags.
(defun mpxe-build (i rows fn-mpxt)
  (declare (xargs :stobjs fn-mpxt
                  :guard (and (natp i) (true-listp rows) (fn-mpxt-wfp fn-mpxt))
                  :measure (nfix (- (len rows) (nfix i)))))
  (if (or (>= (nfix i) (len rows)) (>= (+ 1 (nfix i)) *fn-mpxt-word-limit*))
      fn-mpxt
    (mv-let (outcome fn-mpxt)
      (mpxe-add1 (fn-mpxt-tag (fn-record-msgid (nth (nfix i) rows)) (fn-mpxt-key-octets fn-mpxt))
                 (nfix i) fn-mpxt)
      (declare (ignore outcome))
      (mpxe-build (1+ (nfix i)) rows fn-mpxt))))

(defthm mpxe-build-shape
  (implies (and (fn-mpxtp fn-mpxt) (fn-mpxt-wfp fn-mpxt))
           (and (fn-mpxtp (mpxe-build i rows fn-mpxt))
                (fn-mpxt-wfp (mpxe-build i rows fn-mpxt))))
  :hints (("Goal" :induct (mpxe-build i rows fn-mpxt))))

(defthm mpxe-build-wfp
  (implies (and (fn-mpxtp fn-mpxt) (fn-mpxt-wfp fn-mpxt))
           (<= (* *fn-mpxt-page-words* (fn-mpxt-pages (mpxe-build i rows fn-mpxt)))
               (fn-mpxt-w-length (mpxe-build i rows fn-mpxt))))
  :hints (("Goal" :use mpxe-build-shape :in-theory (disable mpxe-build-shape))))

(in-theory (disable mpxe-build))

; 1. POSITIVE: (faithful  seqs-a  spec-a  seqs-b  spec-b  seqs-none  spec-none  pages)
(defun mpxe-positive (rows)
  (declare (xargs :guard (true-listp rows)
                  :guard-hints (("Goal" :in-theory (disable fn-mpxt-seqs fn-mpxt-faithful)))))
  (with-local-stobj fn-mpxt
    (mv-let (result fn-mpxt)
      (let* ((fn-mpxt (fn-mpxt-set-key *mpxe-key* fn-mpxt))
             (fn-mpxt (mpxe-build 0 rows fn-mpxt)))
        (mv (list (fn-mpxt-faithful rows fn-mpxt)
                  (fn-mpxt-seqs "<a@x>" rows fn-mpxt) (fn-mpxt-spec-from 0 "<a@x>" rows)
                  (fn-mpxt-seqs "<b@x>" rows fn-mpxt) (fn-mpxt-spec-from 0 "<b@x>" rows)
                  (fn-mpxt-seqs "<none@x>" rows fn-mpxt) (fn-mpxt-spec-from 0 "<none@x>" rows)
                  (fn-mpxt-pages fn-mpxt))
            fn-mpxt))
      result)))

(assert-event ; mpxe-positive-witness
  (equal (mpxe-positive *mpxe-rows*)
         '(t (0 2) (0 2) (1) (1) nil nil 1)))

; 5. The catalog bridge: the abstract export's logic function agrees.
(assert-event ; mpxe-catalog-witness
  (and (equal (fn-cat$a-msgid-seqs "<a@x>" *mpxe-rows*) '(0 2))
       (equal (fn-cat$a-msgid-seqs "<b@x>" *mpxe-rows*) '(1))
       (equal (fn-cat$a-msgid-seqs "<none@x>" *mpxe-rows*) nil)))

; 2. GROW: 520 rows <n@x>; (faithful  pages  count  seqs-519  spec-519  seqs-7  spec-7)
(defun mpxe-msgid (n)
  (declare (xargs :verify-guards nil))
  (concatenate 'string "<" (coerce (explode-nonnegative-integer n 10 nil) 'string) "@x>"))

(defun mpxe-rows-to (n acc)
  (declare (xargs :verify-guards nil))
  (if (zp n) acc (mpxe-rows-to (1- n) (cons (mpxe-held (1- n) (mpxe-msgid (1- n)) 100) acc))))

(defconst *mpxe-rows-520* (mpxe-rows-to 520 nil))

(defun mpxe-grown (rows far near)
  (declare (xargs :guard (true-listp rows)
                  :guard-hints (("Goal" :in-theory (disable fn-mpxt-seqs fn-mpxt-faithful)))))
  (with-local-stobj fn-mpxt
    (mv-let (result fn-mpxt)
      (let* ((fn-mpxt (fn-mpxt-set-key *mpxe-key* fn-mpxt))
             (fn-mpxt (mpxe-build 0 rows fn-mpxt)))
        (mv (list (fn-mpxt-faithful rows fn-mpxt)
                  (fn-mpxt-pages fn-mpxt) (fn-mpxt-count fn-mpxt)
                  (fn-mpxt-seqs far rows fn-mpxt) (fn-mpxt-spec-from 0 far rows)
                  (fn-mpxt-seqs near rows fn-mpxt) (fn-mpxt-spec-from 0 near rows))
            fn-mpxt))
      result)))

(assert-event ; mpxe-grow-witness
  (equal (mpxe-grown *mpxe-rows-520* (mpxe-msgid 519) (mpxe-msgid 7))
         '(t 2 520 (519) (519) (7) (7))))

; 3. faithful-from REMOVED: the writer skipped row 2 (a mutation of the load).
;    (okp  faithful-from  seqs-a  spec-a)
(defun mpxe-unindexed (rows)
  (declare (xargs :guard (true-listp rows)
                  :guard-hints (("Goal" :in-theory (disable fn-mpxt-seqs fn-mpxt-okp
                                                            fn-mpxt-faithful-from)))))
  (with-local-stobj fn-mpxt
    (mv-let (result fn-mpxt)
      (let* ((fn-mpxt (fn-mpxt-set-key *mpxe-key* fn-mpxt))
             (fn-mpxt (mpxe-build 0 (list (nth 0 rows) (nth 1 rows)) fn-mpxt)))
        (mv (list (fn-mpxt-okp (len rows) fn-mpxt)
                  (fn-mpxt-faithful-from 0 rows fn-mpxt)
                  (fn-mpxt-seqs "<a@x>" rows fn-mpxt) (fn-mpxt-spec-from 0 "<a@x>" rows))
            fn-mpxt))
      result)))

(assert-event ; mpxe-unindexed-witness
  (equal (mpxe-unindexed *mpxe-rows*)
         '(t nil (0) (0 2))))

; 4. okp REMOVED: a stale entry (tag 1, sequence 5) beyond the three rows;
;    tag 1 is the empty key's tag, and the row beyond the rows has no
;    Message-ID, so the reader answers 5 for the key nil where the walk
;    answers nothing.  (faithful-from  okp  seqs-nil  spec-nil  seqs-a)
(defun mpxe-stale (rows)
  (declare (xargs :guard (true-listp rows)
                  :guard-hints (("Goal" :in-theory (disable fn-mpxt-seqs fn-mpxt-okp fn-mpxt-put
                                                            fn-mpxt-faithful-from)))))
  (with-local-stobj fn-mpxt
    (mv-let (result fn-mpxt)
      (let* ((fn-mpxt (fn-mpxt-set-key *mpxe-key* fn-mpxt))
             (fn-mpxt (mpxe-build 0 rows fn-mpxt)))
        (mv-let (placed fn-mpxt)
          (fn-mpxt-put 1 5 fn-mpxt)
          (mv (list placed
                    (fn-mpxt-faithful-from 0 rows fn-mpxt)
                    (fn-mpxt-okp (len rows) fn-mpxt)
                    (fn-mpxt-seqs nil rows fn-mpxt) (fn-mpxt-spec-from 0 nil rows)
                    (fn-mpxt-seqs "<a@x>" rows fn-mpxt))
              fn-mpxt)))
      result)))

(assert-event ; mpxe-stale-witness
  (equal (mpxe-stale *mpxe-rows*)
         '(t t nil (5) nil (0 2))))

; 6. PAGE NEED and SKEW.
; For each Message-ID: (counted-candidates = candidates, counted-pages = need,
;                       need <= pages, need <= 2, saturated)
(defun mpxe-need-each (msgids fn-mpxt)
  (declare (xargs :stobjs fn-mpxt :guard (and (true-listp msgids) (fn-mpxt-wfp fn-mpxt))
                  :guard-hints (("Goal" :in-theory (disable fn-mpxt-candidates-counted fn-mpxt-candidates
                                                            fn-mpxt-candidates-pages                                                             fn-mpxt-saturatedp)))))
  (if (consp msgids)
      (let* ((tag (fn-mpxt-tag (car msgids) (fn-mpxt-key-octets fn-mpxt)))
             (np (fn-mpxt-pages fn-mpxt)))
        (mv-let (cands pages)
          (fn-mpxt-candidates-counted tag fn-mpxt)
          (cons (list (equal cands (fn-mpxt-candidates tag fn-mpxt))
                      (equal pages (fn-mpxt-candidates-pages tag fn-mpxt))
                      (<= pages np)
                      (<= pages 2)
                      (fn-mpxt-saturatedp tag fn-mpxt))
                (mpxe-need-each (cdr msgids) fn-mpxt))))
    nil))

(defun mpxe-need (rows msgids)
  (declare (xargs :guard (and (true-listp rows) (true-listp msgids))
                  :guard-hints (("Goal" :in-theory (disable fn-mpxt-candidates-counted fn-mpxt-candidates
                                                            fn-mpxt-candidates-pages                                                             fn-mpxt-saturatedp fn-mpxt-no-adjacent-fullp)))))
  (with-local-stobj fn-mpxt
    (mv-let (result fn-mpxt)
      (let* ((fn-mpxt (fn-mpxt-set-key *mpxe-key* fn-mpxt))
             (fn-mpxt (mpxe-build 0 rows fn-mpxt)))
        (mv (mpxe-need-each msgids fn-mpxt) fn-mpxt))
      result)))

(defun mpxe-condition (rows)
  (declare (xargs :guard (true-listp rows)
                  :guard-hints (("Goal" :in-theory (disable fn-mpxt-no-adjacent-fullp)))))
  (with-local-stobj fn-mpxt
    (mv-let (result fn-mpxt)
      (let* ((fn-mpxt (fn-mpxt-set-key *mpxe-key* fn-mpxt))
             (fn-mpxt (mpxe-build 0 rows fn-mpxt)))
        (mv (list (fn-mpxt-pages fn-mpxt) (fn-mpxt-no-adjacent-fullp (fn-mpxt-pages fn-mpxt) fn-mpxt)) fn-mpxt))
      result)))

(assert-event ; mpxe-page-need-witness: the grown table (2 pages) satisfies the condition; every need is 1
  (and (equal (mpxe-condition *mpxe-rows-520*) '(2 t))
       (equal (mpxe-need *mpxe-rows-520* (list (mpxe-msgid 0) (mpxe-msgid 7) (mpxe-msgid 519) "<none@x>"))
              '((t t t t nil) (t t t t nil) (t t t t nil) (t t t t nil)))))

; N entries under one TAG from sequence I (a leaked key's crafted tags).
(defun mpxe-add-same (tag n i fn-mpxt)
  (declare (xargs :stobjs fn-mpxt :measure (nfix (- n (nfix i)))
                  :guard (and (natp tag) (< tag *fn-mpxt-word-limit*) (natp n) (natp i)
                              (< (+ 1 n) *fn-mpxt-word-limit*) (fn-mpxt-wfp fn-mpxt))))
  (if (>= (nfix i) (nfix n))
      fn-mpxt
    (mv-let (outcome fn-mpxt)
      (mpxe-add1 tag (nfix i) fn-mpxt)
      (declare (ignore outcome))
      (mpxe-add-same tag n (1+ (nfix i)) fn-mpxt))))

(defthm mpxe-add-same-shape
  (implies (and (fn-mpxtp fn-mpxt) (fn-mpxt-wfp fn-mpxt) (natp tag) (< tag *fn-mpxt-word-limit*)
                (natp n) (< (+ 1 n) *fn-mpxt-word-limit*))
           (and (fn-mpxtp (mpxe-add-same tag n i fn-mpxt))
                (<= (* *fn-mpxt-page-words* (fn-mpxt-pages (mpxe-add-same tag n i fn-mpxt)))
                    (fn-mpxt-w-length (mpxe-add-same tag n i fn-mpxt)))))
  :hints (("Goal" :induct (mpxe-add-same tag n i fn-mpxt))))

(in-theory (disable mpxe-add-same))

; (pages count saturated-7 need-7 condition saturated-6 need-6 placed-7 need-7-after)
(defun mpxe-skew (n)
  (declare (xargs :guard (and (natp n) (< (+ 1 n) *fn-mpxt-word-limit*))
                  :guard-hints (("Goal" :in-theory (disable fn-mpxt-candidates-pages fn-mpxt-saturatedp fn-mpxt-put
                                                            fn-mpxt-no-adjacent-fullp)))))
  (with-local-stobj fn-mpxt
    (mv-let (result fn-mpxt)
      (let* ((fn-mpxt (fn-mpxt-set-key *mpxe-key* fn-mpxt))
             (fn-mpxt (mpxe-add-same 7 n 0 fn-mpxt))
             (before (list (fn-mpxt-pages fn-mpxt) (fn-mpxt-count fn-mpxt)
                           (fn-mpxt-saturatedp 7 fn-mpxt) (fn-mpxt-candidates-pages 7 fn-mpxt)
                           (fn-mpxt-no-adjacent-fullp (fn-mpxt-pages fn-mpxt) fn-mpxt)
                           (fn-mpxt-saturatedp 6 fn-mpxt) (fn-mpxt-candidates-pages 6 fn-mpxt))))
        (mv-let (placed fn-mpxt)
          (fn-mpxt-put 7 n fn-mpxt)
          (mv (append before (list placed (fn-mpxt-candidates-pages 7 fn-mpxt))) fn-mpxt)))
      result)))

(assert-event ; mpxe-saturated-witness: 2,048 entries under tag 7: the 2,048th placement reached
              ; half the slots of 4 pages and grew to 8 (paged-history-4: the add places, then
              ; settles), where tag 7's home page and its overflow hold exactly those 2,048 --
              ; saturated for tag 7 at load 1/4, and the 2,049th is not placed.
  (equal (mpxe-skew 2048) '(8 2048 t 2 nil nil 1 nil 2)))

(assert-event ; mpxe-not-skewed-witness: 1,000 entries under tag 7 (2 pages: page 1 not full)
  (equal (mpxe-skew 1000) '(2 1000 nil 1 t nil 1 t 1)))

; P2 structural collision: put a different row under A's exact stored tag
; beside its own ordinary mapping. This is an overinclusive candidate set,
; not a claim to have found a BLAKE3 collision. Both table entries really
; carry the same tag; the exported concrete reader must compare Message-IDs.
; The full faithful antecedent still holds: every own mapping is retained.
(defun mpxe-exact-collision (rows)
  (declare (xargs :guard (true-listp rows)
                  :guard-hints (("Goal" :in-theory (disable fn-mpxt-seqs
                    fn-mpxt-faithful fn-mpxt-candidates)))))
  (with-local-stobj fn-mpxt
    (mv-let (result fn-mpxt)
      (let* ((fn-mpxt (fn-mpxt-set-key *mpxe-key* fn-mpxt))
             (fn-mpxt (mpxe-build 0 rows fn-mpxt)))
        (mv-let (word fn-mpxt)
          (mpxe-add1 (fn-mpxt-tag "<a@x>" *mpxe-key*) 1 fn-mpxt)
          (mv (list word (fn-mpxt-faithful rows fn-mpxt)
                    (fn-mpxt-candidates (fn-mpxt-tag "<a@x>" *mpxe-key*) fn-mpxt)
                    (fn-mpxt-seqs "<a@x>" rows fn-mpxt)
                    (fn-mpxt-spec-from 0 "<a@x>" rows)
                    (fn-mpxt-seqs "<b@x>" rows fn-mpxt)
                    (fn-mpxt-spec-from 0 "<b@x>" rows))
              fn-mpxt)))
      result)))

(assert-event ; positive structural collision, full antecedent and conclusion
  (and (fn-cat-rowsp *mpxe-rows*)
       (not (equal (fn-record-msgid (nth 0 *mpxe-rows*))
                   (fn-record-msgid (nth 1 *mpxe-rows*))))
       (equal (mpxe-exact-collision *mpxe-rows*)
              '(:placed t (0 1 2) (0 2) (0 2) (1) (1)))))

(defun mpxe-grow1 (fn-mpxt)
  (declare (xargs :stobjs fn-mpxt :guard (fn-mpxt-wfp fn-mpxt)
                  :guard-hints (("Goal" :in-theory (disable fn-mpxt-grow)))))
  (with-local-stobj fn-mpxt2
    (mv-let (ok fn-mpxt fn-mpxt2)
      (fn-mpxt-grow fn-mpxt fn-mpxt2)
      (mv ok fn-mpxt))))

(defthm mpxe-grow1-shape
  (implies (and (fn-mpxtp fn-mpxt) (fn-mpxt-wfp fn-mpxt))
           (and (fn-mpxtp (mv-nth 1 (mpxe-grow1 fn-mpxt)))
                (fn-mpxt-wfp (mv-nth 1 (mpxe-grow1 fn-mpxt)))))
  :hints (("Goal" :in-theory (disable fn-mpxt-grow))))
(in-theory (disable mpxe-grow1))

; Growing a saturated same-tag generation succeeds for its existing2048
; mappings; it cannot create room for the2049th equal-tag entry. Exercise
; the actual ADD verdict after actual GROW, preserving every candidate,
; key, count, page cardinality and health bit through refusal.
(defun mpxe-saturated-grow (n)
  (declare (xargs :guard (and (natp n) (< (+ 1 n) *fn-mpxt-word-limit*))
                  :guard-hints (("Goal" :in-theory (disable fn-mpxt-candidates
                    fn-mpxt-saturatedp fn-mpxt-key-octets)))))
  (with-local-stobj fn-mpxt
    (mv-let (result fn-mpxt)
      (let* ((fn-mpxt (fn-mpxt-set-key *mpxe-key* fn-mpxt))
             (fn-mpxt (mpxe-add-same 7 n 0 fn-mpxt))
             (before (fn-mpxt-candidates 7 fn-mpxt))
             (saturated (fn-mpxt-saturatedp 7 fn-mpxt)))
        (mv-let (ok fn-mpxt)
          (mpxe-grow1 fn-mpxt)
          (let ((grown (list (fn-mpxt-pages fn-mpxt) (fn-mpxt-count fn-mpxt)
                            (fn-mpxt-stuck fn-mpxt) (fn-mpxt-key-octets fn-mpxt)
                            (fn-mpxt-candidates 7 fn-mpxt))))
            (mv-let (word fn-mpxt)
              (mpxe-add1 7 n fn-mpxt)
              (mv (list saturated ok (len before)
                        (equal before (fn-mpxt-candidates 7 fn-mpxt))
                        (nth 0 grown) (nth 1 grown) word
                        (fn-mpxt-saturatedp 7 fn-mpxt)
                        (equal grown
                          (list (fn-mpxt-pages fn-mpxt) (fn-mpxt-count fn-mpxt)
                                (fn-mpxt-stuck fn-mpxt) (fn-mpxt-key-octets fn-mpxt)
                                (fn-mpxt-candidates 7 fn-mpxt))))
                  fn-mpxt)))))
      result)))

(assert-event
  (equal (mpxe-saturated-grow 2048) '(t t 2048 t 16 2048 :mpx-saturated t t)))
