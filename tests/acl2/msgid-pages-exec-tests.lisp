; fn: teeth for books/msgid-pages-exec and books/msgid-pages-catalog (lane
; paged-history-2, 2026-09-29; PRF-969, PRF-970).  Prefix mpxe-.
;
; The tables are built by the writer (`fn-mpxt-add': the tag of each row's
; Message-ID, the row's sequence) under `with-local-stobj', so they run on
; the live arrays; each driver returns the values the keystone names and a
; theorem asserts them.  The teeth:
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

(in-package "ACL2")
(include-book "../../books/msgid-pages-catalog")

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

; The writer the host runs at load: add rows I.. under their own tags.
(defun mpxe-build (i rows fn-mpxt)
  (declare (xargs :stobjs fn-mpxt
                  :guard (and (natp i) (true-listp rows) (fn-mpxt-wfp fn-mpxt))
                  :measure (nfix (- (len rows) (nfix i)))
                  :guard-hints (("Goal" :in-theory (disable fn-mpxt-add)))))
  (if (or (>= (nfix i) (len rows)) (>= (+ 1 (nfix i)) *fn-mpxt-word-limit*))
      fn-mpxt
    (mv-let (placed fn-mpxt)
      (fn-mpxt-add (fn-mpxt-tag (fn-record-msgid (nth (nfix i) rows))) (nfix i) fn-mpxt)
      (declare (ignore placed))
      (mpxe-build (1+ (nfix i)) rows fn-mpxt))))

(defthm mpxe-build-shape
  (implies (and (fn-mpxtp fn-mpxt) (fn-mpxt-wfp fn-mpxt))
           (and (fn-mpxtp (mpxe-build i rows fn-mpxt))
                (fn-mpxt-wfp (mpxe-build i rows fn-mpxt))))
  :hints (("Goal" :induct (mpxe-build i rows fn-mpxt))))

(in-theory (disable mpxe-build))

; 1. POSITIVE: (faithful  seqs-a  spec-a  seqs-b  spec-b  seqs-none  spec-none  pages)
(defun mpxe-positive (rows)
  (declare (xargs :guard (true-listp rows)
                  :guard-hints (("Goal" :in-theory (disable fn-mpxt-seqs fn-mpxt-faithful)))))
  (with-local-stobj fn-mpxt
    (mv-let (result fn-mpxt)
      (let ((fn-mpxt (mpxe-build 0 rows fn-mpxt)))
        (mv (list (fn-mpxt-faithful rows fn-mpxt)
                  (fn-mpxt-seqs "<a@x>" rows fn-mpxt) (fn-mpxt-spec-from 0 "<a@x>" rows)
                  (fn-mpxt-seqs "<b@x>" rows fn-mpxt) (fn-mpxt-spec-from 0 "<b@x>" rows)
                  (fn-mpxt-seqs "<none@x>" rows fn-mpxt) (fn-mpxt-spec-from 0 "<none@x>" rows)
                  (fn-mpxt-pages fn-mpxt))
            fn-mpxt))
      result)))

(defthm mpxe-positive-witness
  (equal (mpxe-positive *mpxe-rows*)
         '(t (0 2) (0 2) (1) (1) nil nil 1))
  :rule-classes nil)

; 5. The catalog bridge: the abstract export's logic function agrees.
(defthm mpxe-catalog-witness
  (and (equal (fn-cat$a-msgid-seqs "<a@x>" *mpxe-rows*) '(0 2))
       (equal (fn-cat$a-msgid-seqs "<b@x>" *mpxe-rows*) '(1))
       (equal (fn-cat$a-msgid-seqs "<none@x>" *mpxe-rows*) nil))
  :rule-classes nil)

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
      (let ((fn-mpxt (mpxe-build 0 rows fn-mpxt)))
        (mv (list (fn-mpxt-faithful rows fn-mpxt)
                  (fn-mpxt-pages fn-mpxt) (fn-mpxt-count fn-mpxt)
                  (fn-mpxt-seqs far rows fn-mpxt) (fn-mpxt-spec-from 0 far rows)
                  (fn-mpxt-seqs near rows fn-mpxt) (fn-mpxt-spec-from 0 near rows))
            fn-mpxt))
      result)))

(defthm mpxe-grow-witness
  (equal (mpxe-grown *mpxe-rows-520* (mpxe-msgid 519) (mpxe-msgid 7))
         '(t 2 520 (519) (519) (7) (7)))
  :rule-classes nil)

; 3. faithful-from REMOVED: the writer skipped row 2 (a mutation of the load).
;    (okp  faithful-from  seqs-a  spec-a)
(defun mpxe-unindexed (rows)
  (declare (xargs :guard (true-listp rows)
                  :guard-hints (("Goal" :in-theory (disable fn-mpxt-seqs fn-mpxt-okp
                                                            fn-mpxt-faithful-from)))))
  (with-local-stobj fn-mpxt
    (mv-let (result fn-mpxt)
      (let ((fn-mpxt (mpxe-build 0 (list (nth 0 rows) (nth 1 rows)) fn-mpxt)))
        (mv (list (fn-mpxt-okp (len rows) fn-mpxt)
                  (fn-mpxt-faithful-from 0 rows fn-mpxt)
                  (fn-mpxt-seqs "<a@x>" rows fn-mpxt) (fn-mpxt-spec-from 0 "<a@x>" rows))
            fn-mpxt))
      result)))

(defthm mpxe-unindexed-witness
  (equal (mpxe-unindexed *mpxe-rows*)
         '(t nil (0) (0 2)))
  :rule-classes nil)

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
      (let ((fn-mpxt (mpxe-build 0 rows fn-mpxt)))
        (mv-let (placed fn-mpxt)
          (fn-mpxt-put 1 5 fn-mpxt)
          (mv (list placed
                    (fn-mpxt-faithful-from 0 rows fn-mpxt)
                    (fn-mpxt-okp (len rows) fn-mpxt)
                    (fn-mpxt-seqs nil rows fn-mpxt) (fn-mpxt-spec-from 0 nil rows)
                    (fn-mpxt-seqs "<a@x>" rows fn-mpxt))
              fn-mpxt)))
      result)))

(defthm mpxe-stale-witness
  (equal (mpxe-stale *mpxe-rows*)
         '(t t nil (5) nil (0 2)))
  :rule-classes nil)
