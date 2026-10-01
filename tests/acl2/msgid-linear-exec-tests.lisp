; fn: teeth for books/msgid-linear-exec (lane msgid-linear-hash, 2026-10-01;
; PRF-1219).  Prefix mlhx-.
;
; The tables are built by the writer (`fn-mlh-put') under `with-local-stobj'
; on the live typed array; each driver returns the values the keystone names
; and an `assert-event' checks them at certification.  The teeth:
;   1. POSITIVE: three rows, <a@x> at 0 and 2, on one page (N = 1, S = 0);
;      the table is faithful; the reader answers (0 2), (1) and nil, each the
;      walk's answer; the bridge agrees (the word reader is the logical
;      reader of the abstraction).
;   2. THE FLAG: N = 2, S = 0; 1,024 entries of tag 2 fill page 0 (home 0);
;      tag 4 (home 0) at seq 1024 lands on page 1 with page 0's flag set, and
;      the reader finds it; the keyed tags are 60-bit and differ by key.
;   3. SATURATION BY NAME: page 1 filled too (tag 3, home 1); the next tag-4
;      entry is refused (fn-mlh-saturatedp), the reader's answer unchanged.
;   4. faithful-from REMOVED: a row the writer never indexed; okp holds,
;      faithful-from fails, the reader misses it.

(in-package "ACL2")
(include-book "../../books/msgid-linear-exec")
(include-book "must-fail-checked")

(make-event
 (if (equal (len (formals 'fn-held-make (w state))) 16)
     '(defun mlhx-held (seq msgid octets)
        (declare (xargs :verify-guards nil))
        (fn-held-make seq (+ 1 seq) 0 msgid seq '("fn.test") "o" "s" "e" 1 5
                      (fn-hf-make octets 14 2 nil)
                      (fn-hc-make (fn-stx-make-verdict :unverified nil 0) nil 0)
                      nil nil
                      (fn-ab-make :post-d25 (append *fn-ab-subject-head* (make-list 32 :initial-element 0)))))
   '(defun mlhx-held (seq msgid octets)
      (declare (xargs :verify-guards nil))
      (fn-held-make seq (+ 1 seq) 0 msgid seq '("fn.test") "o" "s" "e" 1 5
                    (fn-hf-make octets 14 2 nil)
                    (fn-hc-make (fn-stx-make-verdict :unverified nil 0) nil 0)
                    nil nil))))

(defconst *mlhx-rows*
  (list (mlhx-held 0 "<a@x>" 100) (mlhx-held 1 "<b@x>" 200) (mlhx-held 2 "<a@x>" 300)))

(assert-event (and (equal (fn-record-msgid (nth 0 *mlhx-rows*)) "<a@x>")
                   (equal (fn-record-msgid (nth 1 *mlhx-rows*)) "<b@x>")
                   (equal (fn-record-msgid (nth 2 *mlhx-rows*)) "<a@x>")))

; The keyed tag: 60-bit, positive, and a function of the key.
(defconst *mlhx-key-a* (make-list 32 :initial-element 7))
(defconst *mlhx-key-b* (make-list 32 :initial-element 8))
(assert-event (and (< (fn-mlh-tag "<a@x>" *mlhx-key-a*) *fn-mlh-tag-limit*)
                   (posp (fn-mlh-tag "<a@x>" *mlhx-key-a*))
                   (not (equal (fn-mlh-tag "<a@x>" *mlhx-key-a*) (fn-mlh-tag "<a@x>" *mlhx-key-b*)))
                   (not (equal (fn-mlh-tag "<a@x>" *mlhx-key-a*) (fn-mlh-tag "<b@x>" *mlhx-key-a*)))))

; A table of NP pages, N = NP, S = 0 (the zero key).
(defun mlhx-pages (np fn-mlh)
  (declare (xargs :stobjs fn-mlh :guard (posp np)))
  (let* ((fn-mlh (resize-fn-mlh-pg np fn-mlh))
         (fn-mlh (update-fn-mlh-pages np fn-mlh))
         (fn-mlh (update-fn-mlh-n np fn-mlh))
         (fn-mlh (update-fn-mlh-s 0 fn-mlh)))
    fn-mlh))

; The reserved empty tag is rejected by the public guard.  Initialize a
; valid page so the rejection cannot be attributed to another argument.
(defun mlhx-try-put (tag)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-mlh
    (mv-let (placed fn-mlh)
      (let ((fn-mlh (mlhx-pages 1 fn-mlh)))
        (fn-mlh-put tag 0 fn-mlh))
      placed)))

(assert-event (with-guard-checking :all (mlhx-try-put 1)))
(must-fail-checked
 (assert-event (with-guard-checking :all (mlhx-try-put 0))))

; The writer the host runs at load: rows I.. under their own keyed tags.
(defun mlhx-build (i rows fn-mlh)
  (declare (xargs :stobjs fn-mlh :verify-guards nil
                  :guard (and (natp i) (true-listp rows) (fn-mlh-wfp fn-mlh))
                  :measure (nfix (- (len rows) (nfix i)))))
  (if (or (>= (nfix i) (len rows)) (>= (+ 2 (nfix i)) *fn-mlh-tag-limit*))
      fn-mlh
    (mv-let (placed fn-mlh)
      (fn-mlh-put (fn-mlh-tag (fn-record-msgid (nth (nfix i) rows)) (fn-mlh-key-octets fn-mlh)) (nfix i) fn-mlh)
      (declare (ignore placed))
      (mlhx-build (1+ (nfix i)) rows fn-mlh))))

; 1. POSITIVE: all three reader hypotheses, three answers, and the bridge
; with all four of its literal hypotheses.
(defun mlhx-positive (rows)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-mlh
    (mv-let (result fn-mlh)
      (let* ((fn-mlh (mlhx-pages 1 fn-mlh))
             (fn-mlh (mlhx-build 0 rows fn-mlh)))
        (mv (list (fn-mlhp fn-mlh) (fn-mlh-wfp fn-mlh)
                  (fn-mlh-faithful rows fn-mlh)
                  (fn-mlh-seqs "<a@x>" rows fn-mlh) (fn-mpxt-spec-from 0 "<a@x>" rows)
                  (fn-mlh-seqs "<b@x>" rows fn-mlh) (fn-mpxt-spec-from 0 "<b@x>" rows)
                  (fn-mlh-seqs "<none@x>" rows fn-mlh) (fn-mpxt-spec-from 0 "<none@x>" rows)
                  (fn-mlhp fn-mlh) (fn-mlh-wfp fn-mlh)
                  (posp (fn-mlh-pages fn-mlh))
                  (posp (fn-mlh-tag "<a@x>" (fn-mlh-key-octets fn-mlh)))
                  (equal (fn-mlh-candidates (fn-mlh-tag "<a@x>" (fn-mlh-key-octets fn-mlh)) fn-mlh)
                         (fn-mpxl-cands (fn-mlh-tag "<a@x>" (fn-mlh-key-octets fn-mlh)) (fn-mlh-abs fn-mlh))))
            fn-mlh))
      result)))

(assert-event ; mlhx-positive-witness
  (equal (mlhx-positive *mlhx-rows*) '(t t t (0 2) (0 2) (1) (1) nil nil t t t t t)))

; N entries under one TAG from sequence I.
(defun mlhx-add-same (tag n i fn-mlh)
  (declare (xargs :stobjs fn-mlh :verify-guards nil :measure (nfix (- (nfix n) (nfix i)))))
  (if (>= (nfix i) (nfix n))
      fn-mlh
    (mv-let (placed fn-mlh)
      (fn-mlh-put tag (nfix i) fn-mlh)
      (declare (ignore placed))
      (mlhx-add-same tag (nfix n) (1+ (nfix i)) fn-mlh))))

; 2 + 3. THE FLAG and SATURATION: page 0 full of tag 2; tag 4 at 1024 lands on
; page 1 with the flag; page 1 then filled with tag 3 (home 1); the next
; tag 4 is refused by name, the table's answer unchanged.
;   (flag0-before placed-4 flag0-after cands-4 saturated-4-before
;    saturated-4-after placed-again cands-4-after flag1)
(defun mlhx-flag ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-mlh
    (mv-let (result fn-mlh)
      (let* ((fn-mlh (mlhx-pages 2 fn-mlh))
             (fn-mlh (mlhx-add-same 2 1024 0 fn-mlh))
             (flag0-before (fn-mlh-ovf 0 fn-mlh)))
        (mv-let (placed-4 fn-mlh)
          (fn-mlh-put 4 1024 fn-mlh)
          (let* ((flag0-after (fn-mlh-ovf 0 fn-mlh))
                 (cands-4 (fn-mlh-candidates 4 fn-mlh))
                 (sat-before (fn-mlh-saturatedp 4 fn-mlh))
                 (fn-mlh (mlhx-add-same 3 3024 2000 fn-mlh))
                 (sat-after (fn-mlh-saturatedp 4 fn-mlh)))
            (mv-let (placed-again fn-mlh)
              (fn-mlh-put 4 5000 fn-mlh)
              (mv (list flag0-before placed-4 flag0-after cands-4 sat-before sat-after placed-again
                        (fn-mlh-candidates 4 fn-mlh) (fn-mlh-ovf 1 fn-mlh))
                  fn-mlh)))))
      result)))

(assert-event ; mlhx-flag-witness
  (equal (mlhx-flag) '(nil t t (1024) nil t nil (1024) nil)))

; 4. faithful REMOVED: the writer skipped row 2.  Both structural
; hypotheses hold; faithful fails and the literal reader equality fails.
(defun mlhx-unindexed (rows)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-mlh
    (mv-let (result fn-mlh)
      (let* ((fn-mlh (mlhx-pages 1 fn-mlh))
             (fn-mlh (mlhx-build 0 (list (nth 0 rows) (nth 1 rows)) fn-mlh)))
        (mv (list (fn-mlhp fn-mlh) (fn-mlh-wfp fn-mlh)
                  (fn-mlh-okp (len rows) fn-mlh)
                  (fn-mlh-faithful rows fn-mlh)
                  (fn-mlh-faithful-from 0 rows fn-mlh)
                  (fn-mlh-seqs "<a@x>" rows fn-mlh) (fn-mpxt-spec-from 0 "<a@x>" rows))
            fn-mlh))
      result)))

(assert-event ; mlhx-unindexed-witness
  (equal (mlhx-unindexed *mlhx-rows*) '(t t t nil nil (0) (0 2))))

; CORRUPTED-STATE hypothesis removal for fn-mlh-seqs-is-spec-from.
; These are logical stobj values, not calls through the guarded raw API.
; Page 0 is empty; page 1 of the page array holds (tag 1, seq 0), but only
; page 0 belongs to the abstraction (pages = 1).  With rows nil, faithful
; holds, but the nil query has tag 1 and confirms the stale seq against
; (nth 0 nil).
(defconst *mlhx-page-empty* (list (make-list 2048 :initial-element 0)))
(defconst *mlhx-page-stale*
  (list (append (list 1) (make-list 1023 :initial-element 0)
                (list 1) (make-list 1023 :initial-element 0))))

; The malformed logical stobjs cannot use the raw executable counterparts
; of the recursive readers.  Expand those readers in the ground proof; a
; 1,024-slot page needs more than the default 1,000 rewrite depth.  ACL2
; restores this defaults-table setting when the book finishes.
(set-rewrite-stack-limit 10000)

; fn-mlh-wfp alone REMOVED: all scalar and word types hold, but N + S = 2
; and the page array's two pages disagree with pages = 1.  The stale entry
; supplies the false answer.
(defthm mlhx-wfp-removal-witness
  (let ((fn-mlh (list (list *mlhx-page-empty* *mlhx-page-stale*) 1 2 0 0
                      (make-list 32 :initial-element 0) 0)))
    (and (fn-mlhp fn-mlh)
         (not (fn-mlh-wfp fn-mlh))
         (fn-mlh-faithful nil fn-mlh)
         (not (equal (fn-mlh-seqs nil nil fn-mlh)
                     (fn-mpxt-spec-from 0 nil nil)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-mlh-tag fn-mlh-candidates
                                    fn-mlh-okp fn-record-msgid
                                    fn-mlhp fn-mlgp fn-mlh-pgi fn-mlg-wi fn-mlh-pg-length fn-mlh-pgsp
                                    fn-mlh-pages fn-mlh-n fn-mlh-s
                                    fn-mlh-key-octets fn-mlh-keyi
                                    fn-mlh-tag-at fn-mlh-seqw
                                    fn-mlh-seq-at fn-mlh-ovf fn-mlh-abs
                                    fn-mlh-abs-pages fn-mlh-pe fn-mlh-scan
                                    fn-mlh-key-from fn-mpxt-ins
                                    fn-mpxt-confirm fn-mpxt-hitp
                                    fn-mpxl-seqs fn-mpxl-pages-okp
                                    fn-mpxl-ents-below)
                                   ((:e fn-mlh-abs-pages) (:e fn-mlh-pe)
                                    (:e fn-mlh-scan) (:e fn-mlh-key-from)))
           :expand ((:free (p fn-mlh) (fn-mlh-abs-pages p fn-mlh))
                    (:free (p j fn-mlh) (fn-mlh-pe p j fn-mlh))
                    (:free (i fn-mlh) (fn-mlh-key-from i fn-mlh))))))

; fn-mlhp alone: the flat predecessor's witness (a negative S) reads only
; pages the abstraction also reads on the paged representation, so it no
; longer separates; no witness is claimed here (the lane's LANEDUMP has it
; as an open item: prove the weakened keystone or find one).

; -----------------------------------------------------------------------------
; THE SPLIT, THE ADD, THE FOLD (lane msgid-linear-hash-2).

; 5. POSITIVE ACROSS SPLITS: 1,100 rows, distinct Message-IDs, folded by
;    the add from the set-keyed empty table: nothing unplaced, the table
;    split past one page, faithful, and the reader is the walk for rows on
;    either side of the splits.
(defun mlhx-rows-from (i n acc)
  (declare (xargs :verify-guards nil :measure (nfix (- (nfix n) (nfix i)))))
  (if (>= (nfix i) (nfix n))
      (reverse acc)
    (mlhx-rows-from (1+ (nfix i)) n
                    (cons (mlhx-held (nfix i) (concatenate 'string "<" (coerce (explode-atom (nfix i) 10) 'string) "@x>") 100)
                          acc))))

(defconst *mlhx-big* (mlhx-rows-from 0 1100 nil))

(defun mlhx-fold (rows)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-mlh
    (mv-let (result fn-mlh)
      (let ((fn-mlh (fn-mlh-set-key *mlhx-key-a* fn-mlh)))
        (mv-let (u fn-mlh)
          (fn-mlh-build-from 0 0 rows fn-mlh)
          (mv (list u (fn-mlh-pages fn-mlh) (fn-mlh-n fn-mlh) (fn-mlh-s fn-mlh) (fn-mlh-stuck fn-mlh)
                    (fn-mlhp fn-mlh) (fn-mlh-wfp fn-mlh)
                    (fn-mlh-faithful rows fn-mlh)
                    (fn-mlh-seqs "<0@x>" rows fn-mlh) (fn-mpxt-spec-from 0 "<0@x>" rows)
                    (fn-mlh-seqs "<600@x>" rows fn-mlh) (fn-mpxt-spec-from 0 "<600@x>" rows)
                    (fn-mlh-seqs "<1099@x>" rows fn-mlh) (fn-mpxt-spec-from 0 "<1099@x>" rows)
                    (fn-mlh-seqs "<none@x>" rows fn-mlh))
              fn-mlh)))
      result)))

(defconst *mlhx-big-result* (mlhx-fold *mlhx-big*))

(assert-event ; mlhx-fold-across-splits-witness
 (let ((r *mlhx-big-result*))
   (and (equal (nth 0 r) 0)                 ; nothing unplaced
        (< 1 (nth 1 r))                     ; the table split past one page
        (equal (nth 4 r) 0)                 ; no split refused
        (nth 5 r) (nth 6 r) (nth 7 r)       ; fn-mlhp, wfp, faithful
        (equal (nth 8 r) (nth 9 r)) (equal (nth 8 r) '(0))
        (equal (nth 10 r) (nth 11 r)) (equal (nth 10 r) '(600))
        (equal (nth 12 r) (nth 13 r)) (equal (nth 12 r) '(1099))
        (equal (nth 14 r) nil))))

; 6. THE SPLIT REFINES THE LOGICAL SPLIT, positive: N = 2, S = 0; tags 2
;    and 6 move (mod 4 = 2 = the new page), 4 and 3 stay; the abstraction
;    after the split is the logical split of the abstraction before it, and
;    the movers are found on the new page.
(defun mlhx-put-tags (tags seq fn-mlh)
  (declare (xargs :stobjs fn-mlh :verify-guards nil))
  (if (atom tags)
      fn-mlh
    (mv-let (placed fn-mlh)
      (fn-mlh-put (car tags) seq fn-mlh)
      (declare (ignore placed))
      (mlhx-put-tags (cdr tags) (+ 1 seq) fn-mlh))))

(defun mlhx-split-witness (tags)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-mlh
    (mv-let (result fn-mlh)
      (let* ((fn-mlh (mlhx-pages 2 fn-mlh))
             (fn-mlh (mlhx-put-tags tags 0 fn-mlh))
             (before (fn-mlh-abs fn-mlh)))
        (mv-let (ok fn-mlh)
          (fn-mlh-split fn-mlh)
          (mv (list ok (mv-let (lok ltab) (fn-mpxl-split before) (declare (ignore ltab)) lok)
                    (equal (fn-mlh-abs fn-mlh) (mv-let (lok ltab) (fn-mpxl-split before) (declare (ignore lok)) ltab))
                    (equal (fn-mlh-abs fn-mlh) before)
                    (fn-mlh-pages fn-mlh) (fn-mlh-n fn-mlh) (fn-mlh-s fn-mlh)
                    (fn-mlh-candidates 2 fn-mlh) (fn-mlh-candidates 6 fn-mlh)
                    (fn-mlh-candidates 4 fn-mlh) (fn-mlh-candidates 3 fn-mlh)
                    (if (< 2 (fn-mlh-pages fn-mlh)) (fn-mlh-pe 2 0 fn-mlh) :none))
              fn-mlh)))
      result)))

(assert-event ; mlhx-split-refines-witness
 (let ((r (mlhx-split-witness '(2 4 6 3))))
   (and (equal (nth 0 r) t) (equal (nth 1 r) t)
        (nth 2 r) (not (nth 3 r))
        (equal (nth 4 r) 3) (equal (nth 5 r) 2) (equal (nth 6 r) 1)
        (equal (nth 7 r) '(0)) (equal (nth 8 r) '(2))
        (equal (nth 9 r) '(1)) (equal (nth 10 r) '(3))
        (equal (nth 11 r) '((2 . 0) (6 . 2))))))

; 7. THE REFUSED SPLIT: 1,025 movers (tags 2 + 4k, home page 0; the last
;    overflows onto page 1 with page 0's flag set) exceed a page: the split
;    is refused exactly when the logical one is, and the table is unchanged
;    -- every entry still found.
(defun mlhx-mover-tags (k acc)
  (declare (xargs :verify-guards nil))
  (if (zp k) acc (mlhx-mover-tags (1- k) (cons (+ 2 (* 4 (1- k))) acc))))

(defconst *mlhx-refused-result* (mlhx-split-witness (mlhx-mover-tags 1025 nil)))

(assert-event ; mlhx-split-refused-witness
 (let ((r *mlhx-refused-result*))
   (and (equal (nth 0 r) nil) (equal (nth 1 r) nil)
        (nth 2 r) (nth 3 r)
        (equal (nth 4 r) 2) (equal (nth 5 r) 2) (equal (nth 6 r) 0)
        (equal (nth 7 r) '(0)))))
