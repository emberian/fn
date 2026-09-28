; fn: the page store's whole-disk refinement (lane arena-store-5, 2026-09-28).
; Prefix pgs-x-.
;
; The model (books/pagestore.lisp) is a whole disk: pages by address and,
; per root, two record slots.  The host (host/native/proto-pagestore.lisp)
; holds a HANDLE: the stobj pgs-mem, whose pgs-m[0, 1024) are the slot
; words it read from the root's page and which after an open holds the
; landed record's table (pgs-t) and directory (pgs-m from 1024), and the
; files it writes.  This book states the host's two write commands as
; squares over an abstraction from the concrete state to the model disk.
;
; The abstraction.  CS = (PAGES . ROOT-WORDS): the model pages of the page
; file and, per root name, the words of its slot page.
; `pgs-x-abs-disk' CS R PGS-MEM is the model disk whose root R is the
; handle's slot words (bound first), each slot decoded by
; `pgs-x-rec-of-words' -- the very record `pgs-x-read-rec' answers
; (pgs-x-read-rec-is-rec-of-words).  A write is abstracted as the model's
; content of the words the host writes: a data page's 2048 words, a table
; page's and the directory run's words decoded (`pgs-x-abs-writes').
;
; Keystones (the host calls the subject):
;   pgs-x-fork-refines: `pgs-x-fork' (fnps-cmd-branch) leaves the root page
;     that, bound as the new root, makes the abstraction `pgs-fork''s disk,
;     when the model's open of R lands on the slot K the host passes.
;   pgs-x-commit-refines-plan: the plan `pgs-x-commit' (fnps-commit)
;     answers IS `pgs-plan-commit' over the abstraction; with
;   pgs-x-commit-refines-crash / pgs-x-commit-refines-commit: the files
;     after the host's writes (any KEEP subset; the record in the handle's
;     slot words) abstract to `pgs-crash' of that plan, all kept to
;     `pgs-commit'.
; Their hypotheses, in words: the model's open of R lands (on the slot
; the handle's other slot is not), the handle's table and directory are
; that record's (`pgs-sp', `pgs-sd'), TXID is one past the newest valid
; slot, the free list holds naturals, the handle's two invariants; and
; A-PGS-OBSERVE, stated as hypotheses about the digest seam: the digests
; the executable computed (BLAKE3 of the words, proved in
; books/pagestore-words-blake3.lisp) are `pgs-digest' of the same
; objects -- the dirty pages, the rewritten table pages, the record's
; check and its directory digest.  The teeth
; (tests/acl2/pagestore-refine-tests.lisp) attach the seam to BLAKE3 of
; those words and every hypothesis holds on a ground store.
;
; NOT proved here: the open square.  The host's open is a host loop over
; ACL2 steps and fills (fnps-open, fnps-try); no ACL2 function composes it,
; and its lazy mode defers table-shape checks the model's makes
; (L-PGS-LAZY-SHAPE), so the handle's agreement with `pgs-open' is a
; HYPOTHESIS of both squares; the model pages are not derived from the
; page file through A-PGS-HOST-IO (a page's model content is typed by the
; record that names it: data words, a decoded table, a decoded run).
(in-package "ACL2")
(include-book "pagestore-keystones")
(include-book "pagestore-exec")
(local (include-book "arithmetic/top" :dir :system))

(local (in-theory (disable floor mod pgs-ntables-step)))

(defun pgs-x-zero-listp (ws)
  (declare (xargs :guard t))
  (if (consp ws) (and (equal (car ws) 0) (pgs-x-zero-listp (cdr ws))) t))

(defun pgs-x-rec-of-words (ws)
  (declare (xargs :guard (true-listp ws)))
  (cond ((pgs-x-zero-listp ws) nil)
        ((and (equal (nth 0 ws) *pgs-magic*) (equal (nth 4 ws) *pgs-page-words*)
              (equal (nth 5 ws) 0) (equal (nth 6 ws) 0) (equal (nth 7 ws) 0)
              (equal (nth 12 ws) 0) (equal (nth 13 ws) 0) (equal (nth 14 ws) 0) (equal (nth 15 ws) 0))
         (list :pgs-commit (nth 1 ws) (nth 2 ws) (nth 3 ws)
               (pgs-h64 (nth 11 ws) (pgs-h64 (nth 10 ws) (pgs-h64 (nth 9 ws) (nth 8 ws))))
               (pgs-h64 (nth 19 ws) (pgs-h64 (nth 18 ws) (pgs-h64 (nth 17 ws) (nth 16 ws))))))
        (t :torn)))

(defthm pgs-x-read-rec-is-rec-of-words
  (implies (natp base)
           (equal (mv-nth 0 (pgs-x-read-rec base pgs-mem fn-octets-pg))
                  (pgs-x-rec-of-words (pgs-x-words 1 base 20 pgs-mem))))
  :hints (("Goal" :in-theory (enable pgs-x-read-rec pgs-x-word$inline)
                  :expand ((:free (a k) (pgs-x-words 1 a k pgs-mem))
                           (:free (lo hi) (pgs-x-zero-range 1 lo hi pgs-mem))))))

(local
 (defun pgs-x-words2-ind (a j k)
   (if (or (zp j) (zp k)) (list a j k) (pgs-x-words2-ind (+ 1 a) (1- j) (1- k)))))

(defthm pgs-x-take-of-words
  (implies (and (natp j) (natp k) (<= j k))
           (equal (take j (pgs-x-words s a k pgs-mem)) (pgs-x-words s a j pgs-mem)))
  :hints (("Goal" :induct (pgs-x-words2-ind a j k)
                  :expand ((pgs-x-words s a k pgs-mem) (pgs-x-words s a j pgs-mem)))))

(defthm pgs-x-nthcdr-of-words
  (implies (and (natp j) (natp k) (natp a) (<= j k))
           (equal (nthcdr j (pgs-x-words s a k pgs-mem)) (pgs-x-words s (+ a j) (- k j) pgs-mem)))
  :hints (("Goal" :induct (pgs-x-words2-ind a j k)
                  :expand ((pgs-x-words s a k pgs-mem) (pgs-x-words s a j pgs-mem)))))

(defun pgs-x-slots-of-words (ws)
  (declare (xargs :guard (true-listp ws)))
  (cons (pgs-x-rec-of-words (take 20 ws)) (pgs-x-rec-of-words (take 20 (nthcdr 512 ws)))))

(defun pgs-x-abs-roots (rw)
  (declare (xargs :guard t))
  (if (atom rw)
      nil
    (if (consp (car rw))
        (cons (cons (caar rw) (pgs-x-slots-of-words (true-list-fix (cdar rw))))
              (pgs-x-abs-roots (cdr rw)))
      (pgs-x-abs-roots (cdr rw)))))

(defun pgs-x-abs-disk (cs name pgs-mem)
  (declare (xargs :stobjs pgs-mem :verify-guards nil))
  (cons (car cs)
        (cons (cons name (pgs-x-slots-of-words (pgs-x-words 1 0 1024 pgs-mem)))
              (pgs-x-abs-roots (cdr cs)))))

(defun pgs-x-cs-put-root (name w cs)
  ; The files CS with root NAME's page W (bound first).
  (declare (xargs :verify-guards nil))
  (cons (car cs) (cons (cons name w) (cdr cs))))

(defun pgs-x-copy-words (from to k pgs-mem)
  (declare (xargs :stobjs pgs-mem
                  :guard (and (natp from) (natp to) (natp k)
                              (<= (+ from k) (pgs-m-length pgs-mem))
                              (<= (+ to k) (pgs-m-length pgs-mem)))
                  :measure (nfix k)))
  (if (zp k)
      pgs-mem
    (let ((pgs-mem (pgs-x-put 1 to (pgs-x-word 1 from pgs-mem) pgs-mem)))
      (pgs-x-copy-words (+ 1 from) (+ 1 to) (1- k) pgs-mem))))

(defthm pgs-x-copy-words-facts
  (implies (and (natp to) (natp k) (natp from) (<= (+ to k) (pgs-m-length pgs-mem))
                (<= (+ from k) (pgs-m-length pgs-mem)))
           (and (equal (pgs-m-length (pgs-x-copy-words from to k pgs-mem)) (pgs-m-length pgs-mem))
                (implies (pgs-memp pgs-mem) (pgs-memp (pgs-x-copy-words from to k pgs-mem)))))
  :hints (("Goal" :induct (pgs-x-copy-words from to k pgs-mem))))

(defthm pgs-x-word-of-copy-words
  (implies (and (natp from) (natp to) (natp k) (natp j) (<= (+ to k) from))
           (equal (pgs-x-word 1 j (pgs-x-copy-words from to k pgs-mem))
                  (if (and (<= to j) (< j (+ to k)))
                      (pgs-x-word 1 (+ from (- j to)) pgs-mem)
                    (pgs-x-word 1 j pgs-mem))))
  :hints (("Goal" :induct (pgs-x-copy-words from to k pgs-mem))))

(defthm pgs-x-word-of-zero-words-1
  (implies (and (natp a) (natp k) (natp j))
           (equal (pgs-x-word 1 j (pgs-x-zero-words 1 a k pgs-mem))
                  (if (and (<= a j) (< j (+ a k))) 0 (pgs-x-word 1 j pgs-mem))))
  :hints (("Goal" :in-theory (enable pgs-x-zero-words) :induct (pgs-x-zero-words 1 a k pgs-mem))))

(defun pgs-x-fork (k pgs-mem)
  (declare (xargs :stobjs pgs-mem :guard t))
  (if (not (and (or (equal k 0) (equal k 1)) (<= 1024 (pgs-m-length pgs-mem))))
      (mv (list :refused :state-unloaded) pgs-mem)
    (let* ((pgs-mem (if (equal k 1) (pgs-x-copy-words 512 0 20 pgs-mem) pgs-mem))
           (pgs-mem (pgs-x-zero-words 1 20 1004 pgs-mem)))
      (mv nil pgs-mem))))

(defthm pgs-x-fork-facts
  (implies (and (or (equal k 0) (equal k 1)) (<= 1024 (pgs-m-length pgs-mem)))
           (and (equal (mv-nth 0 (pgs-x-fork k pgs-mem)) nil)
                (equal (pgs-m-length (mv-nth 1 (pgs-x-fork k pgs-mem))) (pgs-m-length pgs-mem))
                (implies (pgs-memp pgs-mem) (pgs-memp (mv-nth 1 (pgs-x-fork k pgs-mem)))))))

(defthm pgs-x-word-of-fork
  (implies (and (or (equal k 0) (equal k 1)) (<= 1024 (pgs-m-length pgs-mem)) (natp j))
           (equal (pgs-x-word 1 j (mv-nth 1 (pgs-x-fork k pgs-mem)))
                  (cond ((< j 20) (pgs-x-word 1 (+ j (* 512 k)) pgs-mem))
                        ((< j 1024) 0)
                        (t (pgs-x-word 1 j pgs-mem))))))

(in-theory (disable pgs-x-fork))

(local
 (defun pgs-x-words-ind (a n)
   (if (zp n) a (pgs-x-words-ind (+ 1 a) (1- n)))))

(defthm pgs-x-words-of-fork-slot0
  (implies (and (or (equal k 0) (equal k 1)) (<= 1024 (pgs-m-length pgs-mem))
                (natp a) (natp n) (<= (+ a n) 20))
           (equal (pgs-x-words 1 a n (mv-nth 1 (pgs-x-fork k pgs-mem)))
                  (pgs-x-words 1 (+ a (* 512 k)) n pgs-mem)))
  :hints (("Goal" :induct (pgs-x-words-ind a n)
                  :expand ((:free (a m) (pgs-x-words 1 a n m))))))

(defthm pgs-x-words-of-fork-zero
  (implies (and (or (equal k 0) (equal k 1)) (<= 1024 (pgs-m-length pgs-mem))
                (natp a) (natp n) (<= 20 a) (<= (+ a n) 1024))
           (equal (pgs-x-words 1 a n (mv-nth 1 (pgs-x-fork k pgs-mem)))
                  (pgs-zeros n)))
  :hints (("Goal" :induct (pgs-x-words-ind a n)
                  :expand ((:free (a m) (pgs-x-words 1 a n m)) (pgs-zeros n)))))

(defthm pgs-x-slots-of-fork
  (implies (and (or (equal k 0) (equal k 1)) (<= 1024 (pgs-m-length pgs-mem)))
           (equal (pgs-x-slots-of-words (pgs-x-words 1 0 1024 (mv-nth 1 (pgs-x-fork k pgs-mem))))
                  (cons (pgs-slot k (pgs-x-slots-of-words (pgs-x-words 1 0 1024 pgs-mem))) nil)))
  :hints (("Goal" :in-theory (disable pgs-x-words))))

(defthm pgs-x-fork-refines
  (implies (and (equal (car (pgs-open (pgs-x-abs-disk cs r pgs-mem) r mode)) :ok)
                (equal (second (pgs-open (pgs-x-abs-disk cs r pgs-mem) r mode)) k)
                (<= 1024 (pgs-m-length pgs-mem)))
           (equal (pgs-x-abs-disk (pgs-x-cs-put-root r (pgs-x-words 1 0 1024 pgs-mem) cs) r2
                                  (mv-nth 1 (pgs-x-fork k pgs-mem)))
                  (pgs-fork (pgs-x-abs-disk cs r pgs-mem) r r2 mode)))
  :hints (("Goal" :in-theory (e/d (pgs-c-k0) (pgs-open pgs-x-words pgs-x-slots-of-words pgs-slot))
                  :use ((:instance pgs-c-open-facts (disk (pgs-x-abs-disk cs r pgs-mem)))))))

; -- Frames of the commit's effect: the image (pgs-w) is untouched, and so
;    are the metadata words below the directory run outside the written slot.

(defthm pgs-x-wi-of-put-1
  (equal (pgs-wi j (pgs-x-put 1 a v pgs-mem)) (pgs-wi j pgs-mem))
  :hints (("Goal" :in-theory (enable pgs-x-put$inline pgs-wi update-pgs-mi))))

(defthm pgs-x-wi-of-zero-words
  (equal (pgs-wi j (pgs-x-zero-words 1 a k pgs-mem)) (pgs-wi j pgs-mem))
  :hints (("Goal" :in-theory (enable pgs-x-zero-words) :induct (pgs-x-zero-words 1 a k pgs-mem))))

(defthm pgs-x-wi-of-put-dig4
  (equal (pgs-wi j (pgs-x-put-dig4 1 a d pgs-mem)) (pgs-wi j pgs-mem))
  :hints (("Goal" :in-theory (enable pgs-x-put-dig4))))

(defthm pgs-x-wi-of-write-rec
  (equal (pgs-wi j (mv-nth 1 (pgs-x-write-rec slot txid addr npages ddig pgs-mem fn-octets-pg)))
         (pgs-wi j pgs-mem))
  :hints (("Goal" :in-theory (enable pgs-x-write-rec))))

(defthm pgs-x-wi-of-update-tvi
  (equal (pgs-wi j (update-pgs-tvi i v pgs-mem)) (pgs-wi j pgs-mem))
  :hints (("Goal" :in-theory (enable pgs-wi update-pgs-tvi))))

(defthm pgs-x-wi-of-mark-tables1
  (equal (pgs-wi j (pgs-x-mark-tables1 tl pgs-mem)) (pgs-wi j pgs-mem))
  :hints (("Goal" :induct (pgs-x-mark-tables1 tl pgs-mem))))

(defthm pgs-x-wi-of-resize-tv
  (equal (pgs-wi j (resize-pgs-tv k pgs-mem)) (pgs-wi j pgs-mem))
  :hints (("Goal" :in-theory (enable pgs-wi resize-pgs-tv))))

(defthm pgs-x-wi-of-mark-tables
  (equal (pgs-wi j (pgs-x-mark-tables tl nt2 pgs-mem)) (pgs-wi j pgs-mem))
  :hints (("Goal" :in-theory (enable pgs-x-mark-tables))))

(defthm pgs-x-wi-of-ensure-m
  (equal (pgs-wi j (pgs-x-ensure-m k pgs-mem)) (pgs-wi j pgs-mem))
  :hints (("Goal" :in-theory (enable pgs-x-resize pgs-wi resize-pgs-m))))

(defthm pgs-x-wi-of-commit-apply
  (equal (pgs-wi j (mv-nth 1 (pgs-x-commit-apply lpages n txid slot plan pgs-mem fn-octets-pg)))
         (pgs-wi j pgs-mem))
  :hints (("Goal" :in-theory (disable pgs-x-plan-entries pgs-x-ensure-m pgs-x-mark-tables
                                      pgs-x-words-digest pgs-x-write-rec pgs-x-table-digests))))

(defthm pgs-x-word-1-of-grow-1
  (implies (and (natp j) (< j (pgs-m-length pgs-mem)))
           (equal (pgs-x-word 1 j (pgs-x-grow 1 b k pgs-mem)) (pgs-x-word 1 j pgs-mem)))
  :hints (("Goal" :in-theory (enable pgs-x-grow pgs-x-len$inline))))

(defthm pgs-x-word-below-base-of-plan-entries
  (implies (and (natp j) (natp b) (< j b) (< j (pgs-m-length pgs-mem)))
           (equal (pgs-x-word 1 j (mv-nth 1 (pgs-x-plan-entries 1 b lpages fresh digests txid n pgs-mem)))
                  (pgs-x-word 1 j pgs-mem)))
  :hints (("Goal" :induct (pgs-x-plan-entries 1 b lpages fresh digests txid n pgs-mem)
                  :in-theory (e/d (pgs-x-eaddr) (pgs-x-grow pgs-x-set-entry pgs-x-grow-need)))))

(defthm pgs-x-write-rec-frame-below
  (implies (and (natp slot) (natp j) (< j slot))
           (equal (pgs-x-word 1 j (mv-nth 1 (pgs-x-write-rec slot txid addr npages ddig pgs-mem fn-octets-pg)))
                  (pgs-x-word 1 j pgs-mem)))
  :hints (("Goal" :in-theory (enable pgs-x-write-rec))))

(defthm pgs-x-rec-of-write-rec
  ; The slot's words after `pgs-x-write-rec' decode to the record it answers.
  (implies (or (equal slot 0) (equal slot 512))
           (equal (pgs-x-rec-of-words
                   (pgs-x-words 1 slot 20 (mv-nth 1 (pgs-x-write-rec slot txid addr npages ddig pgs-mem fn-octets-pg))))
                  (mv-nth 0 (pgs-x-write-rec slot txid addr npages ddig pgs-mem fn-octets-pg))))
  :hints (("Goal" :in-theory (enable pgs-x-write-rec pgs-x-put-dig4)
                  :cases ((equal slot 0))
                  :expand ((:free (a k m) (pgs-x-words 1 a k m))))))

(defthm pgs-x-write-rec-record
  (equal (mv-nth 0 (pgs-x-write-rec slot txid addr npages ddig pgs-mem fn-octets-pg))
         (list :pgs-commit (pgs-dlo txid) (pgs-dlo addr) (pgs-dlo npages)
               (pgs-x-dig4 1 (+ 8 slot) (mv-nth 1 (pgs-x-write-rec slot txid addr npages ddig pgs-mem fn-octets-pg)))
               (pgs-x-dig4 1 (+ 16 slot) (mv-nth 1 (pgs-x-write-rec slot txid addr npages ddig pgs-mem fn-octets-pg)))))
  :hints (("Goal" :in-theory (e/d (pgs-x-write-rec) (pgs-x-dig4)))))

(defthm pgs-x-word-1-of-ensure-m
  (implies (and (natp j) (natp k) (< j (pgs-m-length pgs-mem)))
           (equal (pgs-x-word 1 j (pgs-x-ensure-m k pgs-mem)) (pgs-x-word 1 j pgs-mem)))
  :hints (("Goal" :in-theory (enable pgs-x-len$inline))))

(defthm pgs-x-commit-prepare-bounds
  (implies (not (mv-nth 0 (pgs-x-commit-prepare lpages n txid alloc pgs-mem fn-octets-pg)))
           (let ((plan (mv-nth 1 (pgs-x-commit-prepare lpages n txid alloc pgs-mem fn-octets-pg))))
             (and (< (nth 4 plan) 18446744073709551616)
                  (< (nth 6 plan) 18446744073709551616))))
  :hints (("Goal" :in-theory (disable pgs-alloc pgs-grown-len pgs-touched pgs-lpages-ok
                                      pgs-x-plan-fits pgs-ntables pgs-ntables-as-tq
                                      pgs-x-dirty-digests pgs-ptab-run-pages
                                      pgs-x-lpages-resident pgs-x-tables-ready pgs-x-u64-bounded
                                      pgs-dir-run-pages)))
  :rule-classes nil)

(defthm pgs-x-commit-apply-result
  (implies (and (pgs-x-commit-plan-p (list tl fresh tfresh digests rs m n2 nt2 a2))
                (natp txid) (< txid 18446744073709551616) (< rs 18446744073709551616)
                (< n2 18446744073709551616) (or (equal slot 0) (equal slot 512))
                (<= 1024 (pgs-m-length pgs-mem)))
           (let* ((r (pgs-x-commit-apply lpages n txid slot (list tl fresh tfresh digests rs m n2 nt2 a2)
                                         pgs-mem fn-octets-pg))
                  (res (mv-nth 0 r))
                  (m2 (mv-nth 1 r)))
             (and (equal (nth 5 res) rs)
                  (equal (nth 6 res) m)
                  (equal (nth 7 res) a2)
                  (equal (nth 8 res) digests)
                  (equal (nth 1 res) (list :pgs-commit txid rs n2
                                           (pgs-x-dig4 1 (+ 8 slot) m2) (pgs-x-dig4 1 (+ 16 slot) m2)))
                  (equal (pgs-x-rec-of-words (pgs-x-words 1 slot 20 m2)) (nth 1 res))
                  (implies (and (natp j) (< j 1024) (or (< j slot) (<= (+ slot 20) j)))
                           (equal (pgs-x-word 1 j m2) (pgs-x-word 1 j pgs-mem)))
                  (equal (pgs-wi j m2) (pgs-wi j pgs-mem)))))
  :hints (("Goal" :in-theory (e/d (pgs-x-commit-apply)
                                  (pgs-ntables pgs-ntables-as-tq
                                   pgs-ptab-run-pages pgs-x-tab pgs-x-dir pgs-plan-ptab
                                   pgs-x-plan-entries
                                   pgs-x-mark-tables pgs-x-table-digests pgs-x-ensure-m
                                   pgs-x-words-digest pgs-x-write-rec pgs-x-dig4 pgs-x-words
                                   pgs-x-rec-of-words)))))

(defthm pgs-x-commit-plan-verdict
  (implies (equal (car (mv-nth 0 (pgs-x-commit lpages n txid alloc slot pgs-mem fn-octets-pg))) :plan)
           (not (mv-nth 0 (pgs-x-commit-prepare lpages n txid alloc pgs-mem fn-octets-pg))))
  :hints (("Goal" :in-theory (union-theories '(pgs-x-commit pgs-x-commit-prepare-verdict-not-plan)
                                             (theory 'minimal-theory))))
  :rule-classes nil)

(defmacro pgs-x-plan-list ()
  '(list (pgs-touched lpages nil)
         (take (len lpages) (true-list-fix (second (pgs-alloc (+ (len lpages) (len (pgs-touched lpages nil))) (pgs-dir-run-pages (pgs-grown-len lpages n)) alloc))))
         (nthcdr (len lpages) (true-list-fix (second (pgs-alloc (+ (len lpages) (len (pgs-touched lpages nil))) (pgs-dir-run-pages (pgs-grown-len lpages n)) alloc))))
         (mv-nth 0 (pgs-x-dirty-digests lpages pgs-mem fn-octets-pg))
         (nfix (first (pgs-alloc (+ (len lpages) (len (pgs-touched lpages nil))) (pgs-dir-run-pages (pgs-grown-len lpages n)) alloc)))
         (pgs-ptab-run-pages (pgs-ntables (pgs-grown-len lpages n)))
         (pgs-grown-len lpages n)
         (pgs-ntables (pgs-grown-len lpages n))
         (list (third (pgs-alloc (+ (len lpages) (len (pgs-touched lpages nil))) (pgs-dir-run-pages (pgs-grown-len lpages n)) alloc)) (fourth (pgs-alloc (+ (len lpages) (len (pgs-touched lpages nil))) (pgs-dir-run-pages (pgs-grown-len lpages n)) alloc)))))

(defthm pgs-x-commit-as-apply
  (implies (and (natp n) (nat-listp lpages)
                (equal (car (mv-nth 0 (pgs-x-commit lpages n txid alloc slot pgs-mem fn-octets-pg))) :plan))
           (and (equal (pgs-x-commit lpages n txid alloc slot pgs-mem fn-octets-pg)
                       (pgs-x-commit-apply lpages n txid slot (pgs-x-plan-list) pgs-mem
                                           (mv-nth 2 (pgs-x-commit-prepare lpages n txid alloc pgs-mem fn-octets-pg))))
                (pgs-x-commit-plan-p (pgs-x-plan-list))
                (< (nfix (first (pgs-alloc (+ (len lpages) (len (pgs-touched lpages nil))) (pgs-dir-run-pages (pgs-grown-len lpages n)) alloc))) 18446744073709551616)
                (< (pgs-grown-len lpages n) 18446744073709551616)
                (< (nfix txid) 18446744073709551616)))
  :hints (("Goal" :in-theory (union-theories '(pgs-x-commit pgs-x-commit-prepare-verdict-not-plan pgs-x-plan-fits mv-nth
                                               nth-0-cons nth-add1 (:executable-counterpart zp) (:executable-counterpart binary-+)
                                               zp-open car-cons cdr-cons)
                                             (theory 'minimal-theory))
                  :use (pgs-x-commit-plan-verdict pgs-x-commit-prepare-plan pgs-x-commit-prepare-plan-p
                        pgs-x-commit-prepare-bounds)))
  :rule-classes nil)

(defthm pgs-x-commit-result
  ; What `pgs-x-commit' answers and leaves when it answers a plan, past
  ; `pgs-x-commit-refines': the run start, the run's pages, the allocator
  ; state after, the record's fields, the slot's words decoding to that
  ; record, the other metadata words below the directory run, the image.
  (implies (and (natp n) (nat-listp lpages) (natp txid) (or (equal slot 0) (equal slot 512))
                (<= 1024 (pgs-m-length pgs-mem))
                (equal (car (mv-nth 0 (pgs-x-commit lpages n txid alloc slot pgs-mem fn-octets-pg))) :plan))
           (let* ((r (pgs-x-commit lpages n txid alloc slot pgs-mem fn-octets-pg))
                  (res (mv-nth 0 r))
                  (m2 (mv-nth 1 r))
                  (n2 (pgs-grown-len lpages n))
                  (al (pgs-alloc (+ (len lpages) (len (pgs-touched lpages nil))) (pgs-dir-run-pages n2) alloc)))
             (and (equal (nth 5 res) (nfix (first al)))
                  (equal (nth 6 res) (pgs-ptab-run-pages (pgs-ntables n2)))
                  (equal (nth 7 res) (list (third al) (fourth al)))
                  (equal (nth 8 res) (mv-nth 0 (pgs-x-dirty-digests lpages pgs-mem fn-octets-pg)))
                  (equal (nth 1 res) (list :pgs-commit txid (nfix (first al)) n2
                                           (pgs-x-dig4 1 (+ 8 slot) m2) (pgs-x-dig4 1 (+ 16 slot) m2)))
                  (equal (pgs-x-rec-of-words (pgs-x-words 1 slot 20 m2)) (nth 1 res))
                  (implies (and (natp j) (< j 1024) (or (< j slot) (<= (+ slot 20) j)))
                           (equal (pgs-x-word 1 j m2) (pgs-x-word 1 j pgs-mem)))
                  (equal (pgs-wi j m2) (pgs-wi j pgs-mem)))))
  :hints (("Goal" :in-theory (union-theories '(pgs-x-nfix-when-natp natp)
                                             (theory 'minimal-theory))
                  :use (pgs-x-commit-as-apply
                        (:instance pgs-x-commit-apply-result
                                   (tl (pgs-touched lpages nil))
                                   (fresh (take (len lpages) (true-list-fix (second (pgs-alloc (+ (len lpages) (len (pgs-touched lpages nil))) (pgs-dir-run-pages (pgs-grown-len lpages n)) alloc)))))
                                   (tfresh (nthcdr (len lpages) (true-list-fix (second (pgs-alloc (+ (len lpages) (len (pgs-touched lpages nil))) (pgs-dir-run-pages (pgs-grown-len lpages n)) alloc)))))
                                   (digests (mv-nth 0 (pgs-x-dirty-digests lpages pgs-mem fn-octets-pg)))
                                   (rs (nfix (first (pgs-alloc (+ (len lpages) (len (pgs-touched lpages nil))) (pgs-dir-run-pages (pgs-grown-len lpages n)) alloc))))
                                   (m (pgs-ptab-run-pages (pgs-ntables (pgs-grown-len lpages n))))
                                   (n2 (pgs-grown-len lpages n))
                                   (nt2 (pgs-ntables (pgs-grown-len lpages n)))
                                   (a2 (list (third (pgs-alloc (+ (len lpages) (len (pgs-touched lpages nil))) (pgs-dir-run-pages (pgs-grown-len lpages n)) alloc)) (fourth (pgs-alloc (+ (len lpages) (len (pgs-touched lpages nil))) (pgs-dir-run-pages (pgs-grown-len lpages n)) alloc))))
                                   (fn-octets-pg (mv-nth 2 (pgs-x-commit-prepare lpages n txid alloc pgs-mem fn-octets-pg))))))))

; -- The abstraction of what the commit writes.

(defun pgs-x-abs-dirty (lpages pgs-mem)
  ; The model's DIRTY for image pages LPAGES: each page's 2048 words.
  (declare (xargs :stobjs pgs-mem :verify-guards nil))
  (if (atom lpages)
      nil
    (cons (cons (car lpages) (pgs-x-words 0 (* 2048 (nfix (car lpages))) 2048 pgs-mem))
          (pgs-x-abs-dirty (cdr lpages) pgs-mem))))

(defun pgs-x-abs-table-writes (tl tfresh n2 pgs-mem)
  ; The table-page writes: table page T's words, decoded, to its fresh address.
  (declare (xargs :stobjs pgs-mem :verify-guards nil))
  (if (atom tl)
      nil
    (cons (cons (car tfresh)
                (pgs-decode-table (pgs-x-words 2 (* 2048 (nfix (car tl))) 2048 pgs-mem)
                                  (pgs-x-tcnt (car tl) n2)))
          (pgs-x-abs-table-writes (cdr tl) (cdr tfresh) n2 pgs-mem))))

(defun pgs-x-abs-writes (lpages res pgs-mem)
  ; The writes the host performs after `pgs-x-commit' answered RES and
  ; left PGS-MEM, as the model's writes: each data page's words, each
  ; touched table page's words decoded, the directory run's words decoded.
  (declare (xargs :stobjs pgs-mem :verify-guards nil))
  (let* ((n2 (pgs-rec-npages (nth 1 res))))
    (append (pgs-page-writes (pgs-x-abs-dirty lpages pgs-mem) (nth 2 res))
            (pgs-x-abs-table-writes (nth 3 res) (nth 4 res) n2 pgs-mem)
            (list (cons (nth 5 res)
                        (pgs-decode-table (pgs-x-words 1 *pgs-x-dir-base* (* 2048 (nth 6 res)) pgs-mem)
                                          (pgs-ntables n2)))))))

(defthm pgs-x-dirty-lpages-of-abs-dirty
  (implies (nat-listp lpages)
           (and (equal (pgs-dirty-lpages (pgs-x-abs-dirty lpages pgs-mem)) lpages)
                (equal (len (pgs-x-abs-dirty lpages pgs-mem)) (len lpages))
                (alistp (pgs-x-abs-dirty lpages pgs-mem)))))

(defthm pgs-x-abs-table-writes-is-model
  (implies (and (pgs-x-tab-inv n2 pgs-mem) (pgs-memp pgs-mem) (nat-listp tl)
                (pgs-all-below tl (pgs-ntables n2)))
           (equal (pgs-x-abs-table-writes tl tfresh n2 pgs-mem)
                  (pgs-page-writes (pgs-table-dirty tl (pgs-chunk (pgs-x-tab n2 pgs-mem))) tfresh)))
  :hints (("Goal" :induct (pgs-x-abs-table-writes tl tfresh n2 pgs-mem)
                  :in-theory (disable pgs-x-tab pgs-chunk pgs-x-tcnt pgs-ntables pgs-ntables-as-tq
                                      pgs-x-table-page-words))))

(defthm pgs-memp-of-commit-apply
  (implies (and (pgs-memp pgs-mem) (or (equal slot 0) (equal slot 512)))
           (pgs-memp (mv-nth 1 (pgs-x-commit-apply lpages n txid slot plan pgs-mem fn-octets-pg))))
  :hints (("Goal" :in-theory (disable pgs-x-plan-entries pgs-x-ensure-m pgs-x-mark-tables
                                      pgs-x-words-digest pgs-x-write-rec pgs-x-table-digests))))

(defthm pgs-memp-of-commit
  (implies (and (pgs-memp pgs-mem) (or (equal slot 0) (equal slot 512)))
           (pgs-memp (mv-nth 1 (pgs-x-commit lpages n txid alloc slot pgs-mem fn-octets-pg))))
  :hints (("Goal" :in-theory (disable pgs-x-commit-apply pgs-x-commit-prepare))))

(defmacro pgs-x-commit-hyps-basic ()
  '(and (natp n) (nat-listp lpages) (natp txid) (or (equal slot 0) (equal slot 512))
        (<= 1024 (pgs-m-length pgs-mem))
        (equal (car (mv-nth 0 (pgs-x-commit lpages n txid alloc slot pgs-mem fn-octets-pg))) :plan)))

(defthm pgs-x-words-0-of-commit
  (implies (pgs-x-commit-hyps-basic)
           (equal (pgs-x-words 0 a k (mv-nth 1 (pgs-x-commit lpages n txid alloc slot pgs-mem fn-octets-pg)))
                  (pgs-x-words 0 a k pgs-mem)))
  :hints (("Goal" :induct (pgs-x-words 0 a k pgs-mem)
                  :in-theory (e/d (pgs-x-word$inline) (pgs-x-commit)))))

(defthm pgs-x-abs-dirty-of-commit
  (implies (pgs-x-commit-hyps-basic)
           (equal (pgs-x-abs-dirty ls (mv-nth 1 (pgs-x-commit lpages n txid alloc slot pgs-mem fn-octets-pg)))
                  (pgs-x-abs-dirty ls pgs-mem)))
  :hints (("Goal" :induct (pgs-x-abs-dirty ls pgs-mem)
                  :in-theory (disable pgs-x-commit))))

(defthm pgs-x-words-1-below-dir-of-commit
  (implies (and (pgs-x-commit-hyps-basic) (natp a) (natp k) (<= (+ a k) 1024)
                (or (<= (+ a k) slot) (<= (+ slot 20) a)))
           (equal (pgs-x-words 1 a k (mv-nth 1 (pgs-x-commit lpages n txid alloc slot pgs-mem fn-octets-pg)))
                  (pgs-x-words 1 a k pgs-mem)))
  :hints (("Goal" :induct (pgs-x-words 1 a k pgs-mem)
                  :in-theory (disable pgs-x-commit))))

(defthm pgs-x-slots-of-commit
  ; The handle's slot words after the commit: the record in the slot the
  ; open did not land on, the other slot as it was.
  (implies (pgs-x-commit-hyps-basic)
           (equal (pgs-x-slots-of-words
                   (pgs-x-words 1 0 1024 (mv-nth 1 (pgs-x-commit lpages n txid alloc slot pgs-mem fn-octets-pg))))
                  (pgs-set-slot (if (equal slot 0) 0 1)
                                (nth 1 (mv-nth 0 (pgs-x-commit lpages n txid alloc slot pgs-mem fn-octets-pg)))
                                (pgs-x-slots-of-words (pgs-x-words 1 0 1024 pgs-mem)))))
  :hints (("Goal" :in-theory (disable pgs-x-commit pgs-x-words pgs-x-rec-of-words pgs-x-commit-result)
                  :cases ((equal slot 0))
                  :use pgs-x-commit-result)))

; -- The plan square, in named parts.

(defun-nx pgs-x-cres (lpages n txid alloc slot pgs-mem fn-octets-pg)
  (mv-nth 0 (pgs-x-commit lpages n txid alloc slot pgs-mem fn-octets-pg)))
(defun-nx pgs-x-cmem (lpages n txid alloc slot pgs-mem fn-octets-pg)
  (mv-nth 1 (pgs-x-commit lpages n txid alloc slot pgs-mem fn-octets-pg)))

(defmacro pgs-x-res () '(pgs-x-cres lpages n txid alloc slot pgs-mem fn-octets-pg))
(defmacro pgs-x-m2 () '(pgs-x-cmem lpages n txid alloc slot pgs-mem fn-octets-pg))
(defmacro pgs-x-al ()
  '(pgs-alloc (+ (len lpages) (len (pgs-touched lpages nil))) (pgs-dir-run-pages (pgs-grown-len lpages n)) alloc))

(defthm pgs-x-abs-disk-parts
  (and (equal (pgs-pages (pgs-x-abs-disk cs r pgs-mem)) (car cs))
       (equal (pgs-root-slots r (pgs-x-abs-disk cs r pgs-mem))
              (pgs-x-slots-of-words (pgs-x-words 1 0 1024 pgs-mem)))))

(defthm pgs-x-commit-facts-named
  ; pgs-x-commit-refines and pgs-x-commit-result over the named parts.
  (implies (and (pgs-x-commit-hyps-basic) (pgs-memp pgs-mem)
                (pgs-x-tab-inv n pgs-mem)
                (pgs-x-dir-inv *pgs-x-dir-base* (pgs-ntables n) pgs-mem))
           (let ((res (pgs-x-res)) (m2 (pgs-x-m2))
                 (n2 (pgs-grown-len lpages n)) (tl (pgs-touched lpages nil)) (al (pgs-x-al)))
             (and (equal (nth 3 res) tl)
                  (equal (nth 2 res) (take (len lpages) (true-list-fix (second al))))
                  (equal (nth 4 res) (nthcdr (len lpages) (true-list-fix (second al))))
                  (equal (nth 5 res) (nfix (first al)))
                  (equal (nth 6 res) (pgs-ptab-run-pages (pgs-ntables n2)))
                  (equal (nth 7 res) (list (third al) (fourth al)))
                  (equal (nth 8 res) (mv-nth 0 (pgs-x-dirty-digests lpages pgs-mem fn-octets-pg)))
                  (equal (nth 1 res) (list :pgs-commit txid (nfix (first al)) n2
                                           (pgs-x-dig4 1 (+ 8 slot) m2) (pgs-x-dig4 1 (+ 16 slot) m2)))
                  (equal (pgs-x-tab n2 m2)
                         (pgs-plan-ptab (pgs-x-tab n pgs-mem) lpages (nth 2 res) (nth 8 res) txid))
                  (equal (pgs-x-dir (pgs-ntables n2) m2)
                         (pgs-plan-ptab (pgs-x-dir (pgs-ntables n) pgs-mem) tl (nth 4 res) (nth 9 res) txid))
                  (pgs-x-tab-inv n2 m2)
                  (pgs-x-dir-inv *pgs-x-dir-base* (pgs-ntables n2) m2)
                  (pgs-memp m2)
                  (equal (pgs-x-abs-dirty ls m2) (pgs-x-abs-dirty ls pgs-mem)))))
  :hints (("Goal" :in-theory (union-theories '(pgs-x-cres pgs-x-cmem natp)
                                             (theory 'minimal-theory))
                  :use (pgs-x-commit-refines pgs-x-commit-result pgs-x-abs-dirty-of-commit
                        (:instance pgs-memp-of-commit)
                        (:instance pgs-x-dir-inv-m-length (b *pgs-x-dir-base*) (nd (pgs-ntables n)))))))

(in-theory (disable pgs-x-cres pgs-x-cmem))

(defthm pgs-x-c-al-is
  (implies (and (equal (pgs-x-tab n pgs-mem)
                       (pgs-sp (pgs-c-cur (pgs-x-abs-disk cs r pgs-mem) r mode) (car cs)))
                (natp n) (nat-listp lpages))
           (equal (pgs-c-al (pgs-x-abs-disk cs r pgs-mem) r mode (pgs-x-abs-dirty lpages pgs-mem) alloc)
                  (pgs-x-al)))
  :hints (("Goal" :in-theory (e/d (pgs-c-al) (pgs-x-abs-disk pgs-sp pgs-c-cur pgs-alloc pgs-touched
                                              pgs-grown-len pgs-dir-run-pages pgs-x-tab))
                  :use ((:instance pgs-len-of-tab-from (sel 2) (base 0) (i 0)))
                  :expand ((pgs-x-tab n pgs-mem)))))

(defthm pgs-x-take-singles-nat-listp
  (implies (and (nat-listp free) (natp hwm))
           (nat-listp (car (pgs-take-singles n free hwm))))
  :hints (("Goal" :induct (pgs-take-singles n free hwm) :in-theory (enable pgs-take-singles))))

(defthm pgs-x-remove-all-nat-listp
  (implies (nat-listp free) (nat-listp (pgs-remove-all xs free)))
  :hints (("Goal" :in-theory (enable pgs-remove-all))))

(defthm pgs-x-take-singles-first-natp
  (implies (and (nat-listp free) (natp hwm) (not (zp n)))
           (natp (car (car (pgs-take-singles n free hwm)))))
  :hints (("Goal" :expand ((pgs-take-singles n free hwm)))))

(defthm pgs-x-take-singles-true-listp
  (true-listp (car (pgs-take-singles n free hwm)))
  :hints (("Goal" :induct (pgs-take-singles n free hwm) :in-theory (enable pgs-take-singles)))
  :rule-classes :type-prescription)

(defthm pgs-x-alloc-parts
  ; A free list of naturals is all the square needs of the allocator state:
  ; the run starts at a natural and the singles are a true list.
  (implies (nat-listp (pgs-alloc-free alloc))
           (and (natp (first (pgs-alloc k m alloc)))
                (true-listp (second (pgs-alloc k m alloc)))))
  :hints (("Goal" :in-theory (disable pgs-alloc pgs-take-singles pgs-remove-all pgs-find-free-run pgs-run
                                      pgs-alloc-free pgs-alloc-hwm)
                  :use ((:instance pgs-alloc-unfold (n k))))))

(defthm pgs-x-commit-lpages-ok
  (implies (pgs-x-commit-hyps-basic)
           (pgs-lpages-ok lpages n 0))
  :hints (("Goal" :in-theory (e/d (pgs-x-commit)
                                  (pgs-x-commit-prepare pgs-x-commit-apply pgs-x-commit-prepare-plan
                                   pgs-lpages-ok pgs-alloc pgs-touched pgs-grown-len))
                  :use (pgs-x-commit-prepare-plan))))

(defmacro pgs-x-square-hyps ()
  '(and (equal (car (pgs-open (pgs-x-abs-disk cs r pgs-mem) r mode)) :ok)
        (equal slot (if (equal (second (pgs-open (pgs-x-abs-disk cs r pgs-mem) r mode)) 1) 0 512))
        (equal txid (pgs-next-txid (pgs-x-slots-of-words (pgs-x-words 1 0 1024 pgs-mem))))
        (equal (pgs-x-tab n pgs-mem)
               (pgs-sp (pgs-c-cur (pgs-x-abs-disk cs r pgs-mem) r mode) (car cs)))
        (equal (pgs-x-dir (pgs-ntables n) pgs-mem)
               (pgs-sd (pgs-c-cur (pgs-x-abs-disk cs r pgs-mem) r mode) (car cs)))
        (pgs-x-tab-inv n pgs-mem)
        (pgs-x-dir-inv *pgs-x-dir-base* (pgs-ntables n) pgs-mem)
        (pgs-memp pgs-mem) (natp n) (nat-listp lpages)
        (nat-listp (pgs-alloc-free alloc))
        (equal (car (mv-nth 0 (pgs-x-commit lpages n txid alloc slot pgs-mem fn-octets-pg))) :plan)
        (equal (mv-nth 0 (pgs-x-dirty-digests lpages pgs-mem fn-octets-pg))
               (pgs-dirty-digests (pgs-x-abs-dirty lpages pgs-mem)))
        (equal (nth 9 (pgs-x-res))
               (pgs-dirty-digests (pgs-table-dirty (pgs-touched lpages nil)
                                                   (pgs-chunk (pgs-x-tab (pgs-grown-len lpages n) (pgs-x-m2))))))
        (pgs-rec-valid (nth 1 (pgs-x-res)))
        (equal (pgs-rec-dir-digest (nth 1 (pgs-x-res)))
               (pgs-digest (pgs-x-dir (pgs-ntables (pgs-grown-len lpages n)) (pgs-x-m2))))))

(defthm pgs-x-plan-commit-shape
  ; The model's plan, in the parts the square equates.
  (implies (and (equal (car (pgs-open d r mode)) :ok)
                (pgs-lpages-ok (pgs-dirty-lpages dirty) (len (pgs-sp (pgs-c-cur d r mode) (pgs-pages d))) 0))
           (equal (pgs-plan-commit d r mode dirty alloc)
                  (let* ((cur (pgs-c-cur d r mode)) (p (pgs-pages d)) (al (pgs-c-al d r mode dirty alloc))
                         (fresh (take (len dirty) (second al))) (tfresh (nthcdr (len dirty) (second al)))
                         (rs (first al)) (txid (pgs-c-txid d r))
                         (tl (pgs-touched (pgs-dirty-lpages dirty) nil))
                         (t2 (pgs-plan-ptab (pgs-sp cur p) (pgs-dirty-lpages dirty) fresh
                                            (pgs-dirty-digests dirty) txid))
                         (tdirty (pgs-table-dirty tl (pgs-chunk t2)))
                         (dir2 (pgs-plan-ptab (true-list-fix (pgs-sd cur p)) tl tfresh
                                              (pgs-dirty-digests tdirty) txid)))
                    (list :plan
                          (append (pgs-page-writes dirty fresh) (pgs-page-writes tdirty tfresh)
                                  (list (cons rs dir2)))
                          (if (equal (pgs-c-k0 d r mode) 1) 0 1)
                          (pgs-make-rec txid rs (len t2) (pgs-digest dir2))
                          (list (third al) (fourth al))))))
  :hints (("Goal" :in-theory (union-theories '(pgs-c-writes pgs-c-rec pgs-c-fresh pgs-c-tfresh pgs-c-rs
                                               pgs-swr pgs-srec pgs-sd2 pgs-std pgs-sp2
                                               pgs-step-ptab2 pgs-step-tdirty pgs-step-dir2 pgs-step-writes
                                               pgs-step-tl pgs-c-lpages-ok)
                                             (theory 'minimal-theory))
                  :use ((:instance pgs-c-open-facts (disk d))
                        (:instance pgs-plan-commit-unfold (disk d))))))

(defthm pgs-x-rec-is-make-rec
  (implies (and (pgs-rec-valid rec) (equal (pgs-rec-dir-digest rec) dd)
                (equal rec (list :pgs-commit tx rs n2 x y)) (natp x))
           (equal (pgs-make-rec tx rs n2 dd) rec))
  :hints (("Goal" :in-theory (enable pgs-rec-valid pgs-rec-ok pgs-rec-body pgs-rec-dir-digest
                                     pgs-rec-shape-p pgs-make-rec)))
  :rule-classes nil)

(local
 (defthm pgs-x-rec-npages-of-list
   (equal (pgs-rec-npages (list :pgs-commit a b c d e)) (nfix c))
   :hints (("Goal" :in-theory (enable pgs-rec-npages)))))

(defthm pgs-x-len-of-tab
  (equal (len (pgs-x-tab n pgs-mem)) (nfix n)))

(defthm pgs-x-true-list-fix-of-dir
  (equal (true-list-fix (pgs-x-dir nd pgs-mem)) (pgs-x-dir nd pgs-mem)))

(defthm pgs-x-grown-len-natp
  (natp (pgs-grown-len ls n))
  :rule-classes :type-prescription)

(defthm pgs-x-rec-npages-when-list
  (implies (equal rec (list :pgs-commit a b c d e))
           (equal (pgs-rec-npages rec) (nfix c)))
  :rule-classes nil)

(defthm pgs-x-decode-dir-run-is-dir
  (implies (and (pgs-x-dir-inv *pgs-x-dir-base* nd pgs-mem) (pgs-memp pgs-mem))
           (equal (pgs-decode-table (pgs-x-words 1 *pgs-x-dir-base* (* 2048 (pgs-ptab-run-pages nd)) pgs-mem) nd)
                  (pgs-x-dir nd pgs-mem)))
  :hints (("Goal" :in-theory (disable pgs-x-decode-dir-run pgs-decode-table pgs-x-words pgs-ptab-run-pages)
                  :use ((:instance pgs-x-decode-dir-run (b *pgs-x-dir-base*))))))

(defthm pgs-x-dig4-natp
  (natp (pgs-x-dig4 sel a pgs-mem))
  :rule-classes :type-prescription)

(defthm pgs-x-commit-glue
  ; The model's plan parts (`pgs-x-plan-commit-shape') over the handle's
  ; table SP, directory SD, dirty pages DIRTY, allocation AL and txid TX,
  ; equal the plan the host writes.
  (implies (and (equal sp (pgs-x-tab n pgs-mem))
                (equal sd (pgs-x-dir (pgs-ntables n) pgs-mem))
                (equal dirty (pgs-x-abs-dirty lpages pgs-mem))
                (equal al (pgs-x-al))
                (equal tx txid)
                (pgs-x-commit-hyps-basic) (pgs-memp pgs-mem)
                (pgs-x-tab-inv n pgs-mem) (pgs-x-dir-inv *pgs-x-dir-base* (pgs-ntables n) pgs-mem)
                (natp (first al)) (true-listp (second al))
                (equal (mv-nth 0 (pgs-x-dirty-digests lpages pgs-mem fn-octets-pg)) (pgs-dirty-digests dirty))
                (equal (nth 9 (pgs-x-res))
                       (pgs-dirty-digests (pgs-table-dirty (pgs-touched lpages nil)
                                                           (pgs-chunk (pgs-x-tab (pgs-grown-len lpages n) (pgs-x-m2))))))
                (pgs-rec-valid (nth 1 (pgs-x-res)))
                (equal (pgs-rec-dir-digest (nth 1 (pgs-x-res)))
                       (pgs-digest (pgs-x-dir (pgs-ntables (pgs-grown-len lpages n)) (pgs-x-m2)))))
           (let* ((fresh (take (len dirty) (second al))) (tfresh (nthcdr (len dirty) (second al)))
                  (rs (first al))
                  (tl (pgs-touched (pgs-dirty-lpages dirty) nil))
                  (t2 (pgs-plan-ptab sp (pgs-dirty-lpages dirty) fresh (pgs-dirty-digests dirty) tx))
                  (tdirty (pgs-table-dirty tl (pgs-chunk t2)))
                  (dir2 (pgs-plan-ptab (true-list-fix sd) tl tfresh (pgs-dirty-digests tdirty) tx)))
             (and (equal (append (pgs-page-writes dirty fresh) (pgs-page-writes tdirty tfresh)
                                 (list (cons rs dir2)))
                         (pgs-x-abs-writes lpages (pgs-x-res) (pgs-x-m2)))
                  (equal (pgs-make-rec tx rs (len t2) (pgs-digest dir2)) (nth 1 (pgs-x-res)))
                  (equal (list (third al) (fourth al)) (nth 7 (pgs-x-res))))))
  :hints (("Goal" :in-theory (union-theories '(pgs-x-abs-writes pgs-x-rec-npages-of-list pgs-x-len-of-tab
                                               pgs-x-true-list-fix-of-dir pgs-x-grown-len-natp
                                               pgs-x-dirty-lpages-of-abs-dirty pgs-true-list-fix-when-true-listp
                                               pgs-x-nat-listp-of-touched pgs-x-nfix-when-natp natp pgs-x-dig4-natp
                                               (:compound-recognizer natp-compound-recognizer))
                                             (theory 'minimal-theory))
                  :use ((:instance pgs-x-commit-facts-named (ls lpages)) pgs-x-commit-lpages-ok
                        (:instance pgs-x-rec-npages-when-list (rec (nth 1 (pgs-x-res))) (a txid)
                                   (b (nfix (first al))) (c (pgs-grown-len lpages n))
                                   (d (pgs-x-dig4 1 (+ 8 slot) (pgs-x-m2)))
                                   (e (pgs-x-dig4 1 (+ 16 slot) (pgs-x-m2))))
                        (:instance pgs-touched-below (ls lpages) (lo 0) (prev nil))
                        (:instance pgs-x-abs-table-writes-is-model
                                   (tl (pgs-touched lpages nil)) (n2 (pgs-grown-len lpages n))
                                   (tfresh (nth 4 (pgs-x-res))) (pgs-mem (pgs-x-m2)))
                        (:instance pgs-x-decode-dir-run-is-dir
                                   (nd (pgs-ntables (pgs-grown-len lpages n))) (pgs-mem (pgs-x-m2)))
                        (:instance pgs-x-rec-is-make-rec (rec (nth 1 (pgs-x-res))) (tx txid)
                                   (rs (nfix (first al))) (n2 (pgs-grown-len lpages n))
                                   (dd (pgs-digest (pgs-x-dir (pgs-ntables (pgs-grown-len lpages n)) (pgs-x-m2))))
                                   (x (pgs-x-dig4 1 (+ 8 slot) (pgs-x-m2)))
                                   (y (pgs-x-dig4 1 (+ 16 slot) (pgs-x-m2))))))))

(defthm pgs-x-commit-refines-plan-named
  (implies (pgs-x-square-hyps)
           (equal (pgs-plan-commit (pgs-x-abs-disk cs r pgs-mem) r mode (pgs-x-abs-dirty lpages pgs-mem) alloc)
                  (list :plan (pgs-x-abs-writes lpages (pgs-x-res) (pgs-x-m2))
                        (if (equal slot 0) 0 1)
                        (nth 1 (pgs-x-res))
                        (nth 7 (pgs-x-res)))))
  :hints (("Goal" :in-theory (union-theories '(pgs-c-k0 pgs-c-txid pgs-x-abs-disk-parts
                                               pgs-x-dirty-lpages-of-abs-dirty pgs-x-len-of-tab
                                               pgs-next-txid-natp pgs-x-grown-len-natp pgs-x-nfix-when-natp
                                               (:compound-recognizer natp-compound-recognizer))
                                             (theory 'minimal-theory))
                  :use ((:instance pgs-x-plan-commit-shape (d (pgs-x-abs-disk cs r pgs-mem))
                                   (dirty (pgs-x-abs-dirty lpages pgs-mem)))
                        (:instance pgs-x-commit-glue
                                   (sp (pgs-sp (pgs-c-cur (pgs-x-abs-disk cs r pgs-mem) r mode) (car cs)))
                                   (sd (pgs-sd (pgs-c-cur (pgs-x-abs-disk cs r pgs-mem) r mode) (car cs)))
                                   (dirty (pgs-x-abs-dirty lpages pgs-mem))
                                   (al (pgs-c-al (pgs-x-abs-disk cs r pgs-mem) r mode
                                                 (pgs-x-abs-dirty lpages pgs-mem) alloc))
                                   (tx txid))
                        pgs-x-c-al-is pgs-x-commit-lpages-ok
                        (:instance pgs-x-dir-inv-m-length (b *pgs-x-dir-base*) (nd (pgs-ntables n)))
                        (:instance pgs-x-alloc-parts
                                   (k (+ (len lpages) (len (pgs-touched lpages nil))))
                                   (m (pgs-dir-run-pages (pgs-grown-len lpages n))))))))

(defthm pgs-x-tables-ready-second
  (implies (and (nat-listp tl) (pgs-x-tables-ready tl nt pgs-mem))
           (natp (nth 1 (pgs-x-tables-ready tl nt pgs-mem))))
  :hints (("Goal" :induct (pgs-x-tables-ready tl nt pgs-mem))))

(defthm pgs-x-commit-prepare-verdict-shape
  (implies (mv-nth 0 (pgs-x-commit-prepare lpages n txid alloc pgs-mem fn-octets-pg))
           (not (consp (nth 1 (mv-nth 0 (pgs-x-commit-prepare lpages n txid alloc pgs-mem fn-octets-pg))))))
  :hints (("Goal" :in-theory (disable pgs-alloc pgs-grown-len pgs-touched pgs-lpages-ok
                                      pgs-x-plan-fits pgs-ntables pgs-ntables-as-tq
                                      pgs-x-dirty-digests pgs-ptab-run-pages pgs-x-tables-ready
                                      pgs-x-lpages-resident pgs-dir-run-pages pgs-x-u64-bounded pgs-x-get-entry)
                  :use ((:instance pgs-x-tables-ready-second (tl (pgs-touched lpages nil)) (nt (pgs-ntables n)))))))

(defthm pgs-x-commit-plan-when-rec-valid
  ; The commit answered a plan when its record is valid: a refusal's or a
  ; :need-table's second element is a keyword or a number, never a record.
  (implies (pgs-rec-valid (nth 1 (mv-nth 0 (pgs-x-commit lpages n txid alloc slot pgs-mem fn-octets-pg))))
           (equal (car (mv-nth 0 (pgs-x-commit lpages n txid alloc slot pgs-mem fn-octets-pg))) :plan))
  :hints (("Goal" :in-theory (e/d (pgs-x-commit pgs-x-commit-apply pgs-rec-valid pgs-rec-ok pgs-rec-shape-p)
                                  (pgs-x-commit-prepare pgs-x-plan-entries pgs-x-mark-tables pgs-x-table-digests
                                   pgs-x-ensure-m pgs-x-words-digest pgs-x-write-rec))
                  :use (pgs-x-commit-prepare-verdict-shape))))

(defun pgs-x-commit-files (cs r keep lpages w res pgs-mem)
  ; The files after the host wrote what `pgs-x-commit' answered RES and
  ; left PGS-MEM: the page writes KEEP says reached the disk (nil: all),
  ; root R's page W as the handle read it before the commit (the binding
  ; the new one shadows, as the model's `pgs-set-root-slot' keeps it).
  (declare (xargs :stobjs pgs-mem :verify-guards nil))
  (cons (pgs-apply-pages (pgs-x-abs-writes lpages res pgs-mem) keep (car cs))
        (cons (cons r w) (cdr cs))))

(defthm pgs-x-commit-refines-plan
  ; THE PLAN SQUARE: over the handle the host opened on root R of the
  ; abstract disk, the plan `pgs-x-commit' answers (the writes the host
  ; performs, abstracted; the slot; the record; the allocator after) IS
  ; the model's `pgs-plan-commit'.
  (implies
   (and (equal (car (pgs-open (pgs-x-abs-disk cs r pgs-mem) r mode)) :ok)
        (equal slot (if (equal (second (pgs-open (pgs-x-abs-disk cs r pgs-mem) r mode)) 1) 0 512))
        (equal txid (pgs-next-txid (pgs-x-slots-of-words (pgs-x-words 1 0 1024 pgs-mem))))
        (equal (pgs-x-tab n pgs-mem)
               (pgs-sp (pgs-c-cur (pgs-x-abs-disk cs r pgs-mem) r mode) (car cs)))
        (equal (pgs-x-dir (pgs-ntables n) pgs-mem)
               (pgs-sd (pgs-c-cur (pgs-x-abs-disk cs r pgs-mem) r mode) (car cs)))
        (pgs-x-tab-inv n pgs-mem)
        (pgs-x-dir-inv *pgs-x-dir-base* (pgs-ntables n) pgs-mem)
        (pgs-memp pgs-mem) (natp n) (nat-listp lpages)
        (nat-listp (pgs-alloc-free alloc))
        (equal (mv-nth 0 (pgs-x-dirty-digests lpages pgs-mem fn-octets-pg))
               (pgs-dirty-digests (pgs-x-abs-dirty lpages pgs-mem)))
        (equal (nth 9 (mv-nth 0 (pgs-x-commit lpages n txid alloc slot pgs-mem fn-octets-pg)))
               (pgs-dirty-digests
                (pgs-table-dirty (pgs-touched lpages nil)
                                 (pgs-chunk (pgs-x-tab (pgs-grown-len lpages n)
                                                       (mv-nth 1 (pgs-x-commit lpages n txid alloc slot
                                                                               pgs-mem fn-octets-pg)))))))
        (pgs-rec-valid (nth 1 (mv-nth 0 (pgs-x-commit lpages n txid alloc slot pgs-mem fn-octets-pg))))
        (equal (pgs-rec-dir-digest (nth 1 (mv-nth 0 (pgs-x-commit lpages n txid alloc slot pgs-mem fn-octets-pg))))
               (pgs-digest (pgs-x-dir (pgs-ntables (pgs-grown-len lpages n))
                                      (mv-nth 1 (pgs-x-commit lpages n txid alloc slot pgs-mem fn-octets-pg))))))
   (equal (pgs-plan-commit (pgs-x-abs-disk cs r pgs-mem) r mode (pgs-x-abs-dirty lpages pgs-mem) alloc)
          (list :plan
                (pgs-x-abs-writes lpages (mv-nth 0 (pgs-x-commit lpages n txid alloc slot pgs-mem fn-octets-pg))
                                  (mv-nth 1 (pgs-x-commit lpages n txid alloc slot pgs-mem fn-octets-pg)))
                (if (equal slot 0) 0 1)
                (nth 1 (mv-nth 0 (pgs-x-commit lpages n txid alloc slot pgs-mem fn-octets-pg)))
                (nth 7 (mv-nth 0 (pgs-x-commit lpages n txid alloc slot pgs-mem fn-octets-pg))))))
  :hints (("Goal" :in-theory (union-theories '(pgs-x-cres pgs-x-cmem) (theory 'minimal-theory))
                  :use (pgs-x-commit-refines-plan-named pgs-x-commit-plan-when-rec-valid))))

(defthm pgs-x-true-listp-of-words
  (true-listp (pgs-x-words s a k pgs-mem))
  :rule-classes :type-prescription)

(defthm pgs-x-abs-disk-of-commit-files
  (equal (pgs-x-abs-disk (pgs-x-commit-files cs r keep lpages w res post) r post)
         (cons (pgs-apply-pages (pgs-x-abs-writes lpages res post) keep (car cs))
               (cons (cons r (pgs-x-slots-of-words (pgs-x-words 1 0 1024 post)))
                     (cons (cons r (pgs-x-slots-of-words (true-list-fix w)))
                           (pgs-x-abs-roots (cdr cs))))))
  :hints (("Goal" :in-theory (disable pgs-x-words pgs-x-slots-of-words pgs-x-abs-writes pgs-apply-pages))))

(defthm pgs-x-crash-glue
  (implies (and (equal (pgs-plan-commit d r mode dirty alloc) (list :plan w k rec a2))
                (equal d (cons p (cons (cons r s) rest))))
           (equal (pgs-crash d r (second (pgs-plan-commit d r mode dirty alloc)) keep
                             (third (pgs-plan-commit d r mode dirty alloc))
                             (fourth (pgs-plan-commit d r mode dirty alloc)))
                  (cons (pgs-apply-pages w keep p)
                        (cons (cons r (pgs-set-slot k rec s)) (cons (cons r s) rest)))))
  :hints (("Goal" :in-theory (e/d (pgs-crash pgs-set-root-slot) (pgs-plan-commit pgs-apply-pages pgs-set-slot))))
  :rule-classes nil)

(defthm pgs-x-commit-refines-crash
  ; THE WRITE SQUARE: the files after the host wrote what `pgs-x-commit'
  ; answered -- the page writes KEEP says landed, and the record in the
  ; slot the open did not use (the handle's slot words) -- abstract to the
  ; model's `pgs-crash' of `pgs-plan-commit''s writes, slot and record.
  (implies
   (and (equal (car (pgs-open (pgs-x-abs-disk cs r pgs-mem) r mode)) :ok)
        (equal slot (if (equal (second (pgs-open (pgs-x-abs-disk cs r pgs-mem) r mode)) 1) 0 512))
        (equal txid (pgs-next-txid (pgs-x-slots-of-words (pgs-x-words 1 0 1024 pgs-mem))))
        (equal (pgs-x-tab n pgs-mem)
               (pgs-sp (pgs-c-cur (pgs-x-abs-disk cs r pgs-mem) r mode) (car cs)))
        (equal (pgs-x-dir (pgs-ntables n) pgs-mem)
               (pgs-sd (pgs-c-cur (pgs-x-abs-disk cs r pgs-mem) r mode) (car cs)))
        (pgs-x-tab-inv n pgs-mem)
        (pgs-x-dir-inv *pgs-x-dir-base* (pgs-ntables n) pgs-mem)
        (pgs-memp pgs-mem) (natp n) (nat-listp lpages)
        (nat-listp (pgs-alloc-free alloc))
        (equal (mv-nth 0 (pgs-x-dirty-digests lpages pgs-mem fn-octets-pg))
               (pgs-dirty-digests (pgs-x-abs-dirty lpages pgs-mem)))
        (equal (nth 9 (mv-nth 0 (pgs-x-commit lpages n txid alloc slot pgs-mem fn-octets-pg)))
               (pgs-dirty-digests
                (pgs-table-dirty (pgs-touched lpages nil)
                                 (pgs-chunk (pgs-x-tab (pgs-grown-len lpages n)
                                                       (mv-nth 1 (pgs-x-commit lpages n txid alloc slot
                                                                               pgs-mem fn-octets-pg)))))))
        (pgs-rec-valid (nth 1 (mv-nth 0 (pgs-x-commit lpages n txid alloc slot pgs-mem fn-octets-pg))))
        (equal (pgs-rec-dir-digest (nth 1 (mv-nth 0 (pgs-x-commit lpages n txid alloc slot pgs-mem fn-octets-pg))))
               (pgs-digest (pgs-x-dir (pgs-ntables (pgs-grown-len lpages n))
                                      (mv-nth 1 (pgs-x-commit lpages n txid alloc slot pgs-mem fn-octets-pg))))))
   (equal (pgs-x-abs-disk (pgs-x-commit-files cs r keep lpages (pgs-x-words 1 0 1024 pgs-mem) (mv-nth 0 (pgs-x-commit lpages n txid alloc slot pgs-mem fn-octets-pg)) (mv-nth 1 (pgs-x-commit lpages n txid alloc slot pgs-mem fn-octets-pg)))
                          r (mv-nth 1 (pgs-x-commit lpages n txid alloc slot pgs-mem fn-octets-pg)))
          (pgs-crash (pgs-x-abs-disk cs r pgs-mem) r (second (pgs-plan-commit (pgs-x-abs-disk cs r pgs-mem) r mode (pgs-x-abs-dirty lpages pgs-mem) alloc)) keep (third (pgs-plan-commit (pgs-x-abs-disk cs r pgs-mem) r mode (pgs-x-abs-dirty lpages pgs-mem) alloc)) (fourth (pgs-plan-commit (pgs-x-abs-disk cs r pgs-mem) r mode (pgs-x-abs-dirty lpages pgs-mem) alloc)))))
  :hints (("Goal" :in-theory (union-theories '(pgs-x-abs-disk-of-commit-files pgs-x-abs-disk
                                               pgs-x-true-listp-of-words pgs-true-list-fix-when-true-listp
                                               pgs-next-txid-natp (:compound-recognizer natp-compound-recognizer))
                                             (theory 'minimal-theory))
                  :use ((:instance pgs-x-crash-glue (d (pgs-x-abs-disk cs r pgs-mem))
                                   (dirty (pgs-x-abs-dirty lpages pgs-mem))
                                   (w (pgs-x-abs-writes lpages (mv-nth 0 (pgs-x-commit lpages n txid alloc slot pgs-mem fn-octets-pg))
                                                        (mv-nth 1 (pgs-x-commit lpages n txid alloc slot pgs-mem fn-octets-pg))))
                                   (k (if (equal slot 0) 0 1))
                                   (rec (nth 1 (mv-nth 0 (pgs-x-commit lpages n txid alloc slot pgs-mem fn-octets-pg))))
                                   (a2 (nth 7 (mv-nth 0 (pgs-x-commit lpages n txid alloc slot pgs-mem fn-octets-pg))))
                                   (p (car cs)) (s (pgs-x-slots-of-words (pgs-x-words 1 0 1024 pgs-mem)))
                                   (rest (pgs-x-abs-roots (cdr cs))))
                        pgs-x-commit-refines-plan pgs-x-commit-plan-when-rec-valid
                        (:instance pgs-x-slots-of-commit)
                        (:instance pgs-x-dir-inv-m-length (b *pgs-x-dir-base*) (nd (pgs-ntables n)))))))

(defthm pgs-x-commit-refines-commit
  ; The complete commit: every write landed, then the record.
  (implies
   (and (equal (car (pgs-open (pgs-x-abs-disk cs r pgs-mem) r mode)) :ok)
        (equal slot (if (equal (second (pgs-open (pgs-x-abs-disk cs r pgs-mem) r mode)) 1) 0 512))
        (equal txid (pgs-next-txid (pgs-x-slots-of-words (pgs-x-words 1 0 1024 pgs-mem))))
        (equal (pgs-x-tab n pgs-mem)
               (pgs-sp (pgs-c-cur (pgs-x-abs-disk cs r pgs-mem) r mode) (car cs)))
        (equal (pgs-x-dir (pgs-ntables n) pgs-mem)
               (pgs-sd (pgs-c-cur (pgs-x-abs-disk cs r pgs-mem) r mode) (car cs)))
        (pgs-x-tab-inv n pgs-mem)
        (pgs-x-dir-inv *pgs-x-dir-base* (pgs-ntables n) pgs-mem)
        (pgs-memp pgs-mem) (natp n) (nat-listp lpages)
        (nat-listp (pgs-alloc-free alloc))
        (equal (mv-nth 0 (pgs-x-dirty-digests lpages pgs-mem fn-octets-pg))
               (pgs-dirty-digests (pgs-x-abs-dirty lpages pgs-mem)))
        (equal (nth 9 (mv-nth 0 (pgs-x-commit lpages n txid alloc slot pgs-mem fn-octets-pg)))
               (pgs-dirty-digests
                (pgs-table-dirty (pgs-touched lpages nil)
                                 (pgs-chunk (pgs-x-tab (pgs-grown-len lpages n)
                                                       (mv-nth 1 (pgs-x-commit lpages n txid alloc slot
                                                                               pgs-mem fn-octets-pg)))))))
        (pgs-rec-valid (nth 1 (mv-nth 0 (pgs-x-commit lpages n txid alloc slot pgs-mem fn-octets-pg))))
        (equal (pgs-rec-dir-digest (nth 1 (mv-nth 0 (pgs-x-commit lpages n txid alloc slot pgs-mem fn-octets-pg))))
               (pgs-digest (pgs-x-dir (pgs-ntables (pgs-grown-len lpages n))
                                      (mv-nth 1 (pgs-x-commit lpages n txid alloc slot pgs-mem fn-octets-pg))))))
   (equal (pgs-x-abs-disk (pgs-x-commit-files cs r nil lpages (pgs-x-words 1 0 1024 pgs-mem) (mv-nth 0 (pgs-x-commit lpages n txid alloc slot pgs-mem fn-octets-pg)) (mv-nth 1 (pgs-x-commit lpages n txid alloc slot pgs-mem fn-octets-pg)))
                          r (mv-nth 1 (pgs-x-commit lpages n txid alloc slot pgs-mem fn-octets-pg)))
          (pgs-commit (pgs-x-abs-disk cs r pgs-mem) r mode (pgs-x-abs-dirty lpages pgs-mem) alloc)))
  :hints (("Goal" :in-theory (union-theories '(pgs-commit car-cons cdr-cons) (theory 'minimal-theory))
                  :use (pgs-x-commit-refines-plan (:instance pgs-x-commit-refines-crash (keep nil))))))
