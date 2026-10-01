; fn: THE PAGE STORE'S GENERATION: the pages one root commit writes, and
; the two-generation reserve sized by K (lane recovery-refinement-2,
; 2026-10-01; PRF-1215; specs/recovery-refinement.md section 4; design
; 2026-10-01 stages 5 and 7).  Prefix fn-rrp-.
;
; On the page store (books/pagestore.lisp) a checkpoint is a root commit:
; the dirty pages are written copy-on-write to fresh addresses, the table
; pages they touch are rewritten, the directory run is written, and the
; root's other slot takes the record (pgs-plan-commit).  A GENERATION is
; what one commit writes; the owner publishes when the log's suffix reaches
; K/2 (fn-ock-publication-duep, PRF-083), so a generation is the dirty set
; of at most K records.  KeyKOS's format-time reserve (specs section 4) is
; two generations: the durable root's pages and the staged commit's.
;
; THE BOUND fn-rrp-commit-writes-within-the-generation: a planned commit
; writes at most 2 * |DIRTY| + 1 pages: one per dirty page, at most one
; table page per dirty page (pgs-touched emits each touched table once,
; ascending), and the directory run.  fn-rrp-two-generations-fit-the-reserve:
; two planned commits over dirty sets of at most K * D pages each (K
; records, D pages a record) write at most fn-rrp-reserve-pages K D in all.
; What binds |DIRTY| to K * D on the host (the due rule, and a per-record
; dirty-page bound from the profile) is PRF-1220's, with the medium
; instance: no host path opens the owner's state from a root yet (design
; stage 5), so the page store is not yet an instance of
; books/recovery-refinement.lisp's medium; its own crash keystone
; pgs-open-after-crash (PRF-344) is the "medium's own ordering" row of the
; spec, and the snapshot program's cuts (*pgs-snapshot-cuts*,
; pgs-cut-crash-point) map onto it in the spec's table.
;; Rules withdrawn at their source that this book's proofs use
;; (lane rule-hygiene, tools/rule_cost.py).
(in-package "ACL2")
(include-book "pagestore")

; -----------------------------------------------------------------------------
; 1. The counts of a commit's parts.

(defthm fn-rrp-page-writes-count
  (equal (len (pgs-page-writes dirty fresh)) (len dirty))
  :hints (("Goal" :induct (pgs-page-writes dirty fresh)
           :in-theory (enable pgs-page-writes))))

(defthm fn-rrp-dirty-lpages-count
  (equal (len (pgs-dirty-lpages dirty)) (len dirty))
  :hints (("Goal" :induct (pgs-dirty-lpages dirty)
           :in-theory (enable pgs-dirty-lpages))))

(defthm fn-rrp-table-dirty-count
  (equal (len (pgs-table-dirty tl cs)) (len tl))
  :hints (("Goal" :induct (pgs-table-dirty tl cs)
           :in-theory (enable pgs-table-dirty))))

; Each touched table page is emitted once, so at most one per dirty page.
(defthm fn-rrp-touched-count
  (<= (len (pgs-touched lpages prev)) (len lpages))
  :rule-classes :linear
  :hints (("Goal" :induct (pgs-touched lpages prev)
           :in-theory (e/d (pgs-touched) (floor)))))

(local
 (defthm fn-rrp-len-append
   (equal (len (append a b)) (+ (len a) (len b)))))

; -----------------------------------------------------------------------------
; 2. The generation and the bound.

; The pages one commit of DIRTY-COUNT dirty pages may write.
(defun fn-rrp-generation-pages (dirty-count)
  (declare (xargs :guard (natp dirty-count)))
  (+ 1 (* 2 dirty-count)))

; KEYSTONE: a planned commit writes at most the generation of its dirty set.
(defthm fn-rrp-commit-writes-within-the-generation
  (implies (equal (car (pgs-plan-commit disk r mode dirty alloc)) :plan)
           (<= (len (second (pgs-plan-commit disk r mode dirty alloc)))
               (fn-rrp-generation-pages (len dirty))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-rrp-touched-count (lpages (pgs-dirty-lpages dirty)) (prev nil)))
           :in-theory (e/d (pgs-plan-commit fn-rrp-generation-pages)
                           (pgs-open pgs-alloc pgs-plan-ptab pgs-touched pgs-table-dirty
                            pgs-page-writes pgs-chunk pgs-flatten pgs-contents pgs-lookup
                            pgs-dirty-lpages pgs-dirty-digests pgs-make-rec
                            pgs-grown-len pgs-dir-run-pages pgs-next-txid pgs-lpages-ok
                            pgs-root-slots pgs-slot pgs-pages pgs-rec-dir-addr
                            fn-rrp-touched-count take nthcdr)))))

; -----------------------------------------------------------------------------
; 3. The reserve: two generations of K records at D pages each.

(defun fn-rrp-reserve-pages (k d)
  (declare (xargs :guard (and (natp k) (natp d))))
  (* 2 (fn-rrp-generation-pages (* k d))))

; Two planned commits (the durable root's and the staged one's), each over
; the dirty pages of at most K records at D pages a record, write at most
; the reserve in all.
(defthm fn-rrp-two-generations-fit-the-reserve
  (implies (and (natp k) (natp d)
                (equal (car (pgs-plan-commit disk r mode dirty alloc)) :plan)
                (<= (len dirty) (* k d))
                (equal (car (pgs-plan-commit disk2 r2 mode2 dirty2 alloc2)) :plan)
                (<= (len dirty2) (* k d)))
           (<= (+ (len (second (pgs-plan-commit disk r mode dirty alloc)))
                  (len (second (pgs-plan-commit disk2 r2 mode2 dirty2 alloc2))))
               (fn-rrp-reserve-pages k d)))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-rrp-commit-writes-within-the-generation)
                 (:instance fn-rrp-commit-writes-within-the-generation
                            (disk disk2) (r r2) (mode mode2) (dirty dirty2) (alloc alloc2)))
           :in-theory (e/d (fn-rrp-generation-pages fn-rrp-reserve-pages)
                           (pgs-plan-commit)))))

(in-theory (disable fn-rrp-generation-pages fn-rrp-reserve-pages))
