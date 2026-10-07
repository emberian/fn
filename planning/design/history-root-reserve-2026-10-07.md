# History-root reserve (lane N-MEM10; MEM-010, MEM-011; CONVERGE-2 rows 15, 16)

Design note, 2026-10-07. Phase 1: statements only; no code until Deputy N's GO.

The live history roots are funded out of the article pool. `fn-mca-initial` (books/owner-credits.lisp:322) builds the ledger
so that `budget - base - completion - runtime = fn-heap-articles-octets profile`; `fn-owner-hroot-resize`
(host/history-root-host.lisp:25) is `fn-mcr-resize` on `(:history-root . g)` and so draws that free room;
books/heap-store-figure.lisp has no history-root term. Measured at the refusal (hbox:/tank/fn/scratch/n-mem10/r2.log,
capacity_free, 1,100 POSTs): budget 5,624,942,530, total 5,624,434,186, the retained generation 1 holds 2,239,432, the
candidate generation 2 holds 693,888 and asks 1,792,688; the free room is the profile's 3,441,664 article octets, and
retained + candidate (about 4.3 MB at the ask) exceed it, so `fnn-owner-history-root-fund` refuses MEMORY-BUDGET-EXHAUSTED
(MEM-010). The same draw leaves article-slot admission less than one article (MEM-011's 440 "in flight fill the memory").
Two generations coexist across every publication, so the fix is a funded reserve for exactly that, outside the pool.

## 1. The figure term: two generations at the profile's bound

What a root holds (books/history-root-credit.lisp `fn-hroot-memory-octets`, books/history-records.lisp `fn-hrecs$c`,
books/history-pages-resident.lisp `fn-hp-resident-row-boundsp`): the image's pages
`fn-hroot-page-octets np = 8(2048 np + 2 np + ntables np) + 512`, a suffix array (8 octets a slot), 4096 fixed. The image
layout is four word columns of one word per row (each starts at a page, `2048*start + seq < 2048 np`) and one octet column
(`16384*start4 + len4 <= 16384 np`). So, for N rows and O event octets:

    np(N,O) <= 4*ceil(N/2048) + ceil(O/16384) + 1          ; +1: the grow placement's slack page, see fn-hpr-final-placement
    ntables np <= 1 + tq(np-1) <= 1 + floor((np-1)/341)    ; pgs-ntables-bounds

The profile's bounds: N <= `max-transactions` T (the figure's state term already charges T handles and rows) and
O <= `max-history-octets` H (the history budget commits at most H charged octets, each >= the payload octet). Proposed
`(defun fn-heap-hroot-bound (profile) ...)` =

    page-octets(npmax) + 8*T (suffix) + 4096          ; the memory term at the bound
    + 64*T                                            ; fn-hroot-retain-demand's per-row term
    + 96*(8 + tree-bound(max-record-octets))          ; fn-hroot-event-demand's one-event term
    + page-octets(1)

where `tree-bound` is a new bound of `fn-hroot-tree-octets` of any event whose encoding is within `max-record-octets`
(OWED lemma; today only the value-by-value function exists). The reserve is `2 * fn-heap-hroot-bound` (retained + candidate;
a third generation cannot exist because `fn-owner-hroot-begin` is one candidate at a time and retire precedes the next begin
-- to be stated, see K3). Honest size: a generation at the bound is about H + 40 T octets, so the term is about 2H: for a
big preset it is large and may overlap the arena's 2H (`fn-heap-store-history-octets`) if the root IS the resident history;
that overlap is a separate parsimony question I do NOT resolve here (decision for N: add the term now at its honest size
and measure; shrinking the arena term is its own lane). For the CONVERGE-2 small preset the term is megabytes, not the
pool. The launcher sizes the heap from `fn-heap-store-figure-octets`/`fn-heap-store-live-figure-octets`; the term enters
`fn-heap-store-base-octets` (and the reclaim base), so `fn-mca-figure-octets` grows by it, and the keystones there that pin
the figure's shape re-prove (adding a summand).

Also in the reserve's charge: the host's pin-time key `(:history-root-tail g)` (host/history-root-host.lisp:202,
`16*bytes`) and `fn-hroot-tail-demand` (2 memory + ...) also draw the free room today. The tail credit is a THIRD root-class
draw; this note moves it into the reserve too (the bound above then needs `2*memory` for the tail beside the generation's
own, i.e. a per-generation 3x memory in the worst case, to be fixed when the code is read in phase 2; stated as OWED, not
assumed).

## 2. The ledger change

`fn-mcr` gains one funded field, `hroot` (reserve octets), next to `completion`; `fn-mcr-total` counts it whole (funded whole
whether or not drawn, like completion). Root credits are NOT ops-credits: a separate alist field `hroots` (generation-class
key -> credit) is drawn from the reserve:

    (fn-mcr-hroot-resize l id n)   ; l -> (:ok l') | (:refused :history-root-reserve-exhausted)
    ; admitted iff sum(hroots with id's entry replaced by n) <= hroot; touches ONLY hroots; budget, base, cache, ops,
    ; completion, runtime, drawn, total all unchanged (the reserve is already in total).

`fn-mca-initial` takes `hroot = (fn-heap-hroot-reserve-octets profile)` into the budget and the base solve, so
`budget - total = fn-heap-articles-octets` stays true and `fn-mca-initial-funds-exactly-the-articles` still holds (plus a
conjunct for the reserve). `fn-owner-hroot-resize` / `-release-credit` / the tail funding call `fn-mcr-hroot-resize`; release
is resize to 0 (drops the entry; never refused). The twin `fn-mcr-resize` use for roots is deleted, not kept. fn-mcr-make
(12+13 uses, all in books/memory-credits.lisp and books/owner-credits.lisp; no host callers) is extended in place by two
args; `fn-mca-default` passes 0 and 0 (it admits one article at RESERVE and no roots, so a root before the run's budget is
installed refuses by name, which is the right default).

## 3. Keystone statements (ACL2 text) and their notes

K1 (roots never draw the pool; in books/memory-credits.lisp):

    (defthm fn-mcr-hroot-resize-leaves-the-pool-and-the-total
      (implies (equal (car (fn-mcr-hroot-resize l id n)) :ok)
               (let ((l2 (cadr (fn-mcr-hroot-resize l id n))))
                 (and (equal (fn-mcr-total l2) (fn-mcr-total l))
                      (equal (- (fn-mcr-budget l2) (fn-mcr-total l2)) (- (fn-mcr-budget l) (fn-mcr-total l)))
                      (equal (fn-mcr-ops l2) (fn-mcr-ops l)) (equal (fn-mcr-cache l2) (fn-mcr-cache l))
                      (equal (fn-mcr-completion l2) (fn-mcr-completion l)))))
      :hints ...)
    (defthm fn-mcr-hroot-resize-refuses-exactly-past-the-reserve
      (equal (car (fn-mcr-hroot-resize l id n)) ; :refused iff growth and sum' > hroot, by name
             (if (and (< (fn-mcr-hroot-credit-of id l) (nfix n)) (< (fn-mcr-hroot l) (fn-mcr-hroot-sum-with l id n)))
                 :refused :ok)))
    (defthm fn-mcr-hroot-resize-keeps-funded (implies (fn-mcr-fundedp l) (fn-mcr-fundedp (cadr (fn-mcr-hroot-resize l id n)))))

  Satisfiable: `(fn-mca-initial small-profile core nursery live)` admits a resize of 1 to the reserve. Teeth: n = reserve+1
  refuses by name; and the pool witness: a refused AND an admitted resize leave `fn-mcr-resize` of a connection's article
  credit admitted at the same figure (the K3 witness). Premise inhabitation: `fundedp` of the initial ledger is already a
  theorem; add the instance that `hroot` is positive for the small preset.

K2 (the figure: retained + candidate fit; books/heap-store-figure.lisp or a new books/history-root-figure.lisp):

    (defthm fn-heap-hroot-two-generations-fit-the-reserve
      (implies (and (<= nrows (fn-bs-profile-max-transactions profile)) (<= octets (fn-bs-profile-max-history-octets profile))
                    (fn-hroot-shape-within-p g1 nrows octets) (fn-hroot-shape-within-p g2 nrows octets))
               (<= (+ (fn-hroot-demand-at g1) (fn-hroot-demand-at g2)) (fn-heap-hroot-reserve-octets profile))))

  where `fn-hroot-demand-at` is the max of `fn-hroot-event-demand` / `fn-hroot-grow-demand` / `fn-hroot-retain-demand` /
  `fn-hroot-tail-demand` over the shape (a pure function of np, rows, suffix length, event octets; the stobj reads are
  replaced by the shape's numbers by lemmas about `fn-hroot-memory-octets` = page-octets np + 8 sfx + 4096). The statement
  is about the demand FUNCTIONS the host calls (definterface keystones name them or `:via`). Teeth: np one past the bound
  (N = T + 2049) exceeds the reserve -- the bound is tight in np by the arithmetic. Premise inhabitation: a profile and a
  shape instance (the small preset, N = 1100, O = its history) satisfy the premises; the premise `fn-hroot-shape-within-p`
  ("the root's row/octet counts are the store's") is the NEW assumption: it is discharged by the store budget
  (`fn-sbud-admitp` caps rows and octets), owed as a lemma from books/store-budget.lisp, never assumed silently. If that
  discharge fails for the suffix (suffix length <= N is not obviously kept), N is told and the term widens.

K3 (articles whatever roots hold; in books/owner-credits.lisp):

    (defthm fn-mca-article-slots-ignore-the-history-roots
      (implies (fn-mcr-fundedp l)
               (equal (fn-mcr-free (fn-mcr-hroot-resize* l keys-and-amounts))   ; any run of admitted/refused root resizes
                      (fn-mcr-free l))))
    (defthm fn-mca-initial-admits-the-profiles-articles-beside-full-roots
      (let ((l (fn-mca-hroots-full (fn-mca-initial profile core nursery live)))) ; the reserve drawn to its limit
        (<= (* (fn-heap-article-slots profile) (fn-heap-article-reserve-octets profile))
            (- (fn-mcr-budget l) (fn-mcr-total l)))))

  `fn-mcr-free` is `budget - total` (already the admission's room: `fn-owner-article-slots` reads it). Teeth: against the
  CURRENT ledger (roots as ops) the second statement is false at the CONVERGE-2 figures (3,441,664 free minus 4.3 MB of roots);
  that failure is the red-before and is encoded as an `:rule-classes nil` counter-instance on the old shape before it is
  deleted. Premise inhabitation: same as K1.

K4 (end to end, books/owner-credits.lisp): `fn-mca-initial`'s existing `fn-mca-initial-funds-exactly-the-articles` extended
with `(equal (fn-mcr-hroot l) (fn-heap-hroot-reserve-octets profile))` and `(equal (fn-mcr-hroots l) nil)`.

## Owed items this raises (not assumed)
1. `tree-bound` of an event from `max-record-octets` (K2's one-event term).
2. Store budget => root shape (rows <= T, event octets <= H, suffix <= T).
3. One candidate at a time + retire before the next begin (so two generations is the maximum); the lease/`retire-word`
   machinery in planning/design/reclaim-2026-10-04.md L1 may keep a retired generation alive longer than a swap --
   if so the count is 2 + live leases and the bound is stated per lease.
4. The tail credit's place in the bound (section 1).
5. Whether the arena's 2H term and the root's term overlap (parsimony; separate lane).

## Phase 2 plan
books/memory-credits.lisp (field, resize, K1) -> books/owner-credits.lisp (initial, K3, K4) -> books/history-root-credit.lisp
(shape demand lemmas, K2) -> books/heap-store-figure.lisp (term, re-proved keystones) -> host/history-root-host.lisp (calls
only) -> farm certify --affected-by, host_check --load, interface_emit, world.py --check. Native red-before/green-after
(N's): capacity_free and kill_mid_catch_up, exact command in READY.
