# Lane tariff — lanedump (Fable; wound down 2026-10-04 on ember's call, an Opus seat continues)

Worktree `build/lanes/tariff`, branch `lane/tariff` from `origin/integrate/20261004 @ec2c1b3da`
(the assembler's base). Brief: the tariff design packet first, then the ARTICLE slice.

## Coordinate table

| sha | world receipt | manifest | image | native run |
|---|---|---|---|---|
| (this commit) | REPL admission only: `books/output-tariff-article.lisp` 10 forms, 0 refused, 2,770 prover steps on the laptop over `books/output-command-admission` (6 deps source-loaded); `books/nntp-responses` loaded (413 forms) and stopped unused | none | none | none |

Nothing certified; nothing on an image. READY #1 (the packet) is this commit; READY #2 (the slice) is NOT reached.

## What is decided (planning/design/tariff-2026-10-04.md, DECISION block)

1. The tariff is produced from the row by ACL2 (extent length via the factory's own lookup
   composed with the representation's cost model), never declared; the gate consumes it as today.
   ARTICLE first; the ratchet is the count of `:unpriced` rows in `*fn-ocap-command-families*`.
2. One ledger in one stobj (Q1) is the DIRECTION with preconditions (exec refund/grow/destroy; the
   tree layout as a `def-representation` instance; re-proved correspondences; one-lock analysis).
3. `definterface :operation` becomes the generator (Q2); supplied tariffs with lane-proved bounds
   are the norm, the census their logical dimension; `:accounted` refused until the ledger ops
   have cost rows and `NAME$tariff-bound` exists.
4. Credits/heap figure (Q4): theorems 1 (with hypothesis H) and 3 next; retirement in ONE commit
   carrying the simulation theorem 2 — never against a proof-owed item.
5. Funded (Q5) = `:hold`; the lease ordering is the host's (owner.lisp:6293 before :6299) until the
   issue token enters `fn-ocap-admit-preview`; unpriced families refuse by name, always.
6. Migration (Q6): def-cost rows for every :logic entry in this area; generator emits the rest;
   the counter change is its own commit, baseline pinned.
Advisory review: kimi and grok, pasted verbatim with the lane's fact-check; six amendments
accepted; grok's dissent on the generator recorded with the engineering reason.

## Open (ESCALATED to ember in the packet)
(a) deleting the absent-policy pass-through (owner.lisp:1932) — a node without `[resources]` gets a
default pool and refuses an over-quantum ARTICLE with the busy line until ST2;
(b) the wire line for an unpriced family in accounted mode (lane proposes 403, connection kept).

## The first slice's state (ARTICLE)
DONE (admitted, uncertified): `books/output-tariff-article.lisp` — `fn-tariff-article-octets`
(= 2·16·(initial + 2·ELEN + 3) + ELEN), `fn-tariff-article-descriptor`, keystones
`fn-tariff-article-admits-exactly-within-capacity` (both directions over `fn-ocap-admit-preview`),
`fn-tariff-article-unrepresentable-is-refused`, `-descriptor-is-a-tariff`. No test book yet, no
Makefile root yet (add `books/output-tariff-article` + `tests/acl2/output-tariff-article-tests`
beside the admission roots at Makefile:1979).
NOT DONE, in order (the exact continuation):
1. `tests/acl2/output-tariff-article-tests.lisp`: `defkeystone` teeth for the three keystones
   (witness elen 1000 / preview `(:preview 9 :article ((65 82 84 73 67 76 69) (49)))` / capacity
   1048576; removals per hypothesis; corrupted elen labelled).
2. `books/output-tariff-article-row.lisp` (closure includes `nntp`; needs persvati, or hbox under
   load 16 after compose's nntp-auth fix, or the laptop-warm cache): `fn-tariff-article-elen session
   args v fn-arena fn-cat` mirroring the ARTICLE row's form tests (protocol-served-table.lisp:410:
   number form → `fn-cnx-view-seq` → `fn-cat-at` → `fn-record-payload` → `fn-arena-payload-len`
   guarded by `< h (fn-arena-count)`; msgid form via `fn-scat-msgid-article`; current form; else 0),
   `fn-tariff-article-preview preview session v fn-arena fn-cat`; KEYSTONE
   `fn-tariff-article-prices-the-served-row`: for the number form the ELEN equals
   `(len (fn-nntp-article-bytes (fn-scat-number-article group n v fn-arena fn-cat) fn-arena))`
   (0 when nil); likewise msgid form.
3. The bound obligation over the arm that runs: `(def-cost fn-nntp-article-response-of-bytes
   :conses (+ K (* 2 (+ INITIAL (* 2 n) 3))) :sizes ((n (len bytes))) ...)` in a cost book over
   nntp-responses (closure 35 books, loads on the laptop with --source-deps in ~6 s); if the
   derivation leaves unaccounted leaves, state `fn-tariff-article-reply-within-tariff` and file it
   `proof-owed` by name (planning/repair/repair.py).
4. `host/owner-host.lisp:5512-5518 fn-owner-output-tariff-preview`: signature `(id preview fn-arena
   fn-cat state)`; body: find the conn (`fn-own-find-conn id (fn-own-conns (fn-owner-core state))`),
   its session (`fn-own-conn-session`), its pinned version v (as fn-owner-chunk-span-at resolves it),
   and answer `(fn-tariff-article-preview preview session v fn-arena fn-cat)` when
   `(fn-ocap-at 2 preview)` is `:article`, else `(fn-ocap-unpriced-tariff preview)`. The host call at
   owner.lisp:1933 keeps its shape (fnn-core-state appends trailing stobjs by declared kind) — verify
   with `python3 tools/harness_check.py` and `tools/interface_emit.py --check`. ONLY this region of
   owner-host.lisp is this lane's (announced to the assembler; retire/reclaim own :1831 and the orc-*).
5. `host/interfaces.lisp`: declare `fn-tariff-article-octets`, `-descriptor`, `-elen`, `-preview`
   (:common-lisp-compliant); `host/cost-host.lisp`: def-cost rows (`:visits` constant where it is:
   `fn-ocap-at`, `fn-ocap-admit-preview`, `fn-rlo-capacity`, the tariff arithmetic); then
   `tools/cost_obligations.py --write` is the INTEGRATOR's — quote the none count it prints.
6. `tests/owner_output_preview_fixture.lisp`: add a catalog holding one article (fn-cat/fn-arena
   stobjs, `fn-cat-commit` one row, group selected in the session) and assert
   `(:tariff :article N)` with N = `(fn-tariff-article-octets elen)`; NEWNEWS still `(:unpriced
   :newnews)`. `tests/native_output_preflight_raw.lisp`: ARTICLE arm (red at base: unpriced refused
   before any factory; green: `:hold`, factory reached, NEWNEWS still refused). Image native
   `tests/test_native_output_tariff.py`: `[resources] output_heap_octets/quantum` set, POST, `ARTICLE
   1` → 220 vs the accounted refusal at base; over-quantum article → busy line.
7. Certify: `tools/farm.py submit auto --affected-by books/output-tariff-article` (and the row book);
   `tools/remote_check.sh auto --target check-lane`; READY #2 with the coordinate table.

## REPL/box log
Laptop: `tariff` over output-command-admission (started, 10 forms admitted, stopped); `tariff-resp`
over nntp-responses (started with --source-deps, loaded 413 forms in 5.7 s ACL2 time, stopped
unused). persvati: asked, refused (2/2 full), first in queue. hbox: GO given at load 18.5 then
withdrawn at 18.9; never started.

## The apps lane's ask (FNCR connection class)
Answered directly (two messages): interim = the HST-046 projection pattern on a private ledger,
vector (RESIDENT 0 1 1 0 0 0 1 0) per session (resident, descriptors 1, workers 1, conn-ids 1),
draw at accept, settle at PHYSICAL close only, `:operation (:stage :projection ...)` +
`def-operation-check` as fn-ros-issue. The charge row proper = the generator with `:principal
:connection` (packet Q2 amendment (i)); ETA: after the ARTICLE slice lands — apps files a
tariff-owed item naming Q2(i).

## Counts for the exit line
cost-obligations: none 1,442 → 1,442 (no def-cost row landed; step 5 above moves the admission's
and the tariff's entries). proof-owed: 0 filed (step 3 may file one). Families priced: 0 → 0 on the
served path (the ARTICLE producer is written but not wired: steps 2 and 4).
