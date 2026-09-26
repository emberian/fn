# catalog-slice: the held record and the committed event catalog (2026-09-26)

Lane `lane/catalog-slice` (Fable), wave 5 lane 2 under D33, from dev
`91c59dabb`; brief `build/coordinator/queue/w5-catalog-slice.txt`; absorbs
the held `w3-rep-wave-d-4` brief (PKT-293/PKT-167 decided by D33: two views,
the shared transition; where the two briefs differ this one won: the w5 ids,
the checkpoint value left to checkpoint-pipeline, a context of verdict AND
delta). Ids taken: PRF-201 (proved), PRF-202, PRF-203, PRF-204 (planned,
statements registered), REP-013, STO-027, SCN-130 (implemented), SCN-131
(specified), PKT-585 (what remains), PKT-586 (decision). No NNT id was
assigned; the REQ line for the pinned view advancing at GROUP/LISTGROUP is
in PKT-585 for the deputy. No wire, delta or store-format code taken.

## The step reached

Steps 1 to 3 of the brief's order, certified: the interface (LANEDUMP), the
held record with its interns (books/catalog-record.lisp), the catalog
abstract stobj with its obligations and keystones (books/catalog.lisp),
and the teeth for both (tests/acl2/catalog-record-tests.lisp,
tests/acl2/catalog-tests.lisp). Steps 4 to 9 are NOT done (below).

**What the brief assumed that was not so at launch.** checkpoint-pipeline
had not merged (its branch is at dev HEAD, no `fn-sct-load`); the
proto-catalog books are on lane/consolidation-design only (read as the
pattern, not included); over-number-index and post-identity-index are
READY on their branches, unmerged (nothing reused; the catalog's tables
supersede them by design 4.1).

## What was proved (manifest `planning/evidence/manifests/certify-20260926T194426Z-1747941.json`, persvati `run-20260926T194345Z-3d11`, ACL2 8.7 w25, 2 jobs, 300 s: passed 4, failed 0, no book over 10 s)

**The held record** (`fn-held-p`, `fn-defrecord fn-held`, 15 positions):
the wire tuple's eleven positions read by the wire accessors
(`fn-held-accessors-are-the-wire-accessors`), the payload a natp handle;
facts `(octets body-start body-lines)`; context `(verdict delta
generation)`; numbers; withdrawn `nil | (at . by)`. The recognizer is
guard-verified (its field recognizers are the wire record's).

- `fn-cat-intern-list-materializes` (keystone): for `(fn-record-shapep w)`,
  `(fn-held-wire-of held fn-arena') = w` where `(mv held fn-arena')` is
  `(fn-cat-intern-list w keyring generation fn-arena)`: alpha of intern is
  the identity on the wire (through `fn-arena-seal-new-handle`).
- `fn-cat-intern-is-intern-list`: the buffer intern equals the list intern
  of the wire record whose payload is the buffer's list; hypothesis-free
  (the `fn-arena-p` hypothesis proved redundant by proving the weakened
  theorem first).
- `fn-hf-split-index-is-split-article`, `fn-hf-crlf-count-is-crlf-lines`,
  `fn-hf-body-lines-of-is-nov-body-line-count-by-definition`: the byte
  facts are the served machine's split and line count (books/nntp-session);
  the column that removes OVER's per-row walk (`fn-nov-body-line-count`).
- `fn-held-p-of-intern-list`, `fn-intern-list-handle`, `fn-intern-list-arena`.

**The catalog** (`fn-cat`, `defabsstobj ... :attachable t`; foundation
`fn-cat$c`: rows array, count, three `(hash-table equal)` fields, octets).
Logical value: `fn-held-listp`. Exports and their `:logic` bodies are in
the book's header. `fn-cat$corr`'s conjuncts: recognizer; held list; count
= length; count within the array; rows below the count are the list
(`fn-cat-rows-corr`); Message-ID table: bound keys look up to
`fn-cat-seqs-for`, every row's Message-ID bound; numbers table: a bound
`(group . n)` NAMES a row and looks up to `fn-cat-number-seq`, every row's
pairs bound (the strengthening is what keeps a fresh number from colliding
with a stale key); groups table: bound groups map to `(rows . 1+high)`,
every row's groups bound; octets = `fn-cat-octets-of`. Obligations proved
exactly as `defabsstobj-missing-events` prints them: `create-fn-cat{...}`,
and `{correspondence}`/`{guard-thm}`/`{preserved}` for count, at,
msgid-seqs, group-number, group-next, group-count, total-octets,
visible-at, commit, withdraw, redecide, clear. The commit's exec reads its
plan (next number and old count per group) before any write, so a group
listed twice gets one number and one count, as the logical assignment
reads C once; the numbers table is append-only (`fn-ctg-number-seq-above-high`).

Keystones over the opened view: `fn-cat-commit-keeps-rows`,
`fn-cat-commit-new-row`, `fn-cat-commit-count`,
`fn-cat-commit-binds-fresh-numbers` (under `fn-cat-p`: no falsifying
witness was found and the weakened theorem did not close in budget, so
the hypothesis stays and is NOT counted as teeth), `fn-cat-visible-at-withdrawn`
(a row withdrawn at version W is visible to version V iff V <= W: the
cancel-after-target case in its list form).

**Teeth.** catalog-record-tests: guard-class assertions, ground witnesses
with complete antecedent and conclusion for the split, the line count, the
by-definition equation and materialization, a must-fail per falsifiable
hypothesis (octet-list, shape, record-p, generation), the exec path on a
live arena and buffer. catalog-tests: the exec path on a live `fn-cat`
(SCN-130: three commits, lookups, a withdrawal, the pinned view at versions
3 and 4, a redecision, a clear), ground witnesses and must-fails for the
membership hypothesis, the withdrawal hypothesis and the row bound.

## The assurance chain, as far as it reaches

native entry: NONE YET (the host still calls the owner's view) ->
executed ACL2 subject: `fn-cat-commit`, `fn-cat-withdraw`, `fn-cat-redecide`,
`fn-cat-intern`, `fn-cat-intern-list` (guard-verified, compiled) ->
refinement: `fn-cat$corr` and `fn-arena$corr`, proved once per export;
`fn-held-wire-of` as alpha (PRF-201) -> maintained relation:
`fn-cat-owner-relation` NOT defined (step 6) -> behavioural theorems:
PRF-202/203/204 planned -> observed result: none measured.

## Which entry establishes R and which transitions preserve it

Not reached. What exists: the creator establishes `fn-cat$corr`
(`create-fn-cat{correspondence}`); commit, withdraw, redecide, clear
preserve it (their `{correspondence}`). The relation R with the owner
(design 1.5) and its four entries are PKT-585.

## Not done, and why (PKT-585: the restart record is the LANEDUMP)

Budget: the lane's ~250 tool calls went to steps 1 to 3 (the obligation
proofs of an eleven-export abstract stobj with three hash-table fields
took the bulk: the table lookups after a put-fold, the first-wins alist
model, the field-level discipline that keeps the stobj from opening into
list structure). Remaining, in the brief's order: (4) books/catalog-commit
(PreparedCommit, prepare/complete/abandon, `fn-sn-finish-held`, the
phase-gate context theorem: chosen form stated in the LANEDUMP), (5)
books/catalog-delta (`fn-delta-p`, `fn-view-apply`, `-step`, PRF-202), (6)
books/catalog-relation (R, entries 1 to 4; `fn-cat-load-row` is
`fn-cat-commit`), (7) the served reads (PRF-204), (8) the host, (9) the
measurement; SCN-131's native module; the composite's carried Message-ID
binding at intern (the row binds its own Message-ID field today; a kind-4
composite's carried article is PKT-585); the index-scanning exec of the
split and line count over the buffer (the facts are computed over the
buffer's logical list, the transient the prepare builds today; no list is
retained). Measurements: none (nothing served changed). Deletion map
(design 4.1 to 4.4): nothing deleted yet; every item stays until the
served path moves (named in the LANEDUMP).

## PKT-586 (decision, for ember)

The numbers table's invariant is "a bound number names a row" (append-only
numbers; a cancel never frees a number). That matches `fn-allocate-memberships`
today but forecloses reclaiming numbers on `declare-group` resets. Default:
keep (RFC 3977 3.1.1: numbers are never reused). Rejected: a per-group
reset (a data-dependent renumbering the pinned view cannot express).
