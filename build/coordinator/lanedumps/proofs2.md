# proofs2 (Opus) lanedump, branch lane/proofs2 (+ lane/proofs2-s150)

Successor of lane/proofs (Fable, dde4ad9b0). Base: origin/next merged at e0a8516e9 (first merge
at b7624961f: dev d4e53323c's books/nntp-auth does not certify,
fn-auth-tls-reader-base-preserves-consistentp; next carried 87740d810). Own worktree
build/lanes/proofs2 (new, not a reused directory). Exited on the 10-04 ramp-down.

## LANDED on lane/proofs2@883c28b5a (READY), certified by narrow --recertify

| subject | book | events | certify run |
|---|---|---|---|
| PRF-1287 | books/served-available-read.lisp | fn-av-mca-read-span-keeps-funded, -within-the-credit-unfolds, -never-blocks-what-is-held, -covers-the-connection | certify-20261004T043850Z-1112347 (persvati) |
| may-seal | books/catalog-may-seal.lisp | fn-cat-may-seal-is-the-prepare-transition-gate, fn-cat-may-seal-admits-the-prepare-after-the-seal | same |
| KW-i ssr=srs | books/statement-recover-stream.lisp (+ tests: inhabitation and necessity witnesses) | fn-ssr-rows-are-the-raw-rows-without-snapshots, fn-ssr-recovery-rows-are-the-raw-rows-without-snapshots | same |
| PRF-1242 prereqs | books/page-read-direct.lisp | fn-pio-direct-admit-keeps-okp, fn-pio-direct-settle-keeps-okp, fn-pio-direct-admit-issues-exactly-its-row, fn-pio-direct-settle-removes-exactly-its-row | certify-20261004T043618Z-98000 (laptop) |
| PRF-1242 composed | books/host-model.lisp (+ host-model-machine comment) | fn-hmc-do-issue/-settle/-close-keeps-invp, fn-hmc-step-keeps-invp, fn-hmc-run-keeps-invp (any invariant state, every schedule), fn-hmc-init-run-keeps-invp | same |

- host/interfaces.lisp: fn-owner-cat-may-seal cites the two may-seal keystones (0a1e06ad2; announced).
- Ledger: PRF-1287-OWED filed (selective-chain refinement, chain guards, stale fn-mca-read-span-* citations at host/owner-host.lisp:4484-4486 and rows P1/P3/P8/M6/T17/PRF-1266/PRF-1269). HM02 noted (T1(b) PRF-1243/1244 open).
- Checks run: keystone_emit/interface_emit --check (no finding on the may-seal row); current_view --check (only "current.md stale": integrator regenerates); ledger --check stale (ledger.json/md/proofs.json: integrator regenerates). check-fast-lane's other reds are not this lane's: merge_registry (HST-003 += PRF-1251), reach 22 unbaselined (the plan's dev count), lock_discipline NEW host/native/admin.lisp:683 and its unit test.
- The persvati run installed 435 closure books without a cited manifest (green_check still owes them; certified by this lane's --certify-missing earlier, never cited): `--recertify-uncited` is the integrator's batch job.
- Findings: def-holder's exported rules are stated over `mv-nth 0`, which normalizes to `car`; they do not fire as stated. statement-recover-stream's local fn-ssr-resident-ignores-places loops the preprocessor; disable it in any proof that mentions nil places.

## S150 on lane/proofs2-s150@82abba272 (pushed, NOT yet READY)
- Deletes fn-owner-recover-rows, -from-checkpoint, -extended-arena, -extended (no host caller); P10 (current-view.json) re-pointed to fn-ock-install / bridge fn-ock-install-of-store-open-by-definition (P10 rested on uncalled code); PRF-1136 statement and five spec/doc mentions follow. init cleared it (owner.lisp's docstring names a book theorem about fn-ock-*, which stands).
- Owed before READY: check-lane on a box for the host change (host_check --load; an image build loads owner-host.lisp; no native behaviour changes: dead program-mode defuns). Then READY.
- Follow-up (announce to raw-dispatch and carrier2 first): host/owner-served-carried.lisp still lists fn-ock-recover-extended as a :produced producer of fn-owner-install-extended; with no caller it constrains nothing; dropping it removes fn-assume-capture-extensionp from the raw dispatch's assumptions.

## Continuation (the successor's, in order)
1. S150: check-lane at lane/proofs2-s150 merged onto next, then READY.
2. S151 (owner now proofs2): the substance is on next (books/native-retire.lisp fn-nret-observation-step, the decision host/native/operator.lisp:615 polls; keystones fn-nret-observation-expiry-is-uncertain, -report-requires-stopped). Owed: narrow `FN_CERT_ORIGIN_KIND=run certify_books.py --recertify books/native-retire books/native-retire tests/acl2/native-retire-tests` (laptop), cite, then set S151 landed with the run id.
3. PGO-* (22 items, owner now proofs2; announce owner-served-carried.lisp edits to raw-dispatch and carrier2 first): PGO-REFUSE-ABORT first (high, live: fn-owner-refuse-reservation / -known-abort / -finish evaluate fn-sn-statep per call; model keystones exist).
4. Cold-line's CL-* items stay cold-line's unless it hands one over after its slice is in next.

## Coordinates
| sha | world receipt | manifest id | image sha | native run id |
|---|---|---|---|---|
| lane/proofs2@883c28b5a | none (narrow recertify, per assembler rule 3) | certify-20261004T043850Z-1112347; certify-20261004T043618Z-98000 | none | none (no host behaviour change; interfaces citation only) |
| lane/proofs2-s150@82abba272 | none | none | none | owed (check-lane) |
