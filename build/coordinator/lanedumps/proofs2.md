# proofs2 (Opus) lanedump, branch lane/proofs2

Successor of lane/proofs (Fable, dde4ad9b0). Base: origin/next b7624961f merged in (dev
d4e53323c's books/nntp-auth does not certify: fn-auth-tls-reader-base-preserves-consistentp;
next carries 87740d810). Worktree build/lanes/proofs2 (own, new; not a reused directory).

## State (REPL-admitted; certification queued: assembler hbox queue #5, 27 roots, --jobs 8, sha 0a1e06ad2)

| subject | book | events | REPL |
|---|---|---|---|
| PRF-1287 | books/served-available-read.lisp | fn-av-mca-read-span-keeps-funded, -within-the-credit-unfolds, -never-blocks-what-is-held, -covers-the-connection | persvati 33/33 |
| may-seal | books/catalog-may-seal.lisp | fn-cat-may-seal-is-the-prepare-transition-gate, fn-cat-may-seal-admits-the-prepare-after-the-seal | persvati 7/7; (t nil) on (nil nil)/(nil (x)) |
| KW-i ssr=srs | books/statement-recover-stream.lisp | fn-ssr-rows-are-the-raw-rows-without-snapshots, fn-ssr-recovery-rows-are-the-raw-rows-without-snapshots | persvati 24/24; test book: inhabitation (two articles from sequence 0) and necessity (enroll/rotate are fn-stxk-p; rows differ) |
| PRF-1242 prereqs | books/page-read-direct.lisp | fn-pio-direct-admit-keeps-okp, fn-pio-direct-settle-keeps-okp, fn-pio-direct-admit-issues-exactly-its-row, fn-pio-direct-settle-removes-exactly-its-row | laptop 94/94 |
| PRF-1242 | books/host-model.lisp | fn-hmc-do-issue/-settle/-close-keeps-invp, fn-hmc-step-keeps-invp, fn-hmc-run-keeps-invp (any invariant state, every schedule), fn-hmc-init-run-keeps-invp | laptop 231/231, 14.26M steps |

- host/interfaces.lisp ~1549: fn-owner-cat-may-seal cites the two may-seal keystones (0a1e06ad2; announced to the assembler; keystone_emit/interface_emit --check: no finding on the row).
- Ledger: PRF-1287-OWED filed (proof-owed: selective-chain refinement, chain guards, stale fn-mca-read-span-* citations at host/owner-host.lisp:4484-4486 and rows P1/P3/P8/M6/T17/PRF-1266/PRF-1269). HM02 noted (T1(b) PRF-1243/1244 open).
- Findings: def-holder's exported rules are stated over `mv-nth 0`, which the prover normalizes to `car`; they do not fire as stated (local car-form restatements used). statement-recover-stream's local fn-ssr-resident-ignores-places loops the preprocessor in any proof that mentions nil places; disable it.

## Continuation
1. On the hbox certify result (run id from the assembler): `evidence_manifests.py add RUN`, READY per book to the assembler (cc integrator).
2. proof-owed, newest first: cold-line's CL-PRE-PRODUCTIVE-READ-NEWNEWS, CL-OWED-NEWNEWS-DEMAND, CL-OWED-HDR-CURSOR-FRAME (asked the assembler about ownership/base; they live in cold-line's unmerged changes); then PGO-* (post-guard-off/carrier owners).

## Coordinates
| sha | world receipt | manifest id | image sha | native run id |
|---|---|---|---|---|
| lane/proofs2@0a1e06ad2 | pending | pending (hbox #5) | none (no host change but the interface citation) | none |
