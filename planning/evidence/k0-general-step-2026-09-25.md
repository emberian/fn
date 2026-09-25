# K0 general step (T16 model side), 2026-09-25

Lane `k0-general-step`, branch `lane/k0-general-step` from dev `3a1dcb34`.

## What is proved

`books/byte-store-k0-step.lisp`, keystone `fn-bs-step-preserves-k0-coverage`:
for every byte state `bs`, kernel `ks`, step and outcome, if
`(fn-bs-k0-coveredp bs ks)` and `(fn-bs-k0-step-inputp bs ks step outcome)`,
then after `fn-bs-step` the pair is covered, and the kernel is unchanged unless
the step is an `:observe`. Covered means related, or a pending
committed-history rename whose dropped and landed resolutions are both related;
`fn-bs-k0-covered-crash-image-is-a-related-image` shows that every crash image
of a covered state is a crash image of a related state. So every crash image
after the step is related to the kernel or to its successor. Any outcome
includes the error returns. A program made of covered steps is covered at
every cut: a `:cut` is the identity (`fn-bs-k0c-cut-step-is-identity`).

These are the step kinds covered, with the precondition each needs. Every
precondition requires that the kernel is outside the recovery window.

| kind | precondition (besides the relation) | outcomes |
| --- | --- | --- |
| `:cut` | coverage | any |
| `:create` | `:staging`, a typed name | any |
| `:write-all` | typed octets; the target is not an authority inode (D2) | any (a short write is its prefix's write) |
| `:fsync-file` | natural non-authority target; `:root` and `:transactions` quiet | `:ok` or a well-formed crash selection of that file's writes |
| `:fsync-dir` | `:staging`; `:transactions` in `:record-attempted` with the link pending; `:root` over a pending marker rename (coverage only) | `:ok`, `:ok`, any |
| `:unlink` | not `:root`/`:transactions` | any |
| `:rename` | `:staging` to the marker name, root quiet, source present (result covered); `:staging` to the frontier name under the frontier conditions of `fn-bs-k0-add-pending-frontier-rename-transports-relation` (result related) | any |
| `:link` | `:staging` to the next transaction name, transactions quiet, source fenced, allocated and reading as the kernel's candidate, kernel record-present-visible with its own durable records | any |
| `:observe` | frontier non-commit events, `(:record-link :error)`, `(:record-dir :error)`, `:core-completion`, `:emit-success`; `(:record-dir :ok)` and `(:frontier-dir :ok)` with their directory-committed premise | n/a |

The step lemmas for arbitrary related states and every outcome are in
`books/byte-store-k0-step-lemmas.lisp`: `fn-bs-k0s-write-preserves-relation`,
`-fsync-file-preserves-relation`, `-create-`, `-unlink-`,
`-marker-rename-covered`, `-frontier-rename-preserves-relation`,
`-add-pending-transaction-link-preserves-relation`, `-link-preserves-relation`
and `-marker-barrier-resolves`.

## Not done (open, named)

- **Not covered by the general theorem:** `:mkdir` and `:link-eexist` (these
  are initialization steps, and init has its own theorem);
  `(:record-file :ok)` and `(:record-link :ok)`, which have no stand-alone
  kernel lemma; the error outcomes of the `:staging` and `:transactions`
  barriers; every step in the recovery window. P-RECORD's two `:ok`
  observations are therefore not covered by construction yet.
- **Corollaries not derived:** the brief asked for the frontier, record and
  marker per-cut theorems to be derived from the keystone. That was not done.
  Deriving them needs `fn-bs-k0-step-inputp` discharged at each program pair,
  which is the pair-shape reasoning the per-cut books already contain. The
  per-cut theorems are unchanged, and the registry still cites them.
- **Marker error arms: partly done.** The witnesses in the test book show
  every marker step kind with an error outcome from its actual pair. Their
  EIO results are covered: create, short write, failed fsync, issued and
  unissued rename, and the root barrier dropping the entry. The general
  theorem covers every outcome of each of these kinds. A universally
  quantified theorem stated at the five marker pairs, with the `fn-hm-*` fence
  (no `:emit-success`; the kernel stays `:completing`), is not proved. It is
  implied by `fn-bs-k0s-syscall-step-keeps-kernel` once the step inputs at the
  pairs are discharged, and that discharge is the same open item as the
  corollaries.

## Teeth (`tests/acl2/byte-store-k0-step-tests.lisp`)

Reachable witnesses come from the K5 fixture's completing pair and the marker
run from it. For each case the precondition and the conclusion both hold:
`:create` (ok, EIO), `:write-all` (ok, `(:eio . 3)`), `:fsync-file` (ok,
`(:eio)`), `:rename` onto the marker (ok, issued EIO, lost EIO), `:fsync-dir
:root` over the pending marker (ok, EIO), `:cut` at the covered-not-related
pair, `:unlink` in staging, and `(:observe (:core-completion 1 1))`. A
`must-fail` drops the step precondition: a write to `config.json` from the
related pair.

Link, frontier rename, transactions barrier and the directory-commit
observations have no witness in this book.

## Findings

1. The coverage hypothesis is implied by the step precondition. Every kind's
   precondition carries the relation, or the marker-pending coverage for the
   root barrier. So `(fn-bs-k0-coveredp bs ks)` has no separating instance,
   and the test book shows the implication instead. Removing the hypothesis
   from the statement is a one-line follow-up.
2. `make check` reports the ledger stale for the new events. The lane does not
   regenerate `planning/ledger.*` (brief).

## Certification

- persvati `run-20260925T043818Z-70ed`, manifest
  [certify-20260925T043836Z-488782](manifests/certify-20260925T043836Z-488782.json),
  source `383c81c5`, ACL2 8.7 w25 `acl2-literal`, 2 jobs, 300 s:
  `books/byte-store-k0-step-lemmas` 8.2 s and `books/byte-store-k0-step`
  6.0 s certified. The test book failed on the coverage tooth (finding 1).
- persvati `run-20260925T044009Z-cd23`, manifest
  [certify-20260925T044034Z-508103](manifests/certify-20260925T044034Z-508103.json),
  source `55f17000`, passed. It certified the roots and
  `--affected-by books/byte-store-k0-step`:
  `tests/acl2/byte-store-k0-step-tests` 5.9 s, with the two books installed at
  the same bytes.
- Proof development was done in a persvati `proof_repl` session. The laptop
  REPL refused the unqualified Homebrew launcher.
