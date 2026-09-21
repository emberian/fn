# Independent review: native host raw I/O seam

Reviewer: Claude Opus 5, isolated worktree `build/lanes/w13-claude-review`,
detached at `406578c`. Date: 2026-09-21. One pass.

## Scope

**Reviewed:** the raw trust-boundary surface of `host/native/` — outcome
conditions, POSIX wrappers, durability barriers, bounded reads, directory
enumeration, the JSON reader for the two host-owned metadata files, the
`fnn-call` bridge into the certified core, and the socket surface — at
**`406578c`** (dev head). These files are unchanged on every live native tip,
so the findings apply to all of them.

**Deliberately excluded, to avoid colliding with work in flight:**

* the storage-codec / metadata-ownership rewrite of `io.lisp` on
  `w13/native-storage-codec` `37ec36b` (−273/+124) — root's persistence and
  publication API investigation;
* the user-facing CLI/config contract — Terra's audit;
* `host/native/crypto.lisp` on `w14/native-primitives` `f83722f`, which is new
  and still moving.

One cross-lane hazard in `host/native/owner.lisp` on `w13/owner-convergence`
`d47212d` is reported as F3 because it is the consumer of the seam defect in
F2, and its owner will want it before that slice lands.

## Findings (4, most severe first)

### F1 — An unreadable `config/` silently skips the generation-1 durability barrier, and `initialize` still reports success. Severity: high.

`fnn-config-record-names` (`host/native/io.lisp:908-915`) wraps the
enumeration in `(handler-case (fnn-list-directory ...) (fnn-os-error () nil))`.
Any errno from `opendir`/`readdir`/`closedir` on `config/` becomes an empty
list, indistinguishable from a directory that is genuinely empty.

`fnn-initialize` calls it **twice**, and it is a fresh enumeration each time
(no cache):

* `io.lisp:1054` — `(when (null (fnn-config-record-names store)) ...)` decides
  whether to publish generation 1;
* `io.lisp:1068` — `(dolist (name (fnn-config-record-names store))
  (fnn-fsync-regular ...))` is the final durability barrier over the
  configuration records.

**Concrete failure trace.** Initialize a fresh store. Root, `transactions`,
`staging`, `config` are created; `config.json` is published; the first
enumeration correctly returns `nil`; `config/00000001.cfg` is published and
`fnn-fsync-dir` fences the directory entry. Execution reaches `:1068`. The
second `opendir` on `config/` fails — EIO on the directory, or EMFILE/ENFILE,
which is reachable because the process is already holding the writer-lock
descriptor and `fnn-transaction-files`/`fnn-staging-orphans` open more. The
handler returns `nil`, **the `dolist` body never runs**, so
`config/00000001.cfg` never receives `F_FULLFSYNC`/`fsync(2)` on its
*contents*. `fnn-initialize` then completes its remaining fences and returns
normally: exit 0, store reported initialized.

The consequence is not cosmetic. `fnn-config-records`
(`io.lisp:917-929`) faults with "refusing store with no durable configuration
record" when the history is absent, so after a power loss that drops the
unfenced record the store is **unopenable** — and the host told the operator
it was initialized. This is the "never infer durable acceptance" rule, and it
is a direct divergence from the model of this exact path:
`books/byte-store-initializer.lisp:94` has `(:fsync-file :config
"00000001.cfg")` as an unconditional step with no failure-free branch.

A second, lesser consequence of the same root cause: at `:1054` a swallowed
errno reports "no records" for a store that has them, and the host proceeds to
publish generation 1 over existing history. `fnn-publish-initial-file`
(`io.lisp:963-979`) returns `nil` on `EEXIST`, and that return value is
discarded, so the divergence is silent.

The correct pattern already exists twelve lines away:
`fnn-transaction-files` (`io.lisp:984-986`) and `fnn-staging-orphans`
(`io.lisp:1002-1004`) both convert the same failure into
`(fnn-fault "cannot enumerate ...")`.

*Minimal correction:* make `fnn-config-record-names` propagate —
`(fnn-os-error () (fnn-fault "cannot enumerate configuration records"))` — and,
where "absent" genuinely must be distinguished from "unreadable", decide it
from an explicit `fnn-lstat` of `config/` rather than from an empty list.

*Evidence needed:* a fault-injection case in the native storage tests that
fails the **second** enumeration and asserts a non-zero exit with no success
output; plus the existing `tools/fn_native.py` differential against the Python
host, which faults on the same condition.

### F2 — At the served-connection boundary, uncertain and fault collapse into refused. Severity: medium-high.

`fnn-store-indeterminate` and `fnn-store-fault` are defined as **subtypes** of
`fnn-store-error` (`io.lisp:67-68`). `handler-case` dispatches by subtype, so
a clause naming `fnn-store-error` catches all three.

`fnn-serve-client`'s outer handler (`io.lisp:1706`) is exactly that:

    (fnn-store-error () nil)

with no `fnn-store-indeterminate` or `fnn-store-fault` clause before it. The
inner handler around `fnn-reader-chunk` (`io.lisp:1690-1693`) has the same
shape. So an uncertain persistence outcome, a store fault and an ordinary
refusal all produce the same thing: the connection is dropped, the listener
continues, nothing distinguishes them. The comment immediately above
(`io.lisp:1704-1705`) asserts the opposite — "only a Lisp condition that is
not a refusal is a bridge fault" — while the code classifies a fault *as* a
refusal.

The contrast is inside the same file: `fnn-exit-code-for` (`io.lisp:87-94`)
gets it right, ordering `fnn-store-indeterminate` → 3 before
`fnn-store-fault` → 4 before `fnn-store-error` → 1. The CLI boundary keeps the
three outcomes distinct; the served boundary does not. That is the D13 rule,
"three outcomes stay distinct all the way out, at every boundary".

Today this is **latent**: the reader path is read-only and hard-codes
`(fnn-reader-outcome :refused)` at `io.lisp:1698`, so an indeterminate is
unlikely to reach the handler. It stops being latent the moment a writable
service replaces that constant — which is what `w13/owner-convergence` does.
See F3.

*Minimal correction:* add `(fnn-store-indeterminate (e) ...)` and
`(fnn-store-fault (e) ...)` clauses ahead of the `fnn-store-error` clause at
both sites, and make them report distinctly.

*Evidence needed:* a served-path test that raises each of the three conditions
and asserts three distinct observable results.

### F3 — The in-flight writable owner slice inherits the collapse at its connection handler. Severity: medium (branch `w13/owner-convergence` `d47212d`, not dev).

`host/native/owner.lisp:265` on that branch:

    ((or fnn-store-error fnn-os-error sb-bsd-sockets:socket-error) (e)
      (fnn-err "owner connection: ~a" e))
    (serious-condition (e)
      (fnn-err "owner connection fault: ~a" e)
      (when cid (ignore-errors ... (fnn-owner-action 'fn-owner-fault cid))))

By the subtype relation in F2, an `fnn-store-indeterminate` escaping
`fnn-owner-handle-chunk` lands in the **first** clause. It is logged with the
same wording as a socket error, and — the material part — `fn-owner-fault` is
reached only from the `serious-condition` clause, so **the owner core is never
moved into its fault state after an uncertain persistence outcome**, and the
service keeps accepting work. "Treat ambiguous persistence failures as
recovery events; do not silently continue mutating after an uncertain commit."

This is worth raising with that lane rather than filing against dev, because
the same file already gets the ordering right elsewhere —
`owner.lisp:169` (`(fnn-store-indeterminate (e) (error e))` ahead of
`fnn-store-error`) and `owner.lisp:180-181`
(`(fnn-store-indeterminate () :uncertain)` ahead of
`((or fnn-store-error fnn-os-error) () :refused)`). The outer connection
handler is the one site that missed it.

*Minimal correction:* one `fnn-store-indeterminate` clause ahead of the
combined clause, routing to `fn-owner-fault` and a distinct message.

*Evidence needed:* an owner-path test that injects an uncertain store outcome
mid-connection and asserts the core entered its fault state.

### F4 — `fnn-send-all` lacks its twin's zero-progress guard, and neither socket primitive retries EINTR. Severity: low.

`fnn-write-all` (`io.lisp:292-299`), which writes files, guards
`(when (<= count 0) (fnn-fault "short store write"))`. Its socket twin
`fnn-send-all` (`io.lisp:1597-1604`) does not: a `count` of 0 leaves `offset`
unchanged and the loop repeats, with `sb-sys:wait-until-fd-usable` continuing
to report the descriptor writable.

Separately, both `fnn-read-fd` (`io.lisp:301-307`) and `fnn-send-all` turn a
`NIL` return from `sb-unix:unix-read`/`unix-write` straight into
`fnn-os-fail`, including when the errno is `EINTR`. The file header claims
"the host's decisions are the Python host's decisions, in the same order, with
the same messages" (`io.lisp:40-42`), but the Python host it mirrors retries
`EINTR` automatically (PEP 475, Python ≥3.5). A signal delivered mid-transfer
therefore drops a connection in the native host and does not in the Python
one — which also means the byte-for-byte differential cannot see it.

*Minimal correction:* add the `(<= count 0)` guard to `fnn-send-all`, and
retry on `EINTR` in both primitives.

*Evidence needed:* a differential case that delivers a signal during a large
transfer and compares the two hosts.

## Checked and cleared — do not re-report

Each of these looked like a defect and is not; I verified rather than assumed.

1. **`readdir` EOF/error conflation.** `fnn-list-directory` (`io.lisp:343-355`)
   treats a null alien as end-of-directory, which would normally hide a
   mid-scan error. SBCL is careful here: `sb-posix:readdir` is defined with the
   `null-alien-and-errno-plusp` error predicate and emits `(set-errno 0)`
   before the call
   (`sbcl-2.6.8/contrib/sb-posix/interface.lisp:221-230`,
   `macros.lisp:97-107`), so a real error signals `syscall-error` and
   `fnn-posix` converts it. **Not a defect.**
2. **Directory ordering versus Python's `sorted()`.** Handled:
   `fnn-config-record-names` sorts with `string<`, `fnn-transaction-files`
   sorts numerically on the parsed sequence and then checks gap-freedom.
3. **The JSON reader on untrusted input** (`io.lisp:484-595`): never touches
   the Lisp reader, depth-bounded at 32, input pre-bounded by
   `fnn-read-regular-bounded` (16384 / 4096), rejects control characters in
   strings, rejects trailing data. Sound against the bounded-parsing rule.
4. **`fnn-read-regular-bounded` TOCTOU** (`io.lisp:309-333`): reads
   `maximum + 1` and re-checks `total > maximum` after the loop, so a file
   that grows between `fstat` and the read is caught.
5. **`fnn-durable-barrier`** (`io.lisp:259-272`): falls back to `fsync(2)`
   only on the enumerated "unsupported" errnos; any other errno, EIO included,
   propagates. The docstring correctly declines to call it a power-loss
   qualification.
6. **`fnn-listen`** (`io.lisp:1636`): defaults to loopback; off-box exposure
   requires the operator to pass an address.

## Acknowledged, already recorded — not findings

* The whole file is an **unproved raw surface under a trust tag**, stated at
  `io.lisp:3-9`, isolated to `host/native/`, and retired with `(defttag nil)`
  before `save-exec` (`host/native/build.lisp:64`).
* **The JSON metadata twins are already owned, not open repair work.** The
  header's admission that this file holds the config and frontier checksums and
  the metadata grammar (`io.lisp:40-44`) describes `406578c`; the active native
  candidate `37ec36b` has already removed them and routed metadata through
  ACL2. I reviewed the seam at dev head, so item 3 of "checked and cleared"
  (the JSON reader) describes code that the candidate supersedes — it is
  sound, and it is also on its way out. **No repair is requested there.** The
  residual host-held decisions after that change (errno classes, the bounded
  directory grammar) sit under the registry's existing D07/HST-001 opening:
  "native owner, configuration/control/CLI, selected feature parity and
  deployment dependency gate remain open" (`planning/requirements.json`,
  HST-001).
* `fnn-random-hex` (`io.lisp:366`) draws staging-name entropy from CL `random`
  over `sb-ext:seed-random-state`, where the Python host uses `os.urandom(12)`.
  Inside a `0700` staging directory this is a naming divergence, not an
  authority one; noting it only so the differential's authors know why the
  names differ.

## Relation to root's BP findings — no overlap

Root's findings on `w13/bp-convergence` `52ab12d` — `fnn-bps-persist-record`
reporting durable after an fsync error on the strength of visible equal bytes,
outcome aggregation, and per-publication whole-journal rescans — do not
intersect F1–F4. Different files (`host/native/bp.lisp` versus `io.lisp` and
`owner.lisp`), different call paths, no shared function.

They are, however, the same two failure patterns, which is worth saying once:

* *A non-durable signal read as durability.* Root: equal visible bytes after a
  failed fsync. Mine (F1): an empty directory listing after a failed
  `opendir`. Both let a successful-looking return stand in for a barrier that
  did not happen, and in both the model of the path has the barrier as an
  unconditional step.
* *Outcome classes collapsing at a boundary.* Root: outcome aggregation. Mine
  (F2, F3): `handler-case` subtype ordering folding uncertain and fault into
  refused.

If the three outcomes and the "durable only on a completed barrier" rule were
each enforced at one place rather than restated per call site, both families
would be structurally excluded rather than separately patched. That is an
observation for whoever converges these, not a fifth finding.

## What I did not do

No build of the native image, no certification run, no lab. Every finding is
decided by reading the source plus, for the cleared item 1, SBCL 2.6.8's own
contrib source on this machine. F1–F4 each name the single test that would
settle them.
