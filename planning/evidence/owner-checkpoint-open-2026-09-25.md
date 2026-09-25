# The served owner opens from the Store checkpoint; replay carries the node invariant (2026-09-25)

Lane `owner-checkpoint-open`, from dev `3c1fd34a` (after the P3 merge). Commits
b5f7340d (books), 0e262c3e (host, native), b78326dc (host order fix), and the
evidence commit carrying this record. Follows
[bounds-p3](bounds-p3-2026-09-25.md) findings 1, 2 and 7. D27.

## What changed

- **Replay carries the node invariant** (`books/config-physical-replay.lisp`).
  `fn-cpr-apply-event` and `fn-cpr-loop` take `(fn-cnode-statep cn)` as their
  guard, the pattern of `fn-replay-loop` (books/replay.lisp). The `:logic`
  bodies are unchanged, so every theorem about the fold keeps its statement.
  The executable path runs the whole-node recognizer on neither the incoming
  node nor the one-event result, and tests a refusal by NIL. Before, it ran
  the recognizer three times per replayed event. `fn-cpr-replay` checks the
  initial node once, by evaluation (`fn-cpr-initial-cnode-statep`).
  `fn-sco-cpr-prefix` carries it the same way. `fn-sco-cpr-resume` and
  `fn-sco-cpr-finish` check a decoded checkpoint's node once, through `mbe`.
  Configuration records keep their checks: they are few, and each changes
  the configuration the node is checked against.
- **The owner opens from the checkpoint** (`books/owner-checkpoint-open.lisp`,
  prefix `fn-ock-`; host/owner-host.lisp). Both paths extend a checkpoint over
  the records after it, then install with `fn-ock-recover-extended`
  (owner-host.lisp:174):
  - From a verified checkpoint, `fn-owner-recover-from-checkpoint`
    (owner-host.lisp:224) extends the decoded checkpoint over the suffix.
  - On a full replay, `fn-owner-recover` (owner-host.lisp:209) extends the
    empty capture over the whole history.

  The native owner (`fnn-owner-recover-core`, host/native/owner.lisp:472 and
  :475) chooses by the Store open's mode. The extended value is the capture
  of the whole history. The owner keeps it as the base of its next
  publication. The full path also stops replaying twice: the old
  `fn-owner-recover` called both `fn-cpr-replay` and `fn-cpo-open-observed`.
- **The owner publishes** (`fnn-owner-maybe-publish`,
  host/native/owner.lisp:1818).
  - **When:** before each accept, on the accept loop's thread. That is after
    a client is launched, or every second when accept times out. It never
    runs inside a command.
  - **Policy:** ACL2's `fn-ock-publication-duep`. The owner publishes when
    twice the suffix since the newest durable checkpoint is at least K (the
    profile's `max-open-suffix`) and the suffix is at least one record. A
    count that already failed is not retried until another commit.
  - **How:** ACL2 computes `fn-ock-next-checkpoint`, the base extended over
    the records after it (owner-host.lisp:298). The host writes the octets
    through `fnn-state-checkpoint-write` (:1842), the P3 byte program
    `fn-bs-scp-program`, under the owner mutex.
  - **What it touches:** it reads `fn-owner` and writes only the
    `fn-owner-sco-*` globals.
  - **On failure:** a write that fails before the rename (exit-1 class), or
    is uncertain at or after it, is logged. Serving continues.
  - **Reporting:** the owner writes `OWNER-OPEN open=...` and
    `CHECKPOINT auto sequence=S suffix=k octets=O ms=T` to stderr. `status`
    now prints `checkpoint-file octets=O modified=T`
    (`fnn-state-checkpoint-file-report`, io.lisp:1655). While an owner runs,
    it is the only publisher, since the verb needs the store lock. So after
    a run this line is the last automatic publication, and `open=checkpoint:S`
    gives its S.
  - **Fault injection:** a developer image arms the five
    `FN_NATIVE_STATE_CHECKPOINT_FAULT` cuts for the owner.

## Theorems (ACL2 8.7, certified; manifests below)

- **`fn-owner-recover-from-checkpoint-equals-full-recover`**, no hypothesis:
  `(equal (fn-ock-recover-extended (fn-sco-extend (fn-sco-capture configs P)
  configs Q) configs frontier max-conns) (fn-ock-recover-full configs frontier
  (append P Q) max-conns))`.
  - `fn-ock-recover-full` is the composition that
    `fn-orec-recover-installs-ocl-relation` is stated over: the Store open
    `fn-cpo-open-observed`, the replay `fn-cpr-replay`, then `fn-own-start`
    (archive, pinned views, Message-ID trie, group buckets, ledger),
    `fn-own-configure` and `fn-ocfg-make`, with the host's checks.
  - Both sides give the same configured owner, or `:fault` on both.
  - Subject: `fn-ock-recover-extended` at owner-host.lisp:174, reached from
    :209 and :224. `fn-ock-recover-from-empty-capture-is-full` is the full
    path's instance.
- **`fn-ock-recover-installs-ocl-relation`**: on either path, a non-`:fault`
  install satisfies `fn-ocl-relation` and `fn-scar-view-indexedp`, the
  premises of the carried served keystones.
- **`fn-sco-extend-of-capture-when-history`** (store-checkpoint-open) and
  **`fn-sco-replay-of-capture`**: over an admitted P ++ Q, the extended
  capture is the capture of P ++ Q, and its configuration fold finishes to
  the full replay.
- **`fn-ock-next-checkpoint-is-the-capture`** (hypothesis: an admitted
  history) and **`fn-ock-published-checkpoint-opens-to-the-full-open`**:
  - What the owner publishes is the capture of its whole history.
  - Opening it over any later records is the full open.
  - So a publication never changes the state a restart serves, and the
    in-memory served owner is only read.
- **`fn-ock-not-due-keeps-the-checkpoint-open`**: until the owner is due,
  `fn-sco-select` serves the durable checkpoint, because the suffix is
  within K.
- **The crash keystone is P3's** `fn-bs-scp-program-crash-is-old-or-new`,
  the same byte program and the same host writer.
- **The carried invariant:**
  - `fn-cpr-apply-event-preserves-cnode-statep`: a non-refused event
    leaves a configured node. It has no other hypothesis: the logical body
    tests the incoming node.
  - `fn-cpr-apply-event-statep-iff-consp`: the `:exec` test.
  - `fn-cpr-loop-preserves-cnode-statep`: every fold result's node is
    configured when the fold starts from one.

## Teeth

**tests/acl2/owner-checkpoint-open-tests:**
- **Witness.** The P3 image (two retention events and two configurations,
  split after the first event). The full owner is not `:fault` and
  satisfies `fn-ocl-relation`. The checkpoint path and the empty-capture
  path each equal it. The configuration generation is 2.
- **`must-fail`:** the capture of a different prefix installs a different
  owner.
- **`must-fail`:** an install refused by a non-natural connection bound
  satisfies no relation.
- **Publication witness.** The next checkpoint from the prefix's capture is
  the whole capture, and it opens to the full open.
- **One `must-fail` for each of the five hypotheses of
  `fn-ock-not-due-keeps-the-checkpoint-open`**, each with the matching
  not-due assertion. The due, not-due and retry cases are asserted.
- **Untoothed:** the history hypothesis of
  `fn-ock-next-checkpoint-is-the-capture`.
  - The identity fold's append lemma takes it, but that fold's fault is
    absorbing.
  - An improper history and a two-non-event history both give the capture
    (asserted).
  - The owner's history always meets it. Dropping it needs a
    hypothesis-free identity append lemma.

**tests/acl2/config-physical-replay-tests:**
- **Witness.** An undertaking replays from the configured default node to a
  different configured node.
- **`must-fail`:** a refused event (unserved group) leaves NIL, which is not
  configured.
- **`must-fail`:** a loop started from a non-configured node carries it in
  its fault.

## Certification (persvati, w25 `acl2-literal`, 2 jobs, 300 s)

- **run-20260925T080519Z-a511 at b5f7340d**, manifest
  `certify-20260925T080536Z-2399940.json` (sha256 1f222bbe…). 30 books:
  - passed: config-physical-replay 2.6 s and its tests 2.1 s;
    store-checkpoint-open 3.3 s; owner-recover-ocl 4.8 s; config-observed,
    the store-node-traces chain and the owner books;
  - failed: owner-checkpoint-open and its tests (the proofs were then
    repaired in the REPL);
  - owner-invariants took 10.08 s. It was already over 10 s at 2 jobs
    before this lane (10.2 to 13.9 s in the manifests of 043843Z to
    064639Z), and this lane does not change it.
- **run-20260925T081930Z-668e at b78326dc**, manifest
  `certify-20260925T081938Z-2529044.json` (sha256 6388ebf4…).
  - Scope: every transitive dependent of config-physical-replay (49 roots:
    52 certified, 207 installed). All passed.
  - owner-checkpoint-open 5.0 s, its tests 4.7 s, store-checkpoint-open-tests
    3.2 s.
  - The slowest book was topic-history-store-invariants at 9.0 s. No book
    took more than 10 s.
- **Dependents:** books/owner.lisp is unchanged. books/config-physical-replay
  has 46 dependents by include-book closure, 19 books and 27 tests, and
  run 2 covers them all.

## Native (hbox)

**Setup:**
- Image `fn-host.core` 65ba0535…, developer core d78a5e4d… (`image.sha256`
  747ed0a6…).
- Tree 0e262c3e with owner-host.lisp from b78326dc, in
  /tank/fn/scratch/owner-checkpoint/.
- Closure certified in place on hbox, run certify-20260925T081058Z-2842298.
- Timed runs use a tmpfs copy of the store, built once in scratch on ZFS.
- Scale profile, K = 4096. Articles are 2 KiB (2,028-octet body).
- Every run is under `systemd-run --user --scope -p MemoryMax=40G`.

**Logs** (/tank/fn/scratch/owner-checkpoint/logs/, sha256):
- meas-n1000.log 1f6c0582…
- meas-n4096.log 8fd4cd32… (the build)
- meas-full-n4096.log aaa1a904…
- meas-smallk.log 95401c97…
- meas-baseline-n1000.log 355ebce0…
- native-tests-2.log 33a9e7d9…

| N=1000 (tmpfs) | wall | max RSS |
| --- | --- | --- |
| `status`, full replay, this image | 2.3 s | 1.70 GB |
| `status`, full replay, P3 image f77ae9bc (baseline, ran beside the N=4096 build) | 510 s | 2.09 GB |
| owner start to LISTENING, full replay (x2) | 3.1 to 3.2 s | 0.59 to 0.63 GB |
| owner start, P3 image (baseline, same store, concurrent) | 859 s | 0.81 GB |
| `store checkpoint` (full replay + capture) | 3.1 s | 2.05 GB |
| owner start from checkpoint, suffix 0 | 3.6 s | 1.03 GB |
| owner start from checkpoint, suffix 16 | 4.2 s | 1.01 GB |
| POST median / max, 16 each run, this image | 5.0 to 5.2 ms / 5.5 ms | |
| POST median, P3 image | 13.6 ms (concurrent with the build) | |
| checkpoint file | 8,098,243 octets | |

| N=4096 (tmpfs; the scale profile admits no 4097th transaction) | wall | max RSS |
| --- | --- | --- |
| `status`, full replay | 35.9 s | 2.60 GB |
| `status`, checkpoint (suffix 2048 / 0) | 19.3 s / 20.7 to 34.2 s | 2.6 / 4.08 GB |
| owner start, full replay | 47.9 s | 1.48 GB |
| owner start from its own checkpoint S=2048, suffix 2048 | 30.3 s | 2.05 GB |
| owner start from checkpoint S=4096, suffix 0 | 40.6 s | 3.30 GB |
| automatic publication at S=2048 (during the build), at S=4096 (at start) | 6.0 s, 7.6 s (12.2 s after a full-replay start) | |
| checkpoint file at S=2048 / 4096 | 16,336,719 / 32,686,012 octets | |

**Findings from these numbers:**
- **The full replay no longer grows with the node.**
  - At N=1000, full replay drops from P3's 226-251 s (alone) to 2.3 s.
  - At N=4096 it is 35.9 s, where P3 extrapolated about 7 h.
  - Why: the per-record factor c(S) that P3 found was the whole-node
    recognizer.
- **The checkpoint is no longer worth opening at these sizes.** Opening
  from it now costs about the same as a full replay: 3.6 s against 3.2 s
  at N=1000, 30 to 41 s against 48 s at N=4096. It also takes 1.6 to 2.2
  times the RSS.
  - Cause: the checkpoint carries the record list (P3 finding 3), so the
    open decodes a 32 MB value.
  - The Store open then re-encodes the covered prefix's octets for the
    owner (P3 finding 4).
  - The owner then extends the checkpoint over the suffix a second time.
- **POST wall is unchanged by this lane.** The POST path calls none of the
  changed functions. It measured 5.0 to 5.2 ms at N=1000 before and after
  a checkpoint. The build POSTs (on ZFS, 0.19 to 0.20 s median) are
  fsync-bound and not comparable.
- **A publication blocks served commands while it runs.** It held the owner
  mutex 6.0 s at S=2048: the build's post_max is 6.2 s, and the other
  connections wait. The value it encodes is immutable, so the extension
  and encoding could run outside the mutex. That is the next change.

**Automatic publication at K/2**, K=8 (`--max-open-suffix 8`):
- 14 POSTs 1.2 s apart publish at S = 4, 8 and 12:
  `CHECKPOINT auto sequence=4 suffix=4 octets=32165 ms=45`, then 8 and 12.
- Afterwards `status` prints `open=checkpoint:12 suffix=2` and
  `checkpoint-file octets=95753`.
- The restart opens `open=checkpoint:12 suffix=2`.

**Kill during the automatic publication** (developer image, `:kill`), from
S=12 with suffix 4. The owner is due at its first tick and is killed there
(rc -9, before any POST).

| cut | status after kill | restart | after 2 POSTs |
| --- | --- | --- | --- |
| state-checkpoint-written | `open=checkpoint:12 suffix=4` (old), staging orphan `.stage-checkpoint-…` | opens checkpoint:12, republishes S=16, orphan swept | checkpoint:16 suffix=2 |
| state-checkpoint-replaced | `open=checkpoint:16 suffix=0` (new) | opens checkpoint:16 | checkpoint:16 suffix=2 |
| state-checkpoint-durable | `open=checkpoint:16 suffix=0` (new) | opens checkpoint:16 | checkpoint:16 suffix=2 |

Every restart served and accepted POSTs. `tests/test_native_state_checkpoint.py`
and `tests/test_native_operator_cli.py` pass on the image (11 tests,
native-tests-2.log). The state-checkpoint test's observation now leaves out
the new `checkpoint-file` status line, which is file metadata and not state.

## The deployed store

The hbox node (`/tank/fn/node`, image 18c91321, not touched here) runs the
scale profile (K = 4096) with 8 transactions used
(node-hbox-18c91321-2026-09-24.md). No image there carries this lane.

- **On this image:** `operator run` at its next restart would find no
  checkpoint, replay its 8 records in full (milliseconds), and not publish
  until 2048 records are committed.
- **With a checkpoint:** it would open from it with the same result.
- **At its size:** neither path costs anything visible.
- **At 4096 records:** full replay would be about 48 s against 30 to 41 s
  from a checkpoint.

## Open items

- **Encoding off the mutex.** The publication should extend and encode
  outside the owner mutex.
- **The record list in the checkpoint** (P3 finding 3) and the prefix
  re-encode (P3 finding 4). Until both are removed, the checkpoint does not
  pay at 2 KiB and N ≤ 4096.
- **Suffix replayed twice.** The Store open and the owner open each replay
  the suffix. The owner could take the Store open's value; the keystone
  would then need the bridge's global named as its subject.
- **Untoothed hypothesis:** the history hypothesis of
  `fn-ock-next-checkpoint-is-the-capture` (see Teeth).
- **K0** still does not admit the `:root` rename (P3 finding 6).
