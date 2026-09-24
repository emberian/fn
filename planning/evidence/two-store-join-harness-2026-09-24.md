# Two-Store join harness, dry-run on 863c2141 (2026-09-24)

This record covers the harness for the night's stretch goal: one end-to-end
join with crash cuts, fresh signed peering into Mini consumption across two
Stores. **It does not claim the join.** On `863c2141` the harness stops, as
expected, where the e160 preflight stopped: B has no acceptance-time receiver
verdict for the peered report. That is a correct negative result from fn and
not a harness defect. The fix (peer-authored ingress, `c12f4f28`, `9963dbbe`,
`e7aeac8f` and later; [record](peer-authored-ingress-2026-09-24.md)) is newer
than this image.

## What the harness does

`tools/runbooks/two_store_join.py` (SHA-256
`c88160cf459d3959928f6ae913f455ed9ff49971b89619518ab7b49c884c99e6`) is one
file with two halves:

- `run` executes on the Mini host (the Mac, where the Darwin Mini
  executable lives). It copies itself and the retained R source into
  `SCRATCH/harness/` on hbox. It then runs every native step as
  `ssh hbox python3 SCRATCH/harness/two_store_join.py fn --scratch SCRATCH <subcommand>`.
  Mini steps run locally. Mini reaches fn only through Mini's own transport
  `scripts/fn-e1e2/fn_bridge.sh` (SHA-256 `2d47f20b…ce68c`), the bridge that
  Mini's retained evidence names.
- `fn <subcommand>` executes on hbox. It provisions the two Stores, starts and
  kills the owners by recorded PID, and observes them over protected NNTP and
  the native CLI. Every value it compares is produced by the fn image:
  `hybrid-sign`/`hybrid-author`/`hybrid-verify-source`, `consumer
  poll/ack/position`, `consumer-project`, `HDR :fn-verified`, and `GROUP`.
  Python only compares bytes and never computes an identity, verdict or
  cursor.

Provisioning follows the pattern of the retained owner fixture
`tests/test_fn_e1e2_two_store_owner.py`, but runs outside unittest so that
each step leaves its own record. It creates two fresh Stores (`store init
fn.test`) under `SCRATCH/{a,b}`, each with a fresh self-signed STARTTLS pair.
Each Store requires `[auth] required = true, protected_only = true`. Each has
one posting principal whose generated password is stored only in
`SCRATCH/<node>/password` (0600) and in the peer's `.fnauth` profile (0600).
The Stores peer reciprocally with `starttls` and the peer certificate as the
only anchor. Separate R (A-side author) and Q (reply author) Ed25519 +
ML-DSA-65 keysets are created with the pinned OpenSSL 3.5.8. Two ports above
11200 are chosen that `ss -ltnH` shows free and that bind. Before starting,
the harness checks the launcher and core SHA-256 values against the image
directory's manifest (`image.sha256`, or `freeze/image-pair.sha256`). It
refuses to start without a manifest. It also rejects a SCRATCH directory that
already exists. At each owner start it records `/proc/PID/exe` and the core
SHA-256.

The exchange, one step per line in `logs/NN-<step>.{log,exit}`:

1. Mini: two fresh deployments (B side and A side), each bootstrapped from the
   pinned E2 genesis and admitted only its birth intent.
2. fn: provision; start A and B; consumer bootstrap and register `worker` on
   both; enroll R at generation 1 on both. A bridge `consumer position` checks
   that Mini's transport reaches this image.
3. R accepted at A (`hybrid-sign` then `hybrid-author` on A's control socket),
   then read back durably from A. Control step `a-verdict-r-control`: A's own
   acceptance carries `HDR :fn-verified = 0 verified <R> keyring 1`.
4. Protected A→B peering: R appears at B and B's copy verifies natively
   against R's keys and exact source. Live `GROUP fn.test` returns count 1 on
   both Stores.
5. B's receiver verdict is durable: B is stopped (TERM) and restarted, R's
   bytes are unchanged, `HDR :fn-verified` must be `0 verified <R> keyring 1`,
   and B's `consumer poll` must project through `consumer-project`. A drains
   its own R (poll, project, ACK). Q is enrolled at generation 2. Then
   generation 2 is checked, with B's preview poll.
6. Mini consumes at B: `consumer-poll-decide` through B's control socket
   (`proposed-fresh`, bytes equal to the preview), `mini submit`,
   `consumer-export-poll`/`-reply`, then `consumer-ack-poll`
   (`fnAck=durable-accepted`). B's `consumer position` must equal the ACKed
   cursor.
7. Mini's reply: `consumer-stage-reply-plan` and `consumer-stage-reply-sign`
   (Q secret keys never leave hbox), then the bridge runs `hybrid-author` at
   B, generation 2. Q must be durable at B, verify natively, reach A, and
   `GROUP` must count 2 on both Stores.
8. Restart A and B (TERM by PID, restart from the same Stores). Q's bytes at
   A are unchanged and counts are still 2/2. A's `HDR` for Q is
   `keyring 2`, and A's preview poll projects Q.
9. Mini reads at A: `reply-consumer-poll-decide` (the A-side Mini deployment,
   Q claim from Mini's signed slot), `mini submit`,
   `reply-consumer-export-result`, `reply-consumer-ack-poll`. A's position
   must equal the ACKed cursor.
10. Stop both owners. `operator status` reports `articles=2` on each Store.

Every step has exactly one outcome: ACCEPTED, REFUSED, UNCERTAIN, or FAULT.
FAULT means the harness itself is defective, never an fn answer. Native exit
1 is REFUSED, and native exit 3 is UNCERTAIN. An NNTP timeout, a missing
article at a deadline, or a lost transport reply is UNCERTAIN. A Mini
`fnAck` of `uncertain` or `transport-fault` is UNCERTAIN. The run stops at the
first step that does not produce the required outcome. It then stops the
owners it started, by PID and only after checking that PID's cmdline, writes
`steps.json`/`summary.json`, and copies the logs to `SCRATCH/logs`.

## Crash cuts (`--cut`)

The harness adds no new cut machinery. The feed cuts reuse the developer
selector `FN_NATIVE_FEED_TEST_STOP_AFTER_SENT`
(`host/native/feed-service.lisp`, used by
`tests/test_native_protected_peering.py::test_durable_sent_cut_requeues_on_protected_restart`).
With it, the feed worker SIGSTOPs its own process after the durable
`:feed-sent` record and before the article bytes reach the peer. The
restart is a state that `fn-feed-restart` expresses.

| Family | Boundary | Invariant checked after restart |
| --- | --- | --- |
| `a-accepted` | A runs the developer image; after R is accepted, A stops at durable `:feed-sent`; R absent at B; SIGKILL A; restart A (production image) | R durable at A, A verdict intact, R reaches B, `GROUP` 1/1 (no duplicate, no loss) |
| `b-verdict` | after B's verdict is durable **and** Mini has committed the poll in its own transaction, before Mini's ACK: SIGKILL B, restart | re-poll returns the identical cursor and event bytes; position still equals the registration cursor (no advance, no loss); the ACK then proceeds |
| `ack-response` | Mini's ACK is committed by fn, its reply lost (Mini's bridge `FN_E1E2_DROP_ACK_REPLY`) | recorded as UNCERTAIN; settled only by `consumer position` = cursor; the repeated ACK is `durable-accepted` |
| `reply-at-b` | B restarted on the developer image with the feed cut before Q is posted; B stops after Q's durable `:feed-sent`; Q absent at A; SIGKILL B; restart | the post outcome is recorded as-is (UNCERTAIN if the stop beat the reply); Q is settled by a read of restarted B; Q reaches A; `GROUP` 2/2 |

The `b-verdict` kill targets an owner that is idle between commands. The
harness cannot prove that the feed worker was idle at that instant. The
claim is "restart from the durable Store", not a named model crash point.
A reviewer should check this against the AGENTS.md rule "every process-death
cut is a model crash point" before citing a pass.

## Invocation

On the Mac, from a checkout containing the harness, with ssh alias `hbox`:

```sh
python3 tools/runbooks/two_store_join.py run \
  --image-dir /tank/fn/gates/<gate>/build \
  --mini-bin /Users/ember/dev/minidregg-wt/fn-evidence/.lake/build/bin/minidregg-host \
  --mini-sha256 0cce4fbd02c5b5156fb061e2d96f2e25e12588c35b59d2fd2efe20acb202f286 \
  --scratch /tank/fn/scratch/two-store-<date>/<run> \
  --local-out <fresh local dir> \
  --cut none|a-accepted|b-verdict|ack-response|reply-at-b
```

Mini inputs default to the retained E2 paths: pinned config/genesis/birth
intent/policy/origin pin under `/tmp/mini-fn-e2-native-20260923/`, custody key
`/tmp/mini-fn-portable-inbox-native-20260923/consumer.key`, the R claim and
source from `tests/fixtures/dregg-e1/`, and the `mini` client from the
fn-evidence worktree. Each can be overridden (`--help`). An image directory
built by `hbox-image-build.sh` works if its `image.sha256` names `fn-host`
and `fn-host.core`. The developer pair is required only for the two feed
cuts.

## Dry run on 863c2141

Image `/tank/fn/gates/capability-863c2141-20260924/build`: production
launcher/core `d3214eb2…4bfeb4f` / `fb208850…2803107`, developer
`c70fdd71…ecbf49e` / `e743ae19…a489e7c0`, matching `freeze/image-pair.sha256`.
Runtime `/tank/fn/sbcl/bin/sbcl` is `b115fe95…c6d5`. The observed
`/proc/PID/exe` and core matched at every start. Mini executable
`minidregg-host` from `implement/fn-evidence` `183cd37`, SHA-256
`0cce4fbd02c5b5156fb061e2d96f2e25e12588c35b59d2fd2efe20acb202f286`
(verified by `--mini-sha256`). The `mini` client is `e86dbc95…9ae60`. Ports
were 11201/11202. Each run took about 60 s, 40 s of it in the two Mini
births.

| Run (`--cut`) | Reached | Stopped at | Cut reached | `steps.json` SHA-256 |
| --- | --- | --- | --- | --- |
| `none` | 22 steps ACCEPTED | 23 `b-verdict-gen1` REFUSED | n/a | `6b0aa601…4f5612` |
| `a-accepted` | 26 steps ACCEPTED, including the whole cut | 27 `b-verdict-gen1` REFUSED | **yes, invariant held** | `b0d683d1…72c41b` |
| `b-verdict` | 22 steps ACCEPTED | 23 `b-verdict-gen1` REFUSED | no (boundary is after this step) | `6ec3b858…7eae` |

The refusing step logs (`logs/23-b-verdict-gen1.log`, SHA-256
`4254a95a…a987d3` for `none`, `f1351417…0f4ea` for `a-accepted`, `7ce189f0…e1f8`
for `b-verdict`) all record the same three facts:

- B's `HDR :fn-verified <R>` is `0 absent no-record`. The expected value was
  `0 verified 5252…52 keyring 1`. (e160's wording was `no-field`.)
- B's `consumer poll` returned a 30,338-byte event, the same size as e160's
  legacy `fn-r` record.
- Native `consumer-project` answered `fn-consumer-project-refused-v1 codec`
  (exit 1).

A control on the same image in the same run distinguishes this from a harness
fault. Step `a-verdict-r-control` returned `0 verified 5252…52 keyring 1` at A
for the same R, authored by the same harness under the same keys. An earlier,
discarded iteration also polled A: the poll projected, with a 53,043-byte
kind-4 event. Before the refusal, the whole peering leg ran through fn: B
received R over protected transit, `hybrid-verify-source` on B's copy matched
R's keys and exact source, B's bytes were unchanged across a B restart, and
`GROUP` counted 1/1. What is missing is the receiver's own acceptance-time
verdict. The peer-authored-ingress packet adds exactly that.

The `a-accepted` cut ran to completion on 863 (steps 14–22). A stopped
(`State: T`) after durable `:feed-sent`, and R was absent at B for 3 s.
A was then SIGKILLed (PID 1128081, developer core `e743ae19…`) and restarted
on the production core (PID 1128863). R was then durable at A with its
verdict, arrived at B, and `GROUP` counted 1/1. Cut family result on 863:
**`a-accepted` held its invariant; `b-verdict`, `ack-response` and
`reply-at-b` were not reachable**.

Three harness defects were found and fixed during the dry runs. Their runs
were discarded and are not evidence. `GROUP`'s one-line 211 reply had been
read as multi-line, which gave a FAULT. A control read of A was attempted
while the cut had A SIGSTOPped, which gave a FAULT and later an UNCERTAIN
timeout, now classified as UNCERTAIN. The read of A's durability now happens
after the cut's restart.

Retained on hbox under `/tank/fn/scratch/two-store-20260924/dry-863-{none,a-accepted,b-verdict}/`:
Stores `a/`, `b/`, `logs/`, `steps.json`, `summary.json`, `pids.log`,
`console.txt`, the harness copy under `harness/`, and the Mini-side output
under `mini-side/` (including both Mini deployment roots). No owner is left
running. Every PID the harness started is recorded in `pids.log` with its
stop.

## Expected on the repaired image

If peer-authored ingress works on a source-matched image, step
`b-verdict-gen1` becomes ACCEPTED (`keyring 1`, projected source equal to R).
The run then continues into Mini's consumption at B, which has not been
exercised in this composition. The first new failure point will be in
steps 6 to 9, which nothing has run end to end. Specific risks:

- `reply-consumer-poll-decide` has never run against a live fn.
- The A-side Mini deployment reuses the E2 genesis, birth intent and custody
  key, so it is a fresh root but not a separate admin/custody identity. Mini's
  handoff asks for a separate identity.
- The bridge's post-ACK check hardcodes consumer `worker`, which is why both
  Stores register `worker`.
- The bridge sets `FN_OPENSSL_PREFIX` but not `LD_LIBRARY_PATH`. This worked
  for `consumer position` on 863 but has not been checked for `hybrid-*`
  through the bridge on the new image.
- `reply-at-b` assumes that B's restarted feed has nothing to send A before Q.

Each pass must be read from the refusal or acceptance line of each step, not
from the summary.

## What this does not establish

- No end-to-end join. Nothing past B's verdict ran on 863.
- The R report is not a fresh Mini submission. It is the retained Mini E1
  source, authored at A by fn `hybrid-sign`/`hybrid-author` under fresh
  harness keys, as in the retained owner fixture.
- No physical power-loss durability. The cuts are SIGKILL of owner processes
  on one host, and the Stores are loopback peers on the same machine.
- Nothing about the live node `/tank/fn/node`, which was not touched.
- The harness is not a qualification of the image. It does not run the
  relocation or two-host gates.
