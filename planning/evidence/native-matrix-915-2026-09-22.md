# The full v0 matrix against the native 915 image — 2026-09-22

Seven runs of `tools/v0_matrix.py --backend native-operator` from `dev`
(`2202a95f`, `783db508`, then `6c5df887`/`5f1e6c48`) against the immutable
`915d5c72` production
image on persvati, with two preprovisioned stores (`store init fn.letters`
through the image, `fn.toml` with a loopback listener and a control socket).
Each run's rows, invocations and logs are its own directory under
`v0-runs/`; nothing here is published as `planning/v0-matrix.json`.

| run (UTC) | driver | rows exercised | disagreed | faulted | what changed |
| --- | --- | --- | --- | --- | --- |
| `20260922T012330` | `2202a95f` | 13 | 0 | - | as quiesced: both nodes reported dead in 0.3 s |
| `20260922T012512` | `783db508` (uncommitted) | 81 | 0 | - | nodes start through `env` |
| `20260922T013727` | `783db508` | 99 | 4 | 4 | offline admin, outcomes, transit, pins, stop added; `$HOME` quoted |
| `20260922T014155` | `783db508` | 121 | 12 | 2 | quoting fixed; peer records carried an outbound feed |
| `20260922T014358` | `783db508` | 123 | 4 | 0 | outbound `-`; the four loop rows remain |
| `20260922T030846` | `6c5df887` | 128 | 6 | 7 | AUTHINFO, live groups, the wildcard listener and the independent client became measurements |
| `20260922T032121` | `5f1e6c48` | 128 | 6 | 7 | same rows, same counts; the duplicate submission swapped nodes |

Counts are the tool's (`summary` in each `matrix.json`); "exercised" is
accepted plus refused plus uncertain.

## What the last run shows on the 915 image

Node status and start, groups (create, served, retire, unknown), capacity on
a scratch store, peer add and remove, POST with read-back, fresh and duplicate
POST, the reader profile, capability pins on both nodes, two readers across
one POST, the operator `post` accepted then refused as a duplicate, `recover`
after SIGTERM, transit offer/transfer/identical/duplicate both ways, MODE
STREAM, CHECK/TAKETHIS fresh and duplicate, and the witness's feed queue,
offer and journal rows. None of it needed a Python process in the node.

## Findings, in the order they surfaced

1. **The driver had never started a native node.** `nohup VAR=x cmd &` execs
   `VAR=x`. Every earlier native run's 181 not-exercised rows were this.
2. **A host fault was reported as D13's uncertain outcome.** `exit_verdict`
   folded every code outside 0/1/3 into `uncertain`. It is now not-exercised
   with the code named, counted as `faulted`, and the run exits 1 over it.
3. **The native outbound feed works, live.** With `fn.*` outbound on the peer
   records, every live post reached the other node before the driver's own
   offer (eight articles per node in the 01:41Z run). The matrix's records
   now carry outbound `-`; the feed is the witness's row.
4. **The native node has no name of its own.** The 915 operator has no policy
   verb and `books/native-config.lisp` has no path-identity key, so RFC 5537
   3.5 loop suppression cannot fire: `V0-TRANSIT-LOOP-{AB,BA}` draw 235 and
   `-ABSENT` serve the looped article. This is the K2 gap of the v0.2
   checklist on the native path, now measured rather than inferred.

## What the slice still does not reach, and why

`not-built` on this image: init/reinit (no operator verb), uncertain outcome
(no public fault injection), `peer list`, and `principal new` (the local
principal id is derived inside `set-password`, so no verb derives one from a
seed). `not-exercised` by the slice: crash, BP, statements, media, scale, INN
and slrn.

What the 03:08Z run changed is where the remaining F-AUTH, live-configuration
and loopback gaps live. They are no longer the harness declining to look:

- The two credential rows and the wildcard-listener row now carry this
  image's own exit code 5 (`operator principal UNSUPPORTED-COMMAND`, and
  `operator request (CONFIGURATION INVALID)`), and the six AUTHINFO session
  rows name the enrolment that did not happen. A usage error is not an
  outcome, so none of them reads as a refusal.
- `V0-CFG-LIVE` disagrees rather than being not-built: `group create` against
  the live node's own configuration exits 1 with `store is already locked`
  and `GROUP fn.matrix.live` then answers 411, so this image does not
  dispatch live administration. `V0-CFG-LIVE-REFUSE` keeps its property on a
  second configuration over the same store whose control path is unbound,
  which is the executor that can still show it once an image does dispatch.
- `V0-CLIENT-NNTPLIB-{A,B}` are accepted and are the first two `independent`
  rows the native slice has had: stdlib nntplib 3.12.13 drove CAPABILITIES,
  GROUP, STAT, ARTICLE, HEAD, BODY, OVER, LIST and an absent lookup on both
  listeners.
- `V0-CAP-REFUSE-{A,B}` are refused, where the 01:43Z run could not start the
  scratch owner at all.
- **The second submission of one Message-ID is nondeterministic.** At 03:08Z
  node A exited 1 with `refused operator post REFUSED` and node B exited 0
  with `accepted operator post DUPLICATE`; at 03:21Z, over freshly
  reprovisioned stores, the two swapped. The two runs are identical in every
  other row and count. So it is not a node difference: the same operation on
  the same image answers refused or accepted by race, and D13's three
  outcomes do not stay distinct on the native `post` path. `V0-OUT-REFUSED`
  is the row; the owner is the submission path, not this harness.

The 915 image is 210 commits behind `dev`; `principal`, `policy set
path-identity`, STARTTLS and live administration exist there and need their
own image before those rows can move.
