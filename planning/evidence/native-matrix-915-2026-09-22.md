# The full v0 matrix against the native 915 image — 2026-09-22

Five runs of `tools/v0_matrix.py --backend native-operator` from `dev`
(`2202a95f`, then `783db508`) against the immutable `915d5c72` production
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
(no public fault injection), `peer list`, live group declaration (the control
socket is ACL2-framed), path identity. `not-exercised` by the slice: the
loopback refusal, capacity refusal (needs an owner over the scratch store),
AUTH (the 915 image predates `principal`), crash, BP, statements, media,
scale, INN, independent clients. The 915 image is 210 commits behind `dev`;
`principal`, STARTTLS and live administration exist there and need their own
image before their rows can move.
