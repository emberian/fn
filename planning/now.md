# Now — 2026-09-27

The one page a new agent reads first: where dev is, what is being worked on,
and where the rest is. Written by lane docs-sync from dev `33bbfae9c` (batch
AW, round 18) at about 16:30 UTC. The log that lived here before is
[archive/now-2026-09-26.md](archive/now-2026-09-26.md).

## Coordinates

AGENTS.md keeps four coordinates apart; none implies another.

- **Source.** dev as above. [The current view](current.md) (generated) gives
  each capability's host line, keystone and certificate at this revision.
- **Proof.** Each capability's certificate is named in the current view;
  merged lanes' manifests are under
  [`evidence/manifests/`](evidence/manifests/), cited in each batch's
  "cite round" commit.
- **Qualified image.** The newest qualification record is
  [qual-69046a76](evidence/qual-69046a76-2026-09-26.md) (2026-09-26), from
  before the record log. No image of the one store format, 9, is qualified
  yet. Batch AW builds a native image per round and runs the affected
  modules on it; those are lane evidence, not a qualification.
- **Deployment.** hbox `/tank/fn/node` runs `bbf52159` with a format-8
  store ([node record](evidence/node-hbox-bbf52159-2026-09-25.md)). dev
  refuses that store by name (below), so the next deployment is a fresh
  install and an import (D34). There is no release for friends yet:
  [release-v6.7.0](release-v6.7.0.md) is NOT CUT until its fundamentals are
  met.

## What changed on 2026-09-27

About sixty lanes landed through batches AQ to AW. Each has a record
under [`evidence/`](evidence/) named `*-2026-09-27.md`. What an operator or a
reader sees:

- **One store format, 9: the record log.** A store commits through
  chained segment files `journal/NNNNNN.log`
  ([commit-onto-log](evidence/commit-onto-log-2026-09-27.md),
  [log-2](evidence/log-2-2026-09-27.md)). A format-8 store is refused at the
  open, `open refused reason=store-format`; a profile of another field
  width is refused `older-release` / `newer-release`
  ([fixtures-refresh](evidence/fixtures-refresh-2026-09-27.md)). A format-8
  history moves by `store export` on the release that made it and
  `store import` here ([log-recovery](evidence/log-recovery-2026-09-27.md)).
- **Compaction and reclaim over the log.** `store compact` is a checkpoint
  with the log rotated, then the covered segments dropped; the owner's
  automatic checkpoint does the same; `store reclaim` works over the log.
  A 40,000-article compact went from 2,963 s and 16.4 GB to 40-139 s and
  4.7 GB (log-recovery). The open streams one log entry at a time: a
  10,000 x 32 KiB open from 4:38 and 14.1 GB RSS to 55 s and 1.25 GB
  ([log-open-stream](evidence/log-open-stream-2026-09-27.md)).
- **Commit cost.** fsyncs per POST at 8 posters from 7.0 to 0.27-0.58
  (commit-onto-log). Control `status` p50 from 10,320 to 554 ms under the
  mixed load ([control-quanta](evidence/control-quanta-2026-09-27.md)).
- **Memory.** The launcher's heap for an empty small store from 824 to 586
  MB, 88.3 MiB RSS after 1,000 posts
  ([reservation-after-flip](evidence/reservation-after-flip-2026-09-27.md));
  a 40,000 x 2 KiB checkpoint open in 13.6 s at 579 MB live
  ([checkpoint-arena-3](evidence/checkpoint-arena-3-2026-09-27.md)). A
  capacity-free `init` takes the largest of 64, 32 or 16 MiB of history the
  machine holds, else 8 MiB ([friend-blockers](evidence/friend-blockers-2026-09-27.md)).
- **Friends' path.** The systemd unit starts under `ProtectSystem=strict`;
  `fn redeem` redeems an invitation without openssl; a mission's `init`
  serves `control.cancel`; a full store answers a peer 436
  (friend-blockers, [stranger-rehearsal](evidence/stranger-rehearsal-2026-09-27.md)).
  Consumers: `--json`, reasons on the wire, withdrawal events
  ([friend-blockers-2](evidence/friend-blockers-2-2026-09-27.md)).
- **Readers and moderation.** Xref leads the header of ARTICLE and HEAD
  ([reader-compat](evidence/reader-compat-2026-09-27.md), batch AR);
  `moderation approve/reject` and `article withdraw`
  ([moderation-verbs](evidence/moderation-verbs-2026-09-27.md)); peers by
  name, refused-offer memory, relay date and Path checks.
- **Served reads.** ACL2 decides the read size per step: 512 octets under a
  step rate, 4 KiB without ([input-loop-2](evidence/input-loop-2-2026-09-27.md)).
- **Proof tooling.** `proof_repl.py` gained `send-range`, `forms`, `probe`,
  `--host`, `--certify-missing`/`--source-deps` and a 20-minute idle stop;
  `proof_cost` ratchets on prover steps, and D26's seconds are the fastest
  quiet 2-job measurement ([decisions](decisions.md) D26,
  [how we work](how-we-work.md)).

## Open, as of this page

- **The release's fundamentals** F1 to F8 ([release-v6.7.0](release-v6.7.0.md)
  section 2): each is OPEN there until one image carries its evidence; lane
  fundamentals-scoreboard is gathering it.
- **No qualified format-9 image** (above), and the live node cannot be
  upgraded in place.
- **M5's drop theorem** is stated over a fold the streamed open no longer
  calls; the equation is owed ([current view](current.md#m5)).
- **`health` prints `format=8`** for every valid profile, including format 9
  (books/native-health.lisp `fn-nh-profile-words` hard-codes it).
- **Consumers' withdrawal events** are proved and the view is refreshed
  (flip-L8-2), but no native case observes one at a consumer yet.

## Lanes

Lanes run on Claude Opus 5.5 in `build/lanes/<name>` on `lane/<name>`; the
coordinator merges them in batches and names each lane's model in its
brief. Its running log is `build/coordinator/WAVE-STATE.md` (newest on top,
not tracked). How lanes work: [how we work](how-we-work.md).

## Where to read next

[The current view](current.md), [decisions](decisions.md),
[requirements](requirements.json), [proofs](proofs.json),
[the release checklist](release-v6.7.0.md), and the docs index
[docs/README.md](../docs/README.md).
