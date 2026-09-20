# Handoff: w5/config-groups (packets R3 model, R4 store host)

Lane `w5/config-groups`, branched at `b7f106b` (dev). Deliverable: the node
carries its configuration; groups come from configuration records; `group
create`/`retire` are CLI commands. Landed scope and every walk-back are in
[`specs/reconfiguration.md`](../../specs/reconfiguration.md) section 8; the
board carries the CHANGE lines and the owner proposal.

## The one design decision, and why it is forced

The design (section 1.6) puts the served table into `fn-state-groups`. It
cannot go there: `fn-nexts-for-p groups nexts` keys the watermarks on exactly
that list, in order, and `fn-articlep configured x` requires every article's
groups inside it. A retired name that left the list would lose its watermark
and unbind its articles -- the opposite of NNT-006 and of the keystone this
lane owed ("a group retired at generation g keeps its watermark and every
article already bound"). So [`books/node-config.lisp`](../../books/node-config.lisp)
carries two tables with one equality each:

- `fn-state-groups` of the acceptance state **is** the allocation domain,
  `fn-cfg-group-all-names` of the configuration: every name ever created,
  retired or not. Creation only appends (or revives in place), so a code --
  a position in this list -- is stable across retirement and revival.
- the served table is `fn-cfg-group-names` at the generation, a subset of the
  domain, and admission checks it in `fn-cnode-selection-servedp`, which
  `fn-cnode-prepare` and the store host (`fn-store-sn-prepare`) both call.
- the retention capacity **is** the configured capacity.

`books/acceptance`, `books/node`, `books/replay` and `books/config*` are
untouched: every theorem of theirs still holds of the node inside, and each
configured transition lifts a node transition and re-establishes the
equalities. The retirement transition rebuilds the acceptance state with the
new domain and `fn-cnode-extend-nexts` (every existing name keeps its exact
watermark, a new name starts at 1); the preservation proof is
`fn-cnode-apply-config-preserves-state`, and it needed the reservation total
to stay inside the capacity through the whole delta list
(`fn-cnode-apply-capacity`, local) and the domain to grow monotonically
(`fn-cnode-apply-grows-all-names`, local).

Two hypotheses were deleted as unnecessary rather than given teeth
(docs/proof-style.md section 5): `fn-cnode-apply-config-keeps-watermarks-and-
articles` has none, because a refused or non-state application returns the
node itself and the conclusions hold of it trivially -- the theorem is the
structural fact that retirement never deletes; and
`fn-cnode-prepare-stages-only-served-groups` keeps only "prepare staged".

## Which replay the store uses

Neither `fn-replay` nor `fn-config-aware-loop` changed; both keep their
keystone statements. The host replays configuration history through
`fn-cnode-config-replay` (a config-only `fn-cnode-replay-loop`) and article
history through `fn-sn-open-observed` (still `fn-replay`) into a node whose
domain and capacity come from the configured node. `fn-cnode-replay-loop` has
both arms and is what the keystones are about; the article arm is exercised
by the test book, not by the host, until the store cluster interleaves the two
kinds on disk. That interleaving is the reason `set-capacity` is not offered:
a decrease admitted against the reservation total live at its time cannot be
re-checked by a config-only replay.

## Host and CLI

- Store layout: `config/00000001.cfg` (generation 1, from `init --group`),
  `config/00000002.cfg` ... one record per generation; `config-record` is gone
  (no deployed store; re-init).
- `run_store.py init [--group NAME]...` (default the two experimental groups);
  `group create NAME` / `group retire NAME` (admitted by
  `fn-store-cfg-reconfigure` = `fn-cnode-record-acceptablep` against the live
  node, `fn-cnode-line-ceiling`, idle node; refused 1, uncertain 3, accepted
  0); `config` prints generation, served table, domain.
- `group_codes(groups, store, bridge)`: codes over the domain ACL2 handed the
  store at recover, computed by `fn-store-group-codes`; Python carries the
  list back and never indexes it.
- The reader prints `LISTENING <port> generation=<g>`: the generation it
  pinned at open. It holds the shared lock, so a reconfiguration while it is
  open is refused at the lock (`test_reader_pins_the_generation_it_opened_at`).
  Two connections across a reconfiguration need the owner's pins (proposal on
  the board).
- `tools/run_owner.py` and `host/owner-host.lisp` were not edited (sibling
  lane); the board CHANGE names the three lines `owner-host.lisp` needs.

## Certification and tests

Certified one root at a time on this laptop (ACL2 8.7), evidence under
`build/acl2/` of this worktree: `books/node-config`
(`certify-20260920T012826Z-30058`), `books/store-config`
(`certify-20260920T014451Z-95396`), `tests/acl2/config-tests`
(`certify-20260920T015339Z-13977`). `books/config`, `config-invariants`,
`config-records`, `acceptance`, `node`, `replay` and `nntp-syntax` are
unchanged and keep their certificates. `python3 tools/ledger.py --write` and
`make check` pass (structural checks only).

Python, run after every edit above: `tests.test_store_config` (4 tests, OK:
init from arguments incl. a nine-group store, create/retire/revive with
numbering resumed across recovery, duplicate/unknown/overflow refused with
the reason on stderr, the reader's pinned generation) and
`tests.test_store tests.test_store_lifecycle tests.test_store_corruption
tests.test_reader` (38 tests, OK). One pre-existing defect fixed on the way:
`tests/test_store.py`'s `SimpleNamespace` lacked the `owner` attribute the
CLI parser always sets since the w4/post merge (`args.owner` in
`command_post`), so `test_published_post_with_failed_core_reply_stays_fenced_
and_recovers` errored at `dev`; it now carries `owner=None`.

Two statements were corrected rather than weakened while certifying:
`fn-store-codes-from-groups-inverts` needs `(not (member-equal nil names))`
over a table parameter (a NIL name's code round-trips to "unknown"; the
compiled table hid it; tooth in `config-tests`), and the plain-replay
separating witness had to number its records from 0.

For the gate: `host/owner-host.lisp` (sibling lane's file, not edited) still
names `*fn-store-groups*` and the one-argument `fn-store-groups-from-codes`;
the three-line edit is on the board, and `tests/test_owner*.py` were not
run here. `planning/proofs.json` rows for the R3 keystones are not cited yet
(the ledger wrote no new event arrays); the row owner cites
`fn-cnode-apply-config-keeps-watermarks-and-articles`,
`fn-cnode-prepare-stages-only-served-groups`,
`fn-cnode-replay-loop-splits-at-any-prefix` and
`fn-cnode-recovered-generation-is-at-most-the-live-generation`.

## Open, recorded rather than weakened

See section 8 of the spec: interleaved two-kind journal (store cluster), the
owner event and per-connection pin (owner lane), `LIST ACTIVE` over the domain
until R5's per-generation projection, `fn-initial-state`'s signature (core
cluster, whole-tree blast radius; the compatibility statement is the ground
equality `fn-cnode-initial-of-the-default-record-is-fn-initial-state-of-its-
groups`), `*fn-store-capacity*` in `fn-store-sn-reset` only, and the
`true-listp` hypothesis of the recovered-generation keystone.
