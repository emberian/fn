# Handoff: w9/runtime (call-site breakage from the hbox gate of dev d50c392)

Branch `w9/runtime`, worktree `build/lanes/w9-runtime`, branched at `34f5a95`.
This lane fixed **call sites**, not semantics: no model function, no host
signature and no theorem changed. Two merged lanes had tightened a host
signature and left callers behind, and three gate tests could not start in a
`git archive` tree.

## What the gate found, and what it is now

| Class | Gate (dev d50c392) | Now |
| --- | --- | --- |
| `receive_bpa_request() missing … 'bundle'` | 16 | 0 |
| `ingest_bpa_adu() missing … 'bundle'` (same lane, same cause) | 4 | 0 |
| `SystemExit: 5` from argparse (the CLI's own `--bundle`) | 4 | 0 |
| `'dict' object has no attribute 'config'` | 11 | 0 (already fixed on dev by `1c5864a`; confirmed by running the module) |
| `git rev-parse HEAD` in a `git archive` tree | 6 `setUpClass` | 0 |

## The bundle argument (w2/bundle-identity)

`run_bp_receive.receive_bpa_request` and `run_bp_ingress.ingest_bpa_adu` take
a keyword-only `bundle: Callable[[str], bytes]` because ACL2 settles the
carried identity and the expiry decision from the bundle's own primary block
(`fn-bpi-host-bundle-report`). A caller that cannot supply the octets cannot
be fixed by defaulting them: defaulting would put the identity decision back
in the host. Every caller below now hands over the octets its transport
actually holds.

- **`tools/media.py` — a carried volume now carries the bundle octets.** This
  is the one real change of this lane. `MediaItem` gained `bundle_file`,
  `bundle_octets` and `bundle_sha256`; `export_media` takes
  `(identity, ADU, bundle)` triples and writes both files under `bundles/`;
  `read_manifest` validates both; `MediaVolume.present` requires both whole;
  and `MediaVolume.bundle` is the copy-checked callback the receiver takes
  (`MediaIncomplete` / `MediaCorrupt`, refused before anything is staged, as
  for the ADU). The export CLI keeps `--bundle ID=PATH` for the projected
  request ADU and gains `--bp-bundle ID=PATH` for the bundle octets; a volume
  whose two sets of identities disagree is `EXIT_USAGE`. Manifest schema
  stays `1` and **old volumes no longer read** — they are laboratory volumes,
  and a volume without bundle octets is one whose importer would have to
  decide identity locally.
- **`tests/campaign/`** — `child.bundle_path(root, bid)` is where a case keeps
  the octets; `Campaign.build_bundles` writes one per carried BID into the
  template, so the parent's `receive()` and the killed child's `_receive()`
  read the same file. Distinct creation sequences per BID, so "the same ADU
  under a fresh BID is a duplicate" is still a second real bundle.
- **`tests/test_bp_receive_process_crash.py`** — the child takes `--bundle`;
  the parent builds both BIDs' bundles in one ACL2 session (`lab_bundles`).
- **`tests/test_bp_ingress_host.py`** — `stage()` registers a bundle beside the
  ADU.
- **`tests/test_host_boundary.py`** — the two BID-boundary refusals pass a
  `bundle` that is never called (they refuse on the BID first), and the two
  `run_bp_ingress.main` argument lists gained the `--bundle` that argparse was
  rejecting with exit 5.

## The git fallback (three gate tests)

`tests/test_deploy_gate.py`'s fallback was copied into `test_inn_lab.py`,
`test_scale_gate.py` and `test_twonode_gate.py` — **and it is not enough for
these three**. Unlike the deploy gate, which needs only a revision string,
these harnesses go on to `git archive <rev>` the tree, which fails the same
way one line later. They now raise `unittest.SkipTest` when `rev-parse` fails,
naming the reason: a gate that exports the tree cannot run from an export.
In a real checkout the original path is unchanged.

## Not touched: cascade from served

The gate's two largest classes are a served-book admission failure another
lane owns, and nothing here addresses them. Listed so they are not re-found:

- **"reader did not listen" (18)** — `test_nntp_wire.py`, `test_reader_*`,
  `test_nntp_reader_*` cases, plus `test_reader_pins_the_generation_it_opened_at`.
- **"owner did not start" (9)** — `test_owner_*` / `test_post_*` cases.

## Still open

- **`tests/bp-dtn7/run_four_node_lab.py:receive()` has no `bundle=`, and
  `tests/bp-dtn7/mock_bpa.py` carries no bundle octets.** The mock BPA spools
  an ADU and a JSON document, never a BPv7 bundle, so there is nothing for it
  to return; giving it one means the lab's submit path encodes a primary block
  through ACL2. That is a lab-fidelity change, not a call-site fix, and it is
  left for the lane that owns the four-node lab. `test_four_node_lab` also
  reaches `git rev-parse` at `run_four_node_lab.py:405` for its evidence
  record; that one is provenance and must not be given a fake revision.
- `tests/ltp/run_fn_ltp_lab.py` and `tests/bp-dtn7/run_fn_exchange_lab.py`
  already pass `bundle=` and were not exercised here.
