# w2/bundle-identity

HEAD at branch point: `9321344` (dev). Worktree
`/Users/ember/dev/fn/build/lanes/w2-bundle-identity`.

## What the packet asked, and what moved

**Bundle identity, not the dtn7-rs BID, is now the key the host stages and
deduplicates on.** The BID is retained as the transport handle for `/download?`
and `/delete?` and nothing else.

### Moved into ACL2 (it was nowhere before, not in Python)

| Decision | Where it now lives |
| --- | --- |
| the canonical primary-block identity and its octets | `fn-bpp-primary-identity-value`, `fn-bpp-primary-identity` in `books/bp-primary.lisp`, guard-verified |
| the bundle frame split (RFC 9171 §4.1 head, one CBOR item, exact octets to `fn-bpp-decode`) | `fn-bpi-host-primary-octets`, `fn-bpi-host-bundle-block` in `host/bp-ingress-host.lisp` |
| milliseconds, the DTN epoch, and the `fn-clock-observationp` | `fn-bpi-host-observation`; Python hands over raw `time.monotonic_ns()`/`time.time_ns()` and one configured error bound |
| identity + expiry in one answer | `fn-bpi-host-bundle-report` |
| the identity field in the FNBI frame | `books/frame.lisp`: `fn-frame-inbound-prefix`/`-open` carry a `:blob` identity field beside the BID text field, capped by `*fn-frame-max-identity*` (1152) |

### New theorems and teeth

- `books/bp-primary-invariants.lisp`: `fn-bpp-primary-identity-value-is-shape`,
  `fn-bpp-primary-identity-is-octets` (the keystone the staging path needs --
  without it the identity cannot be hashed or framed),
  `fn-bpp-primary-identity-ignores-destination-lifetime-and-crc-type-by-definition`
  (named `-by-definition`; it is a projection fact, not a proof event), and
  `fn-bpp-primary-identity-determines-adu-key` (`:rule-classes nil`).
- `books/frame-invariants.lisp`: `fn-frame-inbound-open-of-prefix` restated and
  reproved over **both** fields, with an arbitrary tail.
- `tests/acl2/bp-primary-tests.lisp`: eleven `assert-event` witnesses --
  separation by source, by creation time, by sequence, whole-bundle versus
  fragment, fragment versus fragment, the routing/lifetime/CRC non-dependence,
  the canonical round trip, and the *limit* of the projection stated as a fact
  rather than as prose.
- `tests/acl2/frame-tests.lisp`: the inbound vectors carry the identity field,
  and a frame with the BID field alone is refused `:field-length`.

### Python (counts from `git diff --stat`)

970 insertions, 182 deletions across 24 tracked files plus new
`tools/bundle_bridge.py` (156 lines). No Python spells a BP field, a DTN time,
an epoch offset or an identity; `bundle_bridge` marshals decimal octets, reads
a regex-checked form, and computes SHA-256 over an octet string it does not
interpret (A-CRYPTO, exactly as `frame_bridge` already does).

- `tools/workflow_journal.py`: `stage_inbound(bid, identity, ...)` names the
  inbox file `sha256(identity).hex + ".bp"`; `encode_inbound`/`decode_inbound`
  carry three values; `inbound_items` is `(bid, identity, path)`; recovery
  checks the file name against the *identity*. Reconciliation of an existing
  frame now compares identity and payload and **not** the BID, because a
  redelivery under a fresh handle is the same bundle.
- `tools/run_bp_ingress.py`, `tools/run_bp_receive.py`: `identify_bundle` runs
  before anything is written; a required `bundle` callable supplies the raw
  octets, distinct from `download`, which still supplies the ADU.

### Three outcomes, kept distinct

`refused-identity:<reason>` (`:not-a-bundle`, a codec reason, or `:anonymous`),
`refused-expired`, and `uncertain-expiry` all leave the bundle staged nowhere
and deleted nowhere. `run_bp_ingress.main` maps them to `EXIT_REFUSED`,
`EXIT_REFUSED` and `EXIT_UNCERTAIN`. `:uncertain` is an operator fence: it is
never a deletion and never an acceptance.

## The differential test, and its honest scope

`tests/test_bpa_dtn7.py::Dtn7IdentityDifferentialTests` parses the three
identity fields dtn7-rs spells into its own BID
(`<source EID>-<creation DTN time>-<sequence>`, plus `-<offset>` for a
fragment) and requires ACL2's decoded source EID, creation timestamp and
sequence number to equal them for every bundle in the inventory. A
disagreement fails the test.

**It ran against the mock BPA, not the pinned agent.** The lab needs a Cargo
build of the pinned dtn7-rs checkout (`tests/bp-dtn7/pin.json`), which was not
available in this lane, so the bundles were built by the ACL2 encoder and
served over the mock HTTP server. This is a real check of the BID-format
agreement and of the identity projection; it is **not** evidence that fn and
`bp7` 0.10.7 agree on a wire encoding either produced. Running it against the
live agent is the first open item.

## Findings

1. **The primary block does not determine a fragment's bundle identity, and
   the packet's identity is therefore coarser than RFC 9171 §4.3.1's.** The RFC
   identifies a fragment by *this bundle's* payload length; the primary block
   carries the *total ADU length*. Two fragments of one ADU at the same offset
   with different payload lengths share one identity here. This is recorded in
   the book comment, in `specs/bp-primary.md`, and as an `assert-event` that
   states the collision rather than hiding it. Whole bundles and fragments
   never collide (three-element versus five-element encoded array).
2. **Staging used to key on the BID, so a redelivery under a fresh handle was
   a second staged frame.** It is now one. The converse also changed: two
   bundles with identical payloads and different identities are two staged
   requests, which the old code could not express at all.
3. **The FNBI frame's BID is no longer part of what must agree on
   reconciliation.** Keeping the old whole-frame byte comparison would have
   fenced the journal on exactly the redelivery this packet exists to
   recognise.

## Proposals (not done here)

- Move `fn-bpi-host-primary-octets` into a book as a modeled bundle frame
  (RFC 9171 §4.1) with a round-trip theorem, so the split is a certified
  decision rather than a `:program`-mode host composition.
- Model the canonical block format (§4.3.2) and the payload block, which is
  what `fn-bpp-bundle-id` needs to become computable and what reassembly needs.
- Run the differential against the live pinned agent and record the evidence.
- Carry the decoded primary block, not only the identity, in the FNBI frame, so
  that a relay has the source node ID and creation timestamp as values.

## Certification status: NOT RUN. Do not read this lane as certified.

The lane's `make certify` baseline was started at 10:10 and killed by the root
coordinator at ~11:05 (laptop at load 98, nineteen ACL2 processes); it was
moved to a remote box, and the targeted follow-up run over this lane's own
roots was killed with it (exit 144). **No book in this lane has been certified
with these edits.** `make check` is green (scaffolding, ledger and
`planning/ledger.json`/`.md` regenerated); no Python suite has been run,
because every one of them opens an ACL2 bridge.

What the next session must run, one root at a time, after the baseline
certificates are installed:

```sh
FN_ACL2_TIMEOUT_SECONDS=1800 python3 tools/certify_books.py books/frame
FN_ACL2_TIMEOUT_SECONDS=1800 python3 tools/certify_books.py books/frame-invariants
FN_ACL2_TIMEOUT_SECONDS=1800 python3 tools/certify_books.py tests/acl2/frame-tests
FN_ACL2_TIMEOUT_SECONDS=1800 python3 tools/certify_books.py books/bp-primary
FN_ACL2_TIMEOUT_SECONDS=1800 python3 tools/certify_books.py books/bp-primary-invariants
FN_ACL2_TIMEOUT_SECONDS=1800 python3 tools/certify_books.py tests/acl2/bp-primary-tests
python3 -m unittest tests.test_bpa_dtn7 tests.test_bp_receive \
        tests.test_bp_receive_faults tests.test_workflow_journal -v
```

The two roots most likely to need work are `books/frame-invariants`
(`fn-frame-inbound-open-of-prefix` is restated over two fields and an
arbitrary tail; the hint is the original `e/d`, which should let
`fn-frame-field-parse-of-octets-text` and `-blob` fire in sequence through
`fn-frame-parse-rest-of-parse-ok`) and `books/bp-primary-invariants`
(`fn-bpp-primary-identity-determines-adu-key`, which leans on
`fn-bpp-value-eid-of-eid-value` to invert the source endpoint). Note that
`identity` and `second` are ACL2 function names and were deliberately renamed
to `ident` and `blob` in the frame book; do not reintroduce them as formals.

Because nothing certified, the differential test result reported above is a
**design claim, not an observation**: the comparison is written and wired, and
it has not been executed.
