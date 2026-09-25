# Bounds blob: per-schema frame blob widths; the control socket follows A (2026-09-25)

Lane `lane/bounds-blob` (D27; backlog packets PKT-008 to PKT-011), from dev
`595d3a47`. PRF-091. Book commits `f5d0c571` and `d9203155` (the image rev).

## 1. What changed

- **Frame field grammar** (books/frame-fields). A spec form `(:blob . W)`,
  1 <= W <= 2^32-1, beside `:blob`. `:blob` keeps its 131 072 width and every
  statement about it; it is now named as the width of the node's own fields
  (identities, labels, signatures, chunks). The new form has its own branch in
  `fn-frame-specp`, `-field-okp`, `-field-octets` and `-field-parse`, and the
  value predicate `fn-frame-blob-withinp`. A value within both widths encodes
  to the same octets under either form (frame-tests).
- **Schema widths.** `fn-frame-field-width` and `fn-frame-specs-width`: a
  schema's payload bound is the sum of its field widths, replacing
  frame-journal's field count times one blob cap.
- **FNCT** (books/native-control). The article field is
  `(:blob . *fn-record-max-payload*)` and the group-list field
  `(:blob . *fn-nctrl-max-groups-octets*)` (17 104 640: a five-octet count,
  65 535 names at 256 octets with five-octet heads). `*fn-nctrl-max-payload*`
  is the spec's width, 4 278 518 026, within the u32 frame: a codec width, not
  a read bound. New: `fn-nctrl-max-frame-for A G`, the request frame at the
  profile's bounds, and `fn-nctrl-read-bound-for A G`, its maximum with
  `*fn-nctrl-max-command-frame*` (262 708, a work bound: the read bound of a
  frame with no article, the pre-D27 request frame).
- **Hybrid control** (books/native-hybrid-control). Each field's width is the
  value it carries (keys 32/32/1 952, v1 source 65 535, signatures 64/3 309,
  principal 32), and `*fn-nhctrl-max-payload*` is the widest spec's width,
  69 438, derived. Before, a fixed 65 536 refused a v1 source above about
  62 000 octets. `fn-nhctrl-read-bound-for A G` covers both kinds.
- **Host.** The owner reads a control connection under
  `fn-nctrl-read-bound-for` (or its hybrid twin) of the carried profile's A and
  G. The bound is computed once in `fnn-control-start` through
  `fn-owner-control-profile-bounds` (host/owner-host.lisp) and kept in the
  control state. Before D27, `fnn-control-handle-client` used the hybrid frame
  (65 578) instead of the FNCT frame whenever hybrid control was built in,
  which capped `operator post` at about 65 000 octets. The client reads the
  article file up to the FNCT article width (`fn-native-control-host-max-article`
  is now `*fn-record-max-payload*`): it does not know the store's profile, and
  the owner applies A. A client reads a reply under the command frame.

## 2. Theorems (PRF-091)

- **KEYSTONE `fn-native-control-request-within-profile-frame`**
  (books/native-control):
  `(implies (and (natp a) (natp g) (<= (len article) a) (<= (len groups) g))
  (<= (len (fn-native-control-request-encode msgid groups article))
  (fn-nctrl-max-frame-for a g)))`. The subject is the encoder the client calls
  (`fn-native-control-host-request-encode`, host/native/control.lisp
  `fnn-control-submit`).
- `fn-native-control-request-within-read-bound`: the same under
  `fn-nctrl-read-bound-for`, the bound `fnn-control-handle-client` reads under.
- `fn-nhctrl-read-bound-covers-both`: the hybrid read bound is at least the
  FNCT bound and the hybrid frame.
- `fn-nctrl-groups-encode-length-bound`: a group list encodes to at most
  5 + 261 per name.
- `fn-frame-fields-octets-within-width` (books/frame-fields): a record whose
  values satisfy SPECS encodes to at most `(fn-frame-specs-width SPECS)`. It is
  now the bound in the journal encoders' guards (books/frame-journal), with
  `fn-frame-spec-for-within-table-width`.
- `fn-frame-field-parse-of-octets-wide-blob` (books/frame-invariants): the
  round trip of the new form. It enters `fn-frame-field-parse-of-octets`, so
  the existing record round trips cover it without restatement.
- `fn-frame-workflow-table-within-its-payload` and
  `fn-frame-receipt-table-within-its-payload`: each journal payload cap is at
  least its table's width.

No existing theorem statement moved.

## 3. Teeth

- tests/acl2/native-control-tests.lisp:
  - a 131 073-octet article is a request value and round-trips through the
    request grammar; under the pre-D27 `(:blob :text :blob)` it is not;
  - the witness: the test request at A equal to its article length and G = 2
    encodes within the bound, less than 1 100 octets below it;
  - one evaluated counterexample per hypothesis (each request meets every other
    hypothesis, and its encoding exceeds the bound):
    - `(<= (len article) a)`: a 2 000-octet article at A = 0;
    - `(<= (len groups) g)`: forty groups at G = 0;
    - `(natp a)`: A = 4001/2 admits the 2 000-octet article and reads as 0;
    - `(natp g)`: G = 81/2 admits forty groups and reads as 0;
  - the read bound: the command floor at A = 32 768, and above the floor at
    A = 300 000.
- tests/acl2/frame-tests.lisp: the new form's recognizer, parse and round trip
  of a 131 073-octet value, and a refusal one past W. A `:blob` refuses the
  value. Schema widths, and the table widths within the journal caps.
- tests/acl2/native-hybrid-control-tests.lisp: a 65 535-octet v1 source
  round-trips (refused before); 65 536 is `:bad`.
- tests/acl2/native-control-host-tests.lisp: the host's article width, command
  frame and read bound.

## 4. Certification

| Run | Box, toolchain | Rev | Scope | Result | Manifest |
| --- | --- | --- | --- | --- | --- |
| run-20260925T085910Z-22ae | persvati, w25, 2 jobs, 300 s | f5d0c571 | `--affected-by` the frame books, native-control, native-hybrid-control, transfer-journal, the two host control books, owner-host, the four test books (537 roots, 548 certified) | 538 passed, 10 failed: native-control (the keystone lacked the Message-ID text bound) and its nine dependents | `certify-20260925T085948Z-2943385.json` |
| run-20260925T093314Z-2f56 | persvati, w25, 2 jobs, 300 s | d9203155 | the same set (533 roots): 524 installed at these bytes, 10 certified | exit 0, 10 of 10 passed | `certify-20260925T093356Z-3302564.json` |
| run-20260925T093714Z-e8e4 | hbox, w28 `acl2-literal-4g`, 2 jobs, 300 s | d9203155 | the default and dtn image roots (136) | exit 0, 198 of 198 passed | `certify-20260925T093812Z-3053804.json` |

The fix to native-control was proved in a persvati REPL over run 22ae's
certificates before run 2f56.

Per book at 2 jobs, persvati:

- frame-fields 3.2 s, frame-invariants 2.6 s, frame-journal 1.0 s,
  frame 4.1 s, frame-tests 0.8 s;
- transfer-journal 1.0 s, transfer-journal-invariants 2.6 s;
- native-control 2.5 s, native-control-tests 2.6 s;
- native-hybrid-control 2.9 s, native-hybrid-control-tests 2.5 s;
- native-control-host 2.8 s, native-control-host-tests 3.1 s.

**Over 10 s (run 22ae).** Eleven books:

- byte-store-record-provenance-owner 12.7, consumer-store-invariants 12.5,
  owner-invariants 12.5, byte-store-k0-step-lemmas 11.6, store-node-invariants
  11.5, topic-history-store-invariants 11.2, native-admin-peer 11.1,
  checkpoint-codec 11.0, config-owner-live 10.5, bp-node-fragment-guards 10.4,
  byte-store-k0-staging 10.2.

None opens the frame grammar: no `fn-frame-field-okp`, `-values-okp` or
`fn-frame-codec-vocabulary` appears in any of the seven not already listed
over 10 s. Their times rose by about 30% together against run
certify-20260925T073426Z (for example 9.1 to 12.7 and 8.3 to 11.6), and
persvati's load average was 6 to 7 through the run. They are recorded as
load, not as this lane's regression. owner-invariants,
store-node-invariants, config-owner-live and native-admin-peer were already
over 10 s.

## 5. Native (hbox)

- Images from `d9203155`, built by tools/runbooks/hbox-image-build.sh in
  /tank/fn/gates/bounds-blob-r3:
  - fn-host.core `3420d1bc…`
  - fn-host-developer.core `d9a483a6…`
  - fn-host-dtn.core `8fffb85f…`
  - fn-host-dtn-developer.core `5683ce79…`
  - the image's hash list is `image-d9203155.sha256`.
- The before image is `0e2173ab` (spike-mission, after the bounds join),
  fn-host.core `7266a43b…`.
- Every test ran under `systemd-run --user --scope -p MemoryMax=24G`, with
  TMPDIR=/tank/fn/scratch/bounds-blob.

`tests.test_native_bounds_blob` uses a profile with `--max-article-octets
300000`. That A is above the 262 708-octet command frame, so the owner's
read bound comes from A. The operator posts over the control socket:

| Octets | after (d9203155) | before (0e2173ab) |
| --- | --- | --- |
| 131 073 | accepted, exit 0, re-read with its body as suffix | exit 4, `fault operator post store file exceeds bound` (the client's 131 072 read) |
| 290 000 | accepted, exit 0, re-read with its body as suffix | exit 4, the same fault |
| 300 001 | exit 1, `refused operator post ARTICLE-EXCEEDS-PROFILE-BOUND` | exit 4, the same fault |

A submission of exactly 300 000 octets is also refused by name. A bounds
the injected article, and the owner adds Path, Injection-Date and
Injection-Info (first run of this test, before the 290 000 row).

Regression on the new image (`native-regress.log`):

- The suites were tests.test_native_control, test_native_profile_upgrade,
  test_native_bounds_join.LargeArticleTests, test_native_owner and
  test_native_operator_verbs: 66 run, 6 failed, 4 skipped.
- The same six fail on the before image over the same tree
  (`native-regress-old-image.log`), so this lane did not cause them:
  - two raw-stub harness runs stop reading host/native/io.lisp
    (`SOCKOPT-ERROR` not in SB-BSD-SOCKETS);
  - two owner runs stop on the same symbol;
  - `test_peer_list_is_a_query...` pins a defun that moved to
    native-admin-peer;
  - `test_article_over_the_body_limit...` expects the bounds join's oversize
    wording and gets `441 ... the article was refused`.
- Because of the harness failure, the raw-stub run did not exercise this
  lane's stub change (tests/native_developer_selectors_raw.lisp,
  `fnn-control-state-read-maximum`).

| Log (planning/evidence/bounds-blob-2026-09-25/) | sha256 |
| --- | --- |
| native-after.log | `c5cf1174…` |
| native-before.log | `9cd99fa6…` |
| native-regress.log | `9d7cb5f9…` |
| native-regress-old-image.log | `6b4ee2ca…` |
| image-d9203155.sha256 | `59d0ee00…` |

## 6. Not done, and why

- **PKT-011 (the pre-reservation figures): blocked by a cited theorem.**
  - Deriving `fn-sbud-verdict-at`'s history figure from the profile makes
    it grow with the profile: the article figure becomes
    `fn-record-encoded-octets-ceiling A G`, and kind 4 becomes R.
  - Kind 4 at R is sound, because the signed path checks the actual
    composite against R before commit (`fn-sbud-signed-event-boundary`).
    A figure from A and G alone is not proved for the composite: the
    authored source is u32-wide.
  - `fn-profile-upgrade-keeps-verdict` (PRF-072's statement: "whatever the
    old profile admitted, the new profile admits") is then false. Raising A
    without raising H makes the history gate stricter.
  - Keeping it needs one of two changes, and ember or the deputy should
    choose:
    - a hypothesis on the theorem (H grows by at least the figure's
      growth); or
    - a new relation in `fn-profile-upgradep` that refuses such an upgrade.
      This changes the deploy procedure of bounds-join §5, where A rises to
      4 MiB with H unchanged.
  - The existing statements do not move, so this was not done.
- **PKT-010, the remainder: data caps, open.**
  - FNRJ's request-context blobs are `:blob` at 131 072 and carry the
    request ADU and the Store record of an application ingress. An
    application article whose record exceeds 131 072 cannot be journalled.
    tools/receipt_journal.py mirrors the width (`MAX_BLOB`).
  - Two u32 fields cannot both fit a u32 frame. The fix is a receipt spec
    parameterised by the profile's R, carried into the FNRJ codec, the
    Python bridge and host/native/workflow.lisp.
  - app-journal's `*fn-aj-max-records*` (4 096) and the two aggregates
    (16 MiB, 64 MiB) bound the number and total size of application journal
    records over a store's life. They are data caps too. The fix is to
    derive them from T and H in `fn-aj-statep`, carried by the host.
  - Neither is classified as a work bound, because neither is one.
- **Done in PKT-010:**
  - `*fn-tj-max-payload*` is now the chunk spec's width. It is a work bound
    on one chunk record: an object is many chunks.
  - `*fn-frame-max-workflow-payload*` is a codec width over node-built
    fields, proved at least its table's width.
- **Found:** `*fn-bpn-machine-max-job-octets*` = `*fn-frame-max-blob*`
  (books/bp-node-machine.lisp, `bp-limits`) caps the BP held bundle image at
  131 072. This is the BP lanes' data cap, and it now has a way out:
  `(:blob . W)`.
- **Representation.** The client and owner still build the request as an
  ACL2 octet list, and `fn-frame-decode`'s cons walk runs over it. For an
  article of several MiB this is D27's concrete-representation work, the
  same as the owner's take recursion in bounds-join §2. The native run
  stops at 290 000 octets for that reason.
- **Overbound frames.** A request frame past the owner's read bound is read
  as `:overbound` and answered `refused`. A client still writing may see a
  closed connection and report uncertain (exit 3). An article more than
  about 17 MB past A reaches this path. Below that, the read succeeds and
  the injection refuses it by name.
- `make check` in this worktree: the one error left is `planning/ledger.*`
  stale. The deputy regenerates the ledger on merge.
