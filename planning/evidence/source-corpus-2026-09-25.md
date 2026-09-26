# Source corpus: one authored source, one identity, every route (2026-09-25)

Lane source-corpus, branch lane/source-corpus, base 483987b1. The Fable mandate
s5.3 and s5.4, s15 rows "Retry at a later injection time" and "Cancel order and
policy change". Ids: NNT-020, PRF-117, SCN-062, PKT-166.

## What now works, in one sentence

One authored article keeps one identity through the served POST, the operator
post, a signed carrier POSTed by a client, protected NNTP transit to a second
node and a SIGKILL reopen. The node shows the table
(`SOURCE-CORPUS-TABLE` in `tests/test_native_source_corpus.py`). Each
layer's equality is the one its contract means (specs/nntp.md NNT-020). The
exception is the signed control route: a retry through `hybrid-author` exits
1 with no word (PKT-166, below).

## The corpus

`tests/fixtures/source-corpus/*.article`, exact bytes:
- `supplied-date`, `generated-date`: supplied and generated Date;
- `client-path`: a valid client-supplied Path, `poster.example.invalid!not-for-mail`;
- `xref`: a supplied Xref (refused);
- `unknown-headers`: unknown fields, a lower-case name, a folded line;
- `mime`: multipart, 8-bit UTF-8, base64, and a body line opening with a dot;
- `signed`: the dual-signature source (Ed25519 and ML-DSA-65), signed at run time;
- `legacy`: an unsigned legacy post with a bare Path and no Date or Message-ID.
The injection-added Path prefix is observed, not supplied: A writes
`a.corpus.invalid!`, and B's relay adds `b.corpus.invalid!!` in front of it.

## The identity table (native, hbox)

Image: developer, built from e79286bf by `source-corpus-2026-09-25/build.sh`.
Launcher sha256 55e9964b766aeeae7af00c546c16a2b3389611a7abf9b3918a201a0bcf4b86e0,
core ba5c976500980b42397e37beadb3b89ae80c4aa56e7f82efe61af9b1acd331af. No later
commit on this lane touches an image input: only a test module, fixtures,
registries, a spec and this record changed. Runner: `source-corpus-2026-09-25/native.sh`,
under `systemd-run --user --scope -p MemoryMax=24G`, in `/tank/fn/scratch/source-corpus`.

Logs (sha256):
- run 4, `native-4.log` (committed), both tests OK:
  f9feb9da5c9ebd4c2962d6301a98a113cc0e590ad21d284fa6c29090e50d5e0a
- run 5, adding `test_signed_route_retry_is_already_stored`: the table and
  cancel tests OK, the signed retry FAILS (the PKT-166 finding):
  dd7527e89ea013c3053dda96efe939ad35f07d71b55c0a90ac821a829d1e602a
- earlier runs, each a harness classification:
  - run 1 (b8ad2cf3...): B did not admit the signed article. D23 requires
    the author's enrollment at the receiver; the harness now enrolls at
    both nodes.
  - run 2 (3f202723...): my guess that a duplicate operator post exits
    non-zero was wrong. It exits 0 and prints `accepted operator post
    DUPLICATE`, and the test now asserts that answer.
  - run 3 (c843b217...): I expected the relayed Path to begin
    `b.corpus.invalid!`. RFC 5537 s3.2.1 and fn-pu-edit-path write
    `b.corpus.invalid!!`: an empty path-diagnostic marks a verified hop.

Rows from run 4, abridged. A is the injecting node and B the receiving one.
The digests are SHA-256 of `store inspect`, which equals the served octets on
both nodes.

| element | POST at A | retry, later second | one changed byte | A number | A stored | B stored, Path | re-offer at B | after SIGKILL at A |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| supplied-date | 240 | 441 already stored | 441 different article | 1 | 94366703 | 507068ec `b!!a!not-for-mail` | 435 | same number and octets; retry 441 already stored |
| generated-date | 240 | 441 already stored | 441 different article | 2 | 83f1ac27 | b59a7723 | 435 | same; retry 441 already stored |
| client-path | 240 | 441 already stored | 441 different article | 3 | 543bad68 `a!poster.example.invalid!not-for-mail` | d877fb05 `b!!a!poster...` | 435 | same; retry 441 already stored |
| xref | 441 Xref must not be supplied | same | same | - | - | - | - | - |
| unknown-headers | 240 | 441 already stored | 441 different article | 4 | 63a41597 | 0530bc21 | 435 | same |
| mime | 240 | 441 already stored | 441 different article | 5 | fb497786 | e244dca1 | 435 | same; retry 441 already stored |
| legacy | 240 (generated Message-ID) | 240, a new article | 240, a new article | 6 | 28155d7d | 2c3e66b1 | 435 | same |
| signed, hybrid-author | exit 0 | exit 1, no word (PKT-166) | - | 9 | f6785d33 | 62543371 | 435 | same |
| carrier, POSTed | 240 | 441 already stored | - | 10 | 8381f33d | a9c5742e | 435 | same |

Operator post of the same source under its Message-ID (supplied-date,
client-path, mime): exit 0 and `accepted operator post DUPLICATE`; the served
Message-ID set is unchanged.

What each equality is:
- **Application operation.** The client's own identity, its persisted
  Message-ID. The legacy post has none, so its retry is a new article under
  a new generated Message-ID (NNT-005). That is the contract, not a defect.
- **Message-ID.** Transit decides by it alone: the re-offer answers 435
  (`fn-peer-decide-offer`). BP admission also keys on it
  (`fn-bpaj-transit-plan` through `fn-peer-decide-transfer`).
- **Authored source.** On the injecting routes the D25 verdict is
  `fn-rcl-existing-action`, keyed on the poster's source. The first post of
  every accepted element is a suffix of A's stored octets: the carrier, the
  8-bit MIME body and the unknown headers are kept byte for byte. A
  supplied Path gets A's identity spliced in and its tail kept (D32). No
  field is normalized.
- **Stored representation.** B's record is A's octets with
  `b.corpus.invalid!!` spliced after `Path: ` (`fn-peer-relayed-octets`),
  asserted exactly for every carried element. The two digests differ by
  that splice and nothing else.
- **Local number.** Per node, and never compared across nodes (A 1..10, B
  1..10 here only because B received in order). Unchanged by the SIGKILL
  reopen.
- **Bundle identity and forwarding attempt.** Not exercised by this module
  (see "Not done").

## Theorems (books/source-routes.lisp, PRF-117)

Subject: `fn-rcl-existing-action`. The host calls it in host/owner-host.lisp
at `fn-owner-existing-action` and `fn-owner-prepare`, and at
`fn-owner-existing-action-buffer` through `fn-rclb-existing-action`
(`fn-rclb-existing-action-is-rcl-existing-action`). Those are reached from
host/native/owner.lisp `fnn-owner-attempt`, which serves the served POST and
the operator post.

- `fn-sr-an-injection-is-not-a-tombstone` (no hypothesis): no
  `fn-inj-decide` decision's octets are a tombstone. So on a live injected
  article the host's tombstone-aware verdict is the D25 one. It closes the
  join that `fn-rcl-existing-action-is-pb-without-a-tombstone` left as a
  hypothesis.
- `fn-sr-a-retry-is-already-stored`:
  - hypotheses: the held payload is S injected at A; S is injected at A and
    at B; both carry Message-ID M; the groups are the held ones;
  - conclusion: `:duplicate`.
  - The node-added fields (Path's agent, Injection-Date, Injection-Info, a
    generated Date) never make a retry a conflict.
- `fn-sr-a-changed-source-is-a-conflict`: sources S1 and S2 differ, both are
  injected under M, and the held payload is S1 at A. The verdict is
  `:conflict` for any groups and clocks, so a changed authored byte is never
  a duplicate.
- `fn-sr-the-tombstone-keeps-the-source`: the tombstone of an injection
  keeps SHA-256 of the exact source, the injecting agent and SHA-256 of the
  octets.
- `fn-sr-a-retry-after-reclaim-is-already-stored` and
  `fn-sr-a-changed-source-after-reclaim-is-a-conflict`: the same two verdicts
  against the tombstone.
  - The second holds up to a SHA-256 collision on the two sources
    (`fn-rcl-collisionp`). That is the collision figure, about 2^128 work,
    assumed and not proved.
  - These three tombstone theorems are **unreachable-in-composition** today.
    No program writes a tombstone: `store reclaim` is not implemented
    (reclaim-host-2026-09-25.md s2).
- The `held` hypothesis was dropped only after the weakened statements were
  proved. `fn-sr-an-injection-is-a-cons` shows an injection is a cons.

Assurance chain, served POST:
1. Native entry: `fnn-owner-attempt`.
2. Executed ACL2 subject: `fn-rclb-existing-action` on the octet buffer.
3. Refinement: `fn-rclb-existing-action-is-rcl-existing-action`.
4. Maintained relation: none needed. The verdict reads one held record, and
   the held payload is the injection the same store committed.
5. Behavioural theorem: `fn-sr-a-retry-is-already-stored` and
   `fn-sr-a-changed-source-is-a-conflict`.
6. Observed result: the 441 lines in the table.

Transit and BP carry no source comparison: their equality is the Message-ID.
For a relayed carrier, the receiver verifies the author's signature over
`fn-hc-authored-source`, which drops exactly the node-added fields.

Teeth (tests/acl2/source-routes-tests.lisp):
- Reachable witnesses: a supplied Date, a generated Date and a supplied
  Path (recipe v3), injected by the real `fn-inj-decide` 37 s apart and held
  by the real Store. Each asserts the complete antecedent and the
  conclusion. The byte-identity decision D25 replaced answers `:conflict` on
  the same retry.
- Changed-source witnesses: a changed body byte, a changed supplied Path
  tail (D32) and a removed Date.
- Tombstone witnesses: stores built by `fn-rcl-reclaim-state`.
- Hypothesis-removal witnesses, each keeping the other hypotheses true:
  - another source held: conflict;
  - other groups: conflict;
  - the first Message-ID differs (a generated one per clock): conflict;
  - equal sources, in the conflict keystones: duplicate;
  - a refused decision's tombstone names no source;
  - another source's tombstone: conflict.
- `must-fail` forms for each of these.
- Not shown necessary: the injection and Message-ID hypotheses of the
  conflict keystones. They are the statement's scope (two injections under
  M), as in `fn-pb-two-sources-are-two-articles`, and no counterexample was
  constructed.

Certification: persvati run-20260925T235003Z-3cb2, green at 2 jobs
(`source-routes` 1.9 s, `source-routes-tests` 7.1 s), manifest
`planning/evidence/manifests/certify-20260925T235018Z-2734100.json`.
Run-20260925T233835Z-c1d5 was the cache-filling run; its failure was the
block lemma, since repaired.

## Cancel order, pinned reader, Supersedes, replay (s5.4, D29)

`test_cancel_orders_pinned_reader_and_replay`, on one node with every
article signed and authored:
- T1 then its cancel C1. A reader pinned before C1 answers 220 after it
  (now asserted, where control-c3b only recorded it). A fresh reader gets
  `430 withdrawn`.
- C2 then its target T2: `430 withdrawn` from T2's first view.
- S3 carrying `Supersedes: T3`: T3 answers 430, and S3 stays 220 and
  visible.
- The fresh view of fn.test is exactly [S3], live and after SIGKILL and
  replay. That is visible(T then C) = visible(C then T).
- It passes in runs 1 to 5.

Supersedes contract, a correction to the brief: Supersedes is **not** an
ordinary header on dev. Control-c3d made it a withdrawal of its target under
the cancel's rules (books/control-authority.lisp `fn-ctl-supersedes-target`;
planning/requirements.json). RFC 5537 s5.4 asks for exactly that: the
superseding article is handled as a normal article. The spike/control
finding (spike-control-2026-09-25.md) is stale, so no packet is needed.

Policy change at replay was not driven here: the newest-declined-key-statement
behaviour belongs to lane peering-compose.

## PKT-166: the signed control route has no retry identity

- **Trace.** `hybrid-author CONTROL 1 SOURCE ED ML PEM` with the same signed
  source a second time, 1.2 s later, exits 1 with empty stdout and stderr.
  The served Message-ID set is unchanged, so nothing new is stored and
  nothing is lost. Run 5 shows it: `SOURCE-CORPUS-SIGNED-RETRY`.
- **Cause.** host/native/hybrid-control.lisp `fnn-hybrid-control-author`
  commits through `fnn-owner-identity-commit` (`fn-owner-prepare-identity`)
  and never asks `fn-rcl-existing-action`. The Store's identity prepare
  refuses the held Message-ID, and the route answers `:refused`.
- **Constraints.**
  - "Uncertain, refused and accepted stay distinct at every boundary, exit
    codes included".
  - D25: a retry of the same source is "already stored here".
  - The operator post already answers exit 0 with
    `accepted operator post DUPLICATE`.
- **Default.** Before building the event, ask `fn-owner-existing-action`
  with the injected carrier octets `received`, the Message-ID and the filed
  groups. On `:duplicate`, answer a new control reply that the client prints
  as `DUPLICATE` with exit 0. On `:conflict`, answer a named refusal.
  `fn-sr-a-retry-is-already-stored` already proves the verdict for this
  input: the route's octets are `fn-inj-decide`'s.
- **Rejected alternative.** Leave exit 1. The cost is that an agent cannot
  tell a safe retry from a refusal.
- **Affects.**
  - the control-socket reply vocabulary (`fn-native-hybrid-control-host-*`);
  - the `hybrid-author` client's exit map;
  - `test_signed_route_retry_is_already_stored`, which is red until then.
- **What continues without it.** Everything else. A client POSTing the
  carrier has the right retry (441 already stored).

## Not done, and why

- **BP carriage of the corpus to a second node through dtn7.**
  - Not exercised: the lane's budget went to the table, the theorems and the
    signed-route finding.
  - What the route does is traced: `fn-bpo-request-message` carries the
    stored payload, and the receiver stores `fn-peer-relayed-octets` keyed
    on the Message-ID.
  - The next action: extend the module with the
    `tests/bp-dtn7/run_fn_dtn7_app_receipt.py` flow on `fn-host-dtn-developer`.
    It should record the bundle identity (source EID, creation time,
    sequence) and the kind-8 attempt, and assert B's record is A's with B's
    Path splice.
- **Reclamation.** It has no native route (no `store reclaim`), so the
  tombstone theorems stand as the specification for that program.
- **A theorem that relaying keeps the authored-source projection.**
  - Statement:
    `fn-hc-authored-source (parse (fn-pu-relay-article x id e)) = fn-hc-authored-source (parse x)`.
  - Not proved: it needs parser lemmas over the Path splice and the Xref
    drop.
  - Transit's contract does not rest on it (the Message-ID does), but the
    carried-signature check does in part. It is the next proof target.
