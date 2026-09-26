# Source corpus 2: relaying cannot change who wrote it (2026-09-26)

Lane source-corpus-2, branch lane/source-corpus-2, base 4d7ab2b9 (contains
the source-corpus merge 6cfe702e). The Fable mandate s5.3 and s9 (first two
paragraphs). Ids: PRF-127, SCN-073, PKT-246.

## What now works, in one sentence

The proof: an article's authored source (the octets a carried signature
covers) is the same at B as at A whenever B stores it by NNTP transit or by
BP, with no hypothesis beyond the decision B's host already makes. The
native BP run carries all seven accepted corpus articles from A through a
dtn7-rs relay into B. It records each one's kind-8 attempt and bundle
identity, but B refuses every one of them, and the reason is not printed
(PKT-246, below).

## PRF-127: the theorems

Books: `books/relay-source.lisp` (the parser join) and
`books/relay-source-routes.lisp` (the routes).

- `fn-rs-authored-source-is-the-walk`
  - Hypothesis: the parser accepts Y.
  - Conclusion: `fn-hc-authored-source` of the parsed article equals
    `fn-rs-source-walk (fn-pu-strip Y nil) nil`.
  - So the authored source is a function of the octets with Path and Xref
    stripped.
  - Proof: the parser's own partition theorems
    (`fn-article-successful-parse-fields-recompose-header`,
    `-fields-correspond`, `-preserves-source`, `-syntax-p`) make Y the
    fields' raw lines, the blank line and the body.
  - Each field is well formed:
    - its first line opens with ftext and has a colon;
    - its continuations open with WSP;
    - no line carries CR or LF.
  - Two walks over well-formed fields give the result:
    - `fn-pu-strip` drops exactly the fields whose first line names Path or
      Xref;
    - the source walk drops exactly the reserved ones.
  - Every Path or Xref field is reserved (`fn-rs-a-path-or-xref-field-is-reserved`).
- `fn-rs-relaying-keeps-the-authored-source`
  - Hypothesis: the parser accepts both OCTETS and
    `fn-peer-relayed-octets CFG PEER OCTETS`.
  - Conclusion: their authored sources are equal.
  - It composes the walk theorem with
    `fn-peer-relayed-octets-change-only-path-and-xref`, the path-update
    keystone at the peer representation.
- `fn-rs-a-transfer-is-wanted-only-if-both-parse`: `fn-peer-decide-transfer`
  answers `:want` only when the parser accepts both. Those are its
  `:proto-article` check and its RFC 5537 s3.6 `:oversize` check.
- `fn-rs-a-wanted-transfer-keeps-the-authored-source` (NNTP transit)
  - Hypothesis: the decision is `:want`.
  - Conclusion: the payload `fn-peer-injection-arguments` stages parses and
    has the received article's authored source.
  - The host line: host/owner-host.lisp `fn-owner-take` stages that payload
    (`fn-peer-injection-arguments-payload-unfolds`), through `fn-peer-transfer`.
- `fn-rs-a-bp-transit-keeps-the-authored-source` (BP)
  - Hypothesis: `fn-bpaj-transit-plan` answers `:submit`.
  - Conclusion: the request's article and `fn-bpaj-transit-stored-octets`
    both parse and have the same authored source.
  - The host line: host/bp-native-app-host.lisp `fn-owner-app-plan-install`
    calls the planner.

Neither route keystone takes a hypothesis about the article. The
hypothesis is the host's own decision, whose checks discharge the parse
conditions.

What it does not say:
- nothing about signatures, only that the bytes one covers are the same at
  both nodes;
- nothing about A's injection. That is PRF-117 (`books/source-routes.lisp`;
  cited, not restated) and books/injection-path.lisp's keystones
  (`fn-inj-source-of-inverts-the-injection`, `fn-inj-unsplice-of-a-splice`).
  These say A's stored octets give back the poster's source, D32's Path
  tail included. PRF-127 says what B stores keeps the authored-source
  projection of what A sent.

The projection drops the whole Path field. So the poster's Path tail,
which D32 keeps as part of the poster's source at A, is not in
`fn-hc-authored-source`. That is the carrier's contract (the signature
covers the fields the injecting node cannot change). D32's source identity
at A is PRF-117's.

### Teeth (tests/acl2/relay-source-routes-tests.lisp)

The fixture:
- The corpus client-path article (a supplied Path tail), in the BP peer's
  group, with a folded unknown header.
- A injects it with the real `fn-inj-decide` under agent dtnb.example, the
  identity B's peer record expects. So it carries A's injection prefix
  (`Path: dtnb.example!poster.example.invalid!not-for-mail`) and
  Injection-Info.
- B is the bp-transit-join-tests node and configuration.

Reachable witnesses, each asserting the whole antecedent and conclusion:
- The walk equals the projection. The projection keeps the unknown header
  and the Subject, and drops Path and Injection-Info.
- The relay:
  - B's Path is `fnA.hbox.test!!dtnb.example!poster.example.invalid!not-for-mail`;
  - A's octets and B's octets differ, and their authored sources are equal
    and non-empty.
- A sender's Xref: B drops it, and the authored source is still A's.
- A changed Subject is another authored source through the same relay, so
  the projection is not constant.
- A `:want` transfer: the staged payload is B's relayed octets, with A's
  authored source.
- A `:submit` BP plan over an encoded request of that article: the stored
  octets are B's relayed octets, not the article, with A's authored source.

Hypothesis-removal witnesses:
- Each one checks the retained hypotheses, the failure of the omitted one
  and the failure of the conclusion.
- Each has a `must-fail`, with the subject closed and no induction.

| Removed hypothesis | Witness |
| --- | --- |
| walk: the parse | octets with no blank line |
| relay: the received parse | a 1000-octet Xref line: A's octets do not parse, B's (Xref dropped) do |
| relay: the stored parse | a 995-octet Path line: parses, but B's splice pushes it past 998 |
| transfer: `:want` | that Path, refused `:oversize`: its staged projection does not parse |
| BP: `:submit` | a request whose article the parser refuses |

Certification (hbox, 2 jobs, 300 s):
- run-20260926T010101Z-8350, manifest
  `certify-20260926T010122Z-3162`:
  - `relay-source` 1.7 s, `relay-source-routes` 3.9 s, both passed;
  - the test book timed out in its first `must-fail`, an unbounded search
    over the open walk. Every assertion before it had passed.
- run-20260926T010756Z-cf08, manifest `certify-20260926T010817Z-22211`:
  `relay-source-routes-tests` passed, 4.5 s. Each `must-fail` now closes
  its subject.
- The books are unchanged between the two runs (b7e4dfa6).

Assurance chain, BP route:
1. Native entry: host/native/bp-node.lisp `fnn-bpnode-request-result`,
   then bp-app `fnn-bpapp-accept-locked`.
2. Executed ACL2 subject: `fn-owner-app-plan-install`, then
   `fn-bpaj-transit-plan`.
3. Refinement: the planner is the subject itself.
4. Maintained relation: none. The plan is a function of the request octets
   and the node.
5. Behavioural theorem: `fn-rs-a-bp-transit-keeps-the-authored-source`.
6. Observed result: not yet. B refuses (PKT-246).

The NNTP route has the same chain through `fn-owner-take`, and the
source-corpus identity table observed it: B's record is A's with B's
splice.

## SCN-073: BP carriage on hbox (native)

Images, built from this lane's tree at b7e4dfa6 by
`source-corpus-2-2026-09-26/build.sh` and `build-default.sh`:
- dtn developer: launcher
  099ca37eff82f882a74d2160ba09c1c5b5bdab016325da438013701c2a991c8b, core
  e926a51d6031d46e45be473ea9b0adea5f66c9cf83d71e49242c9c4503b92c50;
- developer: launcher
  d175fb41d86c8ac6f92616244281fc7ce781c7ff58bfa228c56bfbc0cd51c9bf, core
  c778dd9465e7687aa1ee99beaba843769cc4c9b0334e72c35972faa4f0ffb3f9.

No image input differs from dev 4d7ab2b9: the lane adds books the host does
not include, tests, registries and records. The runner is
`source-corpus-2-2026-09-26/native.sh`, under
`systemd-run --user -p MemoryMax=24G` in `/tank/fn/scratch/source-corpus-2`.
The dtn7-rs checkout is `/tank/fn/dtn7/repo`.

The module is `tests/test_native_source_corpus_bp.py`. A is the lane's
developer image as the NNTP owner, and the DTN developer image for the
obligations. B is `bp-node serve` behind one dtn7-rs relay (sled) and a
byte relay that can hold a transfer mid-bundle. It prints
`SOURCE-CORPUS-BP-TABLE`.

Logs (sha256):
- run 2 (`native-2.log`,
  580c4886592ca72959dcf079265fda923294a927466ebd46f49fd1ab60121fab).
  - A's records came from `store post`, which files the source raw:
    - no injection, no A Path identity, Xref accepted;
    - so the elements without a Date or Message-ID were not articles B
      could take.
  - B accepted 4 of 8 (supplied-date, client-path, unknown-headers, mime).
  - The module waited 60 s for each refusal, so the run took 478 s, over
    the 300 s budget.
  - Harness classification: `store post` is not the injecting route.
    Superseded by run 3.
- run 3 (`native-3.log`,
  bb97edd6e42d18467537e6a4b8101432ae238978e78633b31227a1e10a1a9977), 108 s.
  - A's owner took the served POST: Xref is 441, and the other seven
    are 240.
  - Each of the seven has A's kind-8 attempt line (`BP obligation request
    durable attempt work=... attempt=... generation=0 ... adu=N`).
  - Each has a distinct bundle identity in B's kind-5 frame: source
    `dtn://sender/`, creation 843700685603 ms, sequences 0 to 6.
  - B's `bp-node serve` answered `BP node delivery request-refused` for
    every one. The contract assertion fails at the first element.
- run 4 (`native-4.log`,
  39852fba4cbd0f3983eecd13934cf3a6a738ef17508c41c41731434d16dfc911).
  - A diagnostic: B's owner never ran, and the author was not enrolled at B.
  - The same seven refusals, so neither B's owner run nor the enrollment is
    the cause.
  - The knob is removed from the module.

Classification: a behavioural failure that is still open. It is not a
harness result, and the expected answer is not changed.
- Same image, same boundaries, same relay:
  - B accepted A's raw `store post` records (run 2);
  - B refuses A's injected ones (runs 3 and 4).
- The model plans `:submit` for an fn-inj-decide article under a matching
  configuration (the BP witness above).
- The reason B refuses is not observable. host/native/bp-node.lisp
  `fnn-bpnode-request-result` returns `:request-refused` without the line
  `fn-owner-app-refusal-log` renders. bp-app's path writes that line; the
  bp-node path never does.
- PKT-246 is the next action:
  1. render the planner's line on the bp-node path;
  2. rerun the module;
  3. fix what the line names.
- The SIGKILL mid-receive step ran (the byte relay held the seventh
  transfer, B was SIGKILLed and restarted, and the relay restarted). B's
  answer after it was the same refusal.

The identity table, as far as it goes, from run 3. A's Path is A's identity
prepended. The creation time is 843700685603 ms for every element, and the
table gives the bundle sequence.

| element | POST at A | A's Path | kind-8 attempt (adu) | bundle seq | B |
| --- | --- | --- | --- | --- | --- |
| supplied-date | 240 | `sender!not-for-mail` | 483 | 0 | refused |
| generated-date | 240 | `sender!not-for-mail` | 546 | 1 | refused |
| client-path | 240 | `sender!poster.example.invalid!not-for-mail` | 513 | 2 | refused |
| xref | 441 Xref must not be supplied | - | - | - | - |
| unknown-headers | 240 | `sender!not-for-mail` | 630 | 3 | refused |
| mime | 240 | `sender!not-for-mail` | 774 | 4 | refused |
| legacy | 240 (generated Message-ID) | `sender!not-for-mail` | 589 | 5 | refused |
| signed (carrier) | 240 | `sender!not-for-mail` | 8015 | 6 | refused after the mid-receive SIGKILL |

## The conflict word: a packet (task 3, not implemented)

The coordinator did not answer before the budget's second half, so this
stays a packet.

- **Trace.**
  - A changed source under a held Message-ID over the control socket
    (`hybrid-author`; the operator post the same way) is D25's `:conflict`
    (`fn-rcl-existing-action`).
  - host/native/hybrid-control.lisp maps it to the reply `:refused`, so the
    client prints `refused hybrid-author REFUSED`, exit 1.
  - The same class answers a bad frame, a closed posting policy or an
    unusable clock.
  - A client cannot tell "you changed an article I hold" from "I refused
    this request". The first calls for a new Message-ID or resending the
    saved bytes. The second calls for a different fix.
- **Constraints.**
  - `*fn-nctrl-statuses*` (books/native-control.lisp) is an enumeration
    codec. A new word must come last, so every earlier status keeps its
    octet. That is the precedent of `:article-exceeds-profile-bound`.
  - Exit codes are classes (`fn-native-control-status-class`): 0
    accepted, 1 refused, 3 uncertain, 4 fault.
  - Uncertain, refused and accepted stay distinct (AGENTS.md).
- **Default.**
  - Append `:conflict` to `*fn-nctrl-statuses*` and classify it `:refused`
    (exit 1).
  - The hybrid-control and operator-post callbacks answer `:conflict`
    where they now answer `:refused` for the D25 conflict.
  - The client prints `refused hybrid-author CONFLICT`.
  - A theorem in the style of `fn-native-control-refusal-status-is-a-refusal`:
    the conflict is a refusal, and every earlier enumeration octet is
    unchanged.
- **Rejected alternative and its cost.** A distinct exit code for the
  conflict (say 2). Scripts that treat 1 as the refusal would read a
  conflict as success or as a new class. That breaks the three-outcome
  contract every client relies on, for one diagnostic.
- **Affected.**
  - Format: the FNCT reply enumeration gains one octet value. Old clients
    decode it as `:bad` and classify it as a fault (exit 4), not a
    refusal. A client upgrade must precede or accompany the node's.
  - Proof: native-control's codec round trip and status-class theorems.
  - Callers: hybrid-control.lisp, the operator post path in owner.lisp,
    tools/fn_client.py (prints the word).
- **What continues without it.** Everything. The conflict is a refusal
  today, correctly classed, and the documented retry rule (resend the
  saved bytes) keeps a correct client out of it. The word only improves
  the diagnostic.

## Registry and docs

- PRF-127 in planning/proofs.json and proof-events.json; NNT-020 names it
  (reciprocal).
- SCN-073 in tests/scenarios/catalog.json, status `specified`: the module
  exists and runs, and its contract assertion fails at B's refusal.
- Makefile roots: `tests/acl2/relay-source-routes-tests` and
  `books/relay-source`. The second is named because tools/ledger.py
  `root_closure` follows a test root's includes only one level (it looks up
  the unresolved `tests/acl2/../../books/...` path). Without it the walk
  theorem reads as unreachable.
- `make check` is green in the worktree with the ledger regenerated
  locally. The generated ledger is not committed; the deputy regenerates it
  on merge.
- PKT-246 in planning/backlog-2026-09-25.md.
- docs/agents.md's retry paragraph gains the ML-DSA-65 sentence (the
  source-corpus merge had not added it; PKT-245's docs part).

## Not done, and why

- **SCN-073's observed result.** B refuses the carried corpus (above). The
  next action is PKT-246's first step: render the reason on the bp-node path.
- **The conflict word.** A packet only; no coordinator answer.
- **Carrier signature verification at B over BP.** It is not exercised,
  because B refuses before its store. PRF-127 is the byte half of that
  claim.

## 2026-09-26, source-corpus-3: the six unsigned elements arrive; the signed one is PKT-247

Lane source-corpus-3 continues on `lane/source-corpus-2` in the same
worktree. dev 43fad7ab was merged at 4f7128b7. That merge brings
mission-signed's reason line and its transit-lookup fix
(`fn-bpaj-transit-article-fields`). Registry conflicts were merged by id:
PRF-127 and SCN-073 were appended, NNT-020 keeps PRF-127, and the backlog
keeps both sides.

### Certification at the merged bytes (hbox, 2 jobs, 300 s)

- The REPL came first, on hbox, in a scratch copy of the tree
  (`/tank/fn/scratch/source-corpus-2/repl-r1`):
  - `books/relay-source-routes` loaded all its forms over its cached
    closure;
  - `peer-inbound-tests`, `bp-transit-join-tests` and
    `relay-source-routes-tests` were loaded by `ld`, 0 errors.
  - The two uncertified test books were loaded before the books that
    include them.
- run-20260926T022220Z-4401 (`--affected-by` both lane books), manifest
  `certify-20260926T022246Z-145464`:
  - relay-source-routes passed, 4.2 s;
  - relay-source-routes-tests passed, 4.9 s;
  - relay-source was already certified at these bytes.
- run-20260926T022458Z-2258 (the 162 default and dtn image roots,
  incremental), manifest `certify-20260926T022535Z-150066`:
  - it certified the 9 books the cache lacked at 43fad7ab, all passed and
    all under 10 s (slowest native-live-status, 8.6 s);
  - the image acquire had refused ("no complete current artifact set")
    before it.

### Images and native runs (hbox, `/tank/fn/scratch/source-corpus-2/tree-r3`)

Built by `build.sh` and `build-default.sh` with `ROOT=.../tree-r3`, under
swarm-build. Each build log was read for ACL2 errors (PKT-284), and it had
none.
- dtn developer: launcher `d710917e3dbd51bb55c340b50fed4ade20ed922fd9131a1264bd98c05d0c9abd`,
  core `ea580f55172ee1d0722e925e8ff18eb546bf5e3959ae4f0d0c6b461b2217dd01`;
- developer: launcher `a3ea9eaed4a1d5998c6b11e4ba985c045735c5a2ebc7483fe6f43db8833906b3`,
  core `7a58d788d13ff751a5c05eb6bf014c8725b355f3f30dc8e6487e83d1be2f3ab6`.

The module now records the line of ACL2's reason that precedes each B
verdict (`b_reason`). The expected answer is unchanged.

- `native-5.log`
  (`c9f6b2895fd8495d359371c38c356cbe630ff5890779225fd69feee4c203b86a`),
  `tests.test_native_source_corpus_bp`, 104 s, FAIL at the signed element.
  - Every unsigned element: B answers `request-accepted`.
  - B's record is A's record with B's splice (`b_is_a_with_b_splice`).
  - It is unchanged across the idle SIGKILL and the reopen.
  - Each has a distinct bundle identity in B's kind-5 frame.
  - B's log for the signed element:
    `native-5-b-serve-1.log`
    (`f8e6debb31b93a37290849dc4b3312707787ef6aa15269b39bb8771293f2422e`).
- `native-6.log`
  (`742eca3bffb36e340fbfd084db5b4550458c60f352bc57274eaf2c289762449e`),
  `tests.test_native_source_corpus` (the NNTP-route regression gate): OK,
  3/3, 14 s.

The identity table from native-5:
- Each bundle's source is `dtn://sender/`, its destination is
  `dtn://receiver/`, and its creation time is 843704988638 ms.
- A's Path is `sender.bp.gate.invalid!…`.
- B's Path is `receiver.bp.gate.invalid!!` followed by A's.
- SHA-256 values are shown to 8 hex digits; native-5.log has them in full.

| element | Message-ID | A POST | kind-8 attempt (adu) | bundle seq | B frame | B verdict (reason) | A stored | B stored | B = A + splice | same after reopen |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| supplied-date | `<sc-supplied-date@example.invalid>` | 240 | 483 | 0 | 1-0 | accepted | e9a0b6b9 | 2928df50 | yes | yes |
| generated-date | `<sc-generated-date@example.invalid>` | 240 | 546 | 1 | 1-3 | accepted | 9d02b805 | 0985e8af | yes | yes |
| client-path | `<sc-client-path@example.invalid>` | 240 | 513 | 2 | 1-6 | accepted | 8aa9d72c | 072842d0 | yes | yes |
| xref | - | 441 Xref must not be supplied | - | - | - | - | - | - | - | - |
| unknown-headers | `<sc-unknown-headers@example.invalid>` | 240 | 630 | 3 | 1-9 | accepted | 3a015185 | 1b14936d | yes | yes |
| mime | `<sc-mime@example.invalid>` | 240 | 774 | 4 | 1-12 | accepted | 3d1922d7 | 2019d250 | yes | yes |
| legacy | `<00000000843704994286.00000000000000002543.fn@sender.bp.gate.invalid>` (generated) | 240 | 589 | 5 | 1-15 | accepted | 78e30aec | 48c567f1 | yes | yes |
| signed (carrier) | `<sc-signed@example.invalid>` | 240 | 8015 | 6 | 2-0 | **refused (reason=history)** | 0c8495b4 | ac2b6303 | yes | yes |

client-path keeps the poster's Path tail at both nodes (D32):
`receiver.bp.gate.invalid!!sender.bp.gate.invalid!poster.example.invalid!not-for-mail`.

### The signed element: PKT-247's second layer, not this lane's scope

- Byte relay: it held the seventh transfer, and B was SIGKILLed mid-receive.
- B restarted (`b-serve-1`):
  1. it received the bundle once (`BP accepted xfer=1 adu=8015`);
  2. it made the carried-source decision
     (`BP node source carried carrier=ingress-boundary author=sender-author`);
  3. it stored the article: B serves it, and it is A's with B's splice,
     the same after reopen;
  4. it answered `BP node delivery refused result=refused reason=history`.
- One receipt and one delivery, so the SIGKILL did not cause a second
  submission.
- This is the second layer mission-signed diagnosed (PKT-247):
  - a signed article commits as a kind-4 acceptance;
  - the BP application's Store binding (`fn-bpaj-record-for-msgid`,
    `fn-bpr-store-record-acceptedp`) reads only plain records;
  - so after the durable commit the lookup is `(:absent)`, and the
    resubmission meets `(:have :history)`.
- Class: implementation, in the BP receiver's Store binding (bp-native-app,
  bp-native-app-fast, bp-receipt). That is outside this lane's scope: the
  corpus, the relay projection and the transit lookup are all correct here.
  It is owned with PKT-247. Stopped here; the expected answer is unchanged.

The first cause of the old refusals (source-corpus-2 native-3 and native-4)
is confirmed as mission-signed's layer 1. With `fn-bpaj-transit-article-fields`,
every unsigned element carrying A's `Injection-Info` is accepted.

Assurance chain, BP route, now observed for the unsigned elements:
1. Native entry: `fnn-bpnode-request-result`.
2. Executed subject: `fn-owner-app-plan-install`, then `fn-bpaj-transit-plan`
   answering `:submit`.
3. Behavioural theorem: `fn-rs-a-bp-transit-keeps-the-authored-source`.
4. Observed: B's stored octets are A's with only B's splice (a stronger
   observation than the authored-source projection the theorem states).

### Status

- SCN-073 stays `specified`:
  - six of seven carried elements meet its expected result;
  - the signed one waits on PKT-247;
  - native-5.log is added to its evidence.
- PKT-246:
  - its reason-rendering step was done by mission-signed;
  - its cause was mission-signed's layer 1, now fixed;
  - what remains is the conflict-word packet (unchanged, no coordinator
    answer: the default is to append `:conflict`, a refusal, exit 1).
- `make check` is green in the worktree, with the ledger and the current
  view regenerated locally (not committed).
