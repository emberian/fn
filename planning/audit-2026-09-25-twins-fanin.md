# Audit: twins, dead definitions and include fan-in (2026-09-25)

Audit lane `lane/audit-twins-fanin`, from dev `67b028c7`. It proposes changes and makes none: no book, host or registry file changed. No ACL2 ran, no farm, no hbox. Every dependent count is what `python3 tools/certify_books.py --affected-by books/<b> --dry-run` prints (the book itself plus every Makefile root that includes it transitively). I ran the tool for each book this report names. The same numbers come out of the reproducible graph in `planning/evidence/audit-twins-fanin-2026-09-25/graph.py`, which imports the runner's own `local_closure` and `default_books` and gives 746 roots over 762 local books.

**Method and limits.**
- *Names* are the heads of `def*` forms, lexed with comments, strings and `#\x` characters removed (`clean.py`). *References* are textual token matches.
- *Live* means reachable from a name in `host/native/*.lisp`, a name in a `host/*.lisp` host book, or the statement of a theorem cited in `planning/proof-events.json` (567 cited theorems), then closed under "a live definition's body mentions it" (`sweep.py`).
- The static analysis cannot see implicit rewrite-rule use. A dependent can rely on a theorem it never names. Every split or narrowed include below therefore needs a certification before it counts, and the pcert Convert wave (`certify_books.py --pcert`) is the cheap way to find the proofs that lose a rule.
- Names that a macro generates are also invisible, for example `defrecord` accessors and `defattach` books.
- *Estimated seconds* = max(critical path, sum of book walls / 2). The walls are each book's latest archived wall (`certify_books.archived_walls`), which mixes hosts and job counts. Calibration against today's measured runs:

| change | books | estimate | measured |
|---|---:|---:|---:|
| records-shape | 619 | 898.6 s | 889.8 s (persvati `certify-20260925T004450Z`, 628 books, 2 jobs) |
| records-shape | 619 | 898.6 s | 999.6 s (hbox `certify-20260924T153508Z`, 560 books, 2 jobs) |
| injection | 423 | 742.4 s | 770.7 s (persvati `certify-20260924T230829Z`, 429 books, 2 jobs) |
| native-admin | 16 | 33.5 s | 42.1 to 52.8 s (hbox `012235Z` 18 books 44.8 s, `013506Z` 26 books 52.8 s; persvati `20260925T010501Z` 19 books 42.1 s) |

  Small runs carry roughly 10 to 20 s of fixed overhead that the estimate leaves out.

## 1. Twins and dead definitions

### 1a. The twins today's merges named

Ranked by the dependent count of the book that would recertify (cheapest first).

| # | twin | sibling or last caller | recertifies | theorem statements that change |
|---|---|---|---:|---|
| T1 | `fn-bpiw-attempt-record` (books/bp-ion-workflow.lisp:61) | `fn-bprq-attempt-record` (books/bp-request-plan.lisp:14), proved equal by `fn-bpiw-attempt-record-is-the-generic-attempt` (tests/acl2/bp-request-plan-tests.lisp:122). The host calls only the generic one (host/workflow-host.lisp:183-188, `fn-workflow-ion-attempt-record`). No book function calls the ION copy. Its remaining callers are test constants (bp-ion-workflow-replay-tests.lisp:71, :118; bp-ion-workflow-tests.lisp:9). | 7 (bp-ion-workflow), est. 8.2 s | delete the test theorem at bp-request-plan-tests.lisp:122; the tests call `fn-bprq-attempt-record` instead. No registry event names either function. |
| T2 | `fn-pix-decide-offer` (books/peer-offer-indexed.lisp:109), `fn-pix-peer-command` (:173), `fn-pix-peer-step-pinned` (:246) | superseded by the `fn-pgc-` chain (books/peer-guard-carried.lisp). Since D24 the host reaches the peer arm through `fn-scar-peer-step-pinned` (books/served-carried.lisp:106), which calls `fn-pgc-peer-arm`; host keystone `fn-pgc-peer-arm-is-peer-step-pinned` (peer-guard-carried.lisp:320). The three `fn-pix-` copies are called only by tests (peer-offer-indexed-tests `pix-step`). `fn-pix-history-hasp` (:33) stays live through `fn-pgc-decide-offer`. | 12 (peer-offer-indexed, which includes peer-guard-carried's 11), est. 29.1 s | delete `fn-pix-decide-offer-is-peer-decide-offer` (:134), `fn-pix-peer-command-is-peer-command` (:209) and `fn-pix-peer-step-pinned-is-peer-step-pinned` (:277). Restate `fn-pgc-decide-offer-is-pix-decide-offer` (peer-guard-carried.lisp:116) as `...-is-peer-decide-offer`, composed with `fn-pix-history-hasp-is-peer-history-hasp` (:92). Re-hint `fn-pgc-peer-command-is-peer-command` (:207, its hint enables `fn-pix-decide-offer` at :214). None of these is a registry event; the cited keystones `fn-pix-history-hasp-is-peer-history-hasp` and `fn-pgc-peer-arm-is-peer-step-pinned` keep their statements. |
| T3 | `fn-sn-existing-action` (books/store-node.lisp:65) | `fn-pb-existing-action` (books/poster-bytes.lisp:80), the only one the host calls (host/owner-host.lisp:364, :1328; host/store-node-host.lisp:497, :624). The Python bridge also calls it through `fn-store-sn-existing-action` (store-node-host.lisp:618-624). The old function is named only by `fn-pb-existing-action-refines-the-byte-identity-decision` (poster-bytes-invariants.lisp:227, `:rule-classes nil`) and by three `-by-definition` lemmas in books/store-node-existing-invariants.lisp:9, :20, :31. None is cited. | 279 (store-node) if removed from store-node. It needs 3 (poster-bytes) if the definition moves into poster-bytes as the refinement reference. The move itself edits store-node, so it costs 279 once, est. 546.5 s. | the refinement theorem keeps its statement. Delete store-node-existing-invariants (2 roots with its test) and its three lemmas. |
| T4 | the K4 family is stated over `fn-sn-open-observed` (books/store-observed.lisp:207) | the host calls `fn-cpo-open-observed` (books/config-observed.lisp:18; host/owner-host.lisp:193, host/store-node-host.lisp:159). `fn-sn-open-observed` has no host caller: it is reached from the live set only through `fn-own-reopen` (books/owner.lisp:1523) and from 11 cited theorems. store-observed.lisp:578 and byte-store-keystones.lisp:8-12 say so in comments. The only cited theorem over the called function is `fn-bs-host-reopened-kernel-is-the-recovered-kernel` (byte-store-k0-recovery), which relates its output to the recovered kernel, not to the K4 conclusions. | a bridge book above config-observed and byte-store-keystones: about 2 roots (book + test), est. about 5 s. Restating in place instead touches store-observed (211, est. 456 s), byte-store-keystones (5) and bp-receiver-evolving-store-invariants (2). | none restated if a bridge `fn-cpo-open-observed-success-is-sn-open-observed-with-configuration` (proposed name) is proved. The 11 cited statements that gain it as their host subject are PRF-007: store-observed.lisp:459, :508, :554, :630, :724 and bp-receiver-evolving-store-invariants.lisp:448, :671; PRF-036: store-observed.lisp:777; PRF-041: byte-store-keystones.lisp:93, :137, :446. |
| T5 | `fn-hc-source-header` / `fn-hc-authored-source` (books/hybrid-carrier.lisp:193, :203) versus `fn-inj-source-of` (books/injection.lisp:712) | not twins in value. The signature preimage drops, by field name, the seven names of `fn-hc-reserved-namep` (:139-147: FN-Authorship, Path, Xref, Injection-Date, Injection-Info, FN-Statement, FN-Policy). The injection inverse strips this agent's recipe block (Path, generated Injection-Date / Message-ID / Date, Injection-Info) and keeps the FN-* carriers. They agree only where no Date or Message-ID was generated, which `fn-hc-required-sourcep` (:161) guarantees for a signed source. No theorem relates them: `fn-hc-authored-source` is named only in hybrid-carrier.lisp and specs/identity.md. | 417 (hybrid-carrier) to change hybrid-carrier. A correspondence theorem in a new book above injection-invariants and hybrid-carrier costs about 2 roots. | new: for a source satisfying `fn-hc-required-sourcep`, `fn-hc-authored-source` of the injected record equals that of the source. This is the correspondence the gpt-6 review asks for (D25 section, "reuse and strengthen that correspondence"). |
| T6 | `fn-store-post-boundary` (host/store-host.lisp:426-427) | an alias, by definition, of `fn-sbud-post-boundary` (books/store-budget-naming.lisp:133). Only the Python bridge calls it (tools/frame_bridge.py:429); the native host calls `fn-sbud-post-boundary`. | 0 (host/store-host is not in the Makefile root closure) | none |
| T7 | `fn-store-txn-prefix-reclaim-plan` | deleted by the m5-compaction merge (`f2a0bdfc`). No book, host or tool names it. One stale sentence remains: planning/proofs.json, the profile-upgrade `progress_note` ("fn-store-txn-prefix-reclaim-plan keeps its own copy of the namespace bound"). | 0 | none; the prose needs one edit |

The three carried chains are twins on purpose. Each copy is proved equal to its reference, and the reference is kept because the requirement theorems are stated over it. Only the unused `fn-pix-` copies (T2) are dead. The sweep flags no `fn-scar-` or `fn-pgc-` function as dead: all 17 `fn-scar-` and 8 `fn-pgc-` definitions reach the host through `fn-scar-ocfg-read-tls-prefix` (host line comment owner-host.lisp:1397-1407).

### 1b. Definitions no host line and no cited theorem reaches

`sweep.py` finds 6743 function-like definitions in `books/`. Of these, 5585 are live and 1070 non-constant definitions in 192 books are not reached. Grouped by the dependent count of their book (the cost of deleting them):

| book dependents | books | unreached definitions |
|---|---:|---:|
| 1 to 3 | 50 | 303 |
| 4 to 20 | 46 | 279 |
| 21 to 100 | 19 | 106 |
| over 100 | 78 | 382 |

"Unreached" is not the same as "delete". The set includes:
- induction schemes (`*-induct`);
- reference specifications that only uncited theorems use, for example the RFC 5536 grammar `fn-record-group-name-grammarp`, whose keystone `fn-record-group-namep-is-the-rfc-5536-grammar` is in no registry target;
- `unreachable-in-composition` notation that the book already marks, for example `fn-sn-fence-node` and `fn-sn-resolve-node` (store-node.lisp:1509-1513);
- 18 macro-time helpers of `books/defrecord`, which are false positives: they run when `defrecord` expands.

Each row still costs the listed dependents on every change to its book. The full list is in the appendix table. Named items from the sweep that are real twins or leftovers:
- `fn-sn-make-v3`, `-v4`, `-v5` (store-node) are superseded record constructors. `fn-sn-make-v6` is the live one.
- `fn-bs-*-impl` (byte-store-frame, 169 dependents): `fn-bs-config-okp-impl`, `fn-bs-frontier-decode-impl`, `fn-bs-frontier-encode-impl`.
- `fn-stmt-decode-*-impl` and `-prechecked` (statement-codec, 482 dependents). These are implementation copies whose spec twins are the live ones.
- `fn-cnode-complete`, `-prepare`, `-recover`, `-served` (node-config, 213 dependents), and `fn-config-aware-*` (config-records, 214 dependents).
- 22 `fn-nntp-dt-*` and `fn-nntp-blind-env` in nntp-responses (214 dependents): a date parser the served path does not call.
- 23 `fn-prin-*` succession functions in principal (464 dependents). These are the design for key succession (author-key-succession-proposal), not dead code; they still cost 464 roots on every edit.

### 1c. `-by-definition` lemmas

There are 121 theorems named `-by-definition` or `-unfolds` in 61 books. The registry cites none of them (the "cite keystones" rule holds). Of these, 64 are named by no other form anywhere, and 27 of those are `:rule-classes nil`. A `:rule-classes nil` lemma can serve another proof only by being named in a hint, and grep finds no such use. So nothing depends on them: they exist for their comment or as the named subject of a matrix row. Ten are mentioned nowhere outside their own form, not in planning, specs, docs, tools or tests:

| lemma | book:line | book dependents |
|---|---|---:|
| `fn-pb-existing-action-is-duplicate-iff-same-article-by-definition` | poster-bytes-invariants.lisp:214 | 2 |
| `fn-sn-existing-action-is-conflict-iff-held-binding-differs-by-definition` | store-node-existing-invariants.lisp:20 | 2 |
| `fn-sn-existing-action-is-missing-iff-no-held-binding-by-definition` | store-node-existing-invariants.lisp:31 | 2 |
| `fn-nntp-msgid-local-number-by-definition` | nntp-list-counts.lisp:301 | 3 |
| `fn-bpnp-uncertain-attempt-row-is-a-forward-candidate-by-definition` | bp-node-forward-retry.lisp:56 | 4 |
| `fn-own-sub-stored-octets-of-a-transit-submission-by-definition` | owner-served-invariants.lisp:85 | 15 |
| `fn-bpah-pending-decision-at-ready-is-live-by-definition` | bp-app-handoff-time.lisp:116 | 60 |
| `fn-bpah-uncertain-delivery-fences-step-by-definition` | bp-node-foundation.lisp:688 | 110 |
| `fn-hsig-authorization-binds-complete-profile-by-definition` | hybrid-signature.lisp:119 | 420 |
| `fn-hsig-authorization-binds-observed-ml-key-by-definition` | hybrid-signature.lisp:126 | 420 |

The other 17 `:rule-classes nil` lemmas are the named subjects of ledger, spec or handoff lines, for example `fn-pb-an-unheld-message-id-is-a-new-article-by-definition` (ledger.md) and `fn-bs-run-stops-at-first-error-by-definition` (specs/crash-model-v2.md). Their names are honest; keep them. The first five of the ten can go on the next edit of their books for 2 to 4 roots each. The two in hybrid-signature cost 420 roots each and should ride with the next substantive change to that book.

### 1d. The Python host (tools/run_store.py)

D07 (planning/decisions.md:52) decides that no Python runs in the deployed node and that Python stays as a development oracle. The "one owner per decision" rule still forbids Python computing a value ACL2 computes. The 2026-09-18 twins table (review-2026-09-18-independent.md:127-131) is mostly closed: identity is ACL2's (`metadata`, run_store.py:1552, calls `subject_id`/`obligation_id`), group codes are ACL2's (:1581), the charge is ACL2's (:1594), and duplicate/conflict goes through `fn-pb-existing-action`. What remains:

| Python | ACL2 owner | kind |
|---|---|---|
| `peer_listing` (run_store.py:1689-1724) renders each peer line field by field in Python. It lacks the D23 `carries-principal=`, `carries=` and `releases-for=` words the native `peer list` prints. | `fn-native-admin-peer-list-octets` (books/native-admin.lisp:856), with `fn-native-admin-peer-extra-decode-lists-exactly-the-rows` | rendering; already diverged |
| `config_record_path` (run_store.py:958-959), `"{:08d}.cfg"` | `fn-native-admin-config-name` (native-admin.lisp:1290); the native host names through `fn-native-admin-host-config-name` (host/native/io.lisp:1118) | naming |
| `generation = store.config_generation + 1` (run_store.py:1642, 1675, 1751, 1820) | the native host reads `fn-owner-config-generation` (host/native/admin.lisp:125) | allocation |
| `records_count >= store.config["max_transactions"]` (run_store.py:1932), `len(files) >= ...` (:1162) | `fn-sbud-` budget verdict (store-budget-naming; the native owner asks `fn-sbud-post-boundary` and `fn-sbud-prepare`) | bounds |
| `SEQ_NAME` regex (run_store.py:100, used :546, :1164) | `fn-sbud-txn-name` / `fn-bs-txn-name` | naming |
| profile constants `MAX_TRANSACTION_COUNT = 128`, `STORE_EVENT_RECORD_BYTES`, `SCALE_TRANSACTION_COUNT = 4096` (run_store.py:34-80) | the persisted profile decoded by `fn-bs-config-decode` | bounds |
| `validate_post_boundary`'s verdict-to-message table (run_store.py:1599-1614), plus the result lines at :1682 and :1753 | ACL2 already renders refusal words natively (`fn-pa-served-word`, `fn-olog-*`) | rendering |
| `metadata`'s third value `b"unsigned-legacy-v0"` (run_store.py:1576), read by run_bp_ingress.py and run_bp_receive.py | `fn-prov-make-bp` (the open w10/provenance item the docstring names) | provenance label |

None of these has an ACL2 dependent. Retiring them is host and tools work with no recertification (0 roots).

## 2. Include fan-in

144 books under `books/` have more than 100 dependents. For each one, the appendix table gives:
- the names it defines;
- how many of those any transitive dependent names;
- a *shape*: the names that some dependent with 100 or more dependents names, closed downward over the book's own internal calls;
- the *rest*: every other name;
- how many dependents a change confined to the rest would recertify.

The table comes from `table.py`. The base of the graph (cbor 718, defrecord 648, records-shape 619, records 553, acceptance 547 and so on) is fan-in by nature: the heavy dependents use its central recognizers. The movable fan-in sits in mid-level books whose count comes from one or two bridge includes. `passthru.py` finds 89 include edges into books with more than 30 dependents where the includer names none of the included book's definitions. Most go into theorem-only books (`-invariants`, `-attach`), where the rules may be exactly what the includer needs. The ones into books that define functions are the candidates.

### 2a. The three most-changed books today

**records-shape: 619 dependents, changed in 2 commits today.** It has five direct includers (`direct.py`):

| includer | its dependents | records-shape names it uses |
|---|---:|---:|
| records | 553 | 22, including `fn-record-group-namep` |
| acceptance | 547 | 1 (`fn-record-stampp`) |
| records-seam | 434 | 5 |
| records-stamp | 416 | 2 |
| the test book | 1 | 8 |

Today's change (the RFC 5536 §3.1.4 group-name grammar, `git diff 43ce09c3 HEAD -- books/records-shape.lisp`, +184 lines) touched 15 forms. Their upward closure is 19 names, and it includes `fn-record-group-namep`, which records uses. Any split still recertifies **555** books for such a change (est. 861 s). Today's run for it was 999.6 s on hbox (`certify-20260924T153508Z`, 560 books, 2 jobs).

What a split can save is the spec and theorem half. These forms have no dependent that names them, apart from native-admin naming the spec function:
- the ABNF spec `fn-record-group-name-grammarp`, `fn-record-group-component-listp` and `fn-record-group-first-component`;
- `fn-record-group-namep-is-the-rfc-5536-grammar`;
- the four `-rejects-*` teeth;
- `-bounds-length-by-definition`;
- the two `octets-aux` lemmas.

In a leaf `records-group-name-grammar` book, an edit to any of them recertifies **18** books (native-admin's 16, the leaf, its test; est. 33.8 s) instead of 619 (est. 898.6 s). The comment-only edit of the stale-comments lane cost 889.8 s over 628 books (`certify-20260925T004450Z`). No split helps that. Batching comment edits into the next substantive recertification of the same book does.

**injection: 423 dependents, one D25 change today (+111/-39 lines).** Two low books carry its count:
- hybrid-carrier (417 dependents) uses 4 injection names: `*fn-inj-date-name*`, `*fn-inj-from-name*`, `*fn-inj-subject-name*` and `fn-inj-single-fieldp` (hybrid-carrier.lisp:164-166).
- hybrid-store (415 dependents) uses 7: `fn-inj-proto-reason`, `fn-inj-mandatory-reason` and `fn-inj-nth` (hybrid-store.lisp:26-32, inside `fn-hsig-authored-source-fields`), plus `fn-inj-decide`, `fn-inj-refuse`, `fn-inj-injectedp` and `fn-inj-decision-octets` (:214-222, :338-339, in `fn-hsig-injected-carrier-plan`/`-octets` and `fn-hsig-authorized-injected-carried-submission-event`).
- hybrid-store is then included by replay (383) and topic-history-metadata (410).

Proposed split:
1. An `injection-shape` book holds the downward closure of those proto-article checks: 13 names at injection.lisp:80-621 (`*fn-inj-date-name*`, `*fn-inj-from-name*`, `*fn-inj-subject-name*`, `*fn-inj-path-name*`, `*fn-inj-injection-date-name*`, `fn-inj-car`, `fn-inj-cdr`, `fn-inj-nth`, `fn-inj-absentp`, `fn-inj-from-validp`, `fn-inj-single-fieldp`, `fn-inj-proto-reason`, `fn-inj-mandatory-reason`). hybrid-carrier and hybrid-store include only this book.
2. A `hybrid-store-injected` book above both holds the three `fn-hsig-injected-*` definitions. Their only book dependents are hybrid-store-invariants (:34, :64) and hybrid-store-tests; `fn-hsig-authored-source-fields`, which stays, calls none of them (upward closure checked by `users.py`).

After the split, injection's dependents are **216** (est. 456 s, against est. 742 s and the measured 770.7 s at persvati `certify-20260924T230829Z`, 429 books, 2 jobs; hbox took 471.2 s at 4 jobs, `certify-20260925T001652Z`). Today's D25 forms (`fn-inj-prefix`, `fn-inj-decide`, `fn-inj-source-of`, `fn-inj-reinjectionp`, `fn-inj-strip-optional`, `fn-inj-source-after-stamp`) are all outside the shape, so today's change would have cost 216 books.

The remaining 216 are intrinsic: injection-invariants (192 dependents) names 73 injection names, and `fn-inj-decide` is used by nntp-post (187) and owner (158). The injection inverse on its own (source-of, reinjectionp, strip-optional, source-after-stamp) has users whose closure is 193, because injection-invariants and owner use `fn-inj-reinjectionp`.

**native-admin: 16 dependents, 11 `--affected-by` runs today.** Its includers are:
- native-control (9 dependents; the argv constants and `fn-native-admin-argvp`);
- native-operator (3; `fn-native-admin-plan`, the result accessors, `-group-name-reservedp`, `-some-group-name-reservedp`);
- native-hybrid-control (2; the decimal parser);
- native-config-observation (2; `fn-native-admin-config-name`);
- its test book.

Today's changes touched 65 of its 111 forms, with an upward closure of 66. Every form they touch is used only by native-operator and the tests, so **5** books would recertify (est. 21.1 s against est. 33.5 s). The measured runs were 42.1 to 52.8 s (hbox `012235Z` 44.8 s, `013506Z` 52.8 s; persvati `010501Z` 42.1 s).

The bigger lever is the book's own wall, the critical path. It grew from 5.7 s (hbox `certify-20260924T150908Z`) to 11.4 s (hbox `certify-20260925T013506Z`) as the peer, BP-boundary and group-name families landed. The proposed shape is the 45 names not touched today (argv, decimal, config-name, result accessors). The peer and BP-boundary parsers are named by no book dependent, so they could become sibling books that certify in parallel under `fn-native-admin-plan`. Per-form proof times are not recorded, so this report claims no number for that part.

### 2b. The other named heavy books

- **peer-inbound: 184 dependents.** Dependents name 64 of its 116 names. nntp-auth (179) names 30. A change confined to the 45 names no heavy dependent uses would recertify 1 book. peer-inbound also includes node-config (peer-inbound.lisp:56) and nntp-pinned-effects (:58) without naming any of their definitions. Narrowing the node-config edge to node-config's own includes would take node-config from **213 to 87** (est. 464 → 173 s). nntp-pinned-effects is theorem-only (11 theorems), so its edge stays until a certification shows its rules are unused.
- **owner: 158 dependents, changed in 2 commits today.** bp-native-app (bp-native-app.lisp:4, 81 dependents) includes owner and names none of its 232 names. Narrowing that edge takes owner from **158 to 78** (est. 369 → 168 s).
- **store-node: 279.** store-node-invariants (256) names 49 of its 181 names and bp-ingress (105) names 8. The shape is 64 names, the rest 117, and a rest-only change would recertify 86 (est. 546 → 179 s). The rest includes the six unreached definitions of 1b.
- **hybrid-store: 415.** topic-history-metadata (topic-history-metadata.lisp:4) includes it and names none of its 20 names. Narrowing gives 389. replay names only `fn-hsig-article-event-carried-bindsp` and `-snapshot-bindsp`.
- **replay: 383.** store-files (344) names 5 of its names and config-records (214) names 6. Shape 30, rest 27, rest dependents 11.
- **nntp-responses: 214.** Dependents name 123 of 173. The shape is 167, so its fan-in is intrinsic. Today's response-line run was 452.6 s at persvati (`certify-20260924T214755Z`, 204 books).

### 2c. Summary for the three hot books

| book | dependents today | after the proposed split | edit-to-verdict today (measured) | after (estimated) |
|---|---:|---:|---|---|
| records-shape | 619 | 555 for a recognizer change; 18 for a spec or theorem change | 889.8 s (persvati, 628 books), 999.6 s (hbox, 560 books) | 861 s; 34 s |
| injection | 423 | 216 | 770.7 s (persvati, 429 books, 2 jobs) | 456 s |
| native-admin | 16 | 5 | 42.1 to 52.8 s | 21 s plus about 10 to 20 s of run overhead |

## Ranked packets

The first four save certification time on every later change. They are ranked by seconds saved per change, weighted by how often the book changed today. The last four are assurance and housekeeping packets whose saving is about 0 s per change; they are ranked by cost, cheapest first. Every split needs its certification (and a pcert Convert wave) before it counts, because implicit rule use is invisible to this analysis. New book names keep their existing prefixes (`fn-inj-`, `fn-hsig-`, `fn-record-`, `fn-native-admin-`), so docs/prefixes.md only gains book names.

1. **Split injection.** Create `injection-shape` (13 names) and `hybrid-store-injected` (3 definitions).
   - Dependents: 423 → 216.
   - Theorems: none restated; hybrid-store-invariants `fn-hsig-injected-carrier-retains-exact-signed-source` (:34) and `fn-hsig-injected-carrier-is-a-news-injection` (:64) include the new book.
   - Benefit: about 286 s per injection change (est. 742 → 456 s; measured today 770.7 s). One-time cost: 423 books, est. 742 s.
2. **Narrow two zero-name includes.** bp-native-app.lisp:4 (owner) and peer-inbound.lisp:56 (node-config) each include their book's own includes instead.
   - Dependents: owner 158 → 78; node-config 213 → 87.
   - Theorems: none.
   - Benefit: about 201 s per owner change (2 today) and about 291 s per node-config change (0 today). One-time cost: 184 books (bp-native-app's 81 lie inside peer-inbound's closure), est. 417 s.
3. **Leaf `records-group-name-grammar`.** It holds the ABNF spec, `fn-record-group-namep-is-the-rfc-5536-grammar`, the four `-rejects-*` teeth, `-bounds-length-by-definition` and the two `octets-aux` lemmas.
   - Dependents for a spec or theorem edit: 619 → 18. For a recognizer edit: 555, no gain.
   - Theorems: moved, not restated.
   - Benefit: about 865 s per spec or theorem-only edit; 0 s for today's kind of change. One-time cost: 619 books, est. 899 s. Batch it with the next records-shape change.
4. **Split native-admin.** A 45-name shape for native-control, native-hybrid-control and native-config-observation; the plan families stay for native-operator.
   - Dependents: 16 → 5.
   - Theorems: none restated.
   - Benefit: about 12 s per change by estimate (33.5 → 21.1 s). The book had 11 runs today, so about 130 s a day. Parallel sibling books would add a critical-path saving that is not measured.
5. **Two bridge theorems, each in a new leaf book.** (a) `fn-cpo-open-observed` success equals `fn-sn-open-observed` with configuration installed. (b) `fn-hc-authored-source` is invariant under this agent's injection for a source satisfying `fn-hc-required-sourcep`.
   - Dependents: about 2 each (book + test).
   - Theorems: gives the host subject to the 11 cited K4-family statements (PRF-007, -036, -041) without restating any; ties the signature preimage to the D25 inverse.
   - Benefit: 0 s per change; closes rule 1 ("the theorem subject is the function the host calls") for K4. Cost: about 5 s each.
6. **Retire the Python host's twins.** Move `peer_listing`, `.cfg` naming, generation allocation, the transaction bound, `SEQ_NAME`, the profile constants and the verdict text onto their ACL2 owners, and delete the `fn-store-post-boundary` alias (host/store-host.lisp:426).
   - Dependents: 0 roots.
   - Theorems: none.
   - Benefit: 0 s; closes the one-owner rule for tools/run_store.py.
7. **Delete the leaf twins.**
   - `fn-bpiw-attempt-record`: 7 roots, est. 8.2 s. Delete the test theorem at bp-request-plan-tests.lisp:122.
   - The three `fn-pix-` copies: 12 roots, est. 29.1 s. Delete peer-offer-indexed.lisp:134, :209, :277; restate peer-guard-carried.lisp:116 over `fn-peer-decide-offer`; re-hint :207.
   - The five unmentioned `-by-definition` lemmas in books with 2 to 4 dependents (1c).
   - Theorems: as listed, all uncited.
   - Benefit: 0 s per change. Total one-time cost about 45 s.
8. **Piggyback cleanups.** Move `fn-sn-existing-action` into poster-bytes; delete store-node-existing-invariants and `fn-sn-make-v3`/`-v4`/`-v5`; delete the two `fn-hsig-authorization-binds-*-by-definition` lemmas; fix the stale reclaim-plan sentence in proofs.json.
   - Dependents: 279 (store-node) and 420 (hybrid-signature). Do this only inside the next substantive change to those books: alone it costs est. 546 s and 741 s.
   - Theorems: `fn-pb-existing-action-refines-the-byte-identity-decision` keeps its statement; three uncited store-node lemmas and two hybrid-signature lemmas are deleted.
   - Benefit: 0 s per change; 0 s marginal if batched.

## Appendix A: fan-in table (books with more than 100 dependents)

"est. s now" is the estimated wall at 2 jobs for a change to the book as it is. "est. s rest-change" is the estimate for a change confined to the rest after a shape split.

| book | dependents (dry-run) | names defined | names any dependent references | shape (heavy-used, downward-closed) | rest | dependents of rest | est. s now | est. s rest-change |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| `cbor` | 718 | 49 | 34 | 36 | 13 | 1 | 976 | 0 |
| `defrecord` | 648 | 18 | 2 | 18 | 0 | 1 | 918 | 0 |
| `cbor-invariants` | 622 | 37 | 18 | 35 | 2 | 1 | 922 | 1 |
| `records-shape` | 619 | 70 | 50 | 51 | 19 | 18 | 899 | 34 |
| `acceptance-alloc` | 565 | 23 | 22 | 21 | 2 | 13 | 850 | 8 |
| `records` | 553 | 31 | 18 | 23 | 8 | 3 | 860 | 8 |
| `wildmat` | 548 | 87 | 61 | 58 | 29 | 5 | 857 | 10 |
| `acceptance` | 547 | 32 | 19 | 18 | 14 | 3 | 841 | 5 |
| `records-invariants` | 545 | 30 | 15 | 28 | 2 | 1 | 854 | 3 |
| `clock` | 513 | 29 | 17 | 20 | 9 | 1 | 827 | 0 |
| `frame-octets` | 503 | 41 | 30 | 41 | 0 | 1 | 818 | 0 |
| `crypto-seam` | 501 | 28 | 10 | 16 | 12 | 3 | 808 | 8 |
| `article` | 499 | 75 | 48 | 50 | 25 | 1 | 808 | 1 |
| `frame-fields` | 499 | 62 | 43 | 46 | 16 | 1 | 816 | 2 |
| `provenance` | 494 | 46 | 9 | 9 | 37 | 83 | 802 | 205 |
| `retention` | 491 | 26 | 19 | 17 | 9 | 4 | 799 | 8 |
| `node` | 488 | 15 | 12 | 12 | 3 | 1 | 798 | 0 |
| `frame-journal` | 485 | 45 | 33 | 36 | 9 | 104 | 800 | 219 |
| `frame` | 484 | 10 | 8 | 8 | 2 | 1 | 800 | 2 |
| `statement-items` | 483 | 9 | 9 | 9 | 0 | 1 | 794 | 1 |
| `statement-codec` | 482 | 31 | 9 | 17 | 14 | 1 | 793 | 2 |
| `statement-seam` | 481 | 8 | 8 | 7 | 1 | 5 | 792 | 14 |
| `acceptance-invariants` | 480 | 37 | 8 | 22 | 15 | 9 | 785 | 16 |
| `statement` | 473 | 94 | 62 | 73 | 21 | 1 | 787 | 2 |
| `statement-invariants` | 470 | 57 | 16 | 38 | 19 | 12 | 785 | 12 |
| `article-fields` | 469 | 42 | 18 | 37 | 5 | 1 | 786 | 1 |
| `principal` | 464 | 36 | 28 | 12 | 24 | 13 | 780 | 11 |
| `stx-carrier` | 461 | 61 | 29 | 30 | 31 | 6 | 777 | 6 |
| `stx-verify` | 458 | 42 | 19 | 29 | 13 | 1 | 775 | 1 |
| `node-invariants` | 445 | 21 | 10 | 13 | 8 | 8 | 755 | 13 |
| `records-canonicality` | 437 | 35 | 11 | 31 | 4 | 9 | 752 | 22 |
| `identity` | 436 | 32 | 26 | 32 | 0 | 1 | 755 | 0 |
| `records-seam` | 434 | 12 | 3 | 0 | 12 | 15 | 748 | 48 |
| `lace` | 431 | 26 | 22 | 25 | 1 | 1 | 747 | 1 |
| `lace-invariants` | 429 | 63 | 10 | 7 | 56 | 8 | 745 | 7 |
| `stx-lace` | 425 | 26 | 12 | 9 | 17 | 5 | 742 | 5 |
| `hybrid-profile` | 424 | 1 | 1 | 1 | 0 | 1 | 744 | 0 |
| `mailbox` | 424 | 24 | 1 | 21 | 3 | 1 | 742 | 0 |
| `injection` | 423 | 108 | 82 | 94 | 14 | 39 | 742 | 67 |
| `hybrid-signature` | 420 | 21 | 17 | 11 | 10 | 7 | 742 | 10 |
| `stx-evidence-records` | 419 | 21 | 9 | 17 | 4 | 2 | 738 | 3 |
| `hybrid-carrier` | 417 | 48 | 18 | 38 | 10 | 2 | 737 | 3 |
| `stx-keyring-records` | 417 | 26 | 19 | 23 | 3 | 2 | 737 | 3 |
| `records-stamp` | 416 | 3 | 2 | 1 | 2 | 7 | 736 | 14 |
| `stx-accept-records` | 416 | 14 | 8 | 14 | 0 | 1 | 736 | 1 |
| `hybrid-store` | 415 | 20 | 16 | 10 | 10 | 37 | 737 | 50 |
| `topic-history-metadata` | 410 | 36 | 28 | 31 | 5 | 16 | 730 | 18 |
| `topic-history-authorship` | 406 | 9 | 3 | 4 | 5 | 1 | 725 | 2 |
| `consumer-position` | 404 | 90 | 34 | 33 | 57 | 11 | 720 | 16 |
| `topic-history-admission` | 403 | 24 | 11 | 19 | 5 | 3 | 722 | 7 |
| `topic-history-local-admin` | 401 | 11 | 9 | 5 | 6 | 13 | 720 | 15 |
| `consumer-store-events` | 400 | 17 | 9 | 16 | 1 | 1 | 717 | 1 |
| `topic-history-store-events` | 400 | 18 | 10 | 14 | 4 | 1 | 718 | 2 |
| `store-events` | 398 | 28 | 25 | 22 | 6 | 45 | 716 | 80 |
| `retention-invariants` | 389 | 18 | 5 | 15 | 3 | 1 | 704 | 0 |
| `node-retention-transitions` | 384 | 18 | 6 | 15 | 3 | 1 | 699 | 0 |
| `replay` | 383 | 57 | 34 | 30 | 27 | 11 | 699 | 15 |
| `store-files` | 344 | 80 | 62 | 60 | 20 | 15 | 640 | 52 |
| `store-files-invariants` | 342 | 67 | 28 | 40 | 27 | 27 | 638 | 60 |
| `stx-reader` | 332 | 9 | 6 | 6 | 3 | 1 | 619 | 1 |
| `frame-invariants` | 312 | 63 | 11 | 49 | 14 | 21 | 585 | 49 |
| `sha256` | 298 | 59 | 5 | 34 | 25 | 1 | 568 | 5 |
| `crypto-attach` | 296 | 8 | 2 | 1 | 7 | 45 | 565 | 115 |
| `consumer-event-index` | 283 | 27 | 10 | 7 | 20 | 24 | 550 | 38 |
| `topic-history-prefix` | 283 | 8 | 5 | 5 | 3 | 6 | 552 | 15 |
| `stx-index` | 282 | 55 | 17 | 22 | 33 | 4 | 549 | 6 |
| `consumer-store-projection` | 281 | 6 | 5 | 4 | 2 | 15 | 550 | 30 |
| `store-node` | 279 | 181 | 73 | 64 | 117 | 86 | 546 | 179 |
| `wire` | 263 | 123 | 77 | 79 | 44 | 33 | 507 | 62 |
| `nntp-syntax` | 258 | 60 | 45 | 54 | 6 | 1 | 505 | 0 |
| `store-node-invariants` | 256 | 71 | 29 | 41 | 30 | 15 | 519 | 33 |
| `topic-history-identity-disjoint` | 256 | 4 | 4 | 4 | 0 | 1 | 520 | 2 |
| `store-files-traces` | 248 | 64 | 18 | 42 | 22 | 39 | 508 | 66 |
| `config` | 231 | 188 | 90 | 119 | 69 | 9 | 484 | 14 |
| `store-node-traces` | 222 | 76 | 38 | 40 | 36 | 81 | 474 | 170 |
| `nntp-session` | 219 | 36 | 33 | 35 | 1 | 1 | 450 | 0 |
| `msgid-index` | 218 | 35 | 13 | 11 | 24 | 20 | 449 | 31 |
| `nntp-projection` | 218 | 45 | 23 | 23 | 22 | 1 | 449 | 1 |
| `bp-workflow` | 217 | 111 | 111 | 98 | 13 | 41 | 425 | 40 |
| `index` | 217 | 56 | 20 | 17 | 39 | 2 | 447 | 0 |
| `store-node-resolution` | 216 | 43 | 22 | 19 | 24 | 78 | 463 | 163 |
| `nntp-index-runtime` | 215 | 20 | 16 | 18 | 2 | 1 | 447 | 0 |
| `config-invariants` | 214 | 32 | 2 | 0 | 32 | 3 | 465 | 3 |
| `config-records` | 214 | 31 | 11 | 6 | 25 | 3 | 465 | 4 |
| `group-bucket-index` | 214 | 34 | 18 | 21 | 13 | 5 | 447 | 12 |
| `nntp-responses` | 214 | 173 | 123 | 167 | 6 | 1 | 448 | 2 |
| `group-bucket-article` | 213 | 6 | 4 | 2 | 4 | 7 | 447 | 16 |
| `node-config` | 213 | 53 | 25 | 0 | 53 | 91 | 464 | 180 |
| `byte-store` | 212 | 69 | 58 | 59 | 10 | 1 | 394 | 0 |
| `nntp-range-indexed` | 212 | 3 | 2 | 2 | 1 | 1 | 446 | 1 |
| `nntp-verdict` | 212 | 7 | 6 | 5 | 2 | 7 | 447 | 17 |
| `path` | 212 | 27 | 9 | 27 | 0 | 1 | 459 | 0 |
| `nntp` | 211 | 13 | 12 | 12 | 1 | 1 | 446 | 3 |
| `store-observed` | 211 | 56 | 23 | 9 | 47 | 113 | 456 | 221 |
| `peer-config` | 209 | 50 | 24 | 25 | 25 | 34 | 458 | 64 |
| `byte-store-invariants` | 208 | 122 | 51 | 88 | 34 | 23 | 392 | 52 |
| `nntp-index` | 204 | 39 | 10 | 5 | 34 | 8 | 438 | 17 |
| `nntp-overview` | 204 | 25 | 10 | 19 | 6 | 1 | 438 | 2 |
| `group-bucket-cursor-invariants` | 201 | 2 | 2 | 2 | 0 | 1 | 436 | 2 |
| `identity-invariants` | 201 | 33 | 6 | 4 | 29 | 3 | 434 | 4 |
| `nntp-invariants` | 201 | 101 | 10 | 13 | 88 | 63 | 435 | 136 |
| `nntp-legacy` | 196 | 21 | 11 | 13 | 8 | 1 | 430 | 3 |
| `nntp-newnews` | 195 | 12 | 6 | 4 | 8 | 2 | 428 | 4 |
| `nntp-effects` | 194 | 153 | 17 | 19 | 134 | 55 | 428 | 142 |
| `injection-invariants` | 192 | 36 | 14 | 2 | 34 | 68 | 425 | 141 |
| `group-bucket-invariants` | 190 | 7 | 3 | 6 | 1 | 1 | 423 | 2 |
| `nntp-post` | 187 | 45 | 27 | 26 | 19 | 62 | 421 | 135 |
| `nntp-verdict-effects` | 187 | 5 | 1 | 1 | 4 | 1 | 420 | 2 |
| `path-update` | 186 | 38 | 28 | 26 | 12 | 8 | 418 | 16 |
| `provenance-codec` | 186 | 38 | 7 | 21 | 17 | 8 | 419 | 17 |
| `nntp-pinned-effects` | 185 | 11 | 0 | 0 | 11 | 1 | 418 | 2 |
| `peer-inbound` | 184 | 116 | 64 | 71 | 45 | 1 | 417 | 10 |
| `scheduler` | 182 | 80 | 55 | 1 | 79 | 5 | 394 | 9 |
| `auth-secret` | 181 | 29 | 11 | 10 | 19 | 23 | 407 | 39 |
| `byte-store-scan` | 180 | 126 | 71 | 1 | 125 | 38 | 359 | 69 |
| `frame-trailer` | 180 | 8 | 5 | 0 | 8 | 128 | 351 | 269 |
| `nntp-auth` | 179 | 137 | 76 | 63 | 74 | 79 | 406 | 166 |
| `records-attach` | 178 | 0 | 0 | 0 | 0 | 1 | 263 | 1 |
| `peer-feed` | 177 | 148 | 95 | 109 | 39 | 2 | 389 | 3 |
| `statement-attach` | 176 | 0 | 0 | 0 | 0 | 1 | 262 | 1 |
| `codec-attach` | 175 | 0 | 0 | 0 | 0 | 1 | 262 | 1 |
| `wire-invariants` | 175 | 59 | 16 | 1 | 58 | 74 | 392 | 153 |
| `feed-events` | 172 | 21 | 20 | 16 | 5 | 8 | 384 | 9 |
| `peer-feed-invariants` | 172 | 121 | 7 | 4 | 117 | 6 | 386 | 12 |
| `byte-store-frame` | 169 | 41 | 32 | 0 | 41 | 45 | 342 | 78 |
| `owner-feed` | 169 | 140 | 54 | 49 | 91 | 14 | 382 | 21 |
| `served` | 168 | 152 | 58 | 34 | 118 | 78 | 386 | 165 |
| `owner` | 158 | 232 | 136 | 0 | 232 | 78 | 369 | 168 |
| `bp-adu` | 156 | 67 | 43 | 47 | 20 | 26 | 298 | 30 |
| `bp-primary-cbor` | 148 | 101 | 43 | 92 | 9 | 1 | 291 | 7 |
| `bp-primary` | 147 | 107 | 75 | 90 | 17 | 48 | 287 | 128 |
| `byte-store-txn-name` | 140 | 30 | 15 | 0 | 30 | 130 | 286 | 270 |
| `bp-primary-invariants` | 131 | 34 | 8 | 8 | 26 | 8 | 268 | 22 |
| `bp-bundle` | 127 | 62 | 38 | 38 | 24 | 60 | 262 | 149 |
| `bp-bundle-invariants` | 126 | 23 | 2 | 1 | 22 | 3 | 261 | 5 |
| `bp-node` | 124 | 33 | 19 | 7 | 26 | 61 | 258 | 151 |
| `journal-publish` | 123 | 18 | 11 | 0 | 18 | 123 | 260 | 260 |
| `bp-node-machine` | 120 | 82 | 63 | 44 | 38 | 43 | 255 | 106 |
| `article-invariants` | 115 | 58 | 5 | 2 | 56 | 2 | 238 | 6 |
| `article-properties` | 112 | 42 | 1 | 9 | 33 | 1 | 235 | 2 |
| `bp-node-foundation` | 110 | 80 | 60 | 0 | 80 | 110 | 241 | 241 |
| `bp-signed-receipt` | 110 | 17 | 9 | 14 | 3 | 3 | 242 | 10 |
| `bp-ingress` | 105 | 68 | 42 | 6 | 62 | 21 | 232 | 29 |
| `bp-receipt` | 102 | 84 | 45 | 0 | 84 | 102 | 229 | 229 |

## Appendix B: unreached definitions by book

From `sweep.py`: definitions reached neither from `host/native`, nor from a `host/*.lisp` book, nor from a statement cited in `planning/proof-events.json`. Candidates only; see 1b for the classes that are not deletions.

| book | dependents | unreached | names (first four) |
|---|---:|---:|---|
| `ideal` | 1 | 16 | `fn-ideal-clock`, `fn-ideal-config`, `fn-ideal-conn-alistp`, `fn-ideal-conn-find` |
| `transfer-assembly-invariants` | 1 | 3 | `fn-transfer-assemble-from-nth-induct`, `fn-transfer-missing-ranges-correct-fromp`, `fn-transfer-nat-induct` |
| `wildmat-work` | 1 | 2 | `fn-wm-pattern-list-induct`, `fn-wm-total-items` |
| `acceptance-stamp-invariants` | 2 | 4 | `fn-articles-msgid-stamps`, `fn-replay-article-eventp`, `fn-replay-article-record`, `fn-replay-journal-article-stamps` |
| `anchor-servers` | 2 | 1 | `fn-anchor-server-namep` |
| `bp-native-app-fast` | 2 | 1 | `fn-bpaj-config-status` |
| `bp-receive-evidence` | 2 | 1 | `fn-bpn-evidence-kindp` |
| `bp-receiver-evolving-store-invariants` | 2 | 3 | `fn-bpr-live-journal`, `fn-bpr-live-state`, `fn-bpr-live-store` |
| `bp-release-replay-status` | 2 | 1 | `fn-bprl-durable-fold` |
| `bp-sequence-fidelity` | 2 | 1 | `fn-bpn-sf-initial` |
| `bp-sequence-persistence` | 2 | 20 | `fn-bpn-sp-authored`, `fn-bpn-sp-authors-belowp`, `fn-bpn-sp-directoryp`, `fn-bpn-sp-effect` |
| `bp-status-report-invariants` | 2 | 5 | `fn-bpn-report-after-header-octets`, `fn-bpn-report-after-reason-octets`, `fn-bpn-report-after-source-octets`, `fn-bpn-report-after-stamp-octets` |
| `byte-store-initializer` | 2 | 3 | `fn-bsi-existing-init-program`, `fn-bsi-history-retry-program`, `fn-bsi-publish-existing-steps` |
| `byte-store-observation-scan` | 2 | 1 | `fn-bso-txn-prefix-entry-agreesp` |
| `byte-store-retention-publication` | 2 | 1 | `fn-bsrp-record-dir-error-outcomes` |
| `checkpoint-compaction-preservation` | 2 | 1 | `fn-ccp-names-below` |
| `consumer-owner-index-invariants` | 2 | 1 | `fn-col-poll-list-reference` |
| `container-invariants` | 2 | 1 | `fn-ct-all-in-store` |
| `exchange-invariants` | 2 | 1 | `fn-exchange-ingest-trace` |
| `feed-filename` | 2 | 1 | `fn-feed-filename-layout` |
| `feed-port-replay` | 2 | 4 | `fn-feed-port-history`, `fn-feed-port-next`, `fn-feed-port-records`, `fn-feed-port-run` |
| `hybrid-signature-invariants` | 2 | 4 | `fn-hsigi-ed-key`, `fn-hsigi-ml-key`, `fn-hsigi-principal`, `fn-hsigi-source` |
| `journal` | 2 | 61 | `fn-journal-anchor-satisfiedp`, `fn-journal-anchorp`, `fn-journal-barrier`, `fn-journal-binary-choices` |
| `native-config-observation` | 2 | 4 | `fn-nco-occurrences`, `fn-nco-result-entries`, `fn-nco-result-reason`, `fn-nco-result-status` |
| `node-traces` | 2 | 1 | `fn-node-eventp` |
| `owner-log` | 2 | 1 | `fn-olog-parts-no-breakp` |
| `poster-bytes-invariants` | 2 | 2 | `fn-pb-served-reply`, `fn-pb-v1-injection` |
| `scheduler-peers` | 2 | 9 | `fn-sched-table-boundp`, `fn-sched-table-find`, `fn-sched-table-forget`, `fn-sched-table-install` |
| `store-history-marker` | 2 | 1 | `fn-hm-burnsp` |
| `stx-authority` | 2 | 3 | `fn-stx-authority-forkedp`, `fn-stx-authority-outcome`, `fn-stx-records-creator-scan` |
| `stx-epochs` | 2 | 9 | `fn-stx-commit-encodablep`, `fn-stx-commit-encode`, `fn-stx-commit-items`, `fn-stx-commit-of-statement` |
| `tcpcl-delivery-invariants` | 2 | 1 | `fn-tcl-events-after-first-bundle` |
| `tcpcl-spool` | 2 | 8 | `fn-tcl-spool-ackp`, `fn-tcl-spool-crash-before-publish`, `fn-tcl-spool-entries`, `fn-tcl-spool-recover` |
| `topic-history-metadata-invariants` | 2 | 2 | `fn-th-author-list-p`, `fn-th-parent-list-p` |
| `transfer-journal-invariants` | 2 | 1 | `fn-tj-induct` |
| `transfer-public-bound` | 2 | 7 | `fn-transfer-public-bound-for`, `fn-transfer-public-chunk-list-step-budget`, `fn-transfer-public-entry-budget`, `fn-transfer-public-overlap-budget` |
| `wildmat-matcher-invariants` | 2 | 1 | `fn-wm-row-induct` |
| `wire-outbound-invariants` | 2 | 1 | `fn-wire-source-lines-rev` |
| `bp-authored-wire` | 3 | 1 | `fn-bpn-authored-wire-operation-sequence` |
| `bp-receiver-evolving-node-invariants` | 3 | 1 | `fn-bprv-node-idlep` |
| `container` | 3 | 43 | `fn-ct-article-content-id`, `fn-ct-article-deps`, `fn-ct-article-list-shapep`, `fn-ct-article-msgid` |
| `exchange` | 3 | 10 | `fn-exchange-any-object-for-messagep`, `fn-exchange-conflicting-messagep`, `fn-exchange-conflicting-with-contentp`, `fn-exchange-fact-listp` |
| `feed-connection-invariants` | 3 | 2 | `fn-fc-gate-induct`, `fn-fc-line-bodyp` |
| `native-operator` | 3 | 1 | `fn-native-operator-resultp` |
| `nntp-list-counts` | 3 | 3 | `fn-gidx-listed-entries`, `fn-nlc-count-in`, `fn-nlc-selected-sum` |
| `tcpcl-invariants` | 3 | 1 | `fn-tcl-inbound-outcome-count` |
| `topic-history-store-invariants` | 3 | 2 | `fn-sti-completed-prefixp`, `fn-sti-livep` |
| `transfer-journal` | 3 | 31 | `fn-tj-apply`, `fn-tj-arg`, `fn-tj-candidate`, `fn-tj-code` |
| `transfer-public-work` | 3 | 19 | `fn-transfer-at-most-work`, `fn-transfer-chunk-input-work`, `fn-transfer-chunk-list-work`, `fn-transfer-chunk-work` |
| `wildmat-parser-invariants` | 3 | 1 | `fn-wm-parse-one-induct` |
| `anchor-record` | 4 | 1 | `fn-anchor-encode` |
| `article-work-budget` | 4 | 1 | `fn-aw-budget-monotone-induct` |
| `bp-node-machine-authorization` | 4 | 1 | `fn-bpn-machine-event-listp` |
| `bp-node-progress-premises` | 4 | 3 | `fn-bpnp-host-event-listp`, `fn-bpnp-host-trace`, `fn-bpnpp-defkeep` |
| `byte-store-observation` | 4 | 8 | `fn-bso-aliases-agree`, `fn-bso-aliases-agree-with`, `fn-bso-directory-agree`, `fn-bso-entry` |
| `checkpoint-pack-retire` | 4 | 4 | `fn-cprt-crash-survivors`, `fn-cprt-prefixp`, `fn-cprt-retire-program`, `fn-cprt-retire-steps` |
| `config-owner-read-invariants` | 4 | 4 | `fn-ocri-connp`, `fn-ocri-conns-p`, `fn-ocri-relation`, `fn-ocri-viewp` |
| `consumer-event-index-store-invariants` | 4 | 1 | `fn-ceis-relatedp` |
| `relay` | 4 | 32 | `fn-relay-accept`, `fn-relay-commit-receipt`, `fn-relay-content-durablep`, `fn-relay-crash-recover` |
| `store-retention-codec-invariants` | 4 | 1 | `fn-srci-retention-items` |
| `stx-policy` | 4 | 3 | `fn-stx-accept-batch`, `fn-stx-batch-delta`, `fn-stx-transit-authority-ok` |
| `transfer-work` | 4 | 2 | `fn-transfer-missing-from-work`, `fn-transfer-position-work-budget` |
| `bp-clock-domain` | 5 | 1 | `fn-bpnf-clock-domain-plan-reason` |
| `bp-workflow-records-invariants` | 5 | 3 | `fn-bp-actionable-effects`, `fn-bp-replay-rejected-recordp`, `fn-bp-trace-effects` |
| `byte-store-k0` | 5 | 2 | `fn-bs-finish-inputp`, `fn-bs-k0-cut-after-related-pair` |
| `byte-store-keystones` | 5 | 3 | `fn-bs-staging-cleanup-stepsp`, `fn-bs-staging-del`, `fn-bs-sweep-run-okp` |
| `feed-connection` | 5 | 6 | `fn-fc-lost`, `fn-fc-table-entryp`, `fn-fc-table-memberp`, `fn-fc-table-names` |
| `hybrid-lifecycle-store-invariants` | 5 | 1 | `fn-hls-current-enrollment` |
| `membership-epochs` | 5 | 48 | `fn-me-addsp`, `fn-me-adopt`, `fn-me-apply-op`, `fn-me-chain` |
| `byte-store-compaction-correspondence` | 6 | 4 | `fn-bs-exact-name-payloadp`, `fn-bs-reclaim-cut-ready-p`, `fn-bs-reclaim-program-shapep`, `fn-bs-reclaim-steps-avoid-namep` |
| `checkpoint-publish` | 6 | 18 | `fn-cpp-candidate-dir-result`, `fn-cpp-candidate-file-result`, `fn-cpp-candidate-link-result`, `fn-cpp-candidate-present-visiblep` |
| `consumer-poll-index` | 6 | 3 | `fn-col-poll-drop`, `fn-col-poll-list-window`, `fn-col-poll-window` |
| `native-auth-admin` | 6 | 5 | `fn-native-auth-admin-recovery-has-cleanup-directory-okp`, `fn-native-auth-admin-recovery-trace`, `fn-native-auth-admin-rp-has-directory-okp`, `fn-native-auth-admin-rp-has-recovery-directory-okp` |
| `owner-verdict-read` | 6 | 1 | `fn-ovr-induct` |
| `policy-invariants` | 6 | 1 | `fn-pol-first-authority-stmt` |
| `transfer-union` | 6 | 4 | `fn-transfer-overlap-position`, `fn-transfer-run-listp`, `fn-transfer-uncoveredp`, `fn-transfer-window-clearp` |
| `bp-ion-workflow` | 7 | 1 | `fn-bpiw-attempt-record` |
| `feed-wire-input` | 7 | 8 | `fn-fwi-memberp`, `fn-fwi-no-duplicatesp`, `fn-fwi-table-entryp`, `fn-fwi-table-lookup` |
| `policy` | 7 | 29 | `fn-pol-admitp`, `fn-pol-authorized-set`, `fn-pol-authorizedp`, `fn-pol-candidate-listp` |
| `anchor-replace` | 8 | 3 | `fn-anchor-rp-has-directory-okp`, `fn-anchor-rp-has-recovery-directory-okp`, `fn-anchor-rp-trace` |
| `checkpoint-codec` | 8 | 6 | `fn-cpc-current-headerp`, `fn-cpc-depth`, `fn-cpc-frame-open`, `fn-cpc-frame-seal` |
| `nntp-auth-fold` | 8 | 4 | `fn-auth-fold-fed-conn`, `fn-auth-fold-no-local-effectsp`, `fn-auth-fold-post-awaiting`, `fn-auth-fold-safe-connp` |
| `tcpcl-octets` | 8 | 2 | `fn-tcl-flag-reply`, `fn-tcl-max-message` |
| `anchor` | 9 | 9 | `fn-anchor-acceptablep`, `fn-anchor-node-accept`, `fn-anchor-node-accept-list`, `fn-anchor-node-advance` |
| `deftransition` | 9 | 4 | `fn-deftransition`, `fn-deftransition-branch-events`, `fn-deftransition-branch-names`, `fn-deftransition-closed` |
| `tcpcl-records` | 9 | 2 | `fn-tcl-parse-errorp`, `fn-tcl-result-shapep` |
| `checkpoint-compaction` | 10 | 2 | `fn-cc-partial-observationp`, `fn-cc-valid-suffixp` |
| `nntp-auth-invariants` | 10 | 2 | `fn-auth-config-no-postersp`, `fn-auth-no-posting-credsp` |
| `peer-offer-indexed` | 12 | 3 | `fn-pix-decide-offer`, `fn-pix-peer-command`, `fn-pix-peer-step-pinned` |
| `transfer` | 12 | 7 | `fn-transfer-agrees-fromp`, `fn-transfer-make-profile`, `fn-transfer-missing-from`, `fn-transfer-missing-ranges` |
| `consumer-store-invariants` | 14 | 4 | `fn-csi-completed-prefixp`, `fn-csi-completion-lastp`, `fn-csi-livep`, `fn-csi-no-crash-eventsp` |
| `bp-fnbs-byte-publisher` | 15 | 10 | `fn-bpnf-byte-after-create`, `fn-bpnf-byte-after-dir-barrier`, `fn-bpnf-byte-after-file-barrier`, `fn-bpnf-byte-after-link` |
| `bp-release` | 15 | 4 | `fn-bprl-evidencep`, `fn-bprl-replay-journal`, `fn-bprl-replay-records`, `fn-bprl-termp` |
| `byte-store-native-correspondence` | 15 | 2 | `fn-bs-native-io-operationp`, `fn-bs-native-io-resultp` |
| `native-admin` | 16 | 14 | `fn-native-admin-group-name-special-purposep`, `fn-native-admin-name-components`, `fn-native-admin-peer-after-token`, `fn-native-admin-peer-boundaryp` |
| `bp-eid-shape` | 17 | 2 | `fn-bp-eid-shape-listp`, `fn-bp-eid-vchar-octetsp` |
| `owner-prepare-correspondence` | 21 | 1 | `fn-opc-pending-octets` |
| `assumptions` | 25 | 1 | `fn-bs-torn-variantp` |
| `bp-node-debt` | 25 | 1 | `fn-bpnd-coverp` |
| `store-prepare-correspondence` | 25 | 2 | `fn-spc-run`, `fn-spc-step` |
| `native-config` | 26 | 1 | `fn-native-config-owner-clock-error-ms` |
| `served-tls-prefix` | 32 | 1 | `fn-served-step-counted` |
| `store-sweep` | 32 | 2 | `fn-sn-digit-octet-listp`, `fn-sn-final-namespace-namep` |
| `byte-store-programs` | 37 | 21 | `fn-bs-checkpoint-publish-program`, `fn-bs-checkpoint-select-program`, `fn-bs-durable-observationp`, `fn-bs-fences-authority-dirs-aux` |
| `bp-fnbs-delivery-replay` | 44 | 4 | `fn-bpah-recover-auto-event`, `fn-bpah-replay-row-record`, `fn-bpah-replay-rows`, `fn-bpah-replay-rows-aux` |
| `bp-fnbs-replay` | 47 | 4 | `fn-bpnf-recover-auto-event`, `fn-bpnf-recover-event`, `fn-bpnf-replay-rows`, `fn-bpnf-replay-rows-aux` |
| `bp-status-report` | 47 | 2 | `fn-bpn-report-assertion-listp`, `fn-bpn-report-at-most-induction` |
| `owner-config` | 55 | 2 | `fn-ocfg-cr-induct`, `fn-ocfg-list-active` |
| `bp-fragment-fast` | 60 | 3 | `fn-bpf-cut-fast`, `fn-bpf-fragment-fast`, `fn-bpf-prefix` |
| `owner-invariants` | 61 | 2 | `fn-own-conns-boundedp`, `fn-own-take-prefix-induct` |
| `bp-fragment` | 71 | 22 | `fn-bpf-agreesp`, `fn-bpf-all-agreep`, `fn-bpf-all-unfragment-to`, `fn-bpf-boundariesp` |
| `bp-app-handoff` | 72 | 11 | `fn-bpah-author-publication-authorizedp`, `fn-bpah-held-claimed-source`, `fn-bpah-held-policy-row`, `fn-bpah-held-received-from` |
| `bp-session-admission` | 77 | 8 | `fn-bpaj-admitted-principal`, `fn-bpaj-boundary-carried-sources`, `fn-bpaj-boundary-list-values`, `fn-bpaj-boundary-release-issuers` |
| `bp-native-app` | 81 | 6 | `fn-bpaj-dispatch`, `fn-bpaj-pending-receipt-resolution`, `fn-bpaj-record-lookup`, `fn-bpaj-record-matches-requestp` |
| `config-stream` | 85 | 12 | `fn-cstr-article-jrec`, `fn-cstr-article-jrecs`, `fn-cstr-article-seqs`, `fn-cstr-config-jrec` |
| `bp-ingress` | 105 | 5 | `fn-bpi-ag-dec`, `fn-bpi-durably-acceptedp`, `fn-bpi-finish-prepared`, `fn-bpi-receipt-eligibility` |
| `bp-node-foundation` | 110 | 6 | `fn-bpnf-outcome`, `fn-bpnf-outcomep`, `fn-bpnf-version-of`, `fn-bpnf-wait` |
| `article-invariants` | 115 | 14 | `fn-article-concat-lines`, `fn-article-crlf-freep`, `fn-article-field-correspondsp`, `fn-article-fields-correspondp` |
| `bp-node-machine` | 120 | 11 | `fn-bpn-contact-listp`, `fn-bpn-effect-listp`, `fn-bpn-effectp`, `fn-bpn-event-listp` |
| `journal-publish` | 123 | 1 | `fn-jpub-crash-outcome` |
| `bp-node` | 124 | 4 | `fn-bpn-forward-decision`, `fn-bpn-forwardp`, `fn-bpn-hop-limitp`, `fn-bpn-transfer-limitp` |
| `bp-bundle` | 127 | 5 | `fn-bpb-bundle-previous-node`, `fn-bpb-flag-delete-if-unprocessable`, `fn-bpb-flag-discard-if-unprocessable`, `fn-bpb-flag-replicate-in-fragments` |
| `bp-primary` | 147 | 7 | `fn-bpp-crc-width`, `fn-bpp-data-previous-node`, `fn-bpp-dtn-demux-first`, `fn-bpp-eid-singletonp` |
| `bp-primary-cbor` | 148 | 3 | `fn-bpc-cost`, `fn-bpc-shapep`, `fn-bpc-valuep` |
| `bp-adu` | 156 | 1 | `fn-bpa-byte-field-listp` |
| `owner` | 158 | 13 | `fn-own-bp-transit-outcome-records`, `fn-own-control-outcome-records`, `fn-own-feed-lost-records`, `fn-own-feed-reply-records` |
| `served` | 168 | 1 | `fn-served-result-shapep` |
| `byte-store-frame` | 169 | 5 | `fn-bs-config-okp-impl`, `fn-bs-frontier-decode-impl`, `fn-bs-frontier-encode-impl`, `fn-bs-initial-config-octets` |
| `owner-feed` | 169 | 12 | `fn-own-feed-accept`, `fn-own-feed-accept-records`, `fn-own-feed-enqueue-records-in`, `fn-own-feed-lost-records-of` |
| `feed-events` | 172 | 4 | `fn-feed-durable-projection`, `fn-feed-live-history`, `fn-feed-live-run`, `fn-feed-live-serializablep` |
| `wire-invariants` | 175 | 2 | `fn-wire-clean-line-byte-induction`, `fn-wire-clear-line-state` |
| `peer-feed` | 177 | 17 | `fn-feed-accepted-outcomep`, `fn-feed-check-linep`, `fn-feed-command-offersp`, `fn-feed-count-accepted` |
| `nntp-auth` | 179 | 3 | `fn-auth-effectp`, `fn-auth-effectsp`, `fn-auth-transit-keywordp` |
| `byte-store-scan` | 180 | 4 | `fn-bs-name-step`, `fn-bs-names-after`, `fn-bs-names-outcomes`, `fn-bs-txn-prefix-agreesp` |
| `scheduler` | 182 | 27 | `fn-sched-admit-event`, `fn-sched-aged-fitsp`, `fn-sched-aging-horizon`, `fn-sched-close-event` |
| `peer-inbound` | 184 | 4 | `fn-peer-decision-shapep`, `fn-peer-decisionp`, `fn-peer-transit-evidence`, `fn-peer-transit-provenance` |
| `path-update` | 186 | 2 | `fn-pu-crlf-endedp`, `fn-pu-has-crlfp` |
| `provenance-codec` | 186 | 2 | `fn-prov-octets`, `fn-prov-of-octets` |
| `nntp-post` | 187 | 1 | `fn-post-result-shapep` |
| `injection-invariants` | 192 | 1 | `fn-inj-instantp` |
| `nntp-effects` | 194 | 2 | `fn-nntp-block-textp`, `fn-nntp-octet-linesp` |
| `nntp-legacy` | 196 | 2 | `fn-nntp-hdr-clean-field-listp`, `fn-nntp-xpat-selects-everythingp` |
| `nntp-index` | 204 | 1 | `fn-nntp-available-numbers` |
| `nntp-overview` | 204 | 3 | `fn-nov-clean-fieldp`, `fn-nov-field-octetp`, `fn-nov-overviewp` |
| `byte-store-invariants` | 208 | 6 | `fn-bs-all-new`, `fn-bs-apply-entries`, `fn-bs-apply-writes`, `fn-bs-entry-after` |
| `store-observed` | 211 | 2 | `fn-sn-open-code`, `fn-sn-open-errorp` |
| `byte-store` | 212 | 1 | `fn-bs-read` |
| `group-bucket-article` | 213 | 1 | `fn-gidx-number-article` |
| `node-config` | 213 | 4 | `fn-cnode-complete`, `fn-cnode-prepare`, `fn-cnode-recover`, `fn-cnode-served` |
| `config-invariants` | 214 | 1 | `fn-cfg-take` |
| `config-records` | 214 | 9 | `fn-config-aware-config`, `fn-config-aware-loop`, `fn-config-aware-replay`, `fn-config-aware-result` |
| `nntp-responses` | 214 | 22 | `fn-nntp-blind-env`, `fn-nntp-dt-alphap`, `fn-nntp-dt-date`, `fn-nntp-dt-day` |
| `bp-workflow` | 217 | 2 | `fn-bp-eventp`, `fn-bp-no-contact-event` |
| `index` | 217 | 1 | `fn-index-entry-key` |
| `msgid-index` | 218 | 4 | `fn-midx-branch-keys`, `fn-midx-lookup-put-induct`, `fn-midx-string-article-listp`, `fn-midx-unique-branchesp` |
| `nntp-projection` | 218 | 1 | `fn-nntp-orderedp` |
| `store-node-traces` | 222 | 1 | `fn-snt-run` |
| `config` | 231 | 16 | `fn-cfg-endpoint-address`, `fn-cfg-item-listp`, `fn-cfg-limit`, `fn-cfg-peer-contact-plan` |
| `store-files-traces` | 248 | 1 | `fn-sf-trace-make` |
| `wire` | 263 | 7 | `fn-wire-begin-article-refusedp`, `fn-wire-continue`, `fn-wire-feed`, `fn-wire-feed-byte-reference` |
| `store-node` | 279 | 6 | `fn-sn-existing-action`, `fn-sn-fence-node`, `fn-sn-make-v3`, `fn-sn-make-v4` |
| `stx-index` | 282 | 7 | `fn-stx-alist-steps`, `fn-stx-index-shapep`, `fn-stx-record-id-held`, `fn-stx-record-id-new` |
| `consumer-event-index` | 283 | 2 | `fn-cei-correspondencep`, `fn-cei-lookup-put-induct` |
| `replay` | 383 | 1 | `fn-replay-result-reason` |
| `consumer-position` | 404 | 1 | `fn-cp-apply-trace` |
| `topic-history-metadata` | 410 | 1 | `fn-th-field-wire` |
| `stx-keyring-records` | 417 | 2 | `fn-stxk-context-tail`, `fn-stxk-current-trust` |
| `stx-evidence-records` | 419 | 4 | `fn-stxe-authority-verdict`, `fn-stxe-from-verdict`, `fn-stxe-profile-supportedp`, `fn-stxe-verdict-detail-octets` |
| `injection` | 423 | 7 | `fn-inj-date-decode`, `fn-inj-days-before-month`, `fn-inj-days-before-year`, `fn-inj-decision-shapep` |
| `mailbox` | 424 | 1 | `fn-mbx-before-at-statep` |
| `stx-lace` | 425 | 1 | `fn-stx-delta-freshp` |
| `lace` | 431 | 13 | `fn-lace-canonicalp`, `fn-lace-causally-closedp`, `fn-lace-closed-inp`, `fn-lace-cross-canonicalp` |
| `identity` | 436 | 2 | `fn-id-from-text`, `fn-id-obligationp` |
| `records-canonicality` | 437 | 2 | `fn-record-tail-after-charge`, `fn-record-tail-after-evidence` |
| `stx-verify` | 458 | 1 | `fn-stx-printablep` |
| `stx-carrier` | 461 | 1 | `fn-stx-why` |
| `principal` | 464 | 23 | `fn-prin-apply-succession`, `fn-prin-chain-validp`, `fn-prin-first-accepted`, `fn-prin-genesis-bindsp` |
| `statement-invariants` | 470 | 1 | `fn-stmt-items-fuel-induct` |
| `statement` | 473 | 19 | `fn-stmt-decode-exact`, `fn-stmt-header-decode-exact`, `fn-stmt-kind`, `fn-stmt-make-receipt` |
| `statement-codec` | 482 | 6 | `fn-stmt-decode-items-bounded-impl`, `fn-stmt-decode-items-impl`, `fn-stmt-decode-items-prechecked`, `fn-stmt-decode-prefix-items-bounded-impl` |
| `node` | 488 | 3 | `fn-node-articles-have-archive-bindingsp`, `fn-node-binding-listp`, `fn-node-binding-msgids` |
| `retention` | 491 | 3 | `fn-retain-no-duplicatesp`, `fn-retain-string-listp`, `fn-retain-sum` |
| `provenance` | 494 | 1 | `fn-prov-kindp` |
| `frame-fields` | 499 | 2 | `fn-frame-parse-shapep`, `fn-frame-result-shapep` |
| `crypto-seam` | 501 | 1 | `fn-sig-seed-p` |
| `clock` | 513 | 2 | `fn-clock-admissible-truep`, `fn-clock-may-drop-local-copyp` |
| `wildmat` | 548 | 2 | `fn-wildmat-codepoint-listp`, `fn-wildmat-codepointp` |
| `records` | 553 | 1 | `fn-record-schema0-encode` |
| `acceptance-alloc` | 565 | 2 | `fn-fencedp`, `fn-membership-listp` |
| `records-shape` | 619 | 3 | `fn-record-groups-validp`, `fn-record-parse-shapep`, `fn-record-with-stamp` |
| `defrecord` | 648 | 18 | `fn-defrecord`, `fn-defrecord-accessor-events`, `fn-defrecord-accessor-terms`, `fn-defrecord-consp-classes` |
| `cbor` | 718 | 1 | `fn-cbor-result-shapep` |

## Reproduce

    FN_AUDIT_OUT=$(mktemp -d) python3 planning/evidence/audit-twins-fanin-2026-09-25/graph.py
    FN_AUDIT_OUT=... python3 planning/evidence/audit-twins-fanin-2026-09-25/split.py 43ce09c3 books/records-shape books/injection books/native-admin
    FN_AUDIT_OUT=... python3 planning/evidence/audit-twins-fanin-2026-09-25/table.py
    FN_AUDIT_OUT=... python3 planning/evidence/audit-twins-fanin-2026-09-25/sweep.py
    FN_AUDIT_OUT=... python3 planning/evidence/audit-twins-fanin-2026-09-25/passthru.py

Python 3 from the repository root at `67b028c7`; `43ce09c3` is the dev first-parent commit before 2026-09-24 07:00, the base for "changed today". The walls come from `planning/evidence/manifests/`.
