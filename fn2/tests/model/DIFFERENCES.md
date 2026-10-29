# H2b recorded differences

This ledger records wire disagreements, not automatic adjudications. The laptop
rows below are deliberately planted **fake-target** faults, not fn1 findings.
No fn1 image was run on the laptop. The H2c section adjudicates the seat’s
four-shard hbox run separately from those fake controls.

The machine-readable [adjudications.json](adjudications.json) is the source of
truth for the H2c/H2d groups (rule, detail, command pattern, primary class).
The tables below retain the evidence and rationale for those records.

## JSONL format

Each failed comparison writes one object to `OUT/differences.jsonl`:

| Field | Meaning |
|---|---|
| `seed`, `mode`, `cut`, `transport` | Generator seed; reader/node/peer; whole/per-item/bytewise; plain/starttls/implicit. |
| `command_index` | Zero-based complete wire command or article-block index; -1 is greeting/transport setup. |
| `command_hex` | Complete failing command bytes; empty for greeting, EOF or environment failures. |
| `reply_hex` | Status plus wire block, truncated to its first 1,024 bytes. |
| `rule`, `spec`, `detail` | H2a verdict rule, source citation, and explanation. |
| `class` | `unclassified` for wire disagreements; `driver-environment` for session setup failures. |
| `liveness` | Optional additional `node_verdict` or unconsumed-output finding. |
| `reproducer` | Relative filename of the associated minimized JSON reproducer. |

Classes:

- `fn1-bug`: a determinate specification and a demonstrated departure by fn1.
- `spec-ambiguity`: the seat identifies a relevant accepted alternative and its
  exact ambiguity entry in `SPEC-MAP.md`; retain that citation in the adjudication.
- `model-bug`: **seat decision only**, with the specification line and proposed
  model correction. The driver never emits this classification.
- `driver-bug`: recording, transport handling or fixture inputs caused the
  disagreement; the H2c table records these separately from model predicates.
- `driver-environment`: a session setup attempt failed; `retry_attempt` and
  `recovered` distinguish a successful fresh-port retry from a failed session.
- `unclassified`: the driver default, including missing environment inputs.

Adjudications should preserve the original row and add `adjudicator`, `reason`,
and any `ambiguity` identifier. Acceptance of a permitted alternative is a match,
not a mismatch just because its prose or response number differs from another
permitted reply. No inference from a multi-code expectation alone assigns blame.

## Reproducers and bounds of the comparison

Reproducer JSON uses fn1's `campaign: "node"`, `role`, `tls`, `node_tls`,
`chunks_hex`, and `minimized_hex` fields. Additional fields retain the row,
`target`, `plants`, `transport`, and `minimized_commands_hex`. The minimized wire
chunks respect the selected cut; the commands field retains logical ddmin units.
`replay_fixture(path)` understands those extra fields and can override options.
The legacy fuzzer can read this schema, but its shape-only replay cannot reproduce
semantic fake plants or perform this driver's STARTTLS/compression negotiation.
Use this driver for those cases and for semantic verdicts.

H2c also saves `exchanges`, `wire`, `minimized_exchanges`, `minimized_rows` and
`minimized_wire`. Each exchange retains full status/body bytes. Wire evidence
includes complete received/unconsumed bytes, reply-time and final EOF/timeout/
reset, negotiated TLS version, and independent group-creation bounds. These
fields distinguish original observations from minimized-run observations.

`whole` sends one flight up to a protocol transition; `per-item` preserves original
item boundaries within that flight; `bytewise` sends each byte separately. Flights
end at body, STARTTLS, COMPRESS, and authentication boundaries. Ordinary commands
are pipelined, then their expectations resolve and commit in order. A complete
article block is one ddmin unit. An incomplete suffix is sent before client EOF;
it is not invented into a complete command. A failed comparison stops semantic
updates for that session; the EOF/liveness check still runs. Each protocol
mismatch gets a same-rule-and-detail ddmin attempt and a reproducer; setup
failures are recorded without minimization. The time budget does not assert
global minimality. Greeting and setup checks are performed but excluded from the
`commands_compared` and `matches` command counters.

`Node` in this tree initializes **empty** `fn.test` and `fn.letters` groups.
`PRESENT_IDS` is a generator pool, not a preloaded article. The live model starts
empty with Node's source-address peer, fuzz login and parsed auth/posting config.
H2b used a fresh Node and scratch store for every cut and minimizer candidate.
H2c reuses a fixture only after the driver's conservative no-durable-change check;
every new socket still gets a new model connection and pinned initial view. The fake alone has an explicit retained PRESENT_IDS article
at number 2 after withdrawal of number 1, with a dot-leading body. This supplies
the number-reuse, overview, and stuffing controls without inventing live facts.

Unknown clocks and generated/authenticated POST projections remain H2a's E2/E3
seams. A valid reply whose update needs absent injected-byte facts is recorded
as `unclassified` with `environment-update:`; it is not evidence of a server bug.
The fake deterministically chooses permitted POST refusals, so its green does
not claim successful generated/authenticated POST read-back coverage. TLS in the
fake is a state transition; the fn1 adapter uses actual Python SSL. DEFLATE is
encoded and decoded on both fake and client sides.

## Laptop mutation controls (2026-10-28)

All use reader mode, plain transport, Gen seeds 0..199, 20 steps. The first
catching seed is found without adding command probes to the generated transcript.
Each minimized case also fails under all three cuts; its unplanted control passes.

| Plant | First seed | Model rule | Minimized commands |
|---|---:|---|---:|
| `reuse-number` | 4 | `GROUP` | 1 |
| `423-for-420` | 44 | `XOVER` | 2 |
| `frame-after-quit` | 4 | `closed` | 2 |
| `wrong-over-field` | 102 | `XOVER` | 2 |
| `dot-unstuffed` | 4 | `BODY` | 2 |

The complete original comparison rows follow. `plant` and the minimized command
bytes are ledger context added by the control test, not model adjudications.

```jsonl
{"seed": 4, "mode": "reader", "cut": "whole", "transport": "plain", "command_index": 1, "command_hex": "47524f555020666e2e6c6574746572730d0a", "reply_hex": "32313120312031203120666e2e6c6574746572730d0a", "rule": "GROUP", "spec": "specs/nntp.md:419-505; RFC 3977 §6.1.1", "detail": "status arguments/text do not match the rule", "class": "unclassified", "liveness": "unconsumed reply octets after transcript", "plant": "reuse-number", "target": "fake", "minimized_commands_hex": ["47524f555020666e2e6c6574746572730d0a"]}
{"seed": 44, "mode": "reader", "cut": "whole", "transport": "plain", "command_index": 6, "command_hex": "584f5645522020310d0a", "reply_hex": "3432332066616b650d0a", "rule": "XOVER", "spec": "specs/nntp.md:136-159; RFC 2980 §2.8", "detail": "code 423; permitted [420]", "class": "unclassified", "plant": "423-for-420", "target": "fake", "minimized_commands_hex": ["47524f555020666e2e6c6574746572730d0a", "584f5645522020310d0a"]}
{"seed": 4, "mode": "reader", "cut": "whole", "transport": "plain", "command_index": 111, "command_hex": "535441540d0a", "reply_hex": "35303020616674657220717569740d0a", "rule": "closed", "spec": "specs/nntp.md:521-528; RFC 3977 §5.4", "detail": "expected no reply and no framing", "class": "unclassified", "liveness": "shape: reply after 205 (RFC 3977 5.4): b'500 after quit'", "plant": "frame-after-quit", "target": "fake", "minimized_commands_hex": ["515549540d0a", "535441540d0a"]}
{"seed": 102, "mode": "reader", "cut": "whole", "transport": "plain", "command_index": 8, "command_hex": "584f5645520d0a", "reply_hex": "3232342066616b650d0a320977726f6e67207375626a65637409617574686f72406578616d706c652e696e76616c6964094d6f6e2c2032312053657020323032362031323a30303a3030202b30303030093c726561646572406578616d706c652e696e76616c69643e0909313731093209587265663a202e696e76616c696420666e2e746573743a3220666e2e6c6574746572733a320d0a2e0d0a", "rule": "XOVER", "spec": "specs/nntp.md:136-159; RFC 2980 §2.8", "detail": "NOV fields differ from retained article (including Xref)", "class": "unclassified", "liveness": "unconsumed reply octets after transcript", "plant": "wrong-over-field", "target": "fake", "minimized_commands_hex": ["47524f555020666e2e746573740d0a", "584f5645520d0a"]}
{"seed": 4, "mode": "reader", "cut": "whole", "transport": "plain", "command_index": 8, "command_hex": "424f44590d0a", "reply_hex": "3232322032203c726561646572406578616d706c652e696e76616c69643e0d0a2e646f740d0a626f64790d0a2e0d0a", "rule": "BODY", "spec": "specs/nntp.md:400-424; RFC 3977 §6.2.3", "detail": "framing: unescaped leading dot", "class": "unclassified", "liveness": "shape: unstuffed block line 17: b'.dot'", "plant": "dot-unstuffed", "target": "fake", "minimized_commands_hex": ["67726f757020666e2e6c6574746572730d0a", "424f44590d0a"]}
```

## Committed corpus inventory

This checkout contains 11 JSON files, not nine. All were dispatched without a
crash. Four NNTP transcripts match the fake under every cut. The other seven
receive explicit unsupported verdicts, **not passes**:

| File | Verdict |
|---|---|
| `bounds-ihave-endless-body.json` | `unsupported-bounds` |
| `bounds-takethis-endless-body.json` | `unsupported-bounds` |
| `diff-quit-then-authinfo-same-read.json` | `match` |
| `diff-quit-then-capabilities-next-read.json` | `match` |
| `node-quit-then-authinfo.json` | `match` |
| `node-quit-then-starttls-plaintext.json` | `match` |
| `store-import-dropped-manifest.json` | `unsupported-store` |
| `store-import-flipped-profile.json` | `unsupported-store` |
| `store-import-torn-record.json` | `unsupported-store` |
| `store-journal-flip-first-frame.json` | `unsupported-store` |
| `store-journal-flip-mid-log.json` | `unsupported-store` |

The five store fixtures mutate files/imports and have no NNTP transcript. The two
bounds fixtures stream an unterminated 64-MiB body and assert process RSS/early
refusal; H2a's complete-block API cannot provide that oracle. This is a coverage
limitation, not equivalent coverage obtained by synthesizing shorter transcripts.

## H2c fn1 adjudication (2026-10-28)

The four `build/h2b-fn1/shard-*` ledgers contain **267 original mismatch rows**.
All command and reply octets were read from these rows and their reproducers;
classification is independent of fn1 books/host code. The table below groups by
exact original `(rule, detail, command_hex)` (36 groups), so different header or
body spellings remain independently counted. Paths identify real-run examples,
not the planted fake controls above. Body byte counts describe the original
command/block; the reproducer retains its complete bytes.

| Class | Original rows | Disposition |
|---|---:|---|
| fn1-bug | 30 | 24 missing COMPRESS advertisements; 6 TAKETHIS replies omit Message-ID. Carried as layer D requirements. |
| model-bug | 24 | 18 POST refusal-prose checks and 6 reader MODE STREAM codes corrected. |
| driver-bug | 33 | 9 EOF body outcomes; 12 missing TLS-exporter context; 12 missing fixture creation times. |
| spec-ambiguity | 180 | 80 malformed keywords; 94 zero-status observations; 6 syntax/permission precedence cases. A13–A15. |
| **Total** | **267** | One primary class per original row; downstream failures are described separately. |

**Framing investigation comes first.** Every one of the 94 “wrong number of
status lines” rows records `reply_hex=""`: zero lines, not two concatenated
lines. `Wire.line` extracts one CRLF line and leaves the rest buffered. Most
original transcripts reach an embedded CR/LF, overlong line or malformed
TAKETHIS before the empty reply. These bytes do not prove that fn1 emitted two
statuses or that the driver ate a following status. The recording conflates EOF
and timeout. In particular `shard-2/repro-400-peer-whole-00006.json` minimizes to
`CHECK <a>`, but its original empty reply follows malformed XOVER. The minimizer
kept only the *rule*, not the same detail or command, and saves the original
reply, not the candidate's response. A direct clean-CHECK defect is unproven.
A14 preserves these limits rather than inventing missing observed replies.

All nine primary liveness rows have exactly
`441 posting failed; the article was not received\r\n` after an unterminated
POST body reaches EOF. They are the body's refusal, which H2b failed to check.
Additional `liveness` annotations on semantic mismatches are not additional
rows: pipelined commands already sent can still have legitimate pending replies
when semantic comparison stops. These annotations are retained but are not
independently adjudicated as server output bugs; the original primary mismatch
and reply evidence remain the unit counted here.

**What the model corrections mean.** The POST corpus supplies empty mandatory
fields and fn1 names invalid syntax. The specification requires 441 with the
reason, not H2a's invented `malformed|missing|required` wording; adding `syntax`
preserves the required refusal and named store distinctions. The MODE exception
is equally narrow: specs/nntp.md:78-80 assigns reader 502 to IHAVE, CHECK and
TAKETHIS, while 2416-2418 implements MODE STREAM on peer connections; RFC 3977
§3.2.1 assigns 501 to an unavailable variant of implemented MODE. The model does
not change unknown-keyword 500 to 501 merely to match fn1 (A13).

**Environmental replay limits.** All 12 SASL rows are protected connections;
PLUS may be offered only with installed TLS exporter (1707), a fact H2b omitted.
H2c explicitly records that observation as unknown, permitting either PLUS
presence or absence only on TLS; this is no proof of exporter/channel binding.
All 12 ACTIVE.TIMES rows list the two newly created fixture groups. H2b supplied
no creation facts and incorrectly demanded an empty block. H2c uses setup wall
bounds obtained independently of replies. The old run has only its externally
known date. Historical replay therefore leaves these 12 rows evidence-open:
the fixture defect is fixed, but exact persisted creation seconds cannot be
recovered independently. A separately labeled coarse run-day bound can check
shape and plausibility only; it is not an exact replay closure.

The 24 missing-capability rows contain READER, POST, OVER, HDR, XPAT, NEWNEWS,
LIST, IMPLEMENTATION, AUTHINFO and SASL, but omit COMPRESS DEFLATE. TLS does not
excuse that omission and the spec has no peer-only restriction. The six TAKETHIS
rows say `436 the article was not received; closing` without the offered ID.
436 itself is explicitly legal for deferred/uncertain outcomes (2428-2435), so
this ledger does **not** claim a universal 436-versus-439 defect. The missing ID
is determinate; actual body-bound refusal additionally requires 439 (530-534).

| Group | Count | Rule | Original detail | Command shape | Example reproducer | Class | Exact source | Proposed action |
|---|---:|---|---|---|---|---|---|---|
| H2c-01 | 18 | unknown | code 501; permitted [500] | `Date: Mon, 31 Feb 2026 12:00:00 +0000\r\n` | `build/h2b-fn1/shard-0/repro-0-reader-whole-00000.json` | spec-ambiguity | A13; specs/nntp.md:83-87; rfc3977.txt:543-555,5422 | Layer D: choose invalid-keyword rejection; retain well-formed unknown 500. |
| H2c-02 | 3 | syntax | wrong number of status lines (including closing 400) | `TAKETHIS <a@b@c\r\n` | `build/h2b-fn1/shard-0/repro-0-peer-whole-00006.json` | spec-ambiguity | A14; specs/nntp.md:513-518; rfc3977.txt:5866-5899 | Record EOF versus timeout and full prior replies; repeat on clean connection before assigning fn1 blame. |
| H2c-03 | 9 | unknown | code 501; permitted [500] | `Date: garbage\r\n` | `build/h2b-fn1/shard-0/repro-1-reader-whole-00009.json` | spec-ambiguity | A13; specs/nntp.md:83-87; rfc3977.txt:543-555,5422 | Layer D: choose invalid-keyword rejection; retain well-formed unknown 500. |
| H2c-04 | 9 | syntax | wrong number of status lines (including closing 400) | `XPAT Xref 1844674407370\t\r\n` | `build/h2b-fn1/shard-0/repro-2-reader-whole-00018.json` | spec-ambiguity | A14; specs/nntp.md:513-518; rfc3977.txt:5866-5899 | Record EOF versus timeout and full prior replies; repeat on clean connection before assigning fn1 blame. |
| H2c-05 | 6 | syntax | wrong number of status lines (including closing 400) | `POST\t\r\n` | `build/h2b-fn1/shard-0/repro-3-node-whole-00027.json` | spec-ambiguity | A14; specs/nntp.md:513-518; rfc3977.txt:5866-5899 | Record EOF versus timeout and full prior replies; repeat on clean connection before assigning fn1 blame. |
| H2c-06 | 3 | syntax | wrong number of status lines (including closing 400) | `From: \r\n` | `build/h2b-fn1/shard-0/repro-4-reader-whole-00033.json` | spec-ambiguity | A14; specs/nntp.md:513-518; rfc3977.txt:5866-5899 | Record EOF versus timeout and full prior replies; repeat on clean connection before assigning fn1 blame. |
| H2c-07 | 6 | POST | status arguments/text do not match the rule | `POST body (10139 bytes; empty From, empty Newsgroups)` | `build/h2b-fn1/shard-0/repro-4-node-whole-00036.json` | model-bug | specs/nntp.md:724-725,782-785,857-860; RFC 3977 §6.3.1 | Closed by allowing syntax as a reason for missing required fields; retain 441 and exact named duplicate/conflict rules. |
| H2c-08 | 24 | CAPABILITIES | missing or duplicate capability | `CAPABILITIES\r\n` | `build/h2b-fn1/shard-0/repro-5-reader-whole-00042.json` | fn1-bug | specs/nntp.md:2486-2506; RFC 8054 §2.1 | Layer D: advertise COMPRESS DEFLATE while inactive on reader/node sessions too; no peer-only exclusion in spec. |
| H2c-09 | 12 | CAPABILITIES | SASL mechanism list differs from configured connection context | `CAPABILITIES\r\n` | `build/h2b-fn1/shard-0/repro-5-peer-whole-00048.json` | driver-bug | specs/nntp.md:1705-1709,1729-1731 | Supply unknown TLS-exporter observation explicitly; permit optional PLUS only on TLS. Cryptographic exporter installation remains unverified. |
| H2c-10 | 6 | MODE | code 501; permitted [502] | `MODE STREAM\r\n` | `build/h2b-fn1/shard-1/repro-200-reader-whole-00000.json` | model-bug | specs/nntp.md:78-80,2416-2418; rfc3977.txt:552-555; rfc4644.txt:270-274 | Closed: reader MODE STREAM is unavailable variant 501; explicit three-verb transit 502 remains. |
| H2c-11 | 9 | OVER | wrong number of status lines (including closing 400) | `OVER\r\n` | `build/h2b-fn1/shard-1/repro-201-reader-whole-00009.json` | spec-ambiguity | A14; specs/nntp.md:513-518; rfc3977.txt:5866-5899 | Record EOF versus timeout and full prior replies; repeat on clean connection before assigning fn1 blame. |
| H2c-12 | 17 | unknown | code 501; permitted [500] | `Path: not-for-mail\r\n` | `build/h2b-fn1/shard-1/repro-204-reader-whole-00036.json` | spec-ambiguity | A13; specs/nntp.md:83-87; rfc3977.txt:543-555,5422 | Layer D: choose invalid-keyword rejection; retain well-formed unknown 500. |
| H2c-13 | 3 | syntax | wrong number of status lines (including closing 400) | `TAKETHIS <a@b\r\n` | `build/h2b-fn1/shard-1/repro-204-peer-whole-00042.json` | spec-ambiguity | A14; specs/nntp.md:513-518; rfc3977.txt:5866-5899 | Record EOF versus timeout and full prior replies; repeat on clean connection before assigning fn1 blame. |
| H2c-14 | 6 | IHAVE | wrong number of status lines (including closing 400) | `IHAVE <>\r\n` | `build/h2b-fn1/shard-1/repro-205-reader-whole-00045.json` | spec-ambiguity | A14; specs/nntp.md:513-518; rfc3977.txt:5866-5899 | Record EOF versus timeout and full prior replies; repeat on clean connection before assigning fn1 blame. |
| H2c-15 | 3 | syntax | wrong number of status lines (including closing 400) | `IHAVE <>\r\n` | `build/h2b-fn1/shard-1/repro-205-peer-whole-00051.json` | spec-ambiguity | A14; specs/nntp.md:513-518; rfc3977.txt:5866-5899 | Record EOF versus timeout and full prior replies; repeat on clean connection before assigning fn1 blame. |
| H2c-16 | 6 | LIST | wrong number of status lines (including closing 400) | `LIST OVERVIEW.FMT\r\n` | `build/h2b-fn1/shard-1/repro-207-reader-whole-00063.json` | spec-ambiguity | A14; specs/nntp.md:513-518; rfc3977.txt:5866-5899 | Record EOF versus timeout and full prior replies; repeat on clean connection before assigning fn1 blame. |
| H2c-17 | 9 | CHECK | wrong number of status lines (including closing 400) | `CHECK <a>\r\n` | `build/h2b-fn1/shard-2/repro-400-reader-whole-00000.json` | spec-ambiguity | A14; specs/nntp.md:513-518; rfc3977.txt:5866-5899 | Record EOF versus timeout and full prior replies; repeat on clean connection before assigning fn1 blame. |
| H2c-18 | 9 | unknown | wrong number of status lines (including closing 400) | `CAPABILITIESCAPABILITIES AUTOUPDATE\r\n` | `build/h2b-fn1/shard-2/repro-401-reader-whole-00009.json` | spec-ambiguity | A14; specs/nntp.md:513-518; rfc3977.txt:5866-5899 | Record EOF versus timeout and full prior replies; repeat on clean connection before assigning fn1 blame. |
| H2c-19 | 6 | unknown | code 501; permitted [500] | `Path: a!a!a!a!a!a!a!a!a!a!a!a!a!a!a!a!a!a!a!a… (409 bytes)` | `build/h2b-fn1/shard-2/repro-402-reader-whole-00018.json` | spec-ambiguity | A13; specs/nntp.md:83-87; rfc3977.txt:543-555,5422 | Layer D: choose invalid-keyword rejection; retain well-formed unknown 500. |
| H2c-20 | 3 | TAKETHIS | code 436; permitted [439] | `TAKETHIS body (13513 bytes; long Path)` | `build/h2b-fn1/shard-2/repro-402-peer-whole-00024.json` | fn1-bug | specs/nntp.md:530-534,2428-2435; rfc4644.txt:370-387 | Layer D: echo offered Message-ID on every response, including local 436. Use 439 for explicit body-bound refusal; 436 remains legal for deferred/uncertain. |
| H2c-21 | 12 | unknown | code 501; permitted [500] | `From: author@example.invalid\r\n` | `build/h2b-fn1/shard-2/repro-403-reader-whole-00027.json` | spec-ambiguity | A13; specs/nntp.md:83-87; rfc3977.txt:543-555,5422 | Layer D: choose invalid-keyword rejection; retain well-formed unknown 500. |
| H2c-22 | 3 | syntax | wrong number of status lines (including closing 400) | `LISTGROUP fn.letters.sub 99999999999999999999\r\n` | `build/h2b-fn1/shard-2/repro-403-peer-whole-00033.json` | spec-ambiguity | A14; specs/nntp.md:513-518; rfc3977.txt:5866-5899 | Record EOF versus timeout and full prior replies; repeat on clean connection before assigning fn1 blame. |
| H2c-23 | 9 | liveness | unconsumed reply octets after transcript | `EOF after unterminated POST body` | `build/h2b-fn1/shard-2/repro-404-reader-whole-00036.json` | driver-bug | specs/nntp.md:513-518,724-725; RFC 3977 §§3.1.1,6.3.1 | Closed by checking EOF-interrupted POST body against send_block rejection; 441 is owed body outcome, not stray reply. |
| H2c-24 | 3 | syntax | wrong number of status lines (including closing 400) | `TAKETHIS <fz405.1.213088405@fuzz.invalid>Path: not-for-mail\r\n` | `build/h2b-fn1/shard-2/repro-405-peer-whole-00051.json` | spec-ambiguity | A14; specs/nntp.md:513-518; rfc3977.txt:5866-5899 | Record EOF versus timeout and full prior replies; repeat on clean connection before assigning fn1 blame. |
| H2c-25 | 6 | unknown | code 501; permitted [500] | `Date: Mon, 21 Sep 2026 12:00:00 +0000\r\n` | `build/h2b-fn1/shard-2/repro-406-reader-whole-00054.json` | spec-ambiguity | A13; specs/nntp.md:83-87; rfc3977.txt:543-555,5422 | Layer D: choose invalid-keyword rejection; retain well-formed unknown 500. |
| H2c-26 | 3 | TAKETHIS | code 436; permitted [439] | `TAKETHIS body (15029 bytes; empty Path)` | `build/h2b-fn1/shard-2/repro-406-peer-whole-00060.json` | fn1-bug | specs/nntp.md:530-534,2428-2435; rfc4644.txt:370-387 | Layer D: echo offered Message-ID on every response, including local 436. Use 439 for explicit body-bound refusal; 436 remains legal for deferred/uncertain. |
| H2c-27 | 9 | POST | status arguments/text do not match the rule | `POST body (1850 bytes; empty From, empty Newsgroups)` | `build/h2b-fn1/shard-3/repro-601-reader-whole-00000.json` | model-bug | specs/nntp.md:724-725,782-785,857-860; RFC 3977 §6.3.1 | Closed by allowing syntax as a reason for missing required fields; retain 441 and exact named duplicate/conflict rules. |
| H2c-28 | 12 | LIST | listing rows differ (including multiplicity) | `LIST ACTIVE.TIMES\r\n` | `build/h2b-fn1/shard-3/repro-602-reader-whole-00009.json` | driver-bug | specs/nntp.md:375-389; RFC 3977 §7.6.4 | Supply independent fixture creation-time interval; enforce exact groups and bounded timestamps. Legacy evidence remains open: exact historical creation facts are absent. |
| H2c-29 | 6 | syntax | code 502; permitted [501] | `TAKETHIS <f\xcaz603.1.25457411@fuzz.invalid>Path: src.example.invalid!not-for-mail\r\n` | `build/h2b-fn1/shard-3/repro-603-reader-whole-00018.json` | spec-ambiguity | A15; specs/nntp.md:78-80; rfc3977.txt:547-555,579-603,5866-5899 | Layer D: choose malformed-input versus transit-permission precedence. |
| H2c-30 | 3 | syntax | wrong number of status lines (including closing 400) | `TAKETHIS <f\xcaz603.1.25457411@fuzz.invalid>Path: src.example.invalid!not-for-mail\r\n` | `build/h2b-fn1/shard-3/repro-603-peer-whole-00024.json` | spec-ambiguity | A14; specs/nntp.md:513-518; rfc3977.txt:5866-5899 | Record EOF versus timeout and full prior replies; repeat on clean connection before assigning fn1 blame. |
| H2c-31 | 9 | unknown | code 501; permitted [500] | `POSTFrom: \xc3\xa9 <a@b>\r\n` | `build/h2b-fn1/shard-3/repro-604-reader-whole-00027.json` | spec-ambiguity | A13; specs/nntp.md:83-87; rfc3977.txt:543-555,5422 | Layer D: choose invalid-keyword rejection; retain well-formed unknown 500. |
| H2c-32 | 3 | unknown | code 501; permitted [500] | `Path: src.example.invalid!not-for-mail\r\n` | `build/h2b-fn1/shard-3/repro-605-reader-whole-00036.json` | spec-ambiguity | A13; specs/nntp.md:83-87; rfc3977.txt:543-555,5422 | Layer D: choose invalid-keyword rejection; retain well-formed unknown 500. |
| H2c-33 | 6 | syntax | wrong number of status lines (including closing 400) | `HEAD <fz605.1.154121121@fuzz.invalid>\nAUTHINFO PASS fuzz-password\r\n` | `build/h2b-fn1/shard-3/repro-605-node-whole-00039.json` | spec-ambiguity | A14; specs/nntp.md:513-518; rfc3977.txt:5866-5899 | Record EOF versus timeout and full prior replies; repeat on clean connection before assigning fn1 blame. |
| H2c-34 | 9 | syntax | wrong number of status lines (including closing 400) | `\tSTAT <a\t@b>\r\n` | `build/h2b-fn1/shard-3/repro-608-reader-whole-00054.json` | spec-ambiguity | A14; specs/nntp.md:513-518; rfc3977.txt:5866-5899 | Record EOF versus timeout and full prior replies; repeat on clean connection before assigning fn1 blame. |
| H2c-35 | 3 | POST | status arguments/text do not match the rule | `POST body (2152 bytes; empty From)` | `build/h2b-fn1/shard-3/repro-609-reader-whole-00063.json` | model-bug | specs/nntp.md:724-725,782-785,857-860; RFC 3977 §6.3.1 | Closed by allowing syntax as a reason for missing required fields; retain 441 and exact named duplicate/conflict rules. |
| H2c-36 | 4 | syntax | wrong number of status lines (including closing 400) | `BODY -1\r\n` | `build/h2b-fn1/shard-3/repro-609-node-whole-00066.json` | spec-ambiguity | A14; specs/nntp.md:513-518; rfc3977.txt:5866-5899 | Record EOF versus timeout and full prior replies; repeat on clean connection before assigning fn1 blame. |

## H2d second fn1 run adjudication (2026-10-28)

The four `build/h2c-fn1/shard-*` ledgers contain **322 original rows** from
42 seeds, 370 sessions and 7,455 compared commands (7,133 matched). The table
keeps every exact `(rule, detail, command_hex)` group: **48 groups**, with
original and attributed command distinguished. Counts refer to original rows,
not minimized outcomes or additional liveness annotations.

| Class | Original rows | Disposition |
|---|---:|---|
| fn1-bug | 37 | 24 missing COMPRESS; 13 TAKETHIS replies omit the offered Message-ID. |
| model-bug | 159 | 130 permissible closes; 14 invented article-rejection closes; 15 malformed TAKETHIS command-prefix timeouts (HT). |
| driver-bug | 3 | Unterminated POST over TLS: client raw half-close followed by TLS decode-error alert; reply evidence cannot establish a clean server close. |
| spec-ambiguity | 123 | 114 A13 malformed keywords; 6 A15 syntax/permission precedence; 3 A16 multiple article defects/refusal-reason precedence. |
| **Total** | **322** | One primary class per original row. |

**EOF attribution.** All 148 wrong-number rows contain zero status lines, never
two concatenated statuses. Of these, 130 have `wire.reply_eof=True`,
`reply_timeout=False`, `reply_reset=None`: the immediately preceding command
received `501 syntax error`, then the next read discovered the close. That
preceding command is the attribution, not the later unanswered command.
There are 27 over-512-octet commands and 103 commands containing embedded
CR/LF/NUL; specs/nntp.md:513-518 permits closing instead of draining.
RFC 3977 §3.2.1 (`rfc3977.txt:547-551`) still requires 501 for overlength;
the model accepts 501 then EOF there, **not** silent EOF. RFC 3977 §12.5
(`rfc3977.txt:5866-5899`) permits silent close on illegal UTF-8, and structural
unparseability permits the close alternative under NNT-003. Ordinary semantic
argument errors gain no general close permission. No run-2 close is attributed
to a third authentication failure.

The other 18 empty replies are different evidence: 15 malformed TAKETHIS lines
have `reply_timeout=True`, `reply_eof=False` and only reach final EOF **after
client shutdown**; three unterminated POST bodies encounter a TLS
`TLSV1_ALERT_DECODE_ERROR` after the driver's raw TLS half-close. None is counted
as a permitted spontaneous server EOF. For all other rows, final `wire.eof`
after the driver's drain likewise does not prove that the mismatch's command
closed the connection. The table's “normal reply; final drain” explicitly
preserves that limitation. The driver now records and compares closure once,
without charging the later pipelined commands.

**All 14 `closed` rows were model defects, not replies after QUIT.** Two follow
TAKETHIS 439, three follow IHAVE 437, and nine follow POST 441; every prior body
was dot-terminated but contained NUL. `_article_block` incorrectly inferred
mandatory closure from every framing rejection. NNT-003 permits draining to a
safe boundary and continuing, as these replies demonstrate. The independent
QUIT prohibition at specs/nntp.md:521-528 remains unchanged; a real 205 followed
by another framed reply still fails. The known `diff-quit-then-*` and
`node-quit-then-*` corpus controls are separate from these fourteen observations.

**Layer D must not reproduce these demonstrated fn1 bugs:** omit COMPRESS
DEFLATE from reader/node capability lists while compression is inactive (24
rows; specs/nntp.md:2486-2506), or emit a TAKETHIS response without the offered
Message-ID (13 rows; specs/nntp.md:2428-2435; RFC 4644 §2.5.1). Every one of the
13 replies is `436 the article was not received; closing`. The local 436 code
is explicitly allowed for deferred/uncertain outcomes, so “436 instead of 439”
alone is not the adjudicated bug; the missing ID is. Body-bound refusal still
requires 439 under specs/nntp.md:530-534. The 14 closed rows add **no** fn1 QUIT
bug. A13/A15/A16 policy questions remain distinct from those requirements; HT resolves the A14 TAKETHIS timing groups below.

| Group | Count | Rule | Original detail | Original command shape | Closure attribution / wire evidence | Example reproducer | Class | Exact source | Proposed action |
|---|---:|---|---|---|---|---|---|---|---|
| H2d-01 | 24 | unknown | code 501; permitted [500] | `Date: Mon, 31 Feb 2026 12:00:00 +0000\r\n` | normal reply; final drain is not server-close evidence | `build/h2c-fn1/shard-0/repro-0-reader-whole-00000.json` | spec-ambiguity | A13; specs/nntp.md:83-87; rfc3977.txt:543-555,5422 | Keep open: choose invalid-keyword policy; retain well-formed unknown 500. |
| H2d-02 | 3 | syntax | wrong number of status lines (including closing 400) | `TAKETHIS <a@b@c\r\n` | current command: timeout, then client shutdown; no observed pre-shutdown EOF | `build/h2c-fn1/shard-0/repro-0-peer-whole-00006.json` | model-bug | A14; specs/nntp.md:513-518,2421-2422; rfc4644.txt:375-387 | Closed by HT: no reply before article is required; corresponding HS probes all receive 439 after body. |
| H2d-03 | 9 | unknown | code 501; permitted [500] | `Date: garbage\r\n` | normal reply; final drain is not server-close evidence | `build/h2c-fn1/shard-0/repro-1-reader-whole-00009.json` | spec-ambiguity | A13; specs/nntp.md:83-87; rfc3977.txt:543-555,5422 | Keep open: choose invalid-keyword policy; retain well-formed unknown 500. |
| H2d-04 | 9 | syntax | wrong number of status lines (including closing 400) | `XPAT Xref 1844674407370\t\r\n` | `AUTHINFO PASS pppppppppppppppppppppppppppppppppppppppppppppppppppppppppppppp… (617 bytes)` → 501 → clean EOF | `build/h2c-fn1/shard-0/repro-2-reader-whole-00018.json` | model-bug | specs/nntp.md:513-518; rfc3977.txt:547-551,5866-5899 | Closed by model close alternative plus driver attribution to preceding 501. |
| H2d-05 | 6 | syntax | wrong number of status lines (including closing 400) | `POST\t\r\n` | `HEAD <a@b\r>\r\n` → 501 → clean EOF | `build/h2c-fn1/shard-0/repro-3-node-whole-00027.json` | model-bug | specs/nntp.md:513-518; rfc3977.txt:547-551,5866-5899 | Closed by model close alternative plus driver attribution to preceding 501. |
| H2d-06 | 3 | syntax | wrong number of status lines (including closing 400) | `From: \r\n` | `POST xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx… (1027 bytes)` → 501 → clean EOF | `build/h2c-fn1/shard-0/repro-4-reader-whole-00033.json` | model-bug | specs/nntp.md:513-518; rfc3977.txt:547-551,5866-5899 | Closed by model close alternative plus driver attribution to preceding 501. |
| H2d-07 | 6 | syntax | wrong number of status lines (including closing 400) | `list overview.fmt *\r\n` | `NEWNEWS fn.* 2026010 00000\n\rOVER \r\n` → 501 → clean EOF | `build/h2c-fn1/shard-0/repro-4-node-whole-00036.json` | model-bug | specs/nntp.md:513-518; rfc3977.txt:547-551,5866-5899 | Closed by model close alternative plus driver attribution to preceding 501. |
| H2d-08 | 24 | CAPABILITIES | missing or duplicate capability | `CAPABILITIES\r\n` | normal reply; final drain is not server-close evidence | `build/h2c-fn1/shard-0/repro-5-reader-whole-00042.json` | fn1-bug | specs/nntp.md:2486-2506; RFC 8054 §2.1 | Layer D: advertise COMPRESS DEFLATE on reader/node too when inactive. |
| H2d-09 | 3 | CAPABILITIES | wrong number of status lines (including closing 400) | `CAPABILITIES\r\n` | `NEXT\r\x00\nGROUP fn.nowhere\r\n` → 501 → clean EOF | `build/h2c-fn1/shard-0/repro-5-peer-whole-00048.json` | model-bug | specs/nntp.md:513-518; rfc3977.txt:547-551,5866-5899 | Closed by model close alternative plus driver attribution to preceding 501. |
| H2d-10 | 9 | XOVER | wrong number of status lines (including closing 400) | `XOVER  1\r\n` | `ARTICLE <fz7.2.734559255@fuzz.invalid> \rCHECK <fz7.3.673767654@fuzz.invalid>\r\n` → 501 → clean EOF | `build/h2c-fn1/shard-0/repro-7-reader-whole-00060.json` | model-bug | specs/nntp.md:513-518; rfc3977.txt:547-551,5866-5899 | Closed by model close alternative plus driver attribution to preceding 501. |
| H2d-11 | 6 | unknown | code 501; permitted [500] | `X-Fz-34: 34\r\n` | normal reply; final drain is not server-close evidence | `build/h2c-fn1/shard-0/repro-8-reader-whole-00069.json` | spec-ambiguity | A13; specs/nntp.md:83-87; rfc3977.txt:543-555,5422 | Keep open: choose invalid-keyword policy; retain well-formed unknown 500. |
| H2d-12 | 2 | closed | expected no reply and no framing | `LAST\r\n` | TAKETHIS block → 439; no QUIT / no prior EOF | `build/h2c-fn1/shard-0/repro-8-peer-whole-00075.json` | model-bug | specs/nntp.md:513-518 | Closed: dot-terminated rejected article may drain and continue; retain QUIT silence requirement. |
| H2d-13 | 9 | OVER | wrong number of status lines (including closing 400) | `OVER\r\n` | `GROUP junk\n\rCAPABILITIES AUTOUPDATE\r\n` → 501 → clean EOF | `build/h2c-fn1/shard-1/repro-201-reader-whole-00009.json` | model-bug | specs/nntp.md:513-518; rfc3977.txt:547-551,5866-5899 | Closed by model close alternative plus driver attribution to preceding 501. |
| H2d-14 | 3 | AUTHINFO | wrong number of status lines (including closing 400) | `AUTHINFO SASL SCRAM-SHA-256\r\n` | `help\rXFN-ZARTICLE <a@b.> 845aa5e18680ef219a9b0f0d0b959cd8886d5eabc12236aae19f301aed9de75e\r\n` → 501 → clean EOF | `build/h2c-fn1/shard-1/repro-202-peer-whole-00024.json` | model-bug | specs/nntp.md:513-518; rfc3977.txt:547-551,5866-5899 | Closed by model close alternative plus driver attribution to preceding 501. |
| H2d-15 | 3 | POST | wrong number of status lines (including closing 400) | `Date: Mon, 31 Feb 2026 12:00:00 +0000\r\nFrom: author@example.invalid\r\nNew… (1316 bytes)` | current unterminated POST body: client half-close / TLS decode-error reset | `build/h2c-fn1/shard-1/repro-203-peer-whole-00033.json` | driver-bug | RFC 4642 §2.2; specs/nntp.md:513-518; A14 transport contract | Keep evidence-open: avoid raw TLS half-close; obtain a valid TLS EOF transcript. |
| H2d-16 | 24 | unknown | code 501; permitted [500] | `Path: not-for-mail\r\n` | normal reply; final drain is not server-close evidence | `build/h2c-fn1/shard-1/repro-204-reader-whole-00036.json` | spec-ambiguity | A13; specs/nntp.md:83-87; rfc3977.txt:543-555,5422 | Keep open: choose invalid-keyword policy; retain well-formed unknown 500. |
| H2d-17 | 3 | syntax | wrong number of status lines (including closing 400) | `TAKETHIS <a@b\r\n` | current command: timeout, then client shutdown; no observed pre-shutdown EOF | `build/h2c-fn1/shard-1/repro-204-peer-whole-00042.json` | model-bug | A14; specs/nntp.md:513-518,2421-2422; rfc4644.txt:375-387 | Closed by HT: no reply before article is required; corresponding HS probes all receive 439 after body. |
| H2d-18 | 6 | IHAVE | wrong number of status lines (including closing 400) | `IHAVE <>\r\n` | `LAST xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx… (513 bytes)` → 501 → clean EOF | `build/h2c-fn1/shard-1/repro-205-reader-whole-00045.json` | model-bug | specs/nntp.md:513-518; rfc3977.txt:547-551,5866-5899 | Closed by model close alternative plus driver attribution to preceding 501. |
| H2d-19 | 3 | syntax | wrong number of status lines (including closing 400) | `IHAVE <>\r\n` | `LAST xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx… (513 bytes)` → 501 → clean EOF | `build/h2c-fn1/shard-1/repro-205-peer-whole-00051.json` | model-bug | specs/nntp.md:513-518; rfc3977.txt:547-551,5866-5899 | Closed by model close alternative plus driver attribution to preceding 501. |
| H2d-20 | 3 | POST | status arguments/text do not match the rule | `Message-ID: <fz206.1.650507537@fuzz.invalid>\r\nPath: \r\n: empty name\r\nFr… (5152 bytes)` | normal reply; final drain is not server-close evidence | `build/h2c-fn1/shard-1/repro-206-peer-whole-00060.json` | spec-ambiguity | A16; specs/nntp.md:905-909,930-935; rfc5537.txt:876-884 | Keep open: empty Path plus unnamed header; choose multi-defect precedence, preserve named Path-only refusal. |
| H2d-21 | 9 | LIST | wrong number of status lines (including closing 400) | `LIST OVERVIEW.FMT\r\n` | `MO\nDE \r\n` → 501 → clean EOF | `build/h2c-fn1/shard-1/repro-207-reader-whole-00063.json` | model-bug | specs/nntp.md:513-518; rfc3977.txt:547-551,5866-5899 | Closed by model close alternative plus driver attribution to preceding 501. |
| H2d-22 | 9 | unknown | wrong number of status lines (including closing 400) | `XFEATURE COMPRESS GZIP\r\n` | `XOVER 1-99999999999999999999\r\r\n` → 501 → clean EOF | `build/h2c-fn1/shard-1/repro-208-reader-whole-00072.json` | model-bug | specs/nntp.md:513-518; rfc3977.txt:547-551,5866-5899 | Closed by model close alternative plus driver attribution to preceding 501. |
| H2d-23 | 6 | unknown | code 501; permitted [500] | `X-Fz-0: 0\r\n` | normal reply; final drain is not server-close evidence | `build/h2c-fn1/shard-1/repro-209-reader-whole-00081.json` | spec-ambiguity | A13; specs/nntp.md:83-87; rfc3977.txt:543-555,5422 | Keep open: choose invalid-keyword policy; retain well-formed unknown 500. |
| H2d-24 | 1 | TAKETHIS | code 436; permitted [439] | `X-Fz-0: 0\r\nPath: src.example.invalid!not-for-mail\r\nX-Long: vvvvvvvvvvvvv… (18260 bytes)` | normal reply; final drain is not server-close evidence | `build/h2c-fn1/shard-1/repro-209-peer-whole-00087.json` | fn1-bug | specs/nntp.md:530-534,2428-2435; rfc4644.txt:370-387 | Layer D: echo offered Message-ID on every reply, including local 436; 439 for explicit body bound. |
| H2d-25 | 9 | CHECK | wrong number of status lines (including closing 400) | `CHECK <a>\r\n` | `XOVER 1-2-3\r\r\n` → 501 → clean EOF | `build/h2c-fn1/shard-2/repro-400-reader-whole-00000.json` | model-bug | specs/nntp.md:513-518; rfc3977.txt:547-551,5866-5899 | Closed by model close alternative plus driver attribution to preceding 501. |
| H2d-26 | 9 | unknown | wrong number of status lines (including closing 400) | `CAPABILITIESCAPABILITIES AUTOUPDATE\r\n` | `CHEC\rK a@b>\r\n` → 501 → clean EOF | `build/h2c-fn1/shard-2/repro-401-reader-whole-00009.json` | model-bug | specs/nntp.md:513-518; rfc3977.txt:547-551,5866-5899 | Closed by model close alternative plus driver attribution to preceding 501. |
| H2d-27 | 6 | unknown | code 501; permitted [500] | `Path: a!a!a!a!a!a!a!a!a!a!a!a!a!a!a!a!a!a!a!a!a!a!a!a!a!a!a!a!a!a!a!a!a!a!a!… (409 bytes)` | normal reply; final drain is not server-close evidence | `build/h2c-fn1/shard-2/repro-402-reader-whole-00018.json` | spec-ambiguity | A13; specs/nntp.md:83-87; rfc3977.txt:543-555,5422 | Keep open: choose invalid-keyword policy; retain well-formed unknown 500. |
| H2d-28 | 3 | TAKETHIS | code 436; permitted [439] | `Path: a!a!a!a!a!a!a!a!a!a!a!a!a!a!a!a!a!a!a!a!a!a!a!a!a!a!a!a!a!a!a!a!a!a!a!… (13513 bytes)` | normal reply; final drain is not server-close evidence | `build/h2c-fn1/shard-2/repro-402-peer-whole-00024.json` | fn1-bug | specs/nntp.md:530-534,2428-2435; rfc4644.txt:370-387 | Layer D: echo offered Message-ID on every reply, including local 436; 439 for explicit body bound. |
| H2d-29 | 12 | unknown | code 501; permitted [500] | `From: author@example.invalid\r\n` | normal reply; final drain is not server-close evidence | `build/h2c-fn1/shard-2/repro-403-reader-whole-00027.json` | spec-ambiguity | A13; specs/nntp.md:83-87; rfc3977.txt:543-555,5422 | Keep open: choose invalid-keyword policy; retain well-formed unknown 500. |
| H2d-30 | 3 | syntax | wrong number of status lines (including closing 400) | `LISTGROUP fn.letters.sub 99999999999999999999\r\n` | `LISTGROUP fn.test -1\nBODY a\r\n` → 501 → clean EOF | `build/h2c-fn1/shard-2/repro-403-peer-whole-00033.json` | model-bug | specs/nntp.md:513-518; rfc3977.txt:547-551,5866-5899 | Closed by model close alternative plus driver attribution to preceding 501. |
| H2d-31 | 3 | syntax | wrong number of status lines (including closing 400) | `TAKETHIS <fz405.1.213088405@fuzz.invalid>Path: not-for-mail\r\n` | current command: timeout, then client shutdown; no observed pre-shutdown EOF | `build/h2c-fn1/shard-2/repro-405-peer-whole-00042.json` | model-bug | A14; specs/nntp.md:513-518,2421-2422; rfc4644.txt:375-387 | Closed by HT: no reply before article is required; corresponding HS probes all receive 439 after body. |
| H2d-32 | 6 | unknown | code 501; permitted [500] | `Date: Mon, 21 Sep 2026 12:00:00 +0000\r\n` | normal reply; final drain is not server-close evidence | `build/h2c-fn1/shard-2/repro-406-reader-whole-00045.json` | spec-ambiguity | A13; specs/nntp.md:83-87; rfc3977.txt:543-555,5422 | Keep open: choose invalid-keyword policy; retain well-formed unknown 500. |
| H2d-33 | 3 | TAKETHIS | code 436; permitted [439] | `Path: \r\nDate: Mon, 21 Sep 2026 12:00:00 +0000\r\nFrom: author@example.inva… (15029 bytes)` | normal reply; final drain is not server-close evidence | `build/h2c-fn1/shard-2/repro-406-peer-whole-00051.json` | fn1-bug | specs/nntp.md:530-534,2428-2435; rfc4644.txt:370-387 | Layer D: echo offered Message-ID on every reply, including local 436; 439 for explicit body bound. |
| H2d-34 | 3 | syntax | wrong number of status lines (including closing 400) | `TAKETHIS <a@b>junk\r\n` | current command: timeout, then client shutdown; no observed pre-shutdown EOF | `build/h2c-fn1/shard-2/repro-408-peer-whole-00060.json` | model-bug | A14; specs/nntp.md:513-518,2421-2422; rfc4644.txt:375-387 | Closed by HT: no reply before article is required; corresponding HS probes all receive 439 after body. |
| H2d-35 | 3 | TAKETHIS | code 436; permitted [439] | `Path: not-for-mail\r\nDate: Mon, 21 Sep 2026 12:00:00 +0000\r\nFrom: \xc3\xa… (6237 bytes)` | normal reply; final drain is not server-close evidence | `build/h2c-fn1/shard-2/repro-409-peer-whole-00069.json` | fn1-bug | specs/nntp.md:530-534,2428-2435; rfc4644.txt:370-387 | Layer D: echo offered Message-ID on every reply, including local 436; 439 for explicit body bound. |
| H2d-36 | 9 | unknown | wrong number of status lines (including closing 400) | `From: author@example.invalid\r\n` | `LA\x00ST\r\x00\nPOS\r\n` → 501 → clean EOF | `build/h2c-fn1/shard-2/repro-410-reader-whole-00072.json` | model-bug | specs/nntp.md:513-518; rfc3977.txt:547-551,5866-5899 | Closed by model close alternative plus driver attribution to preceding 501. |
| H2d-37 | 6 | unknown | code 501; permitted [500] | `Message-ID: <fz601.2.117886944@fuzz.invalid>\r\n` | normal reply; final drain is not server-close evidence | `build/h2c-fn1/shard-3/repro-601-reader-whole-00000.json` | spec-ambiguity | A13; specs/nntp.md:83-87; rfc3977.txt:543-555,5422 | Keep open: choose invalid-keyword policy; retain well-formed unknown 500. |
| H2d-38 | 3 | closed | expected no reply and no framing | `NEWNEWS ? 99991231 235959 gmt\t\r\n` | IHAVE block → 437; no QUIT / no prior EOF | `build/h2c-fn1/shard-3/repro-601-peer-whole-00006.json` | model-bug | specs/nntp.md:513-518 | Closed: dot-terminated rejected article may drain and continue; retain QUIT silence requirement. |
| H2d-39 | 9 | closed | expected no reply and no framing | `GROUP fn.\xff  \rIHAVE <fz602.2.257017492@fuzz.invalid>\r\n` | POST block → 441; no QUIT / no prior EOF | `build/h2c-fn1/shard-3/repro-602-reader-whole-00009.json` | model-bug | specs/nntp.md:513-518 | Closed: dot-terminated rejected article may drain and continue; retain QUIT silence requirement. |
| H2d-40 | 6 | syntax | code 502; permitted [501] | `TAKETHIS <f\xcaz603.1.25457411@fuzz.invalid>Path: src.example.invalid!not-for-mail\r\n` | normal reply; final drain is not server-close evidence | `build/h2c-fn1/shard-3/repro-603-reader-whole-00018.json` | spec-ambiguity | A15; specs/nntp.md:78-80; rfc3977.txt:547-555,5866-5899 | Keep open: choose malformed-argument versus reader transit-permission precedence. |
| H2d-41 | 3 | syntax | wrong number of status lines (including closing 400) | `TAKETHIS <f\xcaz603.1.25457411@fuzz.invalid>Path: src.example.invalid!not-for-mail\r\n` | current command: timeout, then client shutdown; no observed pre-shutdown EOF | `build/h2c-fn1/shard-3/repro-603-peer-whole-00024.json` | model-bug | A14; specs/nntp.md:513-518,2421-2422; rfc4644.txt:375-387 | Closed by HT: no reply before article is required; corresponding HS probes all receive 439 after body. |
| H2d-42 | 9 | unknown | code 501; permitted [500] | `POSTFrom: \xc3\xa9 <a@b>\r\n` | normal reply; final drain is not server-close evidence | `build/h2c-fn1/shard-3/repro-604-reader-whole-00027.json` | spec-ambiguity | A13; specs/nntp.md:83-87; rfc3977.txt:543-555,5422 | Keep open: choose invalid-keyword policy; retain well-formed unknown 500. |
| H2d-43 | 6 | unknown | code 501; permitted [500] | `Path: src.example.invalid!not-for-mail\r\n` | normal reply; final drain is not server-close evidence | `build/h2c-fn1/shard-3/repro-605-reader-whole-00036.json` | spec-ambiguity | A13; specs/nntp.md:83-87; rfc3977.txt:543-555,5422 | Keep open: choose invalid-keyword policy; retain well-formed unknown 500. |
| H2d-44 | 6 | syntax | wrong number of status lines (including closing 400) | `HEAD <fz605.1.154121121@fuzz.invalid>\nAUTHINFO PASS fuzz-password\r\n` | `LIST HEADERS R\nANGE\r\n` → 501 → clean EOF | `build/h2c-fn1/shard-3/repro-605-node-whole-00039.json` | model-bug | specs/nntp.md:513-518; rfc3977.txt:547-551,5866-5899 | Closed by model close alternative plus driver attribution to preceding 501. |
| H2d-45 | 3 | TAKETHIS | code 436; permitted [439] | `Path: a!a!a!a!a!a!a!a!a!a!a!a!a!a!a!a!a!a!a!a!a!a!a!a!a!a!a!a!a!a!a!a!a!a!a!… (534 bytes)` | normal reply; final drain is not server-close evidence | `build/h2c-fn1/shard-3/repro-606-peer-whole-00051.json` | fn1-bug | specs/nntp.md:530-534,2428-2435; rfc4644.txt:370-387 | Layer D: echo offered Message-ID on every reply, including local 436; 439 for explicit body bound. |
| H2d-46 | 9 | syntax | wrong number of status lines (including closing 400) | `\tSTAT <a\t@b>\r\n` | `\rNEXT\r\n` → 501 → clean EOF | `build/h2c-fn1/shard-3/repro-608-reader-whole-00054.json` | model-bug | specs/nntp.md:513-518; rfc3977.txt:547-551,5866-5899 | Closed by model close alternative plus driver attribution to preceding 501. |
| H2d-47 | 6 | syntax | wrong number of status lines (including closing 400) | `BODY -1\r\n` | `DATE xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx… (519 bytes)` → 501 → clean EOF | `build/h2c-fn1/shard-3/repro-609-node-whole-00066.json` | model-bug | specs/nntp.md:513-518; rfc3977.txt:547-551,5866-5899 | Closed by model close alternative plus driver attribution to preceding 501. |
| H2d-48 | 4 | syntax | wrong number of status lines (including closing 400) | `POST xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx… (513 bytes)` | `XPAT X-Fuzz 1-1 !fn.*\nCAPABILITIES\r\n` → 501 → clean EOF | `build/h2c-fn1/shard-3/repro-611-reader-whole-00072.json` | model-bug | specs/nntp.md:513-518; rfc3977.txt:547-551,5866-5899 | Closed by model close alternative plus driver attribution to preceding 501. |

**Recorded-byte replay after HT:** all 322 original rows were replayed using
original `exchanges` and reply-time wire evidence, not minimized outcomes.
**159 match / 163 remain open**: 130 permitted malformed-command closes,
14 article-rejection continuations, and all 15 malformed TAKETHIS command-prefix
timeouts match. The timeout rows match because no reply is expected before the
article; this does not establish an unseen article reply or convert timeout to
EOF. Open rows are 37 fn1 bugs, 123 specification ambiguities, and 3 historical
TLS half-close evidence failures. The H2c table remains the adjudication of its
original evidence; run-2 wire facts are not retroactively substituted into run 1.

**HS harness follow-up and HT resolution (2026-10-29).** Live TLS uses `TLS`,
an `SSLObject`/`MemoryBIO` transport: `unwrap` emits client close_notify, then
application reads retain the incomplete-body reply before server close_notify.
No TCP half-close occurs on TLS; historical raw-half-close rows remain open.
The TLS control covers TLS 1.2/1.3 and observes 441 after the client alert; where
loopback bind is forbidden, socket-pair fallback is recorded.

The six HS ledgers (`diff-{0,203,204,405,408,603}`) replay to **15 matched /
39 open**. All 15 A14 probes read the body before returning 439. Each row in
this table covers exactly its `whole`, `per-item`, and `bytewise` observations:

| Seed | Original H2d group | Offered line shape | HS reply (all three cuts) | HT disposition of each cut |
|---|---|---|---|---|
| 0 | H2d-02 | `TAKETHIS <a@b@c` | `439 <a@b@c` | All three original prefixes and all three HS probes match. |
| 204 | H2d-17 | `TAKETHIS <a@b` | `439 <a@b` | All three original prefixes and all three HS probes match. |
| 405 | H2d-31 | `TAKETHIS <valid-id>Path: not-for-mail` | `439 -` | All three original prefixes and all three HS probes match. |
| 408 | H2d-34 | `TAKETHIS <a@b>junk` | `439 <a@b>junk` | All three original prefixes and all three HS probes match. |
| 603 | H2d-41 | invalid UTF-8 ID glued to `Path:` | `439 -` | All three original prefixes and all three HS probes match. |

Contrary to the initial evidence summary, these saved 15 probes contain no
no-argument line: the two header-glued cases receive `439 -`. A no-argument
command is covered by the independent model test.

RFC 4644 §2.5.2 (`rfc4644.txt:375-387`) requires the immediately sent article
block; the model now consumes it before 439 for malformed/missing identifiers.
The echo of an invalid or absent identifier is unspecified, so token-as-sent or
`-` is accepted; a valid ID still requires its exact echo. `--takethis-probe`
remains an opt-in five-octet diagnostic, now sent immediately after a malformed
TAKETHIS command. Both live comparison and recorded replay judge its two phases
through the actual model. There is no separate permissive A14 verdict. No reply
after the body, 239 success, or an early command reply still fails. The early-439
mutation then parses the body as commands and is caught. A13/A15/A16 remain open.

Design judgment beside the implementation: preserving A14 as a timing ambiguity
would retain a false positive after both the RFC ordering and the paired probe
resolve it. The model therefore owns the transition; the probe adapter reuses
it instead of maintaining a second, weaker 439-only oracle. Matching old
command-only records remains explicitly a prefix claim.
