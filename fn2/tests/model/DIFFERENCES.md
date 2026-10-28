# H2b recorded differences

This ledger records wire disagreements, not automatic adjudications. The laptop
rows below are deliberately planted **fake-target** faults, not fn1 findings.
No fn1 image was run on the laptop. The H2c section adjudicates the seat’s
four-shard hbox run separately from those fake controls.

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
