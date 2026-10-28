# H2b recorded differences

This ledger records wire disagreements, not automatic adjudications. The laptop
rows below are deliberately planted **fake-target** faults, not fn1 findings.
No fn1 image was run on the laptop. The seat appends real fn1 rows after hbox.

## JSONL format

Each failed comparison writes one object to `OUT/differences.jsonl`:

| Field | Meaning |
|---|---|
| `seed`, `mode`, `cut`, `transport` | Generator seed; reader/node/peer; whole/per-item/bytewise; plain/starttls/implicit. |
| `command_index` | Zero-based complete wire command or article-block index; -1 is greeting/transport setup. |
| `command_hex` | Complete failing command bytes; empty for greeting, EOF or environment failures. |
| `reply_hex` | Status plus wire block, truncated to its first 1,024 bytes. |
| `rule`, `spec`, `detail` | H2a verdict rule, source citation, and explanation. |
| `class` | `unclassified` initially; seat may adjudicate as described below. |
| `liveness` | Optional additional `node_verdict` or unconsumed-output finding. |
| `reproducer` | Relative filename of the associated minimized JSON reproducer. |

Classes:

- `fn1-bug`: a determinate specification and a demonstrated departure by fn1.
- `spec-ambiguity`: the seat identifies a relevant accepted alternative and its
  exact ambiguity entry in `SPEC-MAP.md`; retain that citation in the adjudication.
- `model-bug`: **seat decision only**, with the specification line and proposed
  model correction. The driver never emits this classification.
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

`whole` sends one flight up to a protocol transition; `per-item` preserves original
item boundaries within that flight; `bytewise` sends each byte separately. Flights
end at body, STARTTLS, COMPRESS, and authentication boundaries. Ordinary commands
are pipelined, then their expectations resolve and commit in order. A complete
article block is one ddmin unit. An incomplete suffix is sent before client EOF;
it is not invented into a complete command. A failed comparison stops semantic
updates for that session; the EOF/liveness check still runs. Every mismatch gets
a same-rule ddmin attempt and a reproducer; the time budget does not assert global
minimality. Greeting and setup checks are performed but excluded from the
`commands_compared` and `matches` command counters.

`Node` in this tree initializes **empty** `fn.test` and `fn.letters` groups.
`PRESENT_IDS` is a generator pool, not a preloaded article. The live model starts
empty with Node's source-address peer, fuzz login and parsed auth/posting config.
Every live attempt (including each cut and minimizer candidate) uses a fresh Node
and scratch store. The fake alone has an explicit retained PRESENT_IDS article
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

## fn1 findings

Pending the seat's hbox run. Append JSONL rows and adjudications here; do not
relabel the planted fake controls as fn1 bugs.
