# BOUNDS recount at HEAD 32b2fa366 (origin/dev), 2026-10-04

Inputs: .spw/audits/bounds/constant-candidates.json (313 candidates, revision 9df4a3a4e); caps lanedump; planning/design-2026-09-25-bounds.md sec 1.1-1.4, 4-5; git log 9df4a3a4e..HEAD. Method: names extracted by script (recount2.py), definition located by name over books/**/*.lisp and host/**/*.lisp (2013 files), declaration form compared to the JSON, callers read for every suspected D.

Totals (313): D 19, W 128, RFC 26, N 135, dup 0, converted/deleted 5. dup is 0: the design 1.3 dup sites (store-host.lisp *fn-store-capacity*, run_store.py MAX_TRANSACTION_COUNT, signature-command.lisp literal 32768, fn_verify.py ARTICLE_MAX) are no longer in the tree and were not in the JSON; the one that remains, +fnn-tcl-transfer-mru+ 1048576 (host/native/tcpcl.lisp:45), is not in the JSON.
No value in the JSON changed between 9df4a3a4e and HEAD: all 308 present constants have the same declaration form; no constant moved files. 5 are gone. The other D27 conversions in the log (P2 8935e8b2d record/article/frame codec widths, PRF-102 2c0c6a084 config generations + credentials, header-limits-profile 07e022db0, consumer count 3ed5d0ddb, G5 profile table 6b981d75a, 105832cca TCPCL node ID) all landed BEFORE 9df4a3a4e, so the audit already saw their results (e.g. *fn-article-max-octets* 4261412864, *fn-frame-max-payload* 2^32-1).

## D27 CEILINGS NOT CONVERTED

Ledger column: grep of planning/repair/items/*.json for each symbol / file / title found NO item tracking any of these (the ledger items that mention D27 or "ceiling" are S002, S011, S013, S029, S035, S046, S047, S048, S051, S125, S132, sl-cold-line-quanta: all per-step work/buffer defects, none a data ceiling; S069 only mentions segment-index-exhausted as a remote limit; S086 touches the clone command, not its caps). So "ledger: NONE" for every row, and every row needs an item.

"caps residual" = one of the 5 rows in caps.md continuation / design 1.4 binding list: (1) 2^24 BP profile ceiling with its codec widths, (2) custody rows, (3) EID length, (4) blocks-per-bundle, (5) lab receive-evidence.

| # | name | file:line at HEAD | value | what data it caps | design-doc row | caps residual | ledger |
|---|---|---|---|---|---|---|---|
| 1 | `*fn-bpn-machine-max-octets*` | bp-node-machine.lisp:19; limit predicate fn-bpn-machine-limitp :383-385 (<= x 16777216) | 2^24 | every BP node profile field (OCTETS, ADU, BUNDLE, held octets) cannot exceed 16 MiB; a store profile may admit an article up to 2^32-1 so BP cannot carry what the store accepts | 1.4 rows 1-5 (D, "raise to the frame LENGTH width with the codec widths") | YES, residual #1 (counted once with the next five) | NONE |
| 2 | `*fn-bpa-max-octets*` | bp-adu.lisp:31 | 2^24 | ADU codec width (same row) | 1.4 row 2 | YES #1 | NONE |
| 3 | `*fn-bpa-max-article*` | bp-adu.lisp:37 | 2^24-2106 | ADU article width (same row) | 1.4 row 2 | YES #1 | NONE |
| 4 | `*fn-bpb-max-data*` | bp-bundle.lisp:56 | 2^24 | bundle payload codec width (same row) | 1.4 row 3 | YES #1 | NONE |
| 5 | `*fn-bpb-max-input*` | bp-bundle.lisp:67 | 2^24 | bundle decode input width (same row) | 1.4 row 3 | YES #1 | NONE |
| 6 | `*fn-bpnf-max-held-image*` | bp-node-foundation.lisp:18 | 2^24 | held-image codec width (same row); derived *fn-bpn-lifecycle-max-payload* bp-node-machine-codec.lisp:30 (16780288) moves with it | 1.4 row 4 | YES #1 | NONE |
| 7 | `*fn-bpn-machine-max-records*` | bp-node-machine.lisp:21 (uses: bp-node-machine-authorization.lisp:465, bp-node-foundation.lisp:664,734, bp-node-machine-guards.lisp:53) | 4096 | FNBS rows (custody) the machine state holds at once; a rotation carries held rows into the new generation so a node holding 4096 bundles in custody takes no more; profile field 9 max-bp-rows exists (byte-store-frame.lisp:139) but this constant is the live cap | 1.4 row "bpn-machine-max-records" (D for rows held at once); 1.3 row | YES #2 | NONE |
| 8 | `*fn-bpc-max-text*` | bp-primary-cbor.lisp:111 (uses: bp-channel-ingress.lisp:22, bp-primary.lisp:898) | 1024 | a dtn EID scheme-specific part (names of nodes/endpoints); RFC 9171 sets none | 1.4 row (A, "a node-profile field") | YES #3 | NONE |
| 9 | `*fn-bpb-max-blocks*` | bp-bundle.lisp:60 (use: :473) | 32 | canonical blocks in one bundle; per bundle, parse linear in blocks, so I class it W; the design itself says "a work bound per bundle" yet lists it for a profile field | 1.4 row (A) | YES #4 (classed W here; see class note) | NONE |
| 10 | `*fn-bpn-evidence-max-records*` | bp-receive-evidence.lisp:21 (uses :26,:78,:100) | 4096 | receive-evidence identities over the lab receiver journal LIFETIME (`bp receive STORE`, not the node); the 4097th faults recovery; startup reads every entry | 1.4 row (D) | YES #5 | NONE |
| 11 | `*fn-bpn-machine-max-job-octets*` | bp-node-machine.lisp:20 (= *fn-frame-max-blob*); uses bp-node-machine-authorization.lisp:208-210, bp-node-machine-codec.lisp:406, bp-report-author.lisp:83 | 131072 | the encoded bundle of one SENDER job: a send is refused when the bundle exceeds 128 KiB, whatever the profile ADU/bundle octets (up to 2^24); bp-limits.lisp:10-17 admits "a sender cannot yet hold an ADU above about 64 KiB as one job" (PKT-294) | NONE in the bounds design (only planning/proofs.json:5599,5639,5787 "PKT-294") | NO: not one of the 5 rows; the "2^24" row is receive side only | NONE (PKT-294 is a proofs.json note, not a ledger item) |
| 12 | `*fn-pol-max-members*` | policy.lisp:58 (uses :97 fn-pol-policy-p, :127 decode) | 64 | members of one group policy; profile field 12 max-policy-members is defined (byte-store-frame.lisp:142, store-profile-namespace.lisp:29,45) and NOTHING reads it for admission | 1.3 row (D) + decisions-packets-2026-09-25.md; P5 | NO | NONE |
| 13 | `*fn-pol-max-name-octets*` | policy.lisp:59 (use :71 fn-pol-namep) | 128 | group name inside a policy: a group named with 129..256 octets (record ceiling 256, NNTP 460) cannot have a policy | NONE (design 1.2 mentions the 128->256 group name change only for records-shape) | NO | NONE |
| 14 | `*fn-record-max-group-name*` | records-shape.lisp:51 (co-bound: *fn-cfg-max-label* config.lisp:53 = 256, native-admin staging) | 256 | group-name length: below the RFC 3977 wire limit 460 (nntp-syntax.lisp:114); profile field 6 max-group-name-octets can only reach this constant | 1.2 row (D; comment records-shape.lisp:44-50 says raising needs the label raised, packet P1 config) | NO | NONE |
| 15 | `*fn-ff-max-observations*` | feed-filename.lisp:22 (use :93 fn-feed-filename-observation-limit) | 8192 | FNFD durable feed journal names the host may retain at recovery; over it recovery faults; unlike store-sweep there is no next round, so it caps durable journal names (about 1170 peers at depth 7) | 1.3 row (D) | NO | NONE |
| 16 | `*fn-cpa-clone-max-entries*` | checkpoint-auxiliary.lisp:14 (host/native/checkpoint.lisp:450) | 1000000 | entries in a store tree the operator `checkpoint clone` will copy | 1.3 row (D) | NO | NONE (S086 is the clone off-Linux refusal) |
| 17 | `*fn-cpa-clone-max-bytes*` | checkpoint-auxiliary.lisp:15 (host/native/checkpoint.lisp:452) | 1099511627776 (1 TiB) | bytes in a store tree the clone will copy | 1.3 row (D) | NO | NONE |
| 18 | `*fn-th-max-authors*` | topic-history-metadata.lisp:12 (uses :68,:73,:176) | 16 | authors per topic root / control event (experimental topic-history surface) | 1.3 row (D, experimental) | NO | NONE |
| 19 | `*fn-th-max-anchors*` | topic-history-admission.lisp:8 (use :99) | 16 | anchors per topic (experimental) | 1.3 row (D, experimental) | NO | NONE |
| 20 | `*fn-th-max-report-quota*` | topic-history-admission.lisp:9 (uses :96, topic-history-store-events.lisp:39) | 64 | report quota of a topic admission (experimental) | 1.3 row (D, experimental) | NO | NONE |

Row count: 19 constants. By row-of-the-design that is 12 distinct ceilings: BP 2^24 group (6 constants, one row), custody rows, EID, evidence, SENDER JOB IMAGE (new), policy members, policy name (new), group name, FNFD observations, clone entries+bytes (2), topic authors/anchors/quota (3, experimental). Of the 5 caps residual rows: #1 (6 constants), #2, #3, #5 are D; #4 blocks-per-bundle (*fn-bpb-max-blocks*) I classed W (design 1.4: "a work bound per bundle: the parse is linear in blocks"), so my D constants include 4 of the 5 residual rows (counting #1 as one row) and the other 8 rows are NOT in the caps list: sender job image, policy members, policy name, group name, FNFD observations, clone entries/bytes, topic-history.

### Lifetime-counter widths (classed N, FLAGGED: finite lifetime counts bounded by a name or integer width)

| name | file:line | value | what runs out | note |
|---|---|---|---|---|
| `*fn-lgs-max-segment*` | store-log-segments.lisp:41 (uses :83 fn-lgs-next-segment, :419 listing bound; store-log.lisp:318 rotation index 999999) | 999999 | log segment index `journal/NNNNNN.log`; one rotation per checkpoint, refused by name `segment-index-exhausted` (host/native/io.lisp:8270,8326) after 999,999 | no design row, no ledger item (S069 only cites the refusal as "a remote limit") |
| `*fn-native-admin-config-name-limit*` | native-admin-shape.lisp:22 (uses :147,:167) | 100000000 | configuration generation file name (8 digits); generation >= 10^8 refused | no design row |
| `*fn-cbor-max-uint*` / `*fn-sf-max-uint*` | cbor.lisp:24 / store-files.lisp:44 (use :689 frontier < max) | 2^32-1 | transaction ID space, burned reservations included | design 1.2 "codec width"; widened by P6 (not landed) |

### Not D after reading the callers (design rows now stale)

- `*fn-stxk-max-octets*`/`-snapshot*` (stx-keyring-records.lisp:15,17): design 1.3 says "whole-keyring snapshot caps principals". At HEAD a kind-3 snapshot is ONE principal plus its two keys (hybrid-store.lisp:770-781, about 2 KiB), so 65536 caps nothing countable. W.
- `*fn-cc-max-events*`/`-octets*` (checkpoint-compaction.lisp:18-19): design 1.2 says D (one pack = whole history). The pack layer is gone; the comment :11-17 re-labels it one scheduling quantum, and `fn-cc-capture`/`fn-cc-decode*` have no caller outside the book (grep books host). Effectively dead: retire rather than convert. W.
- `*fn-cfg-max-rows*`/`-deltas*` (config.lisp:54-55): PRF-171 converted to per-delta work bounds (config.lisp:1122-1131, peer-carriage-rows.lisp:252). W.
- `*fn-bpf-max-length*`/`-fragments*`: reference reassembler only; the node uses uncapped fn-bpfw-reassemble; bp-fragment-send.lisp:1065 comment and :1116 hypotheses are stale but no served cap. W.
- `*fn-bpnf-received-max-records*` (2 x 4096): per journal generation since the rotation; W.
- `*fn-ncfg-max-octets*`/`-lines*`: fixed-schema file (twelve tables, forty keys); W per design 1.4.
- `*fn-nctrl-max-active-clients*` (native-control.lisp:111): still `(fn-profile-limit :control-clients)` = 16 at HEAD; CAPS-4 189d6c832 deletes it for `[control] max_clients` but is only on origin/lane/caps, NOT in HEAD (git merge-base --is-ancestor says no; CAPS-1 018abdd39, CAPS-2 f21b92dea, CAPS-3 bb3cc6b24, 8238ced25 are in HEAD). A work bound by the root ruling.
- Borderline W I did not promote: `*fn-auth-max-name-octets*` 64 (login names; design keeps), `*fn-mbx-max-octets*` 8192 (a From value is refused above 8192 although a raised profile header limit would admit it; mailbox.lisp:274), `*fn-cbor-max-bytes*`/`-input*` 65535/65538 (generic entry; checkpoint tree strings checkpoint-codec.lisp:239,530 inherit it; 17 files, not each traced), `*fn-pol-max-terms-octets*` 256.

## CONVERTED / DELETED (5 of 313)

| name | was | status | evidence |
|---|---|---|---|
| `*fn-aj-max-records*` | books/app-journal.lisp:15 | GONE | deleted by CAPS-1 018abdd39: app-journal capacity is its operator profile (app-journal-profile RECORDS OCTETS, default 2^20 / 2^40; books/app-journal.lisp fn-ajpf-*); caps lanedump line 8, design 1.4 row REMOVED |
| `*fn-aj-workflow-max-aggregate*` | books/app-journal.lisp:16 | GONE | deleted by CAPS-1 018abdd39: app-journal capacity is its operator profile (app-journal-profile RECORDS OCTETS, default 2^20 / 2^40; books/app-journal.lisp fn-ajpf-*); caps lanedump line 8, design 1.4 row REMOVED |
| `*fn-aj-receipt-max-aggregate*` | books/app-journal.lisp:17 | GONE | deleted by CAPS-1 018abdd39: app-journal capacity is its operator profile (app-journal-profile RECORDS OCTETS, default 2^20 / 2^40; books/app-journal.lisp fn-ajpf-*); caps lanedump line 8, design 1.4 row REMOVED |
| `*fn-aj-carry-max-aggregate*` | books/app-journal.lisp:20 | GONE | deleted by CAPS-1 018abdd39: app-journal capacity is its operator profile (app-journal-profile RECORDS OCTETS, default 2^20 / 2^40; books/app-journal.lisp fn-ajpf-*); caps lanedump line 8, design 1.4 row REMOVED |
| `*fn-cu-max-line*` | books/peer-catchup.lisp:67 | GONE | deleted by 450a088e5 (catch-up through the bounded spool controller) |

Also converted but still present as a codec ceiling or profile default (class N above, "converted" in spirit): see group `profile` in the table. The profile fields that replaced earlier constants (byte-store-frame.lisp:138-147: consumers 8, bp-rows 9, config generations 10, credentials 11, policy members 12, header limits 13-15) are all present; policy members (field 12) is defined but unwired (D row 11); bp-rows (field 9) is defined but the live cap is still *fn-bpn-machine-max-records* (D row 7).

## FULL TABLE (all 313)

### Converted / deleted (5)

| name | HEAD file:line | value | class | reason |
|---|---|---|---|---|
| `*fn-aj-max-records*` | books/app-journal.lisp:15 (was) |  | - | deleted by CAPS-1 018abdd39: app-journal capacity is its operator profile (app-journal-profile RECORDS OCTETS, default 2^20 / 2^40; books/app-journal.lisp fn-ajpf-*); caps lanedump line 8, design 1.4 row REMOVED |
| `*fn-aj-workflow-max-aggregate*` | books/app-journal.lisp:16 (was) |  | - | deleted by CAPS-1 018abdd39: app-journal capacity is its operator profile (app-journal-profile RECORDS OCTETS, default 2^20 / 2^40; books/app-journal.lisp fn-ajpf-*); caps lanedump line 8, design 1.4 row REMOVED |
| `*fn-aj-receipt-max-aggregate*` | books/app-journal.lisp:17 (was) |  | - | deleted by CAPS-1 018abdd39: app-journal capacity is its operator profile (app-journal-profile RECORDS OCTETS, default 2^20 / 2^40; books/app-journal.lisp fn-ajpf-*); caps lanedump line 8, design 1.4 row REMOVED |
| `*fn-aj-carry-max-aggregate*` | books/app-journal.lisp:20 (was) |  | - | deleted by CAPS-1 018abdd39: app-journal capacity is its operator profile (app-journal-profile RECORDS OCTETS, default 2^20 / 2^40; books/app-journal.lisp fn-ajpf-*); caps lanedump line 8, design 1.4 row REMOVED |
| `*fn-cu-max-line*` | books/peer-catchup.lisp:67 (was) |  | - | deleted by 450a088e5 (catch-up through the bounded spool controller) |

### BP node and codec (27)

| name | HEAD file:line | value | class | reason |
|---|---|---|---|---|
| `*fn-bpa-max-metadata*` | books/bp-adu.lisp:23 | 256 | N | node-generated BP field width |
| `*fn-bpa-max-octets*` | books/bp-adu.lisp:31 | 16777216 | D | the 2^24 BP profile ceiling (fn-bpn-machine-limitp bp-node-machine.lisp:383) and its codec widths: a node profile cannot admit an ADU/bundle/held image past 16 MiB although a store profile may admit an article up to 2^32-1; one row, caps residual #1 |
| `*fn-bpa-max-article*` | books/bp-adu.lisp:37 | (- *fn-bpa-max-octets* 2106) | D | the 2^24 BP profile ceiling (fn-bpn-machine-limitp bp-node-machine.lisp:383) and its codec widths: a node profile cannot admit an ADU/bundle/held image past 16 MiB although a store profile may admit an article up to 2^32-1; one row, caps residual #1 |
| `*fn-bpb-max-data*` | books/bp-bundle.lisp:56 | 16777216 | D | the 2^24 BP profile ceiling (fn-bpn-machine-limitp bp-node-machine.lisp:383) and its codec widths: a node profile cannot admit an ADU/bundle/held image past 16 MiB although a store profile may admit an article up to 2^32-1; one row, caps residual #1 |
| `*fn-bpb-max-blocks*` | books/bp-bundle.lisp:60 | 32 | W | canonical blocks per bundle (bp-bundle.lisp:473); design 1.4 calls it a work bound (parse linear in blocks) yet lists it on the caps binding list as a node-profile field; caps residual #4; I class W, same as the design |
| `*fn-bpb-max-input*` | books/bp-bundle.lisp:67 | 16777216 | D | the 2^24 BP profile ceiling (fn-bpn-machine-limitp bp-node-machine.lisp:383) and its codec widths: a node profile cannot admit an ADU/bundle/held image past 16 MiB although a store profile may admit an article up to 2^32-1; one row, caps residual #1 |
| `*fn-bpcd-payload-limit*` | books/bp-clock-domain.lisp:14 | 40 | N | node-generated BP field width |
| `*fn-bpnf-received-max-records*` | books/bp-fnbs-namespace.lisp:12 | (* 2 *fn-bpn-machine-max-records*) | W | received FNBS names per journal GENERATION (2 x 4096); a rotation starts a generation at zero (bp-node-rotation.lisp); design 1.4 says W |
| `*fn-bpnp-max-forward-retries*` | books/bp-forward-attempt.lisp:41 | 3 | W | forwarding retry policy |
| `*fn-bpf-max-length*` | books/bp-fragment.lisp:50 | 65538 | W | capped REFERENCE reassembler domain only; the node reassembles with uncapped fn-bpfw-reassemble (design 1.4); sender plan theorems carry them as hypotheses only (bp-fragment-send.lisp:1116) so no served data cap |
| `*fn-bpf-max-fragments*` | books/bp-fragment.lisp:51 | 64 | W | capped REFERENCE reassembler domain only; the node reassembles with uncapped fn-bpfw-reassemble (design 1.4); sender plan theorems carry them as hypotheses only (bp-fragment-send.lisp:1116) so no served data cap |
| `*fn-bpnf-max-held-image*` | books/bp-node-foundation.lisp:18 | 16777216 | D | the 2^24 BP profile ceiling (fn-bpn-machine-limitp bp-node-machine.lisp:383) and its codec widths: a node profile cannot admit an ADU/bundle/held image past 16 MiB although a store profile may admit an article up to 2^32-1; one row, caps residual #1 |
| `*fn-bpn-lifecycle-max-payload*` | books/bp-node-machine-codec.lisp:30 | 16780288 | N | derived: held-image width 2^24 + 3072; moves with the D row 2^24 |
| `*fn-bpn-lifecycle-max-hidden-stages*` | books/bp-node-machine-codec.lisp:31 | 16 | N | node-generated BP field width |
| `*fn-bpn-lifecycle-max-stage-name-chars*` | books/bp-node-machine-codec.lisp:32 | 128 | N | node-generated BP field width |
| `*fn-bpn-machine-max-jobs*` | books/bp-node-machine.lisp:18 | 64 | W | concurrent carrier jobs (bp-node-profile default rows); jobs are work in flight |
| `*fn-bpn-machine-max-octets*` | books/bp-node-machine.lisp:19 | 16777216 | D | the 2^24 BP profile ceiling (fn-bpn-machine-limitp bp-node-machine.lisp:383) and its codec widths: a node profile cannot admit an ADU/bundle/held image past 16 MiB although a store profile may admit an article up to 2^32-1; one row, caps residual #1 |
| `*fn-bpn-machine-max-job-octets*` | books/bp-node-machine.lisp:20 | *fn-frame-max-blob* | D | sender job image: a BP send is admitted only if its encoded bundle is <= 131072 octets (= plain frame :blob; bp-node-machine-authorization.lisp:208-210, bp-report-author.lisp:83, codec :406), whatever the profile ADU/bundle octets (up to 2^24); documented as PKT-294 (bp-limits.lisp:10-17, planning/proofs.json:5599) but NOT in the bounds design and NOT in the caps lane residual list |
| `*fn-bpn-machine-max-records*` | books/bp-node-machine.lisp:21 | 4096 | D | custody rows: machine admission refuses a state holding more than 4096 FNBS records (bp-node-machine-authorization.lisp:465, bp-node-foundation.lisp:664,734, bp-node-machine-guards.lisp:53); rotation carries held rows over, so 4096 bundles in custody is a hard stop; profile field 9 (max-bp-rows) exists but is not read here; caps residual #2 |
| `*fn-bpnp-max-routes*` | books/bp-node-progress.lisp:14 | 64 | W | LIST-form route argument only; node passes (:table ..) so it never meets the bp-route table (design 1.4) |
| `*fn-bpc-max-text*` | books/bp-primary-cbor.lisp:111 | 1024 | D | dtn EID scheme-specific part capped at 1024 octets (bp-channel-ingress.lisp:22, bp-primary.lisp:898); RFC 9171 sets none; comment says local policy; caps residual #3 |
| `*fn-bpc-max-arity*` | books/bp-primary-cbor.lisp:114 | 16 | W | one primary block decode (RFC 9171 4.3.1 fixes the shape); design 1.4 W |
| `*fn-bpc-max-bytes*` | books/bp-primary-cbor.lisp:118 | 64 | W | one primary block decode (RFC 9171 4.3.1 fixes the shape); design 1.4 W |
| `*fn-bpc-max-items*` | books/bp-primary-cbor.lisp:120 | 128 | W | one primary block decode (RFC 9171 4.3.1 fixes the shape); design 1.4 W |
| `*fn-bpc-max-input*` | books/bp-primary-cbor.lisp:121 | 65536 | W | one primary block decode (RFC 9171 4.3.1 fixes the shape); design 1.4 W |
| `*fn-bpn-evidence-max-records*` | books/bp-receive-evidence.lisp:21 | 4096 | D | receive-evidence identities over the lab receiver journal LIFETIME; the 4097th faults recovery (bp-receive-evidence.lisp:78,100); startup scans every entry; caps residual #5 |
| `*fn-bpn-report-max-input*` | books/bp-status-report.lisp:8 | 4096 | W | one status report decode; shape fixed by RFC 9171 6.1 |

### Group policy (4)

| name | HEAD file:line | value | class | reason |
|---|---|---|---|---|
| `*fn-pol-max-members*` | books/policy.lisp:58 | 64 | D | group policy members capped at 64 (policy.lisp:97 recognizer, :127 decode); store profile field 12 max-policy-members exists (byte-store-frame.lisp:142, store-profile-namespace.lisp:29) but nothing reads it; design 1.3 row, never converted |
| `*fn-pol-max-name-octets*` | books/policy.lisp:59 | 128 | D | a policy group name is capped at 128 octets (policy.lisp:71 fn-pol-namep) below the record group-name ceiling 256 and the NNTP 460: a group with a 129+ octet name cannot have a policy; no design row |
| `*fn-pol-max-terms-octets*` | books/policy.lisp:60 | 256 | W | policy terms text 256 octets: one fixed-shape field of a statement; (borderline, same book as D rows) |
| `*fn-pol-max-policy-items*` | books/policy.lisp:61 | 68 | N | derived: members + fixed items (68 = 64 + 4); moves with *fn-pol-max-members* |

### Feed journal names (1)

| name | HEAD file:line | value | class | reason |
|---|---|---|---|---|
| `*fn-ff-max-observations*` | books/feed-filename.lisp:22 | 8192 | D | FNFD recovery faults if the feed-journal directory holds more than 8192 names (feed-filename.lisp:93 observation-limit); the comment calls it a restart-observation budget but, unlike store-sweep, there is no next round, so it caps durable journal names and indirectly peers (1024 depth-7 journals); design 1.3 row |

### Checkpoint and clone (8)

| name | HEAD file:line | value | class | reason |
|---|---|---|---|---|
| `*fn-cpa-clone-max-depth*` | books/checkpoint-auxiliary.lisp:13 | 16 | W | clone walk directory depth |
| `*fn-cpa-clone-max-entries*` | books/checkpoint-auxiliary.lisp:14 | 1000000 | D | `store checkpoint clone` refuses a store tree over 1,000,000 entries or 1 TiB (host/native/checkpoint.lisp:450-452 via fn-store-checkpoint-clone-max-*); design 1.3 row |
| `*fn-cpa-clone-max-bytes*` | books/checkpoint-auxiliary.lisp:15 | 1099511627776 | D | `store checkpoint clone` refuses a store tree over 1,000,000 entries or 1 TiB (host/native/checkpoint.lisp:450-452 via fn-store-checkpoint-clone-max-*); design 1.3 row |
| `*fn-cpc-max-groups*` | books/checkpoint-codec.lisp:62 | *fn-record-max-groups* | N | checkpoint frame width = frame / record ceilings |
| `*fn-cpc-max-payload*` | books/checkpoint-codec.lisp:63 | *fn-frame-max-payload* | N | checkpoint frame width = frame / record ceilings |
| `*fn-cc-max-events*` | books/checkpoint-compaction.lisp:18 | 4096 | W | one compaction summary = one scheduling quantum (comment checkpoint-compaction.lisp:11-17); design 1.2 listed it D (one pack = whole history) but the pack layer is gone; fn-cc-capture/-decode have no caller outside the book (grep books host): effectively dead, retire |
| `*fn-cc-max-octets*` | books/checkpoint-compaction.lisp:19 | 4194304 | W | one compaction summary = one scheduling quantum (comment checkpoint-compaction.lisp:11-17); design 1.2 listed it D (one pack = whole history) but the pack layer is gone; fn-cc-capture/-decode have no caller outside the book (grep books host): effectively dead, retire |
| `*fn-cpp-selection-read-bound*` | books/checkpoint-publish.lisp:352 | (+ *fn-frame-overhead-octets* 5) | N | derived: frame overhead + 5 |

### Group names (2)

| name | HEAD file:line | value | class | reason |
|---|---|---|---|---|
| `*fn-cfg-max-label*` | books/config.lisp:53 | 256 | N | per-field label width; group names are staged as a label so it co-binds D row *fn-record-max-group-name* (not counted twice) |
| `*fn-record-max-group-name*` | books/records-shape.lisp:51 | 256 | D | group name octets: codec/profile ceiling 256 (records-shape.lisp:51; profile field 6 ceiling is this constant) while the NNTP wire allows 460 (nntp-syntax.lisp:114); tied to *fn-cfg-max-label* 256 (config.lisp:53); design 1.2 row, comment says raising needs the label raised too |

### Topic history (3)

| name | HEAD file:line | value | class | reason |
|---|---|---|---|---|
| `*fn-th-max-anchors*` | books/topic-history-admission.lisp:8 | 16 | D | topic-history (experimental, "fixed-controller P3 root-only admission machine") caps authors per root/control event 16, anchors 16 (topic-history-admission.lisp:99), report quota 64 (:96); low confidence: experimental surface; design 1.3 row |
| `*fn-th-max-report-quota*` | books/topic-history-admission.lisp:9 | 64 | D | topic-history (experimental, "fixed-controller P3 root-only admission machine") caps authors per root/control event 16, anchors 16 (topic-history-admission.lisp:99), report quota 64 (:96); low confidence: experimental surface; design 1.3 row |
| `*fn-th-max-authors*` | books/topic-history-metadata.lisp:12 | 16 | D | topic-history (experimental, "fixed-controller P3 root-only admission machine") caps authors per root/control event 16, anchors 16 (topic-history-admission.lisp:99), report quota 64 (:96); low confidence: experimental surface; design 1.3 row |

### Lifetime-counter widths (4)

| name | HEAD file:line | value | class | reason |
|---|---|---|---|---|
| `*fn-cbor-max-uint*` | books/cbor.lisp:24 | 4294967295 | N | u32 transaction/sequence width (4.29e9 reservations, burned ones included); design 1.2 codec width, widened by P6 (not landed); FLAG lifetime counter |
| `*fn-native-admin-config-name-limit*` | books/native-admin-shape.lisp:22 | 100000000 | N | FLAG lifetime counter: eight-digit configuration generation file name; generation >= 10^8 refused (native-admin-shape.lisp:147,167); no design row |
| `*fn-sf-max-uint*` | books/store-files.lisp:44 | 4294967295 | N | u32 transaction/sequence width (4.29e9 reservations, burned ones included); design 1.2 codec width, widened by P6 (not landed); FLAG lifetime counter |
| `*fn-lgs-max-segment*` | books/store-log-segments.lisp:41 | 999999 | N | FLAG lifetime counter: six-digit log segment name; rotation (one per checkpoint) is refused by name past 999,999 (segment-index-exhausted, host/native/io.lisp:8270,8326; fn-lgs-next-segment :83); a width by construction but a finite lifetime count; no design row; S069 only mentions the refusal |

### Store profile fields, ceilings and defaults (41)

| name | HEAD file:line | value | class | reason |
|---|---|---|---|---|
| `*fn-af-max-field-value-octets*` | books/article-fields.lisp:24 | (fn-article-limit-octets *fn-article-ceiling-limit | N | codec ceiling at the u32 record width (P2 8935e8b2d, before the audit revision); the OPERATOR bound is store profile field 4 (article) / 3 (record) |
| `*fn-article-max-octets*` | books/article.lisp:25 | 4261412864 | N | codec ceiling at the u32 record width (P2 8935e8b2d, before the audit revision); the OPERATOR bound is store profile field 4 (article) / 3 (record) |
| `*fn-article-max-header-octets*` | books/article.lisp:38 | 16384 | N | DEFAULTS of profile fields 13-15 (header-limits-profile 07e022db0); the profile value is the bound (article.lisp:30-37) |
| `*fn-article-max-header-lines*` | books/article.lisp:39 | 256 | N | DEFAULTS of profile fields 13-15 (header-limits-profile 07e022db0); the profile value is the bound (article.lisp:30-37) |
| `*fn-article-max-fields*` | books/article.lisp:40 | 64 | N | DEFAULTS of profile fields 13-15 (header-limits-profile 07e022db0); the profile value is the bound (article.lisp:30-37) |
| `*fn-article-default-limits*` | books/article.lisp:41 | (list *fn-article-max-fields* *fn-article-max-head | N | DEFAULTS of profile fields 13-15 (header-limits-profile 07e022db0); the profile value is the bound (article.lisp:30-37) |
| `*fn-article-ceiling-limits*` | books/article.lisp:530 | (list *fn-article-max-octets* *fn-article-max-octe | N | codec ceiling at the u32 record width (P2 8935e8b2d, before the audit revision); the OPERATOR bound is store profile field 4 (article) / 3 (record) |
| `*fn-bs-meta-max-frontier-payload*` | books/byte-store-frame.lisp:37 | 5 | N | profile/frontier meta frame payload (fixed field widths) |
| `*fn-bs-meta-max-frontier-payload-3*` | books/byte-store-frame.lisp:44 | 9 | N | profile/frontier meta frame payload (fixed field widths) |
| `*fn-bs-meta-max-config-payload*` | books/byte-store-frame.lisp:45 | 600 | N | profile/frontier meta frame payload (fixed field widths) |
| `*fn-bs-pf-max-transactions*` | books/byte-store-frame.lisp:131 | 1 | N | profile FIELD INDEX (1..15), not a limit |
| `*fn-bs-pf-max-history-octets*` | books/byte-store-frame.lisp:132 | 2 | N | profile FIELD INDEX (1..15), not a limit |
| `*fn-bs-pf-max-record-octets*` | books/byte-store-frame.lisp:133 | 3 | N | profile FIELD INDEX (1..15), not a limit |
| `*fn-bs-pf-max-article-octets*` | books/byte-store-frame.lisp:134 | 4 | N | profile FIELD INDEX (1..15), not a limit |
| `*fn-bs-pf-max-groups-per-article*` | books/byte-store-frame.lisp:135 | 5 | N | profile FIELD INDEX (1..15), not a limit |
| `*fn-bs-pf-max-group-name-octets*` | books/byte-store-frame.lisp:136 | 6 | N | profile FIELD INDEX (1..15), not a limit |
| `*fn-bs-pf-max-open-suffix*` | books/byte-store-frame.lisp:137 | 7 | N | profile FIELD INDEX (1..15), not a limit |
| `*fn-bs-pf-max-consumers*` | books/byte-store-frame.lisp:138 | 8 | N | profile FIELD INDEX (1..15), not a limit |
| `*fn-bs-pf-max-bp-rows*` | books/byte-store-frame.lisp:139 | 9 | N | profile FIELD INDEX (1..15), not a limit |
| `*fn-bs-pf-max-config-generations*` | books/byte-store-frame.lisp:140 | 10 | N | profile FIELD INDEX (1..15), not a limit |
| `*fn-bs-pf-max-credentials*` | books/byte-store-frame.lisp:141 | 11 | N | profile FIELD INDEX (1..15), not a limit |
| `*fn-bs-pf-max-policy-members*` | books/byte-store-frame.lisp:142 | 12 | N | profile FIELD INDEX (1..15), not a limit |
| `*fn-bs-pf-max-header-fields*` | books/byte-store-frame.lisp:145 | 13 | N | profile FIELD INDEX (1..15), not a limit |
| `*fn-bs-pf-max-header-lines*` | books/byte-store-frame.lisp:146 | 14 | N | profile FIELD INDEX (1..15), not a limit |
| `*fn-bs-pf-max-header-octets*` | books/byte-store-frame.lisp:147 | 15 | N | profile FIELD INDEX (1..15), not a limit |
| `*fn-bs-profile-transaction-ceiling*` | books/byte-store-frame.lisp:164 | *fn-cbor-max-uint* | N | codec ceiling a profile field may not pass (carries the operator-set value, defined by the codec width) |
| `*fn-bs-profile-record-ceiling-codec*` | books/byte-store-frame.lisp:165 | *fn-frame-max-store-payload* | N | codec ceiling a profile field may not pass (carries the operator-set value, defined by the codec width) |
| `*fn-bs-profile-article-ceiling-codec*` | books/byte-store-frame.lisp:166 | *fn-record-max-payload* | N | codec ceiling a profile field may not pass (carries the operator-set value, defined by the codec width) |
| `*fn-bs-profile-groups-ceiling-codec*` | books/byte-store-frame.lisp:167 | *fn-record-max-groups* | N | codec ceiling a profile field may not pass (carries the operator-set value, defined by the codec width) |
| `*fn-bs-profile-group-name-ceiling-codec*` | books/byte-store-frame.lisp:168 | *fn-record-max-group-name* | N | codec ceiling a profile field may not pass (carries the operator-set value, defined by the codec width) |
| `*fn-bs-profile-count-ceiling*` | books/byte-store-frame.lisp:169 | *fn-cbor-max-uint* | N | codec ceiling a profile field may not pass (carries the operator-set value, defined by the codec width) |
| `*fn-crp-limit-slot*` | books/consumer-remote-query-profile.lisp:8 | "max-consumer-query-groups" | N | a name/table of generated profile limits (no bound by itself; books/profile-limits.lisp is the one profile table) |
| `*fn-dk-bound-kinds*` | books/defkeystone.lisp:147 | '((:visits . -visits-) (:allocation . -allocation- | N | a name/table of generated profile limits (no bound by itself; books/profile-limits.lisp is the one profile table) |
| `*fn-lb-policy-bound-logins*` | books/login-binding.lisp:50 | "bound-logins" | N | a name/table of generated profile limits (no bound by itself; books/profile-limits.lisp is the one profile table) |
| `*fn-profile-limits*` | books/profile-limits.lisp:36 | '((:tls-limit 65536 "symbols" "SBCL's thread-local | N | a name/table of generated profile limits (no bound by itself; books/profile-limits.lisp is the one profile table) |
| `*fn-record-max-octets*` | books/records-shape.lisp:42 | 4294967295 | N | codec ceiling at the u32 record width (P2 8935e8b2d, before the audit revision); the OPERATOR bound is store profile field 4 (article) / 3 (record) |
| `*fn-record-max-groups*` | books/records-shape.lisp:56 | 65535 | N | codec ceiling: u16 group count (65535); the per-article bound is profile field 5 |
| `*fn-record-max-metadata*` | books/records-shape.lisp:59 | 256 | N | node-generated obligation/subject/evidence strings (records-shape.lisp:57-59) |
| `*fn-record-max-payload*` | books/records-shape.lisp:63 | 4261412864 | N | codec ceiling at the u32 record width (P2 8935e8b2d, before the audit revision); the OPERATOR bound is store profile field 4 (article) / 3 (record) |
| `*fn-rck-capacity-slot*` | books/relay-checks.lisp:338 | "refused-offer-capacity" | N | a name/table of generated profile limits (no bound by itself; books/profile-limits.lisp is the one profile table) |
| `*fn-rck-default-capacity*` | books/relay-checks.lisp:344 | 4096 | N | default of an operator config row (refused-offer-capacity slot, relay-checks.lisp:368) |

### Frame codec widths and derived payloads (28)

| name | HEAD file:line | value | class | reason |
|---|---|---|---|---|
| `*fn-bpcc-frame-max-payload*` | books/bp-carry-frame.lisp:26 | (fn-frame-table-width *fn-bpcc-frame-specs*) | N | derived: sum of the frame schema field widths (fn-frame-specs-width) or a refusal-string length |
| `*fn-cev-max-argument-octets*` | books/control-evidence.lisp:814 | (max *fn-cevg-max-msgid-octets* *fn-record-max-met | N | derived: sum of the frame schema field widths (fn-frame-specs-width) or a refusal-string length |
| `*fn-feed-journal-frame-max*` | books/feed-journal.lisp:14 | (+ *fn-feed-journal-frame-min* *fn-feed-max-payloa | N | derived: sum of the frame schema field widths (fn-frame-specs-width) or a refusal-string length |
| `*fn-frame-magic-inbound*` | books/frame-journal.lisp:24 | '(70 78 66 73) | N | frame codec width: u32 LENGTH / text 512 / plain blob 131072 for node-own fields (frame-octets.lisp:36-41; operator data uses (:blob . W)); P2 landed |
| `*fn-frame-inbound-kind*` | books/frame-journal.lisp:30 | 1 | N | frame codec width: u32 LENGTH / text 512 / plain blob 131072 for node-own fields (frame-octets.lisp:36-41; operator data uses (:blob . W)); P2 landed |
| `*fn-frame-max-store-payload*` | books/frame-journal.lisp:38 | 4294967295 | N | frame codec width: u32 LENGTH / text 512 / plain blob 131072 for node-own fields (frame-octets.lisp:36-41; operator data uses (:blob . W)); P2 landed |
| `*fn-frame-max-workflow-payload*` | books/frame-journal.lisp:48 | 16342 | N | frame codec width: u32 LENGTH / text 512 / plain blob 131072 for node-own fields (frame-octets.lisp:36-41; operator data uses (:blob . W)); P2 landed |
| `*fn-frame-max-receipt-payload*` | books/frame-journal.lisp:49 | 269958 | N | frame codec width: u32 LENGTH / text 512 / plain blob 131072 for node-own fields (frame-octets.lisp:36-41; operator data uses (:blob . W)); P2 landed |
| `*fn-frame-max-inbound-payload*` | books/frame-journal.lisp:52 | 4294967295 | N | frame codec width: u32 LENGTH / text 512 / plain blob 131072 for node-own fields (frame-octets.lisp:36-41; operator data uses (:blob . W)); P2 landed |
| `*fn-frame-max-bundle-store-payload*` | books/frame-journal.lisp:53 | 8 | N | frame codec width: u32 LENGTH / text 512 / plain blob 131072 for node-own fields (frame-octets.lisp:36-41; operator data uses (:blob . W)); P2 landed |
| `*fn-frame-max-payload*` | books/frame-octets.lisp:30 | 4294967295 | N | frame codec width: u32 LENGTH / text 512 / plain blob 131072 for node-own fields (frame-octets.lisp:36-41; operator data uses (:blob . W)); P2 landed |
| `*fn-frame-max-text*` | books/frame-octets.lisp:34 | 512 | N | frame codec width: u32 LENGTH / text 512 / plain blob 131072 for node-own fields (frame-octets.lisp:36-41; operator data uses (:blob . W)); P2 landed |
| `*fn-frame-max-blob*` | books/frame-octets.lisp:41 | 131072 | N | frame codec width: u32 LENGTH / text 512 / plain blob 131072 for node-own fields (frame-octets.lisp:36-41; operator data uses (:blob . W)); P2 landed |
| `*fn-frame-max-nat*` | books/frame-octets.lisp:42 | 18446744073709551615 | N | frame codec width: u32 LENGTH / text 512 / plain blob 131072 for node-own fields (frame-octets.lisp:36-41; operator data uses (:blob . W)); P2 landed |
| `*fn-frame-max-identity*` | books/frame.lisp:57 | 1152 | N | frame codec width: u32 LENGTH / text 512 / plain blob 131072 for node-own fields (frame-octets.lisp:36-41; operator data uses (:blob . W)); P2 landed |
| `*fn-heap-capacity-fields*` | books/heap-reservation.lisp:472 | (list *fn-bs-pf-max-transactions* *fn-bs-pf-max-hi | N | derived: sum of the frame schema field widths (fn-frame-specs-width) or a refusal-string length |
| `*fn-nctrl-max-groups-octets*` | books/native-control.lisp:31 | (+ 5 (* (+ 5 *fn-record-max-group-name*) *fn-recor | N | derived: sum of the frame schema field widths (fn-frame-specs-width) or a refusal-string length |
| `*fn-nctrl-max-payload*` | books/native-control.lisp:74 | (fn-frame-specs-width *fn-nctrl-request-spec*) | N | derived: sum of the frame schema field widths (fn-frame-specs-width) or a refusal-string length |
| `*fn-nctrl-max-frame*` | books/native-control.lisp:76 | (+ *fn-frame-overhead-octets* *fn-nctrl-max-payloa | N | derived: sum of the frame schema field widths (fn-frame-specs-width) or a refusal-string length |
| `*fn-nhctrl-max-source*` | books/native-hybrid-control.lisp:38 | (- *fn-frame-max-payload* *fn-nhctrl-author-fixed- | N | derived: sum of the frame schema field widths (fn-frame-specs-width) or a refusal-string length |
| `*fn-nhctrl-max-payload*` | books/native-hybrid-control.lisp:48 | (max (fn-frame-specs-width *fn-nhctrl-author-spec* | N | derived: sum of the frame schema field widths (fn-frame-specs-width) or a refusal-string length |
| `*fn-nls-max-payload*` | books/native-live-status.lisp:700 | (+ *fn-nls-chunk-octets* 64) | N | derived: sum of the frame schema field widths (fn-frame-specs-width) or a refusal-string length |
| `*fn-nls-max-frame*` | books/native-live-status.lisp:701 | (+ *fn-frame-overhead-octets* *fn-nls-max-payload* | N | derived: sum of the frame schema field widths (fn-frame-specs-width) or a refusal-string length |
| `*fn-exp-limit-slots*` | books/public-exposure-rows.lisp:32 | (list *fn-exp-slot-connections* *fn-exp-slot-per-a | N | derived: sum of the frame schema field widths (fn-frame-specs-width) or a refusal-string length |
| `*fn-sbud-refusal-payload-bound*` | books/store-budget-naming.lisp:207 | (fn-record-string-octets "payload exceeds the mode | N | derived: sum of the frame schema field widths (fn-frame-specs-width) or a refusal-string length |
| `*fn-sbud-refusal-group-bound*` | books/store-budget-naming.lisp:209 | (fn-record-string-octets "group count exceeds code | N | derived: sum of the frame schema field widths (fn-frame-specs-width) or a refusal-string length |
| `*fn-sbud-refusal-charge-bound*` | books/store-budget-naming.lisp:211 | (fn-record-string-octets "charge must be a positiv | N | derived: sum of the frame schema field widths (fn-frame-specs-width) or a refusal-string length |
| `*fn-tj-max-payload*` | books/transfer-journal.lisp:85 | (fn-frame-specs-width (fn-tj-spec-for :chunk)) | N | derived: sum of the frame schema field widths (fn-frame-specs-width) or a refusal-string length |

### Signature, key and node-secret widths (11)

| name | HEAD file:line | value | class | reason |
|---|---|---|---|---|
| `*fn-bpsr-max-signature-octets*` | books/bp-signed-receipt.lisp:21 | 4096 | N | key / signature / receipt octet widths (ML-DSA-65 3309, <= 4096) |
| `*fn-bpsr-max-octets*` | books/bp-signed-receipt.lisp:22 | 16384 | N | key / signature / receipt octet widths (ML-DSA-65 3309, <= 4096) |
| `*fn-sig-max-public-key-octets*` | books/crypto-seam.lisp:42 | 4096 | N | key / signature / receipt octet widths (ML-DSA-65 3309, <= 4096) |
| `*fn-sig-max-signature-octets*` | books/crypto-seam.lisp:43 | 4096 | N | key / signature / receipt octet widths (ML-DSA-65 3309, <= 4096) |
| `*fn-digest-max-tag-octets*` | books/crypto-seam.lisp:44 | 64 | N | key / signature / receipt octet widths (ML-DSA-65 3309, <= 4096) |
| `*fn-hc-max-binary-octets*` | books/hybrid-carrier.lisp:19 | 5405 | W | fixed nine-item hybrid carrier parse |
| `*fn-hc-max-field-octets*` | books/hybrid-carrier.lisp:20 | 8192 | W | fixed nine-item hybrid carrier parse |
| `*fn-hsig-v1-max-source*` | books/hybrid-signature.lisp:36 | 65535 | N | signed-source length width: v1 u16 (legacy), v2 u32 (P4 landed) |
| `*fn-hsig-v2-max-source*` | books/hybrid-signature.lisp:37 | 4294967295 | N | signed-source length width: v1 u16 (legacy), v2 u32 (P4 landed) |
| `*fn-ns-epoch-limit*` | books/node-secret.lisp:108 | 4294967296 | N | node-secret epoch u32 / identity u16 field width (node-generated) |
| `*fn-ns-identity-limit*` | books/node-secret.lisp:109 | 65536 | N | node-secret epoch u32 / identity u16 field width (node-generated) |

### Statement and evidence record shapes (19)

| name | HEAD file:line | value | class | reason |
|---|---|---|---|---|
| `*fn-stmt-max-preds*` | books/statement.lisp:60 | 16 | W | statement/carrier item shape (design 1.3 work-bound list: statement item and header caps) |
| `*fn-stmt-max-header-items*` | books/statement.lisp:61 | 24 | W | statement/carrier item shape (design 1.3 work-bound list: statement item and header caps) |
| `*fn-stmt-max-header-octets*` | books/statement.lisp:62 | 1024 | W | statement/carrier item shape (design 1.3 work-bound list: statement item and header caps) |
| `*fn-stmt-max-payload-octets*` | books/statement.lisp:63 | 8192 | W | statement/carrier item shape (design 1.3 work-bound list: statement item and header caps) |
| `*fn-stmt-max-items*` | books/statement.lisp:64 | 26 | W | statement/carrier item shape (design 1.3 work-bound list: statement item and header caps) |
| `*fn-stmt-max-octets*` | books/statement.lisp:65 | 16384 | W | statement/carrier item shape (design 1.3 work-bound list: statement item and header caps) |
| `*fn-stmt-max-obligation-octets*` | books/statement.lisp:66 | 256 | W | statement/carrier item shape (design 1.3 work-bound list: statement item and header caps) |
| `*fn-stmt-max-receipt-octets*` | books/statement.lisp:67 | 512 | W | statement/carrier item shape (design 1.3 work-bound list: statement item and header caps) |
| `*fn-stxa-max-octets*` | books/stx-accept-records.lisp:31 | (- *fn-cbor-max-uint* (+ 9 346)) | N | derived from the Store frame u32 width less poll-reply overhead; the operator bound is the profile (comment stx-accept-records.lisp:25) |
| `*fn-stxa-max-article-record*` | books/stx-accept-records.lisp:32 | *fn-record-max-octets* | N | derived from the Store frame u32 width less poll-reply overhead; the operator bound is the profile (comment stx-accept-records.lisp:25) |
| `*fn-stxa-max-authored-source*` | books/stx-accept-records.lisp:33 | *fn-cbor-max-uint* | N | derived from the Store frame u32 width less poll-reply overhead; the operator bound is the profile (comment stx-accept-records.lisp:25) |
| `*fn-stxa-max-item*` | books/stx-accept-records.lisp:36 | *fn-cbor-max-uint* | N | derived from the Store frame u32 width less poll-reply overhead; the operator bound is the profile (comment stx-accept-records.lisp:25) |
| `*fn-stx-max-field-octets*` | books/stx-carrier.lisp:60 | 8192 | W | statement/carrier item shape (design 1.3 work-bound list: statement item and header caps) |
| `*fn-stx-max-detached-octets*` | books/stx-carrier.lisp:61 | 6144 | W | statement/carrier item shape (design 1.3 work-bound list: statement item and header caps) |
| `*fn-stx-max-detached-items*` | books/stx-carrier.lisp:62 | 25 | W | statement/carrier item shape (design 1.3 work-bound list: statement item and header caps) |
| `*fn-stx-max-commit-octets*` | books/stx-commit-codec.lisp:5 | 512 | W | statement/carrier item shape (design 1.3 work-bound list: statement item and header caps) |
| `*fn-stxe-max-octets*` | books/stx-evidence-records.lisp:15 | 65538 | W | one verdict evidence record: fixed-shape statement fields |
| `*fn-stxe-max-profile*` | books/stx-evidence-records.lisp:16 | 64 | W | one verdict evidence record: fixed-shape statement fields |
| `*fn-stxe-max-detail*` | books/stx-evidence-records.lisp:17 | 8192 | W | one verdict evidence record: fixed-shape statement fields |

### Keyring snapshot (3)

| name | HEAD file:line | value | class | reason |
|---|---|---|---|---|
| `*fn-stxk-max-octets*` | books/stx-keyring-records.lisp:15 | 131072 | W | a keyring snapshot is ONE principal plus its two keys (~2 KiB: hybrid-store.lisp:770-781), not the whole keyring, so it caps nothing countable; design 1.3 row (whole-keyring snapshot) is stale |
| `*fn-stxk-max-profile*` | books/stx-keyring-records.lisp:16 | 64 | W | a keyring snapshot is ONE principal plus its two keys (~2 KiB: hybrid-store.lisp:770-781), not the whole keyring, so it caps nothing countable; design 1.3 row (whole-keyring snapshot) is stale |
| `*fn-stxk-max-snapshot*` | books/stx-keyring-records.lisp:17 | 65536 | W | a keyring snapshot is ONE principal plus its two keys (~2 KiB: hybrid-store.lisp:770-781), not the whole keyring, so it caps nothing countable; design 1.3 row (whole-keyring snapshot) is stale |

### Configuration (config.lisp, fn.toml) (12)

| name | HEAD file:line | value | class | reason |
|---|---|---|---|---|
| `*fn-cfg-max-rows*` | books/config.lisp:54 | 1024 | W | rows / changes in ONE configuration delta record (config.lisp:1127 "bounds the work of one delta, never the rows one peer holds"; peer-carriage-rows.lisp:252); tables chunk across records (login-binding-live.lisp:539) |
| `*fn-cfg-max-deltas*` | books/config.lisp:55 | 64 | W | rows / changes in ONE configuration delta record (config.lisp:1127 "bounds the work of one delta, never the rows one peer holds"; peer-carriage-rows.lisp:252); tables chunk across records (login-binding-live.lisp:539) |
| `*fn-cfg-max-items*` | books/config.lisp:56 | 65535 | N | configuration record codec width (u16 item count, 65538 octets); a table of any size is published in many records |
| `*fn-cfg-max-octets*` | books/config.lisp:57 | 65538 | N | configuration record codec width (u16 item count, 65538 octets); a table of any size is published in many records |
| `*fn-ncfg-max-node-path*` | books/native-config-show.lisp:1358 | 480 | W | one fn.toml value / path string within a fixed schema; paths are OS-bounded |
| `*fn-ncfg-max-octets*` | books/native-config.lisp:23 | 16384 | W | fn.toml read: fixed schema of twelve tables / forty keys, names no collection (native-config.lisp:15-22 comment; design 1.4 W) |
| `*fn-ncfg-max-lines*` | books/native-config.lisp:24 | 128 | W | fn.toml read: fixed schema of twelve tables / forty keys, names no collection (native-config.lisp:15-22 comment; design 1.4 W) |
| `*fn-ncfg-max-path*` | books/native-config.lisp:25 | 512 | W | one fn.toml value / path string within a fixed schema; paths are OS-bounded |
| `*fn-ncfg-max-text*` | books/native-config.lisp:26 | 256 | W | one fn.toml value / path string within a fixed schema; paths are OS-bounded |
| `*fn-ncfg-max-server*` | books/native-config.lisp:27 | 128 | W | one fn.toml value / path string within a fixed schema; paths are OS-bounded |
| `*fn-ncfg-default-max-connections*` | books/native-config.lisp:30 | (fn-profile-limit :max-connections) | N | default = generated profile row (:max-connections); operator sets [limits] |
| `*fn-ncfg-default-log-max-bytes*` | books/native-config.lisp:45 | 67108864 | W | default of the log writer rotation size [log]; not a datum bound |

### Auth names (2)

| name | HEAD file:line | value | class | reason |
|---|---|---|---|---|
| `*fn-auth-max-name-octets*` | books/auth-credentials.lisp:25 | 64 | W | account/login name octets 64; design 1.3 keeps it as a work bound; borderline name-length (RFC 4643 argument limit is 497) |
| `*fn-prin-max-token-octets*` | books/principal.lisp:38 | 64 | N | principal token is a fixed hex/identity token (64) |

### Consumer cursor shapes (8)

| name | HEAD file:line | value | class | reason |
|---|---|---|---|---|
| `*fn-ncl-max-payload*` | books/consumer-local-control.lisp:22 | 513 | W | local consumer-control frame shapes (fixed tuples) |
| `*fn-ncl-poll-max-payload*` | books/consumer-local-control.lisp:23 | (+ 9 346 *fn-stxa-max-octets*) | W | local consumer-control frame shapes (fixed tuples) |
| `*fn-ncl-status-max-payload*` | books/consumer-local-control.lisp:24 | 13 | W | local consumer-control frame shapes (fixed tuples) |
| `*fn-ncl-max-secret*` | books/consumer-local-control.lisp:25 | 496 | W | local consumer-control frame shapes (fixed tuples) |
| `*fn-ncl-bound-max-payload*` | books/consumer-local-control.lisp:26 | 1024 | W | local consumer-control frame shapes (fixed tuples) |
| `*fn-cp-max-id*` | books/consumer-position.lisp:10 | 64 | W | comment: WORK bound of a fixed cursor shape (D27 community-bounds); consumer COUNT is profile field 9 (consumer-position.lisp:10-20) |
| `*fn-cp-max-token*` | books/consumer-position.lisp:15 | 512 | W | comment: WORK bound of a fixed cursor shape (D27 community-bounds); consumer COUNT is profile field 9 (consumer-position.lisp:10-20) |
| `*fn-crevb-max-chunk*` | books/consumer-remote-event-buffer.lisp:8 | (+ 38 (* 4 *fn-cp-max-id*)) | N | derived from *fn-cp-max-id* |

### Web face (2)

| name | HEAD file:line | value | class | reason |
|---|---|---|---|---|
| `*fn-web-max-idle*` | books/web-config.lisp:33 | 2592000 | W | [web] max_sessions (default 64) / idle_seconds clamps: live in-memory browser sessions, not stored data (web-config.lisp:65-66) |
| `*fn-web-max-sessions*` | books/web-config.lisp:34 | 4096 | W | [web] max_sessions (default 64) / idle_seconds clamps: live in-memory browser sessions, not stored data (web-config.lisp:65-66) |

### Control socket (2)

| name | HEAD file:line | value | class | reason |
|---|---|---|---|---|
| `*fn-nctrl-max-command-frame*` | books/native-control.lisp:84 | 262708 | W | least control read bound, the pre-D27 frame; profile article/group bounds raise it (native-control.lisp:79-84) |
| `*fn-nctrl-max-lease-path*` | books/native-control.lisp:113 | (+ *fn-ncfg-max-path* 5) | N | derived from *fn-ncfg-max-path* + suffix |

### Control clients (1)

| name | HEAD file:line | value | class | reason |
|---|---|---|---|---|
| `*fn-nctrl-max-active-clients*` | books/native-control.lisp:111 | (fn-profile-limit :control-clients) | W | concurrent control clients (work bound, root ruling); converted to [control] max_clients on origin/lane/caps 189d6c832 (CAPS-4), NOT yet in HEAD 32b2fa366 |

### Store node-generated widths (11)

| name | HEAD file:line | value | class | reason |
|---|---|---|---|---|
| `*fn-cpe-max-octets*` | books/consumer-store-events.lisp:8 | 512 | N | node-generated fixed record / file-name width (journal names, mount identity, genesis) |
| `*fn-ff-max-name*` | books/feed-filename.lisp:12 | 256 | N | node-generated fixed record / file-name width (journal names, mount identity, genesis) |
| `*fn-ff-legacy-max-name*` | books/feed-filename.lisp:13 | 250 | N | node-generated fixed record / file-name width (journal names, mount identity, genesis) |
| `*fn-ff-max-v1-chunks*` | books/feed-filename.lisp:15 | 5 | N | node-generated fixed record / file-name width (journal names, mount identity, genesis) |
| `*fn-ff-max-components*` | books/feed-filename.lisp:16 | 7 | N | node-generated fixed record / file-name width (journal names, mount identity, genesis) |
| `*fn-prov-max-field*` | books/provenance-codec.lisp:60 | 32 | N | node-generated fixed record / file-name width (journal names, mount identity, genesis) |
| `*fn-store-event-max-octets*` | books/store-events.lisp:22 | 4096 | N | node-generated fixed record / file-name width (journal names, mount identity, genesis) |
| `*fn-gen-max-payload*` | books/store-genesis.lisp:66 | 512 | N | node-generated fixed record / file-name width (journal names, mount identity, genesis) |
| `*fn-smid-field-max*` | books/store-mount-identity.lisp:81 | 65535 | N | node-generated fixed record / file-name width (journal names, mount identity, genesis) |
| `*fn-smid-max-payload*` | books/store-mount-identity.lisp:82 | (* 5 (+ 2 65535)) | N | node-generated fixed record / file-name width (journal names, mount identity, genesis) |
| `*fn-smid-mountinfo-line-max*` | books/store-mount-identity.lisp:85 | 65536 | N | node-generated fixed record / file-name width (journal names, mount identity, genesis) |

### Integer word widths (20)

| name | HEAD file:line | value | class | reason |
|---|---|---|---|---|
| `*fn-anchor-max-time*` | books/anchor.lisp:93 | *fn-clock-max* | N | integer word width (u32/u64 arithmetic bound), bounded by construction |
| `*fn-bpc-max-uint*` | books/bp-primary-cbor.lisp:108 | 18446744073709551615 | N | integer word width (u32/u64 arithmetic bound), bounded by construction |
| `*fn-cbor-max-uint64*` | books/cbor.lisp:429 | 18446744073709551615 | N | integer word width (u32/u64 arithmetic bound), bounded by construction |
| `*fn-clock-max*` | books/clock.lisp:37 | 18446744073709551615 | N | integer word width (u32/u64 arithmetic bound), bounded by construction |
| `*fn-hrcur-u64-bound*` | books/history-record-cursor.lisp:11 | 18446744073709551616 | N | integer word width (u32/u64 arithmetic bound), bounded by construction |
| `*fn-hrsc-integer-bound*` | books/history-scalar-cursor.lisp:7 | (expt 256 255) | N | integer word width (u32/u64 arithmetic bound), bounded by construction |
| `*fn-mlh-tag-limit*` | books/msgid-linear-exec.lisp:80 | (expt 2 60) | N | integer word width (u32/u64 arithmetic bound), bounded by construction |
| `*fn-mlh-word-limit*` | books/msgid-linear-exec.lisp:82 | (expt 2 61) | N | integer word width (u32/u64 arithmetic bound), bounded by construction |
| `*fn-mpxt-word-limit*` | books/msgid-pages-exec.lisp:90 | (expt 2 64) | N | integer word width (u32/u64 arithmetic bound), bounded by construction |
| `*fn-ncfg-max-decimal-digits*` | books/native-config.lisp:203 | 20 | N | integer word width (u32/u64 arithmetic bound), bounded by construction |
| `*fn-ncfg-max-u64*` | books/native-config.lisp:204 | 18446744073709551615 | N | integer word width (u32/u64 arithmetic bound), bounded by construction |
| `*fn-zar-bound*` | books/nntp-zarticle.lisp:35 | 4294967296 | N | integer word width (u32/u64 arithmetic bound), bounded by construction |
| `*fn-cu-u64-limit*` | books/peer-catchup-serve.lisp:193 | 18446744073709551616 | N | integer word width (u32/u64 arithmetic bound), bounded by construction |
| `*adt-u64-limit*` | books/proto/adt-bytes-lib.lisp:18 | 18446744073709551616 | N | integer word width (u32/u64 arithmetic bound), bounded by construction |
| `*fn-exp-owner-connection-bound*` | books/public-exposure-rows.lisp:67 | (+ 1 *fn-cbor-max-uint*) | N | integer word width (u32/u64 arithmetic bound), bounded by construction |
| `*fn-rl-word-max*` | books/resource-vector-exec.lisp:43 | (1- (expt 2 64)) | N | integer word width (u32/u64 arithmetic bound), bounded by construction |
| `*fn-snap-max-columns*` | books/snapshot-segments.lisp:62 | 255 | N | integer word width (u32/u64 arithmetic bound), bounded by construction |
| `*fn-snap-u64-limit*` | books/snapshot-segments.lisp:63 | 18446744073709551616 | N | integer word width (u32/u64 arithmetic bound), bounded by construction |
| `*fn-scc-u64-bound*` | books/store-checkpoint-codec.lisp:93 | 18446744073709551616 | N | integer word width (u32/u64 arithmetic bound), bounded by construction |
| `*fn-stcp-max-argument-refusal*` | books/substrate-commit-profile-bounds.lisp:4 | (+ (* 256 *fn-cbor-max-uint64*) 255) | N | integer word width (u32/u64 arithmetic bound), bounded by construction |

### Generic CBOR entry (2)

| name | HEAD file:line | value | class | reason |
|---|---|---|---|---|
| `*fn-cbor-max-bytes*` | books/cbor.lisp:25 | 65535 | W | generic one-item CBOR entry (design 1.2: W for generic entry); users that inherit it as a data cap, e.g. checkpoint tree strings (checkpoint-codec.lisp:239,530) hold names not articles; 17 files not each traced |
| `*fn-cbor-max-input*` | books/cbor.lisp:28 | 65538 | W | generic one-item CBOR entry (design 1.2: W for generic entry); users that inherit it as a data cap, e.g. checkpoint tree strings (checkpoint-codec.lisp:239,530) hold names not articles; 17 files not each traced |

### Article parse (1)

| name | HEAD file:line | value | class | reason |
|---|---|---|---|---|
| `*fn-mbx-max-octets*` | books/mailbox.lisp:49 | 8192 | W | one From header value parse (mailbox.lisp:274); minor: a profile may raise header octets past 8192 yet a From > 8192 is refused |

### Protocol limits (RFC) (28)

| name | HEAD file:line | value | class | reason |
|---|---|---|---|---|
| `*fn-af-max-message-id-octets*` | books/article-fields.lisp:15 | 250 | RFC | protocol limit: NNTP RFC 3977 3.1/6, Message-ID RFC 5536 3.1.3, line RFC 5322 2.1.1, DNS 253/63, TCPCLv4 RFC 9174 widths, RFC 2047, wildmat 497 |
| `*fn-article-max-line-octets*` | books/article.lisp:72 | 998 | RFC | protocol limit: NNTP RFC 3977 3.1/6, Message-ID RFC 5536 3.1.3, line RFC 5322 2.1.1, DNS 253/63, TCPCLv4 RFC 9174 widths, RFC 2047, wildmat 497 |
| `*fn-cevg-max-msgid-octets*` | books/control-evidence-grammar.lisp:21 | 250 | RFC | protocol limit: NNTP RFC 3977 3.1/6, Message-ID RFC 5536 3.1.3, line RFC 5322 2.1.1, DNS 253/63, TCPCLv4 RFC 9174 widths, RFC 2047, wildmat 497 |
| `*fn-nntp-max-rendered-year*` | books/nntp-responses.lisp:930 | 9999 | RFC | protocol limit: NNTP RFC 3977 3.1/6, Message-ID RFC 5536 3.1.3, line RFC 5322 2.1.1, DNS 253/63, TCPCLv4 RFC 9174 widths, RFC 2047, wildmat 497 |
| `*fn-nntp-max-command-octets*` | books/nntp-syntax.lisp:97 | 510 | RFC | protocol limit: NNTP RFC 3977 3.1/6, Message-ID RFC 5536 3.1.3, line RFC 5322 2.1.1, DNS 253/63, TCPCLv4 RFC 9174 widths, RFC 2047, wildmat 497 |
| `*fn-nntp-max-argument-octets*` | books/nntp-syntax.lisp:99 | 497 | RFC | protocol limit: NNTP RFC 3977 3.1/6, Message-ID RFC 5536 3.1.3, line RFC 5322 2.1.1, DNS 253/63, TCPCLv4 RFC 9174 widths, RFC 2047, wildmat 497 |
| `*fn-nntp-max-response-octets*` | books/nntp-syntax.lisp:108 | 512 | RFC | protocol limit: NNTP RFC 3977 3.1/6, Message-ID RFC 5536 3.1.3, line RFC 5322 2.1.1, DNS 253/63, TCPCLv4 RFC 9174 widths, RFC 2047, wildmat 497 |
| `*fn-nntp-max-initial-line-octets*` | books/nntp-syntax.lisp:110 | 510 | RFC | protocol limit: NNTP RFC 3977 3.1/6, Message-ID RFC 5536 3.1.3, line RFC 5322 2.1.1, DNS 253/63, TCPCLv4 RFC 9174 widths, RFC 2047, wildmat 497 |
| `*fn-nntp-max-article-number*` | books/nntp-syntax.lisp:112 | 2147483647 | RFC | protocol limit: NNTP RFC 3977 3.1/6, Message-ID RFC 5536 3.1.3, line RFC 5322 2.1.1, DNS 253/63, TCPCLv4 RFC 9174 widths, RFC 2047, wildmat 497 |
| `*fn-nntp-max-group-octets*` | books/nntp-syntax.lisp:114 | 460 | RFC | protocol limit: NNTP RFC 3977 3.1/6, Message-ID RFC 5536 3.1.3, line RFC 5322 2.1.1, DNS 253/63, TCPCLv4 RFC 9174 widths, RFC 2047, wildmat 497 |
| `*fn-nntp-max-message-id-octets*` | books/nntp-syntax.lisp:116 | 250 | RFC | protocol limit: NNTP RFC 3977 3.1/6, Message-ID RFC 5536 3.1.3, line RFC 5322 2.1.1, DNS 253/63, TCPCLv4 RFC 9174 widths, RFC 2047, wildmat 497 |
| `*fn-nntp-max-decimal-octets*` | books/nntp-syntax.lisp:118 | 10 | RFC | protocol limit: NNTP RFC 3977 3.1/6, Message-ID RFC 5536 3.1.3, line RFC 5322 2.1.1, DNS 253/63, TCPCLv4 RFC 9174 widths, RFC 2047, wildmat 497 |
| `*fn-phost-max-name*` | books/peer-host.lisp:37 | 253 | RFC | protocol limit: NNTP RFC 3977 3.1/6, Message-ID RFC 5536 3.1.3, line RFC 5322 2.1.1, DNS 253/63, TCPCLv4 RFC 9174 widths, RFC 2047, wildmat 497 |
| `*fn-phost-max-label*` | books/peer-host.lisp:38 | 63 | RFC | protocol limit: NNTP RFC 3977 3.1/6, Message-ID RFC 5536 3.1.3, line RFC 5322 2.1.1, DNS 253/63, TCPCLv4 RFC 9174 widths, RFC 2047, wildmat 497 |
| `*fn-pinv-max-redecide-msgid*` | books/peer-invite.lisp:1231 | 250 | RFC | protocol limit: NNTP RFC 3977 3.1/6, Message-ID RFC 5536 3.1.3, line RFC 5322 2.1.1, DNS 253/63, TCPCLv4 RFC 9174 widths, RFC 2047, wildmat 497 |
| `*fn-record-max-msgid*` | books/records-shape.lisp:37 | 250 | RFC | protocol limit: NNTP RFC 3977 3.1/6, Message-ID RFC 5536 3.1.3, line RFC 5322 2.1.1, DNS 253/63, TCPCLv4 RFC 9174 widths, RFC 2047, wildmat 497 |
| `*fn-tcl-max-u16*` | books/tcpcl-octets.lisp:84 | 65535 | RFC | protocol limit: NNTP RFC 3977 3.1/6, Message-ID RFC 5536 3.1.3, line RFC 5322 2.1.1, DNS 253/63, TCPCLv4 RFC 9174 widths, RFC 2047, wildmat 497 |
| `*fn-tcl-max-u32*` | books/tcpcl-octets.lisp:85 | 4294967295 | RFC | protocol limit: NNTP RFC 3977 3.1/6, Message-ID RFC 5536 3.1.3, line RFC 5322 2.1.1, DNS 253/63, TCPCLv4 RFC 9174 widths, RFC 2047, wildmat 497 |
| `*fn-tcl-max-u64*` | books/tcpcl-octets.lisp:86 | 18446744073709551615 | RFC | protocol limit: NNTP RFC 3977 3.1/6, Message-ID RFC 5536 3.1.3, line RFC 5322 2.1.1, DNS 253/63, TCPCLv4 RFC 9174 widths, RFC 2047, wildmat 497 |
| `*fn-tcl-max-message-overhead*` | books/tcpcl-octets.lisp:897 | (+ 25 *fn-tcl-node-id-cap* *fn-tcl-ext-cap*) | N | node ID at its u16 width (105832cca removed the 1024 cap); derived |
| `*fn-tcl-init-need-bound*` | books/tcpcl-octets.lisp:1183 | (+ 24 *fn-tcl-node-id-cap* *fn-tcl-ext-cap*) | N | node ID at its u16 width (105832cca removed the 1024 cap); derived |
| `*fn-pxy-v1-max*` | books/tls-proxy.lisp:42 | 107 | RFC | PROXY protocol v1/v2 header sizes (107 / 16 + body) |
| `*fn-pxy-v2-max-body*` | books/tls-proxy.lisp:43 | 512 | RFC | PROXY protocol v1/v2 header sizes (107 / 16 + body) |
| `*fn-pxy-max*` | books/tls-proxy.lisp:44 | (+ 16 *fn-pxy-v2-max-body*) | RFC | PROXY protocol v1/v2 header sizes (107 / 16 + body) |
| `*fn-wildmat-max-octets*` | books/utf8.lisp:22 | 497 | RFC | protocol limit: NNTP RFC 3977 3.1/6, Message-ID RFC 5536 3.1.3, line RFC 5322 2.1.1, DNS 253/63, TCPCLv4 RFC 9174 widths, RFC 2047, wildmat 497 |
| `*fn-wildmat-max-codepoint*` | books/utf8.lisp:23 | 1114111 | RFC | protocol limit: NNTP RFC 3977 3.1/6, Message-ID RFC 5536 3.1.3, line RFC 5322 2.1.1, DNS 253/63, TCPCLv4 RFC 9174 widths, RFC 2047, wildmat 497 |
| `*fn-w47-max*` | books/web-2047.lisp:40 | 4096 | RFC | protocol limit: NNTP RFC 3977 3.1/6, Message-ID RFC 5536 3.1.3, line RFC 5322 2.1.1, DNS 253/63, TCPCLv4 RFC 9174 widths, RFC 2047, wildmat 497 |
| `*fn-w47-word-max*` | books/web-2047.lisp:41 | 75 | RFC | protocol limit: NNTP RFC 3977 3.1/6, Message-ID RFC 5536 3.1.3, line RFC 5322 2.1.1, DNS 253/63, TCPCLv4 RFC 9174 widths, RFC 2047, wildmat 497 |

### Anchor / RoughTime (6)

| name | HEAD file:line | value | class | reason |
|---|---|---|---|---|
| `*fn-anchor-max-payload*` | books/anchor-record.lisp:54 | 1024 | W | RoughTime/anchor protocol record and wire shapes (anchor-record, anchor-wire, server timeout) |
| `*fn-anchor-server-max-timeout-seconds*` | books/anchor-servers.lisp:12 | 60 | W | RoughTime/anchor protocol record and wire shapes (anchor-record, anchor-wire, server timeout) |
| `*fn-anchor-wire-max-response*` | books/anchor-wire.lisp:10 | 4096 | W | RoughTime/anchor protocol record and wire shapes (anchor-record, anchor-wire, server timeout) |
| `*fn-anchor-wire-max-tags*` | books/anchor-wire.lisp:11 | 32 | W | RoughTime/anchor protocol record and wire shapes (anchor-record, anchor-wire, server timeout) |
| `*fn-anchor-wire-max-path-nodes*` | books/anchor-wire.lisp:12 | 32 | W | RoughTime/anchor protocol record and wire shapes (anchor-record, anchor-wire, server timeout) |
| `*fn-anchor-tag-maxt*` | books/anchor.lisp:110 | '(77 65 88 84) | W | RoughTime/anchor protocol record and wire shapes (anchor-record, anchor-wire, server timeout) |

### Peer auth (2)

| name | HEAD file:line | value | class | reason |
|---|---|---|---|---|
| `*fn-fap-max-octets*` | books/feed-auth-profile.lisp:6 | 1024 | W | one outbound AUTHINFO profile file (user/password); fixed shape |
| `*fn-fap-max-token-octets*` | books/feed-auth-profile.lisp:10 | 494 | W | one outbound AUTHINFO profile file (user/password); fixed shape |

### Host (SBCL) constants (10)

| name | HEAD file:line | value | class | reason |
|---|---|---|---|---|
| `*fn-log-sink-pending-bound*` | books/log-sink.lisp:50 | 1048576 | W | log writer backlog (comment: work and allocation bound of the log writer, D27) |
| `+fnn-bps-fragment-quantum+` | host/native/bp-service.lisp:1071 | m+ 4096 "Positions of the reassembly sweep one fn- | W | host work bound: read/reassembly quantum, retry or hop policy, fixed message/file width (+fnn-node-secret-file-bound+, pem capacity, token octets are fixed shapes) |
| `+fnn-bp-hop-limit+` | host/native/bp.lisp:34 | t+ 32 | W | host work bound: read/reassembly quantum, retry or hop policy, fixed message/file width (+fnn-node-secret-file-bound+, pem capacity, token octets are fixed shapes) |
| `+fnn-crypto-max-message-octets+` | host/native/crypto.lisp:19 | s+ 4096 | W | host work bound: read/reassembly quantum, retry or hop policy, fixed message/file width (+fnn-node-secret-file-bound+, pem capacity, token octets are fixed shapes) |
| `+fnn-feed-idle-max-seconds+` | host/native/feed-service.lisp:34 | s+ 1 | W | host work bound: read/reassembly quantum, retry or hop policy, fixed message/file width (+fnn-node-secret-file-bound+, pem capacity, token octets are fixed shapes) |
| `+fnn-node-secret-file-bound+` | host/native/io.lisp:4271 | d+ (+ 18 4 2 65535 32) | W | host work bound: read/reassembly quantum, retry or hop policy, fixed message/file width (+fnn-node-secret-file-bound+, pem capacity, token octets are fixed shapes) |
| `+fnn-max-read+` | host/native/io.lisp:5973 | d+ 512 | W | host work bound: read/reassembly quantum, retry or hop policy, fixed message/file width (+fnn-node-secret-file-bound+, pem capacity, token octets are fixed shapes) |
| `+fnn-pinv-max-token-octets+` | host/native/peer-invite.lisp:20 | s+ 64 | W | host work bound: read/reassembly quantum, retry or hop policy, fixed message/file width (+fnn-node-secret-file-bound+, pem capacity, token octets are fixed shapes) |
| `+fnn-pinv-pem-capacity+` | host/native/peer-invite.lisp:346 | y+ 8192 | W | host work bound: read/reassembly quantum, retry or hop policy, fixed message/file width (+fnn-node-secret-file-bound+, pem capacity, token octets are fixed shapes) |
| `+fnn-tls-max-fact-octets+` | host/native/tls.lisp:378 | s+ 65536 | W | host work bound: read/reassembly quantum, retry or hop policy, fixed message/file width (+fnn-node-secret-file-bound+, pem capacity, token octets are fixed shapes) |

### Per-request / per-step work bounds, record shapes and quanta (50)

| name | HEAD file:line | value | class | reason |
|---|---|---|---|---|
| `*fn-cbud-read-quantum*` | books/connection-read-quantum.lisp:6 | 4096 | W | per-request / per-step work bound, a fixed record shape, a deadline or quantum (comments cite D27 where they were re-labelled) |
| `*fn-col-poll-max-scan*` | books/consumer-poll-index.lisp:19 | 16 | W | per-request / per-step work bound, a fixed record shape, a deadline or quantum (comments cite D27 where they were re-labelled) |
| `*fn-cwait-max-seconds*` | books/consumer-wait-codec.lisp:39 | 3600 | W | per-request / per-step work bound, a fixed record shape, a deadline or quantum (comments cite D27 where they were re-labelled) |
| `*fn-cwait-bound-wait-code*` | books/consumer-wait-codec.lisp:41 | 10 | W | per-request / per-step work bound, a fixed record shape, a deadline or quantum (comments cite D27 where they were re-labelled) |
| `*fn-flb-max-delay*` | books/feed-link-backoff.lisp:34 | 300000 | W | per-request / per-step work bound, a fixed record shape, a deadline or quantum (comments cite D27 where they were re-labelled) |
| `*fn-feed-wire-input-max-chunk-octets*` | books/feed-wire-input.lisp:19 | 512 | W | per-request / per-step work bound, a fixed record shape, a deadline or quantum (comments cite D27 where they were re-labelled) |
| `*fn-inj-max-agent-octets*` | books/injection.lisp:108 | 128 | W | per-request / per-step work bound, a fixed record shape, a deadline or quantum (comments cite D27 where they were re-labelled) |
| `*fn-mpr-slot-quantum*` | books/msgid-probe-cursor.lisp:8 | (* 2 *fn-mpxt-page-slots*) | W | per-request / per-step work bound, a fixed record shape, a deadline or quantum (comments cite D27 where they were re-labelled) |
| `*fn-native-auth-admin-max-secret-octets*` | books/native-auth-admin.lisp:13 | 256 | W | per-request / per-step work bound, a fixed record shape, a deadline or quantum (comments cite D27 where they were re-labelled) |
| `*fn-ncline-max-line-octets*` | books/native-control-line.lisp:17 | 1024 | W | per-request / per-step work bound, a fixed record shape, a deadline or quantum (comments cite D27 where they were re-labelled) |
| `*fn-nctrl-max-reason-octets*` | books/native-control-reason.lisp:37 | 512 | W | per-request / per-step work bound, a fixed record shape, a deadline or quantum (comments cite D27 where they were re-labelled) |
| `*fn-nh-reason-max-octets*` | books/native-health.lisp:1753 | 480 | W | per-request / per-step work bound, a fixed record shape, a deadline or quantum (comments cite D27 where they were re-labelled) |
| `*fn-nlp-max-versions*` | books/native-live-pages.lisp:282 | 4 | W | per-request / per-step work bound, a fixed record shape, a deadline or quantum (comments cite D27 where they were re-labelled) |
| `*fn-nls-max-restarts*` | books/native-live-status.lisp:697 | 8 | W | per-request / per-step work bound, a fixed record shape, a deadline or quantum (comments cite D27 where they were re-labelled) |
| `*fn-nop-max-watch-seconds*` | books/native-operator.lisp:819 | 86400 | W | per-request / per-step work bound, a fixed record shape, a deadline or quantum (comments cite D27 where they were re-labelled) |
| `*fn-nop-control-path-max-octets*` | books/native-operator.lisp:3221 | 103 | W | per-request / per-step work bound, a fixed record shape, a deadline or quantum (comments cite D27 where they were re-labelled) |
| `*fn-nret-max-drain-seconds*` | books/native-retire.lisp:26 | 86400 | W | per-request / per-step work bound, a fixed record shape, a deadline or quantum (comments cite D27 where they were re-labelled) |
| `*fn-auth-failure-limit*` | books/nntp-auth.lisp:782 | 3 | W | per-request / per-step work bound, a fixed record shape, a deadline or quantum (comments cite D27 where they were re-labelled) |
| `*fn-ocm-bound*` | books/owner-commit-class.lisp:31 | 4 | W | per-request / per-step work bound, a fixed record shape, a deadline or quantum (comments cite D27 where they were re-labelled) |
| `*fn-ocp-pass-bound*` | books/owner-commit-pipeline.lisp:75 | 4 | W | per-request / per-step work bound, a fixed record shape, a deadline or quantum (comments cite D27 where they were re-labelled) |
| `*fn-own-feed-retry-bound*` | books/owner-feed.lisp:446 | 3 | W | per-request / per-step work bound, a fixed record shape, a deadline or quantum (comments cite D27 where they were re-labelled) |
| `*fn-olog-max-field-octets*` | books/owner-log.lisp:30 | 256 | W | per-request / per-step work bound, a fixed record shape, a deadline or quantum (comments cite D27 where they were re-labelled) |
| `*fn-osch-bound*` | books/owner-scheduler.lisp:51 | 3 | W | per-request / per-step work bound, a fixed record shape, a deadline or quantum (comments cite D27 where they were re-labelled) |
| `*fn-own-body-limit*` | books/owner.lisp:1399 | 8192 | W | per-request / per-step work bound, a fixed record shape, a deadline or quantum (comments cite D27 where they were re-labelled) |
| `*fn-lzr-dict-max*` | books/payload-lz-record.lisp:180 | 65536 | W | per-request / per-step work bound, a fixed record shape, a deadline or quantum (comments cite D27 where they were re-labelled) |
| `*fn-cu-max-quantum*` | books/peer-catchup-serve.lisp:79 | 1048576 | W | per-request / per-step work bound, a fixed record shape, a deadline or quantum (comments cite D27 where they were re-labelled) |
| `*fn-cu-request-quantum*` | books/peer-catchup.lisp:55 | 262144 | W | per-request / per-step work bound, a fixed record shape, a deadline or quantum (comments cite D27 where they were re-labelled) |
| `*fn-cu-max-payload*` | books/peer-catchup.lisp:585 | 1024 | W | per-request / per-step work bound, a fixed record shape, a deadline or quantum (comments cite D27 where they were re-labelled) |
| `*fn-feed-max-backoff*` | books/peer-feed.lisp:78 | 3600000 | W | per-request / per-step work bound, a fixed record shape, a deadline or quantum (comments cite D27 where they were re-labelled) |
| `*fn-feed-max-payload*` | books/peer-feed.lisp:1181 | 1024 | W | per-request / per-step work bound, a fixed record shape, a deadline or quantum (comments cite D27 where they were re-labelled) |
| `*fn-pull-max-line*` | books/peer-pull.lisp:68 | 512 | W | per-request / per-step work bound, a fixed record shape, a deadline or quantum (comments cite D27 where they were re-labelled) |
| `*fn-pull-max-payload*` | books/peer-pull.lisp:1572 | 1024 | W | per-request / per-step work bound, a fixed record shape, a deadline or quantum (comments cite D27 where they were re-labelled) |
| `*fn-exp-quantum-ms*` | books/public-exposure.lisp:101 | 1000 | W | per-request / per-step work bound, a fixed record shape, a deadline or quantum (comments cite D27 where they were re-labelled) |
| `*fn-rpf-file-limit*` | books/recovery-profile-buffer.lisp:7 | (nth 5 (fn-recovery-profile-envelope)) | W | per-request / per-step work bound, a fixed record shape, a deadline or quantum (comments cite D27 where they were re-labelled) |
| `*fn-sched-max-payload*` | books/scheduler.lisp:423 | 4096 | W | per-request / per-step work bound, a fixed record shape, a deadline or quantum (comments cite D27 where they were re-labelled) |
| `*fn-scram-max-iterations*` | books/scram.lisp:77 | 1000000 | W | per-request / per-step work bound, a fixed record shape, a deadline or quantum (comments cite D27 where they were re-labelled) |
| `*fn-sf-max-trace-events*` | books/store-files-traces.lisp:27 | 4096 | W | per-request / per-step work bound, a fixed record shape, a deadline or quantum (comments cite D27 where they were re-labelled) |
| `*fn-sn-max-staging-observation*` | books/store-sweep.lisp:93 | 64 | W | per-request / per-step work bound, a fixed record shape, a deadline or quantum (comments cite D27 where they were re-labelled) |
| `*fn-tlsr-max-word*` | books/tls-reload.lisp:585 | 16 | W | per-request / per-step work bound, a fixed record shape, a deadline or quantum (comments cite D27 where they were re-labelled) |
| `*fn-tlsr-max-line*` | books/tls-reload.lisp:592 | *fn-record-max-payload* | W | per-request / per-step work bound, a fixed record shape, a deadline or quantum (comments cite D27 where they were re-labelled) |
| `*fn-ssc-length-limit*` | books/tls-self-signed.lisp:29 | 16777216 | W | per-request / per-step work bound, a fixed record shape, a deadline or quantum (comments cite D27 where they were re-labelled) |
| `*fn-th-max-binary*` | books/topic-history-metadata.lisp:9 | 1536 | W | per-request / per-step work bound, a fixed record shape, a deadline or quantum (comments cite D27 where they were re-labelled) |
| `*fn-th-max-field*` | books/topic-history-metadata.lisp:10 | 2048 | W | per-request / per-step work bound, a fixed record shape, a deadline or quantum (comments cite D27 where they were re-labelled) |
| `*fn-th-max-items*` | books/topic-history-metadata.lisp:11 | 39 | W | per-request / per-step work bound, a fixed record shape, a deadline or quantum (comments cite D27 where they were re-labelled) |
| `*fn-th-max-parents*` | books/topic-history-metadata.lisp:13 | 8 | W | per-request / per-step work bound, a fixed record shape, a deadline or quantum (comments cite D27 where they were re-labelled) |
| `*fn-th-topic-max-octets*` | books/topic-history-store-events.lisp:15 | 1024 | W | per-request / per-step work bound, a fixed record shape, a deadline or quantum (comments cite D27 where they were re-labelled) |
| `*fn-th-topic-max-items*` | books/topic-history-store-events.lisp:16 | 24 | W | per-request / per-step work bound, a fixed record shape, a deadline or quantum (comments cite D27 where they were re-labelled) |
| `*fn-wrq-max-name*` | books/web-request.lisp:329 | 24 | W | per-request / per-step work bound, a fixed record shape, a deadline or quantum (comments cite D27 where they were re-labelled) |
| `*fn-owner-feed-send-quantum-octets*` | host/owner-host.lisp:5128 | 65536 | W | per-request / per-step work bound, a fixed record shape, a deadline or quantum (comments cite D27 where they were re-labelled) |
| `*fn-owner-feed-send-quantum-seconds*` | host/owner-host.lisp:5129 | 10 | W | per-request / per-step work bound, a fixed record shape, a deadline or quantum (comments cite D27 where they were re-labelled) |
