"""Static, regenerable inventory of the 120 H1a quarry modules. No test imports."""
import argparse
import ast
import fcntl
import hashlib
import os
import tempfile
import re
import json
from pathlib import Path


# Frozen H1a input snapshots; classification is supplied, never inferred.
QUARRY = {'node': ['conformance', 'nntp_post_probe', 'newnews_wildmat', 'over_pins', 'over_window', 'over_cursor_cost', 'header_limits', 'article_quiet', 'article_slots', 'article_subject', 'own_cancel', 'moderation_outcome', 'reader_index', 'reader_freshness', 'public_limits', 'public_exposure', 'group_authority', 'group_name_bound', 'mux', 'listener_v6', 'known_abort', 'fence_boundary', 'accept_maintenance', 'visibility_join', 'status_live_posts', 'cold_line_deadline', 'cold_line_quanta', 'cold_off_loop', 'decoded_custody', 'expiry', 'auth', 'sasl', 'starttls', 'implicit_tls', 'injection_info', 'tls_handshake_budget', 'tls_key_exchange', 'tls_proxy', 'tls_reload', 'key_statements', 'hybrid_author', 'friends_accounts', 'peering', 'peer_pull', 'peer_catchup', 'peer_hostile_feed', 'peer_misbehaving', 'peer_by_name', 'peer_rows_growth', 'control_across_peers', 'control_filing', 'friends_feed', 'feed_reply_cold', 'consumer_exchange', 'pattern_pubsub', 'topic_local', 'source_corpus_bp', 'replay_determinism', 'served_crash_model', 'commit_log', 'log_compaction', 'checkpoint', 'snapshot_bless', 'store_lineage', 'store_identity', 'reclaim_seal_cost', 'reclaim_in_flight', 'frozen_relocation', 'served_differential', 'page_io', 'operator_walk', 'install', 'installed_start', 'start_every_preset', 'profile', 'host_lifecycle', 'heap_from_profile', 'image_floor', 'image_heap', 'capacity_vector', 'bounds_join', 'credits', 'scaling', 'open_depth', 'owner_offlock', 'web', 'source_corpus'], 'node_internal': ['outside_in', 'header_lines', 'moderation', 'group_access', 'group_policy', 'post_seal_gate', 'nov_metadata', 'compress', 'tls_transport', 'protected_peering', 'consumer_exchange_two_nodes', 'consumer_e2', 'consumer_identity', 'control', 'slow_disk', 'recovery', 'state_checkpoint', 'journal_torn', 'log_sink', 'dead_run', 'reclaim_walk', 'store_mount_identity', 'extent_identity', 'operator_cli', 'operator_verbs', 'live_reconfiguration', 'admin', 'image_differential', 'owner_scheduler', 'owner', 'outcome_algebra', 'agent_wait', 'harness']}
RELEASE_SECTION_1 = '| surface item | fn1 evidence (origin/dev path) | fn2 layer | status | the test that will prove it |\n|---|---|---|---|---|\n| **NNTP reader commands (RFC 3977)** | | | | |\n| greeting 200/201 (posting allowed / not), banner `fn VERSION` | `books/nntp-auth.lisp` ~1678; `specs/nntp.md` l.1985-2010 | D | brief (D3) | sim scenario 1; WIRE; `conformance`, `public_exposure` |\n| CAPABILITIES (always: VERSION 2, READER, OVER MSGID, HDR, XPAT, NEWNEWS, LIST …, IMPLEMENTATION; conditional: POST, IHAVE, STREAMING, STARTTLS, AUTHINFO, SASL, COMPRESS, XFN-DICT) | `books/nntp-responses.lisp:609-657`; `nntp-auth.lisp:939`; `peer-inbound.lisp:1201` | D (E adds the TLS/SASL/COMPRESS labels) | brief (D3, E2) | WIRE; `conformance`, `auth`, `sasl`, `compress`, `implicit_tls`, `listener_v6` |\n| HELP (31 keywords; an unknown keyword in command state → 500, PRF-194) | `books/nntp-help.lisp:52-59`; `specs/nntp.md` NNT-038 | D | brief (D3) | grammar fuzz (every non-keyword in command state → 500); `conformance` |\n| QUIT, MODE READER (200/201, not mode-switching), DATE (503 without a clock) | `nntp.lisp` session command; `nntp-responses.lisp:1398`, `:972` | D | brief (D3) | WIRE; `conformance`, `starttls` |\n| GROUP (211; empty group `211 0 wm+1 wm`; an issued article number is never reused, while an abandoned tentative assignment is distinct and may be), LISTGROUP [range] | `books/nntp-projection.lisp:338`, `:380`; `specs/nntp.md` l.420-505 | D over C | brief (D7) | stateful model test (§2.3: numbering never reused); `conformance`, `reader_freshness`, `reader_index` |\n| NEXT / LAST (moves only to an available article) | `nntp-responses.lisp:260`; `nntp-invariants.lisp:685` | D | brief (D7) | stateful model test; `conformance`, `over_pins` |\n| ARTICLE / HEAD / BODY / STAT by number, by Message-ID, current; Xref prepend; 430 `withdrawn` | `nntp-responses.lisp:239`; `nntp-pinned-msgid.lisp`; `specs/nntp.md` l.363-416, 601-632 | D over C | brief (D7) | sim scenarios 1, 2, 3 (cold 16 MiB BODY, stalled reader, late corruption); WIRE, OWN; `article_*`, `reader_index`, `own_cancel` |\n| OVER / XOVER (resumable cursor; 423 vs 420 empty range) | `nntp-responses.lisp:1372`, `:1672`; `served-plan-cursor.lisp`; `over-window.lisp` | D over C | brief (D7) | sim scenario 6 (sparse XOVER); WORK, WIRE; `over_window`, `over_cursor_cost`, `over_pins`, `nov_metadata` |\n| HDR / XHDR incl. fn metadata items `:fn-verified`, `:fn-control`, `:fn-enrollment` | `nntp-responses.lisp:1834`; `nntp-verdict.lisp`; `nntp-control.lisp` | D over C | brief (D7) | `header_lines`, `key_statements`, `control_filing`, `visibility_join` |\n| XPAT (RFC 2980; 2,000-article window; Xref deferral stated) | `nntp-responses.lisp:2010`; `specs/nntp.md` NNT-016 | D | brief (D7) | `cold_line_quanta`, `cold_line_deadline`, `conformance` |\n| LIST, LIST ACTIVE [wildmat] (y/n/m), NEWSGROUPS, OVERVIEW.FMT, HEADERS, ACTIVE.TIMES, COUNTS, MOTD, SUBSCRIPTIONS (RFC 3977/6048) | `nntp-responses.lisp:2522`, `:2395`, `:2515`; `nntp-list-counts.lisp`; `nntp-reader-compat.lisp:221` | D over C | brief (D7) | `conformance`, `group_policy`, `moderation`, `operator_verbs`, `reader_clients` |\n| LIST DISTRIB.PATS / DISTRIBUTIONS (recognised, always 503) | `nntp-responses.lisp:547-551` | D | brief (D3; stays 503) | grammar fuzz; `open_depth` |\n| NEWGROUPS, NEWNEWS (wildmat; 503 on a two-digit year without a clock; streamed cursor) | `nntp-responses.lisp:1128`, `:2304`; `specs/nntp.md` NNT-008 | D over C | brief (D7) | `newnews_wildmat`, `reader_clients`, `cold_line_*` |\n| **NNTP posting and transit** | | | | |\n| POST (340/440/480; 240; the 441 refusal words: duplicate, conflict, malformed, unaffordable, history-exhausted, storage-failed, control-not-filed, control-malformed, the generic refused, read-only group, moderation, login-unsigned, login-not-bound; `mpx-saturated` and the other index-specific words of fn1 retired by name in R3; the separate *uncertain* 441, never a 240 or a refusal; each word a fixture, *[Astra]*) | `nntp.lisp`; `nntp-auth.lisp` (480/440); `nntp-post.lisp:464`; `owner.lisp fn-own-outcome`; `specs/nntp.md` l.681-1480 | D over B, C | brief (D4, D5) | sim scenarios 1, 4, 13, 14; HISTORY, IDENTITY, WIRE; `nntp_post_probe`, `post_seal_gate`, `header_limits`, `control_filing`, `moderation_outcome`; F2S/F4 as sim scenarios |\n| control messages: cancel (own-cancel, control.cancel filing), moderation `Approved`, injection info (RFC 5537) | `books/injection.lisp`; `nntp-control.lisp`; `specs/nntp.md` NNT-040/047 | D over C | brief (D5) | `own_cancel`, `control_filing`, `moderation`, `injection_info` |\n| IHAVE (435/436/437/335/235; 502 on a reader connection), MODE STREAM (203), CHECK (238/431/438), TAKETHIS (239/439; 436 deferred not 400; `max-inflight` 16) | `peer-inbound.lisp:1229`, `:1282`; `served-catalog-chain.lisp`; `specs/nntp.md` NNT-045 l.2412-2478 | D over C (inbound half) | brief (D4, D5) | sim scenario 5 (TAKETHIS window); ACCOUNT, HISTORY, IDENTITY; `peering`, `peer_misbehaving`, `peer_hostile_feed`, `protected_peering` |\n| transit body bound: 437/439 with Message-ID then close | `specs/nntp.md` l.530-537 | D | brief (D4) | sim scenario 4; `peer_hostile_feed` |\n| **NNTP: fn\'s own commands** | | | | |\n| XREDEEM CODE NAME / XREDEEM PASS PW (381 → 281 / 482; 502 when authenticated; 483 before TLS under protected-only) | `nntp-auth.lisp:1423`; `accounts.lisp`; `specs/nntp.md` NNT-034 l.1784-1914 | E (over D\'s connection machine) | brief (E2) | `friends_accounts`, `agent_wait`, `consumer_identity`, `group_access` |\n| XFNCATCHUP WILDMAT FROM CHAIN QUANTUM → 291 / 423 / 501 (serving half) | `peer-catchup-serve.lisp:390`; `specs/peering.md:372-390` | E | brief (E4) | `peer_catchup`; sim peer workload machine |\n| XFN-ZARTICLE &lt;msgid&gt; &lt;digest&gt;… (a digest *list*; 229 with the encoded response on a dictionary match, else the plain ARTICLE reply; `specs/nntp.md` l.2484-2499), capability XFN-DICT | `nntp-zarticle.lisp:138`; `nntp-compress-dict.lisp:93`; `docs/extensions/nntp-compress-dict.md` | E | brief (E2, "carried, not promised": no native names it today) | new native `compress_dict` (E2 writes it) |\n| **Connection policy (the 4xx behaviours clients see)** | | | | |\n| capacity 400s: too many connections / from this address (8 public) / authentication failures; then close | `specs/nntp.md` NNT-031/043 l.2301-2384; `books/public-exposure.lisp` | D | brief (D7) | sim scenario 11 (principal exhaustion); ACCOUNT, FAIR; `public_limits`, `public_exposure`, `mux` |\n| pacing and posts/minute: no reply, the connection waits | `specs/nntp.md` l.2316-2322 | D | brief (D7) | sim scenario 11; `public_limits` |\n| first-command 60 s and idle 600 s: silent close; the 10 s send deadline (`send-stalled`) | `specs/nntp.md` l.2317-2318; host mux | D (timer service) | brief (D7) | sim scenario 2, 18; `mux`, `known_abort` |\n| third failed AUTHINFO PASS / SASL: 481, 400, close | NNT-1002 l.1661 | E | brief (E2) | `auth` |\n| framing: pipelining, any fragmentation, dot-stuffing, the 512-octet initial line, `fn-article-parse-limit` (long header line) | `books/wire.lisp`; `article-line-bound.lisp:147`; F6 | D (grammar DSL) | brief (D2) | WIRE over every split (F6 as a sim scenario); grammar fuzz; `conformance`, `header_limits` |\n| **TLS and authentication** | | | | |\n| STARTTLS (382; nothing framed during the handshake; resets group and cursor; 502 after auth / twice / after COMPRESS) | `nntp-auth.lisp:1499`; `served-tls-prefix.lisp`; `host/native/tls.lisp`; `specs/nntp.md` l.1482-1660 | D (admission machine, sim TLS stub) + E (OpenSSL adapter, the command) | brief (D7, E1) | sim scenario 18 (STARTTLS boundary fragments, handshake flood); `starttls`, `tls_handshake_budget`, `tls_reload` |\n| implicit TLS listener (`[listener] tls_port`, 563-style; protected-only from the first command; PROXY header from `tls-proxy-trusted-peers`) | `served-implicit-tls.lisp`; `native-config.lisp:716-743`; `fn-pxy-step`; `specs/host.md:1641` | E | brief (E1) | `implicit_tls`, `tls_transport`, `tls_proxy`, `listener_v6` |\n| handshake admission `tls-handshakes-in-flight` (16) | `fn-hsb-admit`; `specs/host.md:1630-1639` | D | brief (D7) | sim scenario 18; `tls_handshake_budget` |\n| TLS key exchange: post-quantum first (ML-KEM hybrid), the certificate reload | `host/native/tls.lisp`; `docs/operator.md` certificates | E | brief (E1) | `tls_key_exchange`, `tls_reload` |\n| AUTHINFO USER/PASS (salted tagged BLAKE3 verifier `:fn-authsec-v2`); `auth required` / `protected-only` (483 before TLS) | `nntp-auth.lisp:1344`; `auth-secret.lisp`; `native-auth-profile.lisp` | E | brief (E2) | `auth`, `public_exposure`, `friends_accounts` |\n| AUTHINFO SASL: PLAIN (TLS only), SCRAM-SHA-256, SCRAM-SHA-256-PLUS (tls-exporter channel binding); 383/283/503/504; DIGEST-MD5 is a stated deviation | `nntp-auth.lisp:1239`; `sasl.lisp:130`; `scram.lisp`; `tls.lisp:944-975` | E | brief (E2) | `sasl`; a SCRAM conformance fixture (RFC 7677 vectors) |\n| per-login group access (read/post wildmats), private groups, moderation bindings, signed-post bindings (`hybrid-sign` / `hybrid-author`, Ed25519 + ML-DSA-65) | `group-access.lisp`; `docs/operator.md` accounts/private groups/signed posts; CLIENTS §1.1 | E (policy in D\'s accounts; verbs in E) | brief (D7, E2, E6) | `group_access`, `group_authority`, `visibility_join`, `hybrid_author`, `key_statements` |\n| COMPRESS DEFLATE (206; bomb and BFINAL close rules) | `nntp-auth.lisp:1610`; `nntp-compress.lisp`; `host/native/fn-deflate.c` | E | brief (E2) | `compress` |\n| TLS client certificates (server side) | absent in fn1 (`peering.md:1826` "later") | — | not surface; not carried | — |\n| **The consumer control surface (`specs/consumer-progress.md`; the grammar is `books/wire-export.lisp:427-483`: 15 families, 4 exchanges)** | | | | |\n| the cursor `fncu` v1 (≤ 346 octets: history, incarnation, consumer, epoch, principal, query, query-version, view-version, position); a foreign cursor refused before any mutation | `wire-family-fncu.lisp:34`; `consumer-position.lisp`; spec L14-65 | D (wait machine) + E (encoding on the wire) | brief (D8, E3) | CONSUMER checker; `consumer_inspect`, `consumer_project_bounds`; the cursor fixtures (E3) |\n| `fnct.consumer.request` k4 (codes: register 0, ack 1, position 2, unregister 3, bootstrap 4, poll 5, status 6, bound-poll 7, bound-ack 8, wait 9, bound-wait 10) and `reasoned-request` k22 | `wire-family-consumer.lisp:438,506,1187`; `consumer-local-control.lisp:46-55`; `consumer-wait-codec.lisp:40-41`; spec L62-65, 340, 384, 414-457 | E over D8 | brief (E3) | sim scenarios 7, 8, 9; CONSUMER, HISTORY; `consumer_e2`, `consumer_exchange`, `consumer_exchange_two_nodes`, `consumer_identity`, `agent_wait`, `control` |\n| the replies: `reply` k5, `status-reply` k9, `poll-reply` k6 (FNWD1 withdrawal report; FNRB1 collection), `reasoned-reply` k18, `line-reply` k23 | `wire-family-consumer.lisp:257,270,18-35,1269,1314`; `wire-family-control.lisp:311-317,410-417`; spec L459-499, 630-660 | E | brief (E3) | as above; CNS-008\'s withdrawal-at-a-consumer gets its first native (E3 writes it: the spec L496-499 says none observes it today) |\n| the four exchanges: consumer request → {reply, status, poll}; reasoned-request → {…, reasoned-reply}; store-identity k24 → k25; live-profile k26 → k27 | `wire-export.lisp:477-483`; `wire-family-identity.lisp:30,42`; `live-profile-control.lisp:10-11` | E (consumer, identity); E6 (live-profile is an operator exchange) | brief (E3, E6) | `store_identity`, `state_checkpoint`; live-profile gets its first native (E6) |\n| the three conformance families (`conformance.where/text/tail`, not on any wire) and `share/fn/wire-grammar.json` in the tarball | `wire-export.lisp:301-335`; `packaging/release-tarball.sh` step 2b; `tests/test_wire_grammar.py` | E (the grammar DSL emits the JSON) | plan (E3: the export comes out of `defgrammar`) | `test_wire_grammar.py` carried |\n| the local control socket: FNCT frames (magic, v1, kind, payload limit, BLAKE3-256 trailer) on the owner\'s 0600 Unix socket, peer UID checked, 16 control clients | `host/native/control.lisp`; spec seam L589-596; CLIENTS §1.1 | E over A\'s `listen(Unix)` and ROUND2 §D.1\'s `Qc` | brief (E3, E6) | `control`, `consumer_e2`; the FNCT codec fixtures |\n| the remote consumer (CNS-011 / PKT-673 / FNCR envelope): wait/poll/ack over the authenticated TLS connection, same cursor and report bytes, three outcomes, `position` to settle an uncertain ack; the waiter bound an operator setting; per-group/per-inbox wake | spec L772, 934-985 (spec only: "the decoder is not called on the served path"); emberian/fn#19; GOALS LD | E | plan (E3; EXECUTION-MODEL §7a item 4 is the owed specification; E3\'s specification quest fixes the carrier with its arithmetic, ember decides only the inbox model, D5 in §6) | sim scenarios 7, 8, 9 with the remote waiter workload machine; the reporter\'s numbers from #19 (30 seats, 4 boxes, 3-7k rows/day, wake p50/p95, crash/redelivery) published |\n| the consumer\'s exactly-once contract (its own inbox keyed `(history, incarnation, source, application-id, operation-id)`), `fn consumer …`, `consumer-article/inspect/project` | `host/native/consumer-local.lisp:157`; `signature-command.lisp`; spec "Consumer transaction and recovery" | E (clients) | brief (E6: the clients ship in the tarball) | `consumer_e2`, `consumer_inspect`, `consumer_project_bounds` |\n| **The operator CLI (`fn operator CONFIG VERB …`; `books/native-operator.lisp:922-990`; `host/native/operator.lisp:1205-1226`)** | | | | |\n| `init [--budget --largest --profile --max-*] GROUP…`, `run [--once]`, `mission small-community\\|relay\\|archive`, `show`, `help` | `docs/operator.md` L1264-1348, L1371, L570, L1352 | E | brief (E6) | `init_publication`, `start_every_preset`, `install`, `operator_walk`, `operator_cli`, `operator_verbs` |\n| `status [--watch --replay]`, `operation`, `health` (ten states; exit 19-29), `pins`, `obligations`; the service log and its reopen behaviour (`docs/operator.md` L227-240) | operator.md L158-225, L1369 | E | brief (E6) | `status_scale`, `init_status_probe`, `host_lifecycle`, `install`, `status_live_posts`, `open_depth` |\n| `post --message-id --payload --group` (local post) | help text | E | brief (E6) | `admin` |\n| `recover [--repair truncate SEG:OFF]` | operator.md L946, L983-1007 | E over B5 | brief (E6) | `operator_verbs`, `operator_walk`, `served_crash_model`, `recovery` |\n| `store export DIR`, `export --status`, `store import DIR [--FIELD N]`, `store bless-snapshot DIR` (backup, move, restore) | operator.md L774-837; install.md "Moving a store" | E over B, C | brief (E6) | `store_export`, `import_publication`, `snapshot_bless`, `image_differential`, `maintenance_live` |\n| `store compact` / `store checkpoint`, `store reclaim [--dry-run\\|--recorded]` (live only with `reclaim_live`), `store inspect MSGID\\|--group G`, `store rebind-filesystem` | operator.md L1183-1211, L1078-1110, L48-70 | E over B6, C5 | brief (E6) | `log_compaction`, `checkpoint`, `reclaim_walk`, `expiry`, `commit_log`, `store_mount_identity` |\n| `group create\\|retire\\|describe\\|policy\\|authority\\|moderate\\|subscribe-default`, `moderation list\\|approve\\|reject`, `motd set\\|clear`, `capacity N`, `retention set\\|expire` | operator.md §3 L246-311, L1364 | E over D\'s config transactions | brief (E6) | `group_authority`, `group_access`, `control_filing`, `moderation`, `operator_verbs`, `reader_index`, `expiry`, `over_pins` |\n| `account invite\\|list\\|set-password\\|access\\|delete\\|hash`, `principal list\\|set-password\\|delete\\|bind\\|unbind`, `consumer bind\\|unbind\\|show` | operator.md §4 L313-475 | E | brief (E6) | `friends_accounts`, `friends_feed`, `group_access`, `auth`, `injection_info`, `consumer_identity`, `agent_wait` |\n| `tls reload`, `tls self-signed NAME… [--days]` | operator.md §6 L477-541 | E | brief (E1, E6) | `tls_reload`, `operator_walk` |\n| `policy set KEY VALUE` (every live limit below) | operator.md §7 L566-690, L1278-1300 | E over D\'s configuration generations | brief (E6) | `limits_live`, `public_limits`, `live_reconfiguration` |\n| `peer set\\|login\\|add\\|remove\\|list\\|pull\\|pull-login\\|catch-up\\|feed pause/resume\\|distributions\\|budget`, `peer keygen\\|invite\\|accept\\|confirm` | operator.md §8 L693-719, L1353-1365; `docs/peering-with-a-friend.md` L28-224 | E | brief (E4, E6) | `peering`, `peer_pull`, `peer_catchup`, `peer_by_name`, `peer_invite`, `friends_feed` |\n| `bp-boundary add`, `bp-route add\\|remove`, `carry JOURNAL list\\|inspect\\|pause\\|resume\\|drop [--abandon]` | operator.md §8 L721-757 | E | brief (E5, E6) | `operator_verbs`, `source_corpus_bp`, `bp_carry_abandon` (raw today; E5 rewrites it black-box) |\n| `control grant\\|revoke\\|list\\|log\\|evidence`, `article withdraw MSGID --reason`, `keys redecide MSGID` | operator.md L1112-1137 | E | brief (E6) | `control_evidence`, `control_authority`, `control_filing`, `key_statements` |\n| `retire [--drain S]` | operator.md L853-890 | E | brief (E6) | `admin`, `conformance`, `peering` |\n| top-level: `fn store STORE {init\\|recover\\|node-secret create\\|rotate\\|status\\|checkpoint\\|digest\\|journal\\|export\\|bless-snapshot\\|import\\|retention\\|compression\\|rebind-filesystem\\|repair-control\\|config\\|inspect\\|provenance\\|probe\\|post}`, `fn redeem`, `fn identity`, `fn --version` (`fn 5.1.1 (REV12)`) | `host/native/io.lisp:9988-10071`; `store-identity.lisp:107`; operator.md L917-930, L346 | E | brief (E6) | `own_cancel`, `init_publication`, `friends_accounts`, `reader_clients`, `store_identity`; `fn --version` in the tarball test |\n| top-level `hybrid-sign\\|hybrid-author\\|hybrid-*`, `statement-sign` (`host/native/signature-command.lisp:257`), `checkpoint`, `heap`, `log`, `topic`, `pattern`, `anchor acquire STORE SERVER TIMEOUT` (`host/native/anchor.lisp:377`: obtains external evidence), `bp*`, `tcpcl`, `app-journal` (`host/native/workflow.lisp:722`: durable workflow and receipt operations), `config`, `digest-check`; `peer genesis` (`books/native-operator.lisp:964`) | `fnn-register-verb` sites in `host/native/*.lisp` | E | brief (E6): a per-verb disposition, *[Astra]*: **carried** `hybrid-*`, `statement-sign`, `topic`, `pattern`, `bp*`, `tcpcl`, `config`, `peer genesis`, `anchor acquire` (it is the independent frontier witness of ROUND2 §E.5 / STORAGE-DESIGN §4.4 and feeds B5\'s witness hook) and `app-journal` (with E5\'s custody); **candidates for removal, each with its external purpose, callers, replacement and lost capability recorded** (`fn2/docs/e-surface.md`, decision D4): `heap` (the installed launcher calls it: its probe must be replaced by the profile before removal), `log`, `checkpoint`, `digest-check` | `hybrid_author`, `pattern_pubsub`, `topic_local`; a removed verb\'s tests retire only with replacement coverage named |\n| exit codes: the complete exit-class table (refused 1, fault 4, usage, interrupted, not-connected, …; `books/outcome-class.lisp` read by `tools/outcome_codes.py:15-36`) and health\'s separate mapping: **ten** states (`fenced, exhausted, unqualified-profile, space-pressure, no-route, stranded-transfer, unavailable-peer, receipt-debt, disk, checkpoint-deferred`; `books/native-health.lisp:93-99`), exit 19 unobserved and 20-29 for the first state held; local fenced uncertainty distinguished from a client\'s uncertainty after reply loss (*[Astra]*) | `specs/host.md` CLI exit codes; `books/native-health.lisp:93-99`; node-functionality §3.4 | E | brief (E6) | `host_lifecycle`, `health`-bearing natives; an exit-table fixture; T6\'s image |\n| **Config (`fn.toml`, read at start) and live limits (`policy set`, durable config rows)** | | | | |\n| the accepted key set (`books/native-config.lisp:247-277`, `fn-ncfg-key-allowedp`): `[store] path`; `[listener] host\\|port\\|tls_cert\\|tls_key\\|tls_port` (0.0.0.0 and `::` refused); `[auth] required\\|protected_only\\|path`; `[posting] enabled\\|agent`; `[anchor] server`; `[acl2] path\\|slots`; `[log] path`; `[control] path`; `[alerts] command\\|headroom_min_percent\\|refusal_rate_per_minute\\|cooldown_seconds`; `[web] port\\|host\\|site\\|domain\\|proxied\\|tls\\|idle_seconds\\|max_sessions`; `[tls] key_exchange` (`hybrid-preferred`); `[resources] cold_heap_octets\\|cold_workers\\|cold_descriptors\\|cold_read_ids\\|cold_file_ids\\|output_heap_octets\\|output_quantum_heap_octets\\|reclaim_live`; `[ops] mission\\|unit\\|scope\\|keep_releases\\|log_max_bytes\\|log_keep\\|memory_max`; `run` refuses `[posting] agent`, `[anchor]`, `[acl2]` | `books/native-config.lisp:247-277`; operator.md L1245-1262; install.md L28; web.md L34-66 | E | brief (E6): *[Astra]* every key gets an explicit preserve / replace / remove disposition and a fixture; the `[resources] cold_*` and `output_*` keys are fn1\'s owner heap and are **replaced** by fn2\'s profile keys (ROUND2 §B.1/§G) with the old names refused by name, so the row\'s claim is "same keys where the semantics exist, named replacements where not", never "unchanged" | `install`, `start_every_preset`, `profile`, `heap_from_profile`, `web`; the `Node` adapter writes exactly these keys |\n| live limits: `exposure-connections` 31, `-per-address` 8, `-steps-per-second` 64, `-first-seconds` 60, `-idle-seconds` 600, `-auth-failures` 10/min, `-posts-per-minute` 60, `exposure-trusted`, `anonymous`; `tls-handshakes-per-source-per-minute` 30, `-in-flight` 16, `tls-handshake-ms` 5000, `-source-overrides`, `tls-proxy-trusted-peers`; `log-batch-records` 64, `log-batch-octets` 16 MiB; `barrier-deadline-ms` 5000, `barrier-stall-ms` 30000, `clock-event-ms` 1000; `compress-min-octets`; `disk-reserve-octets`; `relay-date-skew` 86400, `refused-offer-capacity` 4096, `relay-require-path`; `path-identity`, `posting-policy`, `complaints-to`; `max-transactions`, `max-history-octets`, `max-article-octets` (applied now / recorded for next start / refused by name) | `books/profile-limits.lisp:75-97`; `public-exposure-rows.lisp:67`; `owner-log-route.lisp:106-107`; `owner-time-model.lisp:56-58`; `limits-live.lisp`; `relay-checks.lisp:340-343`; operator.md L1283-1295 | D (the policy values are configuration-generation fields read by the machines) + E (the verb) | brief (D7, E6) | `limits_live`, `public_limits`, `live_reconfiguration`, `tls_handshake_budget`, `capacity_vector`, `bounds_join`, `credits` |\n| `init`-time fixed limits (`--max-record-octets`, `--max-groups-per-article`, `--max-open-suffix`, `--max-consumers`, `--max-config-generations`, `--max-credentials`, `--max-bp-rows`, `--max-group-name-octets`, `--max-policy-members`, `--profile`, `--budget`) and the runtime profile (`max-connections` 32, `control-clients` 16, …) | operator.md L1297-1300; `docs/resource-contract.md` L1039-1045 | E (they become profile keys: structural capacities for process life, data limits as the operator\'s profile, EXECUTION-MODEL §7 item 3: no compile-time ceilings) | brief (E6) | `profile`, `start_every_preset`, `image_floor`, `image_heap` (re-stated for fn2\'s resident numbers) |\n| **The web reader inside the node (`books/web-request.lisp:983-998` `*fn-web-routes*`; 15 routes, 11 paths)** | | | | |\n| `GET/HEAD /health` (200 `ready`; 503 `unavailable disk\\|checkpoint` / `unobserved`), `GET /style.css`; HEAD on every GET route (`web-request.lisp:961`); request-level 400/411/413/501/505; Transfer-Encoding rejected (fn1 takes no chunked bodies; a chunked extension is explicit or absent, *[Astra]*) | `web-health.lisp`; `web.md` L159-173 | E | brief (E7) | `web`; a health fixture |\n| `GET/POST /signin` (login CSRF `:pre`), `GET/POST /redeem` (XREDEEM), `POST /theme` (same-site), `POST /signout` (CSRF) | `web-session.lisp` (`fn-wss-signin`, `-redeem`, `-theme`, `-signout`) | E over E2\'s accounts | brief (E7) | `web`; a session fixture (sign-in, redeem, sign-out, idle expiry) |\n| `GET /` (groups, LIST ACTIVE), `GET /g?name&before` (group, older posts), `GET /a?g&n` (article) | `fn-wss-groups`, `-group`, `-article`; `web.md`, `reader.md` L9-20 | E over D6 (the same cursor machine renders HTML) | brief (E7) | `web`; HTML fixtures per page (the rendered bytes for a fixed store) |\n| `GET /new?g`, `POST /post` (CSRF; the three sentences: Posted! / The server said no / We couldn\'t tell) | `fn-wss-compose`, `-post`; `reader.md` L17-23 | E over D5 | brief (E7) | `web`; T6\'s three outcomes on the page |\n| `GET/POST /remove` (Remove my post; CSRF) | `fn-wss-remove-form`, `-remove` | E over D4 (own-cancel) | brief (E7) | `web` |\n| 404 / 405 with Allow (15 routes on 12 paths: `/ /a /g /health /new /post /redeem /remove /signin /signout /style.css /theme`); `[web]` config; `LISTENING-WEB`; sessions in memory until sign-out, `idle_seconds` or restart; no accounts or permissions of its own (WEB-003/005) | `fn-web-route` (PRF-337); `web.md` L34-66; `specs/human-client.md` | E | brief (E7) | `web`; the HTTP grammar fuzzer |\n| not on the page (fn1, stated): threads, search, read-marking, moderation, JSON API | `web.md` L151; issues #1, #2 | — | not surface (not carried in 5.1.1; after) | — |\n| **Peering (`INTERFACES-TODAY` §peering: 49 books, 145 host entries; `docs/peering-with-a-friend.md`)** | | | | |\n| outbound feed (push): Message-ID queue with offer state; IHAVE / CHECK+TAKETHIS streaming; 436 backoff; distributions; `path-identity` loop detection; feed journal FNFD | `peer-feed.lisp:596-1092`; `feed-journal.lisp`; `host/native/feed-service.lisp` | E (a peer-connection machine: D\'s connection machine in client role over `Connect`) | brief (E4) | sim peer workload (two simulated nodes); `peering`, `friends_feed`, `feed_reply_cold`, `feed_temporary`, `peer_rows_growth` |\n| pull: dial, DATE, NEWNEWS since a cursor; each Message-ID offered to the node\'s own IHAVE decision on a logical transit connection; pull journal; `peer pull friend SECONDS` | `peer-pull.lisp:307-1836`; `peer-pull-session.lisp`; `host/native/pull-service.lisp` | E | brief (E4) | `peer_pull`, `peer_by_name`, `test_pull_from_inn` (INN 2.7.4, `tests/inn/pin.json`; FN_INN_SRC) |\n| catch-up: XFNCATCHUP batches in 512-octet windows to a private spool; digest chain compared; replay oldest-first by IHAVE; FNCU journal; refusals `digest-mismatch`, `peer-lacks-catch-up`, `local-deferred`, `peer-flight-unfunded` | `peer-catchup.lisp:292-668`; `peer-catchup-spool.lisp`; `host/native/catchup-spool.lisp` | E | brief (E4) | `peer_catchup`; L-CATCHUP (W6q/W6a) published |\n| the round driver (deadlines, resume, idle, write quanta) | `peer-round-driver.lisp:62-216` | E (it is D\'s timer service plus the peer machine\'s phases) | brief (E4) | `peering`, `peer_misbehaving` |\n| invite / enrol: `peer keygen\\|invite\\|accept\\|confirm\\|list`; encrypted feed both ways with `--tls starttls\\|implicit --server-name --anchor`; `peer login`, `peer pull-login` | `peer-invite.lisp`; `host/peer-invite-host.lisp`; peering-with-a-friend L28-120 | E | brief (E4, E6) | `peer_invite`, `protected_peering`, `control_across_peers` |\n| the guide\'s two "known gaps" (peering-with-a-friend L243-250) are stale, *[Astra]*: dedicated pull credentials exist and are tested (`peer pull-login`; `tests/test_native_peer_pull.py:805-833`, SCN-1139: survives feed edits and restart, works with outbound disabled) and the 500/501 → IHAVE fallback for non-streaming peers is specified (`specs/nntp.md:2414-2450`) | `test_native_peer_pull.py:805`; `specs/nntp.md:2414-2450` | E | brief (E4 carries SCN-1139 and the fallback; any remaining non-streaming defect is identified by a failing transcript before a fix is scheduled) | `peer_pull` (SCN-1139), `peering`, `feed_temporary` |\n| **BP / DTN (BPv7 RFC 9171, TCPCLv4 RFC 9174; 184 books; QUARRY "bpnm" LIFT WHOLE 27 books)** | | | | |\n| the BP outbound bundle machine (`fn-bpn-step`: enqueue, contact, resume, persist-result, forward-result, clock, restart; 64 jobs, 16 MiB, 4,096 records; keystone M1) | `books/bp-node-machine.lisp:1072`; `bp-node-foundation.lisp:717`; `bp-node-progress.lisp:1824` | E (quarried, polished, re-declared through D1\'s machine DSL over the pool) | brief (E5) | the dtn7-rs golden bundles (`tests/bp-dtn7/`, 7 drivers); `source_corpus_bp`; F8 as a sim scenario (two nodes, lost receipts, duplicates, restarts, incarnation change, divergence 0) |\n| TCPCLv4 session (`drive, open, send, pump, tick, terminate, tcp-closed`; one outbound transfer at a time; no TLS upgrade) | `books/tcpcl-session.lisp:438-1042`; `host/native/tcpcl.lisp` | E over A\'s sockets | brief (E5) | dtn7-rs interop (pinned 0.21.0); `tcpcl_acquisition` rewritten black-box |\n| custody and receipts: forwarding as a retention obligation released only by the peer\'s receipt or a recorded waiver; `carry` verbs; receipt regeneration | operator.md §8 L728-733; CLIENTS §1.5; `bp-obligation.lisp` | E over C\'s obligations schema | brief (E5) | F8; `bp_carry_abandon` |\n| BP receivers / ingress / native-app (QUARRY REWRITE, 49 books) | `bp-receiver*`, `bp-app*` | E | brief (E5: rewrite as machines; the DTN image is one build, not a second server) | the golden bundles\' receive half |\n| ION-DTN LTP/UDP (one feasibility run; no non-destructive receive) | `tests/ltp/`; CLIENTS §1.5 | — | not surface (feasibility only; not carried in 5.1.1) | — |\n| **Store operator operations** (init, import, status, reclaim, backup) | the CLI rows above: `init`, `store import`, `status`, `store reclaim`, `store export`/`bless-snapshot` | E over B, C | brief (E6) | the rows\' natives; plus RECLAIM and RECOVERY on the import/export paths (sim) |\n| **Release artefacts and deployment** | | | | |\n| `fn-VERSION-linux-x86_64.tar.gz`, `fn-VERSION-openbsd-amd64.tar.gz`, `SHA256SUMS`; layout `fn/{SHA256SUMS,install.sh,bin/fn,libexec/fn/…,share/fn/…,clients/}`; no images, no signatures | `packaging/release-tarball.sh:2-90`; install.md L40-41 | R | plan (R3; the OpenBSD tarball is decision D1, signing D2) | gate 12/13 of `cut_release.sh` (`test_release_tarball`, `fn --version` on Debian 12; `openbsd_smoke.sh`) |\n| `tools/cut_release.sh`\'s 17 gates (version, tree, fundamentals, changelog, closure, check, docs, runpath, native, throughput, hostile, tarball-linux, tarball-openbsd, power-loss, friends, extract, tag) and `planning/release-vVERSION.md` | `tools/cut_release.sh` L29-63, L557-573 | R | plan (R1 rewrites the checklist for fn2\'s tree: the gates stay, their commands change; `planning/release-v5.1.1.md` must exist or gate 01 is red) | the cut itself |\n| the public node `fn.fg-goose.online` (ports 563 / 119, Let\'s Encrypt, no anonymous reading, XREDEEM invitations, the seven groups, one peer) and its runbook | `docs/public-node.md`; `planning/runbook-public-node-2026-09-27.md` (A1-A9, Layout B, Rollback); `docs/nodes/fsn1.md` L31-37 (fresh install, D34/D60) | R | plan (R4) | A8 "check it from outside": greeting over 563 and 119, XREDEEM, a post, a read, the peer\'s feed |\n| `docs/install.md`, `docs/operator.md`, `docs/web.md`, `docs/reader.md`, `docs/agents.md`, `docs/peering-with-a-friend.md`, the FAQ articles (`articles/*.txt`) in `share/fn/` | the files | R | plan (R3: rewritten whole for fn2 where a row above changed; install.md L42-45\'s "first release is 6.6.0" is stale and goes) | `docs_check --check` (gate 07) |\n| the clients: `fn-client`, `fn-agent`, `fn-consumer`, `fn-verify`; `docs/agents.md` | `clients/`; tarball layout | E/R | brief (E6) | `test_release_tarball`; the clients\' own tests carried |\n| **The natives as the classical gate** | `tests/test_native_*.py` (247 modules; 87 black-box, 33 node+internal); `tests/native_harness.py:1413` `Node`, its launcher path `:1379-1405`, `tools/outcome_codes.py:15-36` | §2.6 | plan (the `Node` adapter and the dependency inventory are quest H1 of §5.5, starts now) | the 87 plus the socket halves of the 33 green on the release sha; the carried reds at the cut base (`bounds_join`, `decoded_custody`, `mux`, `public_limits`, `resilience_cuts`, `status_live_posts`) are not accepted as pre-existing: each is green or its row says why |'
RELEASE_FIRST_LINE = 19

ROOT = Path(__file__).resolve().parents[3]
JUDGMENTS_DIR = Path(__file__).with_name('judgments')
DEFAULT_OUT = ROOT / 'build/natives'
FIELDS = ('images', 'skips', 'node_construction', 'config_keys', 'cli_verbs',
          'control_socket', 'developer_selectors', 'fixtures', 'helpers', 'wires')
OPERATIONS = ('start', 'stop', 'config', 'socket', 'control', 'kill_at', 'observe')
MARKER = '<!-- BEGIN GENERATED INVENTORY -->\n'
MARKDOWN_HEAD = "# Native dependency inventory (H1a)\n\nThis inventory covers the supplied 87 `node` and 33 `node_internal` quarry modules at fn1 `6521f18c4`. It inventories dependencies and replacement evidence; it does not run the natives or implement the H1b adapter.\n\n`inventory.py` uses only Python's standard library. Its AST pass reads the original sources without importing them; the per-module records in `fn2/tests/harness/judgments/` (one JSON file per module, validated against `judgments.schema.json`) carry the reviewed representation sites and module decisions. Frozen copies of the supplied quarry lists and release-plan table make regeneration independent of the coordinator's scratch directory. Section 1 coverage is the mechanical inverse of that table's test column, including wildcard module names.\n\nThis document and `natives-inventory.json` are build outputs, never committed: `python3 -m fn2.tests.harness.inventory --out build/natives` writes both, and `inventory.load()` regenerates them when any input changes. `--check` checks subject totals, dependency sites, row references and the mixed-module method partitions.\n\nDependency sites are qualified by `source`; `via` records imported fixture chains. Literal arguments and forwarding wrappers are resolved where possible. `dynamic` retains an unresolved expression and its site rather than inventing a value. Counts are module unions, including reachable shared helpers. `test_methods` expands static unittest inheritance; `declared_test_methods` counts definitions, including mixins.\n\nThe seven adapter operations are `start`, `stop`, `config`, `socket`, `control`, `kill_at`, and `observe`. `carry-with-adapter` includes modules with a public core whose cited representation assertions need replacement. `carry-socket-half` records the public methods separately from probes, mixed methods and source-only checks; it can expose a hidden probe even in the supplied `node` category. `rewrite-row` retains the named public obligation while replacing the old test design. A public-contract verdict identifies a carried observable, not approval of fn1's encoding or implementation as fn2's design.\n\nNode starts also depend on the installed launcher, core layout, heap probe, deployed stack, pinned OpenSSL prefix and liveness obligations. These inherited requirements are counted. `require_node_greeting` must observe an existing NNTP/control/HTTP response or a named terminal outcome; a readiness announcement alone is insufficient. H1b must replace the outcome-table, protocol-table and environment-selector source dependencies, and preserve uncertainty separately from refusal.\n\nHost-requirement counts describe what each module depends on, including tests needing rewrites. They do not imply that one item alone makes those modules pass. Old heap keys, storage layouts, fault-cut names and in-image probes require the public replacements listed below. No image availability, runtime skips or native assertions were exercised for H1a.\n\n"
IMAGE_KINDS = {'FN_NATIVE_HOST': 'production', 'FN_NATIVE_DEVELOPER_HOST': 'developer',
               'FN_NATIVE_REFERENCE_HOST': 'reference',
               'FN_NATIVE_DEVELOPER_STRIPPED_HOST': 'developer-stripped',
               'FN_NATIVE_CRASH_HOST': 'crash', 'FN_NATIVE_DTN_DEVELOPER_HOST': 'dtn-developer'}
UNKNOWN = object()


def name(node):
    if isinstance(node, ast.Name):
        return node.id
    if isinstance(node, ast.Attribute):
        return name(node.value) + '.' + node.attr
    return ''


def expr(node):
    return ast.unparse(node) if node is not None else ''


def constants(node):
    return [n.value.decode('utf-8', 'replace') if isinstance(n.value, bytes) else n.value
            for n in ast.walk(node) if isinstance(n, ast.Constant)
            and isinstance(n.value, (str, bytes))]


def doc_nodes(tree):
    return {id(n.value) for n in ast.walk(tree)
            if isinstance(n, ast.Expr) and isinstance(n.value, ast.Constant)
            and isinstance(n.value.value, str)}


class Source:
    """No imports/evaluation: modest constant propagation retains unknowns explicitly."""
    def __init__(self, path):
        self.path = path
        self.text = (ROOT / path).read_text()
        self.tree = ast.parse(self.text, filename=path)
        self.lines = self.text.splitlines()
        self.bindings = {}
        self.imports = {}
        self.defs = {}
        self.parents = {}
        for node in ast.walk(self.tree):
            for child in ast.iter_child_nodes(node):
                self.parents[child] = node
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
                self.defs.setdefault(node.name, []).append(node)
            if isinstance(node, (ast.Assign, ast.AnnAssign)):
                targets = node.targets if isinstance(node, ast.Assign) else [node.target]
                for target in targets:
                    if isinstance(target, (ast.Name, ast.Attribute)) and node.value is not None:
                        self.bindings.setdefault(name(target), []).append(node.value)
            if isinstance(node, ast.ImportFrom) and node.module:
                for alias in node.names:
                    self.imports[alias.asname or alias.name] = (node.module, alias.name, node.lineno)
            if isinstance(node, ast.Import):
                for alias in node.names:
                    self.imports[alias.asname or alias.name] = (alias.name, '*', node.lineno)

    def resolve(self, node, seen=()):
        if node is None:
            return UNKNOWN
        if isinstance(node, ast.Constant):
            return node.value
        if isinstance(node, (ast.Name, ast.Attribute)):
            key = name(node)
            if key in seen:
                return UNKNOWN
            bindings = self.bindings.get(key, [])
            if len(bindings) == 1:
                return self.resolve(bindings[0], (*seen, key))
            return UNKNOWN
        if isinstance(node, ast.JoinedStr):
            return ''.join(str(n.value) if isinstance(n, ast.Constant) else '{dynamic}' for n in node.values)
        if isinstance(node, (ast.List, ast.Tuple, ast.Set)):
            return [self.resolve(n, seen) for n in node.elts]
        if isinstance(node, ast.Dict):
            return {self.resolve(k, seen): self.resolve(v, seen) for k, v in zip(node.keys, node.values)
                    if isinstance(k, ast.Constant)}
        if isinstance(node, ast.BinOp):
            a, b = self.resolve(node.left, seen), self.resolve(node.right, seen)
            if isinstance(node.op, ast.Add) and type(a) is type(b) and isinstance(a, (str, bytes, list)):
                return a + b
            if isinstance(node.op, ast.Div):
                if isinstance(b, str):
                    return (a.rstrip('/') + '/' if isinstance(a, str) else '{dynamic}/') + b
            if isinstance(node.op, ast.Mod) and isinstance(a, (str, bytes)):
                return a
        if isinstance(node, ast.Call):
            fn = name(node.func).rsplit('.', 1)[-1]
            if fn in ('str', 'Path', 'bytes') and node.args:
                return self.resolve(node.args[0], seen)
            if isinstance(node.func, ast.Attribute) and fn in ('format', 'encode', 'decode', 'rstrip', 'strip'):
                return self.resolve(node.func.value, seen)
        return UNKNOWN

    def scope(self, node):
        while node in self.parents:
            node = self.parents[node]
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                parent = self.parents.get(node)
                return (parent.name + '.' if isinstance(parent, ast.ClassDef) else '') + node.name
        return '<module>'

    def selected(self, symbol):
        """A module-level symbol and the local functions/constants it reads."""
        if symbol == '*':
            return [self.tree]
        pending, selected, visited = [symbol], [], set()
        while pending:
            key = pending.pop()
            if key in visited:
                continue
            visited.add(key)
            roots = [n for n in self.defs.get(key, []) if isinstance(self.parents.get(n), ast.Module)]
            roots += [n for n in self.bindings.get(key, []) if isinstance(self.parents.get(self.parents.get(n)), ast.Module)]
            for root in roots:
                selected.append(root)
                for n in ast.walk(root):
                    if isinstance(n, ast.Name) and isinstance(n.ctx, ast.Load):
                        pending.append(n.id)
        return selected


_SOURCES = {}

def source(path):
    if path not in _SOURCES:
        _SOURCES[path] = Source(path)
    return _SOURCES[path]


def image_defaults():
    src = source('tests/native_harness.py')
    return src.resolve(src.bindings['IMAGE_DEFAULTS'][0])


def rows():
    result = []
    for number, line in enumerate(RELEASE_SECTION_1.splitlines(), RELEASE_FIRST_LINE):
        cells = [c.strip().replace('\\|', '|') for c in re.split(r'(?<!\\)\|', line)[1:-1]]
        if len(cells) != 5 or not cells[4] or cells[0] in ('surface item', '---'):
            continue
        result.append({'row': cells[0], 'status': cells[3], 'test': cells[4], 'line': number,
                       'carried': not ('drop' in cells[3] or 'not carried' in cells[3])})
    return result


def witnessed(module, release_rows):
    matches = []
    for row in release_rows:
        for token in re.findall(r'`([^`]+)`', row['test']):
            token = token.removeprefix('tests/test_native_').removeprefix('test_native_').removesuffix('.py')
            if re.fullmatch(re.escape(token).replace(r'\*', '.*'), module):
                matches.append(row['row'])
                break
    return matches or ['unclaimed']


def store_expression(src, node):
    # Bindings form a graph (the same local name can occur in several scopes).
    # Visit each AST node once; recursive path enumeration is exponential.
    pending, visited = [node] if node is not None else [], set()
    while pending:
        current = pending.pop()
        if id(current) in visited:
            continue
        visited.add(id(current))
        if isinstance(current, ast.Attribute) and current.attr == 'store_path':
            return True
        if isinstance(current, (ast.Name, ast.Attribute)):
            key = name(current)
            if key in ('self.store', 'cls.store', 'store'):
                return True
            pending.extend(src.bindings.get(key, []))
        pending.extend(ast.iter_child_nodes(current))
    return False


def wrappers(src):
    """Infer forwarding wrappers from their *args path, without running them."""
    if hasattr(src, '_wrappers'):
        return src._wrappers
    result = {'op': (0, ['operator', None]), 'store_cli': (0, ['store', None])}
    functions = [n for n in ast.walk(src.tree) if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef)) and n.args.vararg]
    for _ in range(len(functions) + 1):
        previous = dict(result)
        for function in functions:
            vararg = function.args.vararg.arg
            params = [a.arg for a in function.args.posonlyargs + function.args.args if a.arg not in ('self', 'cls')]
            for call in ast.walk(function):
                if not isinstance(call, ast.Call):
                    continue
                short = name(call.func).rsplit('.', 1)[-1]
                sequence = None
                if short in ('operator', 'store'):
                    sequence = [short, None] + list(call.args)
                elif short == 'invoke':
                    sequence = list(call.args)
                elif short in result and short != function.name:
                    offset, head = result[short]
                    sequence = [call.args[v[1]] if isinstance(v, tuple) and v[0] == 'param' and len(call.args) > v[1] else v for v in head] + list(call.args[offset:])
                elif short in ('run', 'Popen', 'start', 'start_filed', 'check_call', 'check_output'):
                    for arg in call.args:
                        if isinstance(arg, (ast.List, ast.Tuple)):
                            elements = arg.elts
                            found = next((i for i, e in enumerate(elements) if isinstance(e, ast.Constant) and e.value == '--fn'), None)
                            if found is not None:
                                sequence = list(elements[found + 1:])
                                break
                if sequence is None:
                    continue
                for index, element in enumerate(sequence):
                    if isinstance(element, ast.Starred) and (name(element.value) == vararg or vararg in expr(element.value)):
                        head = []
                        for value in sequence[:index]:
                            if isinstance(value, ast.Name) and value.id in params:
                                head.append(('param', params.index(value.id)))
                            elif isinstance(value, tuple):
                                head.append(value)
                            else:
                                resolved = src.resolve(value) if isinstance(value, ast.AST) else value
                                head.append(resolved if isinstance(resolved, str) else None)
                        # Only operator/config/verb/subverb can enter the requested verb path.
                        result[function.name] = (len(params), head[:4])
                        break
        if result == previous:
            break
    src._wrappers = result
    return result


class Extractor:
    def __init__(self, src, roots=None):
        self.src = src
        self.nodes = sorted({n for root in (roots or [src.tree]) for n in ast.walk(root)},
                            key=lambda n: (getattr(n, 'lineno', 0), getattr(n, 'col_offset', 0), type(n).__name__))
        self.data = {field: {} for field in FIELDS + ('exit_classes', 'announcements', 'argv_shapes')}
        self.docstrings = doc_nodes(src.tree)
        self.defaults = image_defaults()
        self.wrappers = wrappers(src)

    def add(self, field, value, node, operations, **extra):
        line = node if isinstance(node, int) else node.lineno
        key = json.dumps([value, extra], sort_keys=True)
        record = self.data[field].setdefault(key, {'value': value, 'sites': [], 'operations': sorted(set(operations)), **extra})
        record['sites'] = sorted(set(record['sites']) | {line})
        record['operations'] = sorted(set(record['operations']) | set(operations))

    def wire(self, value, node):
        op = ('control',) if value in ('control-fnct', 'consumer', 'operator-cli') else ('observe',) if value == 'store-files' else ('socket',)
        self.add('wires', value, node, op)

    def image(self, arg, site):
        candidates = []
        visited = set()
        def visit(src, node):
            key = (src.path, expr(node))
            if key in visited:
                return
            visited.add(key)
            value = src.resolve(node)
            if isinstance(value, str) and value in self.defaults:
                candidates.append((value, self.defaults[value]))
            if isinstance(node, ast.Call) and name(node.func).rsplit('.', 1)[-1] in ('native_image', 'get', 'getenv') and node.args:
                variable = src.resolve(node.args[0])
                if isinstance(variable, str) and variable in self.defaults:
                    default = src.resolve(node.args[1]) if len(node.args) > 1 else self.defaults[variable]
                    candidates.append((variable, default if isinstance(default, str) else 'dynamic: ' + expr(node.args[1])))
            if isinstance(node, (ast.Name, ast.Attribute)):
                for binding in src.bindings.get(name(node), []):
                    visit(src, binding)
                if name(node) in src.imports:
                    module, symbol, _ = src.imports[name(node)]
                    path = module.replace('.', '/') + '.py'
                    if (ROOT / path).is_file():
                        dep = source(path)
                        for binding in dep.bindings.get(symbol, []):
                            visit(dep, binding)
            if isinstance(node, (ast.IfExp, ast.BoolOp)):
                for child in ast.iter_child_nodes(node):
                    visit(src, child)
        visit(self.src, arg)
        for variable, default in sorted(set(candidates)):
            self.add('images', variable, site, ['start'], default=self.defaults[variable],
                     image=IMAGE_KINDS.get(variable, 'dtn'), resolved_default=default, expression=expr(arg))
        if not candidates:
            self.add('images', expr(arg), site, ['start'], default=None, image='dynamic', resolved_default=None, expression=expr(arg))

    def config(self, arg, site, table='listener'):
        value = self.src.resolve(arg)
        if isinstance(value, bytes):
            value = value.decode('utf-8', 'replace')
        if not isinstance(value, str):
            self.add('config_keys', 'dynamic', site, ['config'], expression=expr(arg))
            return
        found = False
        for line in value.splitlines():
            section = re.match(r'\s*\[([\w.-]+)\]', line)
            if section:
                table = section[1]
            key = re.match(r'\s*([\w-]+)\s*=', line)
            if key:
                self.add('config_keys', (table + '.' if table else '') + key[1], site, ['config'])
                found = True
        if not found and ('dynamic' in value or '%' in value or '{' in value):
            self.add('config_keys', 'dynamic', site, ['config'], expression=expr(arg))

    def cli(self, args, site, prefix=None, expanded=False):
        if not expanded:
            parent = site
            while parent in self.src.parents:
                parent = self.src.parents[parent]
                if isinstance(parent, ast.For):
                    values = self.src.resolve(parent.iter)
                    targets = [parent.target] if isinstance(parent.target, ast.Name) else (parent.target.elts if isinstance(parent.target, (ast.Tuple, ast.List)) else [])
                    target_names = [t.id for t in targets if isinstance(t, ast.Name)]
                    if isinstance(values, list) and target_names and any(isinstance(a, ast.Name) and a.id in target_names or isinstance(a, ast.Starred) and isinstance(a.value, ast.Name) and a.value.id in target_names for a in args):
                        def literal(value):
                            if isinstance(value, list):
                                return ast.List(elts=[literal(v) for v in value], ctx=ast.Load())
                            return ast.Constant(value=value) if isinstance(value, (str, bytes, int, bool)) or value is None else ast.Name(id='dynamic', ctx=ast.Load())
                        for row in values:
                            row = [row] if len(target_names) == 1 else row
                            if not isinstance(row, list) or len(row) != len(target_names):
                                continue
                            mapping = dict(zip(target_names, row))
                            replaced = []
                            for a in args:
                                if isinstance(a, ast.Name) and a.id in mapping:
                                    replaced.append(literal(mapping[a.id]))
                                elif isinstance(a, ast.Starred) and isinstance(a.value, ast.Name) and a.value.id in mapping:
                                    replaced.append(ast.Starred(value=literal(mapping[a.value.id]), ctx=ast.Load()))
                                else:
                                    replaced.append(a)
                            self.cli(replaced, site, prefix=prefix, expanded=True)
                        return
                if isinstance(parent, (ast.FunctionDef, ast.AsyncFunctionDef)):
                    break
        vals = [self.src.resolve(a) for a in args]
        if prefix:
            vals.insert(0, prefix)
        if not vals:
            return
        if any(isinstance(a, ast.Starred) for a in args):
            expanded = []
            for a in args:
                if isinstance(a, ast.Starred):
                    value = self.src.resolve(a.value)
                    expanded.extend(value if isinstance(value, list) else [UNKNOWN])
                else:
                    expanded.append(self.src.resolve(a))
            vals = ([prefix] if prefix else []) + expanded
        if vals[0] is UNKNOWN or not isinstance(vals[0], str):
            self.add('cli_verbs', 'dynamic', site, ['control'], expression=', '.join(expr(a) for a in args))
            return
        # CONFIG and STORE are operands, not words in a verb path.
        if vals[0] in ('operator', 'store') and prefix is None and len(vals) > 2:
            vals.pop(1)
        words = [vals[0]]
        for v in vals[1:3]:
            if not isinstance(v, str) or v.startswith('-') or not re.fullmatch(r'[a-z][a-z0-9-]*', v):
                break
            words.append(v)
            if len(words) == (3 if words[0] == 'operator' else 2):
                break
        if len(words) == 1 and len(vals) > 1 and vals[1] is UNKNOWN:
            words.append('dynamic')
        self.add('cli_verbs', ' '.join(words), site, ['control'])
        self.wire('operator-cli', site)
        if words[:2] == ['operator', 'peer']:
            self.wire('peering', site)
        if '--tls' in vals:
            if 'starttls' in vals:
                self.wire('starttls', site)
            if 'implicit' in vals:
                self.wire('implicit-tls', site)
        if words[0].startswith(('bp', 'tcpcl')) or words[0] == 'app-journal':
            self.wire('bp/tcpcl', site)
        if vals[0] in ('consumer', 'topic', 'identity', 'hybrid-enroll', 'hybrid-author', 'hybrid-revoke'):
            self.wire('consumer', site)
            self.add('control_socket', 'CLI over control: ' + ' '.join(words), site, ['control'])

    def run(self):
        node_calls = []
        node_subclasses = {c.name for c in ast.walk(self.src.tree) if isinstance(c, ast.ClassDef) and any(name(b).endswith('Node') for b in c.bases)}
        for n in self.nodes:
            if isinstance(n, ast.ImportFrom) and n.module and (n.module in ('tests', 'tools') or n.module.startswith(('tests.', 'tools.'))):
                for a in n.names:
                    self.add('helpers', n.module + '.' + a.name, n, ['observe'], alias=a.asname or a.name)
            if isinstance(n, ast.Import):
                for a in n.names:
                    if a.name.startswith(('tests.', 'tools.')) or (ROOT / 'tools' / (a.name + '.py')).is_file():
                        self.add('helpers', a.name if '.' in a.name else 'tools.' + a.name, n, ['observe'], alias=a.asname or a.name)
            if isinstance(n, ast.Name) and n.id.startswith('EXIT_') and n.id[5:] in ('OK', 'REFUSED', 'UNCERTAIN', 'FAULT', 'USAGE', 'INTERRUPTED', 'NOT_CONNECTED'):
                self.add('exit_classes', 'EXIT.' + n.id[5:], n, ['observe'])
            if isinstance(n, ast.Attribute):
                if name(n).startswith('EXIT.'):
                    self.add('exit_classes', name(n), n, ['observe'])
                if n.attr == 'AF_UNIX':
                    self.add('control_socket', 'Unix control socket', n, ['control'])
                    self.wire('control-fnct', n)
                if n.attr == 'control':
                    self.add('control_socket', expr(n), n, ['control'])
                if n.attr in ('stdout', 'stderr', 'returncode'):
                    self.add('announcements', 'stdout/stderr/exit observation', n, ['observe'])
            if isinstance(n, ast.Constant) and isinstance(n.value, (str, bytes)) and id(n) not in self.docstrings:
                value = n.value.decode('utf-8', 'replace') if isinstance(n.value, bytes) else n.value
                for match in re.finditer(r'\b(?:FN_[A-Z0-9_]+|SBCL_USER_ARGS|SBCL_HOME|ACL2_CUSTOMIZATION|ACL2_SYSTEM_BOOKS)\b', value):
                    selector = match[0]
                    self.add('developer_selectors', selector, n, ['start', 'kill_at'] if any(s in selector for s in ('FAULT', 'STALL', 'CUT', 'KILL', 'STOP')) else ['start'])
                for path in re.findall(r'(?:tests/fixtures|books|host|specs|docs|packaging|clients|tools)/[\w./*+{}-]+', value):
                    self.add('fixtures', path, n, ['config' if path.startswith('packaging/') else 'observe'])
                if value.startswith(('LISTENING', 'CONTROL ')):
                    self.add('announcements', value.rstrip(), n, ['observe'])
                if re.search(r'\((?:fn[n-]|in-package|load |setf |sb-ext:|defun )', value):
                    self.add('helpers', 'raw Lisp: ' + value.strip()[:180], n, ['observe'])
                if re.search(r'(?:target/release/|/bin/)(?:dtnd|dtnsend|curl|openssl)\b', value):
                    self.wire('external', n)
                if 'FNCT' in value or 'fn-nctrl-' in value:
                    self.add('control_socket', 'FNCT frame: ' + value[:160], n, ['control'])
                    self.wire('control-fnct', n)
                if 'fn-consumer-' in value or 'fncu' in value or 'fnct.consumer' in value:
                    self.add('control_socket', 'consumer codec: ' + value[:160], n, ['control'])
                    self.wire('consumer', n)
            if isinstance(n, ast.BinOp) and isinstance(n.op, ast.Div):
                value = self.src.resolve(n)
                if isinstance(value, str):
                    path = re.search(r'(tests/fixtures|books|host|specs|docs|packaging|clients|tools)/.+', value)
                    parent = self.src.parents.get(n)
                    if path and not (isinstance(parent, ast.BinOp) and isinstance(parent.op, ast.Div)):
                        self.add('fixtures', path[0], n, ['observe'])
            if not isinstance(n, ast.Call):
                continue
            fn = name(n.func)
            short = fn.rsplit('.', 1)[-1]
            if short in ('read_text', 'read_bytes', 'write_text', 'write_bytes', 'open', 'iterdir', 'glob', 'rglob', 'stat', 'unlink', 'exists', 'is_file', 'is_dir', 'copytree', 'copyfile', 'copy2', 'move', 'rename', 'truncate'):
                target = n.func.value if isinstance(n.func, ast.Attribute) and short not in ('copytree', 'copyfile', 'copy2', 'move') else (n.args[0] if n.args else None)
                if store_expression(self.src, target):
                    self.wire('store-files', n)
            kwargs = {k.arg: k.value for k in n.keywords}
            if short in self.wrappers and short not in ('operator', 'store', 'invoke'):
                offset, head = self.wrappers[short]
                args = [n.args[v[1]] if isinstance(v, tuple) and v[0] == 'param' and len(n.args) > v[1] else ast.Constant(value=v if not isinstance(v, tuple) else None) for v in head] + list(n.args[offset:])
                self.cli(args, n)
            if short in ('fn', 'native', 'run_native', 'run_fn', 'image', 'command', 'ok', 'spawn') and short not in self.wrappers:
                # A literal CLI head in a project wrapper is still observable.
                for index, arg in enumerate(n.args[:3]):
                    if self.src.resolve(arg) in ('operator', 'store', 'consumer', 'topic', 'pattern', 'heap', 'checkpoint', 'log', 'bp', 'tcpcl', 'model', 'reader', 'hybrid-sign', 'hybrid-enroll', 'identity'):
                        self.cli(n.args[index:], n)
                        break
            if short == 'native_image' and n.args:
                self.image(n, n)
                if len(n.args) > 1:
                    variable = self.src.resolve(n.args[0])
                    for record in self.data['images'].values():
                        if record['value'] == variable and n.lineno in record['sites']:
                            record['resolved_default'] = self.src.resolve(n.args[1]) if isinstance(self.src.resolve(n.args[1]), str) else 'dynamic: ' + expr(n.args[1])
            if short in ('get', 'getenv') and n.args and self.src.resolve(n.args[0]) in self.defaults:
                self.image(n.args[0], n)
            if short == 'slow':
                self.add('developer_selectors', 'FN_RUN_SLOW', n, ['start'], via='slow decorator')
            if short == 'requires':
                for arg in n.args:
                    self.image(arg, n)
            if short in ('slow', 'requires', 'skip', 'skipTest', 'skipUnless', 'skipIf'):
                condition = expr(n)
                if short == 'skipTest':
                    parent = n
                    while parent in self.src.parents:
                        parent = self.src.parents[parent]
                        if isinstance(parent, ast.If):
                            condition = expr(parent.test) + ' -> ' + condition
                            break
                lower = condition.lower()
                cls = ('slow' if short == 'slow' or 'fn_run_slow' in lower else
                       'image' if short == 'requires' or any(s in lower for s in ('executable(', 'image', 'fn_native_host')) else
                       'external-tool' if any(s in lower for s in ('which(', 'openssl', 'curl', 'shutil', 'sbcl', 'tool', 'dtn7', 'inn')) else
                       'platform' if any(s in lower for s in ('platform', 'linux', '/proc', 'posix', 'ipv6', 'darwin', 'os.name')) else
                       'env' if any(s in lower for s in ('environ', 'getenv', 'fn_')) else 'other')
                self.add('skips', condition, n, ['start'], classification=cls)
            if short == 'Node' or short in node_subclasses:
                node_calls.append(n)
                self.add('node_construction', short, n, ['start', 'config'],
                         keywords={k.arg or '**': expr(k.value) for k in n.keywords}, scope=self.src.scope(n))
                for key in ('store.path', 'listener.host', 'listener.port', 'control.path'):
                    if key.startswith('listener.') and self.src.resolve(kwargs.get('listener')) is False:
                        continue
                    if key == 'control.path' and self.src.resolve(kwargs.get('control')) is False:
                        continue
                    self.add('config_keys', key, n, ['config'], via='Node.write_config')
                self.add('argv_shapes', 'IMAGE --fn operator CONFIG run', n, ['start'])
                self.add('argv_shapes', 'bin/fn operator CONFIG run', n, ['start'], via='Node.launch default installed_launcher')
                self.add('argv_shapes', 'IMAGE --fn heap -- operator CONFIG run', n, ['start'], via='installed launcher probe')
                self.add('fixtures', 'packaging/fn', n, ['start'], via='Node.launch -> installed_launcher')
                self.add('fixtures', 'libexec/fn/fn-host.core', n, ['start'], via='installed_launcher')
                self.add('fixtures', '/tank/fn/toolchains/openssl-3.5.8', n, ['start'], via='OPENSSL_SHIPPED; FN_OPENSSL_PREFIX overrides')
                self.add('announcements', 'LISTENING PORT', n, ['observe'], via='Node.start')
                self.add('exit_classes', 'EXIT.OK', n, ['stop', 'observe'], via='Node.init/stop defaults')
                for selector in ('FN_OPENSSL_PREFIX', 'FN_TEST_CONTROL_STACK_KB', 'FN_TEST_CONTROL_STACK_REASON', 'FN_TEST_HEAP_MB', 'SBCL_USER_ARGS', 'FN_NATIVE_TEST_FAULT_BACKTRACE', 'FN_NATIVE_FAULT_BACKTRACE', 'ACL2_CUSTOMIZATION', 'ACL2_SYSTEM_BOOKS', 'FN_HOST'):
                    self.add('developer_selectors', selector, n, ['start'], via='Node.launch/environment (inherited conditional read or sanitization)')
            if short in ('Node', 'write_config', 'config'):
                for key, table in (('extra', 'listener'), ('tls', 'tls')):
                    if key in kwargs:
                        self.config(kwargs[key], n, table=table if key == 'tls' or self.src.resolve(kwargs.get('listener')) is not False else '')
                if 'cold_resources' in kwargs:
                    v = self.src.resolve(kwargs['cold_resources'])
                    if isinstance(v, dict):
                        for key in v:
                            self.add('config_keys', 'resources.' + str(key), n, ['config'])
                    else:
                        self.add('config_keys', 'dynamic', n, ['config'], expression=expr(kwargs['cold_resources']))
                if 'protected_only' in kwargs:
                    self.add('config_keys', 'auth.protected_only', n, ['config'])
            if short == 'which' and n.args and self.src.resolve(n.args[0]) in ('openssl', 'curl', 'inn', 'dtn7', 'dtnd', 'nc'):
                self.wire('external', n)
            if short == 'use_tls':
                for key in ('listener.tls_port', 'listener.tls_cert', 'listener.tls_key', 'auth.protected_only'):
                    self.add('config_keys', key, n, ['config'])
                self.wire('implicit-tls', n)
                self.wire('external', n)
            if short in ('write_text', 'write_bytes') and n.args:
                target = expr(n.func.value)
                value = self.src.resolve(n.args[0])
                if 'config' in target or 'toml' in target or (isinstance(value, str) and '[store]' in value):
                    self.config(n.args[0], n, table='')
            if short in ('operator', 'store', 'invoke') and isinstance(n.func, ast.Attribute):
                self.cli(n.args, n, prefix=short if short != 'invoke' else None)
                if short == 'operator':
                    self.add('control_socket', 'operator-over-control', n, ['control'])
            if short == 'init' and isinstance(n.func, ast.Attribute):
                self.add('cli_verbs', 'operator init', n, ['control'])
                self.wire('operator-cli', n)
            if short in ('start', 'try_start') and isinstance(n.func, ast.Attribute) and name(n.func.value) not in ('thread', 'worker'):
                if 'verb' in kwargs and isinstance(kwargs['verb'], (ast.Tuple, ast.List)):
                    self.cli(kwargs['verb'].elts, n, prefix='operator')
                elif 'node' in fn or fn.startswith('self.'):
                    self.add('cli_verbs', 'operator run', n, ['start'])
                if 'env' in kwargs and self.src.resolve(kwargs['env']) is UNKNOWN:
                    self.add('developer_selectors', 'dynamic', n, ['start'], expression=expr(kwargs['env']))
            if short == 'start_store_owner':
                self.add('cli_verbs', 'owner run', n, ['start', 'control'])
            if short in ('died_at', 'kill_at') or 'death_cut' in kwargs:
                self.add('developer_selectors', short if short in ('died_at', 'kill_at') else 'death_cut', n, ['kill_at'], expression=expr(n))
            if short in ('run', 'Popen', 'start', 'start_filed', 'check_output', 'check_call', 'argv', 'invoke'):
                for arg in n.args:
                    if isinstance(arg, (ast.List, ast.Tuple)):
                        items = arg.elts
                        values = [self.src.resolve(v) for v in items]
                        if '--fn' in values:
                            self.cli(items[values.index('--fn') + 1:], n)
                            self.add('argv_shapes', 'IMAGE --fn WORDS...', n, ['start'])
                        elif short == 'argv':
                            self.cli(items, n)
                        elif values and isinstance(values[0], str) and Path(values[0]).name in ('openssl', 'curl', 'inn', 'dtn7', 'dtnd', 'dtnsend', 'nc'):
                            self.wire('external', n)
            if short in ('Acl2Session', 'runtime_sbcl') or short.startswith('acl2_'):
                self.add('helpers', 'in-image probe: ' + short, n, ['observe'])
            if short in ('Client', 'session') or fn.endswith(('socket.create_connection', 'nntplib.NNTP')):
                self.wire('implicit-tls' if 'implicit_tls' in kwargs else 'nntp-plain', n)
            if short == 'starttls' or (short in ('command', 'send') and any('STARTTLS' in v for a in n.args for v in constants(a))):
                self.wire('starttls', n)
            if short in ('HTTPConnection', 'HTTPSConnection', 'urlopen', 'observe_http_reply', 'observe_web_reply'):
                self.wire('web-http', n)
            if short in ('control_exchange', 'old_client_exchange', 'observe_control_reply') or fn.endswith('socket.AF_UNIX'):
                self.add('control_socket', short, n, ['control'])
                self.wire('control-fnct', n)
            if short in ('consumer', 'consumer_request', 'consumer_exchange', 'bound_request'):
                self.add('control_socket', expr(n), n, ['control'])
                self.wire('consumer', n)
            if short in ('AcceptThenClosePeer', 'FakePeer', 'ScriptedPeer', 'Peer') or 'fake_peer' in short:
                self.wire('peering', n)
            if short in ('bp_request', 'tcpcl', 'bundle') or 'tcpcl' in short:
                self.wire('bp/tcpcl', n)
            if short == 'table_reply':
                self.add('fixtures', 'books/protocol-table.lisp', n, ['observe'], via='table_reply')
            if short == 'fund_peer_flights':
                self.wire('store-files', n)
                self.wire('peering', n)
            if short == 'decided_launch':
                self.add('cli_verbs', 'heap --', n, ['start'])
                self.add('argv_shapes', 'IMAGE --fn heap -- operator CONFIG run', n, ['start'])
                self.add('developer_selectors', 'SBCL_USER_ARGS', n, ['start'])
        if any(r['value'] == 'tests.native_harness.EXIT' or r['value'].startswith('tests.native_harness.') for r in self.data['helpers'].values()):
            line = min(r['sites'][0] for r in self.data['helpers'].values() if r['value'].startswith('tests.native_harness.'))
            self.add('fixtures', 'books/outcome-class.lisp', line, ['observe'], via='native_harness import -> tools.outcome_codes')
            self.add('fixtures', 'host/native/io.lisp', line, ['start'], via='environment -> developer_selectors')
        return {k: sorted(v.values(), key=lambda r: (str(r['value']), r['sites'], json.dumps(r, sort_keys=True))) for k, v in self.data.items()}

# Reader review9: filesystem identity, extent identity, operator CLI.

# H1a reader review: reader/poster and OVER modules (review0).

# Human review: TLS, authorship/accounts, and peering (review3).

# H1a review7: complete source review; internal-only includes explicitly noted static source checks.

# Read in full: operator_verbs reviewer, H1a.

# Read in full: slow_disk, state_checkpoint, recovery (H1a representation review).

# Read-through judgments: compaction, lineage, PageIO and installation.

# H1 source review: owner, owner_scheduler, outcome_algebra (full modules read).

# Reader review4: twelve whole-source reviews; indirect history helpers inspected.

# Read in full: admin/live_reconfiguration reviewer, H1a.

# Expand repeated meaningful representation assertions/manipulations.

# Reviewed in full: image_differential, harness, agent_wait.

# Human source review: installed startup, profiles, capacity and depth (review6).

# Human review: protected peering, consumer/control, journals, reclaim and cost.


def import_edges(src, nodes):
    """Follow used project symbols, including qualified aliases and borrowed methods."""
    edges = set()
    for n in nodes:
        if not isinstance(n, ast.Name) or not isinstance(n.ctx, ast.Load) or n.id not in src.imports:
            continue
        module, symbol, line = src.imports[n.id]
        if module == 'tests.native_harness' or not module.startswith(('tests', 'tools')):
            continue
        suffix = []
        parent = src.parents.get(n)
        while isinstance(parent, ast.Attribute):
            suffix.append(parent.attr)
            parent = src.parents.get(parent)
        candidate = module.replace('.', '/') + '.py'
        submodule = module + '.' + symbol
        if (ROOT / (submodule.replace('.', '/') + '.py')).is_file():
            candidate = submodule.replace('.', '/') + '.py'
            symbol = suffix.pop(0) if suffix else '*'
        elif symbol == '*' and suffix:
            symbol = suffix.pop(0)
        # Borrowed fixture methods: C.setUp does not execute all C's tests.
        if suffix and (ROOT / candidate).is_file():
            dep = source(candidate)
            if any(isinstance(d, ast.ClassDef) for d in dep.defs.get(symbol, [])):
                symbol += '.' + suffix[0]
        if candidate == 'tests/native_harness.py':
            continue
        if (ROOT / candidate).is_file():
            edges.add((candidate, symbol, line))
    return sorted(edges)


def select_roots(src, symbol, demanded=()):
    cls, _, method = symbol.partition('.')
    definitions = [c for c in src.defs.get(cls, []) if isinstance(c, ast.ClassDef)]
    if not definitions:
        return src.selected(symbol)
    selected = []
    for c in definitions:
        # Class metadata and bases are reachable, but unrelated helper methods are not.
        selected.extend(c.bases)
        selected.extend(c.decorator_list)
        methods = {n.name: n for n in c.body if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef))}
        aliases = {t.id: n for n in c.body if isinstance(n, ast.Assign) for t in n.targets if isinstance(t, ast.Name)}
        pending = [method] if method else [k for k in methods if k.startswith('test') or k in ('setUp', 'setUpClass', 'tearDown', 'tearDownClass', '__init__')]
        pending += list(demanded)
        visited = set()
        while pending:
            key = pending.pop()
            if key in visited:
                continue
            visited.add(key)
            root = methods.get(key) or aliases.get(key)
            if root is None:
                continue
            selected.append(root)
            for n in ast.walk(root):
                if isinstance(n, ast.Attribute) and name(n.value) in ('self', 'cls'):
                    pending.append(n.attr)
                if isinstance(n, ast.Name) and isinstance(n.ctx, ast.Load):
                    selected.extend(src.selected(n.id))
        # Image/profile attributes supply setup even when referenced as self.image.
        selected.extend(n for n in c.body if isinstance(n, (ast.Assign, ast.AnnAssign)) and not isinstance(getattr(n, 'value', None), ast.Attribute))
    return selected


def dependencies(src):
    direct = Extractor(src).run()
    for entries in direct.values():
        for entry in entries:
            entry['source'] = src.path
    demanded = {n.attr for n in ast.walk(src.tree) if isinstance(n, ast.Attribute) and name(n.value) in ('self', 'cls')}
    pending = [(path, symbol, [{'source': src.path, 'sites': [line]}])
               for path, symbol, line in import_edges(src, ast.walk(src.tree))]
    seen = set()
    inherited = []
    while pending:
        path, symbol, via = pending.pop(0)
        if (path, symbol) in seen or path == src.path:
            continue
        seen.add((path, symbol))
        dep = source(path)
        selected = select_roots(dep, symbol, demanded)
        demanded.update(n.attr for root in selected for n in ast.walk(root) if isinstance(n, ast.Attribute) and name(n.value) in ('self', 'cls'))
        if not selected:
            # Re-exported names still have a statically identifiable import edge.
            if symbol in dep.imports:
                mod, sym, line = dep.imports[symbol]
                target = mod.replace('.', '/') + '.py'
                if mod != 'tests.native_harness' and (ROOT / target).is_file():
                    pending.append((target, sym, via + [{'source': path, 'sites': [line]}]))
            continue
        extracted = Extractor(dep, selected).run()
        inherited.append({'source': path, 'symbol': symbol, 'via': via})
        for field, entries in extracted.items():
            for entry in entries:
                entry['source'] = path
                entry['via'] = via
                direct[field].append(entry)
        nodes = {n for root in selected for n in ast.walk(root)}
        for target, sym, line in import_edges(dep, nodes):
            pending.append((target, sym, via + [{'source': path, 'sites': [line]}]))
    # Same helper reached by several names: combine identical source entries.
    for field, entries in direct.items():
        unique = {}
        for entry in entries:
            key = json.dumps({k: v for k, v in entry.items() if k not in ('sites', 'via')}, sort_keys=True)
            if key in unique:
                unique[key]['sites'] = sorted(set(unique[key]['sites'] + entry['sites']))
            else:
                unique[key] = entry
        direct[field] = sorted(unique.values(), key=lambda r: (r['value'], r['source'], r['sites']))
    return direct, sorted(inherited, key=lambda r: (r['source'], r['symbol']))


def locate_class(src, expression):
    parts = expression.split('.')
    if parts[0] in src.imports:
        module, symbol, _ = src.imports[parts[0]]
        sub = module + '.' + symbol
        if (ROOT / (sub.replace('.', '/') + '.py')).is_file():
            module, symbol = sub, parts[1] if len(parts) > 1 else ''
        elif symbol == '*':
            symbol = parts[1] if len(parts) > 1 else ''
        path = module.replace('.', '/') + '.py'
        if (ROOT / path).is_file():
            dep = source(path)
            return dep, next((n for n in dep.defs.get(symbol, []) if isinstance(n, ast.ClassDef)), None)
    return src, next((n for n in src.defs.get(parts[0], []) if isinstance(n, ast.ClassDef)), None)


def class_methods(src, cls, seen=()):
    identity = (src.path, cls.name)
    if identity in seen:
        return False, {}
    concrete, methods = False, {}
    for base in cls.bases:
        bname = name(base)
        if bname in ('unittest.TestCase', 'TestCase', 'unittest.IsolatedAsyncioTestCase'):
            concrete = True
            continue
        dep, parent = locate_class(src, bname)
        if parent is not None:
            is_case, inherited = class_methods(dep, parent, (*seen, identity))
            concrete |= is_case
            for key, value in inherited.items():
                methods.setdefault(key, value)
    for n in cls.body:
        if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef)) and n.name.startswith('test'):
            methods[n.name] = {'source': src.path, 'line': n.lineno, 'defined_in': cls.name}
    return concrete, methods


def test_classes(src):
    result = []
    for cls in src.tree.body:
        if isinstance(cls, ast.ClassDef):
            concrete, methods = class_methods(src, cls)
            if concrete:
                result.append({'value': cls.name, 'sites': [cls.lineno], 'bases': [expr(b) for b in cls.bases],
                               'test_methods': [{'value': k, **v} for k, v in sorted(methods.items())]})
    return result


def multi_node(src):
    factories = {'Node'}
    for n in ast.walk(src.tree):
        if isinstance(n, ast.ClassDef) and any(name(b).endswith('Node') for b in n.bases):
            factories.add(n.name)
        if isinstance(n, ast.FunctionDef) and any(isinstance(c, ast.Call) and name(c.func).rsplit('.', 1)[-1] == 'Node' for c in ast.walk(n)):
            factories.add(n.name)
    scopes = {}
    for n in ast.walk(src.tree):
        if isinstance(n, ast.Call) and name(n.func).rsplit('.', 1)[-1] in factories:
            scope = src.scope(n)
            if scope.rsplit('.', 1)[-1] in factories and scope.rsplit('.', 1)[-1] != 'Node':
                continue
            entry = scopes.setdefault(scope, {'scope': scope, 'sites': [], 'minimum_static_constructions': 0, 'dynamic_multiplicity': False})
            multiplicity = 1
            parent = n
            while parent in src.parents:
                parent = src.parents[parent]
                if isinstance(parent, (ast.GeneratorExp, ast.ListComp, ast.SetComp)):
                    for gen in parent.generators:
                        values = src.resolve(gen.iter)
                        if isinstance(values, list):
                            multiplicity *= len(values)
                        else:
                            entry['dynamic_multiplicity'] = True
                if isinstance(parent, (ast.For, ast.While)):
                    entry['dynamic_multiplicity'] = True
                if isinstance(parent, ast.FunctionDef):
                    break
            entry['sites'].append(n.lineno)
            entry['minimum_static_constructions'] += multiplicity
    evidence = sorted(scopes.values(), key=lambda e: e['scope'])
    return {'value': any(e['minimum_static_constructions'] > 1 for e in evidence),
            'dynamic': any(e['dynamic_multiplicity'] for e in evidence), 'evidence': evidence,
            'basis': 'Node/subclass/factory calls per scope; loops remain explicit. Multiple nodes can be storage fixtures; peering is reported separately.'}


def build_inventory():
    _SOURCES.clear()
    judgments = load_judgments()
    release_rows = rows()
    modules = []
    for group, names in QUARRY.items():
        for module in names:
            path = 'tests/test_native_' + module + '.py'
            src = source(path)
            deps, inherited = dependencies(src)
            judgment = judgments[module]
            record = {'module': module, 'quarry_class': group, 'path': path,
                      'lines': len(src.lines), 'test_methods': sum(len(c['test_methods']) for c in test_classes(src)),
                      'declared_test_methods': sum(isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef)) and n.name.startswith('test') for n in ast.walk(src.tree)),
                      'unittest_classes': test_classes(src), **deps,
                      'inherited_dependencies': inherited,
                      'representation_sites': judgment['representation_sites'],
                      'module_verdict': judgment['module_verdict'],
                      'judgment': {k: v for k, v in judgment.items() if k not in ('module_verdict', 'representation_sites')},
                      'section1_rows': witnessed(module, release_rows)}
            ops = set(judgment['adapter_operations'])
            for field in deps.values():
                for dependency in field:
                    ops.update(dependency['operations'])
            record['adapter_operations'] = [op for op in OPERATIONS if op in ops]
            record['multi_node'] = multi_node(src)
            fixture_nodes = [r for r in record['node_construction'] if r.get('scope', '').endswith(('.setUp', '.setUpClass'))]
            test_nodes = [r for r in record['node_construction'] if '.test' in r.get('scope', '')]
            if fixture_nodes and test_nodes:
                record['multi_node']['value'] = True
                record['multi_node']['fixture_plus_test_sites'] = [{'source': r['source'], 'sites': r['sites']} for r in fixture_nodes + test_nodes]
            for site in record['representation_sites']:
                site.setdefault('operations', ['observe'])
            modules.append(record)
    modules.sort(key=lambda m: m['module'])
    aggregate = {}
    def count(field, getter=lambda r: r['value']):
        result = {}
        for module in modules:
            values = {getter(r) for r in module[field]}
            for value in values:
                result.setdefault(value, []).append(module['module'])
        return [{'value': key, 'modules': len(value), 'module_names': value}
                for key, value in sorted(result.items(), key=lambda kv: (-len(kv[1]), str(kv[0])))]
    aggregate['module_verdict'] = [{'value': value, 'modules': sum(m['module_verdict'] == value for m in modules)}
                                   for value in ('carry-unchanged', 'carry-with-adapter', 'carry-socket-half', 'rewrite-row')]
    for field in ('wires', 'config_keys', 'cli_verbs', 'developer_selectors', 'exit_classes', 'argv_shapes', 'announcements'):
        aggregate[field] = count(field)
    aggregate['images'] = count('images', lambda r: r['image'])
    aggregate['skip_classes'] = count('skips', lambda r: r['classification'])
    aggregate['adapter_operations'] = [{'value': op, 'modules': sum(op in m['adapter_operations'] for m in modules)} for op in OPERATIONS]
    drop_rows = {r['row'] for r in release_rows if not r['carried']}
    aggregate['only_not_carried_rows'] = [m['module'] for m in modules if m['section1_rows'] != ['unclaimed'] and set(m['section1_rows']) <= drop_rows]
    aggregate['unclaimed'] = [m['module'] for m in modules if m['section1_rows'] == ['unclaimed']]
    requirements = []
    for field in ('argv_shapes', 'announcements', 'exit_classes', 'config_keys', 'cli_verbs', 'developer_selectors'):
        for entry in aggregate[field]:
            requirements.append({'kind': field, **entry})
    requirements.sort(key=lambda e: (-e['modules'], e['kind'], e['value']))
    aggregate['host_requirements'] = requirements
    return {'schema_version': 1, 'subject': {'node': len(QUARRY['node']), 'node_internal': len(QUARRY['node_internal']), 'total': len(modules)},
            'input_provenance': {'quarry': 'build/h1-input/quarry_lists.json (frozen QUARRY literal)',
                                 'release_plan': 'build/coordinator/fn2/RELEASE-PLAN.md section 1 (frozen RELEASE_SECTION_1 literal, 2026-10-28)',
                                 'native_tree': 'fn1 origin/dev 6521f18c4'},
            'site_convention': 'Dependency sites belong to source, not necessarily module.path; via records the import chain. Judgment lines belong to module.path unless touches/reason identifies an indirect helper.',
            'analysis_limits': ['Static source inventory; no native execution or image availability checks.',
                                'Dynamic expressions are retained explicitly; only literal/config constant text is resolved.',
                                'Imported symbols and borrowed fixture methods are followed without executing imports; dynamic dispatch remains a reader-review responsibility.',
                                'test_methods statically expands unittest inheritance; declared_test_methods counts definitions including mixins. No unittest collection or module import is executed.',
                                'Host requirements are dependency counts, not claims that implementing any one item alone makes a module pass. Obsolete selectors/verbs remain inventoried pending the named row replacements.'],
            'image_defaults': image_defaults(), 'section1_table': release_rows, 'aggregates': aggregate, 'modules': modules}


def markdown(data):
    def cell(value):
        return str(value).replace('|', '&#124;').replace('\n', ' ')
    out = [MARKER.rstrip(), '', 'Generated by `python3 fn2/tests/harness/inventory.py --markdown`. Counts are modules, not executed tests.', '',
           '| Quarry class | Modules |', '|---|---:|', '| node | 87 |', '| node+internal | 33 |', '',
           '| Module | Class | Lines | Test methods | Verdict | Wires | Adapter operations |', '|---|---|---:|---:|---|---|---|']
    for m in data['modules']:
        out.append('| ' + ' | '.join(map(cell, [m['module'], m['quarry_class'], m['lines'], m['test_methods'], m['module_verdict'], ', '.join(sorted({r['value'] for r in m['wires']})), ', '.join(m['adapter_operations'])])) + ' |')
    for key, title in (('module_verdict', 'Carry judgments'), ('wires', 'Driven surfaces'), ('images', 'Image kinds'), ('skip_classes', 'Skip classes'), ('adapter_operations', 'Adapter operations'), ('config_keys', 'Config keys'), ('cli_verbs', 'CLI verb paths'), ('developer_selectors', 'Environment and cut selectors'), ('exit_classes', 'Exit classes')):
        out += ['', '### ' + title, '', '| Dependency | Modules |', '|---|---:|']
        out += ['| ' + cell(r['value']) + ' | ' + str(r['modules']) + ' |' for r in data['aggregates'][key]]
    out += ['', '### What layer D and the host must serve', '',
            'Ordered by modules depending on each item. Entries describe fn1 inputs: representation-specific selectors and removed verbs require the replacements in the judgment table, not blind implementation. The launcher also needs `packaging/fn`, the core-image layout, the heap probe and the shipped OpenSSL prefix (overridable by `FN_OPENSSL_PREFIX`). The adapter must redirect the outcome table and protocol-reply table dependencies.', '',
            '| Kind | Requirement | Modules |', '|---|---|---:|']
    out += ['| ' + cell(r['kind']) + ' | ' + cell(r['value']) + ' | ' + str(r['modules']) + ' |' for r in data['aggregates']['host_requirements']]
    out += ['', '### Row coverage', '', 'Only not-carried rows: ' + (', '.join(data['aggregates']['only_not_carried_rows']) or '(none)') + '.', '',
            'Unclaimed modules: ' + (', '.join(data['aggregates']['unclaimed']) or '(none)') + '.', '',
            '| Module | Mechanically witnessed section 1 rows |', '|---|---|']
    out += ['| ' + m['module'] + ' | ' + cell('; '.join(m['section1_rows'])) + ' |' for m in data['modules']]
    out += ['', '### Reviewed representation boundaries', '',
            'Each line below is a reviewed source site, including public observables easily mistaken for implementation details. The JSON carries the full method partition and cited module judgment. Line numbers refer to `tests/test_native_MODULE.py`; indirect helper locations are named in the description.', '',
            '| Module:line | Touches | Verdict | Public row or retirement | Replacement / rationale |', '|---|---|---|---|---|']
    for m in data['modules']:
        for r in sorted(m['representation_sites'], key=lambda r: r['line']):
            out.append('| ' + ' | '.join(map(cell, [m['module'] + ':' + str(r['line']), r['touches'], r['verdict'], r['row'], r['reason']])) + ' |')
    out += ['', '### Module decisions and remaining judgment uncertainty', '', '| Module | Decision | Reason | Uncertainty |', '|---|---|---|---|']
    for m in data['modules']:
        out.append('| ' + ' | '.join(map(cell, [m['module'], m['module_verdict'], m['judgment']['reason'], m['judgment'].get('uncertainty') or 'none'])) + ' |')
    return '\n'.join(out) + '\n'


def check(data):
    assert data['subject'] == {'node': 87, 'node_internal': 33, 'total': 120}, data['subject']
    expected = set(QUARRY['node'] + QUARRY['node_internal'])
    assert set(load_judgments()) == expected, 'Judgment subject differs from quarry'
    assert len(expected) == 120
    input_path = ROOT / 'build/h1-input/quarry_lists.json'
    if input_path.exists():
        assert json.loads(input_path.read_text()) == QUARRY, 'Frozen quarry input drift'
    public_rows = {r['row'] for r in data['section1_table']}
    allowed = {'carry-unchanged', 'carry-with-adapter', 'carry-socket-half', 'rewrite-row'}
    for m in data['modules']:
        assert m['module_verdict'] in allowed, m['module']
        assert m['judgment']['sites'], m['module'] + ' has no cited judgment'
        for field in FIELDS:
            assert isinstance(m[field], list), (m['module'], field)
            for entry in m[field]:
                assert 'value' in entry and entry['sites'] and entry['operations'], (m['module'], field, entry)
                assert set(entry['operations']) <= set(OPERATIONS)
                assert all(1 <= n <= len(source(entry['source']).lines) for n in entry['sites']), entry
        for r in m['representation_sites']:
            assert r['verdict'] in ('public-contract', 'obsolete-representation'), (m['module'], r)
            assert r['row'] and r['reason'] and r['touches'], (m['module'], r)
            assert r['row'] in public_rows or r['row'].startswith('none: retire, capability = '), (m['module'], r['row'])
            assert 1 <= r['line'] <= m['lines'], (m['module'], r)
    for m in data['modules']:
        if m['quarry_class'] == 'node_internal':
            src = source(m['path'])
            declared = {c.name + '.' + n.name for c in src.tree.body if isinstance(c, ast.ClassDef) for n in c.body if isinstance(n, ast.FunctionDef) and n.name.startswith('test')}
            partition = set(sum((m['judgment'].get(k, []) for k in ('socket_only_tests', 'in_image_tests', 'mixed_tests', 'internal_only_tests')), []))
            assert declared <= partition, (m['module'], 'unclassified methods', sorted(declared - partition))
    print('CHECK OK: 120 modules (87 node, 33 node_internal); all fields, judgments and sites verified')
    for key in ('module_verdict', 'wires', 'images', 'skip_classes', 'adapter_operations'):
        print(key + ': ' + ', '.join(str(e['value']) + '=' + str(e['modules']) for e in data['aggregates'][key]))
    print('representation_sites: ' + str(sum(len(m['representation_sites']) for m in data['modules'])))
    print('only_not_carried_rows: ' + ', '.join(data['aggregates']['only_not_carried_rows']))
    print('unclaimed: ' + ', '.join(data['aggregates']['unclaimed']))


def validate_judgment(value, schema, location='judgment'):
    """Validate the type/required/properties/items/enum subset used by our schema.

    This is deliberately not a general JSON Schema implementation. The checked-in
    draft 2020-12 schema uses only these validation keywords.
    """
    types = {'object': dict, 'array': list, 'string': str, 'integer': int,
             'null': type(None)}
    expected = schema['type']
    expected = expected if isinstance(expected, list) else [expected]
    if type(value) not in tuple(types[k] for k in expected):
        raise ValueError(f'{location}: expected {expected}, got {type(value).__name__}')
    if 'enum' in schema and value not in schema['enum']:
        raise ValueError(f'{location}: invalid value {value!r}; expected {schema["enum"]}')
    if isinstance(value, dict):
        missing = set(schema.get('required', ())) - value.keys()
        if missing:
            raise ValueError(f'{location}: missing required keys {sorted(missing)}')
        properties = schema.get('properties', {})
        extra = value.keys() - properties.keys()
        if schema.get('additionalProperties') is False and extra:
            raise ValueError(f'{location}: unexpected keys {sorted(extra)}')
        for key in value.keys() & properties.keys():
            validate_judgment(value[key], properties[key], f'{location}.{key}')
    elif isinstance(value, list):
        for index, item in enumerate(value):
            validate_judgment(item, schema['items'], f'{location}[{index}]')


def load_judgments():
    schema = json.loads((JUDGMENTS_DIR / 'judgments.schema.json').read_text())
    records = {}
    for path in sorted(JUDGMENTS_DIR.glob('*.json')):
        if path.name == 'judgments.schema.json':
            continue
        record = json.loads(path.read_text())
        validate_judgment(record, schema, str(path))
        module = record.pop('module')
        if module != path.stem:
            raise ValueError(f'{path}: module {module!r} does not match filename')
        records[module] = record
    expected = set(QUARRY['node'] + QUARRY['node_internal'])
    if records.keys() != expected:
        raise ValueError(f'Judgment modules differ from quarry: '
                         f'missing={sorted(expected - records.keys())}, '
                         f'extra={sorted(records.keys() - expected)}')
    return records


def _digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _data_inputs():
    paths = {Path(__file__).resolve(), *JUDGMENTS_DIR.glob('*.json')}
    quarry = ROOT / 'build/h1-input/quarry_lists.json'
    if quarry.exists():
        paths.add(quarry)
    return {str(path.relative_to(ROOT)) for path in paths}


def _stale(out):
    """A manifest is a build cache, never an authoritative inventory input."""
    try:
        manifest = json.loads((out / 'inputs.json').read_text())
        if manifest['schema_version'] != 1 or set(manifest['data_inputs']) != _data_inputs():
            return True
        outputs = [out / name for name in ('natives-inventory.json', 'natives.md')]
        built_at = min(path.stat().st_mtime_ns for path in outputs)
        for relative, digest in manifest['inputs'].items():
            path = ROOT / relative
            if path.stat().st_mtime_ns > built_at or _digest(path) != digest:
                return True
        return any(_digest(path) != manifest['outputs'][path.name] for path in outputs)
    except (OSError, ValueError, KeyError, TypeError):
        return True


def _atomic_write(path, text):
    # Every reader holds the same lock; replace also protects external readers
    # from a partially written JSON file if generation is interrupted.
    with tempfile.NamedTemporaryFile(mode='w', encoding='utf-8', dir=path.parent,
                                     prefix='.' + path.name + '.', delete=False) as stream:
        temporary = Path(stream.name)
        try:
            stream.write(text)
            stream.close()
            os.replace(temporary, path)
        finally:
            temporary.unlink(missing_ok=True)


def _generate(out):
    data = build_inventory()
    payloads = {'natives-inventory.json': json.dumps(data, indent=2, ensure_ascii=False,
                                                   sort_keys=True) + '\n',
                'natives.md': MARKDOWN_HEAD + markdown(data)}
    inputs = sorted(_data_inputs() | set(_SOURCES))
    manifest = {'schema_version': 1, 'data_inputs': sorted(_data_inputs()),
                'inputs': {path: _digest(ROOT / path) for path in inputs},
                'outputs': {name: hashlib.sha256(value.encode('utf-8')).hexdigest()
                            for name, value in payloads.items()}}
    for name, value in payloads.items():
        _atomic_write(out / name, value)
    _atomic_write(out / 'inputs.json', json.dumps(manifest, indent=2, sort_keys=True) + '\n')
    return data


def load(out=None, *, regenerate=False):
    """Return the inventory, generating absent/stale build outputs under a lock.

    Judgment/schema/extractor changes and every source read by the AST extractor
    are tracked by both modification time and content digest. No committed
    generated inventory is read. ``out`` is a directory, defaulting to build/natives.
    """
    out = Path(out) if out is not None else DEFAULT_OUT
    out.mkdir(parents=True, exist_ok=True)
    with (out / '.inventory.lock').open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        if regenerate or _stale(out):
            return _generate(out)
        return json.loads((out / 'natives-inventory.json').read_text())


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', type=Path, default=DEFAULT_OUT,
                        help='generated inventory directory (default: build/natives)')
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--json', action='store_true', help='also print the JSON inventory')
    mode.add_argument('--markdown', action='store_true', help='also print the generated Markdown section')
    mode.add_argument('--check', action='store_true', help='validate extracted fields and source sites')
    args = parser.parse_args()
    data = load(args.out, regenerate=True)
    if args.json:
        print(json.dumps(data, indent=2, ensure_ascii=False, sort_keys=True))
    elif args.markdown:
        print(markdown(data), end='')
    elif args.check:
        check(data)
    else:
        print(f'Wrote {args.out / "natives-inventory.json"} and {args.out / "natives.md"}')


if __name__ == '__main__':
    main()
