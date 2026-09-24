# v0 scoreboard

One row per property of [plan §2.1](plan-2026-09-22-trajectory.md). A row is
DONE when the theorem is over the function the host calls, its teeth book has
a reachable witness and one must-fail per hypothesis, and the property was
observed on the deployed image; otherwise the row names its obstruction. Lanes
update their cells when they land; the audit records
(`planning/v0-audit-*.md`) carry the evidence behind each cell.

| P | theorem | host-called subject | teeth | observed on image | obstruction |
| --- | --- | --- | --- | --- | --- |
| P1 protected channel | not re-verified | | | | |
| P2 240 after consumed completion | not re-verified | | | | |
| P3 reading resumes | not re-verified | | | | |
| P4 one owner decides duplicate vs conflict | not re-verified | | | | |
| P5 a fault costs one connection | not re-verified | | | | |
| P6 live reconfiguration | not re-verified | | | | |
| P7 two nodes exchange both ways | K2 in/out, K3, K5 (port form `fn-feed-port-replay-is-live-modulo-inflight`), PRF-058 octets exist; MISSING loop freedom over the host's filtered `fn-own-submission-targets` and the Path-tail clause | inbound, octets, K5, TLS over host-called functions; outbound loop over a filtered callee; `fn-own-feed-accept` uncalled | PRF-058/047/051/K5 have teeth; PRF-042 loop and history theorems 0 must-fail | 1a9dd747 join: TLS+AUTHINFO feed both ways (indirect), kill -9 then exactly one copy; loop, TLS-negative and octet-diff rows not run | none named; [audit](v0-audit-p7-p9.md) |
| P8 signature verdict visible | PRF-048 injectivity and indexedp exist; MISSING a keystone that finishing a kind-4 event records its verdict, and HDR over `fn-own-step` (PRF-026 has 0 events; the stx-reader theorem restates a definition) | HDR theorem is over the inner `fn-nntp-verdict-hdr-msgid`, not the host-called step | 0 must-fail in nntp-verdict, owner-verdict, stx-reader tests | `HDR :fn-verified` answered `0 verified keyring 1` at B on 1a9dd747 and survived restart; verification only through fn's own binary | no non-fn verifier and no signing client; a signed article POSTed over NNTP gets no durable verdict; library trust not a named assumption; `fn-sig-verify` unattached (ember) |
| P9 keep until release, refuse unaffordable | PRF-004: `fn-spc-prepare-refuses-unaffordable-obligation` (charge over the room the capacity leaves: the store state is returned unchanged), `fn-node-prepare-refuses-unaffordable-obligation`, `fn-node-prepare-refuses-whatever-retain-admit-refuses` (the equation that carries `fn-retain-admit-refuses-unaffordable-obligation` to the called function), `fn-sn-finish-keeps-accepted-articles`, `fn-sn-finish-releases-an-obligation-only-by-its-matching-release` (corollary: no arm releases an `:archive` pin) | `fn-spc-prepare` at store-node-host.lisp:472 (`:refused` at :475, native `fnn-bridge-prepare` io.lisp:810); `fn-sn-finish` at store-node-host.lisp:546 | `tests/acl2/store-node-retention-tests`: reachable store (capacity 10, 2 reserved) refuses charge 9 and stages 8; article, undertaking and release arms keep the article and archive pin; 8 must-fail, one per hypothesis; identity/consumer/topic arms unwitnessed. Certified persvati `certify-20260924T144414Z-1366014` (book 2.4 s, tests 2.5 s), `certify-20260924T144502Z-1374723` (retention-tests 0.5 s) | `V0-CAP-REFUSE` refused on 915 only; not run on bc9be7ec or 1a9dd747 | not observed on an image; charges are abstract units (physical bytes open); no archive-release event in v0, so articles are kept outright |
| P10 every cut is a model crash point | not re-verified | | | | |
| P11 bundles across an outage | not re-verified | | | | |

Image under test: `1a9dd747` ([record](evidence/native-cut-1a9dd747-2026-09-24.md)).
Deployed node: `da5fd8cb`.
