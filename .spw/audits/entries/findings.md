# Entry findings

## E001 — password send may publish before its local return

Source base3f39e6df98b3d87881e43200bba9334e47e1af4b; `host/native/io.lisp`, `fnn-command-redeem`, `:send-password` arm. Logical neighbor: `books/peer-host.lisp`, `fn-redeem-lost`, `fn-redeem-step`, `fn-redeem-outcome-class`.

Host sent password before advancing to `:password`. A physical send exception after partial/full write therefore called the correct logical loss classifier with wrong stage`:code`, reporting unreachable/nothing redeemed. Server durable creation was already possible. Fix advances stage before send, conservatively classifying any send loss uncertain. Both raw and TLS send routes share this transition.

Actual-source fixture observes seven outcomes; pre-fix source fails with `(:unreachable :code)` on password send; fixed source passes uncertain. Tests: `python3 -m unittest tests.test_native_redeem_send_boundary`; `python3 tools/host_check.py --read host/native/io.lisp`; whitespace pass. Archived evidence `planning/evidence/horse-entries-redeem-send.json`. No saved image/TLS/disk/universal theorem claim. Patch commit recorded in lane handoff. Bounds horse independently repairs bounded input/wire synthesis; cross-axis [bounds](../bounds/).

## E002 — mounted initialization adds a commit authorization gate

Workbench651b535b5171: `packages/spw-cli/src/init.ts`, `ensureHook`. Actual init writes `.git/hooks/pre-commit` and `.agents/workflows/commit-review.md` beyond consumer canon; mounted commit skill imposes human authorization on every commit, conflicting with fn's authorized commits. Removed our standalone generated hook and own generated workflow, preserved exact local receipts; no upstream edits. Consumer README explicitly keeps instruments optional and fn authority governing. Useful doctor/root/tree/selector machinery remains available.


## E003 — entry documentation points at retired Python launcher

The selected-runtime paragraph in specs/host.md named repositorybin/fn as Python owner; actual repository entry is packaging/fn, native shell launcher with installed release selection and separate checkout override. Corrected source documentation; launcher behavior unchanged.

## Refuted lead — consumer CRLF credential width

Initial suspicion assumed497-byte consumer password, making498 file cap too small forCRLF. Reading complete fn-ncl-secretp and constant shows496-byte consumer grammar;498 covers496+CRLF. Bounds horse instead found redeem permitted497 though AUTHINFO and consumer require496, and owns common credential representability repair. No consumer-file cap change justified.

## E004 — TLS client caller error queue precondition

`host/native/tls.lisp`, `fnn-tls-client-step`: SSL_connect was called without clearing current thread error queue, unlike sibling accept/read/write entries. [OpenSSL caller contract](https://docs.openssl.org/3.0/man3/SSL_get_error/) requires it empty before the I/O operation. Added explicit clear; commit b026608c0.

Real library fixture leaves a genuine unrelated CA-load error after channel creation, observes queue emptiness immediately at SSL_connect boundary, then executes actual nonblocking TCP/TLS handshake and encrypted roundtrip. Old source fails boundary observer; changed source passes0.176s. **Backend caveat:** current OpenSSL3.6 actually completes old handshake without observer; no current-runtime handshake outage reproduced. This is portable caller-contract repair, not a claim about backend TLS correctness. Archived evidence `planning/evidence/horse-entries-tls-client-queue.json`; no image qualification claimed.

## Cross-axis redeemed input composition

[Bounds](../bounds/) owns ea86cf888, ACL2 command synthesis and password/reply admission. Actual composed command (Bounds body plus E001 pre-send password stage) passes all seven injected success/refusal/loss cases. Fixture command projection is supplied at the admitted-byte seam; Bounds tests own grammar validation. Archived evidence `planning/evidence/horse-entries-redeem-composed.json`.

## Refuted lead — OpenSSL IPv4 name checking

SSL_set1_host initially looked DNS-only from older documentation wording. [OpenSSL3.0 source](https://raw.githubusercontent.com/openssl/openssl/openssl-3.0.0/ssl/ssl_lib.c) explicitly first attempts X509_VERIFY_PARAM_set1_ip_asc before DNS hostname setup. No IPv4 verification patch justified on that backend; LibreSSL realization remains separate evidence.

E005 BP receipt acquisition: fnn-bpapp-open-journal acquired a journal locally, then could escape configuration/initialization before callers retained its handle. Fixed local returned marker with shared fnn-unwind-cleanups;8 actual adapter paths pass and original config-fault leaves0closes instead of1. Macro source dependency Exits1200bf85d. BP node/application callers share repair; Exits owns sticky close debt and downstream cleanup. Evidence planning/evidence/horse-entries-bpapp-acquisition.json.

E006 list seal residency: fnn-seal-octets called fn-arena-seal-list, storing payload permanently in resident INNER and omitting stagedhandle. fn-arena$x-release frees stage only, so simply settinghandle would not fix retained INNERbytes. Both actual consumers (bridgeprepare, identitycommit) now reuse existing bufferstage, capturing ACL2presealcount. Hostfixture exactbytes+actual memberrouter passes3payloads includinghandle0/empty; existingbefore fails. Pendingencoders/catprepare read preparedarena, not oldlivebuffer; History coordinated. No RSS/image/proof claim. Evidence planning/evidence/horse-entries-list-seal.json.

E007 BP resume budget admission: fnn-command-bp-node-resume opened service before reading budget file outside unwind-protect; failure stranded local service/locks. Budget read now inside shared cleanup macro.3 actual command paths pass; original release0 fails. Transport notified same ordering in active main BP node startup, where they own fix. Evidence planning/evidence/horse-entries-bp-resume.json.

E008 TCPCL command acquisition: listen/send opened trace before spool acquisition outside cleanup protection. Failed spool admission stranded trace. Both now acquire within shared cleanup macro and keep socket/spool/trace cleanup independent.8 paths using actual command bodies and real CLstreams pass; original leaves trace open. Exits delegated, Transport notified. Evidence planning/evidence/horse-entries-tcpcl-acquisition.json.

E009 AUTHINFO physical lock boundary: open-lock conflated all fstat/flock OS errors with contention. Only EAGAIN/EACCES from actual flock now refuse; fstat/other flock errors retain their physical fault. Acquisition cleanup preserves primary. Execute developer cut validation now occurs before acquiring lock and protected body acquisition plus independent unlock/close prevents lost custody.13 actual adapter paths pass; original fstatEIO becomes false refusal. Access coordinated. Evidence planning/evidence/horse-entries-auth-lock.json.

E010 — Offline administrative query/execute cleanup masked the primary body error when Store close also failed. Both actual entry consumers use Exits fnn-unwind-cleanups; eleven injected paths include acquisition failure, body failure, close failure, combined failure, successful output and nonlocal limit return. Before fixture fails with close-fault replacing body-fault; repaired source passes. Evidence horse-entries-admin-cleanup.json. Physical close debt remains Exits Store scope.

E011 — BP service construction acquired the shared spool lock before unprotected profile/path computations, then acquired lifecycle FD in constructor arguments before ACL2 initial state and service assignment. Failures lost the spool or lifecycle handle. fnn-bps-open now creates a minimal typed custody carrier immediately within protected acquisition, retains its lifecycle slot before initial state, and releases via Exits sticky debt API on failed return; borrowed HELD locks stay owned by HELD. Fresh acquisition checks shared release observation. Service run/resume and BPO request migrate primary-preserving cleanup. Twenty actual source paths pass with actual Exits release e88075c84; prior constructor fixture fails post-spool projection. Evidence horse-entries-bp-open-custody.json.

E012 — Non-Linux import/init publication lock classified every fstat/flock OS failure as publication-locked refusal. Actual helper now refuses only flock EAGAIN/EACCES, retains local pre-return custody, and routes independent unlock/close through shared cleanup. Unobserved physical return retains exact descriptor/condition debt and blocks retry/new non-Linux ownership. Ten feature-scoped source cases plus Linux no-lock branch pass; old fstat EIO fixture falsely refuses. Evidence horse-entries-publication-lock.json; actual OpenBSD/image qualification remains separate.
