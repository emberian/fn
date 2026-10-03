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
