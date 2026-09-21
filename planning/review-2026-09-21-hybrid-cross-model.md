## Review: hybrid signature + durable-author evidence (source f4f870f8)

**Scope covered:** `books/hybrid-signature.lisp`, `books/hybrid-store.lisp`, `books/hybrid-profile.lisp`, `books/crypto-seam.lisp`, `books/stx-{evidence,keyring,accept}-records.lisp`, `host/hybrid-signature-host.lisp`, `host/native/{signatures,crypto,tls}.lisp`, `tests/native_hybrid_signatures.lisp`, `tests/acl2/hybrid-signature-tests.lisp`. I did not repeat the root-flagged principal/keyring-generation join gap.

### 1. Ed25519 host verification silently faults on any realistic article — the feature cannot authorize most legal-size articles (Critical, reachable)

`fn-hsig-signed-preimage` (`books/hybrid-signature.lisp:93-99`) signs `fn-hsig-subject-body` (`:61-72`): 2022 fixed octets (version, suite, 32-byte principal, both algorithm ids, the *exact-width* Ed25519 (32) and ML-DSA-65 (1952) public keys, u16 source-length) plus the 30-byte CBOR-encoded domain tag, plus up to `*fn-article-max-octets*` = 32768 (`books/article.lisp:15`) of `source`. Worst case = exactly 34820 octets — which is precisely `+fnn-hsig-max-message-octets+` in `host/native/signatures.lisp:8`, correctly used by `fnn-hsig-ed25519-sign` (`:151-168`) and both ML-DSA-65 calls (`:195-254`).

But `fnn-hsig-observe` (`signatures.lisp:256-270`) verifies the Ed25519 component by calling `fnn-crypto-ed25519-observe` → `fnn-crypto-ed25519-verify` (`host/native/crypto.lisp:158-184`), which bounds the message via `fnn-crypto-octets message +fnn-crypto-max-message-octets+ ...` — `+fnn-crypto-max-message-octets+` is **4096** (`crypto.lisp:19`), the generic HST-004 seam bound shared with the freshness-anchor code, never resized for the hybrid-signature preimage. `fnn-crypto-octets` *signals* `fnn-crypto-fault` when the value exceeds the limit; `fnn-crypto-ed25519-observe`'s handler-case (`crypto.lisp:186-197`) maps that to `:fault`, never `:verified`. Since `fn-hsig-authorize` (`hybrid-signature.lisp:103-112`) requires `ed25519-observation` to be `:verified` exactly, **any article whose `source` exceeds ~2044 octets (4096 − 2052 fixed overhead) can never be authorized**, even with two genuinely valid signatures — over 93% of the legal 32768-octet article range is unreachable. `tests/native_hybrid_signatures.lisp` uses a 16-byte message and does not exercise this. This is an availability defect, not a forgery: it fails closed, but it means the durable-writer lane will see real articles fail authorization with no informative signal (both `fnn-hsig-authorize-profile` and `fnn-hsig-authorized-article-event` just return `nil`).

**Repair:** give the hybrid-signature Ed25519 verify path its own bound sized like `+fnn-hsig-max-message-octets+` (either a signatures.lisp-local Ed25519 verify wrapper, or thread the hsig bound into `fnn-crypto-ed25519-verify`), leaving `crypto.lisp`'s 4096 constant for its existing anchor/delegation callers.

### 2. Accepted D09 events are not recognized by the evidence-layer authority gate (Critical for integration, requirement gap)

`fn-hsig-authorized-article-event` / `fn-hsig-keyring-event` (`books/hybrid-store.lisp:45-75`, `:22-30`) now perform genuine dual-signature authorization and tag events with `*fn-hsig-profile-tag*` (`books/hybrid-profile.lisp:7`, `"fn-hybrid-v1"`). But `fn-stxe-profile-supportedp` (`books/stx-evidence-records.lisp:61-63`) still ignores its argument and unconditionally returns `nil`, so `fn-stxe-authority-verdict` (`:65-70`) answers `:unsupported-profile` for every one of these events regardless of how they were constructed. Nothing in this commit connects `fn-hsig-authorize`'s conjunction to that gate (confirmed by grep: `fn-stxe-profile-supportedp` has exactly one definition site and no override). `specs/retention.md:124` lists "D09 signature authority" as open, so this is expected today — but it means: a correctly-signed, correctly-accepted kind-4 event is **indistinguishable from an unsupported/garbage profile** to any replay or reader consumer. There is also no decoder anywhere in the reviewed books for `fn-hsig-verdict-detail`'s encoded bytes (`hybrid-store.lisp:35-43` only encodes; nothing reconstructs `signatures` from `fn-stxe-detail` for replay-time re-verification).

**Requirement for the parallel lane:** before treating "the writer accepted this" as "history is authoritative," it must (a) wire a profile-recognition path for `*fn-hsig-profile-tag*` into the evidence layer, and (b) supply and prove a decoder for `fn-hsig-verdict-detail`'s bytes back into `fn-hsig-keyset-p`/`fn-hsig-signatures-p` shape, since the raw octets round-trip is currently asserted by construction only, never verified by a decode.

### 3. Subject-body injectivity across `(principal, keys, source)` is argued in prose, never proved or tested as a general property (Medium, assurance gap)

`fn-hsig-subject-body` (`hybrid-signature.lisp:61-72`) relies on every field but `source` having *exact* fixed width (enforced by `fn-hsig-subject-p`/`fn-hsig-keyset-p`, `:32-59`) plus a length-prefixed `source`, to make the concatenation unambiguous — stated only as a comment ("Fixed-width fields make the enrolled key set self-delimiting..."). `books/crypto-seam.lisp` proves `fn-digest-tagged-preimage-injective` (`:196-213`) for the *tag-vs-message* boundary, but there is no equivalent theorem for `fn-hsig-subject-body` itself distinguishing two different `(principal, keys, source)` triples. `tests/acl2/hybrid-signature-tests.lisp:48-59` only spot-checks two axes (a one-octet source suffix, and a substituted Ed25519 key) and never varies `principal` or the ML-DSA-65 key. Per this project's own assurance rules ("teeth ship with the theorem," "cite keystones, never corollaries"), the "exact authored bytes / no host semantic twin" claim currently rests on an unproved, only-partially-witnessed argument for the one function that turns three independent identity/content inputs into the single signed byte string both primitives verify.

**Repair:** state and prove `fn-hsig-subject-body-injective` (or an injectivity theorem for `fn-hsig-signed-preimage` over the full input tuple, `:rule-classes nil` like its crypto-seam counterpart), and extend the test book with `principal`- and ML-DSA-key-varying witnesses.

### What cannot yet be determined
- Whether the not-yet-integrated durable-writer/CLI lane already imposes its own (smaller) size cap before calling `fnn-hsig-authorize-profile`/`fnn-hsig-authorized-article-event`, which would mask finding #1 in practice; that code isn't in this packet.
- Whether finding #3's informal argument is actually exploitable (I found no evidence of a real collision — the fixed-width design looks sound — only that it is unproved and under-tested).
- Runtime behavior of the OpenSSL 3.5 ML-DSA-65 EVP message-mode API and libsodium's detached-sign ABI is taken as explicit trust per your framing; I did not attempt to validate it, and no build/test was run.


## Root disposition and evidence boundary

This read-only Claude Sonnet review ran through Claude Code inside tmux session
`fn-w27-hybrid-review` against detached source `f4f870f8`. It executed no
certification, build or runtime test. The source packet was subsequently
rebased as `0ad3b97d`; the review describes its original scope.

Finding 1 is accepted. The generic Ed25519 observation's message limit is
incompatible with the hybrid preimage. The crypto lane owns a separately
bounded verification entry and large-message primitive/runtime witnesses.

Finding 2 is a required composition boundary, not evidence that unsupported
profiles should be authorized merely by recognizing their tag. The durable
writer/replay lane must couple the selected profile with exact enrolled-key
snapshot binding and preserved historical evidence. `f652e92f` adds the
canonical snapshot/detail binding helper and retained principal/public keys;
its invocation by the actual writer and replay remains required. Historical
acceptance evidence and current authorization remain different queries.

Finding 3 is accepted as an assurance obligation. The fixed-width construction
has no demonstrated collision here; a subject/preimage injectivity theorem and
hypothesis counterexamples must establish its claimed tuple binding. This does
not establish either primitive's cryptographic security.
