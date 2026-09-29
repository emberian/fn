# Failure model and assumptions

Status: named assumptions for conditional proofs and qualification. Actual fn
host/process/fault tests now exercise portions of the boundary; they do not
qualify physical power-loss behavior or establish the assumptions universally.
See the [store refinement contract](store-refinement.md) and the
[BP exchange evidence](../tests/evidence/2026-09-18-bp-exchange.md).

## Named assumptions

| ID | Assumption and scope |
| --- | --- |
| A-DURABILITY | A completed platform barrier preserves the named bytes and necessary namespace updates across a modeled crash. |
| A-WRITE-ISOLATION | Later incomplete writes cannot damage previously durable committed storage outside the modeled write unit. The adapter/layout must establish that isolation. |
| A-HOST | The adapter preserves event identity/order contracts, reports outcomes honestly, and does not mutate logical data behind the core. Constrained as `fn-assume-host-report` and `fn-assume-host-events` (`books/assumptions.lisp`); no theorem takes them as a hypothesis yet, so no row with events cites A-HOST (the citations were dropped, keystone audit 2026-09-27 G3-9). A row cites it again when a statement is over those functions. |
| A-HOST-EXCLUSIVE-READ | While a store is open under its lock no other writer changes the files a range read covers, so the concatenation of range reads equals one whole-file read (P3; `books/assumptions.lisp`). |
| A-CRYPTO-TRAILER | The tears the platform produces of a written frame are tears of the byte model, and none validates as a frame unless it is the exact write (`fn-assume-crash-tearp`, `fn-assume-crash-tear-never-validates-unless-exact`, `books/assumptions.lisp`). Qualification is statistical: a validating tear is a garbled region whose 32-octet trailer is the BLAKE3 digest (SHA-256 up to store format 9) of its own prefix; the pessimistic figure is the collision bound, about 2^-128 per chosen pair (the record log, PRF-244). |
| A-CHECKPOINT-PUBLICATION | A checkpoint file whose segment chain verifies at the open is the writer's file of a publication of a history that opened :ok under the open's configuration at the F row's frontier (`fn-assume-checkpoint-publishedp`, `fn-assume-checkpoint-publication-is-a-publication`, `books/assumptions-publication.lisp`; PRF-992). The open from a checkpoint (`fn-store-sn-recover-from-checkpoint`, host/store-node-host.lisp, calling `fn-sfi-extend-open`) relies on it for the two facts it no longer computes: the prefix's finalize verdict and its transaction bound NEXT; under it the open is the twin's (`fn-sfp-open-under-checkpoint-publication`). Pessimistic figure: A-CRYPTO-TRAILER's collision bound, about 2^-128 per chosen pair of frames, not the second-preimage figure; operationally, a foreign store's verifying checkpoint is refused by the lineage check (row A10) before this open runs. |
| A-CARRIED-PAIR | The pair (R . IX) a host carries across extensions of a checkpoint's fold satisfies `fn-sfi-cpr-carriedp`: it is the pair `fn-sfi-carry` produced at the open or the one the previous carried entry answered, which the preservation theorems keep carried (`fn-assume-carried-pairp`, `fn-assume-carried-pair-is-carried`, `books/assumptions-publication.lisp`; PRF-1005). The invariant is a verified guard the evaluator cannot run (a defun-sk) and ACL2 will not hold in a stobj; at a boundary that can afford one node pass `fn-sfk-carried-check` decides it (:ok establishes it, every answer but :uncertain-id-trie refutes it). Nothing on a served path calls the carried entries at this revision (the open calls `fn-sfi-extend-open`); the row is the contract of the swap wiring that will. |
| A-CRYPTO | Selected primitives meet the stated integrity/authentication assumptions for the deployment; no universal digest-injectivity axiom. |
| A-CRYPTO-NATIVE | The served images' BLAKE3 primitive (the vendored BLAKE3 1.8.7 C in `lib/libfn-blake3` beside the core, `third_party/blake3` through `host/native/fn-blake3.c`, loaded by `host/native/digest.lisp`) computes BLAKE3, so the raw `fn-blake3-stobj`, `fn-blake3-of-prefixed-buffer` and `fn-blake3-of-prefixed-range` it installs answer what the ACL2 definitions (proved equal to `fn-blake3`, books/blake3.lisp: `fn-blake3-stobj-is-blake3`, `fn-blake3-of-prefixed-buffer-is-blake3`, `fn-blake3-of-prefixed-range-is-blake3`) answer. A trust-boundary entry (HST-004), not an ACL2 constraint: no theorem mentions the native code, and every theorem about `fn-digest`, `fn-frame-digest`, `fn-frame-digest-buffer` and `fn-frame-digest-range` is about the ACL2 attachment. Qualified at every start (the official vectors through every native form, then every length 0..300 and every chunk edge to 16 chunks against ACL2's `fn-b3x-hash`; a disagreement refuses the start) and per image by `tests/test_native_digest.py` (`digest-check run`: list, buffer and window forms, lengths 0..1 MiB, against `fn-b3x-hash`; the `blake3` verb against `tools/blake3_ref.py`'s pure-Python BLAKE3). A non-octet element leaves the fast domain and is reduced as `fn-b3-fix-octets` reduces it. The keyed and derive_key modes (books/node-secret.lisp) run the ACL2 definition. RFC 8315 Cancel-Lock's lock hash is SHA-256 over the list model `fn-sha256` (RFC 8315 sections 2.1, 2.2, 3) and has no native form. The collision figure for the frame trailers stays A-CRYPTO-TRAILER's: about 2^-128 per chosen pair (a birthday bound over 256-bit digests), not the 2^-256 second-preimage figure. |
| A-SIG-NATIVE | The realizer of `books/crypto-seam.lisp`'s constrained `fn-sig-verify` is pure ML-DSA-65 verification (FIPS 204, empty context) by the image's own library, `lib/libfn-mldsa65` beside the core (the vendored PQClean code behind `host/native/fn-mldsa65.c`, `tools/build_mldsa65.sh`): `host/native/signatures.lisp` defines the raw function and its `*1*` counterpart, and the extracted program calls the same C function of the same file (`tools/extract/native.scm` `a-native-sig-verify`; `tools/extract/build.sh` links the image's `build/lib`, and the extraction gate refuses another copy). The answer is T exactly when the key is a list of 1952 octets, the signature a list of 3309 octets, the message an octet list and the library verifies; NIL for every other shape; a library fault (unloadable, or an answer other than verified or refused) is an error, never a verdict. What is assumed is that this verifier satisfies the seam's constraints, `fn-sig-verify-is-boolean` (by construction) and `fn-sig-verify-of-sign` for ML-DSA-65's KeyGen from the 32-octet seed and its Sign (FIPS 204 correctness), and unforgeability stays A-CRYPTO. A trust-boundary entry like A-CRYPTO-NATIVE, not an ACL2 constraint: no `defattach` (the constraint cannot be proved of foreign code), no theorem mentions the native code, and `fn-sig-sign` and `fn-sig-public-key` stay unattached (nothing the host calls signs a statement). Until lane extract-writable (2026-09-28) the image refused any evaluation of `fn-sig-verify` (an unattached constrained function); every host call passes keyring NIL (`fn-intern-events records nil 0`), so no served path reached it. Qualified per extraction build by the boundary probes (`tools/extract/probes.py`: an OpenSSL-3.5-made signature from the committed carrier `tests/fixtures/dregg-e1/signed.eml`, `tools/extract/sig-vectors.json`, and eight mutations, identical through the image and the program) and per library by `tests/mldsa65_interop.py`. |
| A-TLS-NATIVE | The system TLS library the served image loads at start (`host/native/tls.lisp`: libssl and libcrypto, OpenSSL 3.0 or later or LibreSSL 3 or later, HST-016; every function tls.lisp calls is resolved when the facility initializes, at image build and at each start, and a library lacking one is refused by name) implements TLS 1.2/1.3 record protection, the handshake and certificate/key loading correctly, and its socket BIO and `SSL_peek`-then-consume behave as documented while one client worker is the sole reader and writer of a channel. fn decides nothing inside it: a connection is marked protected only after `fnn-tls-accept` returns a live channel, `tls reload` checks the new pair before it is taken (HST-020), and the consumed plaintext is checked against the peeked prefix (a short, changed or failed consume faults the connection). A trust-boundary entry of the same kind as A-CRYPTO-NATIVE, not an ACL2 constraint: no theorem mentions the library, and a STARTTLS or implicit-TLS session's confidentiality and peer authentication are the library's and the certificate chain's, never a theorem's. Signatures and digests do not use it (A-SIG-NATIVE, A-CRYPTO-NATIVE). Qualified per image by the native TLS modules (`tests.test_native_tls*`) against that image's library; the library's own correctness is its maintainers'. |
| A-SBCL-RUNTIME | The SBCL runtime and compiler that build and run the served image (the toolchain named by its identity in the certify launcher, w28: ACL2 8.7 on SBCL 2.6.8; `host/native/build.lisp` saves the core, the release bundles the same runtime) compile and execute each definition as Common Lisp specifies under ACL2's optimization policy: fixnum and bignum arithmetic, arrays and stobjs, `sb-alien` calls into the vendored libraries, threads, and the saved core's reload. This is the premise every guard-verified ACL2 function relies on when it runs in the image (ACL2 itself assumes its host Lisp, which ACL2's soundness argument names); a trust-boundary entry like A-EXTRACT and A-TARGET-COMPILER, not an ACL2 constraint, and no theorem cites it. What fn adds is bounded: the heap and control stack are sized from the store profile (HST-013) and exhaustion is a named refusal or a crash the crash model already covers, never a wrong answer. Qualified per image by the native modules and, for the product without ACL2, by the extraction gate's byte-identical differential. |
| A-PEER | A peer whose retention undertaking is relied upon follows that undertaking within the declared node-failure model. |
| A-IDENTITY | Origin/incarnation allocation and restore procedures avoid unrecognized reuse, subject to their explicit freshness assumptions. |
| A-POLICY | The evaluated policy context is authorized and identified; accepting one signed statement does not establish arbitrary authority. |
| A-FAIRNESS | For liveness only: useful contacts, capacity, scheduling, retries, and permitted routes eventually occur as stated. |
| A-BP-CONTACT | For liveness only: a base contact to a peer sustains `(fn-assume-bp-contact-asks peer)` of the driver's asks with its gate open, every publication it proposes answered within its ask (`books/assumptions.lisp`; the base-job-offer reading of A-FAIRNESS and A-BP-PERSIST, spec bp-node-machine 4.9). |
| A-DURABLE-EXTENT | A durable file holds, at an extent the host durably wrote and never rewrites, the octets written there, and the host's extent realizer answers them: `fn-durable-octets`, `fn-durable-octet`, `fn-durable-realize-octet`, `fn-durable-realize-octets` (the whole payload in one read) (`books/assumptions.lisp`; the payload arena's extent handles, PRF-294; the commit's reseat after the log's barrier takes the faithful WRITE -- the file holds, at the entry's record position, the record the log wrote there -- as its hypothesis, PRF-309). A read that does not match the entry's recorded trailer is refused by name (`arena-extent-digest`), never served. |
| A-DURABLE-LZ | The host's realizer of a COMPRESSED extent answers the value its block decodes to: `fn-durable-realize-lz` equals `fn-lzr-lz-value` of the block's durable octets (`books/assumptions.lisp`; the host reads the block through the extent realizer, trailer checked, runs ACL2's DEFLATE payload decoder over pooled buffers, `fn-pzd-decode-bufs`, and answers its octets, `fn-lzr-decode-bufs-is-the-lz-value`; PRF-326, PRF-912). A decode that fails is refused by name (`arena-extent-lz-decode`), never served. |
| A-ARENA-STORED | The host's stored-form read of a payload answers the block it holds compressed: `fn-arena-stored` of handle H is nil or (DICT C N) with `fn-lzr-lz-value` of DICT, C, N equal to H's payload (`books/assumptions-stored.lisp`; the host reads H's extent entry and C through the extent realizer, trailer checked, decoding nothing; `host/native/extent.lisp`). Used by XFN-ZARTICLE (NNT-055, `books/nntp-zarticle.lisp`, PRF-974's keystones). It is at the concrete arena what A-DURABLE-EXTENT and A-DURABLE-LZ give; it is named because the abstract arena carries no extent. Kept out of `books/assumptions.lisp`'s closure: its signature needs the arena stobj; this row is its registration (`tools/check_scaffold.py` refuses an unregistered `books/assumptions-*.lisp`). |
| A-EXTRACT | An extracted program computes what ACL2 computes: for every function F of an extracted closure and every argument list satisfying F's guard, the procedure `tools/extract` builds for F (the front end `frontend.lisp` reads F's translated body from the world with each `mbe` resolved to its `:exec`; the backend `chicken.py` compiles it; `runtime.scm`, `native.scm` and `hostio.scm` are the hand runtime; CHICKEN 5.4.0 and its C compiler) returns the value ACL2's evaluation of that body returns and performs the stobj updates it performs. The boundary is not assumed: a function the host calls checks the arity, the guard's kind conjuncts and the whole guard where the host calls it, as `fnn-call` and the `*1*` function do under guard-checking t, and inside an invariant-risk `:program` body each call checks its callee's guard, as the image's `*1*` body does (`chicken.py` boundary_def, star1_call); an interior call's guard is a proved guard obligation of its caller and is not checked. A trust-boundary entry of the same kind as A-CRYPTO-NATIVE, not an ACL2 constraint: no ACL2 term can name the backend's evaluation, and an `encapsulate` over an uninterpreted evaluator would constrain nothing a theorem uses. No theorem cites it; the claim that cites it is a deployment coordinate, an extracted image (`planning/current.md`, "qualified image"), qualified per build by `make extract-check` on hbox (the fail-closed gate `tools/extract/gate.py`: every child's exit status checked, every stage held to its manifest of expected cases, zero executed vectors a failure, uncovered functions listed; it writes `status.json` and the frozen `extraction-manifest.json` next to the run; its own tests, `tests/test_extract_gate.py`, break each stage): the served transcripts byte-identical against the SBCL image, the boundary probes (`tools/extract/probes.py`) identical, the store transcripts over a real format-9 store identical, and the per-function differential (`tools/extract/fcheck.py`: guard-derived inputs, ACL2's value against the extracted procedure's). Its scope is the inputs those runs cover; the functions the per-function differential cannot reach (a stobj or state argument) are exercised only through the transcripts. |
| A-TARGET-COMPILER | The served product without ACL2 (ember, 2026-09-28; planning/extrapolation-2026-09-27.md sections 2.5 and 5): an SBCL core holding fn's functions and host/native and nothing of ACL2 (no world, no prover, no constrained stubs), built by `tools/extract/core.sh`. Assumed: SBCL (the same build that runs the image) compiles each definition `tools/extract/cl.py` emits from the front end's IR -- the translated body with each `mbe` resolved to its `:exec`, attachments resolved, the type declarations ACL2 compiled that definition with, under ACL2's own policy (`(speed 3) (space 1) (safety 0)`, acl2.lisp `*acl2-optimize-form*`) -- to code that computes the value the image computes on every input satisfying the boundary guard, and the hand runtime (`tools/extract/clruntime.lisp`: state globals, the world properties host/native reads, the live stobjs, ACL2's total primitives for :ideal and *1* bodies, the error path) behaves as ACL2's. Not assumed: the host code is host/native itself, loaded as `host/native/build.lisp` loads it (`tools/extract/core_build.py`), so the product's I/O is the image's; each host-called entry's executable counterpart checks the entry's guard as ACL2's *1* does under guard-checking t. A trust-boundary entry of the same kind as A-EXTRACT, not an ACL2 constraint. Qualified per build by `make extract-check` (`tools/extract/gate.py`, the core as a product under test): every served transcript, boundary probe and store read byte-identical to the image, and the stateful differential (`tools/extract/stateful.py --core`: the writable verbs on twin stores, outcomes, files and subsequent reads identical, across posts, interrupted updates at every post, log and recovery cut, malformed input, guard failures, key changes, failed writes, damage and restart). |
| A-PGS-HOST-IO | The page file holds, at a page, the 2048 u64 words the host last durably wrote there, and a host's fill (pread, short counts looped, EINTR retried, end of file and every other error a named condition, never a zero fill; little-endian checked at load) answers them; no build hosts the page store today (its prototype driver was retired, Q7k 2026-09-29): `fn-pgs-page-words`, `fn-pgs-fill-realize` (`books/assumptions.lisp`; the page store, PRF-344). What is proved at this boundary (the word digest is SHA-256, the encodings, the open's verdicts) is listed there. |

### fn obligations stated as constrained functions

Not assumptions: properties fn proves of its own owner, stated as an
`encapsulate` in `books/assumptions.lisp` so that a theorem is proved once
over the obligation and each caller discharges it by functional
instantiation. No registry row cites them as assumptions.

| Obligation | Stated | Used by | Discharged by |
| --- | --- | --- | --- |
| `fn-assume-log-sole-pending-writer` | while the log recovers, no store operation but the segment's own writes is pending | `fn-lgk-recover-establishes-relation` (`books/store-log-recover.lisp`) | `fn-owb-recover-establishes-relation` (a related state, `books/owner-batch.lisp`, PRF-254). `fn-lgob-recovered-segment-fence-is-identity` (PRF-273) used it until 2026-09-27; its weakened statement needs only the segment's inode. |

## Crash-only storage model

FLR-001: permit a crash between any modeled write/barrier/publication actions.
Unsynced writes may be absent, torn, or reordered as allowed by the selected
device model. Completed durability barriers constrain what survives. Do not
assume an entire append is atomic or that unsynced data always survives as a prefix.

The write unit matters. Appending after a committed record in the same physical
sector may threaten that earlier record on some devices. The chosen alignment,
generation scheme, or platform guarantee must justify A-WRITE-ISOLATION. File
creation/renaming also has namespace durability requirements; a file flush alone
is not automatically a directory commit.

FLR-002: disk-full, known failure, and indeterminate completion are modeled
outcomes. A crash loses volatile session state and may lose receipt transmission
without losing the underlying committed obligation. A restarted node recovers
obligations, not just article bodies. Stale host completions are rejected.

## Beyond crash-only

FLR-003: separately model detectable media corruption, unavailable objects, and
whole-node loss. State precisely which copies/anchors must survive for recovery.
No single-node proof promises survival after all copies are destroyed. Hashes
do not establish hardware reliability; checksummed checkpoints do not establish
freshness against replacement of the whole store by an old valid snapshot.

Damaged committed history must cause an explicit fault/repair path. Normal
crash recovery and administrative salvage are different operations with different
claims. A salvage command must not silently report ordinary successful recovery.

FLR-004: tolerate delayed, duplicated, reordered, and replayed network inputs,
arbitrary contact gaps, and clock errors within explicit policy. Safety must not
require a synchronized global clock. Liveness claims name A-FAIRNESS and their
resource/route assumptions. Bundle or message expiry requires explicit clock/age
semantics; “timeout” does not prove remote non-acceptance.

## Required platform evidence

Before a durability claim, record OS/filesystem/device scope, write unit and
overwrite assumptions, barrier and namespace behavior, error handling, and the
fault tests performed. Simulated crash proofs and process-kill tests alone do not
establish actual power-failure behavior. D14 selects the first qualification
profile and the boundary between proved algorithm and trusted platform.

The [isolated hbox device-EIO observation](../planning/evidence/t16-private-eio-2026-09-23.md)
uses ext4 on a disposable tmpfs-backed loop device and a private `dm-flakey`
mapper. It exercises a failed transaction-directory `fsync` after the final
link. It is an error-handling profile only: it does not qualify hbox's ZFS,
physical power loss, write-cache behavior, completed-barrier survival, torn
writes, or A-DURABILITY/A-WRITE-ISOLATION for a deployed node.

The opt-in `tests/campaign/native_block_fault.py` successor profile uses only
new tmpfs backing files, positively identified loop devices, and a private
ext4 mapper on hbox.  It has four distinct cases: `frontier-dir-eio` stops at
the `fn-bs-frontier-program` pair-12 root replacement before its directory
barrier; `record-dir-eio` stops at `fn-bs-record-program` pair 10 before the
transaction-directory barrier and observes the pair-11 error; a
`record-dir-sigkill` case kills that stopped process without injecting I/O
failure; and `record-cut-snapshot` copies the private backing bytes while its
mapper is suspended, then reopens only that copied image to simulate loss of
volatile writes.  Each case checks prior durable transaction bytes, the
allowed old/new namespace outcome, and a fresh native recovery.  An EIO is a
failed syscall outcome, SIGKILL is process death, and the copied backing image
is an explicit simulated write-loss experiment.  None represents an actual
power cut or qualifies hbox's ZFS, hardware write cache, or a deployed node.
No automatic release of retained history follows from this profile.
