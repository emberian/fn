# Native image closure of dev — 2026-09-22, fourth pass (images built)

This record continues
[`native-freeze-01fbdad4-2026-09-22.md`](native-freeze-01fbdad4-2026-09-22.md)
and the third pass on `w31/freeze-3` (up to `47075f0e`), which repaired
`books/store-node-traces`, `books/store-node-resolution`,
`books/store-observed`, `books/owner-invariants` and `books/owner-tls-prefix`
and left two independent reds.  The image closure now certifies in one run
at one frozen origin, and the production, developer and DTN images are built
from it.  Nothing here is a server, proof or flight-readiness claim; the
images have not been qualified at runtime.

## Sources and toolchain

- Branch `w31/freeze-3` at `dabebb845adc3e3d6e8dc93c620782f54e6b106a`,
  which carries `dev` at `2788d4cb` (the release replay `host/native/build.lisp`
  calls).  The image source is that revision: the 308 files under `books/`,
  `host/`, `Makefile` and `tools/build_native_host.sh` at the frozen origin
  were compared by SHA-256 with the revision before the build and are
  identical.  The later commits on the branch change only planning files
  and `tools/runbooks/hbox-image-build.sh`.
- Frozen origin: `hbox:/tank/fn/gates/freeze-dev-28fb4bd0`.
- ACL2 wrapper `/tank/fn/toolchains/w28/acl2-literal-4g`, SHA-256
  `9f73da2a84d664516033fb6e944c55b55d1f7206e9599cac46ca2b208de26aa8`,
  compatibility identity
  `d5f2b9f0d2cf68c6074ea7046f4bd2e560d2984fe22d7e03f93045975ac889f0`,
  ACL2 8.7 core `/tank/fn/acl2-8.7/saved_acl2.core` SHA-256
  `3f5b101bb9437d66366dc2a299b7f9cb98fdaf40d1add5caf8baef9e451dd07d`, SBCL
  `/tank/fn/sbcl/bin/sbcl` SHA-256
  `b115fe956aadee603459fac401e1ff2cc39321e14848544a0fe438788a2fc6d5`.
- OpenSSL: the images refuse to build unless the process-wide OpenSSL pair
  provides ML-DSA-65 (`host/native/signatures.lisp`, OpenSSL >= 3.5), and
  hbox's system library is 3.3.1.  OpenSSL 3.5.8 was built from the release
  tarball `openssl-3.5.8.tar.gz` (SHA-256
  `a8f84a39918ec6415ce765d9b429d313ba97b8143169c172e734b9514464f5b2`,
  matching the published checksum) into
  `/tank/fn/toolchains/openssl-3.5.8` (`shared no-tests linux-x86_64`,
  `--libdir=lib`); `libcrypto.so.3` SHA-256
  `14d40ec690d4d2e4d49f95d9509ec8b3112c39089f9ad11fa8bde42796b99190`,
  `libssl.so.3` SHA-256
  `bb2d12bec3c53f997b5edf5e4ac3ed24584412008070eb731830f29896004ed4`.  The
  runbook now exports `FN_OPENSSL_PREFIX` to it.
- Selection: the 62 roots `tools/proof_artifacts.py roots --profile default`
  names, plus `tests/acl2/native-admin-tests`,
  `tests/acl2/native-operator-tests` and
  `tests/acl2/checkpoint-compaction-tests`.

## Runs

| run | manifest | what it was | result |
|---|---|---|---|
| `run-20260922T181341Z-b012` | `certify-20260922T181346Z-3153839` | third pass's last closure round | the two reds below and their cascades |
| `run-20260922T192515Z-e4cc` | `certify-20260922T192527Z-3194223` | the two repaired books, their dependents and `tests/acl2/checkpoint-codec-tests`, `--closure` | 104 of 105; `books/owner-prepare-correspondence` red on a third, independent cause |
| `run-20260922T200003Z-5011` | `certify-20260922T200011Z-3216833` | the image closure, `--closure`, `--jobs 8`, 1800 s per book | **165 of 165 passed** |

The 165 is the number this record claims: certificates at one origin with
one ACL2 executable, not a coverage claim.

## What changed, by book

### `books/checkpoint-codec`

The red was `fn-cpc-read-uint-of-encoding` at 1800 s, a case split through
`fn-frame-item`.  The cause is the shape of review F3 one level down: the
round-trip lemmas opened `fn-cbor-encode`, which since the bounded profile is
`fn-cbor-encode-bounded` behind the `fn-cbor-valuep-bounded` test; with that
recognizer closed the test stayed unrewritten, the goal split on it and on
`fn-frame-item` in the parse-error arm of `fn-cpc-read-uint`, and inducted.
Two local shape facts state the encoder's value once, with the recognizer
and encoder opened only there:

```lisp
(fn-cpc-encode-uint-is-argument   ; natp n, n <= max-uint
  (equal (fn-cbor-encode (cons :uint n)) (fn-cbor-encode-argument 0 n)))
(fn-cpc-encode-bytes-is-argument  ; octet list xs, len <= max-bytes
  (equal (fn-cbor-encode (cons :bytes xs))
         (append (fn-cbor-encode-argument 2 (len xs)) xs)))
```

Over them `fn-cpc-read-uint-of-encoding` and `fn-cpc-read-bytes-of-encoding`
prove with the encoder and `fn-frame-item` closed and `:do-not-induct` (0.02 s
each in the REPL).  They are disabled with the encoder where the book closes
it, since left on they rewrite an encoding before the round-trip lemmas can
match.  The same bounded-profile gap was behind six more forms below the
first red that no run had reached: `fn-cpc-read-uint-small-reencode`,
`fn-cpc-encoding-nonempty` and `fn-cpc-uint-encoding-len` now use the uint
shape fact; `fn-cpc-read-bytes-of-magic` opens the bounded byte decoder
`fn-cbor-decode-bytes` now calls; `fn-cpc-encode-value-octets`,
`fn-cpc-encode-tree-octets` and the guards of `fn-cpc-selection-protected`
and `fn-cpc-selection-encode` open `fn-cbor-valuep-bounded` instead of the
encoder.

**Restated keystone.**  `fn-cpc-journal-generation-matches` and the keystone
`fn-cpc-valid-refuses-generation-mismatch` were stated over
`fn-record-generation` and `fn-record-txid`.  The journal recognizer
`fn-sf-record-listp` has compared `fn-store-event-generation` and
`fn-store-event-txid` since the journal carries every Store event kind, and on
a retention event the article accessors select other fields (its second
field is its kind), so the old statement was false for a journal holding
one.  Both are restated over the store-event projections; on an article
record these are the article accessors by definition, so the keystone gains
no hypothesis and covers every event kind.  The test book's witness and
the mismatch tooth name the event projections
(`tests/acl2/checkpoint-codec-tests.lisp`), certified in `e4cc`.

### `books/store-prepare-correspondence`

`fn-spc-set-keyring-preserves-relation` failed at the deferred-link arm the
third pass added to `fn-snt-relation`.  Two local lemmas, each stated with
the link open and the replay and codec closed over the accessors
`fn-sn-set-keyring` keeps (store components, completion record, identity
context):

```lisp
(equal (fn-snt-deferred-linkp (fn-sn-set-keyring s keyring))
       (fn-snt-deferred-linkp s))
(equal (fn-snt-completion-linkp (fn-sn-set-keyring s keyring))
       (fn-snt-completion-linkp s))
```

The relation theorem then holds both links closed.

### `books/owner-prepare-correspondence`

Behind the store red there was a third one: since `64a80197`
`fn-ocfg-open` rebuilds a new reader connection's session over the live
node and configuration (`fn-own-reader-context`), and
`fn-opc-configured-step-preserves-owner-relation` had no fact about that
function.  `fn-opc-reader-context-preserves-relation`
(`(implies (fn-own-relation o) (fn-own-relation (fn-own-reader-context o id cfg)))`)
states it: the rebuilt connection keeps its identifier, version, frontier
and archive, and the fresh reader session has no group and no cursor, so
`fn-own-conn-okp` holds of it.  The session facts it needs
(`fn-peer-open-session` is a peer session, its base, `fn-auth-with-base` is
an auth session) are local, with the recognizers closed; the owner-invariants
counterparts are local to that book.

No theorem gained a hypothesis and none was deleted.  No `skip-proofs`,
`defaxiom`, trust tag or new `:verify-guards nil`.

## The images

Built by `tools/runbooks/hbox-image-build.sh` at the frozen origin (log
`build/freeze/image-build.log` there; the first attempt, which stopped at
the OpenSSL check, is `image-build-attempt1.log`).  Acquire and validate
accepted both artifact sets with nothing rejected:

- default: artifact set
  `3f82258998885670b262eda1f12bb0991576ab271214187be4f31c858b2009ca`, 162
  books, source `b188db351c039fbb3ec317f4b1bb424f01f360644e0e671e227728455138c3fd`,
  62 roots loaded;
- dtn: artifact set
  `5a403ba79f3c9e8e554036ecd7c9802a48973e0467c45da7afe7d3bd21b27c5f`, 150
  books, source `e00b1f256ffe8e4c8ddf2451250ee5c80f7867643822f869f698fa2324084294`,
  46 roots loaded.

Frozen under `/tank/fn/gates/freeze-dev-28fb4bd0/build/images/dabebb845adc3e3d6e8dc93c620782f54e6b106a/`:

| file | SHA-256 |
|---|---|
| `build-source.sha256` (308 sources) | `56f7e3d013e457633ea0b0fa86bf06ed6fa69179ed4408f2385aeb340c57ba12` |
| `fn-host` | `21ba38c1a66d96c32c8e50269b852cabd07ae15548306781aafa084cb0e6af32` |
| `fn-host.core` | `6e9ab804cd88ba1758229a76694503e667f210974c50c78dc208807119ab2ebf` |
| `fn-host-developer` | `7c176eda44bba39b131175a25c520c13d9ea5dada26725f08a40c9276fc569ee` |
| `fn-host-developer.core` | `e5030c4711375a43c5898f2fbba95ce531293d5b599c4b2ad50fff0ded0caabe` |
| `fn-host-dtn` | `b0066fec40589c1da3646c1185c553aa9f673a3671245cf5b268cf205a3cd4d5` |
| `fn-host-dtn.core` | `c0fed871f7d20df28e05ace6371d63ea6e7baa26cec3848a78341b55eaf607a6` |

The ready marker is at `build/lanes/w31-freeze/IMAGE-READY.txt` and
`build/lanes/w31-freeze-3/IMAGE-READY.txt`.

## Limitations

- No runtime qualification.  The only execution was `fn-host` with no
  arguments, which answered `fn-host: error: missing arguments` with and
  without `FN_OPENSSL_PREFIX`; that it answered the same without the prefix
  was not investigated, and says nothing about whether the signature
  facility initializes at run time on hbox's 3.3.1.  A running image should be
  given `FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8`.
- The launchers `cp`'d into `build/images/<rev>/` still name the unfrozen
  cores (`--core .../build/fn-host.core` and siblings), which is what the
  runbook copies; a later build at the same origin overwrites what the frozen
  launchers run.  The frozen cores' hashes above are what was built.
- OpenSSL 3.5.8 is a locally built toolchain, not a distribution package, and
  it is inside the image's trust boundary for TLS and ML-DSA.
- `fn-opc-reader-context-preserves-relation` is a supporting lemma of the
  existing keystone and has no witness or teeth of its own in
  `tests/acl2/owner-prepare-correspondence-tests.lisp`.
- The counts are certificates at one origin with one ACL2 executable.
