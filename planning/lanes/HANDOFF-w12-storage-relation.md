# w12/storage-relation — scoped proof checkpoint

Worktree `build/lanes/w12-storage-relation`, baseline `8b474e2`. Root owns
PRF-044 and all registry/board/milestone edits. The scoped proof and concrete
witness books certify; there is no broad K0 completion claim. Root requested this checkpoint and a stop
for budget control; no expanded initializer implementation has been started.

## Implemented subject and boundary

`books/byte-store-relation.lisp` proves an exact final representation of
`fn-bs-run` over `fn-bs-init-program` with successful syscall outcomes, then
establishes the strengthened relation under `fn-bs-initial-inputp`. The physical
normalization lemma `fn-bs-init-program-establishes-initial-image` and the
classification lemma `fn-bs-initial-image-establishes-relation` do the work;
`fn-bs-init-program-establishes-relation` composes them and must not be cited
alone as if it discharged both parts independently.

`fn-bs-first-frontier-program-preserves-relation` proves every returned pair of
the real executable frontier program related, under a positive write unit,
`fn-bs-initial-inputp` and `fn-bs-frontier-inputp`. It covers the first allocation
with successful outcomes, arbitrary valid config/frontier octets, arbitrary
staging name and positive unit. `fn-bs-first-frontier-program-completes` excludes
an empty/refused trace as the positive witness. The old unqualified K0 formula
is false: `fn-bs-first-frontier-program-rejects-old-frontier-bytes` proves that
recycling the old frontier octets breaks the relation at the rename even though
the program reaches reserved. No byte crash freedom or cut was removed.

The initial-input predicate groups boundary checks. With the concrete codec,
metadata validation entails octet shape, so malformed-octet guard probes do not
independently isolate every internal codec conjunct. The keystone hypotheses
are the positive unit, the initial-input boundary and successor-input boundary;
the tests drop each independently and also retain explicit malformed-octet
probes without overstating their independence.

## Definition repairs

`fn-bs-store-relation` now requires `fn-bs-authority-knownp`: every durable or
pending authority target occurs in the inode table. Previously the byte-state
recognizer permitted a dangling authority target equal to next-ino, and the
abstract config/frontier seams permitted valid-looking absent content, allowing
a subsequent staging allocation to alias authority. This is a physical
publication/allocation invariant, not a codec assumption. K1-K4 hypotheses are
strengthened, and their existing statements re-certify unchanged.

The frontier round-trip constraint is bounded by `*fn-cbor-max-uint*`, the same
uint32 allocator domain the host and concrete metadata frame implement. The
previous all-natural constraint could not have a bounded CBOR realization. No
scan theorem consumes the round-trip constraint; name-list injectivity remains
all-natural. Python `{:020d}` is minimum width, so transaction name realization
must preserve that all-natural injectivity rather than add artificial domain
premises to the scan inductions.

## Arbitrary-state continuation

`books/byte-store-program-invariants.lisp` has no empty-history premise. It
proves allocation freshness from relation plus known-inode membership, authority
quietness at ready, and relation preservation for start-frontier and the
frontier-file, frontier-replace and failed-directory observations. The
`fn-bs-frontier-noncommit-observation-preserves-relation` theorem names the actual
`fn-bs-step` interpreter. Its independently enumerated event domain includes
known-failure/refused and uncertain/error callbacks, and excludes announcing a
successful directory commit before the byte fence.

Successful directory observation is proved under the attempted phase and
`fn-bs-frontier-directory-committedp` (quiet root plus candidate bytes durable).
The named `fn-bs-frontier-directory-step-is-kernel-observation-by-definition`
bridge equates the interpreter step to that kernel subject; it is deliberately
not a registry event.

Tests in `tests/acl2/byte-store-program-invariants-tests.lisp` exercise a one-octet
short write, a torn/zero staging fsync failure, an issued rename returning EIO,
and both dropped/applied directory-fsync failures. They assert the interpreter
stops before the explicit host callback, and distinguish ready from
fenced-frontier. These are concrete fault examples, not a proof of arbitrary
syscall outcomes. General fresh create/write/fence/rename preservation and
recovery establishment remain open.

## Call correspondence that remains open

Current `Store.advance_frontier` (`tools/run_store.py:1304`) uses the program's
syscall/cut/observation ordering. Its successful file, replacement and directory
callbacks are at lines 1340, 1353 and 1366; error callbacks at lines 1350, 1363
and 1381. These are a source correspondence anchor, not a theorem of Python. The metadata initializer theorem is NOT complete current-host
initialization correspondence: `Store.initialize` (`tools/run_store.py:980`)
additionally creates/fences
configuration-record history and its directory; `_safe_directory` already
fences the parent before each existing init-created cut; `_open_lock` creates
writer.lock. The old `fn-bs-init-program` does not transcribe these steps.

`tools/transcribe_check.py` reads direct source forms and does not inline Python
`_safe_directory`/`_publish_initial_file` or ACL2 init-file-steps. Its zero
fidelity-defects does not establish a syscall bijection. The continuation will
add a separate current fresh-store initializer model with parent fences, lock
allocation, config namespace/history publication, existing cuts and missing
helper syscall cuts. Existing/retry initialization branches remain distinct.
Root explicitly requested this continuation after landing the scoped packet,
then deferred implementation to a subsequent lane at the budget checkpoint.

## Evidence checkpoint

Local `tools/acl2 --timeout 150` proved all current relation and program
invariant forms. Symbolically enabling the whole runner caused an expansion
fan; `tools/proof_profile.py` identified fn-bs-run/apply-ops. The finite proof
now unfolds exactly one runner call at a simplifier checkpoint via local
computed hints, keeping the syscall and observation definitions executable and
unchanged. No trust tags, skip-proofs or axioms were used. The new model
constructors/predicates retain `:verify-guards nil`; admission and theorem
certification are not a guard-verification claim.

Remote hbox, `/tank/fn/lanes/w12-storage-relation`, jobs 4 through farm/swarm-build:

- `run-20260921T062043Z-70b1`, evidence
  `build/acl2/certify-20260921T062047Z-1641861`: scan, initial relation packet and
  existing K1-K4 keystones certify with the definition repairs.
- `run-20260921T063644Z-8240`, evidence
  `build/acl2/certify-20260921T063649Z-1663162`: initial-input boundary and
  arbitrary-state observation continuation certify. The final by-definition
  interpreter bridge and transaction-target freshness corollary were added
  after this checkpoint and are covered by the final run below.
- Final proof sources: `run-20260921T064844Z-a4b1`, evidence
  `planning/evidence/manifests/certify-20260921T064847Z-1678502.json`, passed
  with ACL2 Version 8.7. Invocation: `python3 tools/farm.py submit hbox
  books/byte-store-relation books/byte-store-program-invariants --jobs 4
  --remote-root /tank/fn/lanes/w12-storage-relation --closure`, followed by
  `farm.py wait`/fetch. The generated manifest carries exact executable,
  runner, source and certificate SHA-256 digests and per-book results.

Local `python3 tools/certify_books.py books/byte-store-frame
books/byte-store-relation books/byte-store-program-invariants
tests/acl2/byte-store-relation-tests tests/acl2/byte-store-program-invariants-tests
--jobs 1 --timeout-seconds 120`, evidence
`build/acl2/certify-20260921T063239Z-85540`: both relation proof roots certify;
metadata fails a real guard (untyped bound in fn-bs-meta-frame-okp), hence witness
books cannot include it. Codec owner received the exact failure and added natp.
A scoped retry `certify-20260921T063538Z-88136` reaches the next metadata guard:
uint encoder payload length bound. Matching scan cert installed in the codec
worktree so that owner can now iterate on the actual certify world.

After integrating codec commits `79a7113` and `4048cf4`, the metadata book
certifies locally in `certify-20260921T065207Z-1440`. The first witness attempt
then exposed a test harness error: `fn-bs-crash-imagep` is existential and
non-executable. The corrected test checks the actual legal choice lists and
proves their constructor bridge to the existential predicate. Both concrete
witness books certify in `certify-20260921T065322Z-2727`, using ACL2 Version 8.7,
with invocation `python3 tools/certify_books.py
tests/acl2/byte-store-relation-tests tests/acl2/byte-store-program-invariants-tests
--jobs 1 --timeout-seconds 120`. Its archived generated manifest records exact
source/tool/certificate digests. They use codec lane's
`fn-bs-initial-config-octets` and `fn-bs-initial-frontier-octets` functions, not
defconsts (which ignore attachments). They include the previously absent live
K1 witness: distinct old/new admissible byte crash images at frontier-replaced,
both scanned through actual metadata frames. No transaction name attachment is
needed for this first allocation witness; nonempty-history executable witnesses
still await the decimal realization.

## Commits and integration

- `1fa0b46`: initial storage relation/code/spec packet.
- `a356f88`, `4000912`: cherry-picks of codec owner `e689969`, `022a844`; root must
  not re-apply them after integrating that lane.
- `c852f1c`, `850fcee`: cherry-picks of codec owner `79a7113`, `4048cf4`;
  these supply the certified metadata guard and grouped attachment fixes.
- The final checkpoint adds phase continuation, witnesses and this handoff.
  Metadata guard fixes remain owned by the codec lane; do not attribute their
  production changes to this proof lane.

Root should add new proof/test roots to Makefile, update PRF-044 with its actual
conditional scope and pending full-init/recovery subjects, and generate events
with tools/ledger.py. No shared registry or generated ledger was hand-edited.
