# Reader, consumer poll and cold-clone integration

Frozen source: `a8e4b17e`. This batch combines the T17 pinned LISTGROUP
bucket, E2 local poll/report, checkpoint auxiliary replay and fenced clone
with entropy-derived incarnation. No live service was changed.

## First combined qualification

Hbox run `run-20260923T224556Z-1ba9`, gate
`/tank/fn/gates/reader-clone-poll-a8e4-20260923`, used ACL2 8.7 via
`/tank/fn/toolchains/w28/acl2-literal-4g`, toolchain identity
`d5f2b9f0d2cf68c6074ea7046f4bd2e560d2984fe22d7e03f93045975ac889f0`.
Invocation: `python3 tools/farm.py submit hbox --jobs 4 --timeout-seconds 180
--cache /tank/fn/certcache --acl2 /tank/fn/toolchains/w28/acl2-literal-4g
--remote-root /tank/fn/gates/reader-clone-poll-a8e4-20260923`.
The [original manifest](manifests/certify-20260923T224617Z-375509.json)
records all source digests and installed origins: 425 cached books, 122 newly
attempted; 112 passed and 10 failed in 168.027 seconds. It is a failed run,
not a combined green claim. No proof timed out.

Four substantive roots failed after the new group-index field/tagged pin;
the other six were dependent roots/tests: `nntp-auth-invariants`,
`config-owner-live`, `owner-prepare-correspondence`, `owner-agent`.
The authentication and injection proofs instantiated the old bare Message-ID
index while actual dispatch now receives the tagged group pin. The historical
reader proofs needed facts for the added bucket field. These failures prevent
claiming the combined invariant closure until its repaired run passes.

## Repairs

`cb66a859` and `416f379d` instantiate the actual pinned-index expression,
carry both group and trie correspondence, and preserve the group bucket in the
proof's byte-feed connection helper. The theorem statements are unchanged.
The first [focused retry](manifests/certify-20260923T225151Z-387621.json)
failed because the correspondence premises and tagged-pin selectors were
still opened. A live ACL2 session then admitted the corrected refused-POST
proof; closing the pin selectors reduced that form from 22.10 to 4.58 seconds
in the same session after undoing the first form. Session admission alone
was not treated as certification. The [final scoped run](manifests/certify-20260923T225611Z-397209.json)
passed both authentication books and both test roots in 22.435 seconds.

`58209b48` repairs the analogous actual dispatch instances and group-aware
feed helper for `owner-agent`, with unchanged theorem statements. Its
[book and test manifest](manifests/certify-20260923T225557Z-396696.json)
is retained. Historical reader/configuration repairs remain in progress.

The static `make check` initially found an omitted linked clone manifest;
`7fe09ab0` archives the original unchanged evidence and the rerun passed.
This does not qualify runtime behavior. Stamp has staged the exact a8e4
source in `/tank/fn/gates/reader-clone-poll-native-a8e4-20260923`, but no
image build or native result is claimed here. Planned scenarios cover
historical LISTGROUP ranges, signed poll/report binding, advancing ACK with
reply loss, and clone process-death/old-cursor rejection.

## Repaired combined qualification

Source `bc9be7ec` contains the four proof repairs and historical READ/TLS
relation, including runtime pin cleanup when a read closes a connection and
session bounds against its pinned archive. It also adds ACL2-owned clone path
preflight and the exact public Mini E1 source option in the native poll test.
The original unbuilt `a8e4b17e` image snapshot is superseded.

Full incremental hbox run `run-20260923T230009Z-f41e`, gate
`/tank/fn/gates/reader-clone-poll-repair-20260923`, passed with 512 cached and
37 newly certified books in 86.662 seconds at four jobs on the same toolchain.
The [original manifest](manifests/certify-20260923T230027Z-407330.json) binds
all input bytes, installed origins and results. No new red remains from the
first run. The remaining slow roots include `owner-invariants` at 44.459
seconds and `owner-config` at 15.265 seconds; this is not a claim that every
individual proof is under ten seconds. `make check` passed.

The new exact native source is staged in
`/tank/fn/gates/reader-clone-poll-native-bc9-20260923`. Developer/production
build and native qualification are authorized to proceed; no runtime result
is inferred from the certificate closure. Later ADVANCE uniqueness,
consumer index, Mini projection and BP fragment/report work are outside this
image's scope.
