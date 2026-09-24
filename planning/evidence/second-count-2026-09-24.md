# second-count: ACL2 names the transaction file; the payload bound is the profile's

Lane `second-count` from dev `7bd50329`; source `11ca2147` (books and host),
`d1ed8ea4` (registry and teeth sections). Closes finding 1 of
[m5-profile-upgrade](m5-profile-upgrade-2026-09-24.md) and its two
payload-constant notes.

## What moved

- The owner's service-struct record count (`host/native/owner.lisp` slot
  `records`, its `(length records)` init and its `incf`) is deleted. The
  owner names each transaction file from `fn-owner-pending-sequence`
  (`host/owner-host.lisp`), the developer `store post` and `probe` from
  `fn-store-sn-pending-sequence` (`host/store-node-host.lisp`); both are
  `fn-sbud-pending-sequence` (`books/store-budget-naming.lisp`) of the Store
  state ACL2 carries. The name is `fn-store-txn-name` = `fn-sbud-txn-name`,
  the scan's `fn-bs-txn-name`.
- `*fn-store-max-payload*` (`host/store-host.lisp`) is deleted.
  `fn-store-post-boundary` takes the persisted profile and is
  `fn-sbud-post-boundary`; the served owner asks `fn-owner-post-boundary` over
  the profile `fn-owner-install-profile` was handed.
  `fnn-validate-post-boundary` relays the verdict and compares nothing. The
  codec limits that used the constant (wire body limit, feed render, prepare
  input checks) read the record codec's `*fn-record-max-payload*`, which bounds
  every profile's (`fn-sbud-payload-bound-within-record-codec`).

## Theorems

`fn-sbud-pending-sequence-is-used`; `fn-sbud-pending-name-is-the-scans-next-name`
(in a record phase of a well-formed kernel, the committed names 0..used-1 plus
the host's name are exactly the pairs `fn-bs-txn-observation-pairs` binds to
0..used); `fn-sbud-post-boundary-refuses-exactly-past-the-profile-bound`
(with the other four boundary facts valid, `:ok` iff the length is at most the
profile's payload field, else `:payload-bound`; the owner relays that as the
Store word `:refused`, W3's 441 line). Teeth: `tests/acl2/store-budget-naming-tests.lisp`,
witness reached by owner transitions, one counterexample and one `must-fail`
per hypothesis. PRF-004, STO-005.

## Certification

- persvati: `certify-20260924T182844Z-3383029` (book 2.18 s, test 4.23 s) and
  `certify-20260924T183604Z-3456823` (the test book after its section edit,
  4.14 s); `--affected-by books/store-budget-naming`, 2 jobs, 300 s, w25.
- hbox image closure: `certify-20260924T183133Z-1784524` (282 installed, 4
  certified, passed); `proof_artifacts.py validate --profile default` loaded
  116 roots. (A first `acquire` in the same tree found no complete cached
  set and removed the tree's certificates; the incremental certify was rerun
  and the images built from that.)

## Images (hbox, `/tank/fn/scratch/second-count/tree-11ca2147/build/images/11ca2147`)

| file | SHA-256 |
| --- | --- |
| `fn-host` | `432622d29a28d59455e01f3e5b426036c5862db21d5f7d1205a9304ab11e3505` |
| `fn-host.core` | `3026b609d48c70140cb51c48c640e3180da48f583a0f6073a492409cb8140076` |
| `fn-host-developer` | `e4eeefd290450e7497dade96e2c4089e0caacfa88f72c737f51a92b2f3b2ba18` |
| `fn-host-developer.core` | `89b60de9de56db987dc30d0386ec57815298ae5eb63f5cc3c671a7b4d41e0c15` |

w28 `acl2-literal-4g`, OpenSSL 3.5.8, `image.sha256` validated.

## Native results (logs in [second-count/](second-count/))

| run | result | log SHA-256 |
| --- | --- | --- |
| `native_operator_campaign`, all 25 cuts, served and store entries | **50 of 50 cut observations pass** (`judge.py` of campaign-1a9dd747; [judged.md](second-count/judged.md)) | log `f5baffe2…`, json.gz `cf387fc9…` |
| same run, faults | 13 of 15 as the 1a9dd747 table; the two `cross-entry-retry-*` faults never seeded: their control socket path was 111 octets, over `sun_path`, because of this scratch directory's name | (same) |
| faults rerun, `--only no-such-cut`, work dir `/tank/fn/scratch/scw` | fault table **identical** to campaign-1a9dd747's, including both cross-entry retries (`committed sequence=1`, then `REFUSED`; `ACCEPTED`, then `conflicting immutable Message-ID`) | log `4a67e65e…`, json.gz `c896ad03…`, [judged-faults-rerun.md](second-count/judged-faults-rerun.md) |
| `tests.test_native_owner.NativeOwnerTests -k post -k body_limit -k uncertain -k fences` | **5 tests OK**, 12.5 s | `7f05dfbe3238789e133d43bec226a1276f3393ae004a772f46e5a09db6acf348` |
| `tests/native_differential.py` (twice) | every step's exit code agrees between the Python and native hosts, file names agree, `post maximum payload` (32768) accepted and `oversize` (32769) refused on both; exit 1 on findings this lane did not cause (below) | `b4ac41c7…`, `716baf34…` |

## Findings

1. The differential is not a clean control: its disk comparison differs in
   record bytes past the common prefix at different steps in the two runs
   (a wall-clock stamp is the likely difference), and the native `status`
   prints a `headroom` line the Python host does not (from the profile
   lanes). Neither concerns naming or the boundary.
2. `books/owner-agent.lisp:81` still names `*fn-store-max-payload*` in a
   docstring; left unedited to avoid recertifying its dependents.
3. `fn-own-body-limit` (the wire limit) is fixed at recovery, before the
   profile is handed over, so it is the codec's 32768 and not the profile's
   field; the profile's bound is enforced at the boundary. For both named
   profiles the two are equal (`fn-sbud-named-profile-payload-bounds`).
4. The per-record ceiling of the profile (field 3 / field 4, 196608) bounds
   encoded records, not payloads; the payload bound is the profile's payload
   field.
