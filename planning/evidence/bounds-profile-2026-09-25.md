# bounds-profile: configuration generations and credentials are the operator's (2026-09-25)

Lane `bounds-profile`, branch `lane/bounds-profile` from dev `534a68d3`, part 1
of bounds-p5 (D27: a constant that bounds data moves into the store profile).
PRF-102, STO-015, SCN-050. Commits: see the LANEDUMP.

## What changed

- **No profile layout change and no new field.** Format 8 already carries
  the five namespace counts (fields 9 to 13, default 2^20, validity
  `fn-bs-profile-countp`, monotone in `fn-profile-upgradep`). Nothing read
  them. The new book `books/store-profile-namespace.lisp` adds the accessors
  (`fn-bs-profile-max-consumers`, `-max-bp-rows`, `-max-config-generations`,
  `-max-credentials`, `-max-policy-members`). It is a separate book so that
  byte-store-frame and store-profile-upgrade, with about 300 dependents,
  are not recertified. The layout stays with byte-store-frame, and whoever
  next changes the layout assembles it.
- **Configuration generations (field 11) replace
  `*fn-nco-max-config-observations*` 8192.**
  - `fn-nco-observe ENTRIES MAX-GENERATIONS` refuses `:budget` exactly past
    the operator's bound.
  - The writer, `fn-native-admin-publication-authorize`, gains
    MAX-GENERATIONS and refuses `:max-config-generations` for a generation
    above it.
  - Finding: before this lane the writer had no bound at all. It would
    publish generation 8193, and the store then faulted `:budget` at every
    open: a store the node wrote was one it could not reopen.
  - Hosts: host/native/io.lisp `fnn-bridge-config-observation-limit STORE`
    (the profile the store opened, read through
    `fn-store-config-observation-limit`), `fnn-config-record-observation`,
    host/native/admin.lisp `fnn-admin-authorize`, which passes
    `(fnn-store-config store)` to `fn-store-cfg-native-admin-authorize`.
    That function reads the field in ACL2. tools/run_store.py
    `config_publication` passes its opaque profile the same way.
- **Credentials (field 12) replace `*fn-native-auth-max-credentials*` 128.**
  - `fn-native-auth-load`, `fn-native-auth-admin-set-password` and
    `-admin-list` take MAX-CREDENTIALS.
  - The file's octet and line bounds follow the count:
    `fn-native-auth-max-octets n` = 512 (n+1) and `-max-lines n` = 8 (n+1).
    The per-credential figures are work bounds. One canonical table is six
    lines and under 320 octets, and the extra unit is for the writer's
    header. The old 65536 and 1024 were these figures at 128 without the
    header unit.
  - Hosts: host/native/auth.lisp `fnn-native-auth-install` (the owner's
    startup hook reads the field from `fnn-owner-service-store`), and
    host/native/auth-admin.lisp `fnn-native-auth-admin-execute`.
    host/native/operator.lisp `fnn-operator-store-max-credentials` reads
    config.json of the store fn.toml names, without the writer lock
    (principal administration never opened the store). This is safe
    because the profile only rises, so a read that races an upgrade sees a
    bound no larger than the owner's.
- **fn.toml (`*fn-ncfg-max-octets*` 16384, `*fn-ncfg-max-lines*` 128)
  stays, classified as work** (comment in books/native-config.lisp). The
  schema is fixed: eight tables and sixteen keys, each at most once, with
  no repeated table. So the file names no collection; the design table's
  "limits how many groups and peers one file names" does not hold. The
  store profile cannot bound it either, because fn.toml is read before the
  store and names it.

## Theorems (PRF-102) and the host line that calls each subject

| Theorem | Book | Statement | Host caller of the subject |
| --- | --- | --- | --- |
| `fn-nco-observe-refuses-exactly-past-the-operator-bound` | native-config-observation | `(true-listp entries)` ⇒ (reason = `:budget` ⇔ `(< (nfix n) (len entries))`) | io.lisp `fnn-config-record-observation` → store-node-host `fn-store-config-observation` |
| `fn-native-admin-publication-within-the-operator-bound` | native-admin | status `:accepted` ⇒ generation is a natural ≤ `(nfix n)` | admin.lisp `fnn-admin-authorize` → `fn-store-cfg-native-admin-authorize` |
| `fn-native-auth-parse-lines-within-the-operator-bound` | native-auth-profile | `(<= (len creds) (nfix n))` ⇒ the result's second element has length ≤ `(nfix n)` | (the parser of the next row) |
| `fn-native-auth-load-within-the-operator-bound` | native-auth-profile | no hypothesis: the installed configuration holds ≤ `(nfix n)` credentials | auth.lisp `fnn-native-auth-install` → `fn-native-auth-host-load` |
| `fn-bs-profile-namespace-counts-within-width` | store-profile-namespace | admitted profile ⇒ each count is within 1..2^32-1 | the accessors above |
| `fn-profile-upgrade-keeps-namespace-counts` | store-profile-namespace | `fn-profile-upgradep old new` ⇒ no count falls | io.lisp `fnn-command-upgrade-profile` (verdict `fn-profile-upgrade-verdict`) |

Old behaviour is an instance: every pre-existing witness in the test books
runs at the old figure (`*ncot-old*` 8192, credentials 128), and no existing
statement moved. The two lock theorems of native-admin gained the argument
only.

**Teeth** (test books):
- native-config-observation-tests: the three-generation history is `:ok`
  under 3 and `:budget` under 2. 8193 entries pass the size gate under
  2^20 (they fail `:decode` for content) and are `:budget` under 8192. A
  must-fail drops `true-listp` (`'malformed`, bound 5).
- native-admin-tests: the second record is accepted at generation 2 under
  bound 2, refused `:max-config-generations` with no jpub under 1. A
  must-fail drops acceptance.
- native-auth-profile-tests: 129 credentials load under 129 and under 2^20,
  and are refused `:too-many-credentials` under 128. Two credentials are
  accepted under 2 and refused under 1. A must-fail drops the
  collected-count hypothesis: two collected, bound 1.
- native-auth-admin-tests: a second login is accepted under 2 and refused
  under 1. Re-setting the existing login under 1 is accepted.
- store-profile-namespace-tests: the default, format-7 and raised
  profiles; a zero count is refused by name; a must-fail per hypothesis
  (a non-profile; no upgrade); an upgrade to 129/8193 is admitted, and the
  shrink is refused naming `max-config-generations`.

The load keystone has no hypothesis to tooth. A refusal installs the open
configuration, so the statement was proved without one; a first version
carried an acceptance hypothesis that had no teeth.

## Certification

persvati, w25 `acl2-literal`, 2 jobs, 300 s, `--affected-by` native-config-observation,
native-admin, native-auth-profile, native-auth-admin, native-config and
store-profile-namespace (32 roots):

- run-20260925T094904Z-f868, manifest
  `planning/evidence/manifests/certify-20260925T095003Z-3458907.json`:
  failed. `fn-native-auth-parse-lines-within-the-operator-bound` could not
  see that a refused finish carries no credential list. Twelve books in its
  closure failed with it; the config-generation books and the new book
  passed.
- run-20260925T095606Z-c762, manifest `certify-20260925T095632Z-3529797`:
  12 of 12 passed. native-auth-profile took 16.9 s, because two
  pre-existing loader theorems (`-accepted-is-config` 5.6 s,
  `-accepted-pins-policy` 6.4 s) now opened the octet and line bounds and
  the parser.
- run-20260925T100026Z-346a at 3916554e, manifest
  `certify-20260925T100051Z-3581003`: 12 of 12 passed after those two
  disabled the parser. The largest book is native-operator-tests at 8.1 s;
  native-auth-profile is below it. No book is over 10 s.

hbox, w28 `acl2-literal-4g`, 8 jobs, incremental over `/tank/fn/certcache`,
the default image closure (140 roots): 104 books certified at 78b91450+
(evidence dir `build/acl2/certify-20260925T095752Z-3093417` in
`/tank/fn/scratch/bounds-profile/tree`). Then native-auth-profile,
native-auth-admin and native-operator were recertified at b2d8f624 (dir
`certify-20260925T100328Z-3108350`).

## Native

hbox, developer image built at b2d8f624 from
`/tank/fn/scratch/bounds-profile/tree` (`fn-host-developer.core` 4b7bdfe5…,
launcher 0f40c674…; `planning/evidence/bounds-profile/image.sha256`). Runs
under `systemd-run --user --scope -p MemoryMax=24G`.

- `tests/test_native_profile_namespace.py` (SCN-050): 1 test, OK. Log
  `planning/evidence/bounds-profile/native-namespace.log`, sha256 75484e33….
  It asserts the image's exit codes.
- The same sequence by hand, with the outputs:
  `planning/evidence/bounds-profile/native-transcript.log`, sha256
  8ce64803…. Its `exit=` lines are the exit of the `grep` in the
  transcript's pipeline, not of the image. The unittest checks the image's
  codes.
  - `init --max-credentials 128 --max-config-generations 2`; status prints
    both.
  - `group create fn.two` configures generation 2. `group create fn.three`
    is refused with `ACL2 refused administrative publication:
    MAX-CONFIG-GENERATIONS`.
  - With 128 credentials in auth.toml, `principal set-password u129` is
    refused `too-many-credentials`.
  - `store upgrade-profile --max-credentials 200 --max-config-generations
    9000` is accepted; status prints 9000 and 200.
  - Then u129 is accepted (above the old cap), `principal list` has 129
    rows, and `group create fn.three` configures generation 3. The owner
    starts and loads the 129-credential file (unittest).
  - `--max-credentials 150` is refused `not-an-upgrade max-credentials`.

Finding, not this lane's: `operator status` prints `max-history-octets=0`
and `history-marker=0`, where `store upgrade-profile` prints
1099511627776 and `unmarked` for the same profile (see the transcript).
books/native-live-status.lisp `fn-nls-field` renders every value through
`fn-nls-nat` = `fn-nntp-decimal-field`. That prints 0 for 2^40, which is
above the NNTP decimal field's width, and for the word `unmarked`.

Also observed: `sh tests/test_native_io_progress.sh` on the laptop stops in
`fn-store-profile-max-transactions` (package `ACL2_*1*_ACL2` missing). That
runs before the config-observation stubs this lane changed, and in code
this lane did not touch. `tests/test_native_admin_authorize_boundary.sh`
passes. The source tests
(`tests.test_native_storage_codec.NativeConfigNamespaceSourceTests`,
`test_build_lists_check`, `test_native_operator_cli`) pass, 16 of them with
5 skipped.

## Not done, and why (named for the continuation)

| Constant | Field | Why not in this lane |
| --- | --- | --- |
| `*fn-cp-max-consumers*` 256 | 9 | consumer-position has 407 dependents, and `fn-cp-apply` (replay) also refuses a register past the cap. The right change is to remove the replay check (the decision refuses, and the profile only rises) and parameterize `fn-cp-statep`. That is a statement change across the consumer invariants, too wide for this budget. |
| `*fn-bpn-machine-max-records*` 4096 (+2x received) | 10 | Twelve BP books (the machine codec, invariants, receipt-send, progress, debt). BP ingress has no profile in hand (host/native/bp-node.lisp), and backlog PKT-139 (a never-answering neighbour fills it in about 2000 passes) needs a design for eviction as well as a larger bound. |
| `*fn-pol-max-members*` 64 | 13 | It bounds a member count inside a signed policy statement codec (`fn-pol-policy-of-items`). A profile-dependent decoder would let two nodes disagree on a signed statement's validity. The right bound is the record width (R), not a local field, and that needs a decision. |
| `*fn-cpp-max-generations*` 4096 | (T) | lane/bounds-p5, unmerged, rewrote the pack chain in checkpoint-publish, pack-retire and pack-chain. A link covers at least one record, so generations ≤ T, and T should bound the names with u32 names. Doing it now would conflict with that merge. |
| `*fn-bpa-max-article*` 32768, `*fn-bpa-max-octets*` 65538 | A, R | bp-adu has 156 dependents, and BP ingress (bp-ingress, host/native/bp*.lisp) carries no profile. bounds-blob owns the neighbouring frame and control widths. |

Also not proved: that the namespace after an accepted publication has
GENERATION entries (contiguity), so the writer and listing keystones are
composed in prose only. The admin's serialized credential file is not
proved within the loader's octet bound; it is checked (`:fault
:serialized-profile`).
