# K5 byte-crash stable-prefix packet, 2026-09-23

The source was branch `implement/byte-store-k568`, based on
`11b8d53bb4ab764220f4db087cc762623993e470`. The root book's actual
passing ACL2 result is in
[`certify-20260923T181727Z-4066830.json`](manifests/certify-20260923T181727Z-4066830.json):
that run failed only because the then-current test book was red. The corrected
test book's actual passing result is in
[`certify-20260923T182257Z-4072178.json`](manifests/certify-20260923T182257Z-4072178.json).
[`certify-20260923T182540Z-4075797.json`](manifests/certify-20260923T182540Z-4075797.json)
then successfully reinstalled both selected roots at their unchanged final
source bytes. All three manifests carry exact closure digests and artifact
provenance; the reinstall alone does not prove ACL2 executed either root.
Its ACL2 8.7 launcher was `/tank/fn/toolchains/w28/acl2-literal-4g`, SHA-256
`9f73da2a84d664516033fb6e944c55b55d1f7206e9599cac46ca2b208de26aa8`.
Command: `python3 tools/farm.py submit hbox --jobs 2 --acl2 /tank/fn/toolchains/w28/acl2-literal-4g --cache /tank/fn/certcache --remote-root /tank/fn/gates/takeover-byte-store-k568 books/byte-store-stable-prefix tests/acl2/byte-store-stable-prefix-tests`; `farm.py wait hbox run-20260923T182538Z-13ac` exited zero.
`make check` passed after regenerating the ledger and tracking that manifest.

`fn-bs-stable-prefix-retained-by-byte-crash` proves that, **if** the byte
store is related to the file kernel and the image is admitted by the byte
crash predicate, the decoded durable transaction list is a prefix of the
scan and the scan contains at most one additional record. The proof uses
K1's exact scan decomposition, fenced-content/read lemmas and the
one-record read bound. It does not establish its own relation premise at
arbitrary host cuts; that is general K0. It does not prove the raw written
frame's octet provenance (K6) or that a completed transaction-directory
fence forces the candidate into every image (K8).

The test book drives the actual frontier, record, finish, next frontier,
and next record programs. At the second `record-linked` cut, the first
record is durable; dropping the pending transaction link scans one record
and applying it scans both exact codec-decoded records. The two counterexamples
separate the theorem's hypotheses: two physical pending links beyond an
empty durable prefix violate the one-record bound when the relation is
removed, while a related first-publication state cannot be paired with a
forged two-record image if the crash-image premise is removed.

Read-only T16b feasibility audit on hbox: `/tank/fn/gates` is mounted from
ZFS pool `tank` (`rw,noatime,xattr,posixacl,casesensitive`), on Linux
6.11.0-29-generic. `tank` was online with about 408 GiB free; its data
vdev is a mirror of two HDD partitions and it has an NVMe special vdev.
`dmsetup`, `zpool`, and `zfs` binaries exist, but unprivileged `dmsetup ls`
failed with permission denied. There was no `/tank/fn/scratch` path. The
current `tank` is shared with `/tank/fn/node` and gate artifacts, so no
fault or snapshot rollback was attempted. T16b needs an explicitly isolated
disposable block device or loop-backed scratch pool, privileged device-mapper
access for a fault run, a separately identified filesystem/device/barrier
profile, a frozen source-matched image and an independent observation of
post-cut files and recovery. Process SIGKILL evidence does not qualify
power loss or firmware flush behavior.
