# Byte crash-image reopen after Store topic admission

The Store v6 observed reopen checks topic replay separately from article,
identity, and consumer replay. `fn-bs-crash-image-reopens` previously derived
consumer replay from `fn-csi-full-relationp` and K2, but passed no topic fact to
`fn-sn-recovery-admissible-image-reopens`. The repaired theorem, its
acknowledged-record dependent, and the sweep-cut dependent now require
`fn-sn-observed-topic-okp` of the exact scanned record list. This is a
conditional K4 repair, not a theorem that every physical crash image has a
valid topic prefix.

`tests/acl2/byte-store-scan-tests.lisp` builds a framed FNST topic anchor
after a completed consumer bootstrap using the actual frontier, record, and
finish byte programs. The anchor's source ID is a valid subject identity and
its authorization reference is structurally valid, but no accepted authorship
event precedes it. The image scans to both Store events with contiguous
sequence numbers. The test proves its `fn-bs-crash-imagep` witness, evaluates
the byte/kernel relation and `fn-csi-full-relationp`, checks identity and
consumer replay, then checks that topic replay fails and the actual
`fn-sn-open-observed` returns a refusal. Its `must-fail` is on that exact
reopen conclusion. The node-side relation witness is reconstructed from the
generic Store/node/consumer replay of the physically produced file history;
it is not a claimed served topic-prepare trace. Maintaining topic validity
through every actual Store crash cut is the separate topic/crash bridge.

On isolated base `0f3b9de5`, persvati ACL2 8.7 with executable
`/home/ember/fn-gates/toolchains/w25/acl2-literal` (SHA-256
`346b7ee183e8c291cb61cf31be75a332caf329fa74b4995921cbb224208f2c08`,
toolchain identity
`1b4169e9c5825a4e1fc827767f00470ceafc459619e0a4fd522c48f1ba964286`)
first admitted all three changed theorem statements in a bounded proof REPL.
The shared cache lacked `books/store-sweep` and three current test parents;
only those four parents were bootstrapped. The final source-matched selected
`--jobs 2 --timeout-seconds 120` run was
`run-20260924T052420Z-2a40`,
[manifest](manifests/certify-20260924T052426Z-604939.json): both roots passed,
with book proof time 2.677 s and test time 3.131 s. The source digests in that
manifest are `1443e5ee5c16d9829f5aec107891d2a2c3c984ae37af50896fbfa644ccca0e1b`
for `books/byte-store-keystones.lisp` and
`73c55a330d813f64a4a67370fbcf7139d00107629f82c5a24692674312489bf3`
for its test. No full closure or native image run was submitted from this lane.
The sole changed-book dependent, `tests/acl2/byte-store-sweep-tests`, passed
the selected one-job `run-20260924T052721Z-7fdf`
([manifest](manifests/certify-20260924T052726Z-633730.json));
`green_check.py --changed-since 0f3b9de5 --summary` reports two changed roots,
one dependent and zero not green at the bytes this merge carries. `make check`
passed on the isolated packet.

Open: a maintained actual Store topic-prefix relation must derive the new
observed premise at the concrete crash image. The byte/kernel relation at
every served call entry, physical syscall/barrier outcomes, and power-loss
qualification also remain open.
