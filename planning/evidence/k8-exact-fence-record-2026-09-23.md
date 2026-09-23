# Exact record after the transaction directory fence, 2026-09-23

At the final source, ACL2 8.7 on hbox certified the changed book in
[`certify-20260923T191637Z-4155049.json`](manifests/certify-20260923T191637Z-4155049.json)
and the corrected test book in
[`certify-20260923T192024Z-4160221.json`](manifests/certify-20260923T192024Z-4160221.json).
The earlier run's test failed because `assert-event` tried to evaluate the
constrained, non-executable `fn-bs-crash-imagep`; the final test instead
proves its legal-choice implication through `fn-bs-crash-imagep-suff` and
evaluates the observable scan. The final run exited zero. Both runs used the
`w28/acl2-literal-4g` executable, `--jobs 2`, and the cached dependency
closure. The command was `python3 tools/farm.py submit hbox --jobs 2 --acl2
/tank/fn/toolchains/w28/acl2-literal-4g --cache /tank/fn/certcache
--remote-root /tank/fn/gates/takeover-byte-store-k8
books/byte-store-record-fence tests/acl2/byte-store-record-fence-tests`.
The prior durable-record-only packet is separately certified in
[`certify-20260923T190519Z-4130438.json`](manifests/certify-20260923T190519Z-4130438.json).

`fn-bs-k8-pending-link-fence-durable-records` proves that a related
`:record-attempted` byte/kernel pair **with a pending transaction link**
has, after `fn-bs-fence-dir :transactions`, exactly its old decoded durable
record list followed by the kernel candidate. The proof passes through the
same decoder read of the pre-fence view, the fenced inode's octets, the
pending link name, and the one-more-record list rule. The test reaches the
second actual P-RECORD publication after the first record is durable.

The pending-link premise is necessary under the current relation. At an
actual pre-link cut of that second program, advancing only the logical
kernel with `fn-sf-record-link-result :ok` produces a related
`:record-attempted` pair with no physical link. Fencing then retains only
the first record. This is a counterexample to the older phase-and-relation
only K8 statement; the corrected specification names the issued-link
premise. The host/model call-trace obligation that the real `:ok` result
follows an issued link is part of K0, not proved by this packet.

`fn-bs-k8-pending-link-fence-keeps-authority-list` proves that fencing
moves the pending link target into the durable transaction directory
without changing the authority inode list. Together with unchanged inode
content and fencedness it establishes
`fn-bs-k8-pending-link-fence-preserves-relation`.
`fn-bs-k8-issued-link-fence-crash-scans-exact-candidate` then applies K1's
crash-image scanner decomposition to **every** modeled post-fence crash
image, producing exactly `ks.records ++ [ks.candidate]`. The test book has
a reachable two-record publication and separate violating cases for the
relation, phase, issued-link and crash-image hypotheses. The phase case is
a related recovery-window state with an outstanding link but no candidate.

K6 raw-frame write provenance, general K0 call-trace establishment, and
physical barrier qualification remain open. In particular this model
theorem does not prove that the native host's callback phase is coupled to
an issued link, or that a physical filesystem honors the model's fence.

Root current-source integration passed the book and test on hbox in `run-20260923T192506Z-be01`, [manifest](manifests/certify-20260923T192514Z-4168191.json), over the schema-1 authored-record dependency closure. The two-root certification took 6.108 seconds with matched cached dependencies and two jobs; changed-root checks and `make check` passed. The hypotheses and remaining physical/K0 boundaries above are unchanged.
