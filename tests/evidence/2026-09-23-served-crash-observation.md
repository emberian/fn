# Served-owner process-death byte observation, 2026-09-23

This is an executable correspondence check for selected process-death cuts,
not a power-loss qualification or a literal physical `fn-bs-crash-imagep`
claim. The host-called path is `fnn-owner-control-submit-serialized` in
`host/native/owner.lisp`, through `fnn-owner-attempt`,
`fnn-advance-frontier`, `fnn-owner-publish-prepared`, `fnn-publish` and
`fnn-finish`. The test invokes `operator CFG post` against the served
`operator CFG run` owner. A prior post receives a successful answer before the
candidate's owner is killed; after the kill the test reopens and rereads that
prior article byte for byte. The candidate is checked against the cut's
absent/present contract.

`tests/test_native_served_crash_model.py` imports the seed and killed physical
directory images. The chosen `books/byte-store-programs.lisp` prefix includes
every issued syscall and observation up to the named cut. For SIGKILL after
those syscalls return, it selects `:new` for each pending write and `:apply`
for each issued pending namespace operation, checks that vector with
`fn-bs-crash-choicesp`, and computes `fn-bs-crash`. ACL2 then evaluates
`fn-bso-served-image-agree` over the computed image and the actual physical
image: exact visible names and octets plus hard-link alias equality across
root, transactions and staging. Physical inode numbers are only compared for
equality; the relation allows an injective renaming to logical inode IDs and
does not read inaccessible unlinked inodes. ACL2 also runs `fn-bs-scan-store`
and `fn-sn-open-observed` over the physical image. Positive fixtures and
separate one-octet corruption, missing-name and same-content/broken-alias
negatives are in `tests/acl2/byte-store-observation-tests.lisp`.

The post cut set is `frontier-replaced`, `record-staged-durable`,
`record-linked`, `record-durable`, `finish-consumed`, `finish-durable`: it spans
prepublication, link uncertainty, the durable directory barrier and both
finish boundaries. `recover-barrier-1` through `recover-barrier-5` now address
the five distinct native hooks while each maps to the corresponding occurrence
of the model's `recover-barrier` cut. The recovery test first leaves a staged
orphan by killing a developer raw post, then starts a served owner whose
startup recovery dies at the selected barrier. It checks the ACL2 recovery
program image, completes recovery, and confirms the prior acknowledged article
is identical while the unpublished candidate stays absent. An unmodeled or
unreachable named cut fails the test with its cut/occurrence; none is accepted
as a skip.

The hbox selected-root ACL2 run was
`run-20260923T142322Z-9816`, with manifest
`/tank/fn/gates/takeover-crash-differential/build/acl2/certify-20260923T142323Z-3848034/manifest.json`.
The w28 toolchain identity was
`d5f2b9f0d2cf68c6074ea7046f4bd2e560d2984fe22d7e03f93045975ac889f0`.
Four unchanged dependencies installed from `/tank/fn/certcache`; the new book
and its test certified in 0.992 and 0.950 seconds respectively. The initial
two failed attempts found an unnecessary reflexivity proof that was removed;
the successful run is the cited one. No other book closure was certified for
this test-only relation.

The source-matched developer image was built with `swarm-build sh
tools/build_native_host.sh`, `FN_NATIVE_PROFILE=developer`,
`FN_OPENSSL_PREFIX=/tank/fn/toolchains/openssl-3.5.8`, and
`FN_ACL2=/tank/fn/toolchains/w28/acl2-literal-4g` from
`/tank/fn/gates/takeover-crash-differential`. Its core SHA-256 was
`9f37b2d610d13cd1c0ef19e4abf4d6188a4bd9928f6e0b5bc440b1ae1abd8a64`
and the loaded `host/native/io.lisp` SHA-256 was
`eef98d0b79c9bb294eff9af6916d934030714ef6dcf9ab0b7473a456a48dcaee`.
The baseline 2026-09-23 developer image core was
`c53ca0cc7cea8ddbbe0796aebaec3762acb88d8b25f4882b583f8318bb498fca`;
its six post cuts passed the same visible observation test before the ordinal
recovery host change. Runtime: Python 3.12.7, Linux
6.11.0-29-generic, source-matched developer image, hbox ZFS isolated temporary
stores under `/tank/fn/gates/cdiff` (removed after the run),
`python3 -m unittest tests.test_native_served_crash_model`: two test methods,
all eleven named process-death cuts passed in 32.933 seconds. The existing
low-level raw-post test's thirteen post cuts also passed with the corrected
native CLI invocation in 32.917 seconds on hbox tmpfs fixtures. The latter is
separate from served-owner evidence.

Open: the visible relation is narrower than `fn-bs-crash-imagep` over a full
inode table; no theorem yet proves that this projection preserves every
decoder/recovery observation. The all-new/all-applied process-death vector
does not exercise torn or lost dirty writes. The seven other served post cuts,
`recover-replayed`, staging cleanup, injected error callbacks, repeated
recovery deaths and a combined image after acceptance-stamp/profile changes
remain to be checked. ZFS process death does not qualify media durability or
power loss.

## Scanner projection theorem extension

`fn-bso-served-agreement-preserves-scan` in
`books/byte-store-observation-scan.lisp` is a real ACL2 theorem over
`fn-bs-scan-store`: visible image agreement, identical **ordered** transaction
names, and a successful model scan imply identical physical and model scan
values. It uses `fn-bs-lookup`/`fn-bs-content` at visible names, so physical
inode IDs can be renamed and unlinked unreachable model inodes are hidden.
Its test book evaluates two actual framed records under distinct physical
inode IDs; `must-fail` cases remove, in turn, visible agreement (damaged
frame), ordered transaction names (reversed alist), and successful model scan
(malformed duplicate-name root). The last case shows why set/count agreement
alone is insufficient at malformed roots. The theorem is about scanner input
and result; it does not prove full recovery transition equivalence or a
converse for every physical crash image.
`fn-bso-served-agreement-preserves-open-by-scan` is an explicit congruence
corollary for the `fn-sn-open-observed` call with the same groups and capacity:
equal scan results supply equal frontier and record inputs. The scan theorem
is the keystone; this corollary does not simulate the recovery program.

The exact hbox ACL2 selected-root run was `run-20260923T145139Z-50e1`, with
manifest `planning/evidence/manifests/certify-20260923T145142Z-3880387.json`.
It certified the new theorem book and its test at toolchain identity
`d5f2b9f0d2cf68c6074ea7046f4bd2e560d2984fe22d7e03f93045975ac889f0`;
the final run installed 70 of 72 closure books and certified both changed
roots. Both passed. The served runtime
test evaluates these premises and exact scan equality at all six post cuts
and five recovery-barrier cuts. On hbox, `python3 -m unittest
tests.test_native_served_crash_model` passed all eleven named cuts in 29.764
seconds, using the self-contained developer image at source
`f0b8b166a3d5d56124ba45114bda0bd34affa5b8` with core SHA-256
`66115e4374e71d107dc94f9f214cc0aeb68ac933334b83ee46d777944c958747`.
The image's source predates this theorem book but its native served fault
hooks are the same; ACL2 in the source tree loads the new book for the check.
The raw native crash suite also passed its thirteen post cuts (six unittest
methods, 36.269 seconds) with the new scanner premises and equality checked.
