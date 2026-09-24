# Owner configuration proof-cost trial (GPT-6-Luna)

This bounded trial reduced the proof cost of
`fn-ocfg-crash-at-any-instant-recovers-the-live-generation` in
`books/owner-config.lisp`. The theorem statement, guard, and runtime
definitions were unchanged. The source patch is `fc4882d23daa6d90585ac8cf551e6073de4e00ce`
(`Reduce owner-config recovery proof branching`), based on
`4b2304b2d71e1717858123a90462a3115e7b1d92`. It adds one local projection lemma
and adjusts only the target theorem's hints: keep
`fn-ocfg-reconfig-okp` closed, expose its accepted-record conjunct, and avoid
rewriting the replay helper. The extracted theorem statement and pre-hint body
hash is `e7adc4428bbfb052e7959753125d44103a430cf59a78019becfa3f264b050302`.

The original hbox log is
`/tank/fn/gates/poll-live-group-repair-1d26-20260923/build/acl2/certify-20260923T232249Z-467250/books--owner-config.certify.log`.
It reports 9.74 s prover time (9.73 s proof), 5,262,889 steps, and 257 split
subgoals for the target; the whole book took 15.734 s. The splitter opened
`fn-ocfg-reconfig-okp` and record-acceptance definitions. A later full-run
baseline on the exact source family used for the patch, before the hint change,
was gate `cleanup-integration-4b2304b2-20260924`: target 10.63 s and 5,262,889
steps; book 17.001 s.

There were three bounded proof attempts. On the original source, disabling
`fn-cnode-record-acceptablep` failed in 0.10 s / 30,141 steps because the
accepted-record bridge was lost. A local projection from
`fn-ocfg-reconfig-okp` to its `fn-cnode-record-acceptablep` conjunct proved in
0.20 s / 50,603 steps, but the target with the reconfiguration predicate
closed still failed in 3.42 s / 1,753,315 steps. Its checkpoint retained the
positive accepted-record fact and the negated corresponding
`fn-cfg-record-acceptablep` fact at the live reservation count. The one
current-source follow-up then used the exact 4b gate read-only, after shared
dependencies were cached. The helper proved in 0.20 s / 50,603 steps and the
target proved Q.E.D. in 6.36 s / 3,142,017 steps (6.56 s for the encapsulate).

Root integrated the patch in source `a785ae03` and certified it in the full
incremental run recorded at
`planning/evidence/manifests/certify-20260924T010818Z-669581.json` (hbox gate
`cleanup-repaired-dfc4c384-20260924`, ACL2 8.7 / SBCL 2.6.8, w28 toolchain,
four jobs). That manifest reports `owner-config` and `owner-config-tests`
passed. In the certified changed source, the target took 5.24 s (5.23 s proof)
and 3,142,017 steps; the whole owner-config book took 11.26 s. The matching
baseline and changed-source full runs both used four jobs and the same hbox
toolchain/cache setup. Shared load was not controlled, so the wall-time change
is evidence for this run, not a causal guarantee. The prover-step reduction
from 5,262,889 to 3,142,017 is the clearer proof-work comparison. This reports
only the owner-config roots in that manifest, not a green claim for the whole
image closure.

The interactive session used `tools/proof_repl.py`, ACL2 8.7 / SBCL 2.6.8 via
`/tank/fn/toolchains/w28/acl2-literal-4g` (toolchain identity
`d5f2b9f0d2cf68c6074ea7046f4bd2e560d2984fe22d7e03f93045975ac889f0`). Two
failed tries preceded the passing try; a current-source startup also initially
found six missing dependencies and stopped before a theorem attempt. No
book-wide codec theory was opened, and no `skip-proofs`, theorem weakening,
guard change, or runtime-definition change was used. The bounded sample shows
this hint adjustment is effective for this target; it does not establish a
general model suitability claim.
