# Owner configuration proof-cost trial (GPT-6-Luna)

This bounded proof-engineering trial investigated the expensive event
`fn-ocfg-crash-at-any-instant-recovers-the-live-generation` in
`books/owner-config.lisp`. Its statement and pre-hint body are byte-identical
between the original certified source at `1d26e01f` and the trial lane based on
`caa917ac` (SHA-256 of the extracted statement/body:
`e7adc4428bbfb052e7959753125d44103a430cf59a78019becfa3f264b050302`). The
full book digests differ: original `f0afb75441e07ffd044aaae373e4839217cb8530f0273431cfaf7562bd1f1747`,
current lane `7b4518bc1ee09acf84a3d8c739a1bc8d1c0ce664df785c96e3cb6b962c9ae197`.

The original hbox certification log is
`/tank/fn/gates/poll-live-group-repair-1d26-20260923/build/acl2/certify-20260923T232249Z-467250/books--owner-config.certify.log`.
It reports 9.74 s prover time (9.73 s proof) and 5,262,889 prover steps for
the target event; the manifest reports 15.734 s for the entire book. ACL2's
splitter note shows 257 subgoals, primarily from opening
`fn-ocfg-reconfig-okp`, together with record-acceptance definitions. The
baseline is a measurement of the old source and hbox conditions, not of the
current lane.

The trial used ACL2 8.7 / SBCL 2.6.8 through the w28 launcher
`/tank/fn/toolchains/w28/acl2-literal-4g` (toolchain identity
`d5f2b9f0d2cf68c6074ea7046f4bd2e560d2984fe22d7e03f93045975ac889f0`) and
`tools/proof_repl.py` on hbox. The exact original gate supplied 113 compatible
cached dependencies. Two theorem proof tries were submitted, both on the
original source; neither changed the theorem statement, guard, or runtime
definition:

1. Removing `fn-cnode-record-acceptablep` from the enabled theory and disabling
   it caused a 0.10 s failure (30,141 steps). The checkpoint lost the bridge
   from the accepted live record to the replay obligation.
2. A local projection fact from `fn-ocfg-reconfig-okp` to its
   `fn-cnode-record-acceptablep` conjunct proved in 0.20 s (50,603 steps).
   Using that fact while keeping `fn-ocfg-reconfig-okp` closed reduced the
   target attempt to 3.42 s (1,753,315 steps), but the target still failed.
   Its remaining checkpoint contained both the positive
   `fn-cnode-record-acceptablep` fact and the negated corresponding
   `fn-cfg-record-acceptablep` at the live reservation count. The likely next
   theorem-local adjustment is to open `fn-cnode-record-acceptablep` while
   keeping `fn-ocfg-reconfig-okp` closed, so the direct accepted-record
   conjunct is visible without the 257-way reconfiguration split. This is a
   candidate, not a proved result.

The single authorized follow-up startup against the `caa917ac` lane source
could not load a compatible cached dependency set. With
`FN_ACL2=/tank/fn/toolchains/w28/acl2-literal-4g` and
`FN_CERT_CACHE=/tank/fn/certcache`, `proof_repl.py start` reported six missing
current-source dependencies: `nntp-auth`, `owner`, `owner-fault`,
`owner-invariants`, `peer-inbound`, and `served`. It stopped before creating an
ACL2 session or attempting the theorem. Root will populate the shared cache
with the combined incremental run before a current-source retry.

No source or theorem file was changed, no certification was run, and no
speedup is established: the only faster target proof attempt failed. This
trial demonstrates a useful diagnosis and a plausible next hint, not a Luna
suitability result; two failed proof attempts are too small a sample for that
claim.
