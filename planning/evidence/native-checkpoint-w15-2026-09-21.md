# Evidence: native checkpoint adoption (w15)

Date: 2026-09-21.  The final implementation and test revision before this
evidence record is `76cd4ded34f0d1887e8d313765d209161532fe6e`.  The hbox
runtime snapshot was `/tank/fn/lanes/w15-native-checkpoint`.  These digests
were identical in that snapshot and the source worktree:

```
2971cbdf4f215ba776eb1c3eb9c5f31723f14dc46b5124fe92e5735bb111f1f1  books/checkpoint-publish.lisp
dda9326d01099a7e66399b452deff43e3775f7d51d6ed0f55cced089feee93b5  tests/acl2/checkpoint-publish-tests.lisp
891e419d461f7335c6ba2058f076084b718ba1182e79a94234695391098b9282  host/checkpoint-host.lisp
46690f8926c9dca03c77016e42596faa748c6c3c68d74a15f644fa2c1d1f0f5f  host/native/checkpoint.lisp
7eafafec1135fb3413e709b0718388322138b63eeaee20875bac739259ee82b3  host/native/io.lisp
94acfb22619efab81a360d369bd8fd3a1b523c5af68a51de6eb21b12aaf43e4c  host/native/build.lisp
ecdfb9742ebcea59bee71220aa3cb9082a57158e885e127020cc4c1969602057  tests/test_native_checkpoint.py
71105bceeb3c220f6f3675c2070411f4b3fc233ff7f4d77465c167d09e822334  specs/checkpoint.md
```

The native runtime calls ACL2 for generation allocation and exhaustion,
immutable-publication authority, checkpoint framing/opening, marker phase
actions and results, and checkpoint restoration/differential comparison.  The
host executes the selected filesystem operations.  Full journal replay stays
authoritative; checkpoint restoration is a diagnostic comparison and does not
replace the live store state.  Python below is an interoperability oracle, not
a deployed runtime dependency.

## Certification

The bounded hbox certification used ACL2 8.7 at
`/tank/fn/acl2-8.7/saved_acl2`, executable SHA-256
`64030dda0b03bbb6cf50984889f5ce1e2ba867b6ce3c9a65403afc44f9b4fdb5`,
SBCL 2.6.8, and at most four ACL2 jobs.  The commands were:

```
python3 tools/farm.py --jobs 4 --closure submit hbox \
  books/checkpoint-publish tests/acl2/checkpoint-publish-tests
python3 tools/farm.py --wait-seconds 1800 wait hbox \
  run-20260921T085406Z-abab

roots=($(python3 tools/proof_artifacts.py roots --profile default))
python3 tools/farm.py --jobs 4 --closure submit hbox $roots
python3 tools/farm.py --wait-seconds 1800 wait hbox \
  run-20260921T090010Z-2430
```

The owned closure passed 40/40 books in 145.051 seconds.  The actual default
image root union passed 107/107 books in 317.224 seconds.  The complete
generated manifests are
`planning/evidence/manifests/certify-20260921T085413Z-1889467.json` and
`planning/evidence/manifests/certify-20260921T090013Z-1900264.json`.
They record every source and certificate digest and the exact tool identity.
The final wrapper and test-harness commits changed no certified ACL2 source;
the book and test-book digests above are the certified bytes.

The default artifact set was then load-checked with:

```
python3 tools/proof_artifacts.py acquire --profile default \
  --cache /home/hbox/.cache/fn-certs \
  --acl2 /tank/fn/acl2-8.7/saved_acl2
```

It loaded artifact set
`e7fb5cf53c83a33a5716215088faa1f2906ba4d9a4deaab966ddefbb88f96521`
with 107 books and no rejected candidate.

## Saved image and native tests

The final saved image was rebuilt with:

```
FN_ACL2=/tank/fn/acl2-8.7/saved_acl2 sh tools/build_native_host.sh
```

The 449-byte launcher has SHA-256
`754c581969688de81d09ed64f65348d2c1125d26c0cd6c88f26785a214bc1dbf`;
the 276,624,520-byte core has SHA-256
`125d0547391b325499706b27379903e126f07ce673c3bc8b78357d13233f8f1b`.
The focused command was:

```
FN_ACL2=/tank/fn/acl2-8.7/saved_acl2 \
FN_NATIVE_HOST=/tank/fn/lanes/w15-native-checkpoint/build/fn-host \
python3 -m unittest -v tests.test_native_checkpoint
```

All 5/5 tests passed in 6.343 seconds.  They cover native initialization,
post, reopen, native/Python cross-open with byte-identical generation and
selection frames, malformed and truncated selected data, missing selected
data, corrupt-unselected isolation, distinct refused and uncertain exits,
and six deterministic SIGKILL cuts after ACL2-observed candidate and marker
file, namespace/replace, and directory-barrier phases.

The existing Python checkpoint regression was also run against the corrected
state-threaded host wrapper:

```
FN_ACL2=/opt/homebrew/bin/acl2 \
python3 -m unittest -v tests.test_checkpoint
```

All 6/6 tests passed in 303.355 seconds, including its 128-record suffix
replay case and existing process-death cut matrix.

This evidence does not claim suffix-only fast recovery: native recovery still
performs full authoritative replay.  The host still recognizes canonical
`generation-N.fncp` names at the filesystem boundary; an ACL2-owned decoder
for that namespace grammar remains recorded specification debt.
