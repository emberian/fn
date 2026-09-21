# Native BP application join evidence — 2026-09-21

This packet exercises the W18 native TCPCL/BP application receiver against
the canonical native owner Store.  Python is the process harness and creates
the request with ACL2; both network endpoints and the Store owner are the
saved native `fn-host` image.

## Source and certification

- Branch: `w18/native-bp-app`
- Implementation revision: `be6e0ab` (the following commit archives this
  evidence).  The chain moves the shared bound-submission completion helper
  into `host/native/owner.lisp`, where native control and BP consume one
  implementation, and adds an ACL2-labeled immutable publication fault seam
  for the receipt-decision namespace-barrier witness.
- Persvati run `run-20260921T100110Z-cac3`, archived as
  `planning/evidence/manifests/certify-20260921T100118Z-2424932.json`: ACL2
  8.7/SBCL 2.6.8, jobs 4/effective 4, 88/88 closure books passed in 258.888s.
  Requested roots included `books/frame`, `tests/acl2/frame-tests`,
  `books/bp-native-app`, and `tests/acl2/bp-native-app-tests`.
- Persvati run `run-20260921T100836Z-3406`, archived as
  `planning/evidence/manifests/certify-20260921T100839Z-2496400.json`: ACL2
  8.7/SBCL 2.6.8, jobs 4/effective 4, 103/103 closure books passed in 861.19s.
  This supplied the remaining direct certificates required by the full native
  image.  Both manifests report no book failures and no forbidden-facility
  findings in the local source closure.
- Persvati run `run-20260921T103555Z-e118`, archived as
  `planning/evidence/manifests/certify-20260921T103559Z-2758143.json`: the two
  BP application roots passed after their assurance scope was corrected
  (8.927s, jobs 2/effective 2).
- Persvati run `run-20260921T104301Z-7fa7`, archived as
  `planning/evidence/manifests/certify-20260921T104305Z-2827099.json`: the two
  changed application-journal publication roots passed (3.561s, jobs
  2/effective 2).

## Native build and scenario

The full image was built on persvati with:

```text
FN_ACL2=$HOME/fn-tools/acl2-8.7/saved_acl2 sh tools/build_native_host.sh
```

The build completed with `FN_NATIVE_BUILD_LOADED`, produced a 279 MiB core,
and contained no uncertified-book or ACL2 error marker.  The focused scenario
then ran:

```text
FN_ACL2=$HOME/fn-tools/acl2-8.7/saved_acl2 \
FN_NATIVE_HOST=build/fn-host \
python3 -m unittest tests.test_bp_app_native -v
```

Result: 2 tests passed in 28.136s.  In the first scenario the native receiver
durably commits the owner Store record and FNRJ receipt decision, then is killed
before authoring the receipt bundle.  A second native receiver replays the
decision and returns the receipt when the native sender retransmits the request
in a new bundle.  The test observes one Store transaction, one article, and one
retention pin before and after restart; exact article bytes and BP provenance
survive; the sender's received receipt bytes equal the FNRJ replay projection.

The second scenario injects an actual `EIO` at the directory barrier selected
by the ACL2-issued `:receipt-decision` publication label.  The final name is
visibly linked, but the first receiver fences and exits 3 without authoring a
receipt.  Reopen repeats the namespace barriers, replays the decision, returns
the exact receipt, and leaves Store transaction/article/pin counts unchanged.

## Artifact digests

```text
b4923a8ada86503cde951d2a9f43934dd07dcc2b580830d9efd04b311fbd5b6a  build/fn-host
c2699fd6f548845edd53a4269d436b7aacc430c759d4d768395046b17cb3ce1d  build/fn-host.core
c701fd2742d0042ac4b72b6fd290af7d12c1878822a14775db28d6818185d4a8  build/native-host-build.log
741c3c4d504a8483a13c5899a5d4a80b2cbe11c453aba182cb1acbf4cf7d9830  host/native/owner.lisp
79eabbd565ca93228b7bac4f999fa56787b29bdd3cc9bd8a004c3e4251132102  host/native/bp-app.lisp
eaaac6cfe28fb6c89ca69369d75049729866875127886438c17e0f6e0530f846  host/native/immutable-publish.lisp
026ba6e07c3de2b4c25b0d3bf44ae07d38cc210bfb37fc87b4776c28603b55df  host/native/workflow.lisp
4b362527298c26d656b2f0d6bf22743edb697e1f357a8b204157185937bdba3e  books/app-journal.lisp
f6c0ef7b3b4580dd68faee18c6fd00f7d723194aca58e90df2c2af5fd65a21ba  books/bp-native-app.lisp
e1a6efc2f2b15509138d7ed2647cf5d071687fe565d1b3851f76b8f65328aa98  tests/test_bp_app_native.py
1f7f5d76446275355b76e853012d7e11a21013e52d86770e9c307af33922ec33  build/bp-app-native-test.log
```

The SHA-256 over those ordered `sha256  path` lines is
`4a86db3728bc309230708fb7a59526cc6258c32dd2cc5b7bde935eb11c40c254`.

## Scope

These are loopback two-process interoperability and restart witnesses.  They
do not claim external BP interoperability, power-loss qualification, or
coverage of every persistence cut.  The covered cuts are after the durable
receipt decision before receipt-bundle authorship, and a receipt-decision
namespace-barrier EIO after link.  The full replay/context/receipt-to-evolving-
Store trace invariant and remaining host-cut correspondence are open.
