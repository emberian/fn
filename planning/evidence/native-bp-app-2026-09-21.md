# Native BP application join evidence — 2026-09-21

This packet exercises the W18 native TCPCL/BP application receiver against
the canonical native owner Store.  Python is the process harness and creates
the request with ACL2; both network endpoints and the Store owner are the
saved native `fn-host` image.

## Source and certification

- Branch: `w18/native-bp-app`
- Final source revision: `190c023dfe2812d891cccea054a5651668fa4c90`
- Deployable native source was last changed by `33159f2`; the three later
  commits change only the focused Python test.  The native source hashes below
  match the final revision.
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

Result: 1 test passed in 6.305s.  The first native receiver durably commits the
owner Store record and FNRJ receipt decision, then is killed before authoring
the receipt bundle.  A second native receiver replays the decision and returns
the receipt when the native sender retransmits the request in a new bundle.
The test observes one Store transaction, one article, and one retention pin
before and after restart; exact article bytes and BP provenance survive; the
sender's received receipt bytes equal the FNRJ replay projection.

## Artifact digests

```text
891a6cb27a615f2d3cce21be621dfcd3c0b73ffac7d829f89e50bc88f7b53ec3  build/fn-host
fe8a1a7fec169910c33981a79ee56c71a05e8ab897a9001153548ea47497a6ca  build/fn-host.core
cf3f4fb871989e3ee187c9eb664a602876e4df37e9390670144511e26bf5ce61  build/native-host-build.log
31aeadfcab1afedb32a708ad0d792fd7b025c00dde0360dbba108dd53a7ba823  host/native/bp-app.lisp
543dc4467c559204d47bac8a988dbd1aa006628aea6ec25d097af6f1aec245b6  books/bp-native-app.lisp
a9e321b40034b0cb4d6de421b09cc82cd10d551abb9d6dc8755591d9c13424e1  tests/test_bp_app_native.py
0ec85a22dc54851110ecc4eda25f72793001d7387dcea1599bfd918f022e9de1  build/bp-app-native-test.log
```

The SHA-256 over those ordered `sha256  path` lines is
`f35a963f45d5d763243b4b4528e96bcbe82cc2d2b8c5853a43418be5763273e4`.

## Scope

This is one loopback two-process interoperability and restart witness.  It
does not claim external BP interoperability, power-loss qualification, or
coverage of every persistence cut.  The modeled death point is after the
durable receipt decision and before receipt-bundle authorship.
