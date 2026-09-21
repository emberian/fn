# Native BP application join evidence — 2026-09-21

This packet exercises the W18 native TCPCL/BP application receiver against
the canonical native owner Store.  Python is the process harness and creates
the request with ACL2; both network endpoints and the Store owner are the
saved native `fn-host` image.

## Source and certification

- Branch: `w18/native-bp-app`
- Implementation revision: `fc78031` (the following commit archives this
  evidence).  This revision also moves the shared bound-submission completion
  helper into `host/native/owner.lisp`, where native control and BP consume one
  implementation.
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

Result: 1 test passed in 8.691s.  The first native receiver durably commits the
owner Store record and FNRJ receipt decision, then is killed before authoring
the receipt bundle.  A second native receiver replays the decision and returns
the receipt when the native sender retransmits the request in a new bundle.
The test observes one Store transaction, one article, and one retention pin
before and after restart; exact article bytes and BP provenance survive; the
sender's received receipt bytes equal the FNRJ replay projection.

## Artifact digests

```text
b8cf7de8f74fd1f4080fdc54af8e70199a439a44f01b4f963bbaf7747c8e8bd0  build/fn-host
d5a7257637b6d0e40831ed026d133308a4a4e483211ef21f94ead28c6827220b  build/fn-host.core
6ca5d7b19bbb3c1ff8725da9f6857f8adb567d1ac4e00fa4ad6eeba9802812c9  build/native-host-build.log
741c3c4d504a8483a13c5899a5d4a80b2cbe11c453aba182cb1acbf4cf7d9830  host/native/owner.lisp
79eabbd565ca93228b7bac4f999fa56787b29bdd3cc9bd8a004c3e4251132102  host/native/bp-app.lisp
543dc4467c559204d47bac8a988dbd1aa006628aea6ec25d097af6f1aec245b6  books/bp-native-app.lisp
a9e321b40034b0cb4d6de421b09cc82cd10d551abb9d6dc8755591d9c13424e1  tests/test_bp_app_native.py
fb1e9bd765353fa93047bf019093efefbff7abbb82d1fdb8cfcc636c21fbd256  build/bp-app-native-test.log
```

The SHA-256 over those ordered `sha256  path` lines is
`b5be81b52827820750d237bfa4397071a27af530d0bf58eb3c989ec591bc5453`.

## Scope

This is one loopback two-process interoperability and restart witness.  It
does not claim external BP interoperability, power-loss qualification, or
coverage of every persistence cut.  The modeled death point is after the
durable receipt decision and before receipt-bundle authorship.
