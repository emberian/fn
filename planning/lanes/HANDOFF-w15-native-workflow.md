# W15 native workflow and receipt persistence handoff

## Frozen commits and interfaces

Branch `w15/native-workflow` is based on `e71c0de`.  The packet is:

- `978be68`: `books/journal-publish.lisp` owns immutable no-replace publication
  phases and `:durable` / `:refused` / `:uncertain` classification.
- `c6de368`, `680ece8`: native FNWF/FNRJ replay and operator operations, logical
  frame wrappers, Store-bound enqueue, and actual restart/fault tests.
- `d307c40`: `books/app-journal.lisp` moves filenames, recovered frontier,
  limits, aggregate accounting, initialization order and resolution headroom
  into the called ACL2 operation.  Append carries the recovered frontier and
  never rescans the old directory.  Empty open explicitly resets its domain.
- `219205f`: exposes modeled publication observations for process-death tests.

The shared raw executor is:

```lisp
(fnn-immutable-publish-effect
 publication stage final final-directory octets
 :cleanup-directory staging-directory
 :observer optional-callback)
```

`publication` must be an ACL2-authorized `(fn-jpub-initial t)` issued by the
caller's allocation machine after it observes its exclusive lock and absence
of ACL2's exact selected name.  The executor checks that state and cannot mint
authority.  Its result is exactly `:durable`, `:refused`, or `:uncertain`.
The optional callback receives `(point publication)` after `:file-barrier`,
`:link-result`, and successful `:directory-barrier` observations.  The app
caller obtains its capability from `fn-aj-authorize`; checkpoint and BP
evidence callers must retain their own ACL2 allocation/frontier contract.

`fnn-app-open` takes an already-open `fnn-store`; it neither opens a second
Store nor resets `fn-store-sn`.  The standalone `app-journal` command opens one
Store and one application journal solely to provide an actual operator and
restart witness.  An integrated owner should call the store-parametric
`fnn-workflow-*` / `fnn-receipt-*` functions while holding its existing service
lock.

## Evidence

Source/tool record: macOS 26.6.1 (25G76), Python 3.14.7, ACL2 8.7 on SBCL
2.6.8.  The native image was explicitly the DTN profile, not the default
reader image:

```sh
FN_NATIVE_BUILD=host/native/build-dtn.lisp \
FN_NATIVE_IMAGE=build/fn-host-dtn \
FN_NATIVE_LOG=build/native-workflow-build-v3.log \
sh tools/build_native_host.sh
```

It built a 283 MiB core.  Against that image:

```sh
python3 -m unittest -v tests.test_native_app_journal
```

passed four tests.  The witnesses cover Store-bound enqueue and outstanding
status after process restart; pre-link stage `EIO` reported as refused with no
intent; final-directory barrier `EIO` reported as uncertain with a visible
intent, no outcome, a fenced retry, and no equal-byte durability shortcut; and
native persistence of request context, receipt intent, committed decision,
then identical nonempty receipt regeneration in two fresh processes.

Existing adapters remained green when run in their isolated supported test
processes:

```sh
python3 -m unittest -v tests.test_workflow_journal tests.test_receipt_journal
python3 -m unittest -v tests.test_workflow_restart
```

The first ran 32 tests and the second ran four.  A prior combined invocation of
all three modules in one Python process hit the known ACL2 theory reload error
(`FN-CRYPTO-SEAM-INTERNALS is in use as a theory`); neither isolated invocation
reproduced it.

ACL2 certification of `books/app-journal` and
`tests/acl2/journal-publish-tests` passed locally and on both farms.  The remote
commands, after checking both hosts idle, were:

```sh
python3 tools/farm.py submit hbox --jobs 4 \
  books/app-journal tests/acl2/journal-publish-tests
python3 tools/farm.py submit persvati --jobs 2 \
  books/app-journal tests/acl2/journal-publish-tests
```

Farm runs `run-20260921T084920Z-5fa0` and
`run-20260921T084920Z-abea` finished with exit code 0.  Their archived manifests
are `planning/evidence/manifests/certify-20260921T084924Z-1881095.json` (hbox)
and `planning/evidence/manifests/certify-20260921T084923Z-1749638.json`
(persvati).  Both pin `books/app-journal.lisp` digest
`08459e316b8fd548f6317d99ecd9b8166e9ecdf4f6bd233a397be4b0e8f921f0`
and test digest
`64d14dfebca71b129fa7a942205c539c7bdb43ce114264b2a0bf7e5794bcad9f`.

## Scope limits

The actual native owner callback was not frozen when this packet was built, so
owner submission does not yet invoke FNWF.  The receipt operation is likewise
not yet called from the TCPCL receive handler.  These are explicit composition
joins, not additional journal implementations.  The DTN operator path, its
immutable persistence, replay, receipt regeneration and fault classifications
are implemented and exercised.  Filesystem durability remains A-HOST; these
proofs do not qualify a drive or filesystem.  Staging namespace reconciliation
on startup belongs to the W15 storage-initializer packet and is not duplicated
here.  The root agent owns registry, Makefile and milestone updates.
