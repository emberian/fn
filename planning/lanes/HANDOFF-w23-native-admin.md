# Handoff: W23 native administrative configuration

`books/native-admin.lisp` owns the bounded administrative plan and the
publication authorization.  The only accepted command shapes are `group
create NAME`, `group retire NAME`, and `capacity DECIMAL`; the plan is
`fn-native-admin-plan` over bounded ASCII octet words.  The public native
operator is owned by the integration lane.  Its private executor is
`fnn-admin-execute ROOT PLAN` in `host/native/admin.lisp`, loaded before the
operator, and it must receive the already ACL2-normalized plan rather than
parse group or capacity input itself.

The executor opens the existing Store through its nonblocking writer lock.
An active owner is consequently an explicit refusal; it never starts a second
owner.  It supplies raw clock observations to
`fn-native-admin-clock-observation`, which accepts only a configuration-codec
representable stamp.  It then uses the existing Store reconfiguration wrapper
to obtain the exact durable record.  The logical
`fn-native-admin-publication-authorize` binds the held lock observation, the
observed final-name set, configuration replay, candidate reopening, the next
generation, `config/%08d.cfg` canonical name, and the `fn-jpub` initial state.
Raw Lisp only validates and interprets that accepted authorization for the
shared immutable publisher.  Publisher uncertainty fences the live Store and
exits as indeterminate; it is never treated as refusal or success.

After a durable publication, `fnn-admin-verify-under-lock` calls the existing
recovery observation while the same exclusive writer lock is still held.  It
therefore cannot mistake a later administrator's generation for a defect in
the completed command.  A verification diagnostic fault fences the in-memory
Store and is reported as `verification=unavailable`, but cannot rewrite the
already durable result into a different CLI outcome.  The temporary file uses
the existing `.stage-` namespace, so ordinary ACL2-owned staging recovery
collects an interrupted administrative residue; there is no `.admin-`
recovery grammar.

The generation filename has one owner:
`fn-native-admin-config-name GENERATION` returns the eight-decimal-digit
`.cfg` name only for natural generations below `100000000`.  The host wrapper
`fn-native-admin-host-config-name` returns that string or `nil`; writer-side
`fnn-config-record-name` and `fnn-config-record-path` in `host/native/io.lisp`
call the wrapper.  Namespace recovery must decode each bounded observed record
and compare the record generation's wrapper result to its basename; it must
retain malformed, duplicate, mismatched, and budget-exhaustion evidence rather
than filtering it away.  This packet does not claim the historical unbounded
configuration-namespace enumeration is already replaced.

The isolated local ACL2(p) closure was run with no cache publication:

```
FN_ACL2=/opt/homebrew/Cellar/acl2/8.7_6/libexec/saved_acl2p \
python3 tools/certify_books.py --jobs 1 --timeout-seconds 180 --no-publish \
  --closure books/native-admin tests/acl2/native-admin-tests
```

`planning/evidence/manifests/certify-20260921T110352Z-22952.json` records the
passing closure at ACL2 8.7 / SBCL 2.6.8 on macOS, the executable SHA-256
`c0a0dfbde5e111168673e845a6daa8d019236b14123e39e4a8548d9f592e56b9`, exact
source digests, and the 344.584-second run.  It pins source through
`463f72a1`; the subsequent test-only commit added the accepted authorization
and occupied-name teeth.  That exact test source passed under the same profile
with:

```
FN_ACL2=/opt/homebrew/Cellar/acl2/8.7_6/libexec/saved_acl2p \
python3 tools/certify_books.py --jobs 1 --timeout-seconds 180 --no-publish \
  tests/acl2/native-admin-tests
```

Its source-pinned manifest is
`planning/evidence/manifests/certify-20260921T111009Z-28049.json`; it records
the dirty source digest set rather than merely the parent revision label.
Neither run populated the serial certificate cache or certifies a saved native
image.  A standalone SBCL load/read of `host/native/admin.lisp` succeeded, but
does not exercise the native image, public operator join, physical publisher,
crash recovery, or namespace recovery.  `tests/test_native_admin.py` now
defines the public-image witnesses for create/capacity/retire history,
owner-lock refusal, uncertainty followed by recovery/sweep, and two
administrators; it is skipped in this isolated worktree because no image has
been saved.  Those runs require the integrated operator image and the normal
remote serial gate.
