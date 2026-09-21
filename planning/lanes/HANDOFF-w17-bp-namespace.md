# W17 BP lifecycle namespace handoff

Source tip: `4a92d4b3da281ec2c3da670adf3a4b8135cf4b54`

The native BP lifecycle service now asks ACL2 for the bounded namespace
observation limit and uses `fnn-list-directory-bounded` before retaining the
directory list.  ACL2 generates the canonical `.fnb` name with the existing
Store transaction decimal codec, separates bounded hidden stage evidence,
requires a contiguous final-name frontier, binds every decoded record token to
its observed name, and checks that replay reaches the same next-token frontier.
The called append path at `host/native/bp-service.lisp:118` uses the ACL2 name;
capacity remains in `fn-bpn-propose`, and the append path no longer enumerates
the lifecycle directory.

Recovery sorting is a host observation only.  ACL2 owns classification and
validity.  Hidden stage entries are retained in the service state and are not
treated as committed records or silently removed.  Namespace or binding
failure is indeterminate recovery.  Existing no-replace link publication,
directory barriers, exact-stage cleanup, and uncertain persistence outcomes are
unchanged.

Integration commits, in order:

- `e9711f1` — namespace plan, host wrappers, actual caller, ACL2/native tests
- `0849c6d`, `75e8acb`, `4a984c8` — verified executable name-renderer guard
- `bd2b6a0` — linear accumulator reversal and pre-allocation namespace bound
- `4a92d4b` — actual-handler physical over-bound witness

Do not cherry-pick `252c86b`: it copies the bounded-directory helper into this
older lane only so the final native image can be built.  Main already has the
same helper through `7a0b96f`.

Evidence:

- Hbox owned closure from the initial functional checkpoint:
  `planning/evidence/manifests/certify-20260921T092428Z-1943222.json`, ACL2 8.7,
  40/40 books passed.  The later changes affect only this codec, its host use,
  and tests.
- Final source-pinned persvati certification:
  `planning/evidence/manifests/certify-20260921T094642Z-2283728.json`, ACL2 8.7
  on SBCL 2.6.8, `books/bp-node-machine-codec` and
  `tests/acl2/bp-node-machine-tests` passed.
- Final persvati DTN image build:
  `planning/evidence/native-host-build-w17-bp-namespace.log`.
- Actual native handler suite:
  `planning/evidence/native-bp-namespace-w17-tests.log`, 8/8 passed.  It covers
  corrupt spelling, namespace gap, decoded-token/name mismatch, retained hidden
  stage evidence, no append-time enumeration, the physical directory bound,
  shared spool ownership, and both existing directory-barrier EIO cuts.

The final target certification is deliberately scoped rather than another full
gate.  The imported `fnn-list-directory-bounded` helper's direct `readdir(3)`
boundary test belongs to main commit `7a0b96f`; this packet adds the BP handler
witness that reaches it.
