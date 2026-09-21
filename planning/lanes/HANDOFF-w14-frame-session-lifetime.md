# Handoff: frame-session lifetime in the Python development oracle

Branch `w14/frame-session-lifetime`, based on `dev` at `ac839c9`.  Scope is
the D07 Python development oracle only; no native runtime or storage semantics
changed.

## Defect and repair

`frame_bridge.session(bridge)` caches a `FrameSession` that adopts an external
`Acl2Store`.  The frame session does not own that process.  When the caller
closed the store, `_SESSION` still pointed at its closed pipe.  The next
unqualified `frame_bridge.session()` therefore returned the stale context,
and same-process tests failed with `ValueError: write to closed file` instead
of opening the next framing context.

`Acl2Store` now records an explicit, idempotent `closed` lifecycle state.
`FrameSession` checks the wrapped context before construction and each call.
The process-wide cache discards an explicitly closed context on its next use,
while preserving a live adopted context and its schema cache.

A poisoned context has different semantics.  `session()` and `adopt()` raise
`BridgeError` while it remains live and poisoned, even if a replacement store
is supplied.  They never construct a replacement process or retry the form.
Only the caller's explicit close establishes a new context boundary.  This
keeps loss of call correlation visible and avoids silently retrying a mutation
whose outcome may be uncertain.

## Evidence

Before the repair, both new minimal tests failed:

* `test_cleanly_closed_adopted_session_is_replaced` returned the identical
  stale `FrameSession` after closing its first store.
* `test_poisoned_adopted_session_is_not_silently_replaced` returned the
  poisoned session instead of raising.

After the repair, `python3 -m unittest tests.test_acl2_bridge -v` passes all
16 tests in 0.242 seconds.  The lifecycle tests use two stores and assert
that clean close creates one new owned session, while poison creates none and
also blocks explicit adoption of a replacement.

`python3 -m unittest tests.test_store -v` ran the existing same-process store
suite once against the current integrated ACL2 books.  Twenty of 21 tests
passed in 266.695 seconds, including every test that had previously cascaded
into the closed-pipe failure.  The only remaining error is a latent,
independent stale test call at `tests/test_store.py:391` to the removed
`Store._frontier_with_checksum` helper.  On unmodified main, that same test
still stops earlier at the original closed-pipe defect, so this packet does
not fold the metadata-test update into a session-lifetime fix.

`python3 -m py_compile tools/frame_bridge.py tools/run_store.py
tests/test_acl2_bridge.py` and `git diff --check` pass.  `make check` reaches
the generated ledger comparison and reports `planning/ledger.json` and
`planning/ledger.md` stale after the just-landed transaction-name proof; the
integration root owns those shared generated files.

