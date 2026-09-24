# Native E2 local-consumer qualification plan (2026-09-23)

`tests/test_native_consumer_e2.py` is a real-process driver for the local
consumer command in `8d3175fd`. It awaits a source-matched developer image
containing that command, Linux `SO_PEERCRED`, and the production local
`consumer bootstrap CONTROL_ABS` command. No native
E2 result is claimed by this plan. The test constructs no cursor bytes: every
`fncu` file is the output of ACL2 through `register` or `position`, and `ack`
reads that exact file.

The first scenario initializes two independent Stores, opens their real
owners, bootstraps through each owner, registers the same consumer name, and compares the owner
issued positions. Registration before bootstrap is refused with no token.
A normal accepted article does not advance the recorded
consumer ack. Equal-position ack is accepted without an extra declaration;
the other Store's cursor is refused; unregister and re-register changes the
epoch and refuses the old cursor. Reopening preserves the new position and
the unrelated article's exact body. The owner calls `fn-col-register`,
`fn-col-ack`, `fn-col-position`, and `fn-col-unregister`; the write outcomes
pass through `fnn-owner-consumer-commit` and full Store replay. These are the
model's register, no-op ack, unregister, and recovery paths, rather than
simulated endpoint responses.

The second scenario bootstraps through an ordinary owner, stops it, then
arms developer `FN_NATIVE_CONTROL_TEST_STOP=after-submit` on reopen.
`host/native/control.lisp` prints `CONTROL-SUBMITTED` after the owner has
completed the durable consumer register, while the worker is stopped before
sending the reply. The driver kills the owner process, requires the client to
report uncertain (exit 3), reopens the Store, and settles the outcome through
`position`. Re-registering the same scope must return that same recovered
cursor. This cut corresponds to durable `fn-sn-finish` followed by process
death before the transport reply, then `fn-sn-recover` from full journal
replay. It does not simulate a partial Store write or an uncertain `ack`.

The third scenario, only when the test runner has Linux root and `setpriv`,
registers a live consumer as the owner UID, makes the Unix socket reachable
at the filesystem level, then issues `position` as UID 65534. Refusal with no
output file and successful owner-UID `position` distinguish `SO_PEERCRED`
authorization from a missing registration or socket permission failure.
Ordinary non-root runs explicitly skip this credential case.

There is no native poll/fetch command in `8d3175fd`. The separate
`FN_RUN_CONSUMER_POLL_E2E=1` method is gated for the later ACL2-owned
`consumer poll` command. It registers, signs and submits an authored source,
checks the returned exact composite Store event using ACL2's decoder and
binding predicate, verifies repeated polls do not change durable `position`,
and acknowledges the returned cursor. A developer stop after durable ack but
before reply makes the client report uncertain; reopening and querying
`position` must resolve it. The test does not construct a cursor or Store
event in Python. A consumer-owned inbox transaction and signed-source
reference-only API are still separate work: poll currently returns the full
encoded accepted event, not a consumer inbox commitment.
When `FN_CONSUMER_POLL_EVIDENCE_DIR` names a new absolute directory, the
successful native test copies the exact authored source, returned fn-e parent,
returned fncu continuation, principal, and public verification keys there
after its assertions. It refuses an existing directory so two runs cannot
silently mix fixtures.
`FN_CONSUMER_POLL_SOURCE_FILE` may name an absolute, preexisting public source
article for the same signed-post/poll path; no field is extracted or rewritten
by Python. This lets the Mini E1 public source fixture exercise the exact
consumer event boundary with a separately identified test-driver digest.
