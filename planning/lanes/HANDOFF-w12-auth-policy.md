# Handoff: w12/auth-policy

Branch `w12/auth-policy`, baseline `8b474e2`.

## Contract delivered

`books/nntp-auth.lisp` now keeps two authorization decisions separate on the
composed command path. `fn-auth-restricted-keywordp` continues to gate local
reader operations and POST under the pinned AUTHINFO policy, while IHAVE,
CHECK and TAKETHIS delegate to `fn-peer-step` whether or not a reader login
exists. The peer layer owns the transit result: a session opened from a
configured source-role record sees its inbound policy; a reader session gets
the peer layer's 502 refusal. The source role remains local configuration
policy, not a claim that AUTHINFO authenticated the peer or that its address
is cryptographically trustworthy.

`fn-auth-capability-lines-for-peer` builds the served list from
`fn-peer-capability-lines` over the record pinned in the peer session and
then adds STARTTLS/AUTHINFO USER where the current reader policy permits.
Thus IHAVE and STREAMING are advertised precisely for an inbound-enabled
configured peer. The ordinary `fn-auth-capability-lines` remains the nil-peer
reader entry used by existing reader/greeting proofs.

The named keystone is
`fn-auth-step-transit-command-delegates-to-peer`: on a valid non-handshaking
transit command, the auth dispatcher equals its peer delegate without an
AUTHINFO-subject hypothesis. `tests/acl2/nntp-auth-tests.lisp` gives reachable
configured-peer IHAVE/CHECK/TAKETHIS cases and a non-peer 502 control; it also
pins the complete peer CAPABILITIES block. `tests/test_auth.py` and
`tests/test_owner.py` exercise the live listener boundary.

## Files changed

- `books/nntp-auth.lisp`, `books/served.lisp`
- `tests/acl2/nntp-auth-tests.lisp`, `tests/test_auth.py`,
  `tests/test_owner.py`
- `specs/nntp.md`, `specs/peering.md`

## Evidence

`python3 -m unittest tests.test_auth.ServedCredentialTests.test_peer_transit_is_advertised_without_a_reader_login tests.test_owner.TransitPortTests.test_the_capability_block_names_the_effective_transit_commands` passed (2 tests).

The final narrow closure farm run passed: `run-20260921T063021Z-9dec` on
`persvati`, submitted with
`python3 tools/farm.py submit persvati --remote-root /home/ember/fn-lanes/w12-auth-policy --jobs 4 --affected-by books/nntp-auth.lisp --closure`.
Its 86 selected books all exited zero, including `books/nntp-auth`,
`tests/acl2/nntp-auth-tests`, `books/served`, and
`tests/acl2/served-tests`. It used ACL2 8.7, began
2026-09-21T06:30:26+00:00, and finished 2026-09-21T06:34:07+00:00. The
archived manifest is
`planning/evidence/manifests/certify-20260921T063026Z-414371.json`; the
downloaded certification logs are under
`build/acl2/certify-20260921T063026Z-414371`. The manifest pins the resulting
`books/nntp-auth.lisp` digest
`f989bd0e5ebbfeb27616e6f78c42465b27f58d2e40d627af35049fff21cb5882` and
certificate digest
`da670ef43f73f7b44dd767e8e5235bade579b35e5d94d099d57b581ae74693e2`.

Earlier narrow runs exposed and corrected two concrete closure defects: the
nil-peer compatibility proof in `books/served` needed to unfold the new
capability composition, and the delegation theorem needed to expose the three
transit keywords. The final fixture correction in `cb2f72a` also uses the
actual IHAVE continuation response, `335 send it; end with <CR-LF>.<CR-LF>`.

## Registry delta for root

No IDs were allocated or registry files edited in this lane. Suggested
central update: add or revise one proof event for the keystone
`fn-auth-step-transit-command-delegates-to-peer`, with the sentence:
“For a well-formed non-handshaking IHAVE, CHECK, or TAKETHIS command, the
served auth dispatcher delegates unchanged to the peer machine, so transit
authorization depends on the pinned configured peer role and not an AUTHINFO
subject; reader and POST authorization remain under the pinned auth policy.”
