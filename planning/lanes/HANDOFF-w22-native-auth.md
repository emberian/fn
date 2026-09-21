# Handoff: w22/native-auth — ACL2-owned native AUTHINFO startup profile

Commits `47c06c53`, `7d36f2bb`, `f7b2e297`, `f087bfc0`, `b68cf738`,
`48cc5c02`, `66ad0e9`, `83d2c0a`, and `7e6737d`, based on `67f45a3`.

The native operator now carries the normalized `[auth]` path, `required`, and
`protected_only` values into a pre-listen owner startup hook.  Raw Lisp reads
one bounded no-follow regular file and supplies its octets and presence
observation to `fn-native-auth-load`; ACL2 alone parses the canonical
`fn principal set-password` format, decodes fixed-width fields, constructs
verifiers, assigns posting permission, decides profile acceptance, and builds
the config installed into the owner.  The owner run's existing five normalized
arguments are unchanged.

The deployed service does not call Python.  Python appears only in the native
test as operator-side credential enrollment and process orchestration.

## Called boundary and policy

`host/native/auth.lisp` calls `fn-native-auth-host-load`, whose body is exactly
`fn-native-auth-load`.  On an accepted result it passes the exact ACL2-built
config to `fn-owner-set-auth-config`; the raw host does not reconstruct a
credential row or policy bit.  `fn-native-auth-load-accepted-pins-policy` is a
local projection lemma: under the accepted-status hypothesis, the model result
carries the three normalized policy observations exactly.  It is not a
registry keystone or a theorem about the raw host installation call.  Its test
book has an accepted required-profile witness and a refusal witness where
removing the hypothesis makes the conclusion false.

The accepted credential syntax is the bounded canonical writer output:
comments and blank lines plus `[login."NAME"]` tables containing exactly one
`principal`, `salt`, `digest`, and `posting` field.  The whole file is at most
65,536 ASCII octets, 1,024 lines, and 128 credentials.  Duplicate names or
fields refuse.  A legacy `secret` field refuses by name without reading or
migrating the cleartext value.

The native image has no TLS socket facility.  It always reports TLS unavailable
to ACL2, so `protected_only=true` remains unavailable before bind; raw Lisp
never calls a loopback or plain socket protected.  Native config continues to
restrict the listener to ACL2's loopback set.  Reader authentication does not
grant peer/transit authority: an `IHAVE` issued by the authenticated-reader
path remains rejected by the peer layer.

The hook runs after Store/FNFD recovery and before listener creation.  It owns
no worker, descriptor, or retained secret resource, so it adds no stop/close
hook.  It is distinct from the control/feed lifecycle hook lists and composes
in this order: install, auth startup gate, listener/wakeup creation, module
start hooks, accept.

## ACL2 evidence

Persvati farm run `run-20260921T100255Z-ecf3` passed the explicit closure of
`books/native-auth-profile` and
`tests/acl2/native-auth-profile-tests` with ACL2 8.7, SBCL 2.6.8, four jobs,
and saved ACL2 SHA-256
`c8a7a804d9cc80e2025a8ab0e1d9325f2a0c4a027a5dcdcb2c1093e9cd5c8163`.
The source-pinned manifest is
`planning/evidence/manifests/certify-20260921T100303Z-2441658.json`; it ran
from 2026-09-21T10:03:03Z through 10:06:56Z and records 231.661 seconds.
The parser source digest is
`01655a8d189416e5fca4af3ec4c9e4ebab7f6ba9282ec030a451aa5ada809543`;
the test source digest is
`898a6b5354527dcb6bce22edbc634abb130f3ab67cdc827061a9930287d97f79`.

The larger owner base is separate evidence, not part of the auth theorem
claim: source `03eb3ba34cc150d8cde63de656558f7cb3bd18b8`, persvati run
`run-20260921T095031Z-5cf4`, manifest
`certify-20260921T095039Z-2322081.json`, 139-book closure and 50 requested
roots, exit 0.  Its certificates retain their ACL2 full-book-name origin
`/home/ember/fn-lanes/w13-owner-integrated-gate`; copying them into the macOS
worktree is not a valid native image load.

## Native evidence

The path-preserving continuation at
`persvati:/home/ember/fn-lanes/w13-owner-integrated-gate` passed focused
certification of the three changed books and four test roots as
`certify-20260921T101518Z-2561161`.  Its 43-root default artifact set
load-checked, and the clean native build produced image SHA-256
`acc73b70c0112b7cceaba8d280f81e369db5ea931babb303a038fdf13f1daf6d`
and core SHA-256
`2abea9e40160956bc8656cdedee64a138959afc3d398fffe4d0c72c00404a89c`.

The first clean live run exposed a raw-boundary defect: the auth hook used the
state-returning adapter for a pure wrapper.  Commit `7e6737d` changes that call
to `fnn-core`; the image and passing results below are after this fix.  With
the corrected image, all three `tests.test_native_auth` cases passed in 2.336
seconds and all nine `tests.test_native_operator_cli` plus
`tests.test_native_owner` regression cases passed in 24.678 seconds.

The exact commands, tools, source digests, artifact digests, pass logs, and
the two retained pre-fix diagnostics are in
[`native-auth-runtime-2026-09-21`](../evidence/native-auth-runtime-2026-09-21/README.md).

## Remaining obligations

* Credentials and policy are pinned at startup.  There is no atomic credential
  reload or live generation/session switching; restart is required.
* Native TLS remains absent, so protected-only authentication is unavailable.
* This packet exercises only ACL2-normalized loopback listeners and makes no
  public-listener or deployment claim.
* Native configured-peer/source-address admission is outside this packet; its
  live test establishes that reader authentication does not grant transit.
* The owner's pre-existing orderly SIGTERM shutdown gap is unchanged; the auth
  startup hook has no asynchronous handler or retained resource.
* No D09 cryptosuite or key-policy decision is made.
