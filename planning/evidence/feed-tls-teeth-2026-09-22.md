# The outbound feed's protected channel, with teeth (T9c)

What this file is: the record of lane `t9c/feed-tls`, step T9 part (c) of
[the trajectory plan](../plan-2026-09-22-trajectory.md) §3, phase 1. It names
what ran, on what bytes, and what it does not establish. It makes no claim
about a deployed node or an image: the matrix rows it adds have not been run
on one.

## What ran

| fact | value |
| --- | --- |
| iteration | `tools/proof_repl.py` against the cached closure, then `tools/certify_books.py` locally (this laptop, macOS 26.6.1 arm64, ACL2 8.7 on SBCL 2.6.8, Python 3.14.7) |
| certification host | `persvati`, ACL2 8.7 at `/home/ember/fn-gates/toolchains/w25/acl2-literal`, toolchain identity `1b4169e9…` |
| branch | `t9c/feed-tls`, worktree `build/lanes/t9c-feed-tls`, base `dev` `2788d4cb` |
| revision certified | `0295a4bb` |
| run | `run-20260922T202644Z-e5f3`, `--closure --jobs 4 --timeout-seconds 1800`, remote root `/home/ember/fn-gates/t9c-feed`, cache `/home/ember/fn-certcache` |
| roots | `books/feed-connection`, `books/feed-connection-invariants`, `books/feed-auth-profile`, `tests/acl2/feed-connection-tests`, `tests/acl2/feed-connection-invariants-tests`, `tests/acl2/feed-connection-teeth-tests`, `tests/acl2/feed-auth-profile-tests` |
| manifest | `planning/evidence/manifests/certify-20260922T202647Z-3725626.json` |
| result | `passed`, 43 books, no failure, 208.5 s of certification wall. `books/feed-connection-invariants` 69.1 s, the teeth book 2.0 s. The manifest's source digests for the changed books equal this tree's bytes |
| earlier run | `run-20260922T201133Z-7a9c` at `197bbc2a`, manifest `planning/evidence/manifests/certify-20260922T201146Z-3590991.json`, `passed`, 43 books, but `books/feed-connection-invariants` took 409.1 s -- over the 300 s discovery budget. 277.9 s of it was the pre-existing `fn-fc-table-lookup-is-state`, which opened the state recognizers; closing them (the table-put proof's posture) is `0295a4bb` |
| static gate | `python3 tools/green_check.py --changed-since 2788d4cb --strict`: "3 changed books, 4 books include one; 0 not green at the bytes a merge would carry." `make check` exits 0 |

The invocation, exactly:

    python3 tools/farm.py submit persvati books/feed-connection books/feed-connection-invariants \
        books/feed-auth-profile tests/acl2/feed-connection-tests \
        tests/acl2/feed-connection-invariants-tests tests/acl2/feed-connection-teeth-tests \
        tests/acl2/feed-auth-profile-tests --closure --jobs 4 --timeout-seconds 1800 \
        --remote-root /home/ember/fn-gates/t9c-feed \
        --acl2 /home/ember/fn-gates/toolchains/w25/acl2-literal --cache /home/ember/fn-certcache

## What is now proved that was not

All in `books/feed-connection-invariants.lisp` unless named. The subjects are
the functions the host calls on a peer's connection: `fn-fc-step`
(`host/owner-host.lisp:1374`, in `fn-owner-feed-reply-chunk`, which
`host/native/feed-service.lisp:256` calls) and `fn-fc-after-tls`
(`owner-host.lisp:1279`, in `fn-owner-feed-tls-established`,
`feed-service.lisp:194`), and the two AUTHINFO renderers the host calls on the
step's next state (`owner-host.lisp:1288`, `:1388`, `:1393`). `fn-fc-drive`
feeds a list of events -- chunks and the symbol `:tls-up` -- to exactly those
two functions and records, per event, the kind the host acts on, the code of
the line consumed, and whether it was the TLS report.

1. `fn-fc-offers-and-credentials-wait-for-tls-and-login`. Hypotheses:
   `fn-fc-protected-profilep` (STARTTLS or implicit TLS, or a credential whose
   profile did not permit clear text) and `fn-fc-opening-phasep` (the phase
   `fn-owner-feed-dial-open` installs). Conclusion, for every event list:
   `fn-fc-gate-okp` of the observations, from stage 0 (1 for implicit TLS). The
   gate reads observations only: stage 1 needs `(:tls 382)`, stage 2 an accepted
   TLS report at stage 1, stage 3 a line coded 281 answered `:mode` or
   `:ready`; `:auth-user`/`:auth-pass` need stage 2 and `:mode`/`:ready`/`:reply`
   need stage 3 (2 without a credential).
2. `fn-fc-starttls-refusal-closes-before-the-credential`. Hypotheses:
   `fn-fc-statep`, the STARTTLS phase, a complete line, its code not 382.
   Conclusion: `:refused`, phase `:closed`, and `fn-fc-quiet-obsp` of whatever
   is fed afterwards (no kind on which the host sends, handshakes or goes live).
3. `fn-fc-refused-login-closes-without-an-offer`. Hypotheses: `fn-fc-statep`,
   a login phase, a complete line, code not 281, and (answering USER) not 381.
   Same conclusion.
4. `fn-fc-auth-user-command-sends-the-configured-name-alone` and
   `fn-fc-auth-pass-command-sends-the-configured-secret-alone`. Hypotheses:
   the field is `fn-fap-tokenp` and a true list. Conclusion: the rendered line
   is the prefix, the field and CRLF.
5. `fn-fc-decoded-profile-renders-verbatim-in-every-state`. No hypothesis:
   for any profile bytes, in the state any event list reaches from
   `fn-fc-initial-auth-state` over `fn-fap-decode`'s fields, the USER and PASS
   lines are the prefix, the decoded field and CRLF. It uses
   `fn-fap-decode-yields-two-renderable-tokens` and
   `fn-fap-decode-refusal-yields-no-credential` (`books/feed-auth-profile.lisp`).

## The teeth

`tests/acl2/feed-connection-teeth-tests.lisp`. The scenario is a profile
`FNAUTH1\nnode\nsecret\n` that `fn-fap-decode` accepts, and the connections
`fn-owner-feed-dial-open` would install from it. Witnesses: the full STARTTLS
trace (greeting, 382, TLS report, 381, 281, 203, a CHECK reply) with its whole
observation list written out and the gate holding; the implicit-TLS trace; a
STARTTLS peer without a credential; a clear peer without permission refused at
the greeting; the reachable `:auth-pass` and `:auth-user` states answered 481;
the reachable STARTTLS state answered 502 and 580. Sixteen `must-fail`s: two for
keystone 1, five for 3, four for 2, two each for the renderers, and for the
unconditional keystone 5 the false neighbour -- the same claim over a name and
secret that did not come through `fn-fap-decode` -- refuted by a name carrying
CRLF and `QUIT`. Beside each, the concrete value that refutes the weakened
statement is evaluated. The `(not (fn-fc-allow-clear st))` clause of the
protected-profile disjunct is separated by a clear peer whose profile permits
clear text: it sends USER at stage 0.

Each must-fail is built by a macro that is also used, first, to admit the
keystone itself under the same hints. The first draft had no such control and
its keystone 2 and 3 must-fails failed for a reason unrelated to the dropped
hypothesis (a lemma they needed was local to the book); each of the sixteen
was re-run in a live session and fails with a key checkpoint, not a translate
error. Because the must-fail bodies are macro calls, `tools/ledger.py`'s
teeth-form lint does not read them.

## The matrix rows

`tools/v0_matrix.py` plans `V0-TRANSIT-TLS-AB/BA`, `V0-TRANSIT-AUTHINFO-AB/BA`
(accepted), `V0-TRANSIT-TLS-WRONG-ANCHOR` and `V0-TRANSIT-AUTHINFO-WRONG`
(refused). The native slice's phase `native protected transit` runs the three
tests of `tests/test_native_protected_peering.py` against the run's image and
maps only their `NATIVE-PROTECTED-WITNESS` lines, and only when both live
owners' runtime and core digests are the run's. `python3 tools/v0_matrix.py
--plan-rows` recorded the six rows in `planning/v0-matrix.json` as
not-exercised; no image has run them. `tests/test_native_v0_matrix.py`
`ProtectedTransitTests` pins the planning and the mapping (seven tests).

## What this does not establish

- Anything on an image. The T9 gate -- two nodes on one box, TLS and AUTHINFO
  both ways, a `kill -9` of the sender mid-transfer, exactly one copy after
  restart -- is root's.
- That the host reports `:tls-up` only after a verified handshake: that is
  OpenSSL's chain and hostname checking, trusted integration evidence.
- The composition with owner-feed's offer: that `fn-feed-offer` and
  `fn-feed-send` need a natp `fn-feed-conn`, set only at `:ready` and cleared by
  `fn-feed-lost`, is read from the definitions and not proved here.
- CAPABILITIES: fn does not read it before STARTTLS.
- The profile file's ownership and mode, and the loss-to-requeue path
  (PRF-029/K5, T9a).
- PRF-049 (principal-bound inbound role), which the plan's §7.5 also labels
  T9c, was not in this lane's brief and has no event.
