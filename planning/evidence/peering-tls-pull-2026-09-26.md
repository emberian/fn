# peering-tls-pull: a node pulls over TLS as its own principal (PRF-125, 2026-09-26)

Dev lane `lane/peering-tls-pull` from `dev` b41720ae, brief
`build/coordinator/queue/w2-peering-tls-pull.txt` (mandate §12 packet 8, §15
"Protected ordinary use"; the design is peering-compose's "Packet 8").
Ids: PRF-125, NNT-023, SCN-071, PKT-236. Commits: ad78c9cc (the session and
the host), 6971bd20 (native gate, pair theorems, registry), and the commit
carrying this record. Everything is `:logic` with verified guards; no
skip-proofs, defaxiom or trust tag.

## What now works (user-visible)

- **B pulls from A over STARTTLS as B's principal.** A serves STARTTLS with
  `[auth] required = true, protected_only = true` and holds a principal
  `nodeB`; B's peer record for A names STARTTLS, A's certificate as the only
  anchor and B's credential profile. B stores both articles once, logs
  `pull peer=A round=done cursor=advanced transport=tls`, and a recording
  proxy in front of A sees `STARTTLS` as the only plaintext command: no
  AUTHINFO, DATE, NEWNEWS or ARTICLE crosses in the clear.
- **A wrong principal is refused by A.** B's profile names a login A does
  not hold: the TLS handshake completes (no TLS error on B's stderr), A
  refuses the credential, every round logs `round=failed cursor=held
  at=preamble`, nothing is stored, and B's FNPL journal stays at 65 octets
  (the first-instant record) across three rounds.
- **A clear transport with a credential is refused by B's own ACL2 before
  any connection**: every round logs `round=failed cursor=held
  refused=clear-credential` and the proxy accepts zero connections; the
  profile file is not read.
- **Packet 5's six kill cuts hold over TLS**: at before-write, after-write
  and after-fsync of appends 1 and 2, every article is stored exactly once
  after the restart and a later round logs `cursor=advanced transport=tls`.
- The loopback-lab exception: a clear transport carries a credential only
  when the profile's `allow-clear` is true AND the host is `127.0.0.1` or
  `::1` (specs/peering.md §1.2.8). It is local policy for a lab on one
  machine and supports no secure-peering claim in general.

## Assurance chain

native entry `fnn-pull-worker` -> `fnn-pull-round`
(host/native/pull-service.lisp) -> ACL2 subjects, all in
books/peer-pull-session.lisp: `fn-pull-plan-profile-path` (line 204: whether
a secret is read at all), `fn-pull-session-begin` through
`fn-pull-session-begin-pair` (line 219: journal, then `(:dial)` or a
refusal), `fn-pull-session-step` through `fn-pull-session-step-pair` (line
275: `fn-fc-step`/`fn-fc-after-tls` until `:ready`, then `fn-pull-step`),
`fn-pull-session-read-limit` (line 279: one feed chunk before `:ready`),
`fn-pull-session-close-effects`/`-close`/`-log-line` (lines 307-309); the
plans from host/owner-host.lisp `fn-owner-pull-plans` (line 2485,
`fn-pull-plans`, now carrying security and credential policy) ->
refinement: the pairs are the session's two values
(`fn-pull-session-{begin,step}-pair-by-definition`) -> maintained relation:
PRF-100's "the FNPL journal replays to the round's cursor", established by
the begin's journal effect and preserved by every session step
(`fn-pull-session-step-keeps-the-cursor-and-journals-nothing`) -> behavioural
theorems below -> observed: the native witnesses. The TLS preamble adds no
relation: its only durable effect is none.

## Theorems (books/peer-pull-session.lisp; peer-pull.lisp for begin-ready)

- `fn-pull-session-credentials-wait-for-tls-and-login` (KEYSTONE): for a
  plan whose `fn-pull-plan-verdict` is `:tls`, the feed-machine
  observations of the session begun from it, driven by ANY host events,
  satisfy `fn-fc-gate-okp` from the start stage. Proved by instantiating
  PRF-051's `fn-fc-offers-and-credentials-wait-for-tls-and-login` (not
  restated) over the session's fed events, through
  `fn-pull-session-obs-is-the-machine-over-its-trace` (the session's
  observations ARE `fn-fc-drive` of its initial machine over the events it
  fed). Each pre-ready step's effects are `fn-pull-obs-effects` of exactly
  those observations, so AUTHINFO leaves only on `:auth-user`/`:auth-pass`
  (stage 2: after the 382 and the verified-TLS report) and DATE only on
  `:ready` (stage 3 with a credential).
- `fn-pull-session-refuses-a-clear-credential-without-the-lab-exception`
  (KEYSTONE): clear security, a credential, and not (allow-clear and a
  loopback literal) => verdict `:refused-clear-credential`, no profile path,
  begin effects = `fn-pull-begin-effects` ++ `((:close))` (no `:dial`), the
  session run over any events is `(mv s nil)`, and the close is the cursor
  `fn-pull-begin` asks with.
- `fn-pull-session-journal-is-the-cursor-at-every-cut` (KEYSTONE, the
  transfer): PRF-100's `fn-pull-journal-is-the-cursor-at-every-cut`
  (statement unchanged) for the session: after the begin, after any events
  (the TLS preamble included), after the close records.
- `fn-pull-begin-ready-is-the-round-after-the-greeting`: on a 200/201
  greeting `fn-pull-on-line` of `fn-pull-begin` is `(mv (fn-pull-begin-ready
  ...) ((:remote . DATE)) t)`; `fn-pull-begin-ready-cursor-fields` (the
  cursor-fields lemma: phase `:date`, and peer, wildmat, since, advances and
  the round cursor are `fn-pull-begin`'s).
- supporting: `fn-pull-session-step-fc`, `fn-pull-session-fc-events-quiet`,
  `fn-fc-drive-of-append`, `fn-pull-session-fc0-opens`,
  `fn-pull-session-step-after-ready-unfolds`,
  `fn-pull-session-run-of-a-done-round`, `fn-pull-session-begin-round`.

Trusted, not proved (A-HOST, as PRF-051): the host reports `(:tls-up)` only
after `fnn-tls-connect` verified the chain against the plan's trust anchor
and the plan's server name (pull-service.lisp line 251).

## Teeth (tests/acl2/peer-pull-session-tests.lisp)

- A whole STARTTLS session from configuration rows to the close: the plan
  from `fn-pull-plans`, begin effects `(:journal ...) (:dial)`, the wire in
  order (STARTTLS, `(:tls "localhost" anchor)`, AUTHINFO USER nodeB,
  AUTHINFO PASS, DATE, the one NEWNEWS, ARTICLE, QUIT), the observation
  kinds `(:starttls :need-input :tls :auth-user :need-input :auth-pass
  :need-input :ready)`, `fn-fc-gate-okp` true, the log line.
- Mutation: `200` then `381` in one chunk on a TLS plan: only STARTTLS is
  sent, the round fails at the preamble.
- must-fail (verdict `:tls` removed): the loopback-lab plan's session sends
  USER, PASS, DATE with no 382 and its observations fail the gate.
- Refusal witness with every antecedent literal asserted; must-fail per
  hypothesis: STARTTLS security dials, no credential dials, the lab
  exception dials. A TLS plan whose profile was unreadable is
  `:refused-profile`.
- begin-ready: the 200 witness; must-fail for a 400.
- Cut transfer: the three replays from the fresh cursor through the TLS
  session; a kill after STARTTLS, TLS and the credential journals nothing;
  must-fail for the replay hypothesis (an older journaled instant) and for
  a non-startable cursor.
- Every must-fail's inner expression was evaluated to NIL in the persvati
  REPL (so each fails for its stated reason, not an error).

## Certification (hbox, w28 `acl2-literal-4g`, 2 jobs, 300 s)

| run | manifest | roots | result |
| --- | --- | --- | --- |
| `run-20260926T003554Z-97e3` (tree ad78c9cc) | `certify-20260926T003614Z-4146295` | `--affected-by` peer-pull, peer-pull-session: 4 | passed; peer-pull 5.6 s, peer-pull-session 7.2 s, tests 2.8 s / 2.6 s |
| `run-20260926T004853Z-41bf` (tree 6971bd20) | `certify-20260926T004913Z-4166387` | `--affected-by` peer-pull-session: 2 | passed; peer-pull-session 8.3 s, tests 3.2 s |

Every book under 10 s. All forms were first admitted in a persvati
`proof_repl` session.

## Native (hbox; script `peering-tls-pull-2026-09-26/image.sh`)

Image from the r1 gate tree (ad78c9cc; r2 adds only the two pair theorems,
no executable change): acquire + validate `roots=157 result=loaded`,
developer image under `swarm-build`, undefined lines 0. Stores under
`/tank/fn/scratch/peering-tls-pull/tmp`; the module ran under `systemd-run
--user -p MemoryMax=24G` and `tools/test_budget.py`: 8 tests, 188.8 s of
300 s, ok (the four earlier pull cases included, INN 2.7.4 among them).

| file | SHA-256 |
| --- | --- |
| `build/fn-host-developer` | `8f082d7bcd98779e8327e297a6f380ebe1694795b1f5ef6c7ccbfd20ae16f6ea` |
| `build/fn-host-developer.core` | `f6110023bb69fdde749d512827936bbc9d1c4699cdfc16909593144265c19f92` |
| `native-build-developer.log` (left on hbox) | `90651ef9d49b16f2c9df73e607fc067c18317193a2189509927c3d8aad1f05da` |
| `native-peer-pull.log` | `57af27637e35011fed797f6fefe1b97bf978b3ab5bca3495a3378bdcbeda246e` |
| `tls-pull.witness.json` | `1cfbbff8df9259633a2f7fef2ddf87c101301fb2e563a09e6219f142edaf3cfb` |
| `tls-wrong-principal.witness.json` | `066b92c2401b9592c0df383e226b0ec798f0e825876b03bf8a372f22c0922593` |
| `clear-credential.witness.json` | `98e9f04951289a9324ea318f9472796a962b0e7f862eeb55e282d17ffc140cb3` |
| `tls-cursor-cuts.witness.json` | `b90af44550d229cf748d7adc61e7ac1f62896c30e6382588d36ea760f2a6abcd` |
| `cursor-cuts.witness.json` (clear, unchanged behaviour) | `87962826121e86956784a09c361fcd66b134b20dd1ff9859d25f17cdd3b4ad15` |
| `tls-wrong-principal-A.log` / `-B.log` | `e1369f01...8e0d` / `85fb0246...b487` |

The witnesses and logs are beside this record. The first run (same image,
witnesses only on stdout) was also 8/8 ok, log `876b55b6...bc62`; the
witness-file change to the harness is the only difference.

Harness change, classified: the recording proxy forwarded only complete
lines, so a TLS record without a newline would have stalled; it now passes
non-line octets through when no ARTICLE is being held (harness; the clear
cases are unchanged and green).

## Not done, and why (PKT-236)

- **Task 3, `peer accept` configuring the inviter**: not started. The
  invitation's `Host`/`Port` are the invitee's; the inviter's address is
  absent. Design in PKT-236 (invitation kind v2 with `Inviter-Host`/
  `Inviter-Port`, a `peer invite` grammar change, an accept record plan
  beside the confirm's with its fold keystone). It is a wire change between
  nodes; budget went to the session, its proofs and the native gate.
- The duplicate-replay bound after a close cut is observed natively only in
  the clear (the proxy cannot read ARTICLE inside TLS); it is proved
  (PRF-100 transferred).
- No native case of the loopback-lab exception against a non-protected
  server (ACL2 witness only).
- A credentialed pull uses the peer's outbound profile, so it needs outbound
  groups; a pull-only credential slot is not built.
