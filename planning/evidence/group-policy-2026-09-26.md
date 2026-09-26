# group-policy (wave 5), 2026-09-26

Lane `lane/group-policy` from dev `8dc094f93`; brief
`build/coordinator/queue/done/w5-group-policy.txt` (gap inventory items 3, 8,
9: P1, O2, CT3). Ids: PRF-196, NNT-040, SEC-006, SCN-125, PKT-575, PKT-576.
Configuration delta code **21** (`:set-group-status`); usenet-headers holds
20 (`:set-group-description`).

## Summary

- **O2, read-only groups: done** (NNT-040, PRF-196, SCN-125). `group policy
  NAME n|y`, offline and live; a local POST naming a closed group is refused
  `441 posting failed; a group this article names is read-only here (LIST
  ACTIVE status n)`; LIST and LIST ACTIVE carry the status field from the same
  list. No store record, no format change, no migration (D34).
- **CT3, operator withdraw: not done**, designed (PKT-575 (2)).
- **P1, own-post cancel and Cancel-Lock: not done**, specified as SEC-006
  (specs/nntp.md "Own-post cancel and Cancel-Lock (SEC-006)"); the obstruction
  is measured and the decision is PKT-576.

## 1. O2: what was proved

RFC 3977 section 7.6.3 (the LIST ACTIVE status field) and RFC 6048 section
2.1 (`n`: local postings are not permitted; relayed articles still arrive):
the gate is an RFC meaning, not a stronger fn guarantee; the 441 text naming
the reason is a stronger fn guarantee (section 6.3.1 permits a plain 441).

- KEYSTONE `fn-cfg-set-group-status-sets-the-status`
  (books/config-invariants.lisp), over `fn-cfg-apply-delta` (the fold replay
  and live publication run): for a typed value V (`fn-cfg-valuep`), NAME live
  at GEN, STATUS in ("y" "n"), applying `(fn-cfg-set-group-status NAME
  STATUS)` makes `fn-cfg-group-status` of NAME equal STATUS and leaves every
  other group's status unchanged. The last two hypotheses are exactly what
  `fn-cfg-delta-reason` admits (`:no-such-group`, `:group-status`); the
  first is the maintained typed value (`fn-cfg-apply-delta-preserves-valuep`,
  re-proved with the new arm).
- `fn-cfg-closed-names-are-the-n-groups`: the closed list is exactly the
  groups whose status is "n".
- KEYSTONE `fn-gst-post-gate-refuses-exactly-a-listed-n-group`
  (books/group-status.lisp): the gate refuses exactly when the ordinary
  article names a group whose `fn-nntp-closed-status` under the
  configuration's closed list is "n" -- the function LIST ACTIVE's status
  field is rendered with.
- `fn-post-reader-env-closed` (books/nntp-post.lisp): the environment the
  POST step hands the reader carries the configuration's closed list, so
  LIST ACTIVE and the gate read one list.
- `fn-post-gated-decision-unfolds`: a refusal of the injection decision is
  unchanged; an accepted article is refused `:group-read-only` exactly when
  the gate names a closed group (so the clock line, `:unknown-group` and
  every other reason keep their lines:
  `fn-post-without-a-clock-refuses-with-the-clock-line` re-proved unchanged).

Host lines: books/nntp-post.lisp `fn-nntp-post-step` (reached through
`fn-nntp-post-step-pinned` and books/peer-offer-indexed.lisp
`fn-pix-post-step-pinned` on the served path) calls `fn-post-gated-decision`
and `fn-post-reader-env`; the verb's delta is books/native-admin.lisp
`fn-native-admin-plan-deltas`, called live by host/native-admin-host.lisp
`fn-native-admin-host-owner-reconfigure` and offline by
`fn-native-admin-host-apply` (the generic delta record); the closed list is
installed by books/owner-agent.lisp `fn-oag-post-config` (host/owner-host.lisp
`fn-owner-post-config`, at recovery and every live reconfiguration) and kept by
`fn-owner-posting-configure` and books/owner-served-bound.lisp
`fn-osb-config`.

Representation: the posting configuration gains an optional fifth field
(`fn-inj-config-closed`; `fn-inj-make-config-closed`); a four-field
configuration closes no group, so every existing constructor and theorem is
unchanged. The reader environment likewise gains an optional fifth field
(`fn-nntp-env-with-closed`); with no group closed, LIST is byte-for-byte the
earlier answer (the list-command arm is taken only with a closed group). The
group's status is its entry's policy identifier (`fn-policy-read-only-1` is
"n", `fn-policy-default-1` "y"): the value shape and the entry shape are
unchanged; the record codec already carries any delta kind code.

Assurance chain: native entry (`operator CONFIG group policy NAME n|y`, live
over the control socket or offline) -> `fn-native-admin-plan-deltas` ->
configuration record (code 21) admitted by `fn-cfg-delta-reason` -> fold
`fn-cfg-apply-delta` (keystone: status set) -> the owner installs
`fn-oag-post-config` (closed list = the n groups) -> a connection pins it at
open -> `fn-nntp-post-step`: POST through `fn-post-gated-decision` (keystone:
the gate is the listed n) and LIST through `fn-post-reader-env` -> observed
441 / LIST ACTIVE `n` (native module below). The relation is established at
recovery (the replayed configuration) and at each live completion; a
connection keeps the configuration it pinned until it re-pins (the existing
pin semantics).

## 2. Teeth (tests/acl2/group-status-tests.lisp)

- The delta: code 21 both ways; `fn-cfg-deltap`; admitted for a live group
  and y/n, refused `:no-such-group` and `:group-status`; the fold (announce
  n, test y, closed list, served names unchanged, y reopens); the record
  codec round trip.
- Keystone (config): a reachable witness asserting every hypothesis and both
  conclusions; without liveness (fn.absent) the status is not set:
  must-fail; without the status hypothesis ("m") the status read is not "m":
  must-fail; the value hypothesis: a CORRUPTED STATE witness (labelled), an
  atom before the entries, is not a value.
- The verb: `group policy fn.announce n` stages exactly the delta; `m` is not
  accepted.
- The owner's posting configuration carries `("fn.announce")` and is
  `fn-inj-configp`.
- The gate: alone and cross-posted refused, open group passes, a cancel is
  not gated, a Supersedes article is; no closed group, nothing gated; the
  keystone's both directions on reachable articles.
- The host-called step: POST to the closed group answers exactly the 441 and
  submits nothing; to the open group submits; the same article under a
  configuration with nothing closed submits; LIST = LIST ACTIVE with
  `fn.announce 0 1 n` / `fn.test 0 1 y`; `LIST ACTIVE fn.a*`; with nothing
  closed both `y`.

## 3. REPL (persvati, ~/fn-gates/group-policy-repl)

Validation by batch: no farm run. Each changed book and the test book was
admitted in the REPL on persvati in its own session (`gp-each`, started on
tests/acl2/article-fields-tests so every certified book is a real include),
with every changed or affected book below it loaded
`:ld-skip-proofsp 'include-book` (locals skipped, as an include would) and
the book itself proved: config (as the session book), config-invariants,
injection, injection-invariants (in an injection-first session),
nntp-responses (as the session book), nntp-invariants, nntp-effects,
group-status, nntp-post, nntp-pinned-effects, owner-agent,
owner-served-bound, native-admin, nntp-auth-fold, peer-offer-indexed,
owner-list-counts-read, owner-control-read, owner-enrollment-read and
tests/acl2/group-status-tests: all admitted, every assert-event and
must-fail passing. Found on the way and fixed: the gate first placed before
the injection decision broke `fn-post-without-a-clock-refuses-with-the-clock-line`
(the clockless server's line), so the gate now runs on an accepted article
only; hints in nntp-invariants, nntp-effects, nntp-auth-fold and
owner-control-read name the new list functions. A red seen only in a session
that had proved books with local `arithmetic/top` (injection-invariants'
`fn-inj-refusal-names-a-reason`) was a session artifact: the same book was
admitted in a session without those locals. Not REPL-run: every other
affected book (the batch certifies the roots below).

## 4. Native

`tools/hbox_native.sh --name group-policy --label n1 --images
developer,production 41ec18743 tests.test_native_group_policy`
(hbox:/tank/fn/scratch/group-policy/native-n1; developer image
`fn-host-developer.core` c8518f28..., production `fn-host.core` 8010ca42...):
**OK, 4 ran, 0 skipped** (the image case 2.8 s). Log
planning/evidence/group-policy-2026-09-26/native-n1-test_native_group_policy.log
`5e41f87e25c2c315d578ffcda3aa3edd725a227367f51f65b68302daf1583a60`;
SHA256SUMS native-n1-SHA256SUMS
`198049d217e655ad34aeeb17f36c194c37b9375f944be4480934e1cb06c9351a`.
Observed (SCN-125): offline `group policy fn.absent n` refused, `fn.ro m` not
accepted, `fn.ro n` accepted; LIST ACTIVE `fn.ro ... n`, `fn.test ... y`;
POST to fn.ro and to fn.test,fn.ro answered the read-only 441, fn.test 240,
STAT of the refused Message-ID 430; live `y` then a new connection lists `y`
and posts 240; live `n` then a new connection's POST is refused; after a
restart LIST ACTIVE shows `n` and POST is refused. The commits after
41ec18743 change proof hints and the test book only, no executable
definition.

## 5. CT3 and P1: not done (PKT-575), and the decision (PKT-576)

### PKT-575 (what remains)

1. **LIST COUNTS status.** RFC 6048 section 2.2 gives LIST COUNTS the same
   status field; fn still answers `y` for every group there (the bucket arm,
   books/nntp-list-counts.lisp, has no environment). One argument through
   `fn-gidx-counts-line`.
2. **CT3, `control withdraw MSGID REASON`** (offline and live) under the
   node's own authority. Design: a configuration delta (the NEXT FREE code on
   dev when the lane lands; this lane took only 21) recorded in the
   configuration journal; the refresh folds it as `(:withdrawal TARGET
   (:operator TXID REASON) NODE-PRINCIPAL ("*") GEN)` with a third effect
   `:node` beside `:author` and `:authority` in
   `fn-ctl-withdrawal-effect`; `fn-ctl-withdrawn-by-p`'s "cause among the
   view's articles" becomes, for an operator record, "record txid at or
   below the view's": the obligations are
   `fn-ctl-visible-is-arrival-order-independent` and
   `fn-ctl-pinned-view-keeps-its-archive` re-proved over the extended fold,
   and the new keystone "the verb's record is exactly the withdrawal the
   control machine applies" over `fn-ctl-journal-withdrawals`. The reader
   sees it in HDR :fn-control (a new status word, "withdrawn by this node's
   operator"). Owner-closure change (control-authority, owner refresh); a
   high-fan-in lane that should certify itself.
3. **P1 / SEC-006**, after PKT-576 is decided: the injected Cancel-Lock, the
   Cancel-Key on a login's own cancel, the new withdrawal basis in
   `fn-ctl-withdrawal-plan` (an unsigned cause whose Cancel-Key matches the
   target's Cancel-Lock), the D25 inverse (`fn-inj-source-of` strips the
   injected Cancel-Lock), and Supersedes as the same basis (RFC 5537 section
   5.4 already shares the decision).

### PKT-576 (decision packet for ember): what "the same login" is made of

Trace: `fn-ctl-withdrawal-plan` declines every unsigned cause (`:unsigned`);
a withdrawal is decided at `fn-own-refresh` from durable state only
(`fn-ctl-journal-withdrawals`: each withdrawing article's txid, Message-ID,
stored verdict and target). For an unsigned article nothing durable names
its posting login: the Store's kind-4 record does not
(planning/evidence/path-and-login-2026-09-25.md, "The Store's kind-4 record
does not; that remains open"), and the injected octets carry only the agent
(`fn-inj-injection-info-line`). So the coordinator's rule ("the accepted
cancel's principal equals the article's posting login") has nothing to
compare after a restart.

Constraints: D34 (no migration, no format bump); a decision must replay from
durable state; visible(T,C) = visible(C,T); a friend's cancel from another
node must work (RFC 8315); never the login in clear in a header.

Default (recommended): **RFC 8315 Cancel-Lock keyed by the login.** The node
injects `Cancel-Lock: sha256:BASE64(SHA256(K))`, K = BASE64(HMAC-SHA256(S,
MSGID || LOGIN)) (RFC 8315 section 4), S a 32-octet node secret created at
`init` beside the configuration (never served, never in a record); a
login's cancel gets `Cancel-Key: sha256:K` for its target. One basis for
same-node and cross-node cancels, carried in the articles' own octets (so
the decision reads two articles, arrival-order independent), SHA-256 in ACL2
(books/sha256.lisp), HMAC over it. Pessimistic number: another login's
cancel is accepted only by a SHA-256 second preimage of the lock (2^256
generic; the collision figure 2^128 does not apply, the lock is fixed first),
a named assumption in books/assumptions.lisp. Cost: the injected block
changes (the D25 inverse re-proved), a node secret file (its loss means own
posts can no longer be cancelled by login: stated, not silent), a new
withdrawal basis with teeth.

Rejected alternatives and their cost: (b) compare a hashed posting-account
in Injection-Info (usenet-headers' P2): same-node only, and it ties cancel
authority to P2's key rotation; (c) a Store record naming the login: a
format change (D34); (d) a configuration row per post: grows the
configuration journal per article and is not atomic with acceptance.

Affected: books/injection.lisp (block and inverse), books/control-authority.lisp
(basis), books/nntp-post.lisp (Cancel-Key on a login's cancel), host init
(the secret). What continues without it: everything; an unsigned cancel is
filed and withdraws nothing, as today.

## Not done

- CT3 and P1 (above). LIST COUNTS status (PKT-575 (1)).
- No farm certification (validation by batch).
