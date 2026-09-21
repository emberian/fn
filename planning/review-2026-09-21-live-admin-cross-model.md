## Review: native live administration packet (7270fad8, f76b2e4a)

### Finding 1 — live admin channel silently faults on ordinary plans (codec reuse bug)

`fn-native-control-admin-encode` (books/native-control.lisp:125-130, new in 7270fad8) marshals the admin `argv` by calling the **pre-existing newsgroup-list codec**:

```lisp
(defun fn-native-control-admin-encode (argv)
  (if (or (not (fn-native-admin-argvp argv)) (not (consp argv))) :bad
    (let ((payload (fn-nctrl-groups-encode argv)))
      (if payload (fn-nctrl-seal *fn-nctrl-admin-kind* payload) :bad))))
```

`fn-nctrl-groups-encode` → `fn-record-groupsp` (books/records.lisp:124-128) requires every element to satisfy `fn-record-group-namep` (**≤128 octets**, books/records.lisp:106-109) and `fn-record-no-duplicatesp` — **no duplicate words**. But the admin grammar it's being asked to carry, `fn-native-admin-argvp` (books/native-admin.lisp:41-48, 17-18), permits up to 10 words of **≤512 octets each with duplicates allowed**. This isn't just an encode-time gap either: `fn-record-parse-groups` (books/records.lisp:281-298) enforces the identical `:duplicate-group`/length checks on decode, so the wire format itself cannot carry the full space of plans ACL2's own planner accepts.

Concrete trace: `fn --fn operator <config> peer add near path-id host.example 119 "*" "*" 198.51.100.5 true` — a symmetric mirror peer (accept-groups = feed-groups = `"*"`, the ordinary case per `fn-native-admin-peer-plan`, books/native-admin.lisp:115-143) is `:accepted` by `fn-native-admin-plan`. With a live owner, `host/native/operator.lisp:172-178` routes it to `fnn-control-admin` (host/native/control.lisp:360-389). There, `fn-native-control-host-admin-encode` returns `:bad` because `"*"` appears twice, and:

```lisp
(unless (fnn-octet-list-p request-list)
  (fnn-fault "ACL2 refused normalized live administration"))   ; control.lisp:365-366
```

`fnn-fault` signals `fnn-store-fault` → **exit 4 ("fault")**, the class reserved for "the host could not carry out the operation" (docs/operator.md:247-252), not `:refused`/exit 1. The identical command issued while the owner is stopped succeeds via `fnn-admin-execute`, which never touches this codec. So the same ACL2-accepted plan is accepted offline and reported as an internal fault live — and any argv word over 128 octets (well within the 512-octet bound the planner allows) hits the same failure even without duplicates. This code was adapted from `fnn-control-submit`'s identical `fnn-fault`-on-bad-encode pattern (host/native/control.lisp:391-403), which is correct there because a legitimate post's Newsgroups list is expected to satisfy `fn-record-groupsp` — that assumption doesn't hold for admin argv and wasn't rechecked.

The packet's own tests (`test_running_owner_applies_durable_administration`, `test_live_uncertain_publication_fences_and_recovers` in f76b2e4a) only exercise `group create` live; no test sends `peer add`/`peer remove` through the live control channel, which is why this didn't surface.

### Finding 2 — `posting-enabled=false` does not gate the new admin surface

The only existing policy toggle for the control socket, `fn-owner-posting-configure` (host/owner-host.lisp:120-132), writes to `fn-inj-config` — consumed solely by the article-injection/post path. The new admin path's admissibility gate, `fn-ocfg-reconfig-refusal`/`fn-ocfg-reconfig-okp` (books/owner-config.lisp:296-360), checks connection existence, clock, busy/staged state, generation, reader pins and record admissibility — it never reads `fn-inj-config` or any posting flag, and `fn-native-admin-host-owner-reconfigure` (host/native-admin-host.lisp:14-32) doesn't check it either. A deployment that sets `posting = false` specifically to restrict what the local control socket permits (docs/operator.md documents the socket as handling "posting and administration" together) will find group create/remove, capacity changes, and peer add/remove — including adding a peer that receives the outbound feed — still fully reachable through that same socket. This is a completeness gap in an existing mechanism, not a request for a new authorization model (AGENTS.md's acknowledged open item about *who* may reconfigure is separate and unaffected by this observation).

### Verified sound / not reported

- **Owner mutex ownership**: `fnn-owner-live-admin-serialized` (host/native/admin.lisp:111-151) runs staging, authorize, publish, complete and feed-refresh entirely inside one `fnn-owner-serialized`/`with-mutex` hold, matching the pattern used by `fnn-owner-control-submit-serialized` and the reconfiguration.md note ("only then does `fn-owner-reconfigure-complete` publish... and `fn-owner-feed-configure` refresh"). The `return-from fnn-owner-live-admin-serialized` inside the nested lambda unwinds correctly through `with-mutex`.
- **Uncertainty fencing**: `fnn-admin-publish`'s `:uncertain` branch and a non-`:durable` `fn-owner-reconfigure-complete` both raise `fnn-store-indeterminate`, which `fnn-owner-shared-action-locked` turns into a service stop at exit 3 before feed refresh can run — exercised by the packet's own `test_live_uncertain_publication_fences_and_recovers`.
- **Generation drift**: 7270fad8 originally passed the raw config generation number as the owner connection `id` into `fn-native-admin-host-owner-reconfigure`/`fn-own-reconfigure` (which indexes connections by id, not generation) — this would have made `fn-ocfg-reconfig-refusal`'s generation/connection checks meaningless. It is already corrected in the lane by `48321149` (opens/closes a real pinned connection via `fn-owner-open`/`fn-owner-close` under the same mutex), so I'm not re-reporting it as live.
- **Feed refresh**: newly-added peers get FNFD journals synchronously under the admin mutex (`fnn-owner-feed-open-missing`); removed peers are closed asynchronously by the polling `fnn-feed-refresh-links` worker (host/native/feed-service.lisp), matching the documented split. The `remove-if` → `loop`/`collect` rewrites in f76b2e4a (feed-service.lisp, owner.lisp) are behavior-preserving.
- Did not re-report the previously-fixed client-closing parenthesis defect; the current `fnn-control-handle-client`/`unwind-protect` shape in control.lisp is correct.

### Untested boundaries worth root's attention

- No live-channel test exists for `peer add`/`peer remove` at all (only `group create`), which is exactly the gap that let Finding 1 through.
- No test exercises an admin command arriving while a post is mid-stage on another connection (the `:busy` refusal path from `fn-ocfg-reconfig-refusal`).
- The control socket's admin/post trust boundary (Finding 2) and the general "who may reconfigure" question are both explicitly open per AGENTS.md/reconfiguration.md §"What this design does not do" — flagged for awareness, not as new scope.

## Root disposition

This was one read-only Claude Sonnet review, run through Claude Code in the
`fn-w25-review` tmux session. It inspected the live-administration packet
`7270fad8`, `f76b2e4a` and the subsequent connection-pin correction `48321149`.
It did not run ACL2, build an image, or execute the runtime scenarios; descriptions
of what tests exercise refer to test source, not observed passing executions.

Finding 1 is accepted: a newsgroup codec cannot represent the administration
argument grammar. A bounded ordered argument codec and live peer regression are
assigned to the administration repair lane.

Finding 2 is not accepted as a defect in the selected contract. The posting flag
controls article submission; it is not an operator-administration authorization
switch. The local control socket is created with mode 0600, and possession of
that operator endpoint permits administration. Disabling article posting must
not silently disable the operator's configuration channel. The operator guide
will state this boundary explicitly. Separate least-privilege agent endpoints
remain a design concern; no new remote administrative authority is introduced
by this interpretation.

The review is scoped input to convergence, not a service or assurance gate.
