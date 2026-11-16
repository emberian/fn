# Required served withdrawal producer

Source audit: `1dec35c0007f0a60d6b7b33bdeb6b2e055990629`, 2026-11-15.
This records an implementation dependency, not a qualified feature or a new
cancellation policy. No executable changes or computation accompanied it.

Withdrawal is a required public behavior. The existing public writer is a
cancel article accepted through NNTP POST/IHAVE/TAKETHIS, not a new FNCT DELETE
verb. [E §13.5](../../e-surface.md#135-control-across-peers-rfc-5537-5)
names that producer; E §7 requires a positioned report in every target stream,
including waking a reader which already acknowledged the target. E's ruled
C amendment requires the count change in the cancel transaction. The separate
cancel-before-target intent is explicitly design until the control path serves.
It is not a reason to mark the delivered-target withdrawal requirement absent.

[AUTHORITY-20261105](../AUTHORITY-20261105.md), ruling 3 and §5/c5/c8,
requires the authenticated original submitter or the node administrator.
Append permission, From, Message-ID, a source signature, and payer identity do
not independently establish that authority. `fn2-cns-withdraw` in
`books/consumer-model.lisp:446` checks the model's recorded author but is a
world/model operation, not an authenticated served decision.

## Actual caller and representation gaps

- `upload-scan.lisp:39..52` recognizes CONTROL's name/presence. Its retained
  ranges at 223..228 cover only Message-ID, Newsgroups and Path. It retains no
  cancel target and invokes no receiver-local cancellation decision.
- `txn.lisp:817..833` is the actual article writer and always supplies LIVE.
  No current txn/commit/recovery producer invokes a concrete withdrawal
  decision. `format-events.lisp:94` only declares the withdrawal codec.
- `authority.lisp:1145` decides consume/read/append stream grants and owner
  bootstrap access. It does not decide whether a caller can withdraw a target.
  Reinterpreting append authority would change policy, not connect a caller.
- `ordered.lisp:31` retains ARTICLE state and the complete physical location,
  hashes, birth and version, but no original submitter/authentication basis or
  accepted-membership reference. `txn.lisp:892` emits ADDR only for the first
  group. Neither that index nor an unbounded overview scan supplies all target
  stream memberships and exact original group numbers. ADDR is keyed
  `(principal, position)` and merges unique: removing the first-group check
  and inserting one row per group would duplicate the same key, not implement
  a reverse membership index.
- `commit-format.lisp:111/117/234` supplies header author0. An immutable birth
  lookup therefore does not by itself recover an authenticated original local
  submitter. Semantic lineage/physical origin and a funded payer are separate
  from the required caller authentication provenance.
- The old E allocation “withdrawals id15” conflicts with current
  `ordered.lisp:85`, where id15 is consumer-names. It cannot be reused silently.
  The native own-cancel tests refer to historical `fn-*`/cancel-lock code;
  they are not a current `fn2-*` receiver-local decision or producer.
- Readers do understand WITHDRAWN: NNTP's declared 423/430 branches and CNS's
  item/FETCH refusal. That read support and the parked model do not establish
  reachability. D §15 explicitly records the missing writer and the versioned
  withdrawal/group-view obligation.

## Owned implementation dependencies and minimal producer

The parent owns integration; this lane owns the source audit/producer plan.
The authority owner must first supply the **existing authorized receiver-local
cancel decision**, bound to the actual authenticated caller, exact resolved
accepted target and immutable authorization evidence. The adopted authority
ruling already selects the authenticated original submitter or node administrator;
there is no outstanding user policy choice here. The prior authorization worker
stopped after a cybersecurity safeguard error. Its exact rejected task payload is
not recoverable, so this is not evidence of a command-specific approval denial or
a prohibition on a particular policy change. The blocked task is not being retried
or rerouted. Resolving that safeguard restriction and implementing the existing
principal-bound decision remain separate obligations. No synthetic acceptance
is supplied by this audit.

Once that real decision exists, connect its result to a bounded txn continuation:
retain and parse the actual Control value through generated pool codecs; resolve
its exact Message-ID through the current identity path; retain the target's
actual accepted membership/number and authority provenance; reserve the complete
successor/member bundle before staging; copy the whole ARTICLE value and change
only the authorized withdrawal fields; emit the positioned reports and count
folds atomically with the cancel acceptance/outcome. Use the ordinary persisted
B member/dispatcher and C publication barrier. Refusal contributes no committed
target change; ambiguity keeps its ownership until recovery. The declaration of
any missing report/membership representation lands with this actual writer
(D46), using a free schema allocation, never the occupied id15.

Controls must drive real target POST then authorized cancel POST, unauthorized
cancel, exact retry/conflicting request, a reader pinned before the cancel, a
reader refreshing after it, and consumer delivery before/after ACK. Assert the
whole real authentication antecedent and negative authorization controls; never
seed withdrawn rows or use a fake DELETE adapter.

## Separate payload-retention/discharge dependency

A withdrawal report is not payload reclamation authority. ARTICLE's latest value
still retains its location/digests; ADDR is append-only/unique. The restore owner
also reports the richer cold `checkpoint-payload-state` path still derives and
authenticates those locations without a withdrawn-state omission (that book is
not present in this application cut). The retention/restore owner must connect
actual rooted withdrawal and discharge semantics before omitting descendants
from a later sufficient base. Preserve archive/history, every selectable bank,
queries/borrows and remaining obligations. Do not null a location, skip payload
verification, infer release from a report, or enable FREE as a shortcut. The
reclamation gate remains closed until that independent dependency is implemented
and its real producer-to-consumer controls pass.
