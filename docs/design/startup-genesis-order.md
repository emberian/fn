# Actual startup genesis ordering

At source32170a880, init-executor calls init-engine/engine-genesis before the
host invokes boot-start. Engine genesis stages/finalizes group and authority
principal NAME overlays, increments ID sequence, binds anonymous/owner accounts,
and configures the sealer. Even though listeners stay gated, this makes C
nonempty before checkpoint adoption. Cold selected NAME state must instead come
from the authenticated summary, while actor account initialization remains.

The C helper split provides:

- `fn2-engine-genesis-actors(profile, core) -> code, core`: bind the actual
  anonymous/configured owner accounts once, then initialize/park the existing
  sealer metadata. It creates no NAME overlay or ID-engine scratch lease.
- `fn2-principals-bound-genesis-ids(owner-slot, core) -> code, ids`: read actual
  already-bound account identities, refusing zero incarnations; no rebind.
- `fn2-principals-name-genesis(profile, core) -> code, core`: the existing
  authority NAME writer, using those current bound IDs. The original
  principals-genesis still binds then calls this writer; non-image engine
  genesis keeps groups -> principal bind/NAME -> sealer order and refusal flow.

The actual single-entry writer is `fn2-grp-insert-one`, shared by group and
principal NAME schemas (name/value field positions coincide). Genesis opens
one overlay through actual scratch acquisition/reserve/ov-start, inserts all
entries, then increments the ID sequence once and freezes that overlay once.
A bounded boot continuation must reuse that same overlay and perform one
insert-one per step. Repeating singleton grp-genesis would allocate one overlay
per entry and change semantics. The existing whole-profile genesis calls must
not be charged as a constant-work boot step.

Parent owns boot/executor branch insertion and sealer scheduling. The actual
fresh alternatives are successful create writes of all four zero anchor slots,
or a reopened image with all four observed canonical-empty slots. Any candidate
or invalid nonempty anchor takes descriptor/census investigation instead.
Fresh NAME genesis must precede full-prefix replay so late initial NAME writes
cannot overwrite durable changes. Selected cold adoption must never stage these
NAME overlays. Config groups are currently destructively consumed during
immutable genesis verification, requiring a retained trusted source for the
bounded NAME continuation. No replay/overlay rows are discarded by this split.

The proposed dedicated C startup carrier captures trusted profile groups/count,
authority policy and configured owner slot at core initialization; boot retains
its existing destructive verification cursor. Begin derives current actor IDs
and binds the actual boot owner generation. Parent and C owner must agree the
actual begin/step phase ABI before adding that carrier; no caller readiness or
caller-supplied identity list is authority.

`tests/startup-genesis-unit` uses actual actor initialization and the real NAME
writers. It requires unbound IDs to refuse, unchanged full NAME/pool/run state
through actor initialization, a parked/non-ready sealer, distinct group/principal
frozen overlays after actual trusted writes, and unchanged full accounts/IDs
through NAME writing. Source prepared only; no ACL2 or physical boot execution.
The split alone does not alter the current executor startup ordering; the parent
must connect it and the bounded fresh branch before claiming the startup repair.

## Actual executor and sealer gate

Image-profile executor initialization now binds accounts and initializes the parked sealer through the actor-only helper. It creates no NAME overlays; non-image initialization keeps its existing full genesis path. The actual sealer grant predicate and direct step both require either absence of a boot actor in the kind directory or a readable, unstopped READY boot actor. An unreadable present actor is refusal, not absence. This prevents fresh NAME and recovered source mutations from racing sealer work before replay/epoch closure.

The bounded fresh NAME continuation and actual fresh boot branch wiring remain pending in this source checkpoint; source parsing passed, not ACL2 execution.
