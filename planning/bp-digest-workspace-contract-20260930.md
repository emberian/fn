# Actual BP reopen integrity workspace

This is an implementation contract for the private full disconnected-delivery
assembly. Public typed recovery475214 is separate and does not qualify these
new storage, schema or native reopen bytes. The actual first remaining caller
boundary is `:integrity-required` to registered workspace begin.

BP owns `bp-digest-workspace-storage`, the per-controller storage/carry,
revisioned source/action handlers and real checkpoint/reopen caller. Physical
owns SAME-pool reserve/intent/promotion/release and status-aware allocation.
Runtime owns the exact selected creators and retained/transient envelope.
Root confirmed this split; it adds no approval gate.

The existing controller-root table receives one workspace-node child. A
separate lazy full-physical-slot LSB tree terminates at address0, where each
node can own its digest/carry. Positive addresses choose parity then floor/2.
This distinguishes all controller slots, including prefix addresses, and
preserves addressing when the controller registry grows. Each node has only
left/right/digest/carry keys, not eagerly allocated64 workspaces. Reads test
boundp before every get; missing paths are unavailable and create nothing.
Fuel bounds actual read recursion. Native never supplies a physical-slot/node.

Carry6 binds controllerToken, actualJobToken, workspacePRSnonce, immutable
source incarnation, phase and revision. The digest child is the actual
pgs-digest-state16-field/fixed64-frame representation. Default phase is
uninstalled. Storage declarations, supplied local test factories and pending
claims are not constructor grants or an installed receipt.

The allocator ABI frozen by physical is:

- `fn-owner-bp-digest-install-begin(controller,fuel,registry,pool)` returns
  word,workspaceToken,installPlan,left,registry,pool. Begin is runtime-unavailable
  before creators until a selected family allowance is installed.
- WorkspaceToken4 is `(:bp-digest PRSnonce controllerToken actualJobToken)`.
  Internal plan7 is `(:bp-digest-install token controller job source phase revision)`.
  Only `:reserved` permits the subsequent intent transition.
- `fn-owner-bp-digest-install-constructing(controller,workspaceToken,fuel,registry,pool)`
  must persist construction intent before any lazy factory. Unknown or partial
  construction retains charge/intent and fences; it is never retried/refunded.
- Publish derives actual registered storage readout, transfers reusable
  installed capacity once C→U, and publishes installed last. The token-selected
  stored-plan projection for the core factory composition is still pending.

`fn-bpck-control-source-incarnation` extracts the existing exact digest capture
`(:bp-checkpoint-stage actualJobToken generation)` only from a private completed
prefix job, exact digest-start/pending I/O control and no pending action.
The registered prefix-end source turn now persists digest-start/pending before
this projection (c89720bc4). A native phase snapshot never establishes authority. Controller-derived readonly
pending-job capture is also a physical source prerequisite: current workspace
read validates a supplied job token against the retained directory rather
than deriving that token.

The end-to-end harness remains real NNTP acceptance→BP queue/send→job and
persistence interruption→bounded reopen/retry→durable matching receipt/right
release→DEFAULT same-Store retirement with unrelated debt retained. Charged
workspace installation, exact trailer/decoder/recovered carry, source schema
assembly and native qualification are all still open. No historical image,
whole-checkpoint decode or supplied demand is a fallback.

Physical subsequently froze the core-only readonly stored-plan projection
`fn-owner-bp-digest-install-plan(controller,workspaceToken,fuel,registry)`:
word,plan,left,registry; it has no native declaration. Internal install-step
uses that actual stored plan, persists constructing, then invokes the lazy
factory in one serialized core invocation. Physical also owns readonly
`fn-bpcc-pending-capture(controller,fuel,registry)`, deriving actual job token.

BP's digest-binding field is fixed intent6:
`(:bp-digest-install-intent workspaceToken phase sourceIncarnation actualClaim selectedAllowance)`.
The exact SAMEPRS-issued resource vector and genuine installed family receipt
are retained by reference. No scalar receipt-shape recognition grants authority
and no turn compares the whole allowance graph. Phase reserved→constructing
precedes every creator; unknown outcomes fence while retaining claim/source.
The immutable source is captured once; later stored-plan revision is read from
the actual pending continuation. Bounded factory progress belongs in the
separate pending-action control, retaining the same intent6 and source.

The dormant actual native prefix caller now retains only controller/action and
I/O lifecycle evidence. Its guarded token-only next subject derives revision
internally, so startup does not require a native revision snapshot. Per turn
it prepares+performs one primitive or joins one prior observation; a failed
join retains action/outcome and fences without repeating I/O. Callbacks have
no setter/install and default NIL. Missing installation refuses before record
construction. This does not discharge actual callback/BODY/stage installation,
digest factory or cleanup/close qualification.

Native record primitive/result ownership is serialized with a nonwaiting
action mutex, distinct from the extent mutex. A busy scheduler turn makes no
core call or source-return update; definite return is published by the primitive
owner. The public record constructor remains an infrastructure unavailable
fault before allocation: compiled role callbacks are not per-job constructor
authority. Runtime/physical must supply the actual record11+mutex creator gate
and same-job claim before activation; raw recording fixtures are unfunded.
