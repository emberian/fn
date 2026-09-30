# Retained incoming authority freshness

The incoming holder remains reserved across configuration/account publication
and bounded recapture. Neither a stale snapshot nor an unavailable authority
permits input mutation, release, refund, a new frontier reservation or replacement
of the retained original input. This is an internal fn guarantee, not an RFC wire
extension or a newly authorized account capability.

The actual authority half consists of two guarded internal STATE callbacks:
`fn-owner-incoming-authority-capture(pool, state)` and
`fn-owner-incoming-authority-recheck(pool, state)`, each returning word, pool and
STATE. They derive the live holder/context from the actual pool carrier, the
process epoch, `fn-cfg-generation(fn-owner-config(state))`, actual Store event
count, canonical CP7 and the sole account-root sidecar. The existing
`fn-cra-availablep` decides account publication availability. The namespace is
forty octets at authority field 3; revision is scalar field 1. Account sidecar6
is `(:ready epoch namespace revision fence-event-count root4)`; field 5 is the
root, not its footprint. Fence count is distinct from Store/Catalog frontiers.

The private `fn-owner-incoming-freshness` global retains twelve fields:

| Field | Meaning |
| --- | --- |
| 0 | `:incoming-freshness` |
| 1 | `:awaiting-query`, `:query-attached`, or `:stale-recapture` |
| 2 | Actual readonly incoming holder token |
| 3 | Context/process epoch |
| 4 | Carried intent digest, exactly 32 octets |
| 5 | Live configuration generation |
| 6 | Account authority namespace, exactly 40 octets |
| 7 | Account authority revision |
| 8 | Last completed account fence event count |
| 9 | Borrowed immutable account root |
| 10 | Borrowed original incoming context/input |
| 11 | Actual registered query token; NIL until its producer attaches it |

Capture writes this coordinate once, only after current authority is available.
Any existing snapshot returns `:freshness-pending` unchanged. Recheck accepts no
saved tuple from its caller. Namespace/digest comparisons have fixed traversal
budgets, holder comparison uses its fixed issued identity, and no config, root,
account table or retained submission graph is compared. A current answer is
`:authority-current`; it is deliberately distinct from the complete query gate.
A changed identity returns `:recapture-required`, retaining fields 2 through 11
and the same pool. Missing current source/publication returns
`:authority-unavailable` without overwriting the saved roots.

The registration owner attaches field 11 only at the actual successful query
begin/adoption result under the same owner exclusion and original holder/source
association. A native job token or public tuple setter is not a producer. The
publication half is `fn-mio-query-publication-recheck(token, fuel, mio)`, whose
fuel must come from the admitted scheduling operation. The combined public
capture/recheck gate remains unavailable until that attachment, actual retained
source lifetime, and prepaid closure are joined. Recapture keeps old roots until
actual last-alias settlement; it never allocates another frontier.

The owner must establish canonical CP7/Store correspondence and complete account
root/publication correspondence, preserve them across actual publication, and
hold owner exclusion across capture/recheck and the decision they authorize.
These are producer invariants, not whole-state predicates on a served path.
The new list12 and two-cell stale-phase update require actual cumulative
allocation funding; no supplied Boolean or numeric allowance is installation.

PRF-1167 covers the actual STATE recheck's source projections and retained roots.
The companion tests execute actual account fence/config/delete producers for
interleaving evidence; separate STATE fixtures explicitly use synthetic owner
installation and the real incoming reservation issuer. Source admission, normal
certification, selected native execution and deployment remain separate claims.
