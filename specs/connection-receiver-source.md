# Connection receiver source custody

PRF-1182 contributes to STO-10001 at the internal accepted-open RX boundary.
`fn-crx-open-origin` consumes the returned accepted-open result and the SAME
installed receiver capacity/instance readout; a well-shaped supplied observation
alone establishes no runtime authority. `fn-ich-rx-bind` stores that origin in
the actual connection segment alongside its issued holder. Its `:associated`
result makes the matching origin readable while preserving the connection row,
segment identity and active count. Conflicting rebind returns recovery without
replacing the original association; another CID is stale.

An issued turn retains the same origin and its actual turn ticket. Acquisition
requires exact CID, holder, ticket, capacity and instance agreement. Revocation
blocks further acquisition; retained parser/response lifetime is separately
settled by its controller. The accepted-open/turn/close host composition must
also revoke stored acquisition authority before close effects. Those hooks and
the genuine runtime getter are the integration owner's independent work.

The model scenario reserves a nonempty holder, attaches its pin, binds and reads
the origin, rejects a conflicting rebind and wrong CID, then closes and observes
staleness. It checks all three custody outputs. Literal turn tests check the
complete current antecedent, all five different coordinates and their rejection;
a stale CID demonstrates failure of the sole antecedent and of the literal
cross-connection conclusion when the substituted CID is the actual one.
Revocation and custody laws are unconditional, so they have no retained
hypothesis-removal case. Synthetic grant/pin/capacity inputs are explicitly
fixtures. This component establishes no complete source allowance, genuine
installation, native execution or image qualification.
