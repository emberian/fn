# Connection operation ticket completion

This internal component contributes to STO-10001. A scheduling receipt alone
does not authorize connection operation completion. The actual STATE callback
requires a present sixteen-field `:connection-operation-ticket` with the same
slot and nonce and a `:prepaid`, `:started` or `:refused` phase. Missing,
malformed, wrong-phase or mismatched tickets return recovery without consuming
the receipt. Definite refusals before ticket publication use the separate
internal refusal settlement, which returns no nonce only after actual ATS
completion reports `:left`.

`fn-owner-index-connection-finish` retains `:finish-intent` before actual ATS
completion. Success retains the complete ticket as `:finished`, consumes one
active turn and leaves cumulative allocation A unchanged. The completed roots
remain available if raw execution escapes between the core result and native
acknowledgment. `fn-owner-index-connection-fault` preserves STATE, slots,
identities, count and allocation while changing the pool to recovery. Its full
multiple-value result is idempotent. PRF-1163 names these actual core subjects in
`books/connection-operation-ticket.lisp`; the narrow host companion declares
the guarded native entries.

The native `fnn-with-prepaid-connection-turn` preserves the body's complete
multiple-value result, includes its allocating cleanup, and only then invokes
operation completion. Nonlocal body exits invoke fault rather than completion.
Completion failure fences under the extent mutex before unlocking; an outer
fence also covers interruption before entering the completion function. Both
fault calls belong to the operation allowance. The caller already holds owner
exclusion. The native component test exercises these paths against the actual
guarded core callbacks and concrete pool/slots, with fixture installation and
ticket construction explicitly outside its claim.

Actual PREPARE/START now has separate native component evidence in
`planning/evidence/connection-native-start-2026-09-30`. Source-derived complete
allowances, immutable installation,
all allocating participants and placement in the complete served caller remain
separate obligations. The fixture constructor and direct ATS test setup do not
grant production authority. No served callback or load path is selected by this
component packet.
