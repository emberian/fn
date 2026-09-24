# Fragment expiry and the actual reception gate

At frozen BP union `48425e4e` plus replay-frontier repair `b7b63f83`,
`tests/acl2/bp-node-fragment-step-tests.lisp` constructs two conformant
same-principal, same-family fragments with Bundle Age 0 and lifetime
60,000,000 ms. The nonzero fragment's durable local age anchor is at
monotonic 0; the offset-zero fragment's is at 60,000,001. At that later
observation the former has `fn-bpah-held-expiry = :expired` and the latter
has `:live`. A constructed held state containing both still makes the actual
`fn-bpnf-family-next` return `:ready`, and the actual
`fn-bpnf-fragment-step (:family 0)` proposes `:persist-family`. This is a
latent fragment-family expiry error in the logical state machine.

The same test establishes that `fn-bpnf-receive-wire-event` returns
`(:refused :fragment-not-reassembled)` for *each* fragment. It calls
`fn-bpn-receive`, whose fragment branch refuses before kind-5 custody.
Therefore the constructed expiry trace is **not reachable through the
current native wire path**; nor can that path currently implement the kind-18
fragment feature. Enabling fragment reception must be paired with an
observation-gated family proposal and versioned durable decision. The
application delivery no-fragment guard remains in force until a complete
whole bundle is durably installed.

The selected hbox run `run-20260923T235555Z-f0e4` certified the exact test
book against 160 installed matching dependencies, manifest
`planning/evidence/manifests/certify-20260923T235600Z-548670.json`.
`make check` passed after regenerating the ledger. No native fragment success
is claimed here.
