; Actual submit/poll interleaving controls over the bounded A/B core entry.
; Settlements/stopped state in these controls are explicitly synthetic.
; This is not a physical writer/fence/ACK or full checkpoint acceptance test.
(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "retirement-intent-leaf-unit")
(include-book "retirement-core-instance")
(include-book "../sim/commit-test-profile")
(include-book "retirement-intent-core-controls")
(fn2-retirement-intent-core-controls-events)

; The real generic body decoder used by txn-scan rejects lifecycle kinds.
; This is its actual entry, not a claim that a synthetic caller cut is sealed.
; Keyed ordinary batches encode KEYED_MUTATION; their journal extent is
; allocated by commit-allocate rather than an ALLOCATION transaction member.
(include-book "retirement-generic-controls")
(fn2-retirement-generic-controls-events)

(include-book "retirement-dispatch-core-unit")
