# Experimental BP sender outbound composition

`books/bp-outbound.lisp` connects the durable sender workflow to the
experimental `FN-BP-ADU` codec. It does not select a native D01/D09 format and
does not perform BP transport, filesystem publication, cryptography or policy.

## Request path

`fn-bpo-request-adu` takes a recovered `fn-bp` state plus work, attempt and
attempt-generation identity. Success requires a ready, unfenced workflow; an
outstanding durable work entry; the exact current `:intent` attempt; the
work-to-node archive binding; and the committed article named by the work's
Message-ID. It constructs the request with:

1. work ID and immutable subject from durable work;
2. source EID from local configuration and destination EID from work;
3. policy, source incarnation, authorization context and terms from work; and
4. the exact committed node article payload.

Because no transport observation returns an attempt to `:intent`
(`fn-bp-observe-transport-never-returns-to-intent` in
`books/bp-workflow-transport-invariants.lisp`), the `:intent` requirement here
cannot be re-satisfied by transport evidence once the attempt has advanced;
only a new attempt at a new generation is `:intent` again.

The `fn-bpa-requestp` gate enforces the portable 256-octet metadata and
32,768-octet article bounds. Missing work/article/binding, stale attempts and
unencodable metadata are refused. Building the ADU is a read-only projection.
The existing workflow journal remains the sole owner of the one-shot external
submit permission and calls this projection inside its already-gated callback.

## Receipt path

`fn-bpo-receipt-intent-record` canonically decodes a kind-1 receipt ADU, converts
its nine fields to the existing workflow receipt, and constructs the existing
`:receipt-intent` journal record. Success additionally requires an explicit
`policy-authorizedp = t` supplied by the trusted local A-POLICY boundary and an
actual successful `fn-bp-apply-journal-record` preflight. Consequently the
workflow rechecks work ID, subject, configured receipt authority, peer EID,
policy, source incarnation, authorization context and terms, plus pending/fence
and transaction-reuse rules. Peer-supplied authorization-context bytes do not
authorize the receipt by themselves.

Transaction ID and generation are local arguments used only in the local
journal record. They are absent from `FN-BP-ADU`, along with Store allocation,
NNTP article numbers, BPA bundle IDs and transport status. The returned record
still requires the existing workflow journal's durable intent/outcome protocol;
this composition does not make preflight durable.

## Host boundary

`host/bp-outbound-host.lisp` provides two program-mode calls:

The sender loads it with `ld` after `host/workflow-host.lisp`; it reads the live
workflow global installed by `Acl2WorkflowReplay` and is not a certified book.

- `fn-bpo-host-request-adu(work-id, state)` derives the current durable attempt
  and returns raw ADU octets without mutating workflow effects. The workflow
  journal must call it only inside its successful `take_submit` callback.
  Refusal returns `nil`.
- `fn-bpo-host-receipt-record(receipt-octets, txid, generation,
  policy-authorizedp, state)` returns the exact local record after canonical
  decode, local policy authorization and workflow preflight. It is read-only;
  the existing journal adapter must publish and apply the record.
- `fn-bpo-host-receipt-validp` returns a primitive boolean for the same check.
  `fn-bpo-host-receipt-field-octets` returns one of the nine ACL2-derived text
  fields as octets, allowing Python to construct its fixed FNWF dictionary
  without parsing printed Lisp strings or selecting receipt fields itself.

BP delivery and status reports remain transport evidence only. Application
success still requires the matching receipt intent and durable outcome.

## Pinned ION/LTP transport binding

The optional native `app-journal workflow-ion-submit` path uses
`books/bp-ion-workflow.lisp` over the same FNWF journal. ACL2 first authors an
`:attempt` intent from the current durable work/configuration; its outcome is
published before one `:submit` effect may be consumed. ACL2 then authors an
append-only `:ion-route` record for that exact work, attempt and generation.
It binds the work's **application peer EID** separately from the operator's
configured **BP destination EID** and local ION source EID. That route record
is durable before the C helper may call `bp_send`.

The helper freezes the ACL2-authored request ADU to a private, barriered ION
file source and publishes one exclusive `observed-v1` line containing the real
RFC 9171 source EID, creation milliseconds and sequence. `fn-bpio-decode`
checks the bounded line grammar and canonical decimal fields;
`fn-bpiw-observation-record` checks its three EIDs against the durable current
attempt and route. Only then may native FNWF publish `:ion-observed`. Replay
rejects an observation without its prior route, mismatched route/source/peer,
or a second ID for the same attempt. Its BP work state and effects remain
unchanged. A missing line, helper timeout or failed FNWF publication after
`bp_send` is **uncertain** and cannot authorize automatic repost.

The existing native `workflow-receipt` operation accepts a returned kind-1
application receipt only with its explicit local authorization profile and
durable receipt intent/outcome. An ION bundle ID, LTP report or BP transport
status cannot substitute for that authorization and cannot release the archive
or forwarding obligation. The present CLI is a single-process, offline
workflow caller under the Store and FNWF locks; it does not assert live owner
dispatch, authenticated remote receipt policy, or every ION crash cut.
