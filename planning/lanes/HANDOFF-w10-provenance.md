# HANDOFF w10/provenance

Branch `w10/provenance`, worktree `build/lanes/w10-provenance`, from `dev`
`92e4a40`, merged with `dev` `43f33f6` (the `w9/records` `fn-defrecord`
migration) before packet 2 and again before the final certification.

The problem: `fn-retain-admissiblep` required `(stringp evidence)`, so every
writer rendered its provenance into a string and threw the structure away —
the inbound transit path produced `"peer-transit:<peer>"` and lost the
transit command, the RFC 5537 §3.2.1 Path diagnostic and the configuration
generation it had already computed; the POST path took a constant the HOST
typed. The inbound lane named it a cross-cluster blocker with no owner
(BOARD, `w6/peering-inbound-2 -> substrate`).

## What landed

| packet | what | commit |
| --- | --- | --- |
| 1 | `books/provenance` (four `fn-defrecord` kinds, `fn-provp`, `fn-prov-kind`, `fn-prov-render`, `fn-prov-describe`), `books/provenance-codec` (canonical octets and the wire string, K-PROV-1/2/3), `tests/acl2/provenance-tests`, prefix `fn-prov-`, three Makefile roots | `c13cbdd` |
| 2 | the widening: four recognizer conjuncts `stringp` → `fn-provp` | `0424352` |
| 3 | writers: `fn-store-prov-post` (the POST twin removed), `fn-peer-transit-provenance`/`-evidence` and the subject-equating theorem, `fn inspect --provenance`, `tests/test_provenance.py`; the wire form made printable | `7f50619` |
| 4 | RET-007, PRF-029, SCN-020, `specs/retention.md`, `specs/peering.md`, `specs/storage.md`, this handoff | below |

### The design decision that carries the lane

`fn-provp` **accepts every string** — that is the `:legacy` kind, verbatim,
no wrapper. So replacing `(stringp evidence)` by `(fn-provp evidence)` is a
widening, and `fn-provp-of-string` discharges every obligation the old
hypothesis discharged directly. **No theorem statement, hypothesis or hint in
the fan changed, and the measured cost of the fan was zero new failures.**

The second decision was made by the host boundary guard, not by the lane.
`fn-store-text-octetsp` (`host/store-host.lisp`) admits an evidence octet
only in 33 to 126, so packet 1's NUL-sentinel CBOR string could not cross
into the store (`fn-store-sn-prepare` answered `:invalid`, which is the guard
working). The canonical octets are unchanged; the WIRE form is those octets
in lowercase hexadecimal behind `"fnprov1:"` — printable, at most 256 octets
(`*fn-prov-max-field*` cut to 32 so it fits `fn-record-metadata-bytes-p`),
and built from `books/identity.lisp`'s `fn-id-hex-octets`/`fn-id-unhex` and
their two proved round trips rather than a second hexadecimal. **Because the
wire form is bounded printable text, the record grammar, `books/records`,
`books/replay`, `books/store-node*` and the checkpoint needed no change at
all.**

## Certification table

Farm, `persvati`, `--jobs 6`, remote root `/home/ember/fn-lanes/w10-provenance`.

| run | roots | result |
| --- | --- | --- |
| `run-20260920T193005Z-bdfb` (`--affected-by books/retention.lisp --closure`, installed 82 / uncached 181) | 353 | **331 certified**, 22 failed, all of them the two pre-existing open theorems and their cascade |
| `run-20260920T195626Z-f6a4` (`--affected-by books/provenance-codec.lisp --affected-by books/peer-inbound.lisp --closure`, installed 80 / uncached 187) | 71 | **59 certified**, 12 failed, all the `fn-peer-echo-reply-effects-well-formed` cascade |
| `run-20260920T200514Z-39c0` **final**, after the `dev` merge and the SUSPECT rename (`--affected-by books/retention.lisp --affected-by books/provenance-codec.lisp --closure`; evidence `build/acl2/certify-20260920T200622Z-2661769` on persvati) | 179 attempted (the rest came from the box cache) | **157 certified**, 22 failed |

Per root, for the roots this lane touched or created:

| root | state | evidence |
| --- | --- | --- |
| `books/provenance` | **certified** | `bdfb`, `f6a4`, `39c0` — `build/acl2/certify-20260920T193159Z-2332387`, `-20260920T195742Z-2575843`, `-20260920T200622Z-2661769` on persvati |
| `books/provenance-codec` | **certified** | `39c0` (final source) and `f6a4` |
| `tests/acl2/provenance-tests` | **certified** | `39c0` (final source) and `f6a4` |
| `books/retention` | **certified** | `bdfb` |
| `books/retention-invariants` | **certified** | `bdfb` |
| `tests/acl2/retention-tests` | **certified** | `bdfb` |
| `books/node`, `books/node-invariants`, `books/node-traces`, `tests/acl2/node-tests` | **certified** | `bdfb` |
| `books/replay` | **certified** | `bdfb` |
| `books/store-node`, `-invariants`, `-traces`, `-resolution` | **certified** | `bdfb` |
| `books/container-invariants` | **certified** | `bdfb` |
| `books/bp-release`, `books/bp-release-invariants` | **certified** | `bdfb` |
| `books/peer-inbound` | **admitted, not certified** | blocked on `fn-peer-echo-reply-effects-well-formed` (w6/peering-inbound-2's recorded open, unchanged by this lane — the book reaches it with every definition of this lane admitted) |
| `books/peer-inbound-invariants` | **admitted, not certified** | four new theorems proved by `tools/acl2 --timeout 560` against an included `books/peer-inbound`; the root has no certificate because its includee has none |
| `host/store-node-host.lisp` | **loaded and exercised**, not certified (host files are `:program` mode) | `python3 -m unittest tests.test_provenance tests.test_store_node_host` — 12 tests, OK, 118 s, this laptop |

The final run's 22 failures, named, so nobody re-discovers them. **None
mentions a provenance symbol except as a definition it admitted**; grepping
the failing logs for `FN-PROV` finds only `books/peer-inbound`, and there
only the type-prescription lines of the two definitions this lane added,
before it reached its own open theorem. `books/checkpoint-codec` now
CERTIFIES (w9/storage's fix arrived on `dev`); `books/byte-store-scan`
(`fn-bs-crash-select-names-are-an-outcome`), `books/checkpoint-publish`
(`fn-cpp-published-generations-retained`) and the two checkpoint test books
fail on `dev`'s own new work, not on anything here. The rest is:
`fn-peer-echo-reply-effects-well-formed` (books/peer-inbound) cascades into
`peer-inbound-invariants`, `nntp-auth`, `served`, `owner`, `owner-config`,
`owner-invariants`, `ideal`, `peer-feed-invariants`, `stx-authority`,
`stx-epochs`, `stx-index` and their five test books;
`fn-cpc-accepted-input-is-canonical` (books/checkpoint-codec, w9/storage's
recorded open) cascades into `checkpoint-publish` and two test books.

## Open, with obligations

1. **The transit path does not yet store the record.** `fn-peer-transit-
   provenance` exists and `fn-peer-evidence-is-the-legacy-rendering` proves
   the record renders to the string the transit path writes, but
   `fn-peer-injection-arguments` (`books/peer-inbound.lisp:306`, the
   seventh element of its answer, built at line 323) still passes
   `fn-peer-evidence`'s rendering, because the transit command is not in
   scope at `fn-peer-decide-transfer`.
   *Obligation*: add a `kind` formal to `fn-peer-decide-transfer`,
   `fn-peer-transfer` and `fn-peer-injection-arguments`, pass it from
   `fn-peer-step`'s IHAVE/TAKETHIS arms and from
   `host/owner-host.lisp:326,328`, and replace `(fn-peer-evidence peer cfg)`
   at `books/peer-inbound.lisp:232` (the offer probe), `:296` (the transfer
   capacity check) and `:323` (the argument list) with
   `(fn-peer-transit-evidence peer cfg kind diagnostic)` where `diagnostic`
   is `(fn-path-diagnostic (fn-peer-local-identity cfg) (fn-af-path-field-
   value article))`. K1/K2/K3 gain the formal in their statements; their
   proofs should not care, because `kind` flows only into the evidence.
   **The inbound lane owns those statements.** Posted as the BOARD ASK.
2. **The record itself never reaches the durable record.** Carrying a
   `fn-provp` rather than its wire string across the store boundary means
   `fn-prov-wire` at `books/store-node.lisp:115` and `fn-prov-of-wire` at
   `books/replay.lisp:278` and in `fn-sn-prepare-node`, and restating
   `store-node-invariants:121` `(equal (fn-record-release-evidence record)
   (fn-node-stage-evidence stage))` through the projection. Fourteen books
   mention `fn-sn-pending-record`/`fn-sn-record-bindsp`. K-PROV-1/2/3 are
   exactly the lemmas that change needs. **This lane did not attempt it**;
   the wire string was designed to make it unnecessary for correctness and
   optional for elegance.
3. **The two BP drivers still read a host constant.**
   `tools/run_bp_ingress.py:260` and `tools/run_bp_receive.py:239` take
   `run_store.metadata`'s third element, which is still
   `b"unsigned-legacy-v0"`. `fn-prov-make-bp` (node id, bundle identity,
   label) exists for them; the receive path has the bundle identity in scope
   (`books/bp-primary`, `fn-bpp-bundle-identity`) and the ingress policy
   carries the label (`fn-bpi-policy-evidence`). A `fn-store-prov-bp` seam
   beside `fn-store-prov-post` is the whole change.
4. **A duplicate refused at transfer does not cite the earlier acceptance's
   provenance.** K3 (`fn-peer-history-is-refused-at-transfer`) answers
   `(fn-peer-decision :have :history)`; the decision record has three slots
   and no provenance one, and `fn-peer-history-hasp` answers a boolean rather
   than the binding it found. *Obligation*: `fn-peer-history-find` returning
   the binding, a fourth slot on `fn-peer-decision`, and K3 restated as
   "the refusal's provenance is the provenance of the pin the binding names".
   That is a shape change to the decision record inside K1/K2/K3, so it
   belongs with open item 1. **Recorded open; no weakened version was
   written.**
5. **`:post` rendering is lossy on purpose.** `fn-prov-render` of a `:post`
   is the constant `"unsigned-legacy-v0"`, because that is the string the
   writer produced before this lane; two different POST provenances render
   alike. The test book exhibits the pair. The lossless forms are
   `fn-prov-wire` (durable) and `fn-prov-describe` (the CLI line).

## Interfaces a successor should know

- `(fn-provp x)` — true of every string. `(fn-prov-kind x)` ∈ `{:post,
  :peer-transit, :bp-receive, :local, :legacy}`.
- `(fn-prov-make-post principal generation)`,
  `(fn-prov-make-transit peer kind diagnostic generation)` with `kind` ∈
  `{:ihave, :takethis}` and `diagnostic` `(:match)` or
  `(:mismatch <identity-octets>)`, `(fn-prov-make-bp node-id bundle label)`,
  `(fn-prov-make-local reason)`. Every text field at most
  `*fn-prov-max-field*` = 32 octets.
- `(fn-prov-render p)` — the legacy string. `(fn-prov-describe p)` — the
  lossless line. `(fn-prov-wire p)` / `(fn-prov-of-wire s)` — the durable
  string and its inverse. `(fn-prov-durablep p)` — the one predicate a store
  writer checks.
- Host: `(fn-store-prov-post state)`, `(fn-store-prov-describe octets state)`,
  `(fn-store-prov-for-msgid octets state)`.
  Python: `bridge.prov_post()`, `bridge.prov_describe(bytes)`,
  `bridge.prov_for_msgid(bytes)`; `fn inspect --provenance`.
