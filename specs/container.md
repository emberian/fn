# Object container

Status: wave-3 laboratory profile (C2-05; REP-001, REP-003). A container
carries articles with their exact octets, their content identities and the
identities they depend on, plus unknown objects it does not interpret. Every
check runs before anything is allocated, and an article that validates is
published through the node's own two-step transaction. The executable
decisions are `books/container.lisp`; the theorems are
`books/container-invariants.lisp`; the tampered-plus-valid witness and the
teeth are `tests/acl2/container-tests.lisp`.

## Shape

A container is `(version articles unknowns)` with version `1`. An article is
`(msgid content-id octets dependencies)`: the Message-ID as a string, the
declared identity in the `fn-id-subject` grammar (`sha256:` plus 64 lowercase
hex octets), the exact source octets, and a list of content ids. An unknown
is `(tag octets)`. The profile is `(max-articles max-article-octets
max-dependencies max-unknowns max-unknown-octets)`; `fn-ct-containerp` bounds
the article count and the unknowns, `fn-ct-article-shapep` bounds each
article. Unknown objects are bounded and never read (ENC-004):
`fn-ct-unknowns-are-never-consulted` says two containers that differ only in
their in-bound unknowns publish identically, and an unknown over the bound is
a container refusal, not a partial import.

## Validation

`fn-ct-article-validp` decides one article without a node:

- shape and sizes against the profile;
- identity: the declared content id equals `fn-id-subject` of the host's
  digest of the article's subject preimage, `fn-id-subject-preimage` of the
  octets (`fn-ct-identity-okp`; the same preimage `fn-id-subject-of-payload`
  hashes in `books/identity.lisp`).
  `fn-ct-identity-okp-is-spec-okp`: when that digest is the constrained
  `fn-frame-digest` of that preimage, the check is
  `(equal content-id (fn-id-subject-of-payload octets))`, the identity rule
  of `books/identity.lisp` under A-CRYPTO;
- dependencies: each content id resolves in the local store (an input set of
  ids) or to a sibling whose declared id matches, whose identity checks
  (`fn-ct-find-provider` skips a sibling that merely claims the id), whose
  shape checks, and whose own dependencies resolve, with a fuel of one step
  per article. A cycle exhausts the fuel: `fn-ct-self-dependency-never-validates`
  says that when the local store lacks a content id and the article the
  container provides for it (`fn-ct-find-provider`) depends on that same id,
  that provider never validates at any fuel.

Limitation, stated as such: dependencies are container metadata, not part of
the identified octets. Two articles with one content id can carry different
dependency lists, and the container's first identity-checked provider wins
(the tooth for the provider hypothesis shows exactly this). The D08/D15
grammar should carry the dependency list inside the signed object; until it
does, the container's dependency list is a relay hint, not authority.

## Acceptance

The composition for one validated article, and nothing else, is

```
(fn-node-complete (fn-node-prepare s generation msgid octets groups
                                   obligation-id subject evidence charge)
                  (fn-state-next-txid (fn-node-acceptance s))
                  generation completion)
```

with `subject` the content id as a string, `obligation-id` the string of
`fn-id-obligation` of the host's obligation digest, `charge`
`fn-charge-for-payload` of the octet count, and `completion` the host's
storage observation for that transaction, exactly as `fn-node-complete` takes
it. The result is `(status state receipt)`:

- `:invalid`: validation failed, or the obligation digest is malformed; the
  state is the input, the receipt `nil`
  (`fn-ct-invalid-article-leaves-node-unchanged`);
- `:refused`: `fn-node-prepare` returned its input (duplicate Message-ID,
  pending transaction, groups, retention capacity); state unchanged, no
  receipt;
- `:not-durable`: the completion was `:aborted` or `:indeterminate`; the
  state is the node's, no receipt;
- `:accepted`: the receipt `(:accepted msgid content-id obligation-id)`.

`fn-ct-receipt-implies-validated`: a result whose receipt has the receipt
shape validated the article, for any inputs whatever.
`fn-ct-accepted-is-complete-of-prepare`: an `:accepted` result validated,
saw `:durable`, saw `fn-node-prepare` change the node, and its state is the
composition above. `fn-ct-accepted-article-is-in-the-node`: an `:accepted`
result's Message-ID is in `fn-state-articles` of its state; the proof opens
`fn-node-prepare`, `fn-accept-prepare`, `fn-node-complete` and
`fn-accept-complete` one layer each and uses `fn-node-prepare-preserves-state`.

`fn-ct-publish-list` publishes a container's articles in order, each with its
own digest, obligation digest and completion. An invalid article is skipped
with the node its siblings see unchanged
(`fn-ct-invalid-head-does-not-block-siblings`), and an article whose
dependencies all resolve in the local store has the same verdict in any
container (`fn-ct-store-resolved-verdict-ignores-siblings`); the witness
shows a tampered first article, a valid second and a valid third that depends
on the second, with the second and third published. Whole-container
atomicity is not claimed and is not the acceptance unit (REP-003): the unit
is one article with its closure.

Under OBJ-004, `fn-ct-conflict-evidence` returns every article whose Message-ID
another article of the container carries with a different content id
(`fn-ct-conflict-is-evidence`); the node publishes the first and refuses the
second, and the container result carries both as evidence.

## Open (recorded, not weakened)

- **`fn-ct-identity-okp-is-spec-okp` has no per-hypothesis tooth.**
  `fn-ct-identity-spec-okp` is stated against the constrained
  `fn-frame-digest` (A-CRYPTO), so no ground term evaluates it and no
  `assert-event` exhibits a digest that is not the digest of the preimage and
  separates the two checks. What the test book exhibits instead is that the
  executable check discriminates between two digests for one article, so the
  equality is not vacuous. Same gap as codecs' `fn-frame-decode-is-open`.
- **Dependency lists are container metadata.** They are not inside the
  identified octets, so a container may attach a different dependency list to
  the same content id, and the first identity-checked provider of a content id
  wins. The witness `*ct-s-provider*` in `tests/acl2/container-tests.lisp`
  exhibits it. D08/D15 is the fix and is host/grammar work.
- **The records are positional lists, not opaque records.** Profile, article,
  unknown, container and result readers lose their definition runes at the
  export theory and the constructors `fn-ct-make-{profile,article,container}`
  exist, but there is no accessor-of-constructor lemma per field and no
  `-shapep` forward-chaining triple: the recognizers still carry `(len x)`
  conjuncts. Full §1 opacity is deferred rather than done half-way.

## Host work (proposals, not claims)

- Byte grammar (D08/D15): a CBOR sequence in the `records.lisp` style,
  `bstr "fn-c"`, `uint 1`, `uint article-count`, then per article `bstr
  msgid`, `bstr content-id`, `bstr octets`, `uint dependency-count`,
  `bstr dependency` each, then `uint unknown-count` and per unknown
  `uint tag`, `bstr octets`. Decoding must check counts and bounds before
  allocating, as `fn-record-decode-exact` does; a golden vector and a
  round-trip theorem are the acceptance gate for that book.
- `tools/run_container.py` (proposed): compute each article's subject-preimage SHA-256 and
  obligation digest, call `fn-ct-publish-container` through the host bridge,
  and write the store transaction with the existing store adapter; the
  completion observation comes from that adapter, never from the container.
- Fragment side: a container is the natural unit a
  [fragment journal](transfer-journal.md) candidate becomes once complete;
  the candidate octets are the container bytes to decode.
