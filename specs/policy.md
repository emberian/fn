# Group policy, authorization and the policy term

Status: local engineering profile from the substrate lane; certified books.
D11 (who controls group identity and policy) remains a proposal; see the
[decision packet](../planning/decision-packet-d09-d11.md).

Books: `books/policy.lisp`, `books/policy-invariants.lisp`; tests
`tests/acl2/policy-tests.lisp`.

## Shape

A group's policy is a statement of kind `:policy` by the group's AUTHORITY
principal whose payload `(group members terms)` names the group, the
principals authorized to post (at most 64, distinct) and terms. The policy in
force in a lace, `fn-pol-current lace keyring group authority`, is the
authority's latest candidate by (incarnation, sequence), where a candidate is
a member of the lace of kind `:policy`, creator equal to the authority,
verified under the keyring (`fn-prin-verifiedp`) and naming the group. Two
distinct candidates at the latest slot are an equivocation by the authority
and leave the group with no policy in force: nothing is admitted and both are
retained.

`fn-pol-authorizedp lace keyring group authority principal action` with
`:policy` (the authority only) and `:post` (a member of the policy in force,
or the authority). `fn-pol-admitp` admits a verified `:article` whose creator
is so authorized. Delegation depth is one (owner/admin succession, D11); the
authority's policy statement is the root block of
`~/dev/breadstuffs/metatheory/Dregg2/Crypto/CapabilityChain.lean` line 65
(`VerifyChain`, root verified under the root key) and the `WellFormed` chain of
`Dregg2/Authority/BiscuitGraph.lean` line 55 with no attenuation step yet.

## Theorems

| Theorem | Property | Hypotheses | Scope |
| --- | --- | --- | --- |
| `fn-pol-current-unchanged-by-foreign-delta` | merging any delta none of whose statements is a verified statement by the authority leaves the policy in force unchanged | `fn-pol-delta-without-authority-p delta keyring authority` | authority confinement of policy change, conditional on `fn-sig-verify` through the keyring |
| `fn-pol-admitp-unchanged-by-foreign-delta`, `fn-pol-authorizedp-unchanged-by-foreign-delta` | such a delta changes no admission or authorization decision | same | authority confinement of cross-post admission |
| `fn-pol-policy-change-needs-authority-signature` | if the policy in force changes across a merge, the delta contains a verified statement by the authority, and the theorem names it | none | the constructive contrapositive |
| `fn-pol-admission-is-grounded` | an admitted post is authorized by a `:policy` member of the lace, verified, by the authority, whose authorized set names the post's creator, and the post itself is verified | admission | grounding, twelve conjuncts in the style of `fn-bprv-replayed-receipt-is-grounded` |
| `fn-pol-current-is-not-superseded` | a candidate strictly below another candidate's slot is not in force | both candidates in the lace, `fn-pol-slot-lessp` | stale policy |
| `fn-pol-receipt-commits-to-term-by-construction`, `fn-pol-receipt-is-receipt` | the receipt for an admission carries `(id of the policy in force . evidence digest)` and is well formed | admission, obligation shape | by construction; named so |
| `fn-pol-receipt-re-verifiable` | in a canonical lace the receipt's policy id resolves by lookup to the policy that authorized it, and `fn-pol-receipt-groundedp` holds | lace well formed and canonical, admission | uses `fn-lace-lookup-of-member`; the canonical premise fails under a colliding digest (tested) |
| `fn-pol-signed-receipt-carries-term` | a receipt statement's payload decodes to the receipt | receipt well formed | the term travels with the signed bytes |
| `fn-pol-unverified-is-not-candidate-by-definition`, `fn-pol-unverified-is-not-admitted-by-definition`, `fn-pol-no-policy-in-force-admits-nothing-by-definition` | refusals | | definitional; named so |

Teeth (`policy-tests`): a forged policy (authority's id, another key) and an
outsider's own policy for the group are not candidates and change nothing; an
outsider's post and a forged post under a member's id are not admitted; a
genuine later policy supersedes the earlier one (the foreign-delta hypothesis
is load-bearing); an equivocating authority yields no policy in force and no
admission until a later unforked policy; a receipt names which policy
authorized it and still resolves after that policy is superseded; a receipt
naming an absent or foreign policy is not grounded; the evidence digest changes
with the keyring; under the length digest a colliding article makes the
receipt's id resolve to the article.

## The policy term

The term is `(content id of the policy statement in force . fn-digest-tagged
"fn-policy-evidence-v1" evidence)` where the evidence is the item sequence
`bstr key-for(authority) || bstr key-for(creator) || bstr encode(statement)`.
A receipt commits to the term, never to a boolean (ATLAS law 12: bind the
policy term, not the decision bit). A later reader with the lace and the
keyring recomputes both halves.

Proposed adoption into the journals (next wave, not done here):

| Record | Today | Add |
| --- | --- | --- |
| FNWF `enqueue` (`books/bp-workflow-records.lisp`, `tools/workflow_journal.py`) | `policy-id` text | `policy-stmt-id` (32 octets), `policy-evidence` (32 octets) |
| FNWF `receipt-intent` | `policy-id` text and the receipt fields | `policy-stmt-id`, `policy-evidence` copied from the validated receipt |
| FNRJ `request-context` (`books/bp-receipt-records.lisp`, `tools/receipt_journal.py`) | `policy-authorized` constant `t` | replace with `policy-stmt-id`, `policy-evidence`; the record is valid only if the pair resolves in the local lace |
| FNRJ `receipt-intent` | `policy-authorized` constant `t` | replace likewise; `fn-bpr-prepare-receipt` takes the term instead of `t` |

This closes review defect D9 at the record level once adopted.

## Assumed

A-CRYPTO through `fn-prin-verifiedp`; the keyring is the node's resolved
principal table ([identity](identity.md)) and is fixed during evaluation; the
lace is canonical for re-verification; A-POLICY's "authorized and identified
context" is now the pair (authority principal, policy statement in force)
rather than a caller-supplied boolean.
