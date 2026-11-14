# Durable local origin

The local acceptance origin is an explicitly configured tuple of positive u60
names: lineage, commit domain, and incarnation. These are allocated names, not
content digests and not proof of uniqueness or writer authority. Deployment
must assign disjoint origins to independent histories. A clean restart preserves
the tuple; restore/fork/transport requires the separately authorized establishment
protocol and cannot conceal lost acknowledged history by changing a name.

`fn2-origin` is a generated immutable core child. The native entry passes
`FN2_ORIGIN_LINEAGE`, `FN2_ORIGIN_DOMAIN`, and `FN2_ORIGIN_INCARNATION`, `FN2_HISTORY_ID`, and `FN2_HISTORY_INCARNATION` as text to
`fn2-origin-profile-from-text`. The ACL2 parser bounds input to nineteen decimal
digits before traversing it, admits positive u60 values, and never invokes the
Lisp reader. `fn init` and `fn serve` expose matching `--origin-*`, `--history-id`, and `--history-incarnation` flags. Missing
native configuration overwrites simulator fixture names and fails profile
admission; there is no operational default shared by every node.

The generated boot record contains the exact tuple. Creation writes and fences
canonical bootstrap units through the existing boot machine. Restart compares
the complete canonical, hashed unit to configuration before journal recovery or
listener release. Both commit record-header encoders and the transaction's
identity history/evidence producers read the same core child. The recovery
payload/replay header reader requires exact equality with that child before a
record can be consumed. Message-ID namespace and original imported receipt
fields remain separate and unchanged.

The six-book parser/immutable-child closure at `32094fae8` is certified on
qualified toolchain `8aeb1bea18968c6cd33ac633a80ebf67e4924504db112fd27eb11f16a27b2a8c`.
Evidence on forge under `/build/fn-durable-origin320-20261114/build/acl2/`:
`certify-20261114T223624Z-507331` (origin) and
`certify-20261114T223625Z-507367` (parser/child fixture). The first attempt
exposed a profile-construction guard obligation; an explicit local alist
preservation lemma discharged it without weakening the guard.

Composed source remains unqualified. Required gates:
bootstrap same-origin restart and changed-origin refusal; two initialized nodes
with distinct configured origins producing distinct receipts at the same local
position; origin persistence/first-accept crash cuts; current host/interface and
composed proof gates. The new parser fixture and structural rewrite fixtures do
not establish these end-to-end properties.

Physical store history-id and history-incarnation are distinct names, per
STORAGE-DESIGN-ASTRA's identity table. The same immutable carrier and canonical
bootstrap now hold the separate expected pair. Journal/page/seal packing,
recovery candidate/checker contexts, and sealer run/filter construction consume
that pair. `fn2-core-history-values` returns it without borrowing across turns.
New checkpoint/recovery implementations in the reclamation lane must consume
these exact readers; those consumers and CNS cursor/export headers are separately
coordinated integration work. Do not equate the pair with the semantic tuple or
advance it on ordinary boot.
