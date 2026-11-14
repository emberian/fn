# Durable local origin

The local acceptance origin is an explicitly configured tuple of positive u60
names: lineage, commit domain, and incarnation. These are allocated names, not
content digests and not proof of uniqueness or writer authority. Deployment
must assign disjoint origins to independent histories. A clean restart preserves
the tuple; restore/fork/transport requires the separately authorized establishment
protocol and cannot conceal lost acknowledged history by changing a name.

`fn2-origin` is a generated immutable core child. The native entry passes
`FN2_ORIGIN_LINEAGE`, `FN2_ORIGIN_DOMAIN`, and `FN2_ORIGIN_INCARNATION` as text to
`fn2-origin-profile-from-text`. The ACL2 parser bounds input to nineteen decimal
digits before traversing it, admits positive u60 values, and never invokes the
Lisp reader. `fn init` and `fn serve` expose matching `--origin-*` flags. Missing
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

Current source is unqualified. Required gates: parser/child admission;
bootstrap same-origin restart and changed-origin refusal; two initialized nodes
with distinct configured origins producing distinct receipts at the same local
position; origin persistence/first-accept crash cuts; current host/interface and
composed proof gates. The new parser fixture and structural rewrite fixtures do
not establish these end-to-end properties.

Physical store history-id and history-incarnation are distinct names, per
STORAGE-DESIGN-ASTRA's identity table. Their existing 1/1 literals remain an
explicit next implementation item: carry a separate persisted physical pair
through actual journal/page/checkpoint writers and recovery validators together.
Do not equate this pair with the semantic tuple or advance it on ordinary boot.
