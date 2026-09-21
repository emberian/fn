# Root disposition: native owner/operator review

The independent Claude review ran interactively in tmux against `a7b155f1`.
Its [report](claude-native-owner-operator-review-w22.md) includes its correction.
No reported arbitrary-IPv6 or bad-hostname trigger reaches the public callback:
`fn-ncfg-normalize` admits only `127.0.0.1`, `::1`, and `localhost`, and operator
planning rejects a failed normalization before executing an owner callback.
The source-only report originally labeled a predicted result “observed”; that
wording is retracted. No runtime result follows from this inspection.

The remaining concrete cleanup is narrower: the callback consults a resolver
for admitted IPv4/localhost strings even though this fixed set has an ACL2-owned
loopback interpretation. The operator lane owns an endpoint projection using
only those existing strings. This does not add arbitrary listener support or
turn a resolver failure into evidence of an invalid public configuration.

Separately, the feed restart fold's admission/guard gap was repaired in
`03eb3ba3`: a record-list type lemma, explicit result-constructor theory, and
a test including the actual subject book. Its accepted two-peer witness now
uses nonempty restart-producing states; empty fresh feeds legitimately emit no
records. The [focused certification manifest](manifests/certify-20260921T094418Z-52829.json)
pins the book and test sources. The combined native default/DTN batch is frozen
at `03eb3ba3` and remains separate pending evidence.
