# Native administrative configuration

Status: implemented host boundary plus ACL2 command plan.  This slice exposes
only durable `group create`, `group retire`, and `capacity` changes.  It does
not add a second public command grammar: public operator/control integration
must consume the same ACL2 plan and projections.

`fn-native-admin-plan` accepts at most sixteen nonempty ASCII words, each at
most 512 octets:

```
group create NAME
group retire NAME
capacity DECIMAL-UINT32
policy set path-identity IDENTITY
peer add NAME PATH HOST PORT INBOUND|- OUTBOUND|- ...
peer remove NAME
peer list
```

The plan produces `:create-group`, `:remove-group`, `:set-capacity`,
`:set-policy` (slot and value as the exact argv octets; the value must satisfy
`fn-path-identityp`, the recognizer a peer's identity also passes),
`:set-peer`, `:remove-peer`, `:list-peers`, and a tagged refusal.  It owns
decimal parsing and applies the existing bounded configuration group-label
predicate.
`fn-store-cfg-reconfigure` remains the sole owner of the record deltas,
configuration history, live reservation check, record encoding, and named
admission reason.

## Queries

`:list-peers` is the one kind that publishes nothing.
`fn-native-admin-result-queryp` is the predicate that says so, and the host
asks it rather than deciding for itself which kinds are safe to read: a query
takes the read-only executor, which opens the store non-writable and never
reaches the live owner's serialized reconfiguration.  Because that executor
takes the shared writer lock, a live owner refuses a query the way it refuses
`status`.

`fn-native-admin-peer-report` renders the listing from a configuration value's
peer rows.  The enumeration is `fn-cfg-peer-names` (books/peer-config.lisp,
the fold over the one `path-identity` row every peer has) and each record is
`fn-cfg-peer-find`; a row group that denotes no well-formed record contributes
no line rather than a partially rendered one.  Raw Lisp writes those octets to
a descriptor and renders no field, formats no number and supplies no name for
an absent half.

The native internal executor is `admin ROOT ...`.  It opens `ROOT` with the
existing nonblocking exclusive Store lock.  A running owner therefore produces
the existing explicit lock refusal; the executor never creates a second owner.
Before publication, its existing byte decoder invokes the logical
`fn-native-admin-candidate-openp` over the proposed exact configuration history
and observed article history.  A candidate must reach the same recovering node
state that ordinary startup requires.

Final configuration records use ACL2's fixed-width renderer:
`config/%08d.cfg` for generations 0 through 99,999,999.  The renderer reuses
the byte-store decimal digit definitions; raw Lisp never formats a persistent
configuration filename.  `fn-jpub` and `fnn-immutable-publish-effect` perform
the no-replace stage, file barrier, link, and `config/` directory barrier.  A
stage/file failure is refused, link or namespace ambiguity is uncertain, and a
durable outcome is accepted only after a fresh Store reopen sees the expected
generation.

`config/` is created and parent-fenced by initialization.  Administrative
publication does not create or repair it.  Existing recovery's suffix-only
enumeration and its total retained-name budget remain a separate namespace
validation/recovery-bound packet; this slice unifies generation *rendering*
without claiming that historical directory parser is validated.
