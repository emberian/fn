# Native administrative configuration

Status: implemented host boundary plus ACL2 command plan.  This slice exposes
only durable `group create`, `group retire`, and `capacity` changes.  It does
not add a second public command grammar: public operator/control integration
must consume the same ACL2 plan and projections.

`fn-native-admin-plan` accepts at most three nonempty ASCII words, each at
most 512 octets:

```
group create NAME
group retire NAME
capacity DECIMAL-UINT32
```

The plan produces `:create-group`, `:remove-group`, or `:set-capacity` and a
tagged refusal.  It owns decimal parsing and applies the existing bounded
configuration group-label predicate.
`fn-store-cfg-reconfigure` remains the sole owner of the record deltas,
configuration history, live reservation check, record encoding, and named
admission reason.

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
