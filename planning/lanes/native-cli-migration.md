# Native CLI, configuration, and packaging migration

**Status: design and direct-image entry scaffold only (2026-09-21).**  The
installed operator command remains the Python development CLI, `bin/fn`.
`packaging/fn-native` is a direct saved-image entry for the verbs that an
image already implements.  It does not provide a production replacement for
`bin/fn`, and neither the existing service unit nor the launchd plist changes
in this packet.

## Boundary and completed scaffold

The deployed command must execute `build/fn-host --fn ...` directly.  A shell
launcher may locate the image, clear ACL2 customization variables, and `exec`
it; it must not import Python, parse TOML, select a profile, fill defaults,
check semantic bounds, or translate a command into a second protocol.  The
new [`packaging/fn-native`](../../packaging/fn-native) does exactly that.  A
missing image is an unavailable runtime fault (exit 4); once it execs, the image's outcome is
passed through unchanged: accepted/query 0, refused 1, uncertain 3, fault 4,
and usage 5 (HST-003).

The native entry's currently implemented protocol is:

```
fn-native store ROOT init [GROUP ...]
fn-native store ROOT post MESSAGE-ID PAYLOAD CHARGE|- FAULT|- GROUP ...
fn-native store ROOT recover|status|config
fn-native store ROOT inspect MESSAGE-ID
fn-native store ROOT probe COUNT
fn-native reader PORT ONCE ROOT|-
fn-native model CHUNK-PATH ROOT|-
fn-native sha256 PATH
fn-native tcpcl ...
fn-native bp ...                 # DTN image profile
fn-native owner run ROOT PORT ONCE MAX-CONNECTIONS  # when owner build lands
```

Those words are the raw image dispatcher protocol, not a stable operator CLI.
`store config`, `probe`, `model`, `sha256`, `tcpcl`, and `bp` are diagnostic,
test, or transport surfaces and are not evidence of operator parity.  The
shell launcher deliberately leaves argument checking to the image, including
the image's guard-checking-on assertion.

The companion test
[`tests/test_native_cli_launcher.sh`](../../tests/test_native_cli_launcher.sh)
executes the launcher with an executable host stand-in and verifies the exact
`--fn` argument boundary and missing-image outcome.  It invokes no Python on
the launched path.  It tests the packaging boundary; it does not validate a
native image or certify a host book.

## Current deployed command inventory

`bin/fn` is the only deployed operator command today.  It uses Python 3.11
`tomllib`, `argparse`, the `run_store` ACL2 subprocess bridge, and, for `run`,
`run_owner`'s socket/TLS/control implementation.  Its complete subcommand
surface is below.  `config` and `inspect` belong to `tools/run_store.py`, but
are not `bin/fn` subcommands.

| `bin/fn` command | Current runtime dependency surface | Native wrapper now | Migration work required |
| --- | --- | --- | --- |
| `init` | TOML read/write; `run_store`; ACL2 subprocess | `store ROOT init [GROUP...]` | Native config writer plus ACL2 configuration construction and validation. |
| `run` | TOML; `run_owner`; TCP/Unix sockets; TLS; auth file; owner control protocol | owner protocol is being added by owner convergence | Native config handoff, listener/auth/TLS startup, control lifecycle, and service integration. |
| `post` | TOML; `run_store`; local control socket or ACL2 bridge | `store ROOT post ...` | Native operator option parser and config-derived routing; preserve control-owner behavior. |
| `group` | TOML; `run_store`; ACL2 bridge | none | Native ACL2 configuration-change wrapper and parser. |
| `capacity` | TOML; `run_store`; ACL2 bridge | none | Native ACL2 capacity wrapper and parser. |
| `peer` | TOML; `run_store`; ACL2 bridge; NNTP/BP peer values | none | Native ACL2 peer-record wrapper and parser. |
| `policy` | TOML; `run_store`; ACL2 bridge | none | Native ACL2 policy-slot wrapper and parser. |
| `status` | TOML; `run_store`; optional local owner probe | `store ROOT status` | Native configuration-derived root/control lookup and owner-liveness path. |
| `recover` | TOML; `run_store`; Roughtime client/verification | `store ROOT recover` only | Native pinned-anchor selection, UDP request, signature verification, and recovery report. |
| `anchor` | TOML; Roughtime JSON server table; UDP; crypto bridge | none | Native anchor client, pinned-key manifest reader, and ACL2 anchor-record boundary. |
| `principal` | TOML; credential TOML; terminal password prompt; ACL2 secret/signing helpers | none | Native credential parser/writer, secret boundary, principal derivation/listing. |
| `statement` | `tools/stx`; ACL2 subprocess; optional real Ed25519 | none | Native statement parser, keyring boundary, and verified Ed25519 implementation. |

The native image also has `reader`, `model`, `tcpcl`, and (in the DTN profile)
`bp` verbs.  They are independent host/test/transport interfaces, not
substitutes for the omitted operator commands.

## Required native configuration path

1. Define a bounded external configuration grammar that produces only an
   inert octet/string/natural AST.  The native parser must never call the Lisp
   reader, evaluator, `read-from-string`, or accept package syntax from a
   configuration file.  Reject duplicate keys, unknown fields, invalid UTF-8,
   excessive nesting/size, and non-canonical numeric syntax before allocating
   unbounded objects.
2. Add an ACL2 callable that receives that bounded AST and returns a tagged
   result: `accepted` with canonical configuration fields, `refused` with a
   reason, or `fault`.  ACL2 owns profile selection, default values, numeric
   bounds, loopback policy, TLS-pair policy, posting/auth policy, and the
   store configuration record.  The raw host only turns the accepted fields
   into bounded OS calls.
3. Keep secrets separate from the general configuration AST.  The credential
   reader follows the same inert-parser rule and passes verifier material to
   an ACL2 secret/configuration boundary; it never implements password or
   policy semantics in raw Lisp.
4. Give the native CLI a real option grammar with the same inert-data rule.
   It passes parsed values to ACL2 rather than applying Python's current
   defaults or validation in Common Lisp.  Each command prints one outcome
   line and exits 0/1/3/4/5.  Statement verdict codes remain separately named
   rather than borrowing storage-outcome words.
5. Only after all rows in the inventory have native implementations and
   equivalent outcome tests may `bin/fn` be replaced in `fn.service` and
   `net.fn.plist`.  Until then, these files continue to identify the Python
   CLI as a development service, and `fn-native` must be labeled experimental.

### `fn.toml` native profile

The native configuration lane owns the inert parser, ACL2 normalization
wrapper, and its tests.  The launcher contract is deliberately smaller: it
passes neither parsed settings nor defaults.  Its frozen diagnostic image
protocol is `config PROFILE-PATH`: raw host code reads bounded bytes and calls
`fn-native-config-load`, whose ACL2 result is `(:accepted config)` or
`(:refused reason)`.  File-read failures remain host `fault` outcomes.  The
later operator verb receives raw `--config PATH` and argv words without shell
or launcher parsing and uses that same boundary; its exact command spelling
will be published with the operator grammar.

The compatibility target is the entire currently documented `fn.toml`
surface.  The table is a contract for native-config implementation and for
the later native `init` writer.  A table or key outside this profile is
refused with exit 1 before service startup; it is never ignored, evaluated as
Lisp, or silently supplied by host code.

| Table and key | Native profile rule | Current availability |
| --- | --- | --- |
| `[store].path` | Required bounded path value. ACL2 validates its presence and canonical configuration use; raw host applies accepted path to bounded filesystem calls. | Needed for every store verb; direct raw `store ROOT` diagnostics already take a positional root. |
| `[listener].host` | Optional; ACL2 defaults to `127.0.0.1` and accepts only the documented loopback identities. | Requires native owner configuration handoff. |
| `[listener].port` | Optional natural; ACL2 defaults to 1119 and enforces its service bound before the host converts it for a socket. | Requires native owner configuration handoff. |
| `[listener].tls_cert`, `[listener].tls_key` | Optional bounded paths; ACL2 enforces the pair-or-neither policy. | Unsupported until native TLS startup exists; refuse the profile rather than drop either path. |
| `[posting].enabled` | Optional boolean; ACL2 defaults true and owns posting policy. | Unsupported for the native operator surface until owner/post control applies it. |
| `[posting].agent` | Optional bounded identity; ACL2 defaults the documented operator identity and validates it. | Unsupported until native post/control owns injection attribution. |
| `[anchor].server` | Optional bounded server identifier; ACL2 selects/validates pinned server policy. | Unsupported until the native pinned-anchor client and verifier land; refuse when present. |
| `[auth].required`, `[auth].protected_only` | Optional booleans; ACL2 defaults false and owns the connection policy. | Unsupported until native owner/auth configuration applies them. |
| `[auth].path` | Optional bounded credential-file path; ACL2 owns the reference policy. | Unsupported until the inert credential parser and native verifier path land. |
| `[log].path` | Optional bounded host-output path. ACL2 decides whether logging is enabled; host opens only an accepted path. | Unsupported until native owner logging is wired. |
| `[control].path` | Optional bounded Unix-socket path. ACL2 owns its default/reference; host owns socket creation after acceptance. | Unsupported until native owner control lifecycle is wired. |
| `[acl2].path`, `[acl2].slots` | Python development-process controls, not settings a saved image can honor. | Explicitly refused by the native profile. They must be removed from a configuration migrated to the direct image; they are not ignored. |

The native parser also refuses duplicate tables/keys, non-table values where a
table is required, unknown tables/keys, invalid UTF-8, oversized paths or
strings, out-of-range numerals, and syntactically accepted but currently
unsupported fields.  A field becomes available only with a named native
consumer and direct-native test; this prevents a configuration from claiming
a TLS, anchor, credential, or control behavior that the saved image does not
perform.  The native `init` implementation must write only fields whose
native consumers are available, with the same canonical profile selected by
ACL2.

## Packaging sequence

1. Build and install the selected saved image and `.core` with
   `tools/build_native_host.sh`; record the certified artifact set that the
   image loaded.  Install `packaging/fn-native` beside it as the direct entry.
2. Add a native configuration path and command grammar first, then an
   explicit `fn-native init`/administration operator surface.  It must either
   implement each listed `bin/fn` behavior or refuse it explicitly with exit
   5 and a named missing capability during development; no command may be
   discarded or silently mapped to a different operation.
3. Keep the raw `owner run ROOT PORT ONCE MAX-CONNECTIONS` and raw `reader`
   entries in the explicit developer image only. The default production image
   starts its owner solely through `operator CONFIG run`, after ACL2 has parsed
   and normalized the configuration. The packaging layer passes words through
   and does not reproduce operator or owner option/default semantics.
4. Produce separate systemd and launchd native templates only after the
   native configuration/owner path can supply the exact store, listener,
   log, control, TLS, and credential fields.  Retain the existing stop,
   restart, writable-path, and exit-outcome behavior and test SIGTERM and
   recovery through the native service.
5. Replace `bin/fn` in package entry points only with a release evidence set:
   direct-native command tests for every inventory row, old-store migration or
   refusal tests, fault/recovery cuts, native service lifecycle tests, and an
   image/artifact manifest.  This plan makes no release or production-readiness
   claim.

## Largest missing dependency surfaces

1. **Configuration and CLI ownership.**  There is no native inert TOML
   parser, no ACL2-owned operator configuration decision, and no native
   full-command parser.  Existing `tools/fn_native.py` deliberately uses the
   Python parsers for test compatibility and therefore cannot be deployed.
2. **Owner/service controls.**  The native operator now supplies the
   configuration-to-owner path, and the production/developer image split
   removes raw owner/reader alternatives from the production entry surface.
   Full service-supervisor lifecycle and remaining operator parity still need
   the ACL2/native path.
3. **TLS and authentication.**  Python `ssl`, credential TOML, password
   prompting, and auth-file policy currently serve `run`/`principal`.  Native
   TLS trust and credential handling need bounded raw I/O plus ACL2-owned
   policy.
4. **Anchor cryptography.**  `recover` currently calls a Python Roughtime UDP
   client, reads `roughtime_servers.json`, and uses crypto helpers to verify
   pinned signatures.  The native image's current `recover` reports only its
   existing store state; a pinned-key manifest grammar, UDP client, and real
   signature verification are required for parity.
5. **Statement/principal signing.**  `tools/stx.py` and the credential tools
   are Python/ACL2 subprocess surfaces.  Real Ed25519 signing, keyring
   handling, and secret storage must have native, bounded implementations.
6. **Store codec convergence.**  The native storage-codec lane owns
   `host/native/io.lisp` metadata/frontier/transaction-name adoption and old
   store handling.  This CLI lane does not duplicate that work; native CLI
   promotion waits for its frozen image interface and migration evidence.

## Ownership and handoff

- This lane owns this plan, `packaging/fn-native`, and its boundary test.
- `owner_convergence` owns `host/native/owner.lisp` and its build-layer
  inclusion; the planned owner protocol is recorded here without changing
  that code.
- `native_storage_codec` owns `host/native/io.lisp` metadata and codec
  realization.  Its current store protocol is recorded above; this lane does
  not alter it.
- Root owns decisions, top-level specifications, and registries.  This file
  is an implementation plan and creates no registry claim.
