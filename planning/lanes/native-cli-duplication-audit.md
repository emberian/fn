# Native CLI duplication audit

**Scope: `bin/fn`, its current Python helpers, the native `--fn` dispatcher,
and operator-facing documents at `1c9f04a` plus this lane's native-entry
packet.**  This is a design/UX audit, not a claim that the native CLI is ready
to replace the deployed development CLI.

## Intended authority split

Today `bin/fn` is the only operator CLI.  `tools/run_store.py`,
`tools/run_owner.py`, and `tools/fn_native.py` are development/test and host
adapters; their overlap with `bin/fn` is useful as an oracle while the native
image grows.  That is not a production competing authority yet.

The future operator path has only these owners.  Native-config's frozen
diagnostic protocol is `config PROFILE-PATH`: raw host code passes bounded
file bytes to ACL2 `fn-native-config-load`, which returns `(:accepted config)`
or `(:refused reason)`.  The later operator verb passes raw `--config PATH`
and argv words to that same boundary; neither the shell launcher nor raw host
code supplies defaults.

| Concern | Single owner | Raw host responsibility |
| --- | --- | --- |
| `fn.toml` syntax, defaults, policy, bounds, supported-field refusal | native-config ACL2 boundary | bounded file read and inert token/AST transport only |
| operator command grammar and operation selection | ACL2 operator boundary | bounded argv octet transport only |
| store, configuration, acceptance, recovery, allocation decisions | existing ACL2 store/config functions | filesystem and socket calls after ACL2 accepts values |
| terminal line and exit outcome | ACL2 tagged result plus one native presentation boundary | emit returned bytes and exit code |
| image location and process replacement | `packaging/fn-native` | locate executable, clear image-customization environment, `exec` |

No Python parser, a second Common Lisp policy table, or another public CLI
belongs in that path.  Raw native `--fn store ...`, `reader`, `model`, and
transport verbs remain image diagnostics until the operator boundary supports
the complete command contract.

## Findings, ordered by operator risk

### 1. The native test adapter parses a wider command language than it can execute

`tools/run_store.py` accepts `group`, `capacity`, `peer`, `policy`, `anchor`,
and `statement` at [tools/run_store.py:2176](../../tools/run_store.py#L2176)
through [tools/run_store.py:2246](../../tools/run_store.py#L2246).
When `FN_HOST=native`, it sends every parsed command to
`tools/fn_native.py` [tools/run_store.py:2249](../../tools/run_store.py#L2249).
`store_protocol` only translates `post`, `inspect`, and `init` specially and
passes every other command word through
[tools/fn_native.py:53](../../tools/fn_native.py#L53) to
[tools/fn_native.py:75](../../tools/fn_native.py#L75).  The image accepts only
`init`, `recover`, `status`, `config`, `inspect`, `probe`, and `post` under
`store` [host/native/io.lisp:1814](../../host/native/io.lisp#L1814) through
[host/native/io.lisp:1824](../../host/native/io.lisp#L1824).

This is **intentional development-oracle duplication**, but it has an
unpleasant failure mode: a syntactically accepted direct-store command reaches
the image and becomes a late generic `unknown store command` usage error.
The native adapter should instead own a small explicit capability map:
supported commands translate; unsupported commands immediately return exit 5
with `native development adapter does not implement <verb>`.  It must not add
semantics or serve as the future operator parser.  The direct packaging entry
does not use this adapter.

### 2. Configuration/default authority is duplicated across Python entry points

`bin/fn` assigns host, port, posting, agent, auth, and ACL2 process defaults
in `Settings` [bin/fn:69](../../bin/fn#L69) through
[bin/fn:122](../../bin/fn#L122), renders the same profile independently at
[bin/fn:146](../../bin/fn#L146), and applies command overrides at
[bin/fn:920](../../bin/fn#L920).  `tools/run_owner.py` independently defaults
and bounds `port`, `max-connections`, and `clock-error-ms` at
[tools/run_owner.py:1561](../../tools/run_owner.py#L1561) through
[tools/run_owner.py:1593](../../tools/run_owner.py#L1593).  The packaged
example repeats the setting documentation at
[packaging/fn.toml.example:1](../../packaging/fn.toml.example#L1).

This is **current production duplication inside the Python development
surface**.  It can drift before a native deployment exists: for example the
two run parsers each state the defaults of 8 connections and 1000 ms.
It also makes type interpretation a host policy: `bool(posting.get("enabled",
True))` at [bin/fn:99](../../bin/fn#L99) treats the TOML string `"false"` as
true, rather than refusing a non-boolean value.  Native-config is the
designated replacement authority.  Its bounded parser
must return the full accepted/refused/defaulted configuration to the ACL2
operator boundary.  The native owner receives only those accepted fields.  It
must explicitly refuse `[acl2]` process settings and every profile key without
a native consumer rather than reinterpret, ignore, or re-default them in raw
Lisp.

### 3. The public command inventory has already drifted

The `bin/fn` parser registers twelve subcommands at
[bin/fn:810](../../bin/fn#L810) through [bin/fn:916](../../bin/fn#L916), but
its module synopsis previously listed only eight.  This was a low-risk,
operator-visible documentation defect, so this packet updates the synopsis to
list `statement`, `principal`, `policy`, and `peer` too.  `docs/operator.md`
correctly describes the current command as Python/ACL2 at
[docs/operator.md:21](../../docs/operator.md), while the raw native
dispatcher protocol is separately recorded in
[planning/lanes/native-cli-migration.md:20](native-cli-migration.md#boundary-and-completed-scaffold).

This is **documentation duplication**, not a semantic authority conflict.
The pleasant full-parity CLI needs one generated command reference from the
ACL2 operator grammar, with the Python development surface shown explicitly as
development-only until it is retired.  Do not make the raw `--fn` diagnostic
verbs aliases of operator commands.

### 4. Outcome codes have a common numeric table but no common operator presentation

The native image owns 0/1/3/4/5 at
[host/native/io.lisp:56](../../host/native/io.lisp#L56) through
[host/native/io.lisp:60](../../host/native/io.lisp#L60).  `bin/fn` separately
maps the storage outcomes to first words at
[bin/fn:50](../../bin/fn#L50) and emits its final line at
[bin/fn:984](../../bin/fn#L984).  `tools/run_store.py` instead prints
`store: ...` errors [tools/run_store.py:2262](../../tools/run_store.py#L2262),
and image commands print operation-specific text.  The existing split is
mostly **intentional oracle/test duplication**, but it would be a competing
production authority if a native operator command copied either Python format.

The parity contract should be: every storage/operator command emits exactly
one UTF-8 result line beginning with `accepted`, `refused`, `uncertain`,
`fault`, or `usage`, and exits 0/1/3/4/5 respectively.  The ACL2 operator
boundary returns the tagged outcome and detail fields; one native presenter
formats the line.  Streaming payload commands may write their documented
payload on stdout, but must put one outcome line on stderr.  Statement
verification retains its separately named verdict words and codes, as the
current Python CLI already documents at [bin/fn:968](../../bin/fn#L968).

### 5. The Python native launcher advertises a shared parser that cannot be deployed

`tools/fn_native.py` says it validates using the Python command parsers at
[tools/fn_native.py:2](../../tools/fn_native.py#L2) through
[tools/fn_native.py:16](../../tools/fn_native.py#L16), and imports those
parsers before `exec` at [tools/fn_native.py:113](../../tools/fn_native.py#L113)
through [tools/fn_native.py:125](../../tools/fn_native.py#L125).  This is
valuable for differential tests, but a deployed native node would still have
Python decide command syntax and several conversions.  The direct launcher in
this lane, [`packaging/fn-native`](../../packaging/fn-native), avoids that
entire path and only execs the saved image.

This is **intentional development-oracle duplication**.  Keep it for
differential tests under its explicit `tools/` name.  Do not install it as
`fn`, do not add it to service files, and do not route the native operator
command through it as a compatibility fallback.

## Full-parity pleasant operator contract

The eventual `fn` command has one stable grammar:

```
fn [--config PATH] init|run|post|group|capacity|peer|policy|status|recover|anchor|principal|statement ...
```

The native operator parser must support the option shapes and documented
behaviors of all twelve current commands before package entry points move.
It reads configuration once, gives the raw file and raw arguments to the
native-config/ACL2 boundary, then dispatches the returned canonical command.
Unsupported fields or commands are named refusals during migration; they are
not hidden, downgraded to raw `--fn`, or replaced with a read-only subset.

`fn --help` and command help come from the same grammar and identify the
active implementation as either `development-python` or `native-image`.  The
configuration profile is the full table in
[native-cli-migration.md](native-cli-migration.md#fntoml-native-profile),
including its availability/refusal status.  The existing service templates
remain on the development CLI until this contract, owner lifecycle, storage
migration, TLS/auth, anchor, and signing rows have direct-native evidence.
