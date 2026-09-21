# Operator and native command-surface audit — 2026-09-21

**Source audited:** `5763a3b` (`dev`). This is a bounded audit of current
operator-visible behavior and native migration seams. `bin/fn`,
`tools/run_owner.py`, and `tools/fn_native.py` are development-oracle surfaces
under D07; `packaging/fn-native` and native `--fn` positional verbs are not a
full operator CLI. No service-parity or deployment claim follows.

## Confirmed findings

1. **`[posting] enabled = false` governs only direct CLI posting.** `bin/fn`
   reads the field at line 100 and refuses `fn post` at lines 452–455.
   `command_run` (342–369) does not pass it to the owner. The actual owner
   projection, `host/owner-host.lisp:73–77`, calls `(fn-inj-make-config t ...)`.
   `books/served.lisp:878–882` consumes that `allow` bit for greeting,
   CAPABILITIES, and POST. Thus a disabled CLI post and an allowed served POST
   can coexist. This is an active development-operator defect, not native
   deployment behavior.

2. **`[posting] agent` is a log label, while durable injection reads another
   identity.** `bin/fn:101,268,329,350` uses it only in log text, although
   `fn init --agent` is described as an injecting-agent identity at line 815
   and `render_config` says it records that identity at lines 165–166. The
   owner calls `fn-owner-agent-of` (`host/owner-host.lisp:66–76`), which reads
   durable `path-identity`; the fallback is a fixed prototype value. The
   packaging example correctly calls `agent` log-only. An operator can see an
   `agent=...` log label that differs from the Path/Injection-Info identity.

3. **Malformed `fn run` options are reported as faults after an accepted-service
   log.** `tools/run_owner.py:1588–1593` makes `--max-connections 0` usage
   error 5. `bin/fn:367` logs `accepted service` before invoking it, then
   `command_run` catches `SystemExit` at lines 369–394 and maps code 5 to
   `fault` 4. The recorded witness shows all three outputs. This contradicts
   the documented configuration/command usage outcome.

4. **`fn init --listen` accepts an unstartable port.** `bin/fn:927–931` checks
   only that the suffix is decimal, so `127.0.0.1:70000` is written by a
   successful init when storage initialization succeeds. `tools/run_owner.py:1588–1589`
   then refuses it as usage 5. Native-config already constrains its port to
   1..65535 (`specs/native-config.md`), so this is also a concrete migration
   drift.

5. **Malformed TOML scalar types escape the CLI outcome table.** `Settings`
   calls `int(listener.get("port", ...))` at `bin/fn:84` and `int` for ACL2
   slots at line 123. `main` only catches StoreError, OSError, and UnicodeError
   (982–985). A quoted nonnumeric port emits a Python traceback and shell exit
   1, although `docs/operator.md:181–187` says a wrong configuration is
   `usage` exit 5. Native-config’s ACL2 parser already has tagged refusal for
   malformed values; this is legacy development-CLI drift.

## Concrete witnesses

`operator-surface-audit-2026-09-21-witnesses.txt` records two executed,
no-store malformed-input witnesses against the audited source:

- `fn run --max-connections 0` exits 4 after both an `accepted service` log
  and the owner parser's usage error 5.
- a TOML `listener.port = "not-a-port"` exits 1 with `ValueError` traceback.
- direct parser construction accepts `fn init --listen 127.0.0.1:70000`; the
  owner parser rejects the same port with exit 5.

The posting and agent findings are source-traced call-chain witnesses; no live
owner run was made on an unfrozen owner checkpoint.

## Next operator-unification packet

Make the ACL2 operator/config boundary return one tagged command result and
one normalized configuration, including a single posting-permission projection.
The native owner must consume that projection for both control submission and
served connection opening. Until then native-config must retain its explicit
refusal of nondefault posting settings; it must not silently claim the Python
field works. Decide one meaning for `posting.agent`: pass an ACL2-owned durable
path identity, or rename it as a log label and remove the inject-identity claim.

The packet needs deterministic teeth at the boundary: malformed port and slot
values yield `usage` before service logging; port-range policy is shared by
init and run; and a disabled posting projection yields the same non-posting
served greeting/CAPABILITIES/POST outcome as control submission. It should not
copy Python conversions or route the native operator through the Python
adapter.
