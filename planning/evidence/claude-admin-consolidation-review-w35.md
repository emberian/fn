# Independent review: native auth administration consolidation (w35)

Claude Opus 5, worktree `build/lanes/w13-claude-review`, detached at
**`d54121b4`** ("Record native feed, credential and namespace integration
boundaries"), branch `dev`. Source inspection only — nothing built, nothing
run, so no statement here is observed behaviour. Not an approval gate.

Scope read: `host/native/auth-admin.lisp` (458 lines, read in full),
`host/native-auth-admin-host.lisp` (75), and the io primitives the admin path
depends on in `host/native/io.lisp`.

## No new findings

I found no defect on this surface at `d54121b4`. Below is what I actually
checked, so the negative result is auditable and root can see where I did and
did not look.

**Salt entropy — correct.** `fnn-native-auth-admin-csprng-salt`
(`host/native/auth-admin.lisp:123-144`) opens `/dev/urandom`, loops until the
ACL2-supplied width is filled, and treats a zero-length read as
`fnn-fault "OS CSPRNG ended before one credential salt"` rather than accepting
a short salt. It does **not** use CL `random`, which is what
`fnn-random-hex` (`io.lisp:366`) uses for staging names; the two are correctly
separated.

**Secret handling — correct.** `fnn-native-auth-admin-prompt-secrets`
(`:91-122`) opens `/dev/tty` and `fnn-native-auth-admin-read-secret-from`
(`:73-90`) clears `sb-posix:echo` via `tcsetattr` before reading, restoring the
saved `lflag` in an `unwind-protect`, so a refusal mid-entry still restores
echo. Secrets never appear in argv. `fnn-native-auth-admin-read-octet-line`
(`:55-72`) bounds the input at the ACL2 maximum, and the check order is right:
the LF test at `:65` precedes the `(>= count maximum)` refusal at `:66`, so a
password of exactly `maximum` octets is accepted rather than refused — the
off-by-one I went looking for is not there.

**Lock — correct.** `fnn-native-auth-admin-open-lock` (`:162-185`) opens the
adjacent `.lock` with `O_NOFOLLOW`, maps `ELOOP` to an explicit symlink
refusal, verifies `fnn-regular-p` on the descriptor, and takes `LOCK_EX |
LOCK_NB`, releasing in the caller's `unwind-protect` (`:456-457`).

**Symlink exposure on the registry itself — covered.**
`fnn-native-auth-admin-check-path` (`:149-154`) refuses a symlink or
non-regular node, and it is called on both the stage and the final name at
`:195-196`, inside `fnn-native-auth-admin-recover`, which runs under the lock
before any read. `fnn-native-auth-admin-read-held` (`:282-288`) then goes
through `fnn-read-regular-bounded`, which opens `O_NOFOLLOW` and re-checks
regularity independently. I specifically checked whether `check-path` was
defined but unused; it is used.

**Publication durability — correct.** `fnn-native-auth-admin-publish`
(`:299-362`) stages through `fnn-write-staged` (`io.lisp:1301-1304`), which is
`O_EXCL` + `fnn-write-all` + `fnn-fsync-file`, so the file barrier precedes the
rename. The model cut is entered *before* `rename(2)` (`:327-329`), so a
process death after the syscall cannot be reported as a known pre-publication
failure. A failure at the replace step maps to `:uncertain` (`:338-340`) and at
the directory barrier to `:uncertain` (`:357-359`); only the stage step maps to
`:known-fail` (`:315-317`). The `serious-condition` arms are deliberate and
conservative in the right direction — an interactive interrupt during the
rename yields uncertainty, not a claimed abort.

**Stale-stage interaction — covered.** `fnn-write-staged`'s `O_EXCL` would fail
on a leftover `auth.toml.stage`, but `fnn-native-auth-admin-recover`
(`:193-281`) unlinks it under the lock first (`:201-212`). If that unlink
fails, the subsequent `O_EXCL` raises into publish's `fnn-os-error` arm
(`:313`), which degrades to `:fault` rather than to a corrupted registry.

## One observation, deliberately not filed as a finding

`fnn-native-auth-admin-execute` (`:434-458`) acquires the exclusive lock at
`:447`, and `fnn-native-auth-admin-execute-held` (`:396-433`) calls the secret
reader at `:400-401`, which blocks in `read-char` on `/dev/tty` with no
timeout. The lock is therefore held for as long as an operator takes to type
and confirm a password.

*Trigger:* run `set-password`, leave the prompt unanswered. Any concurrent
admin invocation refuses at `:180`, "AUTHINFO credential registry is already
locked".

*Why this is not a finding.* Serializing credential administration is the
lock's purpose, and admin-vs-admin refusal under a live prompt is a defensible
outcome rather than a defect. **I did not establish whether any non-admin path
contends for `auth.toml.lock`** — in particular whether a running owner takes
it while reading the registry — so I am not claiming any service impact, and I
am not asserting the hold is harmful.

*Narrow repair if it is judged unwanted:* read the two secrets before
acquiring the lock. The secret does not depend on the held registry, so the
`recover` → `read-held` → publish ordering under the lock is unaffected; only
the human wait moves outside it.

## Limitations

Single revision (`d54121b4`), source only. I did not run the admin command, did
not exercise the ACL2 phase machines in `books/native-auth-admin.lisp` (I
treated their returns as the specification the raw module must obey, and
checked only that the raw module obeys them), and did not review the
`w23/native-admin` or `w23/native-operator-admin-join` branch tips, which are
ahead of `dev` on this surface. A defect introduced there would not be visible
here.

For context, not as a finding: F1 of the w28 control-lifecycle review is
repaired on this revision — `fnn-control-acquire-lease`
(`host/native/control.lisp:32-53`) now holds an adjacent lease before
`fnn-control-remove-stale` inspects the socket name, and the docstring at
`:25` states the lease rather than the Store writer lock as the exclusion.
