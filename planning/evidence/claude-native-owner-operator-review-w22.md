# Independent review: native owner/operator entry (w22)

Claude Opus 5, worktree `build/lanes/w13-claude-review`, detached at
**`a7b155f1`** ("Document native operator entry and outstanding orderly
shutdown"). One pass, source inspection only. No edits, no commits, no builds.
Orderly shutdown is named outstanding in the HEAD commit and is not treated
here as a new finding.

Scope: `host/native/operator.lisp` (140 lines, read in full) and the owner
callback it reaches, `host/native/owner.lisp:654-673`.

## Two findings, both at the one operator→owner callback

Both live in `fnn-owner-run-normalized` (`host/native/owner.lisp:654-673`),
whose docstring is "Operator callback over ACL2-normalized projections; no
argv semantics", and whose caller `fnn-operator-execute-run`
(`host/native/operator.lisp:61-79`) exists to "Invoke the one owner entry only
with ACL2-normalized plan projections". The listener address is the one
projection that is not normalized by ACL2 — raw Lisp resolves it and picks the
family — and both findings follow from that.

### F1 — Only the literal `::1` works as an IPv6 listener; every other IPv6 literal is rejected.

`host/native/owner.lisp:663-669`:

    (address (if (string= host "::1")
                 (sb-bsd-sockets:make-inet6-address host)
               (sb-bsd-sockets:host-ent-address
                (sb-bsd-sockets:get-host-by-name host))))
    (family (if (= (length address) 16) :inet6 :inet))

`::1` is special-cased to a literal parse. Every other host string goes to
`get-host-by-name`, i.e. `gethostbyname(3)`, which is AF_INET only and does not
parse IPv6 literals.

*Trigger:* an operator configuration whose listener host is any IPv6 literal
other than `::1` — `fe80::1`, `2001:db8::1`, or the machine's own global
address. `fn operator <config> run` fails at resolution instead of binding.
`127.0.0.1` and DNS names work, so the gap is invisible until someone writes a
real IPv6 address.

*Implication:* the native owner cannot be bound to a non-loopback IPv6 address
at all, and the failure surfaces as a host fault (see F2) rather than as a
rejected configuration value. `fnn-listen` (`io.lisp:1636`) already accepts an
`address` and a `family` and needs no resolution — the restriction is entirely
in this caller.

*Smallest repair:* parse the host string as a literal first — try
`make-inet6-address` when it contains `#\:`, else `make-inet-address` on a
dotted quad — and resolve only when it is neither. Better, and consistent with
the module's stated contract: have ACL2 hand back the family tag alongside
`listener-host-octets`, since ACL2 already owns the rest of the run plan
(`operator.lisp:66-73`), and let raw Lisp do a pure literal parse with no name
service in the path.

*Scope limit:* read from source; I did not build the image or attempt a bind.
The claim about `gethostbyname` and IPv6 literals is a property of the C
interface SBCL wraps, not something I measured here.

### F2 — A bad listener host is reported as `fault` (exit 4), not `usage` (exit 5), contradicting the module's own classification rule.

`fnn-operator-read-config` (`operator.lisp:96-109`) is explicit and careful:
missing file, non-regular file and over-bound file are each
`fnn-usage-error`, and its docstring states that a later EIO "remains a host
fault". That is the intended operator contract — operator-supplied
configuration defects are `usage`.

The listener host is operator-supplied configuration too, and it does not get
that treatment. `get-host-by-name` signals `sb-bsd-sockets:name-service-error`,
which is an `error` but none of the `fnn-*` conditions, so it reaches
`fnn-operator-execute-run`'s handler (`operator.lisp:76-79`) →
`fnn-exit-code-for` (`io.lisp:89-96`) → the `t` branch → `+fnn-exit-fault+`.

*Trigger:* `listener_host` set to a name that does not resolve, e.g.
`nosuchhost.invalid`. Observed output is `fault operator run <condition>` and
exit 4 — the same class the host uses for EIO and internal defects — where a
missing configuration file on the same command yields `usage` and exit 5.

*Implication:* an operator cannot distinguish "I typed the host wrong" from "the
node is broken" by exit code, which is the distinction exit 5 exists to carry.
It also means a DNS outage reports the node as faulted.

*Smallest repair:* wrap the resolution in
`(handler-case ... (sb-bsd-sockets:name-service-error (e) (error 'fnn-usage-error :message ...)))`
at `owner.lisp:667-668`. If F1's repair lands and ACL2 owns the family, the same
wrap applies to the literal parse failure.

*Related, not a finding:* `get-host-by-name` also blocks with no timeout inside
the run path, so an unreachable resolver hangs `fn operator ... run` with no
diagnostic. F1's repair removes name service from this path entirely and with
it this exposure; I mention it because it is the same line.

## Confirmed landed, not re-reported

`fnn-owner-serve-client` now orders `(fnn-store-indeterminate (e) ...)`
(`owner.lisp:571`) ahead of the combined
`((or fnn-store-error fnn-os-error sb-bsd-sockets:socket-error) ...)` clause
(`:576`), with `serious-condition` faulting the service (`:578`). That closes
the outcome-collapse I reported against `d47212d`; `fnn-owner-serialized:413`
carries the same ordering. No action needed.

## Checked, nothing to report

* `fnn-operator-argv-octets:12-22` bounds count, per-argument length and ASCII
  before any octet reaches ACL2, using ACL2-supplied bounds
  (`operator.lisp:127-128`).
* `fnn-operator-read-config` re-validates through `fnn-read-regular-bounded`,
  which opens `O_NOFOLLOW` and re-checks regularity and size, so the
  lstat→open window is not exploitable.
* `fnn-exit-code-for` orders `fnn-usage-error` ahead of `fnn-store-error`
  (`io.lisp:93-94`), so usage does not collapse into refused.
* `fnn-dispatch`/`fnn-main` (`io.lisp:2041`, `:2100-2109`) do convert an
  escaping `fnn-usage-error` from `fnn-command-operator` into exit 5, so the
  uncaught path out of `fnn-operator-read-config` is handled.
* `:owner-required` (`operator.lisp:121-123`) returns usage rather than
  reaching for a store shortcut, matching the header's claim.

---

## Correction (appended after root disposition)

Root is right. Both triggers I stated for F1 and F2 are **unreachable through
the public operator**, and I retract them.

**The upstream restriction I failed to check.** `books/native-config.lisp:344`,
inside `fn-ncfg-normalize` (`:320`), makes the listener host `:bad` unless it is
one of three literals:

    (not (member-equal host '("127.0.0.1" "::1" "localhost")))

A `:bad` field collapses the whole normalization to `:bad` (`:339-342`), and the
caller returns `(list :refused :invalid)` (`:361`) — before any run plan exists
and therefore before `fnn-owner-run-normalized` is reached. So:

* **F1 retracted as stated.** `fe80::1`, `2001:db8::1` and any other IPv6
  literal never arrive at `owner.lisp:663-669`; ACL2 refuses them at config
  normalization. There is no public operator path on which the `::1`
  special-case leaves a reachable gap. F1 describes a latent property of the
  callback in isolation, not a defect of the operator.
* **F2 retracted as stated.** `nosuchhost.invalid` is refused by the same
  member test, so `get-host-by-name` is never handed an unresolvable name
  through the operator, and the `fault`-versus-`usage` divergence I described
  does not occur on that path. A bad host is already `refused` by ACL2.

**Mislabeled evidence.** F2 says "Observed output is `fault operator run
<condition>` and exit 4". I did not run anything. That sentence should read as
what the source would produce on that path, and it was wrong of me to phrase a
source reading as an observation — particularly after the earlier direction on
exactly this point. The whole report is source-only; nothing in it is observed
behaviour.

**What survives, smaller.** For the three admitted strings, the callback still
sends two of them through the name service: `owner.lisp:663-669` literal-parses
only `::1`, so `"127.0.0.1"` and `"localhost"` both go to
`sb-bsd-sockets:get-host-by-name`. That is an unnecessary resolver dependency
on a path whose entire input set is three fixed literals ACL2 already admitted.
A side effect worth one line for Terra's projection: because `localhost` is
resolved rather than projected, which family the owner binds for it follows the
box's `/etc/hosts` and NSS configuration rather than the ACL2-owned grammar.

This is the cleanup root describes, and it is Terra's to make the existing
three-name endpoint projection ACL2-owned. It does not require broadening the
listener grammar, and I am not proposing that.
