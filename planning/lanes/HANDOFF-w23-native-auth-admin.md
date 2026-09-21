# W23 native AUTHINFO administration handoff

Source: `w23/native-auth-admin`, commits `f5026bd4..7ac60b44` on top of
W22 native auth `d111ef59`.

## Delivered boundary

`books/native-auth-admin.lisp` owns the principal action tail grammar and the
complete credential decision: list/set-password plan, shared
`fn-native-auth-login-namep`, prompt confirmation, explicit principal or local
principal derivation, existing `fn-authsec-enrol`, upsert, canonical sorted v2
serialization and the public-only report.  The password has no argv, plan,
result or report slot.  `fn-native-auth-admin-list` and
`fn-native-auth-admin-set-password` are the host-called semantic subjects.

`host/native/auth-admin.lisp` observes prompt octets twice and an exact salt
from `/dev/urandom`, then drives only the ACL2 result and persistence phases.
It holds `<auth-path>.lock` from recovery through the terminal result.  A fixed
`<auth-path>.stage` is removed and its parent directory barriered before the
observed final name is file/directory barriered and decoded.  Publication
enters `:replace-issued` before `rename(2)` and reports accepted only after the
final parent-directory barrier.  A lost replace result or barrier is
uncertain.  No per-process fence is used as restart authority.

The replacement phase is a thin subsystem wrapper over
`books/anchor-replace.lisp`; it does not reuse FNAN content/generation policy.
The fixed-stage recovery prefix is separate and proves on the actual
`fn-native-auth-admin-recovery-step`/trace that a present stage cannot reach
final-name recovery without a successful cleanup-directory observation.

The public operator join consumes:

- `fn-native-auth-admin-host-parse-argv`, over argv after the outer
  `principal` token;
- plan projections `-plan-{status,reason,action}`;
- action projections `-action-{kind,name,principal-text,principal-presentp,postingp}`;
- raw `(fnn-native-auth-admin-execute PLAN-RESULT AUTH-PATH)`.

Accepted action shapes are `(:list)` and
`(:set-password NAME PRINCIPAL-TEXT PRINCIPAL-PRESENTP POSTINGP)`.  The raw
executor receives the full ACL2 plan result, not a host-reparsed action.

## Evidence

Source loading of the book, wrapper and ACL2 test books completed with no ACL2
error.  `tools/host_check.py` loaded both new host files with ACL2 8.7 and left
the logic prompt.

`python3 -m unittest tests.test_native_auth_admin_fidelity -v` passed.  The
test invokes the real raw write/rename/fsync path through the executable ACL2
wrappers.  One case injects EIO immediately after the actual rename, observes
uncertain, then starts a fresh ACL2 process and recovers.  Another sends
SIGKILL at the same post-rename cut and recovers in a new process.  Recovery
also removes a fixed surviving stage and barriers its namespace before reading
the final registry.

Focused certification evidence will be recorded here from the final
source-preserving persvati run.

## Explicit limits

- Public `operator ... principal ...` routing is owned by the integrated
  runtime join; this packet supplies its bounded plan and executor.
- Credential changes are startup-pinned and report restart required.  There is
  no live generation/reload claim.
- `:fn-authsec-v1` is compatibility behavior: domain-tagged salted SHA-256,
  with no tunable cost or memory hardness.  This packet makes no offline
  guessing-resistance claim.  A successor needs a new version and explicit
  migration/refusal policy; it must not reinterpret v1 fields.
- SBCL may retain secret objects until garbage collection; the guarantee here
  is that secrets do not enter argv, plans, durable files, reports or logs, not
  secure heap erasure.
- Durability relies on the adjacent exclusive-writer convention and the
  observed filesystem barriers.  It is not a proof of storage hardware.
- The raw host checks that the custom credential parent already exists and is
  a non-symlink directory; it does not create arbitrary configured parents.
