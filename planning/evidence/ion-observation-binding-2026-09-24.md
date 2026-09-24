# Offline ION observation bound to one FNWF attempt

The optional `app-journal workflow-ion-submit` path now asks ACL2 for the
durable attempt, the separate BP route, and the exact request ADU before the
pinned C helper enters `bp_send`. The helper's `observed-v1` line is decoded
with bounded length, EIDs and canonical decimal fields. ACL2 checks its
application peer against the current durable attempt and its BP destination
and source against the route record before native FNWF may append
`:ion-observed`. Replay rejects a missing route, changed EID or duplicate
observation. `workflow-ion-status` distinguishes absent, routed/uncertain and
observed after reopen. These records do not mutate application work or emit
an application receipt, release, or transport replay effect.

ACL2 8.7, toolchain identity
`d5f2b9f0d2cf68c6074ea7046f4bd2e560d2984fe22d7e03f93045975ac889f0`,
was invoked on hbox with the pinned
`/tank/fn/toolchains/w28/acl2-literal-4g`, cache `/tank/fn/certcache`, two
jobs and a 180-second per-book bound. The selected command was
`python3 tools/farm.py submit hbox --root /Users/ember/dev/fn/build/lanes/ion-observation-binding --remote-root /tank/fn/lanes/ion-observation-binding --jobs 2 --timeout-seconds 180 --acl2 /tank/fn/toolchains/w28/acl2-literal-4g --cache /tank/fn/certcache books/frame books/frame-journal books/bp-ion-observation tests/acl2/bp-ion-observation-tests books/bp-ion-workflow tests/acl2/bp-ion-workflow-tests tests/acl2/frame-tests`.
Manifest [certify-20260924T062917Z-1013202.json](manifests/certify-20260924T062917Z-1013202.json)
records nine passing books including the decoder, frame codec and their
tests. The composite initially stopped at its first structural theorem: a
book-wide open admissibility predicate made it run to the limit, with no
counterexample. A pinned REPL proved both structural theorems in 0.01 second
each after keeping the route and observation recognizers closed. The exact
follow-up command selected `books/bp-ion-workflow` and
`tests/acl2/bp-ion-workflow-tests` with a 120-second bound; manifest
[certify-20260924T063332Z-1020278.json](manifests/certify-20260924T063332Z-1020278.json)
records both PASS in 3.227 seconds. The source digests, commands and closure
origins are in those manifests. The first REPL also admitted
`fn-bpio-bound-observation-binds-current-request-and-route`.

An attempted stronger `fn-bpio-bound-observation-makes-valid-record`
recognizer theorem did not finish in a bounded REPL attempt: the log stopped
at `Goal'` after opening `fn-bpio-bound-observation`,
`fn-bpio-bound-recordp` and `fn-bpio-recordp`. It was **removed**, not counted
as proved. The executable `fn-bpiw-observation-admissiblep` still checks the
record before publication/replay. The passing `fn-bpiw-ion-record-keeps-bp-state`
and `fn-bpiw-ion-record-emits-no-effects` are structural projections; they
do not prove complete workflow/retention trace refinement.

After replacing a host-local conversion dependency with the underlying ACL2
`fn-record-octets-string`, `host/workflow-host.lisp` loaded alone under the
same pinned ACL2 (`tools/host_check.py host/workflow-host.lisp`, PASS); that
file's SHA-256 was
`d9e15ca6a3da34fcaf7813d52e5f360d833e592194a224952e9c0120cace9446`.
SBCL read all forms of `host/native/workflow.lisp` without a reader error.
Other host files were not given a new standalone qualification: existing
`host/bp-release-owner-host.lisp` depends on the owner bridge load order, and
`host/native/workflow.lisp` depends on native verb registration. No new native
image was built or run. A source-matched native send/restart/fault fixture,
live owner dispatch, authenticated returned ION receipt, and complete
physical crash-cut refinement remain open. The previously qualified C helper
source-lifetime experiment is separate evidence; it cannot qualify this new
native caller by itself.

Root convergence review also corrected PRF-034 to `in-progress`: the new
host-called `fn-bpiw-replay-journal` needs a whole-replay correspondence to the
predecessor work-status theorem. The two structural projections above are
single-record results, not that induction. SCN-017 now names the mixed-history
reopen witness; no existing theorem was removed or weakened.
