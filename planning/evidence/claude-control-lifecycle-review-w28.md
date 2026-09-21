# Independent review: native local-control lifecycle (w28)

Claude Opus 5, worktree `build/lanes/w13-claude-review`, detached at
**`866223f1`** ("make native control stop idempotent"), the revision that
carries `host/native/control.lisp`; it is not yet on `dev` (`3039f47b`).
Source inspection only — I built nothing and ran nothing, so no statement here
is observed behaviour. Concurrent with implementation, not a gate.

Filed at the name root requested. The request that produced this review
arrived truncated and carried no filename, so it was first written as
`claude-native-control-review-w25.md`; this file is that same review, content
unchanged, and the w25 copy has been removed so there is only one.

Scope: `host/native/control.lisp` (302 lines, read in full), its callers in
`host/native/operator.lisp:60-112`, and the owner entry points it composes
with in `host/native/owner.lisp`.

## F1 — Stale-socket removal unlinks a live socket, and its stated safety argument does not cover a reachable configuration

`fnn-control-remove-stale` (`control.lisp:24-30`) unlinks whatever socket node
it finds at the configured path. Its docstring gives the safety argument:
"Remove only an old socket node after the Store writer lock is held" — i.e.
a second owner cannot be live because it could not have taken the Store writer
lock.

That argument holds only when the control path is a function of the store
root. It is not. `books/native-config.lisp:335-336` reads `[control] path`
through `fn-ncfg-string-value` bounded only by `*fn-ncfg-max-path*`;
`(fn-ncfg-under-store store "/control.sock")` is supplied as the **default**,
not as a constraint, and nothing in `fn-ncfg-normalize` ties the accepted value
to the store root.

*Reachable scenario (configuration, not a race).* Two operator configs with
different `[store] path` — so two different writer locks, both acquirable —
and the same explicit `[control] path`. Owner A is running. The operator starts
owner B. B's `fnn-control-listen` (`:32-46`) calls `fnn-control-remove-stale`,
sees a socket node, unlinks A's live socket, binds and `chmod`s its own. A
retains its listener fd and keeps accepting on the now-unlinked inode, so it
reports nothing wrong; every later `fn operator … post`, which resolves the
path afresh in `fnn-control-connect` (`:253-260`), reaches B. Articles the
operator believes are going to store A are submitted to store B.

*The codebase already has the right witness at the other end.* `fnn-control-close`
(`:219-226`) refuses to unlink unless `stat-dev`/`stat-ino` match the node it
created — the `6fc78ca8` "attachment witnesses" fix. The removal end has no
equivalent check.

*Smallest repair.* Either constrain `[control] path` in ACL2 to lie under the
configured store root, which restores the writer-lock argument exactly as the
docstring states it; or, before unlinking, attempt `connect(2)` to the path —
`ECONNREFUSED` means no listener and the node is genuinely stale, a successful
connect means a live owner and this is a refusal, not a cleanup.

*Limitation.* I did not start two owners, and I did not test whether some other
layer rejects a shared control path. This is a reading of the config grammar
plus the removal code; treat the reachability claim as resting on
`books/native-config.lisp:335-336` being the only constraint on that field.

## F2 — Unconfirmed: a stopping thread `close(2)`s client sockets that workers may be using by raw fd

Stated as a suspicion. I have not observed it and it cannot be confirmed
without an interleaving or stress test, which I did not run.

The worker takes a raw descriptor and then uses it outside any lock:

    control.lisp:117-121
      (let ((fd (fnn-socket-fd socket)))
        (fnn-send-all fd (fnn-control-reply-octets status) …)
        (fnn-graceful-close fd))

`fnn-control-stop`, running on a different thread, closes those same sockets,
also outside any per-client synchronization:

    control.lisp:206-207
      (dolist (socket clients) (fnn-socket-shut socket))

and `fnn-socket-shut` (`io.lisp`) is `(ignore-errors (socket-close socket))`.

*The interleaving that would matter.* Worker reads `fd` at `:118`; the stopping
thread closes that descriptor at `:207`; the kernel reuses the integer for any
descriptor opened concurrently — another accepted control client, a feed
journal open, a staged file — and the worker's `fnn-send-all` at `:119` writes
the FNCT reply octets into it. The worker's own `unwind-protect` close at
`:143` is separately harmless because `fnn-socket-shut` swallows the
double-close; the exposure is the write, not the close.

*Why I think it is worth a line anyway.* `fnn-control-stop` already does the
narrower thing for the listener one paragraph earlier — `socket-shutdown
… :direction :io` before `fnn-socket-shut` (`:203-205`) — and does not do it
for clients. A `shutdown(2)` on the client sockets would unblock the worker's
send with an error while leaving the descriptor valid until the worker's own
`unwind-protect` closes it, which removes the reuse window without any new
synchronization.

*What would confirm or dismiss it.* A test that holds many control clients
mid-reply while `fnn-control-stop` runs, with descriptor-number logging around
`:118`–`:119`. Until that exists this is a code-shape concern, not a defect,
and I am not asserting the window is wide enough to hit in practice.

## Checked, nothing to report

* **Fault and uncertainty do not leave a broken store serving.**
  `control.lisp:105-108` catches `fnn-store-indeterminate`/`-fault`/`-error`
  and turns them into client statuses without faulting the service, which
  looked wrong until I read `fnn-owner-serialized` (`owner.lisp:418-430`): it
  calls `fnn-owner-stop-service-locked` with the uncertain or fault exit code
  *before* re-raising, so the service is already stopping by the time
  `control.lisp` classifies the condition. Correct as written.
* **Frame reads are bounded before allocation.** `fnn-control-append:48-55`
  checks `maximum` against the joined length before consing the buffer, and
  `fnn-control-read-frame:57-65` returns `:overbound` rather than growing;
  the bound comes from ACL2 (`fn-native-control-host-max-frame`).
* **Close-time unlink is witnessed.** `fnn-control-close:219-226` compares
  `stat-dev`/`stat-ino` against the values captured at `:184-185`, so a
  stopping owner will not remove another owner's socket.
* **Stop is idempotent.** The `first` flag under the mutex at `:195-200`
  ensures the listener shutdown and client sweep run once.

## Scope note, not a finding

`fnn-control-test-after-submit` (`:73-80`) is compiled into the shipped image
and sends `SIGSTOP` to the owner process when the environment carries
`FN_NATIVE_CONTROL_TEST_STOP=after-submit`. It is plainly deliberate — a
deterministic process-death cut for crash testing, guarded by an exact string
match — and I am not calling it a defect. Recording only that the seam is
environment-reachable in a production image, in case that was meant to be
build-gated.

## Conclusion

One configuration-reachable defect (F1: blind unlink of a live control socket,
with the fix pattern already present twenty lines below it), and one
concurrency suspicion I could not and did not confirm (F2). Everything else I
examined on this path — bounds, outcome classification, close-time witnesses,
stop idempotence — held up.
