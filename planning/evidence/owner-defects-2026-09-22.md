# The three node defects the client exercise found — 2026-09-22

[`fn-client-915-2026-09-22.md`](fn-client-915-2026-09-22.md) ends with three
findings it called the node's and did not touch. This record reproduces each
one against the same node, names the line that causes it, and records the
change. A fourth, found by the `w32/operator-verbs` lane in the same file
family and handed to this one, is recorded with them: a developer-only
process-death cut that a production image honoured. No book changed here and
nothing here is a certification record; one ACL2 process was started, to read
an answer out of an already certified book, and it proved nothing.

## The node these were reproduced against

| what | value |
| --- | --- |
| image | `/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host` on persvati |
| image source revision | `915d5c729877eddee7dd3f72eadad21cca463d1a` |
| store and configuration | `/home/ember/fn-gates/w32-client/`, the node the client lane left; listener `127.0.0.1:11340`, `[posting] enabled = true`, groups `fn.letters` and `fn.agents` |
| start | `nohup env FN_NATIVE_HOST=IMG packaging/fn-native operator CFG run > owner-w32defects.log 2>&1 &` from the `freeze-f7190d69` checkout, pid 328658 |
| reached from | macOS, `ssh -N -L 11340:127.0.0.1:11340 persvati` |
| stop | `kill -TERM 328658` (the process was already dead of defect 1 by then; the tunnel was closed and nothing was left running) |

## 1. A POST over the body limit stopped the process

### Reproduced

A raw client sent `POST` and then an article of an exact canonical size,
counting each line as its octets plus CRLF.

| canonical article octets | what the node answered | the process |
| --- | --- | --- |
| 32 760 | `441 posting failed; the article exceeds the configured size` | alive |
| 32 772 | nothing; the connection closed with no reply | **dead**, `owner core/store fault; process stopped: plaintext owner read left a suffix without TLS` then `fault operator run` |

So the boundary is 32 768, and the clean 441 just below it is the *injection*
refusal. The bracket in the client record (about 32 250 accepted, about 33 031
fatal) is this boundary seen through a client that did not control the exact
size.

### The cause

32 768 is `*fn-store-max-payload*` (`host/store-host.lisp:28`), which
`fn-owner-post-config` (`host/owner-host.lisp:80`) makes the injection
configuration's `max-octets`, which `fn-own-body-limit` (`books/owner.lisp:639`)
gives `fn-served-open` (`books/owner.lisp:673`) as the connection's wire body
limit. When a body line would carry the retained article past that limit,
`fn-wire-after-line` (`books/wire.lisp:721`) answers
`(fn-wire-close wire-state :body-overlimit)`: the wire is **closed**, mid-article.

`fn-served-feed-counted` (`books/served-tls-prefix.lisp:27`) stops at a closed
wire, so the count it returns is a **prefix** of the octets it was given. That
count is what the host receives: `fn-own-read-tls-prefix` ->
`fn-ocfg-read-tls-prefix` -> `fn-owner-chunk` (`host/owner-host.lisp:1018`) puts
it in `fn-owner-consumed`, and `fnn-owner-handle-chunk`
(`host/native/owner.lisp`) returns it as `consumed`.

`books/served-tls-prefix.lisp` states the partition this count induces:

```
(defthm fn-served-tls-prefix-suffix-accounting
  (let ((count (fn-served-counted-consumed (fn-served-step-counted conn octets))))
    (equal (append (take count octets) (nthcdr count octets)) octets)))
```

and `fn-served-step-counted-fast-consumed-is-bounded` gives `count <= (len
octets)`. Neither says the count is the whole read, and nothing in the books
does. **The bound is right; the host was wrong about it.** No ACL2 definition
was changed.

The host had three arms for that count. With a TLS channel it requires an exact
consume. With a TLS context but still in plaintext it consumes exactly the
prefix from the socket (the read was a `MSG_PEEK`), so the suffix stays in the
transport. With neither — the ordinary plaintext node — it faulted:

```
((/= consumed (length incoming))
 (fnn-fault "plaintext owner read left a suffix without TLS"))
```

`fnn-fault` raises `fnn-store-fault`, which `fnn-owner-serve-client`'s handler
sends to `fnn-owner-fault-service`, which stops the whole service. A client that
posts a long article breaks no invariant, and it stopped the node for everyone.

### What the model answers instead

Read out of the certified `books/served-tls-prefix` (ACL2 8.7 over SBCL 2.6.8,
macOS; `books/served-tls-prefix.cert` of 2026-09-22 08:32; nothing certified,
nothing written). A connection opened with body limit 40, handed one chunk of
130 octets carrying `POST`, four header lines, a 40-octet body line, a second
body line past the limit and the terminating `.`:

```
CHUNK-LEN 130
CONSUMED  61
WIRE-MODE :CLOSED
KINDS     (:REPLY :BEGIN-ARTICLE :REPLY :CLOSE)
E2 reply  441 posting failed; the article was not received
```

`fn-nntp-post-step` (`books/nntp-post.lisp:226`) answers that line to any wire
event that is not an `:article` while the session awaits one, and the
open-to-closed transition makes `fn-served-step-counted-core` append the close
effect. So the host already had a reply and a close to carry out; it faulted
before sending either.

### The change

`host/native/owner.lisp`, `fnn-owner-serve-client`:

- a `retained` binding on the function's `let`: the part of the last socket read
  the served machine has not consumed;
- the read is `(or retained (fnn-owner-connection-call service :receive ...))`,
  so the socket is read **only** when nothing is retained and no octet is ever
  taken from the socket twice;
- the plaintext arm sets `retained` to `(subseq incoming consumed)` instead of
  faulting. In the oversize case `closing` is true, so the 441 goes out, the
  connection closes gracefully and the suffix goes with it;
- a fault stays where an invariant really is broken: `consumed` of zero with a
  non-empty chunk, no close and no STARTTLS means feeding the same octets again
  cannot make progress. That is `owner consumed no octets and left the
  connection open`.

The buffer is bounded by construction: `fnn-recv` reads at most `+fnn-max-read+`
= 512 octets (`host/native/io.lisp:1859`) and nothing is read while `retained`
is non-empty, so `retained` is at most 511 octets and cannot grow while a client
keeps sending.

## 2. Every article of a run carried one Date, and DATE answered one value

### Reproduced

Three `DATE` commands on three connections, four seconds apart:

```
10:02:29  111 20260922140006
10:02:33  111 20260922140006
10:02:37  111 20260922140006
```

Two articles posted at 14:03:05 and 14:03:11 and read back:

```
Injection-Date: Tue, 22 Sep 2026 14:00:06 +0000 / Date: ... 14:00:06 +0000
Injection-Date: Tue, 22 Sep 2026 14:00:06 +0000 / Date: ... 14:00:06 +0000
```

14:00:06 is when the process started.

### The cause

`host/native/owner.lisp` called `fn-owner-observe` exactly once, in
`fnn-owner-install` after the recovery barriers, and never again. Every
connection therefore pinned the startup reading as its reader environment and
every submission was injected under it.

This is not what the design says. `books/owner.lisp:655`, on `fn-own-open`:

> The injection clock is not pinned: `fn-own-read` supplies the owner's current
> observation with every read, so each submission is injected at its own time
> (RFC 5537 section 3.4).

and decision **D10-a** (`planning/decisions.md`, 2026-09-21) is written for a
host that supplies readings repeatedly: it gives `fn-own-observe` three
outcomes, and a `:refused` reading — a monotonic counter that went backwards, a
`has-wall` that changed, a widened error bound — costs the owner its clock,
after which it refuses to inject with its own line, refuses to declare a group
and answers DATE 503. None of that machinery can ever run against a host that
reads the clock once.

Nothing anchors the served clock to a freshness reading. `fnn-anchor-report`
(`host/native/io.lisp:1739`, "The freshness question") is the Roughtime anchor
and is read by `recover` only; it never reaches `fn-owner-observe`. D22 is about
the anchor's root and says nothing about the served clock. So there is no
reading of any decision under which a per-run constant Date is permitted.

`tools/run_owner.py`, the Python host this file replaced, already did it
correctly: `self.clock.observe(self.bridge)` at open (line 814, "One clock
observation per connection, pinned into it at open") and once per read before
the chunk (line 894, "one reading before the chunk that may carry an article, so
two posts on one connection get two identities"). The native host dropped both.

### The change

`host/native/owner.lisp` gains `fnn-owner-advance-clock`, which takes one
reading and hands it to `fn-owner-observe`. It is called at three points:

- once at startup, replacing the inline reading, still faulting unless the
  clock-less owner answers `:observed`;
- in `fnn-owner-serve-client`'s open thunk, before `fn-owner-open`, so the
  connection pins the reading it was accepted at — this is what makes DATE and
  NEWGROUPS answer per connection;
- in `fnn-owner-handle-chunk`, before `fn-owner-chunk`, so each submission is
  injected at its own time.

`:refused` is returned and not raised on: it is the model's answer under D10-a
and the owner has already dropped its clock. `:invalid` faults, because it means
this host supplied no observation at all.

The wall reading moved from `get-universal-time`, which has one-second
resolution, to `sb-ext:get-time-of-day`, so two submissions inside one second
are separated. One source, so the seconds and the sub-second part cannot come
from two different instants. The shift to the DTN epoch stays where the previous
line had it and where `tools/run_owner.py` has it; `fn-nntp-unix-dtn-ms`
(`books/nntp-responses.lisp:585`) is the model's twin of that shift and has no
host caller, which is an open item this lane did not widen.

**What still does not advance within a connection.** `fn-own-open` pins one
observation as the READER environment on purpose, "so that time does not move
under a reader mid-session" (D10-a). DATE therefore answers the time the
connection was accepted, for the life of that connection. The reproduction above
opened a connection per DATE, so it moves there; a client holding one connection
open for an hour still reads the accept time. That is the model's decision and
this lane did not change it. The per-run constant it was confused with is gone.

## 3. The listener's accept queue was 1

`ss -ltn` against the running node: `LISTEN 0 1`. `fnn-owner-run`
(`host/native/owner.lisp`) called `fnn-listen` without `:backlog`, taking the
default of 1 (`host/native/io.lisp:2041`), which carried no rationale. The
default suits `fnn-command-reader`, the one-client diagnostic reader; the owner
hands each accepted connection to a worker thread, so a client arriving while
the accept thread is doing that is dropped.

The owner now passes `+fnn-owner-listen-backlog+`, 16, the depth
`host/native/control.lisp:70` already uses, with the reason written at the
constant: this is the kernel's accept queue, not a connection limit — how many
connections the owner holds is `fn-own-open`'s `max-conns` and stays there.
`fnn-listen`'s docstring now says what its default is for.

## 4. A production image honoured a process-death cut from the environment

Not from the client exercise: the `w32/operator-verbs` lane found it while
gating its own `FN_NATIVE_CONTROL_FAULT`, and it is in the same file family.
Not reproduced against a node — that would mean standing up a production image
and stopping it on purpose, and the source says enough.

`fnn-control-test-after-submit` (`host/native/control.lisp:141`, before this change at 121) called itself
"Developer-only deterministic process-death cut after owner completion" in its
docstring and then read `FN_NATIVE_CONTROL_TEST_STOP` with no gate at all. The
cut is `SIGSTOP` to the node's own pid at the one moment that makes an outcome
unknowable: after the owner has completed the submission and before the reply
reaches the caller. In the image an operator deploys, anyone who could set the
environment of the node process could arm it.

The two neighbouring selectors are gated on the saved image's profile, which is
serialized at build time so a restart-time environment cannot change it
(`fnn-select-image-profile`, `host/native/io.lisp:2286`):

- `FN_NATIVE_POST_FAULT` — `fnn-post-test-fault` (`host/native/io.lisp:1667`):
  `(unless (fnn-developer-image-p) (fnn-fault "FN_NATIVE_POST_FAULT requires a
  developer image"))`;
- `FN_NATIVE_CONTROL_FAULT` — `fnn-owner-control-test-fault`, the same shape,
  on `w32/operator-verbs`.

`fnn-control-stop-cut-armed-p` is now that shape for this variable: a
production image faults on it, an unknown value faults, and `t` means the
developer cut is armed. `fnn-control-test-after-submit` asks the gate instead
of the environment, and every mention of the variable is inside the gate.

The fault is raised where the file already classifies one. The cut is called
after the `handler-case` that computes the reply status, on a control worker
thread where an escaping condition is nobody's exit code, so the call is
wrapped:

```
(handler-case (progn (fnn-control-test-after-submit status) status)
  (fnn-store-fault () :fault))
```

A production image handed the variable therefore answers ACL2's `:fault`
status, which `fn-native-control-status-class` projects to exit 4 at the
caller — the same way the caller learns `FN_NATIVE_CONTROL_FAULT`'s refusal.
The owner is not stopped: nothing about its state went wrong.

`tests/test_native_control.py`'s
`test_lost_reply_after_submission_is_uncertain_and_recovers` is the one test
that arms the cut. It ran the owner from `build/fn-host`, the production image,
which now refuses the variable, so it asks for `build/fn-host-developer` and
skips with that exact reason when it is absent — the shape
`tests/test_native_operator_verbs.py` uses for its uncertain-outcome witness.
`start_owner` takes an `image` argument for it; the store, the `operator post`
client and `inspect` stay on the production image.

Two always-active source checks land with it, in a new
`NativeControlCutGateTests`: the gate exists and names the developer image, and
the refusal reaches the caller as `:fault`.

## Tests

- `tests/native_owner_chunk_loop_raw.lisp` (new) reads the deployed
  `fnn-owner-serve-client`, `fnn-owner-handle-chunk` and
  `fnn-owner-advance-clock` out of `host/native/owner.lisp`, evaluates them
  against recording stubs, and checks four things: a prefix consume makes the
  suffix the next step's input and reads the socket no more times than there
  were chunks; an oversize step sends its 441 and closes gracefully with the
  process alive; a zero-consume step that neither closes nor hands over faults;
  and the owner is handed one reading at open and one per chunk, each a fresh
  reading in the model's units.

  Teeth, checked by patching the source and re-running: against the pre-fix
  suffix handling it fails with `the suffix was not the next step's input:
  ("AAA" "BBBBB")`, and with the per-chunk reading removed it fails with `the
  owner was handed 1 clock readings for an open and two chunks`.

- `tests/test_native_owner.py` runs that script (skipping when `sbcl` is not on
  PATH), asserts the listener passes the named backlog, and adds two
  image-driven cases to `NativeOwnerTests`, which skips as a class when no
  developer image is present: a 40 KiB article answered
  `441 posting failed; the article was not received` with the owner still
  serving a later connection and nothing durable, and DATE advancing across
  connections 1.2 s apart with two articles carrying different `Injection-Date`.

## What is not shown

- **No image was built and no image ran this code.** The 915 image is 210
  commits behind and cannot carry the fix; the closure of `dev` was being
  certified elsewhere while this lane ran. The two image-driven tests have never
  executed. Everything claimed about the composed node rests on the raw-Lisp
  test of the shipped functions plus the ACL2 reading above, not on a node.
- The oversize test asserts the exact 441 line because that line was read out of
  the certified book for a connection opened the way `fn-served-open` opens one,
  with an empty archive and no credential. A node with a different auth
  configuration was not exercised.
- Nothing here is a certification record. No book changed, so no book was
  certified; `python3 tools/green_check.py --changed-since dev --strict` reports
  no changed book.
- The backlog change is structural. No test opens sixteen simultaneous
  connections, and the old value was never observed to drop a client — only to
  be a queue of one with no reason recorded.
- Neither the TLS-channel arm nor the TLS-context plaintext arm changed, and
  neither was exercised against a node: the 915 image has no STARTTLS.
- **The cut gate has run in no image either.** A production image was not built
  and not handed `FN_NATIVE_CONTROL_TEST_STOP`, so exit 4 on that variable is
  the classification this file gives it, read from the source, and not a
  witnessed exit code. The developer path is equally unwitnessed: the one test
  that arms the cut now skips for want of `build/fn-host-developer`, so it went
  from running against the wrong image to not running at all until an image
  pair exists.
- Clock refusal (D10-a's `:refused`) is now reachable for the first time, since
  a host that reads the clock once can never contradict itself. No test steps a
  wall clock backwards under a running owner.
