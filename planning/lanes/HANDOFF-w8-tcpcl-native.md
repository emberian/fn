# Handoff: w8/tcpcl-native — TCPCLv4 in the native host

Branch `w8/tcpcl-native`, worktree `build/lanes/w8-tcpcl-native`, from `8c7f33b`
(dev, after the `w6/tcpcl-c2` merge). Spec: [specs/tcpcl.md](../../specs/tcpcl.md).
Books: `books/tcpcl-{records,octets,session}` (certified); `books/tcpcl-invariants`
is another lane's and nothing here depends on it.

## What landed

- **[`host/tcpcl-host.lisp`](../../host/tcpcl-host.lisp)** — the ACL2 side.
  Sixteen `:logic` wrappers over `books/tcpcl-session`, each returning a flat
  `(session events unconsumed)` triple so the raw host applies no record
  accessor. Every protocol value the layer needs comes out of one of them:
  `fn-tcl-host-encode` (octets), `-kind`, `-keepalive`, `-transfer-mtu`,
  `-phase`, and `fn-tcl-host-event-digests`, which is what a session log line
  carries — the bulk octets of a message or a bundle replaced by their `len`,
  computed in ACL2 like every other length here. `fn-tcl-host-terminate`
  carries `*fn-tcl-term-unknown*`; the host never writes a reason code.
  `fn-tcl-host-replay` folds `fn-tcl-drive` over a trace for the differential.
- **[`host/native/tcpcl.lisp`](../../host/native/tcpcl.lisp)** — the loop.
  `fnn-tcl-listen`, `fnn-tcl-connect` and `fnn-tcl-session` over io.lisp's
  eight named socket entry points and nothing else; the file opens no socket
  and makes no syscall of its own beyond the durability barrier. One
  `fn-tcl-drive` per `fnn-recv` chunk with the carry prepended, one
  `fn-tcl-tick` per wakeup with one monotonic millisecond reading,
  `fn-tcl-send` + `fn-tcl-pump` for an offered bundle, `fn-tcl-tcp-closed` on
  a peer close.
- **The image** gains `books/tcpcl-session`, `host/tcpcl-host.lisp`,
  `host/native/tcpcl.lisp` — and `host/anchor-host.lisp`, the w3 gap: `recover`
  now prints `anchor=none` for a store that never recorded one and
  `anchor=uncertain [...]` with exit 3 for one that did, because this image has
  no pinned Roughtime client and a possibly stale store must not read as fresh.
- **[`tools/tcpcl_lab.py`](../../tools/tcpcl_lab.py)** — five scenarios against
  a built image, and the `tcpcl` scenario in
  [`tools/twonode_gate.py`](../../tools/twonode_gate.py) that runs them.

## The one ordering rule the host adds

`fn-tcl-complete` emits the XFER_ACK **before** the `:bundle-received` whose
data that ack promises. Acting on the list in order would put the ack on the
wire before the bundle was durable. So `fnn-tcl-act` buffers every outbound
octet for the length of one event list and releases the buffer at two points:
immediately after a `:bundle-received` has been staged and barriered, and at
the end of the list. The machine's order is preserved exactly; only the moment
of release is the host's. A barrier that does not complete is `uncertain`: the
buffer is dropped, the ack is never written, the session ends, exit 3.

## Evidence

[`planning/evidence/tcpcl-9cbf301-2026-09-20.md`](../evidence/tcpcl-9cbf301-2026-09-20.md),
and its headline is a negative one: **the image did not build, so none of the
five scenarios ran.** 60 of the image's 63-book closure certified in the lane's
own directory on persvati (`run-20260920T051453Z-c9a2`, `--jobs 12 --closure`),
including all three tcpcl books and `anchor-invariants`; `books/served`,
`books/nntp-post` and `books/nntp-effects` — the NNTP reader's, not this
layer's — each exceeded the runner's 1800 s cap on a box carrying five other
lanes and were still retrying when the lane ended.

**The trap that cost the most, written down so the next lane does not pay it
again: an ACL2 certificate records absolute full-book-names, so certificates
are not relocatable and must never be mixed across directories.** Installing
217 certificates scavenged from every gate and lane whose book *text* matched
made ACL2 include each book from the directory its own certificate named, and
the build refused with `its certificate requires
/home/ember/fn-gates/dev-056b29b/books/acceptance.lisp, but ...
dev-498b766/books/acceptance.lisp ... has been included`. No existing
directory holds this image's whole closure (the best gate matches 57 of 63 and
has no tcpcl book; the two directories with a matching `tcpcl-session.cert`
match 5 of 63), so the image needs its own closure certified in its own
directory. When the three books land, one command finishes the lane:

```sh
ssh persvati 'cd /home/ember/fn-lanes/w8-tcpcl-native \
  && FN_ACL2=$HOME/fn-tools/acl2-8.7/saved_acl2 nice -n 10 sh tools/build_native_host.sh \
  && python3 tools/tcpcl_lab.py --image build/fn-host --work /tmp/tcpcl-lab'
```

**Checked again 2026-09-20 by w6/tcpcl-tests, and the dependency still holds.**
`python3 tools/certs.py install` in `/home/ember/fn-lanes/w8-tcpcl-native`
brought that tree to exactly **60 book certificates** and left
`books/served`, `books/nntp-post` and `books/nntp-effects` uncached: the box's
cache holds no pair for any of the three at that tree's source text. The build
list cannot route around them — `host/native/build.lisp` names `books/served`
and `books/nntp-effects` in its own `include-book` list (lines 23 and 24) and
`books/nntp-post` arrives under `served` — so the image is blocked on those
three roots certifying *in that directory*, not on anything in this layer.
`books/nntp-effects` is `w6/nntp-effects`'s open work on dev; `books/served`
and `books/nntp-post` exceeded the runner's 1800 s cap here and want a quiet
box and a raised `FN_ACL2_TIMEOUT_SECONDS`. Until then `tools/tcpcl_lab.py`
has no image to run and the five scenarios stay unrun.

What did run: the raw file compiles clean against stubs for io.lisp's surface
(35 forms, no caught warning), `host/tcpcl-host.lisp` reads as ACL2 (22
forms), `make check` is green, and `tests/test_twonode_gate.py` passes 19/19
with the new `tcpcl` scenario in place — it skips with the build's last lines
and keeps the gate green when no image is produced.

## Open

- **The served path revalidates the whole session per chunk (D3).**
  `fn-tcl-drive`'s guard is `fn-tcl-sessionp`, and `fn-tcl-inboundp` inside it
  runs `fn-tcl-octet-listsp` and `fn-tcl-lists-len` over every octet staged so
  far. A transfer of n octets therefore costs O(n²/chunk) in guard checking
  alone. This is the books' decision, not the host's: the fix
  is the one `books/served.lisp` already made for the wire — carry the
  invariant in the state and prove it preserved, so the recognizer never runs
  per chunk. Until then the layer is not usable for large bundles.
- **No BP node behind it.** `:bundle-received` is staged as a file in a spool
  directory; `fn-bpn-receive` does not exist on this tree, and nothing parses
  the transferred octets as BPv7. The FNBS barrier here is the file's data and
  name, not a receipt. Wiring the receiver (`host/bp-receive-host.lisp`,
  `books/bp-receipt`) to the spool is the next packet.
- **No scheduler.** `:session-up` tells nobody; `books/scheduler.lisp` contacts
  are not opened or closed by this layer.
- **One transfer in flight per direction**, because the machine has one
  inbound and one outbound; `:send-refused :busy` is retried on the next
  wakeup and nothing queues.
- **No TLS**, per the clause matrix; `can-tls` is passed as `nil`.
- **dtn7 interop not attempted**: neither persvati nor hbox holds a dtn7-rs
  checkout, and the layer carries opaque octets rather than BPv7 bundles, so
  a dtn7 peer would complete the session and then reject the transfer's
  content. The exact command that would run it is in the evidence record.
- **The gate scenario skips where certificates are not the deploy tree's.**
  `tools/twonode_gate.py` installs certificates from a neighbour gate
  directory, and an ACL2 certificate records absolute full-book-names, so the
  strict image build inside `$HOME/fn-deploy/<rev>` refuses books whose
  certificates name another directory. The scenario reports that as a skip
  with the build's last lines rather than as a pass. Running the lab in a
  worktree whose own closure was certified there is the way to run it.
