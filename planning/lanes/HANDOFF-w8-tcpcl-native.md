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

See [`planning/evidence/tcpcl-EVREV-EVDATE.md`](../evidence/tcpcl-EVREV-EVDATE.md).

## Open

- **The served path revalidates the whole session per chunk (D3).**
  `fn-tcl-drive`'s guard is `fn-tcl-sessionp`, and `fn-tcl-inboundp` inside it
  runs `fn-tcl-octet-listsp` and `fn-tcl-lists-len` over every octet staged so
  far. A transfer of n octets therefore costs O(n²/chunk) in guard checking
  alone, measured below. This is the books' decision, not the host's: the fix
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
  worktree whose own closure was certified there is what produced the
  evidence below.
