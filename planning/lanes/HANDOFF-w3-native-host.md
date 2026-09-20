# Handoff: w3/native-host — the ACL2 image that replaces the Python bridge

Branch `w3/native-host`, merged with `dev` at `c8886ee` (merge `e7f350b`).

## What is here

- [`host/native/io.lisp`](../../host/native/io.lisp): the whole raw-Lisp
  surface of the native host — POSIX files and barriers, `flock`, SHA-256
  (A-CRYPTO), the two host-owned metadata JSON files, the sockets, and
  `fnn-call`, the raw-Lisp spelling of `ec-call` into the `:program` wrappers
  in `host/*-host.lisp`. No book function is called by its raw symbol.
- [`host/native/build.lisp`](../../host/native/build.lisp) +
  [`tools/build_native_host.sh`](../../tools/build_native_host.sh): the image
  build. Every `include-book` is a Makefile certification root; the one trust
  tag (`:fn-native-host`) is retired before `save-exec`.
- [`host/native/reader-model-host.lisp`](../../host/native/reader-model-host.lisp):
  the model side of the served differential — the one expression
  `tests/test_served_differential.py` types at the ACL2 prompt, as a wrapper,
  because the image has no prompt.
- [`tools/fn_native.py`](../../tools/fn_native.py): the launcher.
  `FN_HOST=native` makes `tools/run_store.py` and `tools/run_reader.py`
  delegate to the image after parsing, so the same tests drive either host.
- [`tests/test_native_served_differential.py`](../../tests/test_native_served_differential.py)
  and [`tests/native_differential.py`](../../tests/native_differential.py):
  socket-against-`fn-served-run`, and native-against-Python.
- [`specs/host.md`](../../specs/host.md) "The native host": the trust-boundary
  table, the served reader path, the store's configuration history.

## What this rebase changed (the realignment)

- **One `fn-served-step` per socket read.** `fnn-reader-chunk` returns
  `(values reply closing)`; the unconsumed-suffix value and the re-feed loop
  in `fnn-serve-client` are gone. `fn-wire-drive` has one owner and it is
  `books/served.lisp`; article mode is wire state inside the five-field
  connection, so a POST and its article are the same one call per read.
- **Posting and the clock are pinned at open**, through
  `fn-reader-set-posting` before selection and `fn-served-open` inside
  `fn-reader-reset`; no served step reads a global.
- **A submission is an outcome, not a reply.** The reader holds a shared
  lock, so a submitted article is completed `:refused` through
  `fn-reader-outcome` and ACL2 writes the 240 or the 441. Uncertain, refused
  and accepted stay distinct out to the exit code.
- **The store opens on the replayed configuration.** `fnn-bridge-recover`
  passes the `config/*.cfg` history as its third argument; a store with no
  durable configuration record is refused; `fn-store-group-codes` resolves
  names against the domain the core hands back. `fn-store-group-table-id` and
  the `group_table` configuration key are gone (format
  `fn-store-experiment-5`), and `init` passes `--group` names to
  `fn-cfg-host-initial-octets`.
- **The socket surface is named**, factored out of the reader command and
  documented at the top of `io.lisp`: `fnn-listen`, `fnn-connect`,
  `fnn-accept-loop`, `fnn-socket-fd`, `fnn-socket-shut`, over `fnn-recv`,
  `fnn-send-all`, `fnn-graceful-close`. `host/native/tcpcl.lisp` (the DTN
  wave, [HANDOFF-w4-tcpcl.md](HANDOFF-w4-tcpcl.md) "Proposed host surface")
  builds on exactly these and opens no socket of its own. Posted to the board.

## Protocol behind `--fn`

```
store ROOT init [GROUP...] | recover | status | config
store ROOT post MESSAGE-ID PAYLOAD CHARGE|- FAULT|- GROUP...
store ROOT inspect MESSAGE-ID
store ROOT probe COUNT
reader PORT ONCE(0|1) STORE-ROOT|-
model CHUNK-FILE STORE-ROOT|-        # the differential's model side
sha256 PATH
```

`model`'s chunk file is length-prefixed (a decimal count, LF, that many
octets, repeated) so a chunk may hold any octet, including LF and half of a
UTF-8 sequence; it is parsed digit by digit and never reaches the Lisp reader.

## Evidence (persvati, 2026-09-20)

The image is built and the differential runs, on the farm box, because the
laptop's four ACL2 slots were held all night (a queued build waited 1604 s and
still produced nothing).

| What | Command | Result |
| --- | --- | --- |
| Image | `rsync -a --exclude build/ <worktree>/ persvati:/home/ember/fn-lanes/w3-native-host/`, certificates from `~/fn-gates/dev-bdd59d2/books/` (local rsync of `*.cert`/`*.port`, 139 books; only the four `tcpcl` books differ between that gate and this base and none is in the closure), then `FN_ACL2=$HOME/fn-tools/acl2-8.7/saved_acl2 nice -n 10 sh tools/build_native_host.sh` | `built build/fn-host (250M core)`, 8.5 s wall, 7.8 s user, 1.5 GiB peak RSS |
| Served differential | `python3 -m unittest tests.test_native_served_differential -v` | 7 tests, **OK**, 0.38 s — whole transcript, three cut points, the bytewise partition of a 3-command transcript, a cut inside a UTF-8 sequence, input after QUIT, a framing rejection |
| SHA-256 | `./build/fn-host --fn sha256 /etc/hostname` | equals `sha256sum` |
| Store path | `init`, `post`, `recover`, `inspect`, `config` on a fresh store | `committed sequence=0 charge=2`; `recovered transactions=1 articles=1`; `inspect` returns the payload; `generation=1 served=fn.letters,fn.test domain=fn.letters,fn.test` |

Two defects the image found, both fixed here and neither visible to any
static check:

- **The SBCL banner was on stdout.** `save-exec`'s `:toplevel-args` are Lisp
  options and `--noinform` is a runtime option; it now goes in
  `:host-lisp-args`. The `model` verb writes reply octets to stdout, so a
  banner made all seven differential tests fail.
- **The record metadata fields take identity TEXT, not canonical identity
  octets** (`fn-store-identity-text`), and the subject preimage is the v1
  head from `fn-store-subject-prefix` followed by the payload, not the bare
  payload. The native host was passing v0 canonical octets, which are not
  `fn-store-text-octetsp`, so every `post` was `:invalid` while the Python
  host committed on the same store.

## Open

- **No owner in the reader.** A served POST is refused because this process
  holds a shared lock. The mutable-owner lane (`host/owner-host.lisp`,
  `fn-own-*`) is where a native writer belongs; when it lands, replace the
  `:refused` constant in `fnn-serve-client` with its completion.
- **One profile only.** `fnn-load-config` accepts exactly the default
  configuration bytes; `tools/run_store.py` also accepts the named scale
  profile (`SUPPORTED_PROFILES`). A scale store therefore opens under the
  Python host and is refused by the image. Pre-existing, and the differential
  will not show it because it initializes default stores.
- **Two JSON implementations.** `config.json` and `allocation-frontier.json`
  are a host decision with a Python implementation and a Lisp one. The
  differential run is what keeps them equal; a core-owned metadata record
  would remove the twin.
- **Not ported:** the BP hosts, the in-process classes the fault-matrix and
  partition tests patch, and the `ReaderBridgeFault` path's Python analogue.
