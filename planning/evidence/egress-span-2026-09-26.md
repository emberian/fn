# egress-span: the served reply as a range of the octet buffer (PRF-192; PKT-555, PKT-491, ledger row 6)

Lane egress-span (Opus 5.5), the performance ledger's fix lane 4, from dev
`6407de33`, branch `lane/egress-span`. Brief:
`build/coordinator/queue/done/w4-egress-span.txt`. Ids: PRF-192, SCN-121,
PKT-550 (what remains). No decision packet arose (PKT-551 unused). Files
under `planning/evidence/egress-span-2026-09-26/`.

## 1. PKT-555 first: where ARTICLE 3 MiB's wall goes

**The 4 s is the client, not fn.** The ledger's harness reads through
`tools/msgid_measure.Conn`, a `makefile("rwb", buffering=0)` socket file:
CPython's `SocketIO` has no `peek`, so `readline` issues one `recv(1)` per
octet, and `rep_measure.read_multiline` reads a 3 MiB reply one octet per
syscall.

`egress.py` (this lane) serves the same store to three clients on their own
connections: the harness reader; a 1 MiB-buffered socket file with
`readline`; a raw `recv(1 MiB)` loop. For each ARTICLE it records wall, the
owner's CPU (`/proc/PID/stat`), the client's CPU, the owner's write
syscalls (`/proc/PID/io` syscw), bytes consed (the perf-ledger heap hook),
and the serving thread ("fn owner client") sampled every 1 ms from
`/proc/PID/task/TID/{stat,syscall}` (the script is the owner's ancestor, so
yama ptrace_scope 1 permits it). Run `pre-f314.json`: the ledger's own
profiling image (core `90544f4c…`, dev `f314a5a3`), hbox, tmpfs, load 9.8
to 10.2, 15:47Z:

| ARTICLE 3 MiB, 3 each | wall median | owner CPU | client CPU | serving thread (1 ms samples) | owner writes |
| --- | ---: | ---: | ---: | --- | ---: |
| harness (recv(1) per octet) | 5,914 ms | 820 ms | 5,472 ms | poll 13,060, running 2,142 | 2 |
| buffered readline | 842 ms | 890 ms | 53 ms | running 2,391, poll 8 | 1 |
| raw recv(1 MiB) | 801 ms | 790 ms | 46 ms | running 2,136, poll 4 | 1 |

32 KiB: harness 62.6 ms, raw 4.0 ms. With a chunked reader the wall IS the
owner's CPU; the owner writes the whole reply in one `write` (the kernel
takes it; no pacing, no sleep in the writer: `fnn-send-all`,
host/native/io.lisp, called from `fnn-owner-send` after
`fnn-owner-handle-chunk` returns). The `clock_nanosleep` and `fstatat` in
the ledger's owner profile are the heap hook's and the profiler's helper
threads (`FNH-THREAD`, `FNP-THREAD`: `probe-file` every 20 and 50 ms), not
the owner. **Row 6's target is therefore owner CPU and bytes consed**, and
the ledger's ARTICLE wall figures are the harness's. A second harness
defect, found on the way: `rep_measure.post` writes the article with one
unbuffered `stream.write`, which may send a 3 MiB article partially and
then wait for a reply forever (hit twice here; `egress.py` uses
`sendall`). Classification: harness, both.

## 2. The change

- **books/served-reply-buffer.lisp** (new): `fn-served-reply-to-buffer
  (effects fn-octets) -> (mv okp fn-octets)`, guard `t`, guard-verified:
  clears `fn-octets` and appends each `(:reply octets)` effect's octets
  with ONE `fn-octets-append-list` export call per effect (one array write
  per octet, no cons); OKP is `fn-srb-effects-octetsp` (every reply effect
  is an octet list), the check the host made on the list before
  (`fnn-owner-octets-global`), now ACL2's.
- **host/owner-host.lisp**: `fn-owner-chunk` installs through
  `fn-owner-install-served-effects`: every projection
  `fn-owner-install-effects` makes except the reply list (`fn-owner-output`
  is NIL); `fn-owner-install-effects` (every other entry) is that plus the
  list, unchanged in value. New `fn-owner-reply-buffer (fn-octets state)`
  calls the subject on `fn-owner-effects`: `:ok` or `:malformed`.
- **host/native/owner.lisp** `fnn-owner-handle-chunk`: the reply is
  `fnn-owner-reply-from-buffer`: `fnn-owner-buffer-action
  'fn-owner-reply-buffer`, fault unless `:ok`, then ONE `subseq` of the live
  array's cells [0, fill) under the service mutex. The rest of the function
  (drain, redeem, exposure close appended) is unchanged.
- **Which buffer and why.** `fn-octets`, the served thread's buffer: only
  the service mutex's holder touches it (`fnn-owner-attempt`'s
  `fnn-octets-fill`, the buffer twins; io.lisp's note "one buffer, one owner
  thread"). Not `fn-octets-pub`: that is the publication thread's, off the
  mutex (checkpoint-capture-stream's hazard note). The copy is required
  because the socket write runs after `fnn-owner-handle-chunk` returns,
  outside the mutex, while the next locked step (this connection's writer
  drain refills the buffer with the POST payload; another connection's
  read) overwrites it. Relative to ingress-span's seal point: the reply
  fill runs after `fn-owner-chunk` has consumed the read, so it never
  overwrites input still being read; a merge with ingress-span-2's
  `fn-owner-chunk-span` should install through
  `fn-owner-install-served-effects` too (the host reads the reply from the
  effects global, so it is correct either way; only the list would remain).
- **tools/run_owner.py** (the Python host): reads the reply as
  `(fn-served-reply-octets (@ fn-owner-effects))` after `fn-owner-chunk`.
- **tests/native_owner_chunk_loop_raw.lisp**: a stub for
  `fnn-owner-reply-from-buffer`. This raw test fails identically on dev and
  on this branch with the laptop's SBCL ("the suffix was not the next
  step's input"); not examined here (harness or environment).

## 3. Theorems (PRF-192)

Subject: `fn-served-reply-to-buffer`, called by host/owner-host.lisp
`fn-owner-reply-buffer`, called by host/native/owner.lisp
`fnn-owner-reply-from-buffer` in `fnn-owner-handle-chunk` for every served
read.

- `fn-served-reply-to-buffer-is-the-reply` (keystone): OKP equals
  `(fn-srb-effects-octetsp effects)`, and when OKP holds,
  `(fn-octets-len buf) = (len (fn-served-reply-octets effects))` and
  `(fn-oct-slice-list 0 (fn-octets-len buf) buf) = (fn-served-reply-octets
  effects)`: the range the host copies is the reply the served machine
  decided. The array cells are the stobj's logical value by PRF-087
  (`fn-octets$corr`); the host's copy of [0, fill) is the same trusted
  boundary as `fnn-octets-fill` (A-HOST, io.lisp).
- `fn-served-reply-to-buffer-refusal-keeps-the-buffer`: when OKP is false
  the buffer is unchanged.
- Unchanged, cited: the exposure's observation reads the effects
  (`fn-exp-observe-effects-is-the-observation-of-the-reply`, PRF-161), so
  no exposure decision moves. The served bytes do not change by the
  keystone.

Teeth (tests/acl2/served-reply-buffer-tests.lisp): a reachable witness (a
reply split over two effects with `(:close)` between them, over a buffer
holding a longer stale value, so the clear is exercised); the must-fail for
the one hypothesis OKP (a reply effect carrying 300: OKP is nil and the
range is not the reply); the refusal theorem's witness (the stale value
stays); a labelled MUTATION witness (the appends without the clear keep the
stale octets: must-fail); the served-size witness (a 3 MiB body behind the
status line: OKP, the length, and the buffer equal the reply, read back
with the tail-recursive `fn-octets-list` because `fn-oct-slice-list`, a
non-tail recursion, exhausts a REPL's control stack at 3 MiB; it is only
the test's reader).

Validation (batch rule): the book (16 forms) and every form of the test
book admitted in the persvati REPL (`~/fn-gates/egress-span-repl`, toolchain
w25): both functions `:common-lisp-compliant`, 7 `assert-event`s passed,
both must-fails held. hbox_native's certify step certified
`books/served-reply-buffer` (w28, `native-a6660cb8/logs/certify.log`). NOT
a farm manifest: the batch certifies the affected roots.

## 4. Native (hbox)

`tools/hbox_native.sh --images developer,production --label a6660cb8p
6660cb8b tests.test_native_bounds_join.LargeReplyTests`: OK (1 ran),
28.2 s: POST and ARTICLE of 1, 2 and 3 MiB, each served identical, a 4 MB
OVER, the owner serving and exiting 0 (log
`test_native_bounds_join.LargeReplyTests.6660cb8b.log`, sha256
`32f576e1…`; images production core `2620a392…`, developer core
`5a398fbe…`, `native-a6660cb8p.SHA256SUMS`). The same module on dev base
`6407de33` (label base6407, for the matched measurement's images): OK
(`…6407de33.log`, `f9a9bb0a…`). (A first run without the production image
SKIPPED the case: not counted.)

## 5. Before and after (matched)

Images: the profiling twins (perf-ledger's `setup.sh` recipe, `prof.sh`)
of dev `6407de33` (core `91136e95…`) and of this lane's `6660cb8b` (core
`814571a2…`), each built in its hbox_native tree. These two profiling
builds are beyond the batch rule's one module run; they were needed for
the brief's bytes-consed figures under matched conditions. Runs
interleaved base, lane, base, lane, 16:04 to 16:06Z, load 8.1 to 8.3, hbox
tmpfs, `run.sh`; files `base-6407-{1,2}.json`, `post-6660-{1,2}.json`.

| op (raw 1 MiB reader unless named) | base 6407de33 | lane 6660cb8b | change |
| --- | ---: | ---: | ---: |
| ARTICLE 3 MiB bytes consed | 574.6 MB (both runs) | 469.8 MB (both runs) | -104.8 MB, -18.2 % |
| ARTICLE 3 MiB, buffered reader, consed | 566.3 MB | 462.5 MB | -103.8 MB |
| ARTICLE 3 MiB wall median | 664, 691 ms | 519, 470 ms | about -25 % |
| ARTICLE 3 MiB owner CPU | 663, 733 ms | 507, 473 ms | about -30 % |
| ARTICLE 32 KiB bytes consed | 5.80 MB | 4.75 MB | -1.05 MB, -18 % |
| ARTICLE 32 KiB wall | 2.2, 2.3 ms | 2.2, 2.7 ms | within noise |
| POST 3 MiB (untouched) | 2,478, 2,644 ms | 2,581, 2,681 ms | unchanged |

Bytes consed are the robust figure (identical across runs); CPU is at the
10 ms tick and times are under load 8. The 105 MB is the reply list and its
`fn-ag-append` copy (two 16-octet conses per reply octet) and the host's
coerced vector: exactly what the lane removed. What remains is the ARTICLE
rendering itself (`fn-nntp-article-response`: `fn-nntp-crlf-lines-aux`,
`fn-nntp-stuff-lines`, `fn-nntp-article-framedp`, 67 percent of the
ledger's profile), which builds the effect's octets as lists: PKT-550.

## 6. Ledger row 6, PKT-491, PKT-555

- PKT-555: **retired** by section 1 (the wall is the harness's recv(1);
  the owner neither paces nor sleeps).
- PKT-491: **narrowed**. The host reply is no longer a list (this lane);
  the effect payloads still are (PKT-550). The per-effect recursion of
  `fn-served-reply-octets` is no longer executed on the served path.
- Row 6: ARTICLE 3 MiB is 0.5 to 0.7 s wall = owner CPU with a chunked
  reader (not 5.0 s), and 470 MB consed (from 575 MB).
- **PKT-550 (what remains)**: the ARTICLE's reply built as octet lists by
  the NNTP renderer (`fn-nntp-article-response` and its dot-stuffing and
  framing check over `fn-nntp-crlf-lines`), about 470 MB and 0.5 s per
  3 MiB; its fix is a reference effect (the article's payload rendered into
  the buffer by the writer, dot-stuffing in the fill), which waits on the
  held-record shape of PKT-293; and the two harness defects of section 1
  (`msgid_measure.Conn`'s recv(1) reader, `rep_measure.post`'s partial
  write), whose owners are the measurement tools.

## 7. Assurance chain

native entry `fnn-owner-handle-chunk` (host/native/owner.lisp) ->
`fn-owner-chunk` (effects installed, no list) -> `fnn-owner-reply-from-buffer`
-> `fn-owner-reply-buffer` -> executed ACL2 subject
`fn-served-reply-to-buffer` (guard-verified, writes `fn-octets`) ->
representation: the array's [0, fill) is the stobj's logical list
(PRF-087's `fn-octets$corr`; host copy at the A-HOST boundary) ->
refinement `fn-served-reply-to-buffer-is-the-reply` (the range is
`fn-served-reply-octets` of the effects) -> behavioural theorems about the
served step's reply, unchanged (the served machine and PRF-161's exposure
observation over the same effects) -> observed: section 4 (identical
ARTICLE bytes at 1, 2, 3 MiB) and section 5. No maintained relation is
introduced: the fill is a function of one step's effects, established per
call.
