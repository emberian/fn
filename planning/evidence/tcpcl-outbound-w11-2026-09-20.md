# Evidence: w11/tcpcl-outbound — the send-side served-path guard (D20)

Branch `w11/tcpcl-outbound` from `dev` at `38460cf`; worktree
`build/lanes/w11-tcpcl-outbound`, mirrored on hbox at
`/tank/fn/lanes/w11-tcpcl-outbound`. Every ACL2 run below is on **hbox**,
under `swarm-build`, with ACL2 8.7 at `/tank/fn/acl2-8.7/saved_acl2`
(sha256 `64030dda0b03bbb6…`, banner `ACL2 Version 8.7`), **no prover step
limit**, `FN_ACL2_TIMEOUT_SECONDS=1800`, `--jobs 4`, `FN_CERT_CACHE=
/tank/fn/certcache`. The box was measured before use, by `AnonPages` and the
RSS sum rather than by `free` (hbox is a ZFS box and `available`
under-reports): load 0.18, `AnonPages` 0.77 G, `MemFree` 27.9 G, no other
lane's ACL2 resident.

Everything here measures the **outbound** half. The receive half is
`planning/evidence/tcpcl-theory-w11-2026-09-20.md` and its numbers are not
restated.

## 1. Certification, with a control taken the same night on the same box

Four roots, `--closure`, one run each. The control is the same command on the
same box at the same `--jobs`, in a copy of this tree
(`/tank/fn/lanes/w11-tcpcl-outbound-base`) with `books/tcpcl-octets.lisp`,
`books/tcpcl-session.lisp` and `tests/acl2/tcpcl-tests.lisp` replaced by
`dev`'s bytes and their four certificates removed. It exists because this
lane is the first to change `books/tcpcl-octets`, and no hbox figure for that
book existed to compare against.

| root | dev bytes (control) | +D20 |
| --- | --- | --- |
| `books/tcpcl-octets` | 101.258 s | **101.740 s** |
| `books/tcpcl-session` | 64.842 s | **62.542 s** |
| `books/tcpcl-invariants` | 7.862 s | **6.974 s** |
| `tests/acl2/tcpcl-tests` | 0.352 s | **0.323 s** |
| wall, eight books at `--jobs 4` | 174.689 s | **172.038 s** |

Both runs: `status passed`, `book_failures {}`, zero `ACL2 Error` in every
log, all eight books `passed`. Lane run
`build/acl2/certify-20260921T004345Z-1351598` (fetched into this worktree),
farm run `run-20260921T004339Z-301c`, exit code 0; control run
`/tank/fn/lanes/w11-tcpcl-outbound-base/build/acl2/certify-20260921T004818Z-1354736`,
`--no-publish` so it seeded nothing.

Reading: making `fn-tcl-take` and `fn-tcl-drop` guard-total costs
`books/tcpcl-octets` **nothing** (+0.48 s on 101 s, inside this box's noise),
and the cheap outbound recognizer costs `books/tcpcl-session` nothing either
(−2.30 s). The previous lane's figures for the three roots it owned — 62.76 /
7.25 / 0.46 s, `certify-20260921T000317Z-1324995` — agree with this control
to within the same noise.

## 2. The guard, measured directly

This is the number to quote. Both recognizers were asked the same question
about the same session record, `books/tcpcl-session` certified, guard
checking on, under `time$`, **200,000 calls at every size** so that no cell
of the table rests on a 0.01 s reading. Driver, `ld`ed from the tree's
`books/` directory under `swarm-build` with `ACL2_CUSTOMIZATION=NONE
ACL2_BOOK_HASH_ALISTP=NIL` and a 900 s wall-clock `timeout`; no step limit,
nothing here is a proof.

```lisp
(include-book "tcpcl-session")
(defun fn-x-octets (n acc) (if (zp n) acc (fn-x-octets (- n 1) (cons 1 acc))))
(defconst *x-p* (fn-tcl-make-params 30 4096 10000000 '(100 116 110) nil nil))
(defconst *x-m* (fn-tcl-make-sess-init 30 4096 10000000 '(100 116 110) nil))
(defconst *x-n* (fn-tcl-negotiate *x-p* nil *x-m*))
(defun fn-x-out (n) (fn-tcl-make-outbound 0 :ref (fn-x-octets n nil) n 0 0))
(defun fn-x-sess (o)
  (fn-tcl-make-session :active :established *x-p* nil *x-m* *x-n* nil o 1 0 0 nil))
(defconst *x-s20000* (fn-x-sess (fn-x-out 20000)))   ; and *x-s1*, *x-s1000*
(assert-event (fn-tcl-sessionp *x-s20000*))          ; all three, both recognizers
(assert-event (fn-tcl-session-cheapp *x-s20000*))
(defun fn-x-rep-spec  (s n) (if (zp n) 0 (+ (if (fn-tcl-sessionp s) 1 0)       (fn-x-rep-spec  s (- n 1)))))
(defun fn-x-rep-cheap (s n) (if (zp n) 0 (+ (if (fn-tcl-session-cheapp s) 1 0) (fn-x-rep-cheap s (- n 1)))))
(time$ (fn-x-rep-spec *x-s20000* 200000))            ; etc
```

The `assert-event`s are what make the timings mean anything: **seven of
seven `:PASSED`** in each tree, so both recognizers return T on all three
sessions, each traverses to completion, and neither is timed on an early
exit. Zero `ACL2 Error` in both logs
(`build/probe/probe-lane.log`, `build/probe/probe-base.log`).

| unsent octets | `fn-tcl-sessionp` | `fn-tcl-session-cheapp` **before** D20 | `fn-tcl-session-cheapp` **after** D20 |
| --- | --- | --- | --- |
| 1 | 0.16 s / 200,000 = 0.80 µs | 0.15 s / 200,000 = 0.75 µs | 0.15 s / 200,000 = **0.75 µs** |
| 1,000 | 0.76 s / 200,000 = 3.80 µs | 0.78 s / 200,000 = 3.90 µs | 0.15 s / 200,000 = **0.75 µs** |
| 20,000 | 12.40 s / 200,000 = 62.0 µs | 12.57 s / 200,000 = 62.85 µs | 0.15 s / 200,000 = **0.75 µs** |

The `before` column is the same driver in the control tree; the
`fn-tcl-sessionp` column there reads 0.80 / 3.65 / 62.9 µs, which is the
third column of that run and the same function.

Three things the table says. **(i) The old cheap guard was not cheap on a
send.** Before D20 it cost 62.85 µs against the specification recognizer's
62.9 µs at 20,000 unsent octets: indistinguishable, because
`fn-tcl-outboundp` sat inside `fn-tcl-session-cheapp` verbatim and both
recognizers walked the suffix the same two times. **(ii) It was linear in the
unsent data.** Subtracting the ~0.7 µs the session's own fields cost, 1,000
octets is 3.1 µs and 20,000 is 61.3 µs: 20× the octets for 19.8× the cost.
Since the host pays it once per socket chunk and the chunk count grows with
the transfer, that per-chunk linear cost is exactly the O(n²/chunk) of
`specs/tcpcl.md` §6. **(iii) After D20 it does not move at all**, to three
significant figures, across four orders of magnitude of unsent data —
**83× cheaper** than the specification recognizer at 20,000 octets, and 84×
cheaper than what the same guard cost the day before.

The unit is one octet of unsent data. The receive-side table counts staged
*segments*, so its 360× and this 83× are not the same ratio and should not be
compared.

Limitation, the same one that record states: this times the recognizers, not
a transfer. It is the mechanism `specs/tcpcl.md` §3 names — the executable
counterpart checks the callee's guard once per socket chunk — and it is not
an end-to-end throughput claim.

## 3. `tools/tcpcl_lab.py --scenario profile`: NOT RUN, and why

The lab's `profile` scenario times a send, so with the send guard fixed it
would for the first time be a gate on the thing this packet changed. It needs
a native image, and a native image needs the DTN closure certified on the
box: `host/native/build-dtn.lisp` includes `books/bp-node`, and
`tools/certify_books.py --dry-run --closure` over its fifteen includes is
**60 books**.

**`books/bp-node` does not certify on `dev`**, so no native image exists to
run the lab against — for this lane or any other. `w10/dtn-3` landed on dev
at `dbf1aa7` and says so on the board: the book is open at exactly one guard
conjecture, `fn-bpp-fragmentp`'s guard on the primary's flags, because
`books/bp-primary` ships its accessors with their `:definition` runes
enabled, and "because `books/bp-node` is open the DTN image was not built".
It is the only root between that tree and `tools/build_native_host.sh`, and
it belongs to the BP cluster. `books/bp-bundle-invariants`, which was the
blocker when `w11/tcpcl-theory` looked at this last night, now certifies on
dev — with two forms removed and recorded open — so the blocker has moved one
book down, not away.

This lane confirmed the shape of the gap rather than taking the BP cluster's
work: after publishing `/tank/fn/lanes/w10-dtn-3`'s pairs into hbox's cache
(850 → 859 entries) and installing them, this tree holds certificates for 42
of the 60, and the missing ones are all BP- and store-side books this packet
does not touch.

So the gate is **not run**, not "passed" and not "failed". Nothing in §1 or
§2 depends on it: the direct measurement is of the certified book itself. The
claim it would settle is end-to-end send throughput on this exact tree, which
no number in this record asserts. It becomes a one-command run the moment
`books/bp-node` certifies, and the previous lane's caveat still applies to
its *ratio* when it does — that scenario times two process starts of a 262 MB
image and reported 1.84 one day and 0.53 the next, so only its pass/fail
verdict and its `intact` flags carry weight, never the number.

## 4. What ran, what it cost, what is not claimed

- `make check`: exit 0 before each commit.
- `tools/ledger.py --write`: `defthm` 5558 → 5560, `defun` 3929 → 3930,
  functions left at the default with an explicit guard 1790 → 1791,
  `assert-event` checks 5398 → 5420.
- No `skip-proofs`, no `defaxiom`, no trust tag, no `:rule-classes nil`
  added to any keystone. C1 to C4 are byte-identical; `git diff` over
  `books/tcpcl-invariants.lisp` is **empty**.
- Not claimed: any interoperability, server or flight property; any
  end-to-end throughput figure; anything about the receive path that the
  previous lane's record does not already say.
