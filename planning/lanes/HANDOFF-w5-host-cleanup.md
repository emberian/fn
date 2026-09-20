# Handoff: w5/host-cleanup

Branch `w5/host-cleanup` from dev `1c5b950`, worktree
`build/lanes/w5-host-cleanup`. Remote root for the ACL2 work:
`persvati:/home/ember/fn-lanes/w5-host-cleanup`, `FN_ACL2` =
`$HOME/fn-tools/acl2-8.7/saved_acl2`, certificates installed from
`/home/ember/fn-certcache` (116 book certificates, 46 test books uncached).

## What was wrong

A host file is never certified. A Python bridge `ld`s it at start-up and
`host/native/build.lisp` `load`s the raw pair; nothing else reads it. On dev,
`tools/ledger.py`'s `host_names` lint reported **81** names in ten host files
that no file the using file loads defines. They resolved only because a
*sibling* had already been loaded into the same session, so each bridge's
`ld` order was load-bearing, a host file could not be loaded alone, and a new
bridge that ordered the files differently would fail at start-up.

## What changed

Every host file now names what it uses. No definition was copied and none
moved: a second `ld` of a file already in the session re-admits identical
definitions, which ACL2 accepts as redundant.

| file | added | for |
| --- | --- | --- |
| `host/store-node-host.lisp` | `(ld "store-host.lisp")` | the decimal-octet helpers, `*fn-store-capacity*`, `books/store-config` under it |
| `host/config-host.lisp` | `(ld "store-host.lisp")` | `fn-store-octet-lists->strings` |
| `host/checkpoint-host.lisp` | `(ld "store-node-host.lisp")` | `fn-store-sn-domain`, `fn-store-decode-records`, `*fn-store-capacity*` |
| `host/bp-ingress-host.lisp` | `(ld "store-node-host.lisp")` | `fn-store-sn-reset`, `fn-store-text-octetsp`, `fn-store-octets->string` |
| `host/owner-host.lisp` | `(ld "store-node-host.lisp")` | nine names across store-host, store-node-host and `books/store-config` |
| `host/native/reader-model-host.lisp` | `(ld "../reader-host.lisp")` | `fn-reader-post-config` and the five `fn-served-*` it brings with it |
| `host/simulator.lisp` | `(include-book "../books/acceptance")` | the eight acceptance functions every scenario calls |
| `host/workflow-host.lisp` | `(include-book "../books/store-node")` | `fn-sn-node` |

An `ld` inside a host file resolves against that file's own directory (ACL2's
connected book directory during an `ld`), which is why the paths are bare
siblings and `../reader-host.lisp`, matching the `../books/` spelling of the
`include-book` forms next to them.

### The raw pair was circular

`host/native/io.lisp` called `fnn-dispatch-tcpcl`, and
`host/native/tcpcl.lisp` called twenty-four of io.lisp's entry points, so
neither could be loaded without the other and build.lisp's order was the only
one that worked. io.lisp now holds a three-function verb registry
(`*fnn-verbs*`, `fnn-register-verb`, `fnn-verb-handler`) and its dispatcher
looks the verb up; it names nothing in the layer above it, and an
unregistered verb is an unknown verb, which is what a host built without that
layer should say. `tcpcl.lisp` registers `"tcpcl"` at its end and, at its
top, loads io.lisp itself when `fnn-core` is not already bound, so
build.lisp's own load of io.lisp is not re-evaluated.

### Two lint defects, fixed rather than worked around

- `slot_accessors` compared a `defstruct` option head to `"conc-name"`
  without stripping the keyword colon, while the option scan four lines below
  it used `.lstrip(":")`. So all thirteen accessors of `tcpcl.lisp`'s
  `(defstruct (fnn-tcl-conn (:conc-name fnn-tclc-)) ...)` were reported
  undefined.
- `load` is now read as a load edge exactly as `ld` is: it is the raw-mode
  spelling, and `host_record` recurses into `when`/`unless` so a guarded one
  counts.

`tools/acl2-builtins.txt` gained three names: `cddr`, `max`, `close`. They
are real ACL2/Common Lisp functions the host files call (`cdddr` and `cddddr`
were already in the file), added by the procedure that file's own header
documents. They are vocabulary for ACL2's world, which is not in this
repository — not exemptions for findings.

**`lints.host_names`: 81 on dev → 0.** No name is excused; every one is an
explicit edge.

## The dynamic half: `tools/host_check.py`

One fresh ACL2 per host file, that file and nothing else. `make check` runs
it when `FN_ACL2` is set and prints that it did not when it is not; a skipped
run is not evidence. It needs installed certificates, because an
`include-book` inside a host file reads a certificate `ld` will not produce —
which means `make test` (`check certify`) fails its check phase on a tree
with `FN_ACL2` set and no certificates yet. The three kinds of host file are
read off `host/native/build.lisp`, not typed into the tool: `ld` for the
interpreted wrappers, `raw` for the files build.lisp `load`s under
`(progn! (set-raw-mode t) ...)`, and build.lisp itself skipped because
loading it is building the image (`tools/build_native_host.sh` is its check).

**The first version of this tool was green and wrong**, and it is worth
knowing why. A failed `ld` does not end a session reading from a pipe: ACL2
reports the error, abandons the form and reads the next one. Deleting the
`ld` edge from `host/config-host.lisp` gave `ACL2 Error [Translate] in
( DEFUN FN-CFG-HOST-INITIAL-OCTETS ...)` and *then* the success marker. The
load now sits inside an `er-progn` with the marker that reports it, and any
`ACL2 Error` or `HARD ACL2 ERROR` printed before that marker fails the check
by itself. The prompt check is a second marker, printed by the next
top-level form, so its prompt is the one the file left behind: a file that
ended in `(program)` prints `ACL2 p>` and fails. That is the check on the
anchor-host `(logic)` rule.

Teeth, measured on persvati:

- negative control, `host/config-host.lisp` with its one added `ld` deleted:
  `FAIL ... error while loading: ACL2 Error [Translate] ...`, exit 1.
- the tree as committed: **21/21 host files load alone** (18 `ld`, 2 raw,
  build.lisp skipped), exit 0.

## The ACL2-backed Python suites

`tests.test_store_lifecycle tests.test_reader tests.test_post tests.test_owner
tests.test_bp_receive tests.test_checkpoint tests.test_workflow_journal` on
persvati, in the remote root above: **73 tests, 893.9 s** — 1 failure, 11
errors, 1 skip on the first run. Neither the failure nor the errors is this
lane's.

- The 11 errors were all `tests/test_checkpoint.py`, and **the whole file was
  dead on dev**: `post_many` called
  `run_store.group_codes(["fn.letters"], store.config)` where `group_codes`
  has taken the `Store` since it started reading the allocation domain the
  core hands it at recover. The same stale call is what w5/scale-2 found in
  `tests/bench/generate.py`. Repaired here, one line; that exposed a second
  staleness one line further on, `existing_action(...) == "new"`, where the
  model's vocabulary is `duplicate`, `conflict` and `:absent` and the
  production path in `run_store.post` refuses on the first two.
  `tests.test_checkpoint` is now **6/6 in 480.9 s**, including
  `test_process_death_at_every_cut_recovers_old_authority_or_complete_generation`,
  which had not run at all.
- The 1 failure is `test_post.test_a_reader_pinned_before_a_post_keeps_its_view`,
  which the board already diagnoses on dev: one clock observation is pinned
  per connection, so a connection can post durably exactly once, and this
  test posts twice on its poster. Left failing, untouched.
- The 1 skip is `nntplib`, absent from Python 3.13.

Net after the two test repairs: 71 pass, 1 pre-existing failure, 1 skip.

## Open


- `make test` runs `check` before `certify`. With `FN_ACL2` set and no
  certificates installed, the host check fails there. Either install
  certificates first or run `make check` with `FN_ACL2` unset; a successor
  may prefer to move the host check to a target after `certify`.
- The other three ledger lints are untouched by this lane (152 warnings
  total, all export/teeth/include hygiene).
