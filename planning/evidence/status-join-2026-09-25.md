# status-join — 2026-09-25

Lane `lane/status-join` from dev `00b0a846`. PRF-089 extended (no new
PRF). Backlog: PKT-150, PKT-156, PKT-105, PKT-145.

Commits: `ea66da80` (PKT-150, 105, 145, the test fixes), `c2963b6d`
(PKT-156 renderer with its theorem), this record.

## What changed

- **PKT-156, the cause.** `fn-nls-nat` rendered through
  `fn-nntp-decimal-field`, the NNTP response renderer, which answers `0` for
  a number of more than ten digits (RFC 3977 §6 bounds what it renders).
  2^33 is ten digits and 2^34 = 17179869184 is eleven, which is the threshold
  native-drift measured on the images; the default max-history-octets 2^40
  printed `max-history-octets=0` and `history-bound=0`. Not a fixnum or
  compiled-path divergence. Now `fn-nls-nat` is `fn-nls-digits` (floor/mod by
  10, any natural), and a profile value that is a word (`history-marker`,
  `required`/`unmarked`) prints the word (`fn-nls-value`), where `nfix` made
  it `0`.
- **PKT-156, the script.** `tests/test_native_io_progress.sh` failed in
  `fn-store-profile-max-transactions` because the transaction-enumeration
  case built a pre-format-8 positional config `(nil 0 0 0 3)` and, since
  bounds-profile, `fnn-config-max-transactions` asks ACL2, which the raw test
  does not load. The case now answers exactly that one wrapper (T = 3) and
  refuses any other ACL2 call; two more stale stub arities
  (`fnn-bridge-transaction-observation`'s selected-lower,
  `fnn-bridge-config-observation`'s initializing) are fixed. The script
  prints `native-io-progress: ok` and `native-config-observation: ok`
  (laptop SBCL).
- **PKT-150.** The host's observation gains a fourth field, the newest
  published state checkpoint's lstat `(OCTETS MODIFIED)` or nil
  (host/native/io.lisp `fnn-state-checkpoint-file-observation`, called in
  `fnn-store-observation`; the old `format` report is gone). ACL2 renders
  `checkpoint-file octets=N modified=T` or `checkpoint-file=absent`
  (`fn-nls-checkpoint-file-words`) after the `open=` line, in both reports.
  The owner observes it at each offset-0 request.
  tests/test_native_state_checkpoint.py asserts `checkpoint-file=absent`
  before the first checkpoint and `octets=` equal to the file's size after.
- **PKT-105.** `open-cost replay-records=T list-memory-octets=M` after the
  profile line (`fn-nls-open-cost-words`), M = 32 × max-history-octets:
  the pessimistic figure of design-2026-09-25-bounds §3.3/§4. Scope: a full
  replay (a checkpoint may be absent or refused) of up to max-transactions
  records, payloads as octet lists, two long-lived copies at 16 octets of
  cons per octet on 64-bit SBCL. It is what the profile admits, not what
  the Store holds or an open measured; at the default H = 2^40 it is
  35184372088832 octets (32 TiB).
- **PKT-145.** The owner renders a report once per request (offset 0) into
  a string buffer with its frame digest (`fn-nls-buffer`) and answers every
  later page of that kind as a substring (`fn-nls-page`), so a page costs its
  chunk, not a render plus a SHA-256 of the whole report. ACL2 chooses
  between the stored buffer and a fresh render (`fn-nls-cached-buffer`,
  `fn-nls-cache-put`); the host only carries the list
  (host/native/control.lisp `*fnn-live-status-buffers*`, under the owner
  mutex). A new offset-0 request of the same kind replaces the buffer, so a
  client mid-join sees a new digest and restarts, as before.
  Host entry: host/native-live-status-host.lisp
  `fn-native-live-status-host-answer` (replaces `-reply`), returns
  `(REPLY CACHED')`, still no `state`.

## Theorems (books/native-live-status.lisp)

- KEYSTONE `fn-nls-nat-is-the-decimal-digits`: `(natp n)` ⇒
  `(consp (fn-nls-nat n))`, `(fn-nntp-decimal-tokenp (fn-nls-nat n))` and
  `(fn-nntp-decimal-value (fn-nls-nat n)) = n`. Every number of the report
  goes through `fn-nls-nat` (via `fn-nls-field`/`fn-nls-value`), reached by
  `fn-native-live-status-host-offline` (io.lisp `fnn-command-live-report`)
  and `fn-native-live-status-host-answer` (control.lisp
  `fnn-control-live-status-answer`).
- `fn-nls-page-of-buffer-is-reply`, no hypothesis:
  `(fn-nls-page (fn-nls-buffer report) off) = (fn-nls-reply report off)`.
  The D27 twin of the page.
- KEYSTONE `fn-nls-client-step-of-owner-page`: the statement of
  `fn-nls-client-step-of-owner-reply` (unchanged, still proved) with the
  owner's page `(fn-nls-page (fn-nls-buffer report) (len acc))`, the
  function the host calls.
- `fn-nls-cached-buffer-of-put`: `(posp off)` ⇒ the buffer looked up for
  KIND after storing BUFFER for KIND is BUFFER.
- `fn-nls-live-report-is-the-offline-report` unchanged in statement; the
  new lines are inside `fn-nls-report`, so live and offline share them.

## Teeth (tests/acl2/native-live-status-tests.lisp)

- digits: 2^40 → `1099511627776`, 2^64−1 in full, `fn-nntp-decimal-field`
  of 2^40 is `0` (the defect), value read back; must-fail at −5.
- words: ` max-history-octets=1099511627776` in a status with H = 2^40; a
  `history-marker=` word and no `history-marker=0`; the exact
  `checkpoint-file octets=4096 modified=1790000000` line and
  `checkpoint-file=absent`; live = offline with the file observed; the exact
  `open-cost` line with `list-memory-octets=35184372088832`.
- page twin: equal to `fn-nls-reply` at offset 0, past the first chunk, and
  for a refused non-octet report; two buffered pages join.
- owner-page keystone: one must-fail per hypothesis (octets, prefix,
  length, same report, uint32 total under the keystone's hints).
- cache: witness with another kind stored; must-fail at offset 0.

## Certification

- persvati (w25 `acl2-literal`, 2 jobs, 300 s):
  run-20260925T102416Z-04da (manifest certify-20260925T102438Z-3869081,
  deps green, the book red on a lemma; fixed in the REPL);
  run-20260925T103112Z-4bcf (ea66da80): manifest
  `planning/evidence/manifests/certify-20260925T103156Z-3949164.json`,
  books/native-live-status 6.48 s, tests/acl2/native-live-status-tests
  5.28 s, passed.
- c2963b6d: book and test book loaded clean in the persvati REPL
  (74 forms; the test book's 44 passes, no error).
- hbox (w28 `acl2-literal-4g`, 2 jobs, 300 s), the 142 default image roots
  plus the test book, at c2963b6d: run-20260925T104923Z-f8a9, manifest
  `planning/evidence/manifests/certify-20260925T104949Z-3199172.json`:
  13 of 14 passed, native-live-status 8.94 s, native-live-status-tests
  7.38 s; `books/poster-bytes-buffer` failed, red on dev since the D32
  merge (lane pbb-d32), not this lane's.

## Native (hbox)

NOT RUN. Every image from dev after 09c0af20 fails at
books/poster-bytes-buffer (D32 join defect; lane pbb-d32, no commit yet
when this lane stopped). The native runs (offline vs live status
byte-identical with the checkpoint-file line and the full values; the
capacity tests; OperatorFieldsTests.test_a_raise) wait for that fix and
are the continuation's first job.

## Not done, and why

- The renderer and the FNLS frames are still octet lists; only the page is
  a string twin (D27 twin of `fn-nls-report` open).
- The page theorems say nothing about a buffer rendered from an older state
  than the current one: a page is of the report its request's first page
  rendered, by design.
- The checkpoint-file line is each answering process's lstat; offline and
  live agree only when no publication happens in between.
