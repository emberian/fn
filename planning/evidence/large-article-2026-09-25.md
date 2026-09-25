# Large articles: the per-octet recursions, the TLS refusal, the signed POST (2026-09-25)

Lane `lane/large-article` from dev `a7756b67`. Commits `4d75b021` (the
twins, the TLS close, the verify test), `7fc757a8` (the test book's
off-guard witnesses) and the evidence commit. Images were built on hbox from
the lane's books and host at `4d75b021` (the later commits change tests
only): `fn-host.core` `b2c9b729…`, `fn-host-developer.core` `7354b90e…`,
default image closure certified at 8 jobs on hbox (w28 `acl2-literal-4g`),
`certify-image-hbox.log`.

## 1. What stopped the owner, and where

Found with the image's own backtrace at the exhaustion: a scratch-only
`handler-bind` on `storage-condition` in `fnn-call` (host/native/io.lisp)
printing `sb-debug` frames, never committed. A developer image from dev
`a7756b67`, profile `--max-article-octets 4194304`, 64 MB control stack:

| Size | Before (dev a7756b67) |
| --- | --- |
| 2,097,152 | 240, re-read identical |
| 3,145,728 | 240, then `store inspect` rc 4 and the restarted owner stops: `ACL2 error in fn-store-frame-store-decode: Control stack exhausted` (`repro-3.log`) |

- **The 2 MiB stop of the bounds-join evidence is already gone on dev.** It
  was the list SHA-256 (`fn-sha256-appx` in `fn-sha256-pad`,
  books/sha256.lisp, one frame per message octet) under `fn-owner-take`'s
  intent digest. The rep-sha256 merge attached `fn-sha256-stobj` to
  `fn-digest` and `fn-frame-digest`, so the take no longer walks the list.
  Dev's image accepts 2 MiB and 3 MiB with no change from this lane.
- **`fn-frame-split` (books/frame-octets.lisp:80 before).** The recursion
  was one non-tail frame per octet of the split prefix. At 3 MiB the
  backtrace (`backtrace-fn-frame-split-owner-restart.err`) shows it as
  frames 6 and up, under `fn-store-frame-store-decode`. The host reaches it
  at host/native/io.lisp:910 (`fnn-unframe`), which runs on
  `store inspect` and on owner recovery. The depth is the stored record's
  payload length, about 3,146,000 octets.
- **`fn-ag-append` (books/acceptance-alloc.lisp:37 before).** Its `:exec`
  was `(cons (car xs) (fn-ag-append (cdr xs) ys))`. This was found by the
  same handler at a 2 MB survey stack after a raw stand-in for the split.
  The ARTICLE reply of the 3 MiB article failed with
  `ACL2 error in fn-owner-chunk`, frames `FN-AG-APPEND` repeated. The depth
  is the length of the first argument, the article. That run's output was
  printed and not saved.

The survey then ran with both raw stand-ins at a 2 MB control stack, 1/32 of
the deployed stack. POST, `store inspect`, owner restart and ARTICLE of a
3 MiB article all passed. No other per-octet recursion is on those paths.
The 2 MB run of the fixed image in §3 repeats this at 4,193,280 octets.

## 2. The fix (D27 concrete twins, constant stack)

- books/frame-octets.lisp: `fn-frame-split-acc` is tail recursive. It
  pushes each octet onto an accumulator and applies `revappend` once, for
  2n conses and constant stack. `fn-frame-split` is `(mbe :logic <the
  unchanged list definition> :exec (fn-frame-split-acc n xs nil))`.
  - **Keystone** `fn-frame-split-acc-is-split`:
    `(equal (fn-frame-split-acc n xs nil) (fn-frame-split n xs))`, with no
    hypothesis. It rests on the local `fn-frame-split-acc-is-split-onto`.
  - `(verify-guards fn-frame-split)`.
- books/acceptance-alloc.lisp: `fn-ag-rev-onto` is tail recursive.
  `fn-ag-append-exec` is `(revappend (fn-ag-rev-onto xs nil) ys)`.
  `fn-ag-append` is `(mbe :logic (append xs ys) :exec (fn-ag-append-exec xs
  ys))` at guard t.
  - **Keystone** `fn-ag-append-exec-is-append`:
    `(equal (fn-ag-append-exec xs ys) (append xs ys))`, with no hypothesis.
  - Every function is guard-verified.
- **Unchanged.** The logical definitions of both functions and every
  theorem above them. The octet list stays the representation at these
  boundaries. The list-free frame decode is boundary 8 of
  design-2026-09-25-representation.md.
- **Teeth**, in tests/acl2/stack-depth-twins-tests.lisp:
  - small exact witnesses;
  - the off-guard agreements (a negative count, an improper list) as
    ground theorems;
  - one accumulator counterexample per keystone, since the only thing a
    keystone can drop is ACC = nil;
  - 3,000,000-octet witnesses through the executable path, a depth the old
    recursion exhausted.
- **Registry.** PRF-014 events `fn-frame-split-acc-is-split` and
  `fn-ag-append-exec-is-append`.

## 3. Native (hbox, fixed images, 64 MB stack unless stated)

`native-sizes.log`. POST, then `store inspect`, then restart, then ARTICLE:

| Source octets | Reply | POST wall | Owner VmHWM | Re-read |
| --- | --- | --- | --- | --- |
| 2,097,152 | 240 | 2.04 s | 569,236 kB | ARTICLE = inspect, source is its suffix |
| 3,145,728 | 240 | 2.73 s | 749,228 kB | identical |
| 4,193,280 | 240 | 3.79 s | 895,504 kB | identical |
| 4,194,304 | `441 … exceeds the configured size` | 1.37 s | 500,240 kB | absent |

- **The 4 MiB rows.** The stored article is the source plus 163 octets of
  injected fields, and A bounds the stored article (`fn-inj-decide`
  compares the injected octets with the configuration's bound). A source of
  exactly A is therefore refused by name. 4,193,280 is 4 MiB minus 1 KiB.
- **At a 2 MB control stack** (`native-sizes-2mb-stack.log`), the
  4,193,280 row passes the same four steps.
- **The probe** (`probe.log`, `probe.json.gz`) was run with
  `--body-octets 3145728` and `--init-flags '--max-article-octets
  4194304'`. **54 of 54 rows pass.**
  - Every POST cut × {kill, eio} (46 rows) passes on the 3 MiB candidate.
  - The four controls pass.
  - The size controls: 2,097,152, 3,145,728 and 4,193,280 get 240 and
    re-read identical; 4,194,305 gets the size 441, and nothing is stored.

## 4. The 60 KiB signed POST: three causes, two fixed

1. **The test's store never had A = 4 MiB.**
   - The cause: `store ROOT init` (developer, host/native/io.lisp:2852
     `fnn-command-init root rest`) takes every word as a group name.
     `--max-article-octets` and `4194304` became groups, visible in the
     config record, and A stayed 32,768.
   - The fix: tests/test_fn_verify.py now runs `operator CFG init FLAGS`,
     which reads profile fields, and reads the bound back from `status`.
   - Not fixed: the developer verb still accepts flag-shaped words as
     group names. RFC 5536 permits the name, so the ACL2 side is right to
     accept it.
2. **On TLS a refusal stopped the whole owner.**
   - A POST past the bound closes the wire mid-article
     (`:body-overlimit`), so the step consumes a prefix of the 512-octet
     read. On a protected channel the host then faulted with "protected
     owner read left a TLS suffix" (host/native/owner.lisp, the `channel`
     arm of `fnn-owner-serve-client`). The instrumented image showed
     `consumed=43 incoming=512 closing=T` with the 441 in hand.
   - Fixed: when the step closes, the reply is sent. On a protected
     channel the close_notify goes first, followed by the same bounded
     drain as plaintext.
   - New test `test_an_article_past_the_profile_over_tls_is_a_441_and_the_owner_serves_on`
     passes at A = 65,536 (`verify-64k.log`, 27 run, OK, 3 skipped) and at
     A = 4 MiB (`verify-large-3.log`).
3. **Not fixed, and the cause of the remaining refusal.** The kind-4
   signed-article composite has data caps (books/stx-accept-records.lisp):
   - `*fn-stxa-max-authored-source*` 32,768 (:27);
   - `*fn-stxa-max-article-record*` 65,538 (:26);
   - `*fn-stxa-max-octets*` 196,608 (:18).

   `fn-hsig-authorized-carried-submission-event-base`
   (books/hybrid-store.lisp:272) returns nil past them. The host reports
   `:event` (instrumented image, `verify-6.log`:
   `word=:REFUSED detail=:EVENT octets=70115` and `octets=215459`), and the
   wire says `441 posting failed; the article was refused`. The signature
   verified before that point.

   This is a D27 defect: a constant that caps stored data. The book's own
   comment assigns it to packets P1 and P4 ("derives all three from the
   profile's record bound … raises the authored source with the v2
   carrier"), and the frame `:blob` 131,072 packet sits under it. **The
   60 KiB v1 and 200 KiB v2 cases therefore cannot be accepted on this
   tree, and fn_verify exit 0 on them is not shown.**
   - `verify-large-3.log` shows every outcome as a 441 with a reply,
     never a closed socket.
   - The tampered v2 gets `441 … the author signature does not verify`.
   - The 7,717-octet signed POST verifies (240; the verifier test
     `test_signed_post_verifies_independently_0` passes).

## 5. Findings for other packets

- **The signed ingress costs superlinear time in the article.** Over TLS:
  - 70,040 octets take 4.53 s;
  - 215,384 octets take 48.02 s, 3.1× the size for 10.6× the time;
  - an unsigned 207,865-octet POST on the same connection type takes
    0.15 s.

  So the cost is in the carrier path: `fn-owner-peer-carrier-form`,
  `fn-owner-peer-carrier-plan`, `fn-hsig-host-preimage` and
  `fn-pa-authorized-event`'s re-plan, all over octet lists. The client's
  `hybrid-sign-carrier` (`fn-hsig-host-render-carrier`) took about 150 s
  for 200 KiB. The function responsible is not isolated.
- **The unnamed refusal.** The `:event` refusal reads
  `441 posting failed; the article was refused`, which names no reason.
  tests.test_native_owner's
  `test_article_over_the_body_limit_is_refused_and_the_owner_survives`
  fails the same way (`native-owner.log`), as it did on the bounds-join
  image (its native-a.log). The developer `owner run` path does not
  install the profile's served bound, so a 40 KiB article passes the wire
  and is refused later without a name.
- **Four books over 10 s at 2 jobs** in the persvati run below:
  `bp-node-progress-guards` 11.0 s, `owner-invariants` 10.8 s,
  `store-node-traces` 10.8 s, `store-node-invariants` 10.5 s. This lane did
  not change them. Earlier persvati 2-job runs had them at 9.3, 13.9, 11.8
  and 11.4 s.

## Certification (persvati, w25 `acl2-literal`, 2 jobs, 300 s)

| Run | Rev | Scope | Result | Manifest |
| --- | --- | --- | --- | --- |
| run-20260925T062518Z-f0ce | 4d75b021 | frame-octets, acceptance-alloc, the test book | the two books passed (0.7 s, 0.1 s); the test book failed on an off-guard evaluation | `certify-20260925T062529Z-1501970.json` |
| run-20260925T062750Z-9c75 | 7fc757a8 | `--affected-by` frame-octets, acceptance-alloc: 629 roots, 639 books certified | 639 of 639 passed, wall 1,049 s | `certify-20260925T062846Z-1530323.json` |
| run-20260925T065152Z-6ead | 7fc757a8 | tests/acl2/stack-depth-twins-tests | passed, 1.1 s | `certify-20260925T065205Z-1741020.json` |

## Logs (planning/evidence/large-article-2026-09-25/)

| File | sha256 |
| --- | --- |
| backtrace-fn-frame-split-owner-restart.err | `26b119d0…` |
| repro-3.log (dev image, 3 MiB inspect exhaustion) | `57af908c…` |
| certify-image-hbox.log | `b291fde6…` |
| native-sizes.log | `1191fbf2…` |
| native-sizes-2mb-stack.log | `be2eb7b8…` |
| probe.log / probe.json.gz | `2dc5356e…` / `35b36caa…` |
| verify-64k.log | `06078cb1…` |
| verify-large-3.log | `84e03b1d…` |
| verify-6.log (instrumented image, the `:EVENT` detail) | `2f4712c4…` |
| native-owner.log | `05955fc1…` |
| native-proof.sh / verify2.sh / repro.py | `fc7e2783…` / `d09211b4…` / `80ca5d74…` |
