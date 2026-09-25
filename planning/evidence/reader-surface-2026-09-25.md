# Reader surface from the spike, as proved packets — 2026-09-25

Lane `reader-surface` (branch `lane/reader-surface`, from dev `00b0a846`),
PRF-110, requirement NNT-014, scenario SCN-052. Brief:
`build/coordinator/queue/reader-surface.txt`. The spike record
(`spike/mega:planning/evidence/spike-reader-2026-09-25.md`) was the
specification; nothing was merged from the spike branch except the two test
tools named below.

## 1. PKT-110: XPAT

**Which rule, and why the spike's "does not OR" is not a defect.** XPAT is
RFC 2980 section 2.9, not RFC 3977. Section 2.9: "If there are additional
arguments the are joined together separated by a single space to form one
complete pattern." fn implements that (`fn-nntp-xpat-join`, unchanged), as
INN's nnrpd does (its XPAT globs the trailing arguments into one pattern;
planning/evidence/inn-xpat-2026-09-20.md). The spike's probe
`XPAT Subject 1-10 *root* *zzz*` asked for the one pattern `*root* *zzz*`,
which correctly matched nothing. ORing a second argument would contradict
section 2.9 and INN, so it is not done. The alternative a client asks for is
the wildmat comma (RFC 3977 section 4.2): `*zzz*,*root*`.
`fn-nntp-xpat-alternation-is-or` states it at the matcher the XPAT arm calls.

**Case.** RFC 3977 section 4.2: "A <wildmat-exact> matches the same
character." `fn-wildmat-item-character-matchp` compares code points, so the
match is case-sensitive; `[...]` classes are outside RFC 3977 section 4.1
and fn parses `[` as a literal in the header profile (D19). Both unchanged.

**The label (changed).** `fn-nntp-capability-lines` now lists `XPAT` in both
branches (books/nntp-responses.lisp). RFC 3977 section 3.3.3 lets a private
extension be listed under a label beginning with "X". XOVER and XHDR stay
unlisted (they have OVER and HDR). `tools/v0_matrix.py` audits XPAT's label
in reverse (a node that answers XPAT without the label fails the pin row).

**The web reader (changed).** `tools/fn_web.py` `/search` sends the reader's
own wildmat verbatim in one bounded window, `XPAT <Subject|From> a-b
<pattern>`; the spike's client-side pattern builder (`*` + query with
reserved characters as `?` + `*`, spike deferral 4) is not carried. The
page names the command it sent. `tests/test_fn_web.py`
`ReaderSearchTests` (fake node).

**Theorems (books/nntp-xpat.lisp, new).**
- `fn-nntp-step-pinned-xpat-is-the-xpat-response`: for a well-formed, open,
  projected session and a command line within the preflight whose tokens
  are bounded and whose keyword is XPAT, `fn-nntp-step-pinned` answers
  `fn-nntp-xpat-response` over the line's arguments. The subject is the
  served reader step: host/native/owner.lisp → host/owner-host.lisp
  `fn-owner-chunk` → `fn-served-step` → `fn-served-dispatch` →
  `fn-auth-step-pinned` → `fn-nntp-post-step-pinned` (books/nntp-post.lisp:726)
  → `fn-nntp-step-pinned`. Not lifted to `fn-served-step` itself (the
  LIST COUNTS lift in books/owner-list-counts-read.lisp is the pattern; open).
- `fn-nntp-xpat-alternation-is-or`: `(implies (fn-nxp-all-positivep q)
  (iff (fn-nntp-xpat-matchesp (append p q) content) (or (... p content)
  (... q content))))`, over the matcher the XPAT arm calls. Only the right
  alternatives need be non-negated (the rightmost matching pattern decides).
- `fn-auth-capability-lines-advertise-xpat`: the block the served
  CAPABILITIES arm renders (`fn-auth-capability-lines-for-peer`, called at
  books/nntp-auth.lisp:985) contains `XPAT`, no hypothesis.

**Teeth (tests/acl2/nntp-xpat-tests.lisp).** A one-article archive, Subject
`probe root`, through `fn-nntp-step-pinned`: `*root*` 221 with the line;
`*Root*` 221 empty (case); `*zzz*` empty, `*zzz*,*root*` the line (OR);
`*zzz* *root*` empty and `probe root` the line (the section 2.9 join); the
message-id form. For the subject theorem, one counterexample per hypothesis
with the others holding: a five-slot record (sessionp), a closed session,
an unprojected session (503), the same four tokens on a 616-octet line
(command-inputp; 501), an HDR line (225, not 221). The argument-bound and
keyword-token hypotheses have no separate counterexample: under the other
hypotheses they are implied (an XPAT keyword token is a keyword token; a
510-octet line cannot hold an over-long argument whose XPAT reply differs).
Alternation: witness, and a counterexample `*` then `!*root*` plus a
`must-fail` without the positivity hypothesis. CAPABILITIES transcript
through the step. The pinned capability transcripts in nntp-tests,
nntp-reader-profile-tests, nntp-legacy-tests, nntp-auth-tests and
tests/test_reader.py now carry `XPAT`.

## 2. PKT-091: the POST boundary's refusal text is ACL2's

`host/native/io.lisp` `fnn-validate-post-boundary` kept a table from the
boundary verdict to refusal text. Now `fn-sbud-post-boundary-refusal`
(books/store-budget-naming.lisp) renders it and the host prints the octets
(`fnn-core`, `fnn-octets-string`), faulting on anything but NIL or an octet
list. The texts are the host's old ones, byte for byte, so
tests/test_native_profile_upgrade.py's `payload exceeds the modelled bound`
still holds. Theorems:
- `fn-sbud-post-boundary-refusal-is-nil-exactly-when-admitted` (keystone,
  no hypothesis): the refusal is NIL iff `fn-sbud-post-boundary` answers :ok.
- `fn-sbud-post-boundary-verdicts-are-named`: the boundary's range is the
  five named words, so the fallback text is unreachable-in-composition (it
  fails closed and is not cited as evidence).
- `fn-sbud-post-boundary-refusals-are-distinct` (two different words, at
  least one a boundary word, never share a text) and
  `fn-sbud-post-boundary-refusal-is-a-printable-line`.
Teeth in tests/acl2/store-budget-naming-tests.lisp: each of the four refusals
through the real boundary, the admitted case, the unnamed fallback, and one
`must-fail` per hypothesis of the distinctness theorem.

The Python twin `tools/run_store.py` already relays the verdict word and
keeps no table (unchanged).

## 3. Threading, search and unread counts in the web reader

| Spike computation | Decision |
| --- | --- |
| Search pattern built in Python (deferral 4) | **Moved to the node.** The reader's wildmat goes verbatim; the node parses and matches. |
| Unread count | **Read from the node** already on dev: `ReadMarks.unread` takes the count from `LIST COUNTS` (exact) or the LISTGROUP span (bounded above). The read marks are per client and per login, like a newsrc: NNTP keeps no read state, so there is no node value to read. Not moved. |
| Thread order from References | **Not moved.** ACL2 computes no thread order and NNTP has no thread verb (RFC 3977, RFC 2980); the order is a presentation over the node's own References field, as in tin and slrn. Moving it would need a non-standard node verb; recorded, not done. |
| In-Reply-To fallback | Not ported (the spike's `HDR In-Reply-To` window). Presentation only; open. |
| Deferral 1, login binding | Closed on dev by PRF-109 (path-and-login). |
| Deferral 2, `withdrawn` grammar | PKT-109, control-c3b's; not this lane's. |
| Deferral 3, live read-only status | Closed on dev by the live-status lane (`operator CONFIG status`, `pins`, `peer list`); the web operator page is not ported here. |
| Deferral 5, Date of a signed post | Stays the author's clock by design (the author's claim, inside the signature). |

## Certification (persvati, w25 `acl2-literal`, identity `1b4169e9…`, 2 jobs, 300 s)

| run | source | scope | result | manifest |
| --- | --- | --- | --- | --- |
| `run-20260925T102534Z-489d` | `d895f676` | `--affected-by books/nntp-responses books/store-budget-naming`: 491 books, 330 certified | 320 passed, 8 failed | [`certify-20260925T102606Z-3884875`](manifests/certify-20260925T102606Z-3884875.json) |
| `run-20260925T110919Z-d698` | `e81f90b5` | the four this lane's failures: nntp-xpat, nntp-xpat-tests, nntp-tests, nntp-reader-profile-tests | **passed**, 4 of 4 | [`certify-20260925T110938Z-144928`](manifests/certify-20260925T110938Z-144928.json) |

Run 1's eight failures: four were this lane's (the alternation hint lacked
`fn-nntp-xpat-matchesp`, which the responses vocabulary disables; two
pinned CAPABILITIES transcripts without XPAT; and nntp-xpat-tests, which
waited on the book). Before run 2 the book and its test book were loaded in
an ACL2 session on persvati against run 1's certificates (30 assertions,
the must-fail and every defthm admitted). The other four are red on dev
already and not caused here: `books/poster-bytes-buffer` (the D32 join
defect; lane pbb-d32), `books/store-reclaim` (`fn-pb-path-agent` now takes
two arguments), and their test books. `green_check --changed-since
00b0a846`: 249 books include a changed book; 2 not green, both those
dev-red tests.

Seconds at two jobs: nntp-xpat 4.7, nntp-xpat-tests 5.9, store-budget-naming
3.0, store-budget-naming-tests 9.3, nntp-responses 2.3, nntp-legacy 3.0.
No book this lane edited is over 10 s.

## Native: NOT RUN (blocked)

The hbox developer image of `fe6c8dcf` (`/tank/fn/scratch/reader-surface/`,
`img.sh`, w28) stopped at certification: `books/poster-bytes-buffer`
fails at `fn-pbb-source-index-is-inj-source-of` on dev since the D32 merge
(hbox evidence `build/acl2/certify-20260925T103024Z-3156392` in that tree).
No image of current dev builds until lane pbb-d32 lands. Therefore NOT done:
- the XPAT label and the refusal text observed on an image;
- PKT-111: the tin phase in a matrix run (the phase and the four
  `V0-CLIENT-TIN-*` rows are written, `tests/test_v0_matrix.py`
  `TinWireTests`; `make check` reports the four rows missing from the
  generated `planning/v0-matrix.json` until a run publishes it). tin 2.6.2
  is now on hbox's PATH: `~/.cargo/bin/tin` → the spike's build in
  `/tank/fn/scratch/spike-reader/tin/inst/bin/tin`. The cancel row needs
  node A to carry `control.cancel`; the matrix stores carry only
  `fn.letters`, so provision that group before the run or the cancel reads
  `441 … control-not-filed`.
- PKT-158: the INN lab's supplied-Path scenario (`tools/inn_lab.py`
  `scenario_supplied_path`, via `v0_matrix.py … --inn`).
- PKT-074: the three-node D23 chain (`FN_RUN_HYBRID_E2E=1 FN_D23_VERIFY=1
  FN_NATIVE_HOST=<developer image> python3 -m unittest
  tests.test_native_hybrid_author -k d23`). Coordination with peer-carriage:
  once it lands, a `carries` list with no budget carries nothing, so the
  chain's relay config must add `peer budget NAME OCTETS COUNT` or the
  allowlisted case reads 439.

The next run, once dev builds: `sh img.sh` (developer), then the production
image, then `v0_matrix.py … --backend native-operator --inn --publish-current`
with `control.cancel` in node A's store, then the D23 pair.
