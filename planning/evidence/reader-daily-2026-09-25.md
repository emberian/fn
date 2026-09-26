# reader-daily — 2026-09-25

Lane `reader-daily` (wave 2, the Fable mandate §11 and §15 "Protected ordinary
use"), branch `lane/reader-daily` from dev `483987b1`, dev merged at
`ebae2d0e` (visibility-join's NNT-019). Ids: NNT-021, PRF-122, SCN-068,
PKT-175. `lane/reader-surface` had no commits beyond dev; nothing salvaged.

What now works, on a developer image, as a person would use it: read a group
whose window has a withdrawn number and see it as a withdrawal with the node's
answer; open a conversation whose middle message was withdrawn and see it in
its place; search a group in a stated window; reply (double-click and Back do
not post twice); post while the node is unreachable, restart the client, and
settle the uncertain post on request; see the five provenance facts apart.
tin posts, follows up and cancels through the same server path.

## The proof (PRF-122) — the search scope is the node's

`books/nntp-search-scope.lisp`, teeth `tests/acl2/nntp-search-scope-tests.lisp`.

- **`fn-nntp-step-pinned-xpat-range-is-the-scope`** (keystone). For an open,
  well-formed, projected session with a selected group, and a line within the
  preflight whose keyword is XPAT, whose field is a header name or metadata
  item, whose second argument is a range and whose joined pattern parses:
  `fn-nntp-step-pinned` = `fn-nntp-multi` of `221 header follows` and
  `fn-nntp-hdr-lines-for-numbers FIELD GROUP (fn-nss-hits FIELD PATTERNS GROUP
  (fn-nntp-group-range-numbers GROUP LOW HIGH ARTICLES) ARTICLES) ARTICLES`.
  Ten hypotheses. Three of the base keystone's hypotheses are dropped after
  proving the weakened theorem (a keyword equal to XPAT is a keyword token:
  `fn-nss-xpat-keyword-is-a-keyword-token`; a parsing pattern is at least one
  argument; tokens are a cons).
- **`fn-nss-hits-are-the-scope`** (keystone, no hypotheses). A number is a hit
  iff it is positive, `LOW <= n <= HIGH`, the group's served archive holds an
  available article at it, its field renders, and `fn-nntp-xpat-matchesp`
  accepts the rendered field.
- **`fn-nss-withdrawn-number-is-never-a-hit`** (keystone). A token the pinned
  step answers `423 withdrawn` for (`fn-nntp-number-withdrawn-p`) never names
  a hit, for any field, pattern or number list.

Host line: `host/native/owner.lisp` → `host/owner-host.lisp` `fn-owner-chunk`
→ `fn-served-step` → `fn-served-dispatch` → `fn-auth-step-pinned` →
`fn-nntp-post-step-pinned` → `fn-nntp-step-pinned` (the chain
`books/nntp-xpat.lisp` states). The client (`tools/fn_web.py`
`Backend.search`, `Backend.thread`) sends `GROUP` then `XPAT`, keeps no index
and decides nothing about scope, visibility or match.

Assurance chain: native entry `fn-owner-chunk` → executed ACL2 subject
`fn-nntp-step-pinned` over the pinned served archive → (no representation
change here: the XPAT arm runs over the same archive list the keystone names)
→ maintained relation `fn-own-control-okp` (books/owner-invariants.lisp,
established at owner open and carried per connection: the served archive is
the visible list, the pin's W the withdrawn list) → behavioural theorems above
→ observed: `XPAT Subject 1-4 *notes*` and `XPAT References 1-4
*<walk-root@fn.example.invalid>*` on the image (walk records below), with the
withdrawn number 2 absent from both.

Teeth: a real accepted archive (`fn-accept-prepare`/`-complete`: fn.letters 1
"search alpha", 2 "Re: search alpha" referencing 1, fn.other 1): witnesses for
both directions of the scope iff (in range, out of range, other group, case
mismatch, the References thread query); control-served-tests' withdrawal view
for the withdrawn keystone (witness: 423 arm fires for 1, hits are (2);
hypothesis removed: over the raw list, 1 is a hit); for the step keystone the
ten hypotheses evaluated as a list, the witness (221 block "1 search alpha",
"2 Re: search alpha"), and one counterexample per hypothesis in which the
other nine hold, the removed one fails and the conclusion fails.

Certification: farm run `run-20260925T234642Z-ec19` on hbox (w28, 2 jobs,
300 s), manifest
`planning/evidence/manifests/certify-20260925T234713Z-4045738.json`: passed,
`books/nntp-search-scope` 3.4 s, `tests/acl2/nntp-search-scope-tests` 3.2 s,
`books/nntp-xpat` 2.8 s, `tests/acl2/control-served-tests` 2.8 s. After the
dev merge, `run-20260926T002150Z-62b8` (manifest `planning/evidence/manifests/certify-20260926T002211Z-4117190.json`) found both roots already certified at
the merged bytes (0 certified). `make check` green with a locally regenerated
ledger (ledger files not committed; the deputy regenerates).

## The client (NNT-021, `specs/human-client.md#the-daily-reader`)

- Holes: every number in the window and the group's range with no overview
  row is asked `STAT n` (at most 40 per page) and shown with the node's answer.
- Conversation `/t`: References asked one by one (`STAT <id>`); replies from
  `XPAT References <window> *<root>*`; a missing earlier message keeps its
  place as a placeholder with the node's answer; wildmat-special characters
  are stood for with `?`, and the page says so.
- Provenance: claimed From; carriers present; the node's historical verdict;
  current enrollment "not available" (no served query; PKT-175); independent
  verification "not performed: carried but not independently verified here".
- Submission identity: `/compose` mints once and redirects to `/c?id=...`;
  after a post that page says "already posted". Uncertain records are
  settled by visibility-join's `/reconcile` (NNT-019), only on request. The
  lane's own `/resend` (commit `f1941527`) duplicated it and was replaced in
  the dev merge (`74191b94`). The lookup is a form POST. A local-record
  failure is labelled as this machine's failure, not the node refusing.
- HTTP: `Sec-Fetch-Site` other than `same-origin`/`none` is refused before any
  NNTP command or write (tested: no ARTICLE sent, no mark written); Host and
  Origin checks, CSRF token, CSP `default-src 'none'`, loopback, no password in
  argv or URL (the walk used `FN_CLIENT_PASSWORD`), escaped content.

Tests: `tests/test_fn_web.py` (fake socket; 5 new cases: holes/withdrawn,
conversation across a withdrawn middle, Back after posting, cross-site
refusal, plus reconciliation cases from visibility-join), `tests.test_fn_web`
+ `tests.test_fn_client` + `tests.test_node_probe`: 92 tests OK.

## The walk (a scripted walk, not a human study)

Playwright (Chromium, `~/tools/playwright`) on the laptop, driving
`tools/fn_web.py` on the laptop, over STARTTLS with a verified certificate and
AUTHINFO as `ember`, through an ssh loopback forward to a scratch node on hbox
(`/tank/fn/scratch/reader-daily/node`, `pl_node.py` from path-and-login,
`[auth] required`, `systemd-run --user -p MemoryMax=24G`). Content: ember's
signed root and signed reply (`hybrid-sign` + `hybrid-author`,
`rd_seed.py`), guest's tin follow-up to the reply, a tin new post and a tin
cancel, then ember's signed cancel of the reply (`423 withdrawn` / `430
withdrawn` natively).

Each first confusing or impossible action, and the fix:

1. The conversation showed the withdrawn reply in a separate list, so guest's
   follow-up to it sat under the root. Fixed: placeholder in place.
2. **Back after posting, then Post, posted a second article** (two 240s on the
   node, `walk2-reply-before-fix.json`: `fd0551f3` and `b12ac165`). Cause:
   `Cache-Control: no-store` re-fetched `/compose`, which minted a new
   identifier. Fixed: `/c?id=...`; the rerun shows "This form was already
   posted" for Back and refresh (`walk3-reply-after-fix.json`).
3. The uncertain page said "Do not repost" beside a re-send button and "as it
   was sent" when no connection had opened. Reworded.
4. The outbox listed bare Message-IDs in arbitrary order. Now uncertain first,
   then drafts, with subject, group and state.
5. After a re-send the node accepted, the headline still said "may or may not
   have been accepted", and "already stored here" wore a "refused" badge.
   Fixed (and then carried onto NNT-019's reconciliation in the merge).

Native observations on image `f1941527` (`image-f1941527.log`,
`fn-host-developer.core` `436a8c96…`): the full session passed after fixes
1–5: groups; group window with the withdrawn number; article provenance;
conversation; search; reply with double-click (one POST); Back (no POST);
refresh; draft save; post with the node unreachable → uncertain; client
restart → the record uncertain, nothing sent; re-send → `240`; re-send again
→ `441 posting failed; this article is already stored here`; lookup → served.

## Final image (the native gate)

Developer image from `74191b94` (the dev merge; later lane commits change only
`tools/fn_web.py` wording, tests, docs and this record: `git diff 74191b94
HEAD -- books host` is empty), `image-74191b94.log`:
`fn-host-developer` `181bd7c2…`, `fn-host-developer.core`
`e7efe680d08df17a530ae4e6b8420298a5f4b305107b2837c2b38aa7497d48d6`, 0
undefined lines. A fresh scratch node (`node2`) on it, seeded the same way:

- tin (`tin-wire-final.log`, `tin-screens-final/`): follow-up with both
  References → 240; new post → 240; cancel → 240 (unsigned: the target stays
  served).
- ember's signed cancel of the middle reply: withdrawn.
- Playwright, one session with the final client behaviour
  (`final-walk-reading.json`, `final-walk-reply.json`, `final-walk-lost.json`,
  `final-walk-resume.txt`, `final-*.png`/`resume-*.png`): group window with
  `423 withdrawn` at #2; provenance panel; conversation with the withdrawn
  placeholder between root and tin's reply; search `XPAT Subject 1-4 *notes*`;
  reply with a double-click → one accepted post; Back and refresh → "This form
  was already posted"; draft saved; post with the node unreachable →
  uncertain/unresolved; client restarted → the outbox lists it first as
  "needs settling", nothing sent; "Re-send this same article to settle it" →
  "accepted … stored once"; the outbox then says "settled by re-sending:
  accepted". The resume script stopped after that step (its JSON was not
  written; the observed lines are in `final-walk-resume.txt`). Two client
  wording edits after that run (the withdrawn note, the settled advice) are
  covered by the fake-socket tests, not by a rerun.

Every file above has its SHA-256 in `reader-daily-2026-09-25/SHA256SUMS`.

## tin (D32 evidence extended)

tin 2.6.2 (`/tank/fn/scratch/spike-reader/tin/inst`, built without TLS, plain
AUTHINFO on loopback as `guest`) through `nntp_wire_log.py`
(`tin-wire.log`): follow-up with `References: <walk-root…> <walk-mid…>` and
`Path: not-for-mail` → `240`; new post → `240`; cancel (`Control: cancel
<…241201.fn@fn.example.invalid>`) → `240`, filed in `control.cancel`; the
unsigned cancel carries no authority, so the target stays served (`STAT 4` →
`223`), which is C2's rule, not a failure. Screens in `tin-screens/`.

## Not done, and why

- Current enrollment/authorization is not served by the node: PKT-175 below.
- Independent verification in the client is not implemented (the client holds
  no verifier; the page says "not performed").
- A lost reply *after* bytes were sent was not produced natively in the walk
  (the unreachable case sends nothing); visibility-join's native case covers
  commit-then-drop.
- The group window does not say a card's parent was withdrawn (its
  conversation does).
- tin over TLS; a human session; a non-loopback deployment: not done.

## PKT-175 — a served current-enrollment fact (decision for ember)

Trace: the article page can show the node's historical verdict but not
whether the signer is enrolled now; the node serves no query for it.
Constraint: ACL2 must decide it (no Python keyring reading). Default: leave
"not available" and add an HDR metadata item `:fn-enrollment` (current
generation and state of the verdict's principal, from the node's keyring
view) as an ACL2 function on the pinned step, with its theorem. Rejected
alternative: the client reads the node's keyring file — a second decision
engine and a store read from a client. Affected: public wire (a new private
`:fn-` metadata name), PRF (new), the article page. Continues without it:
everything above.
