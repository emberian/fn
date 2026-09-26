# peer-feeds (wave 4, lane 2), 2026-09-26

Lane `lane/peer-feeds` from dev `eb79070b`. Brief:
build/coordinator/queue/done/w4-peer-feeds.txt. IDs: PRF-165, NNT-035,
SCN-095, PKT-431, PKT-432.

## What a friend's peering now survives

A friend's server that keeps listing an article it cannot produce (it
answers `ARTICLE` with 430) no longer stalls the pull. Before: in
`fn-pull-on-line`'s `:article` phase any code but 220 went to `fn-pull-fail`,
so the first 430 ended the round and the cursor never moved while the peer
listed that id (PKT-213). Now the 430 is an answer of the class
*unavailable*, the other ids arrive in the same round, the id holds the
cursor's instant for at most BOUND consecutive complete rounds, and the
round whose count reaches BOUND advances and logs `dropped=<id>` once.

BOUND is a peer-record figure: the `pull-unavailable-rounds` row, set by
`peer pull NAME SECONDS ROUNDS` (books/native-admin-peer.lisp; the row is a
single-valued slot in books/peer-carriage-rows.lisp). When absent it is
`*fn-pull-default-unavailable-rounds*` = 5, classed in the book as local
policy: it bounds WORK (each held round re-lists and re-offers what the peer
received since the held instant, one interval apart), never what is stored.
A peer-record figure because the right figure depends on the friend's
server (a slow spool that later produces the article wants more rounds);
not a proved per-round bound, because what it limits is how many rounds, not
the work inside one.

## Assurance chain

native entry `fnn-pull-round` (host/native/pull-service.lisp) -> executed
subject `fn-pull-session-step-pair` (:293) / `fn-pull-session-close-effects`
(:325) / `fn-pull-session-close` (:327), and at open `fn-pull-journal-scan`
(:102) folded by `fn-pull-records-replay` (:124), each append
`fn-pull-cursor-envelope` (:157) -> refinement
`fn-pull-records-replay-is-the-replay` (the scanned records fold to the
logical replay) and `fn-pull-session-step-pair-by-definition` -> maintained
relation: the journal replays to the owner's cursor
(`fn-pull-journal-is-the-cursor-at-every-cut`, PRF-100, statement unchanged
over the four-field cursor; its session transfer
`fn-pull-session-journal-is-the-cursor-at-every-cut`, PRF-125), established
at open by the replay and preserved by the begin's and the close's records
-> behavioural theorems below -> observed in the native cases below.

## Theorems (PRF-165)

Over the host-called session (books/peer-pull-session.lisp):
- `fn-pull-session-close-advances-only-past-a-fully-answered-round`: if the
  close moves the advance count, the round is `:done`, every listed id drew
  235/435/437 from the local node OR the peer's 430 in this round with its
  consecutive count reaching BOUND, the instant is the peer's DATE less the
  overlap, PENDING is nil. PRF-100's round-level keystone of the same name
  is restated the same way; its old conclusion (every id terminal) is kept
  verbatim for a round with nothing unavailable
  (`fn-pull-close-advances-past-all-answered-when-nothing-is-unavailable`)
  and the old form is a `must-fail` on the dropped-id witness.
- `fn-pull-session-unavailable-id-is-retried-below-the-bound`: an id
  unavailable with 1 + its count below BOUND leaves instant and advance
  count unchanged, and a complete round journals its count as exactly one
  more.
- `fn-pull-session-complete-round-past-the-bound-advances`: a complete round
  in which every unavailable id reached BOUND advances and clears PENDING.
  With the previous theorem: dropped at the round its count reaches BOUND,
  never before (the log names it via `fn-pull-dropped`).
- `fn-pull-session-step-marks-unavailable-only-on-the-peers-reply`: only a
  remote event after the preamble, in `:article`, marks an id, and exactly
  the article in hand.
Round level (books/peer-pull.lisp): the four above's round forms,
`fn-pull-unanswered-id-holds-the-cursor` (restated),
`fn-pull-records-replay-is-the-replay`,
`fn-pull-records-replay-ignores-an-uncommitted-tail`.

Teeth: tests/acl2/peer-pull-tests.lisp and peer-pull-session-tests.lisp: a
two-round witness (bound 2: round 1 held with `(<a> . 1)`, round 2 advances
and drops `<a>`), and a `must-fail` per hypothesis (member: `<b>`'s count
does not rise; below the bound: round 2's instant moves; Message-ID: a
corrupted-state non-id is not counted, labelled; not holding / complete:
round 1 and the lost round do not advance; peer's reply: the same `430` line
from the local node marks nothing; the uncommitted tail: with its cursor
record the tail commits; record order: a cursor record before its
unavailable records loses the count, labelled mutation).

FNPL: kind `:pull-unavailable (peer id count)` (code 2) beside
`:pull-cursor`; a cursor append writes one unavailable frame per PENDING
entry then the committing cursor frame, in one write and one fsync (the
crash cuts are unchanged: `FN_PULL_TEST_KILL` counts appends). The scan
carries a committed offset, the truncate authority, so uncommitted
unavailable frames are repaired away. Format consequence: PKT-432.

## Certification

- persvati run-20260926T102057Z-7097 (r1, a97ef763): 25 books green;
  manifest planning/evidence/manifests/certify-20260926T102136Z-292994.json.
  books/peer-pull took 97.5 s (fold-of-append 38 s, the pending envelope's
  guard 27.5 s): a defect, fixed in c89e587a (named, disabled fold
  predicates; the drain's fixed fields as one term). native-admin 15.0 s and
  native-operator 10.3 s at two jobs: their own events are unchanged by this
  lane (they include peer-carriage-rows / native-admin-peer); recorded, not
  fixed here.
- persvati run-20260926T102921Z-d14e (r2, c89e587a): peer-pull,
  peer-pull-session and both test books green, no book over 10 s; manifest
  planning/evidence/manifests/certify-20260926T102946Z-380804.json.

- persvati run-20260926T103741Z-075c (r3, 2dc81256): native-admin-peer
  (the pull words in the closed `fn-native-admin-pull-rows`), its 17
  dependants and the regenerated docs grammar test book green; manifest
  planning/evidence/manifests/certify-20260926T103810Z-481225.json. Books
  over 10 s at two jobs: native-admin 11.1 s (15.0 s in r1; 9.96 s when it
  landed at f811a7af, and public-exposure changed it since),
  native-operator 10.4 s (10.3 s in r1; its own events unchanged here).
  `make check-lane`'s ratchet refuses native-admin (worst 14.995 s, r1,
  not in baseline). An attempt to close `fn-native-admin-peer-extend-plan`
  for the admin plan theorems (a kind lemma, then disable) broke a
  `:set-peer` theorem in native-admin and was reverted; PKT-431 (5).

## Native (hbox)

Image built by tools/hbox_native.sh at a97ef763
(/tank/fn/scratch/peer-feeds/native-pull1; fn-host-developer sha256
e60dd368..., core 0ac573af...). Its executable definitions are the final
commit's (c89e587a changed proof hints and tests only). hbox_native.sh does
not set FN_NATIVE_HOST, so its own module step skipped-errored (8 errors,
no witness); the module then ran with FN_NATIVE_HOST set
(build/pf-native-manual.sh, systemd-run MemoryMax=24G):
planning/evidence/peer-feeds-2026-09-26/native-peer-pull-run1.log sha256
0e89c1528b4855fc8b1f4d347548df230a52eacea1ed0d06b5d07f534f8c6809: 12 tests,
OK, INN skipped (no FN_INN_SRC).
- test_unavailable_id_is_dropped_at_the_bound: bound 3; `held unavailable=1`
  twice then `advanced unavailable=1 dropped=<ghost-drop@...>`; three
  NEWNEWS naming one instant; three `ARTICLE <ghost>`; each real id stored
  once (B log sha256 cb264c1e...).
- test_unavailable_count_survives_a_cut: after-fsync:2 three ghost
  ARTICLEs in all (the count survived the restart; log eccb8920...),
  before-write:2 four (round 1 not durable; log dd04540f...).
- test_tls_replay_bound_counted_by_the_server (PKT-236 b): the scripted
  peer terminates STARTTLS itself and counts ARTICLE inside TLS; at
  before-write:2 and after-fsync:2 no ARTICLE after the restart, both ids
  stored once (logs 37d81981..., 72507117...): the bound
  `fn-pull-recovery-asks-the-dead-rounds-newnews` /
  `fn-pull-session-journal-is-the-cursor-at-every-cut` imply, observed
  server-side.
- test_loopback_lab_exception_against_an_unprotected_server (PKT-236 c): A
  with `required = true, protected_only = false`; B clear, loopback, profile
  allow-clear: `AUTHINFO USER nodeB` in the clear, no STARTTLS,
  `round=done cursor=advanced transport=clear` (A log e6c0a2d0..., B log
  7e6ee054...).
- The eight PRF-100/PRF-125 cases pass unchanged on the new cursor.

PKT-074: `FN_RUN_HYBRID_E2E=1` on the same image,
test_d23_allowlisted_relay_carries_and_the_enrolled_sink_verifies and
test_d23_unlisted_relay_refuses_439_and_logs_it: both ok;
planning/evidence/peer-feeds-2026-09-26/native-hybrid-d23.log sha256
0fdcc20adbfc7f0e85b1226caf65a589ad88eccd40ae4c5c469c148904aa2676. Retired.

Final gate at 2dc81256 (hbox_native.sh --label final built
fn-host-developer sha256 1dec0e37..., core be4f3b83...; the module then run
with FN_NATIVE_HOST set): planning/evidence/peer-feeds-2026-09-26/native-peer-pull-final.log
sha256 9d010fc144ef1dc46ee13163b62f9db8c724d49c98d100a035411fe3712a90ed:
13 tests, OK, skipped 2 (INN without FN_INN_SRC; the soak without
FN_PULL_SOAK_SECONDS). Every witness kind above repeats on this image
(unavailable-drop: three ARTICLE <ghost>).

Soak: see "Soak" below.

## Not done, and why (PKT-431)

Budget went to PKT-213's proof, its FNPL refinement and the D26 repair.
- PKT-264 (3), MODE STREAM durable refusal and the IHAVE fallback: not
  started; design and default in PKT-431 (1). It changes books/owner-feed's
  limits and owner.lisp, which friends-peer-2 is changing.
- PKT-236 (d), the pull-only credential slot: not started (PKT-431 (2)).
- PKT-207 / PKT-115: not started, not measured (PKT-431 (3)).
- The soak's refuser and withdrawal arms wait on those.

## Soak (SCN-095's bounded form)

"Days" is the claim; 30 minutes is the evidence. On the 2dc81256 image
(fn-host-developer 1dec0e37...), FN_PULL_SOAK_SECONDS=1800,
test_soak_two_nodes_and_an_unproducible_listing: B pulls fn node A and the
scripted peer S (which lists `<ghost-soak>` and answers it 430) every 60 s,
bound 3; A received an article every two minutes (15); B was restarted
cleanly half-way. Result: 60 pull rounds, every article stored at B exactly
once, `<ghost-soak>` dropped exactly once (three ARTICLE <ghost>), B's RSS
360,284 KiB first, 386,432 KiB last and max. Log
planning/evidence/peer-feeds-2026-09-26/native-soak.log sha256
89c6ff547c5fe54ac3007eac6f5c6e92374d656a32031f7a47ee34fe8b456fb9; A's log
e09abb11..., B's log 5783f1dd.... Runbook: on hbox,
`FN_PULL_SOAK_SECONDS=1800 FN_NATIVE_HOST=<developer image>
python3 -m unittest tests.test_native_peer_pull.NativePeerPullTests.test_soak_two_nodes_and_an_unproducible_listing`
under `systemd-run --user --scope -p MemoryMax=24G`
(build/pf-native-manual.sh in the lane). Not in the soak: the MODE STREAM
refuser restarted and the withdrawal (PKT-431 (1), (3)).
