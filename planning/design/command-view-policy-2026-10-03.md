# Every served command's VIEW policy, read from source (DEF-COMMAND, 2026-10-03)

Source revision 4aa332295 (origin/dev). This is the table the brief asked for
first: for each keyword the served dispatcher answers, which view it reads
TODAY, whether it moves the pin / selection / current article, how the
restricted route serves it, and whether the policy is written down anywhere
(NAMED), holds by silence (IMPLICIT: it falls under NNT-042's "other reads
stay on that view"), is decided but not landed (DECIDED), or is open to an
RFC objection (RFC?). Every claim names its line.

## How a view reaches a command (the plumbing, once)

- The connection carries ONE pinned view: `archive` (the pinned articles and
  groups), `index` (its Message-ID trie, buckets, control pin W/WS),
  `verdicts`, `config` (pinned with the read: fn-ocfg-with-read-owner), and
  the catalog view `v` = fn-scr-view-of of the pinned version
  (books/served-catalog-chain.lisp:117-125, 888-900). `env` is built from the
  pinned config + the step's observation (clock) + injection.
- It also carries `live` = the owner's committed view, read by exactly one
  site: the re-pin (books/served.lisp:1196-1218 fn-served-repin; the catalog
  twin served-catalog-chain.lisp:1021-1042).
- The view policy has ONE executable site: fn-served-advance-eventp
  (books/served.lisp:1146-1157) names GROUP and LISTGROUP; fn-served-dispatch
  (:1241-1247) re-pins for those and keeps the re-pin iff the reply is 211
  (fn-served-selectedp :1220-1231). Twins: served-carried.lisp:249-258,
  served-catalog-chain.lisp:1061-1072. Every other command reads the pin by
  falling through. Nothing else states a policy.
- TWO ROUTES (served-catalog-chain.lisp:734-760 fn-scr-auth-delegate):
  unrestricted sessions reach fn-nntp-archive-command-cat (the catalog arms,
  books/served-catalog-dispatch.lisp:46-163); a read-restricted session
  (fn-auth-access-read) is served by fn-scar-peer-step-pinned over the
  PROJECTED pinned archive/index by the REFERENCE walks (fn-pix-archive-
  command-pinned = the hand macro fn-nntp-archive-pinned-arms, books/nntp.lisp;
  fallthrough fn-nntp-archive-command). So every "-cat fast arm" claim holds
  for unrestricted clients only; a policy change must land on both.
- Transit (peer) commands read the LIVE Message-ID index, not the pin:
  fn-scr-history-hasp over lver/arts (served-catalog-chain.lisp:437-469).

## The table

Columns: VIEW today | pin/selection effect | restricted route | quantum |
status | RFC.

| Command (form) | View read today (source) | Effect | Restricted | Quantum | Status |
|---|---|---|---|---|---|
| CAPABILITIES, HELP, QUIT, MODE, POST | no ARTICLE view. CAPABILITIES reads the auth config, subject, TLS, posting configuration, peer context and compression (nntp-auth.lisp:1647-1668); MODE READER and POST's offer are session/env dependent; HELP constant | QUIT closes; POST offers | same | — | NAMED (no article view; c07 correction 2: dependencies named) |
| DATE | DEFECT (c07): the clock observation PINNED AT ACCEPT (served.lisp:172-178: `observation` is the reading pinned at accept, the current reading is the separate `injection` field; nntp-responses.lisp:1068-1074 reads fn-nntp-env-observation), so a long-lived connection answers its connect time (RFC 3977 7.1 wants the current time) | none | same | — | DEFECT, fixed separately; DATE must also be the publication fence for NEWGROUPS/NEWNEWS polling (ruling B) |
| AUTHINFO, STARTTLS, XREDEEM, COMPRESS | auth layer, pinned config | none | same | — | NAMED (no view) |
| IHAVE, CHECK (peer conn) | the LIVE Message-ID index when the node's articles are the catalog's, else the node history (chain:441-448, 530-544 fn-scr-decide-offer); admission checks stay | transit | peer only | — | NAMED by design. TAKETHIS is PHASED (chain:551-558): the offer sets :takethis and begins the article; duplicate/admission decisions belong to the received body's later phases |
| GROUP name | re-pinned to LIVE before the arm; kept iff 211 (served.lisp:1146-1247) | selects group + current = low (fn-served-reselect) | repin then projection | — | NAMED: NNT-042; RFC 3977 6.1.1 |
| LISTGROUP [g [range]] | as GROUP | selects | as GROUP | — (the range is one step) | NAMED: NNT-042; 6.1.2 |
| NEXT, LAST | pinned v (served-catalog.lisp:3369-3384) | moves current | reference walk | — | IMPLICIT (defensible: 6.1.3/6.1.4 act on the selection's numbers) |
| ARTICLE/HEAD/BODY/STAT n | pinned v + pinned W (dispatch:62-68, 96-108) | all four move current on success (fn-nntp-number-retrieval-cat updatep=t, served-catalog.lisp:197-199) | reference | — | NAMED: NNT-042's cancel clause ("visible until a view past it"); ember 2026-10-02 "pinned retrieval preserved" |
| ARTICLE/HEAD/BODY/STAT <msgid> | pinned trie + pinned W (dispatch:69-76, 83-95) | none | reference | — | NAMED as above. RFC? interaction: an article committed after the pin answers 430 "no article with that message-id" (6.2.1) although the node holds it; harmless alone, but any LIVE discovery (NEWNEWS, LIST) will hand out ids the pinned retrieval refuses (Astra section 4, HDR/OVER-by-id row) |
| ARTICLE/HEAD/BODY/STAT (current) | pinned v (dispatch:151-162) | none | reference | — | IMPLICIT |
| OVER/XOVER range | pinned v. TWO arms: the Xref prelude answers it WHOLE when the env names an Xref server (served-catalog.lisp:2921-2928 fn-nntp-over-range-served-cat; the served env always names one), so the CURSOR arm (dispatch:112-118 fn-nntp-over-range-ovw) is unreachable in composition (lane served-catalog-live, fixing) | none | reference (no cursor there) | W=256 numbers/quantum (served-plan-cursor.lisp) once the cursor arm is reachable; one whole step today | IMPLICIT; crossed-view tests exist (NNT-042 7b). Arm ORDER hand-wired: the first example of the thing the generator removes. FINDING E below |
| OVER current / OVER <msgid> | pinned (xref prelude nntp-xref.lisp:484-505, column twins) | none | reference | — | IMPLICIT |
| HDR/XHDR field range/current/msgid; XPAT | pinned v (dispatch:135-140) | none | reference | — | IMPLICIT |
| HDR :fn-verified | pinned verdicts (dispatch:119-122) | none | reference | — | IMPLICIT |
| HDR :fn-control <id> | pinned W/WS of the control pin (dispatch:123-126) | none | reference | — | IMPLICIT (design 2026-09-25 2.5 names the pin) |
| HDR :fn-enrollment | the pin's keyring view (dispatch:127-130) | none | reference | — | IMPLICIT |
| HDR/XHDR Xref; ARTICLE/HEAD Xref | pinned (fn-rcompat-reply-cat, dispatch:82) | as the base command | reference | — | IMPLICIT |
| LIST, LIST ACTIVE [wildmat] | TODAY pinned groups + pinned closed status (served-catalog.lisp:3231-3249 over (fn-state-groups archive)) | none | reference | — | DECIDED (ember 2026-10-02): latest COMPLETED durable view, pin unmoved. NOT LANDED (lane served-catalog-live). RFC 3977 7.6.3 violated today for a group created after the pin |
| LIST COUNTS [wildmat] | TODAY pinned (dispatch:55-61; served-catalog.lisp:1711-1726) | none | reference (buckets) | — | DECIDED with ACTIVE (RFC 6048 2.2.2 same MUST). NOT LANDED |
| LIST NEWSGROUPS [wildmat] | pinned groups x pinned config's descriptions (nntp-responses.lisp:2984-2988, fn-nntp-env-listing) | none | reference | — | IMPLICIT. NO NAMED POLICY (Astra follow-up). RFC 7.6.6 permits omission; a live `describe` is unseen until GROUP |
| LIST ACTIVE.TIMES [wildmat] | creation facts of the pinned config FILTERED to the pinned archive's groups (nntp-reader-compat.lisp:82-104 fn-rcompat-held-env) | none | reference | — | IMPLICIT. RFC? 7.6.4 asks consistency with NEWGROUPS: must take NEWGROUPS' policy, whatever it is |
| LIST SUBSCRIPTIONS | pinned config listing AND the pinned groups (nntp-reader-compat.lisp:221-225 fn-rcompat-subscription-names) | none | reference | — | IMPLICIT; RFC 6048 2.6 no completeness duty; decided D (config at the discovery cut) |
| LIST MOTD | pinned config listing (nntp-responses.lisp:2990) | none | reference | — | IMPLICIT; RFC 6048 2.5 |
| LIST OVERVIEW.FMT | constant (nntp-xref.lisp:478-483) | none | same | — | NAMED (no view) |
| LIST HEADERS / DISTRIB.PATS / DISTRIBUTIONS / other | 503 not stored / 501 variant (fn-nntp-list-unmaintained-response) | none | same | — | NAMED (no view) |
| NEWGROUPS date time [GMT] | creation facts of the pinned config filtered to the pinned archive's groups (nntp-reader-compat.lisp:90-104; reference nntp-responses.lisp:1260-1290) | none | reference | — | IMPLICIT. RFC? 7.3: "newsgroups created since": a group created after the pin is OMITTED until GROUP: the same class as LIST's 7.6.3 defect (a poller that never selects never learns). NO NAMED POLICY |
| NEWNEWS wildmat date time [GMT] | pinned groups AND pinned articles, whole-list walk per call (nntp-responses.lisp:2643-2680 fn-nntp-newnews-scan over (fn-state-articles archive)); fallthrough dispatch:163 | none | reference | NONE today: unbounded work per call (D27); the cursor book books/newnews-cursor.lisp is unwired ("called by nothing served yet"; r67) | IMPLICIT. RFC? 7.4: a DATE/NEWNEWS poll loop on a connection that never selects misses every article committed after its pin; the spec's own DATE->NEWNEWS no-miss target (specs/nntp.md:299-304) cannot hold under a pinned NEWNEWS. NO NAMED POLICY |
| XFNCATCHUP | pinned view + log position (peer-catchup-serve.lisp; table :pinned) | none | pinned arm | batched (1 MiB serve quantum, NNT-053) | NAMED: NNT-053/PRF-325 |
| XFN-ZARTICLE | pinned trie + W (table :pinned arms) | none | pinned arm | — | NAMED: NNT-055 |
| (unrecognized) | none: 500 | none | same | — | NAMED by PRF-194 (HELP table) |

## Findings for ember (the rows that need a ruling or a fix)

A. LIST / LIST ACTIVE / LIST COUNTS: decided (completed durable view, pin
   unmoved); not landed; the restricted route needs it too (chain:734-760).
B. NEWGROUPS and LIST ACTIVE.TIMES: same omission class as LIST (a group
   created after the pin never appears to a non-selecting poller). RFC 7.6.4
   ties ACTIVE.TIMES to NEWGROUPS. Proposed policy: NEWGROUPS and LIST
   ACTIVE.TIMES observe the same completed discovery view as LIST, pin
   unmoved (one "discovery view" policy, three commands + COUNTS).
C. NEWNEWS: pinned today, unbounded per call, cursor unwired. Policy must be
   named with DATE and with by-Message-ID retrieval (a live NEWNEWS hands
   out ids a pinned STAT <id> answers 430 for). Proposed: NEWNEWS reads the
   completed discovery view, quantum-bounded (the fn-nnw cursor), and the
   spec states that a Message-ID it lists may answer 430 on this connection
   until the next GROUP (or: by-id retrieval is served at the completed
   view when the pin lacks the id: a second ruling, not assumed).
D. LIST NEWSGROUPS: name it (pinned config's descriptions, as today, or the
   discovery view). No RFC duty either way; the live-reconfiguration story
   (specs/reconfiguration.md T8b) argues for the discovery view.
E. Exposure/idle (as RULED, c07; my first statement was refuted): the mux
   runs the idle check only with no plan, output, input, await or resume
   (host/native/mux.lisp:1169-1176), so neither idle limit applies mid-reply,
   and `answered` is a latch (public-exposure.lisp:744-751). The real defect:
   `last` is not advanced while a reply drains (cursor and ordinary replies
   alike; fnn-mux-after re-arms the host deadline, :510-512, not ACL2's
   `last`), so a long reply can be idle-closed right after it drains. Fix:
   two events, "command received" and "transport accepted output bytes"; no
   re-arm-on-yield rule.
F. The restricted route: every policy above is "reference walk over the
   projected pin" there, so no cost claim of the -cat arms holds for a
   restricted client, and the LIST/NEWGROUPS/NEWNEWS policies have to be
   implemented twice unless the generator emits both routes from one row.

## Astra's view (consultation c07, gpt-6-astra, read-only at 4aa332295, 761 s; ruling-grade, as requested)

### Liaison fact-check (codex-liaison-11, 2026-10-03)
Checked in source myself (worktree build/lanes/codex-c07-cmdview):
- CONFIRMED, a NEW DEFECT the table missed: DATE answers the clock observation PINNED AT ACCEPT, not the step's clock.
  books/served.lisp:172-178 ("`observation` above is the reading pinned at accept and is the reader environment"; the
  current reading is the separate `injection` field); fn-nntp-date-response reads (fn-nntp-env-observation env)
  (books/nntp-responses.lisp:1068-1074). So on a long-lived connection DATE reports the connect time (RFC 3977 7.1: the
  server's current time). The POLICY table's DATE row ("the step's clock observation") is wrong.
- CONFIRMED E's refutation: the mux runs the idle check only with no plan, no output, no input, no await, no resume
  (host/native/mux.lisp:1169-1176), so neither idle limit applies mid-plan; the exposure entry's progress is
  `(or answered (<= *fn-exp-significant-octets* pending))` and `answered` is a latch (books/public-exposure.lisp:744-751).
  What remains real: `last` is not advanced by response drainage (a long reply can be idle-closed right after it drains).
- CONFIRMED: NNT-042's cancel clause (specs/nntp.md:463-469) has no by-Message-ID exception, which is Astra's ground for
  rejecting completed-only by-id retrieval.
- NOT CHECKED by me: the remaining spot-check corrections (CAPABILITIES' config reads, TAKETHIS phases, LIST
  SUBSCRIPTIONS reading groups, HEAD/BODY n moving current), C4's fan-out count, F and G sections' citations.
Liaison's reading of the rulings: B AGREE (one completed discovery snapshot) but no-miss needs a publication fence and a
fixed DATE; C-NEWNEWS completed snapshot captured once per response, held across quanta; C-by-id DISAGREES with the lean:
pin first, then the completed snapshot, number field 0 on fallback (RFC 3977 6.2.1 permits 0), Xref from the chosen
context; D discovery-cut config (changes NNT-039/T8b); E refuted as stated, replaced by command-receipt and
transport-progress events; F generate both routes, scope -cat cost claims to unrestricted sessions. NEEDS EMBER: no,
unless the coordinator holds to completed-only by-id after round two.

### Astra's answer (verbatim)

# RULINGS

B — RULE: LIST/ACTIVE/COUNTS, NEWGROUPS and ACTIVE.TIMES use a coherent latest completed discovery snapshot, without moving the article pin; DATE polling additionally requires a publication fence. AGREE on the view; DISAGREE that changing the view alone establishes no-miss.

C-NEWNEWS — RULE: NEWNEWS uses one completed discovery snapshot captured for the response, with bounded continuation steps and DATE/publication ordering as specified below. AGREE with completed-view discovery; DISAGREE with documenting GROUP as a prerequisite for fetching its results.

C-by-id — RULE: ARTICLE/HEAD/BODY/STAT/HDR/OVER by Message-ID choose the pinned article if it is retrievable there, otherwise consult one captured completed snapshot; all fields of the answer come from the chosen context, and neither branch moves the connection pin or cursor. DISAGREE with completed-only: it withdraws the pinned retrieval that ember explicitly preserved.

D — RULE: configuration-backed discovery lists use the configuration at their completed discovery cut, under the connection's effective authorization; keep that response context alive independently of the article pin. AGREE with discovery metadata; this deliberately changes NNT-039/T8b's existing pinned-description behavior.

E — REFUTED as stated; rating: BUG in progress accounting, not the claimed demonstrated mid-OVER first-timeout bug. The mux excludes an active plan from idle checks, and a normal numeric OVER follows a successful, answered selection. Reject unconditional idle refresh on cursor emission/yield.

F — RULE: generate both route implementations from the same form declarations, but retain the projected reference route and scope catalog cost claims to unrestricted sessions until a restricted catalog refinement actually exists. AGREE with that honest present scope; DISAGREE that it discharges D27.

Macro — WITH THESE CHANGES: per-form semantic view contracts, composed coverage, explicit pending-policy debt, a two-context reference boundary, meaningful teeth and work bounds; remove the proposed cursor/idle shortcut.

NEEDS EMBER: no, for this round. The recorded preservation of pinned retrieval supports the fallback ruling. If the coordinator still wants completed-only cancellation visibility after two rounds, that is a product-promise disagreement to take to ember; RFC text cannot decide it.

Source coordinate: `4aa332295c85f03f5a97d7b0ac2228f9b95ab1e9`. This is a source consultation, not certification or a native experiment. RFC 6048 **is present**, as `rfc6048.txt`; its claims below are verified from the repository. No builds, ACL2, tests, SSH, commits, or tracked edits were performed. No count/low-water-after-reclaim ruling is made here.

## POLICY spot-check, performed before the rulings

The following checks follow the actual call path, including preludes and fallthrough, rather than treating a callee's name as a view guarantee.

| Row | Result and source evidence |
|---|---|
| GROUP | Confirmed: `books/served.lisp:1156–1157` names only `"GROUP"` and `"LISTGROUP"`; `:1241–1248` dispatches `(fn-served-repin conn)` and retains it iff `fn-served-selectedp`. Catalog twin: `books/served-catalog-chain.lisp:1065–1072`. This is the owner's published view, not speculative catalog top. |
| ARTICLE `<id>` | Pinned view confirmed; **representation wording corrected**. `books/served-catalog.lisp:2124–2128` uses `(fn-scat-msgid-article ... v fn-arena fn-cat)` and the pinned compatibility renderer. The comment at `:2122–2123` explicitly says “the served arms read no Message-ID trie”. The withdrawal arm still depends on the matching index/control context (`books/served-catalog-dispatch.lisp:69–76`). |
| LIST ACTIVE / bare LIST | Confirmed pinned today: `books/served-catalog-dispatch.lisp:144–146` supplies `archive`, closed status, and `v`; `books/served-catalog.lisp:3235–3238` enumerates `(fn-state-groups archive)`. Bare LIST is recognized at `:3224–3229`. |
| LIST COUNTS | Confirmed pinned: `books/served-catalog-dispatch.lisp:55–61` supplies the same `archive`, closed status and `v` to its distinct arm. |
| NEWGROUPS | Confirmed pinned configuration facts filtered by pinned groups: `books/nntp-reader-compat.lisp:82–98` uses `(fn-rcompat-held-env env (fn-state-groups archive))`; `:85` obtains the facts from `env`. |
| NEWNEWS | Confirmed pinned, whole-list scan: `books/served-catalog-dispatch.lisp:163` falls to the archive dispatcher; `books/nntp.lisp:131–132` calls the response; `books/nntp-responses.lisp:2672–2681` passes `(fn-state-articles archive)` to the scan. |
| OVER range | Confirmed pinned and shadowed cursor: the Xref prelude at `books/served-catalog.lisp:2921–2928` answers OVER/XOVER ranges before `books/served-catalog-dispatch.lisp:112–118` can return a cursor. The latter is not today's composed fast response. |
| IHAVE / CHECK | Confirmed live acceptance/history decision, with qualifications: `books/served-catalog-chain.lisp:530–544` calls `fn-scr-decide-offer`; `:441–448` takes the catalog lookup at `lver` only when node articles equal `arts`, otherwise `(fn-peer-history-hasp msgid node)`. “LIVE Message-ID index” must not imply that the fallback or admission checks disappear. |
| LIST NEWSGROUPS | Confirmed pinned groups plus pinned descriptions: `books/nntp-responses.lisp:2984–2987` passes `archive` and `(fn-nntp-listing-descs (fn-nntp-env-listing env))`; `:2901–2903` enumerates archive groups. |

**Every erroneous or materially incomplete cell found in the additional checks:**

1. **DATE is not the step's clock today.** `books/served.lisp:172–178` says the current reading is the separate `injection` field and that `observation` is “the reading pinned at accept and is the reader environment”. Executable evidence: `books/owner.lisp:1838–1847` passes `(fn-own-conn-observation conn)` followed by `(fn-own-clock o)`; `books/served-catalog-chain.lisp:892–900` preserves that distinction, and `:352–355` builds `(fn-post-reader-env config observation)`. `books/nntp-post.lisp:381–392` calls this “the connection's pinned clock observation” and passes it to `fn-nntp-env-full`. Finally, `books/nntp-responses.lisp:1068–1074` takes `(fn-nntp-env-observation env)` for DATE. The POLICY plumbing paragraph and DATE row are wrong, as is the question's assertion that DATE already uses the step clock. Ordinary GROUP also retains that observation (`books/served.lisp:1206–1208`); updating the article pin is not a clock repair.
2. **CAPABILITIES/HELP/QUIT/MODE/POST cannot share a literal “none” dependency contract.** CAPABILITIES reads auth config, subject, TLS, posting configuration, peer context and compression at `books/nntp-auth.lisp:1647–1668`; in particular `(fn-inj-config-allow config)`. Its result depends on versioned configuration/session state. HELP can be constant; POST's offer and MODE READER are environment/session dependent. “No article archive read” is accurate; “no view/configuration dependency” is not.
3. **TAKETHIS is not an immediate history test alongside IHAVE/CHECK.** `books/served-catalog-chain.lisp:551–558` sets `:takethis`, adjusts inflight state and emits `(fn-nntp-begin-article-effect)`. Duplicate/admission decisions for the received body belong to later phases. The aggregate row needs phase-specific dependencies.
4. **LIST SUBSCRIPTIONS also reads pinned group membership.** `books/nntp-reader-compat.lisp:221–225` supplies both configured subscriptions and `(fn-state-groups archive)` to `fn-rcompat-subscription-names`; it is not merely a configuration string list.
5. **Numeric HEAD/BODY also move current on success.** The table's “STAT/ARTICLE n move current” omits them. All four forms call `fn-nntp-number-retrieval-cat` at `books/served-catalog-dispatch.lisp:96–108`, which supplies `updatep=t` (`books/served-catalog.lisp:197–199`); `books/nntp-responses.lisp:119–121` executes `(fn-nntp-set-cursor session group number)`.
6. **OVER range's E annotation is wrong about composed idle behavior.** See E. The pinned view and shadowing cells themselves are correct.

The auth row's “pinned config” is useful, but its simultaneous “NAMED (no view)” must likewise mean no article view, not independence from configuration. No other checked view cell was found wrong. The table is a useful starting inventory, not yet an exhaustive semantic declaration.

## B. One discovery view, and the missing temporal contract

**Recommended specification rule (local policy implementing the RFC obligations):**

> At the start of LIST/ACTIVE/COUNTS, NEWGROUPS or LIST ACTIVE.TIMES, capture one latest completed durable discovery context: archive/group domain, visibility, status, creation facts and configuration from a matching published cut. Answer the whole command from that context, restricted by the connection's effective authorization. Do not change the connection's article pin, selected group or current article. Retain the context until response completion or cancellation. Commands started at different cuts need not return identical information.

Here “start” means the semantic capture/first quantum, not the first socket octet. An admitted command waiting behind a barrier has not captured its response yet. Completed means published after successful durability completion, never the working catalog count.

**RFC basis.** `rfc3977.txt:3879–3892` requires ACTIVE to “include every group that the client is permitted to select with the GROUP command” and says the marks are “as described in the GROUP command”. `rfc6048.txt:330–332` repeats that completeness obligation for COUNTS. Its `:321–323` explicitly says the server need not return “the same results if this command is used more than once in a session”. Bare LIST defaults to ACTIVE (`rfc3977.txt:3720`: “If no keyword is provided, it defaults to ACTIVE.”).

NEWGROUPS returns groups “created on the server since the specified date and time”, with unknown-date/unavailable-group exceptions (`rfc3977.txt:3511–3516`). ACTIVE.TIMES and NEWGROUPS “SHOULD be consistent” with the documented oldest-entry exception (`:3990–3999`). That is a SHOULD, not a MUST of identical answers at different instants. Using the same facts and filtering at the same cut is the clean fn guarantee; mutations between commands remain allowed.

LIST must not refresh retrieval invisibly: `rfc3977.txt:3759–3762` says “the behaviour of subsequent commands MUST NOT be affected by whether the LIST command was issued.” The stronger pinned retrieval guarantee is fn policy; the RFC itself permits changes after GROUP (`:2042–2056`) and inconsistent NEXT/LAST results over a session (`:2336–2338`).

**Completed alone does not solve NEWGROUPS time polling.** Let `T_i` be the server DATE saved before poll `i`, and `D_i` the completed snapshot captured by the subsequent discovery command. That command searches from `T_(i-1)`; after successful completion the client stores `T_i`. For every matching, continuously eligible item not already accounted for, the necessary gap-prevention condition is:

```
item omitted from D_i but becoming discoverable later
    => its effective creation/arrival timestamp >= T_i
```

Equivalently, no future publication may introduce a still-eligible item stamped below the polling watermark already allowed to advance past it. Inclusive comparison, the actual seconds-to-milliseconds conversion, a common monotonic clock, recovery and queued/staged work are part of the condition. Permissions newly granted and objects withdrawn/expired before any poll sees them require separate catch-up/retention policies; a timestamp poll cannot promise their discovery unconditionally.

Counterexample: create/stamp a group at time 100; at DATE=110 the configuration record has not reached the completed discovery cut; poll against that cut and save 110; publication later makes the group visible with creation time 100; next poll from 110 omits it. Physical durability without publication is enough to expose the ordering problem; merely reading a more recent completed root on each call is insufficient.

`rfc3977.txt:3434–3438` requires DATE to use “the same clock as is used for determining article arrival and group creation times” and says that clock “SHOULD be monotonic”. The current DATE path is pinned, as established above. Config records are stamped before completion: `books/owner-config.lisp:345–359` constructs the reconfiguration record using `(fn-ocfg-config-stamp (fn-own-clock o))`. Nothing in those statements proves the required publication ordering.

**Engineering rule to adopt:** make DATE an ordered polling fence without altering the connection's article pin. Before returning current clock value `T`, complete/publish or definitively dispose of previously stamped pending work that could later introduce an item with timestamp `< T`; include both article and configuration publication domains. Subsequently admitted work must not publish a backdated discovery timestamp. Capture the clock and fence order in ACL2; asynchronous waiting must yield. Preserve the original durable timestamps rather than relabeling historical groups to conceal lag. If an indeterminate operation prevents the fence from resolving, recovery/refusal is appropriate; returning a successful misleading watermark is not.

This is feasible as an ordered owner protocol, but **not established in this source**. A-CLOCK alone cannot order durable publication. `books/owner-reader-view.lisp:198–208` explicitly distinguishes the completed prefix C from working `C + A + B`: the reader sees “none of the batch in flight (A) or of the next batch (B)”. Reading working top to avoid waiting is prohibited by the durability contract. A fence may stall behind disk/recovery, and an implementation must prevent old stamped work from bypassing it after restart. A fixed two-minute overlap is not a proof against unbounded lag.

**Watermarks on one connection.** The accepted A decision already permits LIST to advertise numbers beyond an older pin and a newer low mark above numbers that pin can still retrieve. A *new successful GROUP* selects its own later cut; it is not a request to repeat the old GROUP response. For example, P has 1–10, D has withdrawn 1–5: LIST low=6 while ARTICLE 1 at P still succeeds. An arrival can produce LIST high=11 while OVER 1–11 at P omits 11. These do not justify mixing P's status with D's marks or inventing empty summaries for newly discovered groups.

The RFC warns that “The client may make use of the low water mark to remove all remembered information about articles with lower numbers” (`rfc3977.txt:2065–2068`). Thus preserving server retrieval is not preserving the client's opportunity to browse old numbers. The supplied LIST consultation (`build/codex/c07/list-view-2026-10-02.md:154–156`) records Gnus pruning below the active minimum and slrn updating remembered ranges from LIST/GROUP. Those upstream source observations are **UNVERIFIED independently in this consultation**; no fn interoperability failure was reproduced. The RFC warning itself establishes the bookkeeping hazard. I would document: discovery marks describe discovery availability, not the retained numeric snapshot; issue GROUP to browse the discovered current range. Do not claim that every real newsreader behaves correctly across the split.

The separate reclaim ruling chooses how a single snapshot computes counts/low/high. Apply that choice identically to GROUP, ACTIVE, COUNTS and relevant list membership at the same snapshot; the present consultation does not select exact counts versus estimates or count tombstones. Rising low marks after reclaim create the same cross-view issue as withdrawal. Monotonic low-water obligations, including the RFC's empty/all-zero exception (`:2058–2068`), still need proof; “newer view” is not that proof.

**Removal/closing.** Closing posting is not deleting readability: ACTIVE status `n` means “Posting is not permitted” (`rfc3977.txt:3894–3899`). Do not erase such groups from discovery solely for being closed. Today's retirement preserves names, rather than realizing the hypothetical removal: `books/config.lisp:2421–2433` says “The entry, its creation stamp and its watermark stay”; `books/node-config.lisp:85–93` uses all historical names for the domain. A future genuinely unselectable group can disappear from current discovery while a retained old pin still reads it, provided authorization permits that retention. A later GROUP may return 411 and must preserve the old pin/cursor. Ordinary removal also checks selected readers (`books/owner-config.lisp:373–414`); do not describe the hypothetical as today's reachable retirement path.

**Restricted route and authorization.** Discovery must be projected too. Use the connection's effective read authorization, not an unrestricted completed catalog. Current GROUP provisionally refreshes archive fields while retaining `conn-config` (`books/served.lisp:1205–1208`); the configured owner updates its pin after successful repinning (`books/owner-config.lisp:582–595`). This makes authorization generation an explicit concern: do not secretly refresh account rules merely because a LIST fetched newer descriptions. Separate effective authorization from discovery metadata, and prove that the groups discovery promises are selectable under the same effective gate. A decision to revoke existing sessions is a separate authorization transition, not a side effect of discovery.

**Cost / change of mind.** Two retained contexts, publication-fence latency, coherent configuration capture and bounded group/output traversal are real work. Completed can remain below catalog top and still require historical summary correction. I would reconsider the fence implementation if a proved safe publication watermark/arrival-stamp protocol meets exactly the same no-gap condition without waiting; I would not replace completed durability with speculative visibility. Reopening A itself would require ember changing the recorded tradeoff or concrete client evidence warranting that discussion.

## C. NEWNEWS and Message-ID retrieval

### C1. The rules and why completed-only is the wrong default

**NEWNEWS:** capture D as in B, enumerate precisely the matching retrievable articles satisfying the effective timestamp predicate in D, and retain D across all quanta. Do not change P, selection or current. Use the same DATE fence. “230 is complete” means the fully terminated response equals the enumeration of D, not that articles published after capture are appended while it drains.

**By Message-ID:** choose a context once, before rendering. If the article is retrievable in the connection's authorized P, use P. Otherwise look in authorized D. Use that chosen context consistently for ARTICLE, HEAD, BODY, STAT, HDR and OVER: visibility, payload handle, memberships, verdicts, control/enrollment metadata and Xref. This is a semantic availability lookup, not “try a command, and on every 430 retry another one”: unsupported fields, syntax failures and field-level absence are not reasons to change context. Where neither context has a retrievable article, choose diagnostic control/withdrawal metadata coherently (prefer P when P has the identity/history, otherwise D); ordinary retrieval remains unavailable. A historical metadata result is not a payload success.

Apply the same rule to served legacy Message-ID forms and XFN-ZARTICLE so that an alias does not become a conflicting identity-visibility API. Numeric/current forms, ranges, NEXT/LAST and numeric metadata stay at P. Successful GROUP/LISTGROUP retain their existing refresh semantics; the poster's 240/control advance remain separately named boundaries.

The strongest objection to the coordinator's lean is the actual promise. `specs/nntp.md:463–469` says a later cancel “leaves that article visible to the connection until it acquires a view past the cancel.” The supplied decision (`build/codex/c07/list-view-2026-10-02.md:203–206`) says “Pinned article retrieval and cancellation visibility are preserved.” There is no by-ID exception. Completed-only would make ARTICLE `<x>` return 430 while ARTICLE n still serves x on the same connection without a refresh. RFC 3977 does not define fn's snapshot promise, but “no such article exists” (`rfc3977.txt:2622–2623`) is a particularly poor account of an article that this session still retrieves. I reject that pair as fn policy.

The reverse pair is intentional under fallback: a newly discovered x can be fetched by ID before P gives it any number. This is useful to a pulling peer and to a reader following a Reference without selecting another group. `rfc3977.txt:2565–2572` explicitly says by-ID ARTICLE must not alter selection/current, partly to facilitate articles “referenced within another article being read”. It does not require all by-ID operations to use the newest view.

**Returned numbers and Xref.** For completed fallback, return **zero** in ARTICLE/HEAD/BODY/STAT's number field and the standard HDR/OVER leading number. This avoids claiming a number usable in P. `rfc3977.txt:2583–2594` says the server “MUST NOT provide an article number unless use of that number in a second ARTICLE command immediately following this one would return the same article”; zero is always permitted. HDR imports this at `:4690–4696`, OVER at `:4289–4295`. Existing pinned successes can retain their valid local number. None of these by-ID forms updates current.

Xref is a different field: render the server's authorized local memberships from the **chosen** context, not guessed numbers and not a mixture with P. `books/nntp-reader-compat.lisp:244–248` derives it using `(fn-xref-locations (fn-xref-pairs article))`; the catalog compatibility arm uses the chosen article (`books/served-catalog.lisp:2124–2128`). On fallback its Xref numbers are current local locations; the old numeric pin may not yet expose them. State that distinction; a client must GROUP before using a newly discovered numeric range. Returning zero in the status line alone does not cure an Xref leak from unrestricted memberships.

Fallback retains old positives; it is **not** a union archive assembled from both views. Repeated commands can observe later D when P lacks the item, so fallback does not promise that a newly discovered article survives a later cancellation between NEWNEWS and ARTICLE. A NEWNEWS response hold ends when that response drains, not after every listed ID has been fetched. Durable per-poller retention would be a separate, substantially stronger promise.

### C2. Alternatives

| Alternative | RFC/client consequence | Proof/implementation cost and ruling |
|---|---|---|
| (i) NEWNEWS pinned; tell pollers to GROUP | A peer doing the RFC DATE/NEWNEWS algorithm without group selection never discovers post-pin arrivals. Documentation does not repair §7.4's discovery result or §7.5's polling method. A fixed old DATE also does not make the missing articles appear. | Cheapest unchanged dispatcher, but cannot discharge the advertised polling target. Reject. |
| (ii) NEWNEWS and all by-ID reads completed | Fresh polling and simple single-context identity answers, subject to B's time fence. Numeric/by-ID cancellation disagreement breaks the explicit fn promise. Zero returned numbers is necessary where P lacks the article. | New two-context dispatcher boundary, all by-ID metadata/preludes routed to D, holds and DATE work. Least branching among fresh alternatives, but wrong inherited product contract. Reject absent a deliberate owner amendment. |
| (iii) NEWNEWS completed; by-ID pin-first then completed | Fresh peer discovery with immediate by-ID access if the item remains available; old pinned positives survive cancellation. No GROUP prerequisite for a peer. New-ID Xref/numeric caveat is explicit. No RFC requirement forces the completed-only choice. | Same new composed boundary plus availability-selection and zero-number lemmas; at most two indexed identity probes, never a whole union/list rebuild. Choose. |
| (iv) NEWNEWS repins the connection | Would alter subsequent numeric reads and possibly invalidate current despite being an information command. §7's information commands “do not alter any state information” (`rfc3977.txt:3397–3400`); NEWNEWS preserves session today. Reselecting as GROUP plainly changes current; keeping fields while silently changing their referent still breaks fn's promise. | Broadest state/cursor/authorization proof changes and awkward pin lifetime; do not implement a synthetic `:select` without selection. Reject. |

### C3. Exact replacement for the no-miss paragraph

Replace the claim at `specs/nntp.md:299–304` along these lines:

> A successfully terminated 230 block is the complete NEWNEWS enumeration of one captured completed durable discovery view, independent of the connection's article pin. NEWNEWS changes neither that pin nor the selected group/current article. DATE returns a current observation of the same clock used for local arrival and group-creation timestamps, ordered by the publication fence. For successive successful polls using the previous DATE as an inclusive lower bound, a matching article that remains authorized and retrievable until a poll captures it is not lost through pin age or delayed publication, provided every item published after poll i's capture but omitted from it has an effective timestamp at least DATE_i. Clock monotonicity, timestamp units/rounding, fence ordering across staged work and recovery, and a fixed response view are hypotheses of this property. A-CLOCK alone is insufficient. This property remains an open proof/integration target until the host-called path establishes those hypotheses. 501 covers malformed arguments; unsupported wall-clock interpretation remains the documented 503 case.

This distinguishes the RFC polling method (`rfc3977.txt:3633–3654`) from a stronger fn theorem and its retention/authorization assumptions. A client's own clock or article `Date:` header is not the local arrival clock. Current NEWNEWS actually uses durable article stamps and a conservative legacy horizon: `books/nntp-responses.lisp:2580–2591` chooses `stamp` or `horizon` and compares `threshold <= 1000 * instant`; `:2611–2627` advances that horizon and excludes tombstones. Its max-index successor expressly does **not** assume stamp monotonicity (`books/newnews-cursor.lisp:8–10`). A proof about exact scan equivalence under clock rollback is not a proof of no-miss between polls.

Completed versus “LIVE committed” is not a binary cure. In this code, `fn-own-view` is the published reader context; the working catalog may include A/B. If “live committed” means a newer durable but unpublished root, exposing it requires a coherent publication operation first. If it means the same published context, it adds nothing. Even instantaneous committed visibility misses a transaction stamped at 100 that commits after DATE=110 and the first query. Ordering, not the adjective “live”, solves that case.

### C4. The actual theorem boundary and fan-out

The public boundary statement is `books/served-catalog-dispatch.lisp:365–389` (quoted in full, omitting hints only):

```lisp
(defthm fn-nntp-archive-command-cat-is-pinned
  (implies (and (equal (fn-state-articles archive)
                       (fn-cat-view-articles v fn-arena fn-cat))
                (fn-statep archive)
                (fn-gidx-pin-correspondencep index archive)
                (fn-midx-correspondencep (fn-gidx-pin-trie index)
                                         (fn-state-articles archive))
                (fn-cnx-freshp fn-cat)
                (fn-scol-okp fn-arena fn-cat))
           (and (equal (fn-nntp-result-session
                        (fn-nntp-archive-command-cat
                         session archive index verdicts env keyword args v fn-arena fn-cat))
                       (fn-nntp-result-session
                        (fn-nntp-archive-command-pinned
                         session archive index verdicts env keyword args fn-arena)))
                (equal (fn-ovw-expand
                        (fn-nntp-result-effects
                         (fn-nntp-archive-command-cat
                          session archive index verdicts env keyword args v fn-arena fn-cat))
                        fn-arena fn-cat)
                       (fn-ovw-expand
                        (fn-nntp-result-effects
                         (fn-nntp-archive-command-pinned
                          session archive index verdicts env keyword args fn-arena))
                        fn-arena fn-cat)))))
```

It equates session and **expanded** effects to one reference archive. It does not merely assert that current/selection are unchanged. Already decision A makes its old universal statement false for the updated implementation.

A two-view implementation can refine **one reference function**, e.g. a proposed `fn-nntp-command-contexts(session,P,D,authorization,clock,form)`. That function dispatches according to the rules above and selects one response context; it is not the old reference evaluated on an invented single union archive. Its refinement must cover session/connection changes, submission effects, complete expanded response bytes, and holds/continuation validity. Keep the old boundary only for the old subject or for a separately named pinned-form restriction. Do not preserve its name while quietly changing its meaning.

Direct local fan-out, counted from literal statements in `books/served-catalog.lisp`: **11 exported refinement theorems explicitly mention `archive` and cover a by-ID-capable arm**:

| Line | Theorem |
|---|---|
| 205 | `fn-nntp-msgid-retrieval-cat-is-scan` |
| 1906 | `fn-nntp-hdr-command-cat-is-archive` |
| 2141 | `fn-rcompat-retrieval-cat-is-retrieval` |
| 2301 | `fn-rcompat-hdr-cat-is-hdr` |
| 2351 | `fn-rcompat-reply-cat-is-rcompat-reply` |
| 2630 | `fn-nntp-verdict-hdr-msgid-cat-is-archive` |
| 2659 | `fn-nntp-verdict-hdr-response-cat-is-archive` |
| 2898 | `fn-nntp-over-msgid-served-cat-is-col` |
| 2943 | `fn-nntp-xref-reply-cat-is-col` |
| 3078 | `fn-nntp-control-hdr-response-cat-is-pinned` |
| 3109 | `fn-nntp-enrollment-hdr-response-cat-is-pinned` |

That count is a defined local interface inventory, **not a total transitive theorem rebuild count**. Add the view-list kernel `fn-scat-msgid-article-is-find-article` at `:118` and index-only withdrawal theorem `fn-nntp-msgid-withdrawn-p-cat-is-trie` at `:2980`, which do not have the formal `archive`; add the local expanded dispatcher lemma and public boundary at `books/served-catalog-dispatch.lisp:287,365`. Many of the 11 can remain unchanged and be instantiated at the chosen context; only the context selection and composed routing must acquire new statements. Do not manufacture a twin of every helper.

For example, `:205–209` says `(equal (fn-state-articles archive) (fn-cat-view-articles v ...))` implies the catalog result equals `(fn-nntp-msgid-retrieval session archive kind token fn-arena)`. That is reusable for P or D. The new fact is **which** of those archive instances the actual call uses.

Composition must then reach `fn-scr-command-is-command-pinned` (`books/served-catalog-chain.lisp:259–272`), auth/restricted dispatch (`:765,823`), dispatch (`:1074`), and `fn-scr-ocfg-read-span-is-reference-under-ocl-relation` (`:2565–2573`), whose conclusion currently compares the served span with `fn-ocfg-read-tls-prefix`. At the owner layer, `fn-own-read-is-served-step-on-pinned-prefix` (`books/owner-invariants-served.lisp:175–202`) constructs a historical replay archive **and** supplies `(fn-own-view-live (fn-own-view o))`. Its name should not be mistaken for a ban on extra context; its reference step needs the new contract. `fn-own-read-repinned` is a returned flag (`books/owner.lisp:1933–1935`), and `books/owner-invariants-outcome.lisp:273–279` makes historical fields move when that flag is true. Discovery/fallback must leave it false; consuming D is not connection repinning.

### C5. Holds, reclaim, and bounded NEWNEWS

There **already is** a response hold. `host/native/owner.lisp:483–488` says “Hold ACL2's arena-reader generation for CID's response” before returning the plan. At `:4545–4549`: “Reclaim's swap excludes every live arena reader, including this pin while a later cursor quantum still uses the original catalog”, followed by `(fnn-owner-response-pin service cid)`. `books/response-plan-pins.lisp:1–7` states one hold spans even several pipelined cursor replies; `:35–45` acquires/releases the arena generation. `host/native/mux.lisp:502–505` releases only after “All windows, including a partial socket write's pending suffix, have drained.”

Thus “by-ID needs its own hold” is correct as a **response ownership requirement**, not as a claim that the host has no holder or necessarily needs a second generation counter. The existing response-generation hold can cover P and D handles in the same captured arena generation. Extend/prove the capture invariant to bind D's version, config, metadata and cursor roots too. An article pin alone is not that binding: its reclaim floor does not describe all newer objects used by a fallback. Logical snapshot lifetime, physical generation exclusion and retained disk extents are separate obligations. If reclamation is later made concurrent with held generations, preserve every captured root through the new protocol rather than relying on today's coarse swap exclusion.

NEWNEWS is unbounded today. The scan recursively visits the whole list and accumulates output (`books/nntp-responses.lisp:2596–2608`); changing the view does not bound work. `books/newnews-cursor.lisp:27–41` defines the residual cursor and run/scan equality, but `:42` says “fn-nnw-response is called by nothing served yet.” Bind it to one D at capture, never advance its source between quanta. Its carried `TAIL/MAXES/HORIZON` must belong to that D and remain retained. Changing the source could skip/repeat IDs and invalidate the residual equality.

An article-count quantum alone is not an allocation or time bound if per-article group matching, metadata access or output is unbounded; account for those dimensions and the configured representation. Index maintenance/rebuild, group-wildmat setup and response rendering also need bounded steps. The cursor is promising reference machinery, not a served D27 completion claim.

**Cost / change of mind.** Fallback costs a second keyed lookup on misses, one explicit selection predicate and a broader response-context theorem; it avoids union materialization and preserves a paid-for pin. I would choose completed-only if ember explicitly changes cancellation visibility, or a concrete proof/resource problem makes preserving it untenable and the coordinator agrees to propose that product change. I would change the DATE mechanism upon a proved cheaper ordering protocol, not on an unbounded overlap heuristic.

## D. Configuration-backed LIST variants

Use D's configuration for NEWSGROUPS, SUBSCRIPTIONS, MOTD and ACTIVE.TIMES creation facts, with the effective authorization distinction in B. Keep configured subscription order and filter against D's allowed groups. For constants such as OVERVIEW.FMT, declare the actual session/config prerequisites separately from the constant body.

This is a **local product-policy recommendation**, not something RFC 3977 forces. NEWSGROUPS “MAY omit newsgroups for which the information is unavailable” and clients must not assume it matches ACTIVE (`rfc3977.txt:4062–4065`). SUBSCRIPTIONS is “a list of recommended newsgroups”; its order is significant and it “SHOULD contain only newsgroups the news server carries” (`rfc6048.txt:796–810`). MOTD may differ across calls/session state (`:706–711`). Those allow fresh metadata; they do not compel it.

The reason to choose it is the operator workflow and uniform discovery semantics. NNT-039 says live configuration publishes descriptions, but explicitly pins what an existing reader sees (`specs/nntp.md:191–198,226–228`: “a connection opened before group describe keeps the text it opened with”). T8b says existing connections “retain their archives and pinned configuration” and the current archive/configuration describe “the same historical cut” (`specs/reconfiguration.md:1373–1392`). These are real existing guarantees to amend, not permission to pair a fresh group table with arbitrary latest strings.

`fn-ocfg-with-read-owner` does **not** implement a general “pin every read's config” operation. `books/owner-config.lisp:591–593` changes the persistent config pin only `if repinned`; otherwise it keeps `(fn-ocfg-pins oc)`. A discovery read therefore needs an independently retained D/config response context, but not a move of that persistent pin. Immutable shared roots may make the extra hold cheap; “one additional context” need not mean copying configuration for each command. A flat formal containing an opaque context is acceptable only with an invariant proving its fields describe the same cut.

**Cost / change of mind.** Revise NNT-039's pinned-listing theorems and their owner consumers, hold the D configuration/root, and cover authorization changes between capture and drain. I would retain pinned metadata if ember explicitly needs historical MOTD/description browsing alongside an old article snapshot. Neither RFC nor the recorded workflow supplies that preference; fresh discovery is the more useful default.

## E. Exposure and idle: confirmed mechanism, refuted scenario

The scan omission is real. `books/public-exposure-reply.lisp:129–135` accepts only an effect with `(equal (car effect) :reply)`. At `:149–155`, answered becomes `(or answered (consp octets))`. At `:207–211`, the host-called observer uses those facts. A cursor-only result is exactly that: `books/served-catalog.lisp:850–856` emits a cursor effect instead of a reply, with the status line “unsent” at `:858–860`. It has no ordinary reply octet yet.

Two qualifications refute the stronger finding:

1. Progress is `(or answered (<= *fn-exp-significant-octets* pending))`, not answered alone (`books/public-exposure.lisp:744–751`); the input threshold is 512 (`:106`). The `answered` latch is `(or (fn-exp-entry-answered e) answered)`. Cursor emission does **not clear** an earlier answer. A successful GROUP/LISTGROUP already produced 211; the normal numeric OVER session therefore uses the longer limit. With no selected group the cursor arm returns a regular 412, not a cursor (`books/served-catalog.lisp:848–856`).
2. The actual mux calls idle only when output, plan, input, await and resume are all absent (`host/native/mux.lisp:1169–1176`), including the decisive `(null (fnn-mux-conn-plan conn))`. It does not apply either idle limit mid-plan. `fnn-mux-plan-yield` indeed does not re-arm idle (`:403–419`), but the omitted call is not proof of mid-reply closure. `fnn-mux-after` re-arms the *host check deadline* (`:510–512`), not ACL2's `last` timestamp. Confusing those two clocks would produce an ineffective fix.

**Rating:** progress-accounting **bug** when a cursor response produces useful output without an observation updating `last`; the stated first-seconds/mid-OVER failure is refuted in this composition. This is more than a nit, but the claimed interleaving is not evidence. Cursor reachability is currently blocked by the Xref prelude (`books/served-catalog.lisp:2921–2928`); that makes the particular cursor omission latent on this served OVER path. Reachability repair alone will not turn the claimed mid-plan idle branch into a reachable one.

The broader “time spent draining is not reflected in core last” problem is not uniquely latent behind the cursor: an ordinary materialized reply that takes longer than the idle interval can also finish with a stale dispatch-time timestamp. Its initial `:reply` sets the answered latch, but final host re-arming still does not update core last. The same progress-event repair should cover both representations.

**Concrete replacement interleaving.** Public defaults are first=60 seconds and idle=600 (`books/profile-limits.lisp:67–70`); cursor quantum=256 numbers and resume delay=1 ms (`books/served-plan-cursor.lisp:114–131`). Suppose GROUP at t=0 records an answer. A future reachable cursor handles 256,000 numbers in 1,000 quanta; under an illustrative loaded schedule taking 0.7 seconds per quantum, it finishes at t≈700 seconds. It is **not** idle-closed at t=60 or t=600 while a plan exists. If no later exposure observation updates `last`, the first idle check after final drain can close it around t=701 because last remains near GROUP. The schedule is a constructed example, not a performance measurement. There is no elapsed-time upper bound from “256 numbers”: even ideal 1 ms yields over the full 2^31−1 numeric span require about 8,388.6 seconds for 8,388,608 quanta, before computation or socket delay, if that whole span is scanned. Scheduling and I/O can add more.

**Reject the proposed repair as the semantic rule.** RFC 3977's actual autologout rule is about receiving a command/significant input: `rfc3977.txt:383–388`, “The receipt of any command from the client during the timer interval SHOULD suffice to reset the autologout timer.” Fn should record receipt of a complete command separately from whether its renderer emitted a `:reply`; the first-command latch should not be called “sent an octet” if it means command accepted for processing.

During response drainage, wire progress must mean positive transport acceptance of outgoing bytes, not constructing a plan or running an empty cursor quantum. Pass host-observed positive-write facts to an ACL2 progress transition; renew the applicable drain/stall timer there. Keep computation/scheduling progress separate, since a sparse scan can legitimately produce no octets while the peer is waiting for the server. A yield may schedule the next check; it must not manufacture client activity. Retain finite resource accounting, cancellation, and a response owner until all output is drained or abandoned.

“Accepted by the peer” is an operational objective, not a fact the current write API proves: a positive socket/TLS write means the local transport accepted bytes; it is not NNTP application acknowledgement. Bounded buffering plus lack-of-write-progress/stall timeouts is the observable enforcement mechanism here. Do not introduce a false remote-acceptance theorem.

**Can a never-reading client hold forever?** Not by the proposed mux re-arm alone in today's code: pending output has a separate 10-second window deadline (`host/native/mux.lisp:57,388,466`), checked before the idle branch at `:1142–1149`. Once bounded transport buffers fill, a queued window times out. Empty yields do not prove peer progress, however, and may hold resources for a long server computation. A slow client draining each window within the deadline can retain a response for a long time; activity is not idleness. A fixed finite snapshot and decreasing residual prevent an infinite enumeration in the logical model, while resource budgets/fairness govern actual service. Never disable the write deadline on the grounds that cursor work is “answered”.

**Cost / change of mind.** This needs explicit command-receipt and transport-progress events, matching exposure proofs, and a native long/sparse reply witness—not a change to every command row's semantics. A demonstrated path invoking `fn-exp-idle` during an active plan could change the mid-reply finding; the cited mux path does the opposite. The current output scan can remain a correct 481 detector without being the authority for transport progress.

## F. Restricted versus unrestricted execution

**Honest now:** keep the reference route and declare catalog performance scope unrestricted. One table should generate the policy/dispatch obligations for both, with route-specific implementations and evidence. Never give a reference route a catalog cost label because its sibling row has a `:cat-by` lemma.

The route is explicit: `books/served-catalog-chain.lisp:741–756` branches on `(fn-auth-access-read as config)` and invokes `fn-scar-peer-step-pinned` or `fn-scar-auth-delegate-pinned`; only `:757–760` uses `fn-scr-peer-step ... v fn-arena fn-cat`. The comment says “the rule's view of the archive, by the reference walks”. The access projection may be cached (`:742–745`); that does not make command walks bounded or catalog-indexed. F's phrase “every command” should be restricted to archive-reading delegation: session/auth commands and transit decisions have their own layers.

**Target:** a catalog implementation of the authorized projection, proved equivalent to the reference route for each form, including bytes/effects/state, errors, selection, withdrawn metadata, counts and Xref. Projection-then-catalog is **not** generally equal to unrestricted catalog-then-filtering completed output. `books/group-access.lisp:224–229` explicitly cuts both article groups and memberships:

```lisp
(fn-gac-filter-groups text (fn-article-groups a))
(fn-gac-filter-pairs text (fn-article-memberships a))
```

`books/group-access.lisp:290–297` rebuilds the trie/buckets and restricts withdrawn articles too. A crosspost into readable A and forbidden B must remain fetchable with B removed from the generated membership/Xref projection; deleting whole response lines cannot both retain A and redact B. Aggregate counts, wildmat enumeration, local-number lookup and refusal causes also need projection-aware operations. A carried authorized view/index or proved restriction-aware catalog reads are valid approaches; a global catalog with an output filter is not a theorem.

No catalog/projection commutation theorem was found in the inspected group-access books; **a claim that the current global catalog arms already refine restricted projection is UNVERIFIED**. The existing projection theorem (`books/group-access.lisp:579`, `fn-gac-restrict-state-is-a-projection`) establishes the model's projection property, not that stronger catalog equation.

**Yes, this remains a D27 violation on a served path.** Reference whole-archive walks/materialized replies are unbounded per step, even if cached projection construction avoids repeating some work. `planning/decisions.md:1194–1208` says “a served command still does bounded work” and the executable path uses concrete representations. Narrowing a performance claim is necessary truthfulness, not implementation completion. Even unrestricted LISTGROUP/LIST/current whole replies have separate output/work debt. Bound reference continuations as an intermediate fix if necessary; target both routes without arbitrary data ceilings.

**Cost / change of mind.** Restricted cursor/index maintenance and projection refinement cost more than copying an arm. I would switch a restricted row to catalog execution once its semantic correspondence, reachable teeth, guards and matched restricted measurements exist. A certificate for unrestricted bytes, or a theorem about a noncalled restricted twin, would not change the ruling.

## G1. Fail-open closure: HELP is hand-written, but already has a theorem

The proposed set-equality assertion alone is insufficient, but the critique must acknowledge existing work. HELP's table is the literal `defconst` at `books/nntp-help.lisp:52–59`; it is not mechanically extracted from executable dispatch. However, the book proves more than table rendering: `fn-auth-step-pinned-answers-500-to-a-keyword-help-does-not-list` (`:216–242`) states that under its command-mode hypotheses an unlisted keyword yields exactly `(fn-auth-single as "500 command not recognized")`, no submission and unchanged session. Its hypotheses exclude TLS/SASL exchange, transit/post body mode, malformed/excess arguments and closed sessions, and include selection-in-view. This is a semantic closure result, not just two hand lists agreeing. Its converse is explicitly “NOT PROVED” at `:33–36`.

Retain that theorem and lift closure to the **actual host-called composed subject** through both routes. Generate HELP and command tables from the declarations, but also inventory every reachable keyword test in reader/archive preludes, auth/SASL/TLS, transit/MODE, extension dispatch and body-mode transitions. Require each recognized form/phase to map to a row, every row to a reachable supported/refusal behavior, and unrecognized/syntax paths to their own total cases. AST/lint coverage is useful to catch an extra hand branch in neither table; the composed theorem is the semantic backstop. Keyword search must distinguish command keywords from LIST variants/field names and from arbitrary response text.

Also close the schema's own loophole: requiring `:view` only on rows with `:arms` omits auth handlers. The AUTHINFO row at `books/protocol-table.lisp:1114–1140` has `:dispatch :auth` and `:model (fn-auth-authinfo)` but no `:arms`. Every served layer/form needs a dependency/effect declaration, whether its implementation is generated or an explicitly registered external handler.

Cost: an explicit reachability/coverage map and composed proof rather than a set assertion. I would accept a narrower assertion only if all command recognition is generated structurally and no reachable hand dispatcher can recognize an undeclared form; that is not this sketch's staged migration.

## G2. A decided view is debt, never the displayed executed rule

Generate **executed view** as the current rule, then a distinct pending decision/registry ID. `:view-decided :completed` must automatically require an open registry item with form, route, source/evidence coordinates and completion criterion. It cannot satisfy a `:view` proof or count as policy implemented. A count is useful; a nonincreasing ratchet prevents growth; neither causes old debt to finish. Required release claims must refuse unresolved decided policy, with an explicit project-scoped exception only if the release contract actually allows it.

Existing source demonstrates why: `specs/nntp.md:467` says “Other reads remain on that view”, while the supplied A decision is explicitly not landed. A generated normative-looking “DECIDED completed” cell would hide this exact distinction.

Cost: tracked debt and release/check integration, not an approval ceremony. Change my mind only for a schema that already enforces the same executed/pending separation and fail-closed completion condition. Do not invent an expiring calendar deadline as a substitute for the engineering criterion.

## G3. Syntactic formal checks do not prove a view

The proposed forbidden-name tests are lints. The existing catalog has all versions in one stobj: `books/served-catalog-chain.lisp:892` computes `v` from the pinned version, and `books/served-catalog.lisp:2124` passes that index to `fn-scat-msgid-article`. Substituting catalog count for v violates the declared pin without naming a completed formal. A helper/env/session/global/stobj can hide the same dependency. Conversely, mentioning D in dead code proves nothing about a `:completed` arm.

Generate a semantic projection/noninterference contract per form, with state/effect scope:

* `:pinned`: under representation invariants, the observable result equals the reference on P; changing unrelated D/other catalog versions with P's projection fixed leaves it unchanged.
* `:completed`: the archive/metadata result equals the reference on captured D; P's contents are irrelevant except explicitly permitted session metadata (e.g. selection or returned-number compatibility). P itself remains unchanged.
* proposed `:pin-or-completed`: context choice is exactly retrievable-in-P, else D, followed by one-context rendering; prove both branches, including negative selection premises.
* `:select`: pre-execution context is D; 211 installs the selected D with normal current effects, and failure preserves old P/selection/current.
* `:live-index`: specify the actual live-history/admission projection, including node-history fallback and inflight inputs, rather than pretending every transit phase is one lookup.
* `:none`: independent of archive projections; declare allowed clock/config/auth/session dependencies separately. DATE needs a clock/fence contract, not a false constant contract.

Cost: per-form boundary lemmas plus reusable context abstractions, not one theorem for every helper. I would remove individual lints once structural context capabilities and semantic proofs subsume them; I would never treat the lints themselves as policy evidence.

## G4. A keyword row is not a protocol form

Keep one top-level row per keyword, with nested **forms/arms** carrying view, argument predicate, effect, route and phase. ARTICLE number/ID/current differ; LIST ACTIVE versus OVERVIEW.FMT versus NEWSGROUPS differ; HDR field/range/ID and fn metadata differ. HELP can still expose one keyword. It is not the grammar, view policy or reachability inventory.

Source already has heterogeneous LIST clauses (`books/protocol-table.lisp:870–880`: Xref prelude, COUNTS, compatibility, then fallback), and the dispatcher separates numeric and ID retrieval (`books/served-catalog-dispatch.lisp:83–108`). A uniform keyword-level view cannot represent the selected policy. Argument errors need explicit total fallbacks. Effect declarations also need conditions: `:current` on successful numeric HEAD/BODY as well as ARTICLE/STAT; none on by-ID, failure and current-only retrieval. Auth/TLS/COMPRESS are state effects, not adequately described by the sketch's five-value effect enum.

Cost: a nested form schema and coverage checks. A keyword default inherited by every form is fine when semantically uniform; I would not require duplicate annotations for genuine uniformity.

## G5. Case splits and the statement that cannot be preserved

Different command names can be exclusive; different arms for one keyword are not. The Xref prelude already proves why ordering matters. Arbitrary `:cat-arms ((TEST TERM) ...)` must either be structurally wrapped in their keyword guard or prove that their tests cannot steal other rows. Within a row, prove first-match semantics/priority and coverage over argument shapes, not just tests on a few syntactically valid strings.

`books/protocol-dispatch.lisp:129–147` already includes **row-none** and **row-syntax** lemmas; its final split includes syntax and every name (`:150–159`). Copy those obligations. A lemma under `(fn-nntp-keywordp keyword "NAME")` can cover all that keyword's arguments if actually proved universally, but it does not cover unknown names, malformed keyword tokens, or an insufficiently guarded neighboring row. Default success/refusal behavior must be part of the generated total dispatcher.

The sketch's “NAME and STATEMENT preserved: every ledger citation stays” is impossible once A or C changes semantics. See C4's quoted equation. Replace it with the two-context reference refinement; retain a separately named pinned-only specialization where true. The equality `P=D` specialization is useful, not a replacement for the general new contract.

Registry impact, read from the JSON: the old theorem is an **event citation** in PRF-202 (`planning/proofs.json:7354`) and PRF-346 (`:12349`), and occurs in prose for PRF-332 (`:12456`), PRF-367 (`:13233`), PRF-1020 (`:17779`) and PRF-1229 (`:21383`). Update every affected statement/event/teeth/scope and recertify the changed reachable subjects; stable IDs preserve obligation identity, not obsolete theorem claims. These rows are `uncertified-at-current-digest` except PRF-1229 `planned` at this source. No green evidence transfers to altered bytes.

Cost: a deliberate boundary/spec/registry change with composed fan-out. I would preserve the old universal statement only for a refactor with literally unchanged policy, before the policy switch; preserving a theorem name is not an engineering goal.

## G6. Migration, subject rule, teeth and quantum

Building beside the hand dispatcher is a reasonable intermediate step. Before the switch, the actual subject remains `fn-nntp-archive-command-cat`, called by `fn-scr-command` (`books/served-catalog-chain.lisp:249–257`). Generated equality lemmas establish that a replacement is ready; they do not establish that production uses it. After the switch, record the actual generated caller chain and delete the superseded **implementation** once all forms/routes are covered. Keep the intentional logical reference. The sketch's “three rows ... then the switch ... then every remaining row” must mean the remaining forms have explicit proved delegation, or else the switch waits: do not drop unconverted behavior or leave an unrecorded second policy source.

Command strings in `:teeth` are test inputs, not AGENTS.md teeth by themselves. A positive witness must assert the entire antecedent and conclusion of each literal theorem, reach the composed route and the claimed form. Hypothesis-removal witnesses must affirm all retained hypotheses, fail the removed hypothesis and fail the conclusion; corruption/mutation witnesses need separate labels. A registry/table entry saying “owed” detects absence only if the checker examines actual obligations, not a nonempty list of strings. Redundant hypotheses are removed by proving the weakened theorem, not by lacking a counterexample.

Likewise, “:quantum checked by teeth, not syntax” can validate examples but cannot prove a bound. Require a decreasing residual, exact residual output/effects equation, representation/guard preservation, and a bound on work/allocation in the cost coordinates actually charged. Prove a cursor arm reachable in composition. `books/newnews-cursor.lisp:30–41` supplies useful run/scan and residual obligations; its uncalled status at `:42` prevents a served claim. `books/served-plan-cursor.lisp:46–50` explicitly ties existing cursor V to the connection pin; D cursors require extending that premise and its holder proof.

Cost: a short-lived, explicitly scoped equality bridge, then one implementation source; substantial proof work remains hand-written in reusable readers. I would change the conversion order when sibling integration changes the live subject, not keep an obsolete twin merely to preserve old names.

## G7. Missing forms, routes, lifetimes and connection-level laws

Add the following to the generated inventory and contracts, not necessarily as more top-level keywords:

The literal HELP table has **31 distinct keywords**, counted from `books/nntp-help.lisp:52–59`; POLICY's grouped rows account for all 31. The omissions identified here are chiefly forms, phases, dependencies and consumers, not a demonstrated 32nd top-level verb. The older comment's “29 keywords” (`nntp-help.lisp:36`) is stale.

* **MODE READER versus MODE STREAM**, including session/permission effects; `books/nntp.lisp:79` delegates MODE, while the peer STREAM branch is `books/served-catalog-chain.lisp:559–562`.
* **CAPABILITIES by auth/TLS/compression/peer state**, not a constant none-view row; the actual auth arm is quoted in the spot-check. Its advertised OVER MSGID and LIST variants must match supported forms. RFC 3977 §7.6.2 even makes LIST HEADERS mandatory when HDR is advertised (`rfc3977.txt:3852–3853`); distinguishing “recognized but unmaintained” 503 from “unrecognized” 501 requires capability/form consistency, not just HELP coverage. This consultation does not claim to complete a separate capability-conformance audit.
* **Bare LIST, all supported/rejected variants and extra-argument errors**. RFC §7.6.1 explicitly distinguishes unavailable information 503 and unrecognized keyword/unexpected argument 501 (`rfc3977.txt:3745–3748`). DISTRIB.PATS has no argument (`:4039–4040`).
* **XOVER versus OVER** (including optional standard by-ID support), **XHDR/XPAT grammar**, and **HDR's field plus range/current/Message-ID forms**. “HDR ranges with msgid” is not one range form; the second argument is classified. Standard zero-number semantics and legacy wire spellings must remain deliberate.
* **Numeric/current/ID ARTICLE/HEAD/BODY/STAT**, withdrawal checks before ordinary retrieval, compatibility/Xref preludes, and fn metadata. Local-number effect and diagnostic visibility are not captured by a keyword's `:view` alone.
* **POST offer, received body, duplicate check, durable completion**, IHAVE offer/body and CHECK/TAKETHIS phases. Duplicate acceptance is live-history/admission work, not reader-pin availability; `specs/lifecycle.md:73–77` distinguishes accepted, duplicate retry and indexed read. The same held/reclaimed ID can correctly be unavailable for reader retrieval yet remain a duplicate for intake. The offer alone does not decide durable acceptance or repin the poster.
* **AUTHINFO-dependent access/advertisement, SASL continuation, STARTTLS and COMPRESS boundary handling**, XREDEEM, XFNCATCHUP and XFN-ZARTICLE. The existing HELP theorem excludes body/handshake modes for a reason. Closure cannot stop at archive dispatch. XFNCATCHUP's log cursor is a different typed coordinate from an NNTP timestamp or selected article number.
* **The response-plan context and physical lifetime**: session P, response D (or chosen by-ID context), effective auth, config generation, arena generation, residual position and owed status/terminator. Multiple pipelined responses can share a physical generation hold while carrying different semantic snapshots. Do not collapse their views into a connection-wide mutable `v`.

**Other hosts are consumers of the same machinery, with additional cost obligations.** `host/native/web-host.lisp:13–22` calls a browser session a “LOGICAL READER CONNECTION” and says it is fed through `fnn-owner-handle-chunk`. Executable calls at `:110–125` use that handler, `fnn-owner-render-next-quantum`, and response-unpin. `host/native/pull-service.lisp:269–293` likewise calls the handler for its local logical connection and drains/unpins quanta. Thus core view-policy changes reach those local routes; they are not independent implementations needing a different view rule. Remote peer discovery in a pull round is, of course, governed by the remote server; no local theorem proves that server's behavior.

However both local wrappers concatenate the entire reply (`web-host.lisp:120`, `pull-service.lisp:288`: `(setq reply (concatenate 'fnn-octets reply ...))`). A mux cursor proof does not establish bounded end-to-end memory for these consumers. Register that scope/work debt and carry cancellation/holder behavior through their paths. Do not claim every consumer streams merely because the dispatcher can emit a cursor.

Finally generate/test **laws between commands**, not only row equality:

1. Successful GROUP/LISTGROUP captures P and normal current; failures leave them unchanged. NEXT/LAST and numeric/current reads remain functions of that P.
2. LIST-family discovery, NEWGROUPS and NEWNEWS do not move P or current. Later discovery may see a newer cut; it is not a numeric-snapshot refresh.
3. Existing retrievable IDs in P remain retrievable through both ID and number forms until an authorized refresh; completed fallback for an absent ID reports zero and leaves current untouched.
4. NEWNEWS followed by by-ID can retrieve a still-available listed article without GROUP; cancellation/expiry between commands is an explicit limit, not pin-age refusal.
5. Every individual multi-quantum answer keeps one chosen context and a valid hold, even as the owner advances; all routes apply the same authorization projection.
6. DATE/poll watermark advancement obeys B/C's no-gap condition, independent of old article pins and in-flight preparation.

Cost: composed scenarios and consumer-specific claims beyond the macro's row generator. I would remove an item only when source establishes it unreachable/unsupported and capability/spec/registry all agree. The consultation's useful destination is one semantic source of truth with honest route and phase boundaries, not a larger hand-written table that happens to generate documentation.

## Delivery scope

Only this scratch `ANSWER.md` was written. Source inspection and small stdlib inventory/counting snippets supplied the findings; no executable behavior or proof certification was claimed. Registries and generated current-view files remain untouched as the brief requires. Implementation work remains for the accepted discovery policy, DATE/publication ordering, by-ID fallback, bounded execution on both routes, cursor reachability/progress accounting, and the revised macro/boundary. The sibling reclaim-summary decision remains separate.

## DECISION (coordinator + Astra agreed, 2026-10-03; ember not needed, may overturn)
- B: one completed DISCOVERY snapshot for LIST / LIST ACTIVE / LIST COUNTS / NEWGROUPS / LIST ACTIVE.TIMES,
  captured once per response, pin unmoved; no-miss additionally needs a publication fence ordered against DATE.
- C, NEWNEWS: reads the completed view; ONE snapshot captured at its first quantum, held across quanta.
  specs/nntp.md:299-304 replaced per Astra's section C3; no "GROUP first" prerequisite.
- C, by-Message-ID retrieval: Astra's ruling adopted (the coordinator's completed-only lean withdrawn):
  PIN FIRST, then the completed snapshot. Reason: completed-only breaks NNT-042's cancel clause, and would
  make ARTICLE <x> answer 430 while ARTICLE n still serves x on the same connection. On fallback, number
  fields are 0 (RFC 3977 6.2.1) and Xref comes from the chosen context; neither branch moves the pin or the
  current article.
- D: config-backed LIST variants read config at the discovery cut (deliberately changes NNT-039/T8b).
- DATE (new defect): DATE must read the CURRENT clock observation, not the reading pinned at accept
  (books/served.lisp:172-178; nntp-responses.lisp:1068-1074; RFC 3977 7.1).
- E: the defect is that `last` is not advanced while a reply drains (cursor and ordinary replies alike), so a
  long reply can be idle-closed just after it drains. Fix with two events, "command received" and "transport
  accepted output bytes"; no re-arm-on-yield rule.
- F: both routes generated from one form declaration; restricted sessions keep the reference route; -cat cost
  claims are scoped to unrestricted sessions until a restricted catalog refinement exists (D27 not discharged).
- Macro: build with Astra's changes (:view per FORM; a semantic contract per view value; :view-decided is
  counted debt and the spec shows the executed rule; composed coverage, not the HELP set; a two-context
  boundary theorem replaces fn-nntp-archive-command-cat-is-pinned once an arm reads a second context).
