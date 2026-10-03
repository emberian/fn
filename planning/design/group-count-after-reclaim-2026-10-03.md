# Decision: do GROUP / LIST / LISTGROUP count reclaimed articles? (2026-10-03, open)

## The rule today
A reclaimed article keeps its number (specs/lifecycle.md row 10; test_native_expiry asserts
`STAT 1` -> 423 and "high water kept"). GROUP reads the catalog's carried live count at the top view
(fn-scat-group-summary), proved equal to the list model's fn-nntp-group-count. Both count EVERY
numbered article in the view, reclaim tombstones included.

## Why it came up
test_native_over_pins (a Codex-era test that has never passed in any recorded run) expects
`211 2 ...` after reclaiming 32 of 34 articles; the node answers `211 34 1 34`, which is what the
reference model says. Found by lane served-catalog-live from source; not yet reproduced natively.

## RFC
RFC 3977 6.1.1.2: the count is an estimate, >= the number available and <= high - low + 1; the low
water mark must not decrease; articles may be removed. So `211 34 1 34` is legal.

## Options
1. Keep the model; correct the test to `211 34 1 34`; document that reclaimed articles stay counted.
   Cheap. Low water never rises after expiry: clients show phantom unread, and `OVER 1-N` /
   LISTGROUP walk N tombstones forever on an expiring server.
2. GROUP / LIST / LISTGROUP exclude reclaimed articles: count exact for available, low water rises
   past a reclaimed prefix, high water kept. Changes fn-nntp-group-summary's definition (it reads the
   tombstone bit), every theorem over group summaries, and needs a per-group carried tally maintained
   by the reclaim swap. A reference-model and spec amendment.
3. A middle: low water rises past a reclaimed PREFIX only; the count stays an upper estimate
   (high - low + 1). Smaller than 2: no exact tally, one carried low-water per group.

## Coordinator's lean
Option 2, or 3 if 2's exact tally costs much more than it gives. A server that expires articles must
move low water or readers degrade without bound; that is the standard reading of low water in
INN-style servers. Open questions for Astra: is exactness worth the tally, or is 3 enough? What
happens to a session PINNED at an older view when low water rises (ember's LIST decision: discovery
reads the latest completed view; article retrieval stays pinned; Astra's own low-water objection in
decisions/list-view-2026-10-02.md applies here directly)? Withdrawn (cancelled) versus reclaimed
(expired) articles: are both excluded, and does LISTGROUP list them? Does this interact with number
reuse (never) and with the ARENA-FORGET work (reclaim returning disk)? What would change my mind: a
client-behaviour or proof-cost argument that phantom numbers are harmless.

## Astra's view

### Liaison fact-check (codex-liaison-11, 2026-10-03, at 4aa332295; consultation c03, gpt-6-astra, read-only, 976 s)
Checked in source myself; file:line as Astra cites them (worktree build/lanes/codex-c03-groupcount).
- CONFIRMED, and it changes the question: the failing fixture is NOT a reclaimed prefix. tests/test_native_over_pins.py:96-103
  posts n0 (kept), 32 expiring gap articles, f0 (kept); reclaimed=32; survivors are numbers 1 and 34 (:129 asserts OVER
  rows [1, 34]). So option 3 (prefix low water) does not make this test pass: low stays 1; only an exact count gives `211 2`.
  The exact answer under option 2 is `211 2 1 34`, not `211 2 33 34`. The file's "reclaiming 32 of 34" is right, "prefix" is not.
- CONFIRMED: the carried live tally exists and is maintained on withdrawal (books/catalog-logic.lisp:932-945 count/low/high
  cells; books/catalog-paged.lisp:1144-1151 fn-cat$p-drop-entry decrements and moves low/high along the links). Its liveness
  predicate fn-cat-live-rowp (catalog-logic.lisp:314-319) tests withdrawal, number and Message-ID only: no reclaim test.
- CONFIRMED: "read the tombstone bit" is not local: fn-nntp-article-tombstonep takes the ARENA (books/article-arena-reads.lisp:
  83-98); fn-nntp-group-summary (nntp-projection.lisp:430) and fn-scat-group-summary (served-catalog.lisp:1386) have no arena formal.
- CONFIRMED: the reclaim swap re-pins every connection (books/owner-reclaim-pass.lisp:333 fn-orcp-repin-conn) and is admitted
  only with readers = 0 (fn-orcp-swap-word :156-163); tests/test_native_expiry.py:278-295 expects the open connection to answer
  "430 article reclaimed" with no GROUP. So "a session pinned at an older view when low water rises" does not arise from reclaim
  for by-number reads today; it arises only between live LIST (decision 2026-10-02) and a pin, across WITHDRAWAL.
- CONFIRMED: OVER already skips reclaimed articles (books/nntp-responses.lisp:1426-1444); ARTICLE/STAT answer 423/430
  "reclaimed" by name (:106-118). So today GROUP's count / LISTGROUP's body and OVER disagree about the same numbers.
- CONFIRMED RFC text: rfc3977.txt:2026-2040 (the three empty forms, "MUST NOT represent an empty group in any other way"),
  :2058-2068 (low MUST NOT decrease within the session, SHOULD NOT across clients; clients may drop state below low),
  :2176-2181 (LISTGROUP "lists precisely those articles that exist"). The file's "low water must not decrease" is the
  session MUST plus a cross-client SHOULD. rfc6048.txt is in the repo.
- CONFIRMED: 4 direct includers of nntp-projection. NOT RE-RUN: the 43-line/9-book census and the 439 transitive includers
  (my own looser grep over books+host+tests+tools+specs: summary 28 lines / 9 files, count 45 lines / 16 files).
- NOT CHECKED by me: the PRF/NNT/STO registry line numbers; the cost table's below-top correction bounds (fn-scv-x).
- Astra marks UNVERIFIED itself: client behaviour (Gnus/slrn), native results, ARENA-FORGET (not in its checkout).
Liaison's reading: Astra's position is option 2' = exact AVAILABLE count with true first/last available numbers, the
allocation watermark kept separately (empty group -> `211 0 35 34`), LISTGROUP/NEXT/LAST/cursor on the same available set,
raw ARTICLE/STAT keeping the named "reclaimed" refusal; implemented by teaching the catalog REBUILD at the reclaim swap
(which already builds a fresh catalog) the availability predicate, not by a new in-place writer. It asks ember only one
thing: whether live discovery may advertise a low above what a pinned connection still retrieves (left open on 2026-10-02).

### Astra's answer (verbatim)

Option: **2′ — exact available-article summaries and enumeration, with allocation history kept separately; not option 2’s unqualified “high water kept.”**
Reason: the sparse fixture retains articles **1 and 34**, so prefix advancement cannot fix it; an exact tally already exists, but its liveness predicate ignores reclamation (`tests/test_native_over_pins.py:96–129`; `books/catalog-logic.lisp:314–319,932–945`).
Must land together: NNT-006/NNT-042 and lifecycle row 10 clarification, STO-014/STO-017 integration, PRF-074/346/363/939/1225/1229 review, writer/refinement teeth, sparse/prefix/empty/tail/cancel/pin/crash tests (registry coordinates below).
Unsure: native results, uncommitted ARENA-FORGET work, and real-client consequences of live LIST marks above pinned retrieval are **UNVERIFIED**; current reclaim actually repins connections (`books/owner-reclaim-pass.lisp:329–346,377–393`).
Needs ember: **not for choosing the tally**; the sources settle that engineering recommendation. The outstanding product choice is whether live discovery may advertise a floor above still-readable pinned articles, explicitly left open by the earlier decision (`build/codex/c03/list-view-2026-10-02.md:201–209`).

Consultation at the supplied `4aa332295c85f03f5a97d7b0ac2228f9b95ab1e9` source coordinate (`build/codex/c03/CONSULT.md:3`). This is source inspection, not certification, native execution, or deployment evidence. No tracked changes, builds, ACL2, tests, commits, SSH, or box commands. All proposed behavior and proof obligations below are proposals, not completion claims. Citations are checkout-relative file:line coordinates; ranges identify surrounding evidence.

## A. Attack the lean first

**The strongest objection is not the extra integer. It is that “available” is presently a property of an arena-backed payload and a particular reader view, whereas the summary is a property of the catalog alone.** `fn-nntp-group-summary(archive, group)` and `fn-scat-group-summary(archive, group, v, fn-cat)` have no arena parameter; articles carry payload **handles**, not tombstone bytes (`books/nntp-projection.lisp:430–437`; `books/served-catalog.lisp:1386–1401`; `books/acceptance.lisp:22–36`). The actual tombstone predicate takes the arena and reads its fixed prefix (`books/article-arena-reads.lisp:83–98`). “Just read the tombstone bit” is therefore not a local edit to these definitions. Neither summary currently has such a bit.

There is a second, more dangerous objection. Exact live availability plus the already chosen live LIST policy can tell a client “discard everything below L” while an old article pin still serves those numbers. RFC 3977 expressly licenses that client bookkeeping (`rfc3977.txt:2058–2068`). The prior decision preserves the article pin and explicitly leaves this conflict to a policy follow-up (`build/codex/c03/list-view-2026-10-02.md:203–209`). An exact number does not resolve the conflict. Nor may we quietly repin on LIST: “The LIST command MUST NOT change the visible state of the server in any way” (`rfc3977.txt:3759–3762`).

**These objections win against the proposed patch’s apparent scope, but not against exact counting.** They require a proved availability projection/carried fact, consistency across writers and commands, and an explicit view policy. Option 3 incurs essentially the same predicate, low-end maintenance, pin, and lifetime obligations. It does not remove the main proof problem.

The strongest argument for option 3 is legitimate: GROUP permits an estimate, and clients obtaining actual numbers with LISTGROUP/OVER need not care about exact counts. A prefix-only scheme can avoid decrementing a count at every interior expiration. But this checkout already decrements a carried count on withdrawal and maintains predecessor/successor links; replacing availability semantics can reuse that infrastructure (`books/catalog-paged.lisp:1090–1119,1144–1199`). Meanwhile the actual failing fixture leaves one old survivor at 1 and another at 34, reclaiming **2–33**, not 1–32 (`tests/test_native_over_pins.py:96–103,129`). An arbitrarily long interior hole remains with option 3. Exact count is a small marginal maintenance operation once the availability index exists; a new low-water-only mechanism is not evidently simpler. **I choose 2′.**

“Phantom numbers are harmless” is unproved. The supplied prior consultation quotes Gnus/slrn behavior, but I have not fetched those upstream versions or run those clients; its external-client observations remain **UNVERIFIED in this consultation** (`build/codex/c03/list-view-2026-10-02.md:152–156`). The RFC itself supplies the strongest established client argument: consumers may discard remembered information below low. Conversely, neither the RFC nor this fixture establishes that raising low eliminates sparse-range work.

## B. RFC reading, sentence by sentence

These are **RFC requirements/definitions**, not fn’s stronger snapshot or durability guarantees.

| Question-file assertion | Reading against the text |
|---|---|
| “The count is an estimate.” | Correct. GROUP returns “an estimate of the number of articles in the group currently available” (`rfc3977.txt:2005–2009`). Exactness is a local choice. |
| “>= number available, <= high − low + 1.” | Correct **for nonempty groups**. “If the group is not empty, the estimate MUST be at least the actual number of articles available and MUST be no greater than one more than the difference between the reported low and high water marks” (`rfc3977.txt:2011–2013`). The third empty form imports that condition only when its estimate is nonzero (`:2037–2040`). |
| “Low water must not decrease.” | Incomplete. Except the empty/all-zero case, it MUST NOT decrease relative to earlier responses for that group **in this session**; it SHOULD NOT decrease relative to responses ever sent to any client, and any failure of the latter SHOULD be transient (`rfc3977.txt:2058–2068`). This is not an unconditional global MUST. |
| “Articles may be removed.” | Correct: “Articles may be removed from the group.” Reinstatement is constrained: “those articles MUST have numbers no less than the reported low water mark” (`rfc3977.txt:2042–2050`). |
| “So `211 34 1 34` is legal.” | Correct **for this sparse fixture’s count and endpoints**, not a proof for every choice of 32 removed articles. The remaining articles here are 1 and 34. The count inequality is 2 ≤ 34 ≤ 34. The argument must also check marks and selection effects, not only the inequality (`tests/test_native_over_pins.py:96–129`; `rfc3977.txt:2005–2013,2082–2089`). |

### The two concrete responses

The examples below omit only the required trailing group name.

* **Actual sparse fixture: survivors {1,34}.** `211 34 1 34` is an allowed estimate. Exact option 2′ produces **`211 2 1 34`**. **`211 2 33 34` is wrong**: it reports low above an existing article 1 and names nonexistent article 33 as the first. The fixture itself expects only the count prefix `211 2`, and separately asserts overview numbers `[1,34]` (`tests/test_native_over_pins.py:115,129`; `rfc3977.txt:2005–2009,2082–2086`).
* **Different prefix fixture: survivors {33,34}.** `211 2 33 34` is correct. The estimate 34 is not legal with these marks, because their span is 2. With obsolete marks 1/34, the count inequality alone passes, but §6.1.1.2 says the response returns “the article numbers of the first and last articles in the group at the moment of selection” (`rfc3977.txt:2005–2013`). I would not certify **`211 34 1 34` for that nonempty prefix case** from the estimate clause: it does not license obsolete endpoints. Historical implementations may retain conservative marks; that interoperability practice is **UNVERIFIED here** and cannot erase the sentence.
* **Tail-only removal:** distinguish the reported last available article from the permanently retained allocation frontier. The RFC explicitly allows reported high to decrease and warns the next allocation need not be high+1 (`rfc3977.txt:2052–2056,2069–2080`). Therefore “keep high” must mean **keep allocation history**, not necessarily advertise that allocation high as the current last article. This is why my recommendation is 2′ rather than literal 2.

### Every article reclaimed: all three empty forms

“Clients MUST accept all three cases; servers MUST NOT represent an empty group in any other way” (`rfc3977.txt:2026–2028`). The three are:

1. **H = L−1, count = 0**. “Servers SHOULD use this method to show an empty group” (`:2030–2033`). After numbers 1–34 were allocated, choose **`211 0 35 34`**.
2. **All three zero** (`:2035`). Thus `211 0 0 0` is permitted, although I would not select it for an exhausted previously populated group.
3. **H ≥ L**, count zero or nonzero; if nonzero, the usual count inequalities apply (`:2037–2040`). Thus `211 0 1 34` and even `211 34 1 34` can represent an empty group if they respect the applicable previous-low rule. Do not claim the RFC forces the count to zero in *every* empty form.

All cases still require an **invalid current article** on empty selection (`rfc3977.txt:2082–2088`), and LISTGROUP must return an empty body (`:2176–2181`). Option 1 as implemented cannot get this right merely because its 211 numbers happen to fit the third form: its selection takes `fn-nntp-group-low`, and its enumeration takes every positive projected number, including tombstones (`books/nntp-projection.lisp:61–68,376–388,458–491`).

For the preferred empty form, fn must retain the next-unused/allocation watermark even when no article is available. It already does: the empty branch uses `fn-state-nexts`; the catalog’s next is one plus its historical group high (`books/nntp-projection.lisp:436–437`; `books/catalog.lisp:69–70`). It must additionally **recognize availability-empty**, independently of “there are no numbered history records.” Reclaimed identity/number history must remain for duplicate and named-reclaimed answers (`specs/lifecycle.md:82–83`; `books/nntp-responses.lisp:111–118`). At the RFC maximum article number, test the representability of the empty successor marker separately from the permitted article-number range; no new article may exceed 2,147,483,647 (`rfc3977.txt:1949–1957`).

### LISTGROUP, ACTIVE, OVER, and a low above pinned retrieval

* LISTGROUP’s initial line has the **same arguments as GROUP**, but its body “lists precisely those articles that exist in the group at the moment of selection” (`rfc3977.txt:2176–2181`). The count may overestimate body length. A range limits the body, **not** the whole-group summary, and the selected current article is the group’s first even if outside that range (`:2191–2205,2211–2217`). Fn’s count-equals-full-LISTGROUP-length theorem is stronger than the RFC, not an RFC obligation (`books/nntp-list-counts.lisp:11–17,42–49`).
* LIST COUNTS also permits an estimate: RFC 6048 imports GROUP’s marks and estimated count, and allows results to change within a session (`rfc6048.txt:312–323`). Thus fn’s exact COUNTS equality is a stronger local guarantee.
* LIST ACTIVE has no count field. Its high and low “are as described in the GROUP command,” in the opposite order (`rfc3977.txt:3885–3892`). It must include every group this client may select without a wildmat (`:3879–3882`). This does **not** require equality with a GROUP response obtained earlier before the store changed.
* OVER: “The server SHOULD NOT produce output for articles that no longer exist.” A numeric range with no existing articles MUST receive 423 (`rfc3977.txt:4335–4345`). The first is SHOULD, not MUST. Fn already deliberately skips reclaimed overview lines (`books/nntp-responses.lisp:1426–1444`); retaining a history record does not make its tombstone a news article for LISTGROUP.
* **Same view:** low above a number still available in that group is inconsistent with GROUP’s first-article definition. LAST is especially sharp: “There MUST NOT be a previous article when the current article number is the reported low water mark” (`rfc3977.txt:2331–2335`).
* **Different completed views:** the RFC has no ViewId/pinned-session vocabulary and no explicit sentence prohibiting ARTICLE of an old still-retained object after a newer LIST advertises a larger low. I cannot turn its cross-view silence into either a blanket MUST NOT or a clean client-safety guarantee. What is established is the client’s right to discard bookkeeping below the advertised floor (`rfc3977.txt:2065–2068`). If fn permits that response pair, document it as the consequence of its local discovery-versus-retrieval policy, not as whole-session snapshot consistency. Actual reinstatement below a previously reported floor is explicitly forbidden (`:2047–2050`).

## C. Precisely chosen semantics and the actual pin behavior

**Proposed option 2′:** for a group and one authorized view V, let A be its numbered, representable, visible, **non-reclaimed** articles. When A is nonempty, report `(length A, min number A, max number A)`; when empty, report `(0, next-unused, next-unused−1)` and select no current article. LISTGROUP enumerates exactly A restricted to the requested range. LIST/ACTIVE uses the same endpoint definition; LIST COUNTS also uses the exact count. Keep the raw identity/number/tombstone lookup for explicit ARTICLE/STAT diagnostics and duplicate admission. This separates **available news** from **retained acceptance evidence**, preserving lifecycle row 10 rather than changing it to “the number disappears” (`specs/lifecycle.md:82–83`).

“Available” here is not a new whole-state parser pass or “all bytes have just been read successfully.” Start from the existing number/identifier projection and visibility contract, adding the independently carried reclaim status. The existing projection checks number bounds and renderable Message-ID (`books/nntp-projection.lisp:55–68`). Read/I/O failure remains a separate outcome; an exact count must not turn a transient disk failure into a durable removal policy (durable/uncertain rules: `AGENTS.md:59–61`).

### The native host and the actual dispatch subjects

The native chunk entry `fnn-owner-chunk-span-no-io` calls `fn-owner-chunk-span`; its evaluation calls ACL2 `fn-mca-read-span` (`host/native/owner.lisp:4160–4166`; `host/owner-host.lisp:4230,4271–4276,4442–4444`). That runs `fn-oas-read-span` (`books/owner-credits.lisp:195–205`), then `fn-otm-read-span` → `fn-orr-read-span` → `fn-scr-ocfg-read-span` (`books/owner-article-slots.lisp:259–269`; `books/owner-time-admission.lisp:197–205`; `books/owner-reader-read.lisp:57–71`). `fn-scr-command` calls `fn-nntp-archive-command-cat` (`books/served-catalog-chain.lisp:249–257`). The unrestricted command subjects are:

| Command | ACL2 function called by the dispatcher |
|---|---|
| GROUP | `fn-nntp-group-result-cat` → cursor `fn-scat-group-low` and rendered `fn-scat-group-summary` (`books/served-catalog-dispatch.lisp:131–134`; `books/served-catalog.lisp:1547–1557,1457–1465`). |
| LISTGROUP | `fn-nntp-listgroup-command-cat`, using summary and catalog number range (`books/served-catalog-dispatch.lisp:109–111`; `books/served-catalog.lisp:1572–1584,1601–1623`). |
| LIST / LIST ACTIVE | `fn-nntp-list-active-cat`, whose active-line functions read the summary (`books/served-catalog-dispatch.lisp:144–146`; `books/served-catalog.lisp:3137–3153`). |
| LIST COUNTS | `fn-nntp-list-counts-command-cat` (`books/served-catalog-dispatch.lisp:55–61`). |
| OVER / XOVER range | `fn-nntp-over-range-ovw`, producing the cursor effect; the native `fnn-owner-cursor-step` calls ACL2 `fn-splan-cursor-step` to render bounded quanta (`books/served-catalog-dispatch.lisp:112–118`; `host/native/owner.lisp:515–526`). Other forms pass through compatibility/fallback handling, so this is specifically the range arm. |
| STAT by number / Message-ID / current | Withdrawal overrides first, then `fn-nntp-number-retrieval-cat`, `fn-nntp-msgid-retrieval-cat` or `fn-nntp-current-retrieval-cat` (`books/served-catalog-dispatch.lisp:62–108,151–162`). |

Restricted readers can take the authorized reference path instead (`books/served-catalog-chain.lisp:741–760`); changing only the unrestricted dispatcher is insufficient. These are inspected call sites, not a newly certified host-boundary claim.

### Which view answers which command?

| Command | Adopted/proposed contract and observed source distinction |
|---|---|
| Successful GROUP or LISTGROUP, even reselecting the same group | Obtain latest **completed durable** reader view, select there, keep that pin. LISTGROUP is not an old-pin enumeration command. Failed selection preserves old pin and cursor (`specs/nntp.md:461–484`; `books/served-catalog-chain.lisp:1061–1072`). |
| OVER/XOVER, ARTICLE/HEAD/BODY/STAT, HDR/XHDR, NEXT/LAST | Use the retained article pin until an authorized refresh boundary. Cancellation after that pin is invisible until refresh (`specs/nntp.md:461–478`; dispatcher at `books/served-catalog-dispatch.lisp:83–162`). |
| LIST / LIST ACTIVE / LIST COUNTS | The **adopted decision** says one latest completed durable discovery view, without moving article pin/cursor (`build/codex/c03/list-view-2026-10-02.md:201–209`). **This checkout’s dispatcher still supplies the ordinary archive and v** to those arms (`books/served-catalog-dispatch.lisp:55–61,144–146`); the decision must not be mistaken for landed code. |
| Online reclaim | **Current source adds a substantial exception:** it rebuilds the store and repins every connection to the rebuilt owner, retaining session/wire state. It does not leave old ordinary connections retrieving pre-reclaim payloads (`books/owner-reclaim-pass.lisp:329–346,377–428`). |

Consequences:

* After a successful GROUP with low 33, a subsequent unchanged-view ARTICLE 1 must not succeed from an older pin; GROUP already replaced that pin. A subsequent LISTGROUP also refreshes; it cannot justify an obsolete body by appealing to the pre-GROUP pin. If the store legitimately changes between commands, distinguish that from an internally mixed response (`books/served-catalog-chain.lisp:1061–1072`; `specs/nntp.md:469–473`).
* A newer **LIST** can show low 33 while the old article pin still supplies ARTICLE 1/OVER 1, particularly across withdrawal. This is the actual unresolved discovery-policy case, not “GROUP stays old.” Reissuing GROUP resolves the split by selecting the new view (same citations; discovery decision at `build/codex/c03/list-view-2026-10-02.md:203–209`).
* An in-progress response is a different kind of pin. The OVER native tests hold a response, expect `reason=readers` on reclaim, drain/cancel it, then allow installation (`tests/test_native_over_pins.py:34–84`). Current swap admission requires zero other arena readers (`books/owner-reclaim-pass.lisp:156–177`). **Response ownership is not indefinite connection snapshot ownership.**
* The expiry test explicitly expects a connection open across the swap to begin answering “reclaimed” without issuing GROUP (`tests/test_native_expiry.py:278–295,321–336`). That agrees with the repin implementation, but deserves a named NNT-042 reclaim boundary; the spec’s listed refresh boundaries omit it (`specs/nntp.md:465–470`). Do not infer reader retention from lifecycle row 5 alone (`specs/lifecycle.md:77`).

My policy recommendation is to preserve the already adopted separation of live discovery and pinned article reading, **explicitly acknowledge the possible LIST/ARTICLE mismatch**, and test it. Do not silently advance pins, disconnect readers, or clamp LIST’s low to a hidden global minimum of old pins. Those would respectively change the pin promise, introduce an availability policy, or abandon latest-view marks and reintroduce indefinite low-water lag. If “no advertised low may exceed anything this connection can still retrieve” is the product requirement, the previous discovery decision must be amended; counting cannot satisfy both promises. This is the one material product question the sources leave open.

### Withdrawn versus reclaimed, today and under 2′

| Property | WITHDRAWN/cancelled | RECLAIMED payload |
|---|---|---|
| Representation | Held catalog row has `(withdrawal-version . cause)`; visibility is versioned; row/number history remains (`books/catalog.lisp:84–86`; `books/catalog-logic.lisp:314–319`; `books/catalog-delta.lisp:14–25`). | Record’s payload becomes FN-RCL2 tombstone; identity/group fields remain and retention charge changes to the history unit (`books/store-reclaim-pack.lisp:41–64`; `planning/decisions.md:1690–1692`). Not the same as setting withdrawal. |
| Current count / LISTGROUP | Excluded at views past withdrawal, included at earlier pins. Live-row predicate tests withdrawal; group enumeration reads visibility (`books/catalog-logic.lisp:314–325`; `books/served-catalog.lisp:1180–1188`). | Included today when its retained number/Message-ID passes projection: no tombstone test in `fn-nntp-article-number` or live-row predicate (`books/nntp-projection.lisp:61–68`; `books/catalog-logic.lisp:314–319`). |
| Current OVER | Invisible past cancellation, visible before it through the pin (`specs/nntp.md:461–478,1274–1276`). | Skipped deliberately (`books/nntp-responses.lisp:1426–1444`); sparse native expects only 1 and 34 (`tests/test_native_over_pins.py:129`). |
| Explicit STAT n / STAT Message-ID | `423 withdrawn` / `430 withdrawn` when withdrawal is visible; these overrides precede retrieval (`books/served-catalog-dispatch.lisp:62–76`; `books/nntp.lisp:345–348`; `books/protocol-table.lisp:713–716`). | `423 article reclaimed` / `430 article reclaimed`, including STAT, before normal success and without moving cursor (`books/nntp-responses.lisp:106–126,159–168`). |
| 2′ | Same versioned exclusion. | Also excluded from count, LISTGROUP, cursor navigation and overview, while explicit raw lookup still returns the named reclaimed refusal. |

A target that is both withdrawn and reclaimed should retain both historical facts; the current explicit withdrawal override takes precedence when applicable. Do not erase the withdrawal or return “never accepted” while changing enumeration (`books/served-catalog-dispatch.lisp:62–95`; `specs/lifecycle.md:82`). Authorization can hide even the distinction: restricted readers receive ordinary absence for excluded articles (`specs/nntp.md:1732–1747`).

### Numbers, storage release, and ARENA-FORGET

The RFC requires unique local `(group,number)` bindings and increasing numbers in arrival order, with sequential unused numbers a SHOULD (`rfc3977.txt:1927–1947`). Fn additionally preserves allocation watermarks through removal/restart (`specs/nntp.md:560–565`), and the expiry fixture refuses a reoffer and allocates the next number (`tests/test_native_expiry.py:144–153`). None of 2′’s filtering reuses, renumbers, or globally merges these identifiers.

The named **arena-forget lane’s implementation is UNVERIFIED**: no `ARENA-FORGET`/`arena-forget` match was found in this checkout’s planning/specs/books/host search. The inspected existing release path reseats retained payload frames, retires files, and closes only files whose arena references and reader stamps permit it (`host/native/owner.lisp:4925–4941`). This is not proof that dead old handles have been forgotten.

Required interaction, independent of that lane’s implementation: reclaim status and exact summary are published with the rebuilt root; every surviving raw tombstone lookup points to a live tombstone handle; no held response or retained snapshot points at forgotten payload storage. Only then may old payload references/extents be released. “Removed from count” is **not** a proof of handle unreachability: raw identity lookups, old pins, feeds/consumers and in-flight responses can still be roots. If the product preserves old article pins across reclaim, ARENA-FORGET must retain their generations; today the swap instead repins connections and excludes active readers (`books/owner-reclaim-pass.lisp:156–177,329–393`). Never conflate reclaiming an arena slot with reusing an NNTP number.

## D. What each option breaks or leaves open

| Option | Clients and protocol | fn contracts/registries/tests | Stored representation |
|---|---|---|---|
| **1: keep current count and enumeration** | The sparse 34 estimate is legal, but tombstone LISTGROUP entries violate “precisely those articles”; empty-group cursor can refer to a reclaimed number. Stale endpoints after prefix/tail reclaim are not justified merely by estimate permissiveness. Counts/unread estimates can remain large. | Correcting only the sparse test to 34 matches current source but papers over availability disagreement. Preserve lifecycle history, but clarify/fix NNT-006 enumeration and selection; changing its normative contract to list tombstones would not establish RFC conformance. PRF-074’s algebra remains true about the wrong set. (`books/nntp-projection.lisp:458–491`; `planning/requirements.json:1421`; `planning/proofs.json:3336`.) | No new layout. Leaves reclaim and pin/handle obligations untouched. |
| **2 as written** | Better counts/listings, but “high water kept” is ambiguous and may retain a removed tail as reported last article. Live LIST/pinned retrieval conflict persists. | Requires all affected commands and projections, not just count. Sparse test’s count 2 can stay; its low must remain 1. Lifecycle row 10 still keeps number history. Changing only `fn-nntp-group-summary` leaves GROUP’s separate cursor-low and LISTGROUP’s enumeration wrong (`books/served-catalog.lisp:1547–1557`; `books/nntp-projection.lisp:479–491`). | A tally already exists; no necessary new on-disk field just to count. A new carried availability fact requires a representation/refinement decision. |
| **3: span estimate after unavailable prefix** | RFC permits span estimate with correct endpoints. Does nothing for the actual interior hole: low=1, span=34. LISTGROUP must still exclude *all* reclaimed articles, not just the prefix. | Breaks fn’s exact count = full LISTGROUP length if implemented as shared summary/count semantics; restate PRF-074 or keep a separate exact COUNTS path. It still needs correct empty selection, cancel/reclaim liveness and endpoint proofs. (`books/nntp-list-counts.lisp:42–49`; `planning/proofs.json:3336`.) | Not “one low word and done”: needs successor finding/liveness and allocation frontier, plus a correct high if tail disappears. Existing link/tally machinery reduces any storage saving (`books/catalog-paged.lisp:101–119,1144–1199`). |
| **2′: my precise recommendation** | Exact available count, actual nonempty endpoints, preferred empty form, raw history retained. Same-view enumeration/cursor consistency; live LIST remains explicitly separate from old article retrieval. | Preserve count/list algebra over the **available** projection, establish carried refinement and all writers, amend NNT-042 for discovery and actual reclaim boundary. Add tests below; do not mark certification complete from this answer. | Reuse existing group summary and links. Choose one proved row availability classification/projection. Persisted layout changes only if that chosen representation adds/changes encoded fields. |

**Registry/spec landing set.** NNT-006 (`planning/requirements.json:1421`) owns membership/marks; NNT-007 (`:1466`) owns carried validation, so no served revalidation; NNT-011 (`:2121`) owns withdrawal; NNT-042 (`:4224`) owns pins. STO-014 (`:2331`) owns reclamation distinctions, STO-017 (`:2850`) its durable execution. Review PRF-074 (`planning/proofs.json:3336`), PRF-346 (`:12349`), PRF-363 (`:13044`), PRF-939 (`:14977`), PRF-1225 (`:6`) and PRF-1229 (`:21383`). The last two are `planned` at these bytes; the four earlier named proof rows are `uncertified-at-current-digest`. Their existence is not current certification. Update `specs/nntp.md:461–500,560–565` and clarify lifecycle row 10 (`specs/lifecycle.md:82`), without deleting number/identity retention. Any new requirement/proof/scenario IDs must be claimed by the implementing lane (`AGENTS.md:17–21`); none are invented or changed here.

**Format answer:** the current paged catalog carries summary tables through the nested old foundation, and the loader rebuilds the catalog from store rows (`books/catalog-paged.lisp:38–49,870–880`; `books/served-catalog-owner.lisp:423–454`). Reclaim constructs a fresh catalog and installs it (`host/owner-host.lisp:5174–5183`; `host/native/owner.lisp:5731–5761`). Therefore “add exact tally ⇒ on-disk catalog-page migration” is not established: the tally is already carried and a rebuild-derived change need not add a serialized group field. If the chosen D41 realization serializes a new tally/availability bit or changes row meaning, update that schema, codec/profile checks and correspondence together; do not assume it fits an unnamed spare bit. D41 is an agreed direction (`planning/decisions.md:1674–1676`), not evidence that every live table is already the durable page image. D38 expressly chooses one format, fresh 6.6.0 redeploys and no migrations (`:1300–1302`).

## E. Proof fan-out, maintenance, and cost

### Reproducible direct dependency census

Search used (exact symbols, excluding longer suffixed names):

```
rg -n --pcre2 '(?<![\w-])fn-nntp-group-(?:summary|count)(?![\w-])' books -g '*.lisp'
```

At this checkout: **43 matching lines / 43 symbol occurrences in 9 books**. The defining book is `books/nntp-projection.lisp` (count at 167; summary at 430). The other books and matching-line counts are: `group-bucket-invariants` 3, `nntp-effects` 4, `nntp-index` 3, `nntp-list-counts` 4, `nntp-responses` 3, `protocol-builders` 2, `served-catalog-dispatch` 1, `served-catalog` 10; the defining book contributes 13. This literal census includes comments, hints, guard verification and disable lists; it is not 43 independent proofs. Exact-symbol tests add **8 lines in 3 books** (`tests/acl2/nntp-index-tests.lisp:61,151,193`; `tests/acl2/nntp-list-counts-tests.lisp:73,77,119`; `tests/acl2/serve-depth-tests.lisp:43,46`). Host adds one instrumentation-list line (`host/native/io.lisp:6160`), not a host summary decision.

`rg -n '\(include-book "nntp-projection"' books` yields **4 direct includers**: `control-served`, `nntp-index-runtime`, `owner-inspect-group`, `nntp-responses`. A small stdlib traversal of literal `include-book "…"` edges among `books/*.lisp` finds **439 transitive includers, 440 including the defining root**. Scope: syntactic local-book graph, includes local/conditional include forms; not a certification schedule or number of broken theorem statements. These are source-derived counts, not registry-generated completion counts.

All direct executable callers: count’s recursion and summary’s call (`books/nntp-projection.lisp:167–174,430–437`); summary’s group-initial (`:449–456`), `fn-nntp-active-line`, `fn-nntp-active-status-line`, `fn-nntp-counts-line` (`books/nntp-responses.lisp:280–289,327–337,418–419`). Other exact-symbol appearances are proof/guard/theory/instrumentation uses. GROUP and LISTGROUP reach summary via their initial-line functions; their separate low/enumeration calls matter (`books/nntp-projection.lisp:458–491`).

### Every directly mentioning theorem

Balanced-form inspection, ignoring comments/strings, finds **21 defthm events** (11 statement mentions, 10 hint-only), plus **2 macro-generated theorem events**. No blanket “every theorem must be restated” conclusion follows.

| Book:line / theorem(s) | Role and expected action for 2′ |
|---|---|
| `nntp-projection.lisp:177` `fn-nntp-group-count-loop-of-rev-onto`; `:183` `fn-nntp-group-count-natp`; `:187` `fn-nntp-group-count-at-most-articles` | Local execution bridge and elementary bounds, not the served keystone. Statements remain sensible under a shared filtering predicate; reprove if definitions change. |
| `nntp-index.lisp:224` `fn-nntp-group-count-is-index-shaped`; `:290` `fn-nntp-index-group-count-equals-fold`; `:447` `fn-nntp-index-cache-open-answers-group` | Shape bridge, representation equality, combined cache correspondence. Reprove with index builder and fold using the same available projection; false if only count changes and index still includes tombstones. Cache keys must distinguish changed availability/root. |
| `group-bucket-invariants.lisp:22` `fn-gidx-group-summary-of-build`; `:54` `fn-gidx-listgroup-result-projection-unfolds` | Derived bucket correspondence and explicitly named assembly restatement. Keep the assembly lemma as support, not a keystone (AGENTS.md:80–82). Under a separate projection, caller instances change; under changed record availability, builders/proofs change together. |
| `nntp-list-counts.lisp:42` `fn-nntp-group-count-is-listgroup-length` | **Named keystone**, PRF-074: count equals full enumeration, not range length. Preserve for 2′ over available articles. Option 3’s shared estimated count requires restating/replacing it, not merely a new proof of the old claim (`planning/proofs.json:3336`). |
| `nntp-list-counts.lisp:60` `fn-gidx-counts-lines-of-build` | Hint-only summary mention; derived renderer lifting. Reprove after bucket boundary, same algebra. |
| `nntp-effects.lisp:658,665,675,690` `fn-nntp-group-initial-is-response-text`, `fn-nntp-group-initial-is-a-status-line`, `fn-nntp-group-initial-fits`, `fn-nntp-listgroup-initial-is-a-status-line` | Hint-only; formatting lemmas explicitly keep summary closed (`:656–657`). No semantic restatement needed if tuple/renderer interface stays. Recertify dependencies. |
| `protocol-builders.lisp:158,161` `fn-proto-code-of-group-initial`, `fn-proto-code-of-listgroup-initial` | Macro-generated status-code facts, hint-only. Keep statements; these do not prove the count correct. |
| `served-catalog.lisp:1127` `fn-scat-group-summary-pass-is-archive`; `:1448` `fn-scat-group-summary-is-archive` | Pass-to-model bridge and derived carried-summary bridge. Present hypotheses identify the archive with **all visible catalog articles**, including tombstones. A separate available projection requires restating that correspondence; changing model/catalog predicates together can preserve statement shapes with an added proved availability relation. |
| `served-catalog.lisp:1467,1684,3195,3206` `fn-scat-group-initial-is-archive`, `fn-scat-counts-lines-is-archive`, `fn-scat-active-lines-is-active-lines`, `fn-scat-active-lines-is-active-status-lines` | Hint-only references, renderer corollaries. Reprove/lift from new boundary; no need to invent a new property for every line builder. |
| `served-catalog-dispatch.lisp:243` `fn-scat-gidx-counts-lines-of-build` | Local hint-only bucket/renderer bridge. Same handling as the prior row. |

The important additional **indirect keystones** are `fn-scat-group-summary-is-pass` (`books/served-catalog.lisp:1438–1446`, PRF-346), its cursor-low companion (`:1528–1537`), and `fn-scv-count-is-count-p`, `fn-scv-first-is-first-p`, `fn-scv-last-is-last-p` (PRF-363, `planning/proofs.json:13044`). Their table/pass definitions and historical correction must share the new availability meaning. The composed boundary is `fn-nntp-archive-command-cat-is-pinned`, equating **session and expanded effects**, not merely count (`books/served-catalog-dispatch.lisp:365–389`). Existing live-link preservation/probe keystones are also affected by changing what counts as live (`planning/proofs.json:6`, PRF-1225). These are substantially more important than the 4 formatting hints.

### Can the signature and most algebra survive?

**Yes, but not by adding an arena read to a function that has no arena.** The lowest-churn design is a *named available-article projection* of a retained archive, supplied to the existing summary/list-enumeration folds. Keep `(fn-nntp-group-summary archive group)` and its `(count low high)` shape, with `archive` at those call sites being the available projection. Raw ARTICLE/STAT/duplicate history continues to use the retained archive. Both projections must be tied to the **same** view/root and access policy, not independently refreshed. An executable must carry this projection’s summary/index; it must never rebuild it on GROUP. The current retained article is a handle-bearing record (`books/acceptance.lisp:22–36`), so the projection needs an arena-aware model and a derived metadata classification at write/load time (`books/article-arena-reads.lisp:83–98`).

An alternative is to add a derived availability field to the article/catalog representation and make `fn-nntp-article-number` filter it; that leaves most theorem formulas intact but broadens record-constructor/refinement work. A semantic change is still a semantic change when the theorem text stays identical. **Do not remove reclaimed records from the only archive or clear their raw memberships**: explicit `423/430 article reclaimed` and duplicate identity require those facts (`books/nntp-responses.lisp:111–118`; `specs/lifecycle.md:82–83`).

Proposed new events **`fn-scat-available-summary-is-projection`** and **`fn-scat-available-dispatch-is-reference`** (names proposed here, not existing events): under the carried root/view/access/arena relation, the actual catalog summary and cursor-low equal the logical available projection’s summary/first; LISTGROUP numbers equal that projection’s range; expanded dispatch effects and resulting session equal its specified command result, while raw lookup retains the tombstone distinction. Separate discovery and article views in the composed relation where the adopted LIST exception requires it. Preserve guards, establish the invariant at load, preserve it at every writer; never recognize the whole store per command (`AGENTS.md:41–54,95–96`; `specs/nntp.md:502–504`).

**Teeth owed:** reachable construction of ordinary rows, a real tombstone rewrite, an actual withdrawal before/after the pin, sparse {1,34}, prefix {33,34}, tail, crosspost, and all-reclaimed groups; assert every antecedent and complete result tuple/session/effects. For each necessary hypothesis, affirm all retained hypotheses, negate the removed one, and demonstrate failed conclusion; test wrong root/view/availability carry/arena relation separately. Label deliberately corrupted summaries and a mutant writer that omits the reclaim update as corrupted-state/mutation witnesses, not reachable counterexamples. Repeated reclaim/withdraw must not double-decrement. Failed selection must preserve both cursor and pin. A stale new summary paired with old payload/root must fail the relation before publication. These follow the proof-teeth discipline (`AGENTS.md:74–89`), and are proposed tests, not run ones.

### Every catalog writer and the reclaim swap

The complete generic mutation surface is `fn-cat-commit`, `fn-cat-withdraw`, `fn-cat-redecide`, `fn-cat-clear`, `fn-cat-clear-keyed` (`books/catalog.lisp:36–42`). Maintain or prove preservation at each:

| Writer/entry | Obligation |
|---|---|
| `fn-cat-commit`; attached `fn-cat$p-commit-w` and foundation `fn-cat$c-commit[-w]` | Insert available memberships into tally/endpoints/links; still allocate historical number for a tombstoned or withdrawn row. Derive availability once from the producer’s validated row/arena relation. Current commit uses only withdrawal and Message-ID in its live plan (`books/catalog-logic.lisp:1053–1063`; `books/catalog-paged.lisp:1090–1119`). Covers posts, peer ingress and other article producers through this interface. |
| `fn-cat-withdraw`; `fn-cat$p-withdraw-w` / foundation withdrawal | Remove each actually available crosspost membership once, update links/endpoints, retain historical number and withdrawal version. Current drop plan tests liveness and uses neighbor probes (`books/catalog-paged.lisp:1144–1185,1216–1233`). Reclaim-then-cancel must not decrement twice. |
| `fn-cat-redecide`; `fn-cat$p-redecide` | Prove preservation if availability remains independent of verdict/context, as proposed; if availability is extended to incorporate moderation/security decisions, this writer must update it too (`books/catalog.lisp:88–90`; `books/catalog-paged.lisp:1235–1238`). |
| `fn-cat-clear`, `fn-cat-clear-keyed`; paged/foundation counterparts | Establish empty tally, links, classification and matching root/key (`books/catalog.lisp:92–96`; `books/catalog-paged.lisp:1240–1274`). |
| Load/recovery/import/checkpoint/reopen | `fn-sca-load-held-row`, `fn-sca-load-held-rows[-from]`, keyed load, and legacy `fn-sca-load-rows`/`fn-sca-load-history` must establish it from each loaded row. Entry map explicitly covers init, full replay, checkpoint, import and crash reopen (`books/served-catalog-owner.lisp:85–102,423–454`; `books/catalog-entries.lisp:39–71`). No trusting a stale serialized tally without a matching root/refinement. |
| Completion/withdrawal orchestration | `fn-sca-complete`, `fn-sca-withdraw-targets`, `fn-sca-finish` call the relevant mutators; preserve the completed-prefix relation during prepare/finish and cancel-before-target ordering (`books/served-catalog-owner.lisp:164,243,945`; `books/catalog-entries.lisp:75–103`). Abort/refusal/non-article steps preserve the carry; they do not fabricate count changes. |
| Reclaim reconstruction and install | `fn-rclp-tombstoned` rewrites record payload and charge; it **does not mutate a catalog** (`books/store-reclaim-pack.lisp:55–64`). `fn-owner-orcp-load-columns` builds a **fresh** catalog with `fn-sca-load-held-rows-keyed`; native install replaces the live catalog after durable checkpoint install (`host/owner-host.lisp:5174–5183`; `host/native/owner.lisp:5731–5761`). Thus the complete reclaim path **does touch/replace the catalog representation**, but not by an in-place per-article tally decrement. Teach the rebuild the new predicate and prove swap coherence. |
| Owner/configuration install and connection repin | `fn-owner-orcp-swap` installs rebuilt owner, retention carry, octet/debt/usage counts and resets publication state; `fn-orcp-swapped-ocfg` repins connections (`books/owner-recovery-retain.lisp:43–75`; `books/owner-reclaim-pass.lisp:423–428`). Refresh derived authorization/bucket views too; newly created/retired group handling must preserve next-number history and fresh discovery. |

This is why the premise “reclaim needs to start touching the catalog page” is misleading. It already reconstructs/replaces the catalog; what is missing is the availability meaning, not necessarily a new mutation API.

### Visits per GROUP, not output size

Define N = catalog rows, G = configured group names, H = historical numeric high of this group, D = rows appended since queried v, W = withdrawal-version slots examined, R = withdrawn rows reached, X = distinct changed numbers, E = numeric endpoint positions searched. These are analysis variables, not new implementation limits.

| Option | Summary-path visit cost and important qualifications |
|---|---|
| 1 today | At catalog top: constant **summary table probes, zero article-row visits**; empty branch additionally searches next-number table. GROUP also tests membership in the group-name list and gets cursor-low separately (`books/served-catalog.lisp:1388–1394,1547–1557`; `books/catalog-logic.lisp:932–945`). Thus do not call the entire command universally O(1): O(G) group membership/next lookup is possible, plus repin/access costs. |
| 2′ with carried available summaries | Same number of top/completed-root summary probes; no payload scan during GROUP. Maintenance absorbs classification, tally and link work. If only the logical model is filtered on each read, it costs Θ(N) article visits plus tombstone-prefix accesses and fails the intended served-path design (`books/nntp-projection.lisp:167–174,202–212,430–437`; `books/article-arena-reads.lisp:83–98`). |
| 3 with carried low/high | Constant top summary probes plus subtraction; **not better asymptotically** than carried exact count. Lazy search for the next low instead costs up to Θ(H) numeric probes when a prefix disappears. A bounded scheduling quantum can bound each step, not total GROUP latency. |
| All three with current below-top correction | `fn-scv-x` scans D rows and W version slots/R withdrawal rows; dedup/list processing adds cost. End searches increment/decrement one number at a time, up to E ≤ O(H), with X-list membership tests (`books/served-catalog-view.lisp:85–92,152–188,466–480,669–684`). A conservative structural bound includes O(D+W+R+X+E) row/table visits, plus potentially quadratic dedup and O(E·X) list comparisons and row-decoding/membership costs. Not a proved flat bound. |

GROUP refreshing to “live” does not automatically reach catalog top: an in-flight batch can place catalog rows above the completed reader view (`specs/nntp.md:490–499`; top predicate `books/served-catalog.lisp:1375–1378`). A carried **completed-root** summary is the way to obtain the proposed zero-row-visit summary there, with publication proof; serving unfinished top rows to save correction work violates the durable-view contract.

Restricted sessions are another scope: they use the cached/rebuilt authorized reference view instead of the unrestricted catalog route (`books/served-catalog-chain.lisp:741–760`). No universal per-GROUP visit bound follows from the top catalog table alone. Measure/verify that route separately. LIST scales with enumerated group names, and LISTGROUP/OVER with visited numeric positions: exact count does not compress holes. OVER already schedules at most W numeric probes per cursor quantum; this is a **visit** bound and can yield with no output (`host/native/owner.lisp:462–474,515–537`; sparse test `tests/test_native_over_pins.py:132–137`). A low-water change cannot make an explicit OVER 1-H skip all gaps by itself.

## F. Missing cases and the concrete landing tests

1. **The fixture was mischaracterized.** Keep the interior-hole test and add an actual reclaimed-prefix test. Assert complete 211 tuples, selected current article via bare STAT, full and ranged LISTGROUP bodies, ACTIVE marks, COUNTS and OVER, not just `startswith("211 2 ")`. Preserve the existing OVER empty-yield/half-close/pipeline checks (`tests/test_native_over_pins.py:96–140`). “Never passed in any recorded run” and “node answers 34” are **UNVERIFIED execution claims** here; the question itself says the finding was from source and not yet natively reproduced (`build/codex/c03/QUESTION.md:10–12`).
2. **All reclaimed, all withdrawn, only lowest/highest surviving, last allocated article reclaimed, empty→new post, repeated reclaim, cancel-before-target, cancel-after-reclaim, multiple crosspost groups.** Test count, cursor and high independently. The existing expiry test’s “high water kept” retains article 5; it does not establish high behavior after the highest article is gone (`tests/test_native_expiry.py:104–108,131–153`).
3. **Define “prefix.”** It is the numeric interval below the first available member at the chosen view, crossing missing numbers, withdrawals visible at that view and reclaimed tombstones. A withdrawn number must not stop it merely because its payload was not reclaimed; an old pin where that withdrawal is not visible can stop it. An interior retained number at 1 prevents advancement despite arbitrarily many later tombstones. This follows the proposed A set, not payload ordering or elapsed expiry time. Existing visibility and membership are distinct tests (`books/catalog-logic.lisp:314–325`; `books/catalog-delta.lisp:14–25`).
4. **NEXT/LAST and current article.** Their model uses `fn-nntp-article-number`, currently unaware of reclaim (`books/nntp-projection.lisp:61–68,330–360`); changing only summary leaves navigation pointing at refused tombstones. Include failure codes and cursor preservation; LAST at low has a specific RFC MUST (`rfc3977.txt:2331–2345`).
5. **OVER/XOVER ranges, empty ranges, HDR/XHDR/XPAT and Message-ID forms.** Preserve XOVER’s compatibility response distinctions, keep numeric and Message-ID forms on one article pin, and do not conflate overview parse success with the membership tally (`specs/nntp.md:134–143,279–288`; `books/served-catalog-dispatch.lisp:112–140`). A count update cannot establish bounded sparse traversal; test visits/yields, not emitted-line count.
6. **NEWNEWS and timestamp polling.** Reclaimed articles are already skipped by its renderer (`books/nntp-responses.lisp:2623–2631`); choose its view with DATE and Message-ID follow-up retrieval, or a poll can discover an ID the old pin cannot retrieve. The specification explicitly leaves DATE/NEWNEWS no-miss across pins as a separate target (`specs/nntp.md:299–304`). Do not infer it from LIST policy.
7. **LIST COUNTS / NEWSGROUPS / NEWGROUPS / ACTIVE.TIMES.** ACTIVE has no count; COUNTS does and has its own arm (`books/served-catalog-dispatch.lisp:55–61,144–146`). NEWSGROUPS is description discovery, not article enumeration; RFC permits omissions and disagreement with ACTIVE (`rfc3977.txt:4062–4065`). The prior decision explicitly requires named policies for the other discovery commands (`build/codex/c03/list-view-2026-10-02.md:207–209`). Cover group creation, retirement/recreation, authorization and read-only/moderated status without mixing view/configuration roots (`specs/nntp.md:1732–1747`).
8. **Peering/feeds and BP.** Raw retained identity must continue suppressing duplicates independently of the reader count (`specs/lifecycle.md:82–83`). Count zero is not release evidence for feed/BP obligations. Holder integration needs its own check: the inspected store-holder implementation carries no reader pins in its first slot, and its comment records feeds/BP as external/open (`books/store-reclaim-holders.lisp:18–23,78–82`); that offline-only comment is stale against the live swap above. BP’s ADU explicitly excludes local NNTP numbers (`specs/bp-adu.md:57–60`); no local tally/floor should become globally merged group state. BP delivery can create new local membership under local allocation, not transport another node’s watermark.
9. **Crash/publication order.** The native pass stages checkpoint, interns, rebuilds fresh columns, checks swap admission, durably installs checkpoint, swaps owner/catalog/history, runs barriers, then releases extents (`host/native/owner.lisp:5725–5787`). The current tests name `captured`, `rewritten`, `staged`, `interned`, `rebuilt`, `installed`, `swapped`, `released`, and assert old/new visibility around installation (`tests/test_native_expiry.py:404–424`). Add count/list/cursor/root assertions at those cuts, not only STAT. A crash after install but before swap must reopen the new coherent summary; the host treats this incomplete swap as indeterminate/recovery-required (`host/native/owner.lisp:5788–5793`). Include lower checkpoint cuts `created`, `written`, `staged-durable`, `replaced`, `durable` (`tests/test_native_expiry.py:222–247`). A new persisted summary write adds corresponding modeled cuts if it changes this sequence; no new ACK before durability.
10. **Generation identity across reclaim.** Rewriting payloads can change availability without adding an article or changing a count-based ViewId. The current swap’s replacement/repin must invalidate every summary/access/cursor cache keyed only by old version; otherwise a “same v” cache can carry old count with new payload (`books/owner-reclaim-pass.lisp:156–175,329–346`; `books/owner-recovery-retain.lisp:43–73`). Carry the root/reclaim generation in the relation, or prove replacement makes old caches unreachable. This also matters for ARENA-FORGET and delayed I/O completions.
11. **Work/accounting.** Include group-name lookup, completed-prefix correction, restricted views, crosspost update work, empty-group next lookup, group-table growth, and rebuilding cost—not just a 211 line’s length. No arbitrary store-size cap or unbounded maintenance hidden in a served quantum; carry and preserve the invariant (`planning/decisions.md:1194–1209`; `AGENTS.md:41–54,95–96`).

The consultation leaves registries and generated current-view files untouched as required by its read-only brief. The implementing lane should land the chosen semantics, source-coordinate proof evidence and native cases together; nothing in this report supplies a green verdict (`AGENTS.md:24–31,105–110`).


## DECISION (coordinator + Astra agreed, 2026-10-03; ember not needed, may overturn)
Option 2' as Astra states it: GROUP / LISTGROUP / LIST report the exact AVAILABLE count with the true
first and last available numbers; the allocation watermark (numbers are never reused) is kept
separately and is what "high water kept" means. The fixture's exact answer is `211 2 1 34`; an
all-reclaimed group answers `211 0 <watermark+1> <watermark>` (RFC 3977 6.1.1.2). Availability is a
carried fact set when the reclaim swap rebuilds the catalog (it already rebuilds afresh), not a read
of the tombstone bit through the arena. The change covers every reader of fn-nntp-article-number
(GROUP's cursor low, LISTGROUP's body, NEXT/LAST) so they agree with OVER, which already skips
reclaimed articles. NNT-042's list of refresh boundaries gains the reclaim swap (it re-pins every
connection). The remaining mismatch (live LIST may advertise a low above what a pinned connection
still retrieves, across withdrawal) is documented and tested, not clamped. Owner: served-catalog-live.
