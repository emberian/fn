# Control messages: a design (2026-09-25)

Status: **proposed, not decided.** A design lane's proposal, written in answer
to ember's "we need to think about extending towards control messages"
(2026-09-25). Nothing here is implemented; no theorem named below exists yet.
It supersedes, if adopted, the position of
[substrate transport §7](../specs/substrate-transport.md) (lines 849-900),
"fn implements none of them", and it answers each of that section's four
objections rather than overruling them (§2.0). The draft spec section is
[peering §8](../specs/peering.md#8-control-messages-filing-and-authority-implemented-cancel-decided-served-withdrawal-open-group-control-deferred).

The one-sentence design: **a control article is evidence that a principal
asked; it is executed only when this node verified that principal's
signature over the exact authored source and this node's operator granted
that principal authority over the namespace the article names, and every
execution is a durable record that replay reads rather than recomputes.**

## 0. Finding: the current behaviour is not what the specs say

Two specs say a control article is "refused as ordinary articles into
`control.*` only if configured, never executed"
([peering](../specs/peering.md) lines 1186-1194) and "accepted as ordinary
articles into `control.*` if the operator configured that group"
([substrate transport](../specs/substrate-transport.md) lines 866-870).
No book or host file reads the `Control` field: a search of `books/` and
`host/` for the field name finds only the group-name classifier
`fn-native-admin-group-name-special-purposep`
(`books/native-admin.lisp:519-552`), which classifies group *names* and, as its
comment says, "confers nothing". So today a `Control:` article is an
ordinary article, filed in whichever groups its `Newsgroups` field names that
this node serves (the D05/D11 indexing rule, `planning/decisions.md` D05).
"Never executed" is true; "filed under `control.*`" is not implemented, and
RFC 5537 §3.7 (line 1136) says control messages SHOULD NOT be stored in the
groups their `Newsgroups` field lists. Packet C1 (§5) closes this before any
execution exists.

## 1. What the RFCs define

RFC 5536 §3.2.3 (lines 944-975): the `Control` header field "marks the
article as a control message and specifies the desired actions (in addition
to the usual actions of storing and/or relaying the article)"; its grammar is
`"Control:" SP *WSP control-command *WSP CRLF`, `control-command = verb
*( 1*WSP argument )`; and "An article with a Control header field MUST NOT
also have a Supersedes header field."

RFC 5537 §5 (lines 1919-1948): any article with a `Control` field is a
control message; agents "MUST either ignore or reject control messages with
unrecognized types" (line 1936); a `Subject` starting `cmsg ` "MUST NOT
cause an article to be interpreted as a control message" (line 1941), and
agents MAY reject such an article with no `Control` field as ambiguous; a
`.ctl` group name or an `Also-Control` field likewise MUST NOT make an
article a control message.

| Verb | RFC 5537 | What it asks a server to do | Syntax (Control field) | Special rules |
| --- | --- | --- | --- | --- |
| `cancel` | §5.3 (2197-2232) | withdraw the target "from circulation and access"; an honouring serving agent "SHOULD make the article unavailable to reading agents (perhaps by deleting it completely)" (2211); a cancel that arrives first SHOULD be remembered and the target rejected on arrival | `cancel <msg-id>` | SHOULD carry the target's `Newsgroups`; MUST carry `Approved` in a moderated group; "not required to contain From and Sender header fields matching the target" (2229) |
| Supersedes field | §5.4 (2234-2257) | withdraw the named Message-ID exactly as a cancel would; the carrying article itself is a normal article | `Supersedes: <msg-id>` (not a Control verb) | SHOULD get the same authentication checks as cancel |
| `newgroup` | §5.2.1 (2006-2097) | create the group, or change its moderation status or description | `newgroup <name> [moderated]` | body SHOULD carry `application/news-groupinfo`; an unrecognized flag SHOULD make the server ignore the message (2031) |
| `rmgroup` | §5.2.2 (2098-2110) | remove the group from the list of valid groups | `rmgroup <name>` | body free text |
| `checkgroups` | §5.2.3 (2111-2196) | make the hierarchy's group list exactly the body's list: add, remove, update descriptions and moderation | `checkgroups [chkscope] [#chksernr]` | `chksernr` MUST increase; servers SHOULD remember the last honoured one per scope and decline a smaller or absent one (2160) |
| `ihave`, `sendme` | §5.5 (2259-2314) | a UUCP-era offer/request protocol, NNTP's predecessor | `ihave <msg-id>... <relayer>` | "News servers are not required to support them" (2264) |
| `sendsys`, `version`, `whogets`, `senduuname` | §5.6 (2316-2322) | obsolete | | "SHOULD NOT be sent or honored" (2319) |

All group control messages (§5.2, lines 1982-2004) "MUST have an Approved
header field" and without one "SHOULD NOT be honored" (1994); before honouring
one, an agent "MUST check the newsgroup or newsgroups affected ... and decline
to create any newsgroups not in conformance with" RFC 5536 §3.1.4 (1991). For
relaying, newgroup/rmgroup SHOULD be relayed when both peers relay a group of
that name whether or not it exists (§3.6, lines 1035-1040), and a relaying
agent SHOULD reject an article matching an honoured cancel or Supersedes
(§3.6 item 5, line 1081).

**The RFC's own statement on authentication (§5.1, lines 1950-1980).**
"There is, at present, no standardized means of authenticating the sender
of a control message or verifying that the contents of a control message
were sent by the claimed sender" (1954); agents "SHOULD take steps to
authenticate control messages before acting on them, as determined by local
authorization policy" (1967), by an unstandardized protocol such as
PGPVERIFY, another protocol, human review "or by some other means"; and "No
Netnews agent is ever required to act on any control message ... an agent MAY
always decline to act on any given control message" (1976-1980). §6.1
(lines 2340-2400) adds that "many sites are ignoring all cancel control
messages and Supersedes header fields due to the difficulty of authenticating
them and their widespread abuse" (2359) and that the `Control` field's
contents are "potentially untrustworthy and malicious".

So every fn choice below is one of three things, labelled as such: an **RFC
requirement** (a MUST/SHOULD fn keeps), a **stronger fn guarantee** (fn
keeps more than the RFC asks), or a **local policy** (§5.1's "local
authorization policy", which the RFC leaves to the site).

## 2. fn's design

### 2.0 Why this does not contradict substrate transport §7

That section's objections, and the answer each gets here:

- *"An article is not an instruction"* (`docs/architecture.md:159-162`: an
  untrusted article cannot change configuration or erase another article "by
  naming it"). It still is not. The instruction is the operator's grant, a
  configuration row this node holds (§2.3); the article is signed evidence
  that the granted principal asked, and it acts only inside the grant.
- *"Unsigned control is a remote root shell."* Nothing unsigned, nothing
  `:carried` (D23) and nothing from a principal without a grant executes.
- *"Signed control is still last-writer-wins."* pgpverify signs a
  canonicalised subset; fn's carrier signs the exact authored source
  (`specs/identity.md:269-292`), which keeps the `Control` and `Approved`
  fields byte-exact (step 4: "Every other field is kept"). Ordering between
  two group changes is the authority's own signed serial (§2.6), never arrival
  order or a clock. Withdrawal is monotone, so it needs no order. Conflicting
  control articles are all retained as evidence.
- *"`cancel`: nothing. D03."* D03 stands: a withdrawal hides, it never erases
  (§2.5). Retention keeps every byte and the history keeps the Message-ID.

### 2.1 Rules that hold for every verb

1. **Recognition is ACL2's.** `fn-ctl-classify` (proposed,
   `books/control.lisp`, prefix `fn-ctl-` to be registered in
   `docs/prefixes.md`) takes the parsed article and returns `:ordinary`,
   `(:control verb args)` or `(:malformed reason)`. It reads only the
   `Control` field: a `cmsg ` Subject, a `.ctl` group and `Also-Control` never
   make an article a control message (RFC requirement, §5 line 1941). fn does
   not reject the ambiguous `cmsg` form (the RFC's MAY is not taken). An
   article with both `Control` and `Supersedes` is `(:malformed
   :control-and-supersedes)` (RFC 5536 §3.2.3's MUST NOT). The parser's
   existing bounds apply before any argument is read (RFC 5537 §6.1's "shell
   code in the Control header field").
2. **Filing, never the named groups.** A control article is filed into
   `control.<verb>` (`control` for an unknown or obsolete verb) when the
   operator created that group, and otherwise refused with a distinct reason
   `:control-not-filed` (441 on POST, 439 on TAKETHIS, 437 on IHAVE). It is
   never indexed in the groups its `Newsgroups` field names (RFC 5537 §3.7's
   SHOULD, line 1136, kept as a requirement). The article's bytes, including
   `Newsgroups`, are stored unchanged. `control.*` names are creatable under
   the existing local-agreement profile (`books/native-admin.lisp:519-531`,
   decisions 2026-09-24 "specific-purpose group names").
3. **No execution without retained evidence.** An executed control article
   is durably accepted first (or in the same composite event); its record is
   the provenance every effect cites. A refused control article executes
   nothing.
4. **Execution needs a verified principal and a grant.** The acceptance
   plan's verdict must be `:ok` from `fn-pa-current-plan`
   (`books/peer-authored-accept.lisp:98-126`): verified under *this* node's
   current enrollment. `:carried` (D23, `specs/identity.md:186-205`) never
   executes, since this node verified nothing; `:absent` (unsigned) never
   executes. The verified principal must hold a control-authority row
   (§2.3) naming the verb and covering the namespace. This is §5.1's "local
   authorization policy", and signature verification is fn's "other means".
5. **Decided once, recorded, replayed.** The execution decision is made under
   the configuration generation the accepting connection pinned and is
   written as a durable record. Recovery replays the record and never
   re-evaluates today's grants or keyring, just as an accepted verdict is
   historical (`specs/identity.md:48-80`). Revoking a grant changes future
   decisions, not past records (the K7 pattern of peering §4).
6. **Three outcomes stay distinct.** Every control article's effect is one of
   `executed`, `declined REASON` (filed as evidence, no effect) or `refused
   REASON` (not stored). The operator's `control log` view and the `HDR
   :fn-control` metadata item (§4) keep them distinct.
7. **The receiver decides again.** A relayed control article carries its
   carrier intact. The next node runs rules 1 to 6 under its own grants and
   keyring (§3).

### 2.2 The authority row (a new configuration row kind)

A grant is a durable configuration row in a new eighth slot `authorities` of
the configuration value (today seven slots: groups, capacity, quotas,
policies, listeners, peers, limits; `books/config.lisp:686-760`), written by
two new delta kinds after `:remove-peer` 10 (`books/config.lisp:571-600`):

| Delta | Code | Row | Admissible when |
| --- | --- | --- | --- |
| `(:grant-control namespace principal verbs)` | 11 | `(namespace principal-hex verbs 0)`, upserted on the pair (namespace, principal) | `namespace` is a group name or a group name followed by `.*`, and not reserved (`fn-native-admin-group-name-reservedp`); `principal-hex` is the 64 lowercase hex characters `fn-pa-carriesp` already compares (`books/peer-authored-accept.lisp:78-83`); `verbs` a nonempty subset of `cancel newgroup rmgroup checkgroups`; and no *other* principal holds a row with a group verb over an overlapping namespace (`:overlapping-authority`) |
| `(:revoke-control namespace principal)` | 12 | removes that row | the row exists (`:no-such-grant`) |

The operator grants through the assured live path: a native verb
`control grant NAMESPACE PRINCIPAL VERBS` / `control revoke NAMESPACE
PRINCIPAL`, planned by `fn-native-admin-plan` (`books/native-admin.lisp:568`)
and staged as `(:reconfigure id deltas)` through `fn-ocfg-step`, made durable,
and installed by `fn-ocl-publish` (`books/config-owner-publish.lisp:32`), so a
grant inherits both headline theorems
(`specs/reconfiguration.md:1262-1289`, restated over the called functions at
1359-1420) with no new crash cut. The overlap rule is a local policy that
gives every group one ordering authority (§2.6); cancel-only grants may
overlap, because withdrawal is monotone.

Why a new slot and not rows riding an existing one (as D23's
`carries-principal` rows ride the peers slot,
`books/peer-authored-accept.lisp:50-60`): a grant is keyed by namespace, not
by peer, and `:set-policy` upserts on its first label alone. The cost is the
configuration value's arity and codec (C2 builds the whole tree).

### 2.3 The authority decision

`fn-ctl-authorize (classified plan-verdict grants filed-groups)` returns
`(:execute verb basis)` or `(:decline reason)`, where the reasons are
`:unsigned`, `:carried`, `:no-grant`, `:verb-not-granted`,
`:outside-namespace`, `:no-approved` (group verbs; RFC 5537 §5.2 line 1994,
kept as a requirement), `:not-creatable` (§5.2 line 1991 via
`fn-native-admin-group-name-creatablep`), `:moderation-unsupported`,
`:no-serial`, `:stale-serial`, `:unsupported-verb`, `:obsolete-verb`. Refusals
(`:control-not-filed`, `:malformed`) happen earlier, in the acceptance plan.
`fn-ctl-authorize` is called from the acceptance plan for every ingress:
served POST, transit, and BP transit, the three callers of
`fn-pa-current-plan` (`specs/identity.md:173-205`). A local author cancelling
their own post over POST is the main use.

### 2.4 Per-verb table

| Verb | ACL2 decision function | Record or row written | Theorems (subject = the host-called function) | Teeth | Native tests |
| --- | --- | --- | --- | --- | --- |
| any | `fn-ctl-classify`, and the filing step inside the acceptance plan | none (filing is the group list of the acceptance event) | `fn-ctl-control-article-is-filed-only-in-control` over the acceptance plan the host calls: a classified control article's served groups are exactly `control.<verb>` or it is refused `:control-not-filed`; `fn-ctl-cmsg-subject-is-ordinary`; `fn-ctl-classify-reads-only-the-control-field` | a cancel naming `fn.test` with `control.cancel` configured is in `control.cancel` and not `fn.test`; must-fail without the filing step; a `cmsg cancel` Subject with no Control field is `:ordinary` | POST and TAKETHIS of a cancel with and without `control.cancel`: 240/239 into `control.cancel`, or 441/439 with the reason; LISTGROUP `fn.test` does not list it |
| `cancel`, Supersedes | `fn-ctl-authorize`, then `fn-ctl-withdrawal-effect` for visibility | a **withdrawal record** (a new Store record kind, §2.5), in the same composite event as the cancel's acceptance | over `fn-own-read` (the served port, `books/owner-invariants.lisp:1492`): `fn-ctl-withdrawn-article-is-430` and `fn-ctl-withdrawn-article-is-absent-from-every-listing`; over the acceptance plan: `fn-ctl-cancel-executes-only-for-author-or-authority`; over the store: `fn-ctl-withdrawal-preserves-retention` and `fn-ctl-withdrawal-preserves-history` | withdrawn article: 430 by Message-ID, 423 by number, absent from OVER/LISTGROUP/HDR/NEWNEWS; must-fails: canceller not the author and no authority; authority not covering one of a cross-post's groups; `:carried` canceller; retention ledger and history unchanged | author cancels own signed post; a stranger's signed cancel is declined `:no-grant`; an authority cancels an unsigned post; cancel before target; restart between (record survives, target still hidden) |
| `newgroup`, `rmgroup` | `fn-ctl-authorize`, then `fn-ctl-group-deltas` | a configuration record `(:reconfigure id deltas cause)` through `fn-ocl-publish`, or a **declined discharge** Store record (§2.6) | `fn-ctl-group-deltas-are-the-operators` (equal to `fn-ocl-request-deltas`, `books/config-owner-publish.lisp:25-30`, for the same kind and name); the headlines inherited over `fn-ocfg-step` and `fn-ocl-publish`; `fn-ctl-owed-is-discharged-exactly-once` over `fn-owner-recover` | serial 5 after 6 is `:stale-serial`; newgroup with `moderated` declined; must-fails: no Approved; group outside namespace; `:carried` | newgroup then a new connection's LIST ACTIVE shows it; rmgroup retires (the group's articles stay retained); kill the host between acceptance and the configuration record, restart: applied exactly once |
| `checkgroups` | `fn-ctl-checkgroups-report` (decision), `fn-ctl-checkgroups-deltas` (the operator's apply) | a **report** Store record; applying stages ordinary deltas through the operator's live path | `fn-ctl-checkgroups-never-reconfigures` over the acceptance plan; `fn-ctl-checkgroups-apply-is-the-report` over the apply plan | a report whose serial is below the last applied one is marked stale; a body group outside the `chkscope` is ignored (RFC 5537 §5.2.3's MUST honour chkscope) | report shown by `control reports`; `control apply-checkgroups MSGID` changes the table; nothing changes without it |
| `ihave`, `sendme`, obsolete, unknown | `fn-ctl-classify` (verb recognized, never granted) | none | covered by the first row plus `fn-ctl-authorize-never-executes-unsupported` | an ihave from a granted principal is still declined | TAKETHIS of an `ihave` control article files it in `control.ihave` or refuses it |

### 2.5 cancel: a withdrawal record, a hidden view, every byte kept

**The record.** A new Store record kind in a new `control` family beside
retention, identity, consumer and topic (`books/store-node.lisp:1109-1200`):

    (:withdrawal target-msgid canceller-principal basis reason cause-msgid)

`basis` is `:author` or `(:authority namespace generation)`, `reason` the
cancel's body truncated to a fixed bound (a local policy bound, stated with
its number in the packet), and `cause-msgid` the cancel article. It is
written **in the same composite event** as the cancel article's kind-4
acceptance (the composite pattern of `fn-sn-composite-delta`,
`books/store-node.lisp:1294`), so no crash leaves an accepted, executable
cancel without its decision, and there is no new crash cut. Supersedes
writes the same record with the superseding article as cause, and the
superseding article is otherwise ordinary (RFC 5537 §5.4, SHOULD, kept).

**The exact-source rule (a stronger fn guarantee than the RFC, which
requires no From match: §5.3 line 2229).** A withdrawal takes effect on a
target T exactly when either

- `basis = :author` and T's stored verdict names the canceller's principal:
  `:ok` (verified here) or `:carried` (the carrier names it). If T was a
  forgery carrying P's name, P withdrawing it is still P's right; or
- `basis = (:authority ns g)` and every group in T's `Newsgroups` that this
  node serves lies in `ns`. An authority may not withdraw a cross-post from
  a group outside its grant.

An unsigned T can only be withdrawn by an authority.

**Cancel before target.** RFC 5537 §5.3 says to remember the Message-ID and
reject the target on arrival. fn keeps the "remember" and replaces "reject"
with accept-and-hide. `fn-ctl-withdrawal-effect` is a pure function of the
withdrawal record and T's acceptance record, so when T arrives its
acceptance is ordinary: it is retained as evidence, and the served view hides
it if the rule above holds. This is a local policy that departs from a SHOULD,
for two reasons: the author rule cannot be decided before T's verdict exists,
and D03 keeps evidence. A withdrawal whose target never arrives stays a
record with no effect.

**What a reader sees (RFC 3977).** The article no longer exists for a
reader, so the RFC's own codes are the answer. By Message-ID, ARTICLE, HEAD,
BODY and STAT answer **430** ("If the argument is a message-id and no such
article exists, a 430 response MUST be returned", §6.2.1.2, rfc3977.txt:2622).
By number they answer **423**. §6.2.1.2 allows this: "a previously valid
article number MAY become invalid if the article has been removed"
(rfc3977.txt:2603). The number is never reused. OVER/XOVER, LISTGROUP, HDR,
NEWNEWS, NEXT and LAST skip it, and GROUP's count may drop (RFC 3977 §6.1.1
allows estimates). The 430 line's text is `430 withdrawn`. RFC 3977 §3.2
(rfc3977.txt:496-499) says "the client MUST NOT make decisions based on this
text", so the text is for people. The machine-readable signal is the `HDR
:fn-control` item on the cancel article (§4). **Decided: hide, not serve with
an X-header.** Serving the bytes with a marker would not "make the article
unavailable to reading agents" (RFC 5537 §5.3, 2211), and it would edit
served bytes that `ARTICLE` promises unchanged (`specs/nntp.md:52-62`). The
bytes stay reachable to the operator through a read-only native `control
evidence MSGID` verb, not through a reader port.

**How the view hides without whole-state revalidation.** The withdrawal
records sit in the same ordered Store journal as the acceptances, so the
prefix a connection pins (`fn-own-take version records`,
`books/owner-invariants.lisp:1492-1522`) decides the archive and the
withdrawal set together, and no reader sees half a cancel. The filter
applies once, where the committed view is refreshed (`fn-own-refresh`,
`books/owner.lisp:815`). There, the served archive becomes
`fn-ctl-visible-archive` of `fn-node-acceptance` and the withdrawal set,
and the Message-ID trie (`fn-midx-refresh`, `books/msgid-index.lisp:191`) and
the group buckets are built over the filtered archive. The existing
trie/bucket correspondence then holds over it unchanged, and no command pays
per-command cost ("No whole-state revalidation on a served path", AGENTS.md).
The refresh is incremental in the new records, like `fn-midx-refresh`'s
old/new pair. Existing connections keep their pinned archive until they
advance (`specs/nntp.md:156-160`), exactly as for a new article.

**What is not hidden.**

- *Retention* keeps the pin: a withdrawal is not `fn-retain-release`
  (`books/retention.lisp:204`), charges nothing and releases nothing. D03
  (`planning/decisions.md:211-217`) and RET-005's "Withdrawal, cancellation,
  visibility, and physical deletion are distinct" (`specs/retention.md:153-157`)
  are both kept.
- *History* keeps the Message-ID. Transit duplicate suppression reads the
  unfiltered node (`fn-peer-history-hasp`, `specs/peering.md:568-576`), so a
  re-offer of a withdrawn article is 435/438 forever. That is RFC 5537 §3.6
  item 5 (line 1081) met by the history rather than by a separate cancel
  cache.
- *Feed*: see §3.

### 2.6 newgroup and rmgroup: the operator's `:reconfigure`, with a signed order

**Same event.** `fn-ctl-group-deltas` produces, for `newgroup NAME` and
`rmgroup NAME`, exactly `fn-ocl-request-deltas :create-group NAME` and
`fn-ocl-request-deltas :remove-group NAME`
(`books/config-owner-publish.lisp:25-30`). Those are the delta lists the
operator's `group create` / `group retire` stage today
(`specs/reconfiguration.md:1359-1366`). The owner stages them as
`(:reconfigure id deltas)` through `fn-ocfg-step` and publishes them with
`fn-ocl-publish`. Both headline theorems quantify over the staged record, so
"no reader observes a half change" and "a crash at any instant recovers the
live generation" hold for a control-caused change with no restatement. What
is new is proved in §2.4's row: the delta equality, and the owed discharge
below. `rmgroup` retires; it never deletes. `:remove-group` only sets
`retired-gen` (`specs/reconfiguration.md:184`, 429), and the group's articles
stay retained and served below its retiring generation (`fn-cstr-`,
`docs/prefixes.md:154`).

**The one new crash cut, and the owed set.** Acceptance of the control
article (Store journal) and the configuration record (configuration
journal) are two durable writes. The process can die between them. By
AGENTS.md's crash rule ("Every process-death cut is a model crash point"),
that cut is modelled rather than argued away. The accepted, authorized
control article is itself the persisted obligation. Its **discharge** is
exactly one of:

- the configuration record, whose new `cause` field names (Message-ID,
  principal, serial); operator records carry `cause nil`; or
- a **declined discharge** Store record `(:control-declined msgid reason)`
  when publication refuses the delta (for example `:duplicate-group` because
  the operator already created the group).

`fn-ctl-owed` over the recovered journals is the set of executable group
control articles with no discharge. `fn-owner-recover` re-stages each owed
entry, and `fn-ctl-owed-is-discharged-exactly-once` states that no Message-ID
is discharged twice across any crash and restart sequence.

**Order: the authority's signed serial, never arrival.** Newgroup X then
rmgroup X, arriving in opposite orders at two nodes, must not leave them
different. fn requires a group control article to carry
`FN-Control-Serial: 1*DIGIT`. It is an fn-reserved field (registered in
`specs/nntp.md`'s reserved-field table), deliberately **not** in
`fn-hc-reserved-namep` (`books/hybrid-carrier.lisp:139-147`), so it stays
inside the signed authored source. Serials compare as RFC 5537 §5.2.3
recommends for `chksernr`: zero-pad and compare as strings (lines 2166-2170).
A group change executes only if its serial exceeds the high-water for (grant,
group), and the high-water is read from the discharge records. So given the
same articles and the same grants, every node reaches the same group state
whatever the arrival order: the highest serial wins, and every lower one is
declined `:stale-serial` and retained. With one ordering authority per group
(§2.2's overlap rule), the serials are comparable. A missing serial is
`:no-serial`. This is a local policy. The RFC defines a serial only for
checkgroups, and legacy servers ignore an unknown field, so fn's group
control articles still honour their RFC grammar for them.

**What fn declines.** `newgroup NAME moderated` is declined
`:moderation-unsupported`: fn has no moderation (`specs/nntp.md:701`), and
honouring the create without the flag would contradict §5.2.1's SHOULD
(line 2026). The `application/news-groupinfo` description is ignored,
because the group table stores no description (`specs/nntp.md:109-112`). A
name that fails `fn-native-admin-group-name-creatablep` is declined
`:not-creatable` (RFC requirement, §5.2 line 1991).

### 2.7 checkgroups: a report, never automatic

An authorized checkgroups article writes a **report** Store record: scope,
serial, and the typed list of groups the body names, parsed by ACL2 under a
fixed bound. An unauthorized one is declined as usual. Nothing changes the
group table. `control reports` lists each report with the delta list
`fn-ctl-checkgroups-deltas` would stage against the *current* configuration
(adds, retirements, and the moderation and description differences fn
declines, listed as such). `control apply-checkgroups MSGID` stages that
list through the operator's ordinary live path, with the operator as the
authority of record. The chksernr rule (RFC 5537 §5.2.3, line 2160, a SHOULD
kept) is part of the apply plan: `:stale-serial` when a later report for the
same scope was already applied.

### 2.8 ihave, sendme, obsolete and unknown verbs

These are filed if `control.<verb>` (or `control`) exists and are otherwise
refused. They are never executed. fn relays by NNTP streaming (RFC 4644) and
IHAVE (RFC 3977 §6.3.2), and RFC 5537 §5.5 says servers need not support these
verbs (line 2264). §5.6's obsolete verbs "SHOULD NOT be ... honored", and
unknown verbs are "ignore[d]", as §5 line 1936 allows.

## 3. The feed and an executed control article

- **Relayed as an article.** A filed control article (executed or declined)
  is an ordinary stored article, and the feed offers it like any other: FNFD
  journal, CHECK-first, exactly-once per peer (peering K5), with its bytes
  and its `FN-Authorship` carrier intact (`specs/identity.md:196`: "Its
  feed relays the stored octets, carrier intact"). Its feed group is
  `control.<verb>`. A peer's `feed-groups` must name it, and RFC 5537 §3.6's
  exception for newgroup/rmgroup (relayed when both sides relay the *named*
  group, lines 1035-1040) is kept as a local policy by letting a peer's
  feed-group match on either the filing group or the named group for those
  two verbs.
- **The receiver decides again.** The receiving fn runs §2.1 under its own
  keyring and grants. The sender's execution is not an input: no field says
  "executed", and a withdrawal or discharge record is never fed. A receiver
  that has not enrolled the canceller holds the cancel as `:carried` (if its
  boundary lists the principal, D23) or refuses it `local-enrollment`, and
  executes nothing either way (§2.1 rule 4). This is D23 ("carriage is not
  authority", `planning/decisions.md:1067-1078`) applied to control.
- **The withdrawn target.** The first cut keeps offering an already-enqueued
  withdrawn target, because the cancel travels beside it and each receiver
  decides for itself. RFC 5537 §3.6 item 5 is a SHOULD on the *receiving*
  relay, and a legacy peer that honours the cancel refuses the target. Not
  offering a withdrawn target (a distinct FNFD settlement `:withdrawn`, not
  `:sent`) is an open item. It touches K5's statement, and it is not in the
  four packets.

## 4. The independent verifier and the web client

- **A new metadata item, `HDR :fn-control`.** RFC 3977 §8.5 permits it, as
  it permits `:fn-verified` (`specs/identity.md:337-340`). It is answered for
  articles in `control.*` with one of `executed withdrawal <target-msgid>
  author|authority`, `executed reconfigure generation <n>`, `owed`,
  `declined <reason>`, or `report <serial>`. Like `:fn-verified`, it is the
  node's historical claim, not a signature check.
- **`tools/fn_verify.py`.** A withdrawn target answers 430 to ARTICLE and to
  `HDR :fn-verified` (`tools/fn_verify.py:444-458`), and today the tool
  treats that as "no article". With withdrawal, the tool (given the cancel's
  Message-ID) verifies the cancel article's carrier against its own pins,
  exactly as for any article, and checks that the signed `Control` line names
  the target. If the caller holds a copy of the target, the tool also checks
  that its carrier principal equals the canceller's (the author basis). It
  reports this beside the node's `:fn-control` claim and exits 2 on a
  disagreement, as for `:fn-verified`. The authority basis cannot be checked
  independently, because the grant is this node's configuration, which is a
  local-policy limit of the same kind as the one `specs/identity.md:371-374`
  already states.
- **Web client.** A thread whose `References` names a withdrawn article
  shows a grey "withdrawn" placeholder where the parent would be, with the
  pill `withdrawn by author` or `withdrawn by authority`, only when a
  `:fn-control` line for a cancel in `control.cancel` names that Message-ID.
  Otherwise it shows the existing "unavailable" (`docs/web.md:109-112`). The
  pill is labelled the node's report, like the verdict pill. The client
  never shows withdrawn bytes: it has no reader-port way to get them.

## 5. Ranked packets (at most four)

Each packet certifies its books, their test books and their closure before it
reports (AGENTS.md, "Behaviour and its invariants land together"). Each one
that touches the configuration value or the Store record shape builds the
whole tree.

1. **C1: recognize and file (no execution).** `books/control.lisp` with
   `fn-ctl-classify` and the filing step in the acceptance plan for all three
   ingresses. It fixes §0's finding and makes peering and substrate
   transport's sentence true. *Dependents touched:* the acceptance plan's
   group list at the served POST, transit and BP ingress call sites
   (`fnn-owner-attempt-served`, host/native/owner.lisp; `fn-pa-current-plan`'s
   callers), `specs/nntp.md` reason lines, `tests/acl2/control-tests.lisp`.
   *Theorems:* `fn-ctl-control-article-is-filed-only-in-control` (over the
   acceptance plan the host calls), `fn-ctl-cmsg-subject-is-ordinary`,
   `fn-ctl-classify-reads-only-the-control-field`; teeth as in §2.4 row 1.
2. **C2: authority rows and the decision.** The `authorities` slot, delta
   kinds 11 and 12 with admissibility and codec round trip, the native
   `control grant|revoke` verbs, and `fn-ctl-authorize` called from the
   acceptance plan, whose result so far is only recorded (`declined` or
   `would-execute`, the latter not yet acted on). *Dependents touched:*
   `books/config.lisp` (value arity, apply, admissibility, codec),
   `books/config-invariants.lisp`, `books/native-admin.lisp`,
   `specs/reconfiguration.md` §1.5's table. *Theorems:*
   `fn-ctl-authorize-requires-verified-verdict` (`:carried` and `:absent`
   never execute; must-fail with a carried witness),
   `fn-ctl-authorize-requires-a-grant-covering-the-namespace`,
   `fn-cfg-grant-control-admissible-iff` (with `:overlapping-authority`),
   `fn-ctl-revoke-changes-decisions-not-records`, and the two headlines
   re-certified over grant deltas.
3. **C3: cancel as a withdrawal record and a hidden view.** The withdrawal
   kind in a composite with the cancel's acceptance, `fn-ctl-withdrawal-effect`
   with the exact-source rule, `fn-ctl-visible-archive` at `fn-own-refresh`,
   the 430/423 text, `HDR :fn-control`, and Supersedes. *Dependents touched:*
   `books/store-node.lisp` (a record family), `books/owner.lisp`
   (`fn-own-refresh`, `fn-own-start`), `books/owner-invariants.lisp` (K1
   restated), the NNTP retrieval books, `tools/fn_verify.py`, the web client.
   *Theorems, restated over the host-called `fn-own-read`:*
   `fn-own-read-is-served-step-on-visible-pinned-prefix` (the K1 statement at
   `books/owner-invariants.lisp:1492` with `fn-ctl-visible-archive` around
   the acceptance projection), `fn-ctl-withdrawn-article-is-430`,
   `fn-ctl-withdrawn-article-is-absent-from-every-listing`,
   `fn-ctl-cancel-executes-only-for-author-or-authority`,
   `fn-ctl-withdrawal-preserves-retention` (ledger equal before and after),
   and `fn-ctl-withdrawal-preserves-history` (`fn-peer-history-hasp`
   unchanged).
4. **C4: newgroup and rmgroup through `fn-ocl-publish`.** `fn-ctl-group-deltas`,
   `FN-Control-Serial`, the `cause` field on configuration records, the
   declined-discharge record, `fn-ctl-owed`, and re-staging in
   `fn-owner-recover`. *Dependents touched:* `books/config-records.lisp`
   (record codec: `cause`, with old records decoding as `cause nil`),
   `books/config-owner-publish.lisp`, `books/config-crash-replay.lisp`,
   `host/owner-host.lisp:173` (recovery re-stage), and `specs/nntp.md`'s
   reserved-field table. *Theorems:* `fn-ctl-group-deltas-are-the-operators`
   (equal to `fn-ocl-request-deltas`), the headlines
   `fn-ocl-no-reader-observes-a-half-change` and
   `fn-ocl-crash-at-any-instant-recovers-the-live-generation` re-certified
   with `cause`, `fn-ctl-owed-is-discharged-exactly-once` over
   `fn-owner-recover` with the kill between acceptance and configuration
   record as a model crash point, and `fn-ctl-serial-order-is-arrival-independent`
   (two arrival orders of one article set give one group table).

Deferred behind these four: the checkgroups report and apply (§2.7), feed
suppression of a withdrawn target (§3), and an operator `withdrawal lift`
(reinstatement, which RFC 3977 §6.2.1.2 permits at a number no lower than the
low water mark).

## 6. Questions for ember

1. Is a signed serial field (`FN-Control-Serial`, §2.6) acceptable, or
   should group control stay operator-only (C4 dropped) until D11 decides
   who owns a group's identity?
2. Should cancel-before-target *refuse* the target (RFC 5537 §5.3's SHOULD)
   rather than accept-and-hide? This design hides it, because the author
   rule needs the target's verdict and D03 keeps evidence.
3. May an authority withdraw an *unsigned* article (legacy gateway
   provenance)? This design says yes, within its namespace.
