# usenet-headers (2026-09-26): group descriptions and LIST MOTD (PRF-195, NNT-039, SCN-124)

Lane `lane/usenet-headers` from dev `8dc094f93`, Opus, launched by deputy 4 on
the coordinator's order (gap inventory items R2, R5, O1, R3, P2:
`planning/nntp-gap-inventory-2026-09-26.md` on `lane/nntp-gap-inventory`).
Done: **R2 + R5 + O1**. Not done: **R3 (Xref)** and **P2 (Injection-Info)**,
recorded as PKT-573 with their designs, and PKT-574, the decision P2 needs.

Configuration delta kind code taken: **20, `:set-group-description`** (dev at
launch ended at 19 `:remove-peer-rows`; no lane branch held 20). No store format
number, FNCT/FNLS kind or migration: the configuration value is replayed, never
written (`books/config.lisp` header), so a store written before this lane
replays with an empty slot, and a record carrying code 20 is refused by an
older binary's decoder as an unknown kind.

## What a reader and an operator see

- `fn operator CONFIG group describe NAME [TEXT ...]` sets NAME's description
  (the words joined by one space; none clears it);
  `fn operator CONFIG motd set LINE [LINE ...]` and `motd clear` set the
  node's message. Each publishes one configuration record with one
  `:set-group-description` delta; a running owner applies it over the
  control socket like `group create`, and restart replays it.
- `LIST NEWSGROUPS [wildmat]` (RFC 3977 §7.6.6) shows `name TAB description`,
  or `name TAB (no description)` for a group with none (the marker, unchanged).
- `LIST MOTD` (RFC 6048 §2.5; the brief cited "§3.1", the RFC's section is
  2.5) answers 215 with the message's lines, an empty block when none is set,
  501 with an argument. CAPABILITIES' LIST line gains `MOTD`.

RFC requirement / stronger fn guarantee / local policy are separated in
`specs/nntp.md` "Group descriptions and the message of the day (NNT-039)".

## Assurance chain

native entry `host/native/owner.lisp` -> `fn-owner-chunk` (host/owner-host.lisp)
-> `fn-served-step` (the executed subject) -> `fn-served-dispatch` ->
`fn-auth-step-pinned` -> `fn-peer-step-pinned` -> `fn-nntp-post-step-pinned`,
which builds the reader environment `fn-nntp-env-listed` with the connection
posting configuration's listing -> `fn-nntp-step-pinned` ->
`fn-nntp-archive-command-pinned` -> `fn-nntp-list-command` ->
`fn-nntp-list-newsgroups-described` / `fn-nntp-list-motd`.

- The relation: the connection's posting configuration is the owner's
  `fn-oag-post-config` of the live configuration (host/owner-host.lisp
  `fn-owner-post-config`; installed at recovery and by `fn-ocl-publish` after
  every published record, pinned into each connection at open by
  `fn-oag-open-pins-the-owner-config`, cited). `fn-owner-posting-configure`
  (host) and `fn-osb-config` (books/owner-served-bound.lisp) rebuild it and
  now carry the listing across (`fn-inj-make-config-listed`).
- Behavioural theorems (all certified, see manifests below):
  - `fn-served-step-list-newsgroups-is-the-described-listing`,
    `fn-served-step-list-motd-is-the-configured-message`
    (books/owner-descriptions-read.lisp): over `fn-served-step`, one framed
    LIST NEWSGROUPS / LIST MOTD line answers the described listing of the
    pinned archive's groups / the message, from
    `(fn-inj-config-listing (fn-served-conn-config conn))`. Same framing and
    session hypotheses as LIST COUNTS's keystone; no projection or bucket
    hypothesis (neither command reads articles).
  - `fn-oag-description-of-the-listing`, `fn-oag-motd-of-the-listing`: the
    listing of `fn-oag-post-config cfg` holds G's slot description exactly
    when G is served and has one, and the node's lines.
  - `fn-cfg-description-after-set-is-its-pieces`,
    `fn-cfg-description-after-set-of-another-name`,
    `fn-cfg-motd-after-set-is-its-lines`, `fn-cfg-descriptions-of-other-kinds`
    (books/config-descriptions.lisp), over `fn-cfg-apply-delta`, which replay
    and live staging both run. `fn-cfg-admitted-description-rows-are-printable`
    and `fn-cfg-set-group-description-refuses-an-unknown-group-by-definition`
    (renamed: the ledger flags it as a branch of `fn-cfg-delta-reason`).
  - `fn-nntp-described-lines-of-no-descs`: with no listing LIST NEWSGROUPS is
    the old marker listing. `fn-nntp-described-lines-are-response-text`,
    `fn-nntp-motd-lines-are-response-text`, `fn-nntp-effects-list-*`:
    every reply is well-formed NNTP.
  - `fn-inj-decide-ignores-the-listing` (books/injection.lisp): the listing is
    not an input of POST's injection decision.
- Observed result: `tests/test_native_reader_index.py`
  `test_list_newsgroups_descriptions_and_motd_published_live` (SCN-124): see
  "Native" below.

## Changed representation

- `books/config.lisp`: an eleventh value slot `fn-cfg-descriptions`
  (`fn-cfg-value-make-full`; the ten-argument `fn-cfg-value-make` keeps every
  caller and test book, with an empty slot), rows `(NAME PIECE "" 0)`, kind 20,
  its admission (`fn-cfg-set-group-description-reason`: `:no-such-group`,
  `:description-row`, `:description-blank`) and projections
  `fn-cfg-description-octets`, `fn-cfg-motd-lines`.
- `books/injection.lisp`: the posting configuration's fifth field
  `fn-inj-config-listing` (`fn-inj-make-config` builds one with none).
- `books/nntp-responses.lisp`: `fn-nntp-env` gains a fourth field,
  `fn-nntp-env-listed`/`fn-nntp-env-listing`; the new LIST arms.
- The env term changed in the served-chain restatements (nntp-post,
  nntp-auth-fold, nntp-pinned-effects, peer-offer-indexed,
  owner-list-counts-read, owner-control-read, owner-enrollment-read).
- `books/native-admin.lisp`: `group describe` / `motd` plans and deltas
  (`fn-native-admin-text-pieces` cuts a description into 256-octet pieces);
  `books/native-operator.lisp`: `motd` routed as administration, help text;
  `host/native-admin-host.lisp`: the offline executor's kind list.

D27: a description's length is bounded by the operator argv (16 words of 512
octets) and by what one configuration record represents, never by a row; a
message line is one row, 256 octets. Printable ASCII only (the argv is ASCII;
RFC 6048 asks UTF-8, of which this is a subset).

## Teeth (tests/acl2/group-descriptions-tests.lisp)

Reachable witness through `fn-config-replay` of the default record and a record
carrying both deltas; each keystone's positive case; `must-fail` of the
another-name theorem without its hypothesis plus its counterexample; the
other-kinds hypothesis fails at the description delta; for the admission
theorem each hypothesis's failure (live group admitted, "" admitted, another
kind, a non-delta `:malformed-delta`) and a retired group refused; a control
octet, a row keyed on another name, and spaces refused; the listing of
`fn-oag-post-config`; the pinned dispatcher's exact replies (wildmat, 501,
MOTD, blind env = old marker listing, empty MOTD); an unclean listed
description falls back to the marker; the operator plans (joined words, clear,
600-octet description cut into 3 pieces that replay to the joined octets,
blank, control octet, bad name, motd set/clear, 257-octet line, bare `motd`).

## Certification (persvati REPL tree, 2 jobs; NOT a batch manifest)

`planning/evidence/manifests/certify-20260926T182855Z-843486.json` (23 books
incl. owner-descriptions-read, served chain; native-admin red, fixed),
`certify-20260926T183221Z-884085.json` (native-admin, native-operator, test
book), `certify-20260926T183536Z-921899.json` (config-descriptions,
owner-descriptions-read, test book after the rename; 167 installed from the
cache at current digests). Earlier reds kept for the record:
`certify-20260926T182443Z-799789.json` (nntp-invariants' list-command
session lemma), `certify-20260926T182646Z-820709.json` (config-descriptions
hints, nntp-pinned-effects' env instance). Slowest changed book 9.78 s
(owner-invariants, unchanged source); every new book under 2 s.
Dependent test books (nntp-list-counts, nntp-auth, nntp-xpat, nntp-legacy, config, owner-agent, native-admin, injection, owner-served-bound, nntp-post, served): all passed, `certify-20260926T183626Z-932996.json`.

## Native

hbox, `tools/hbox_native.sh --label desc --images developer,production --env
FN_RUN_NATIVE_READER_INDEX=1 . tests.test_native_reader_index` on the lane tree
(the bytes of 4904bc529): `tests.test_native_reader_index: OK (6 ran, 0
skipped)`, `== modules: 1 OK, 0 SKIPPED, 0 FAILED`, the new case
`test_list_newsgroups_descriptions_and_motd_published_live ... ok` (2.47 s).
Module log sha256 `a924c542f91896fd545f7ffb1449e2034e6c73ee48a4adb6adb1123afd9a512d`
(copied to `planning/evidence/usenet-headers-2026-09-26-native.log`), run.log
sha256 `1258ab2aeb0b50d839d89955efbeb48788fb735fc5090297995c9635223aead1`, tree
hbox:/tank/fn/scratch/usenet-headers/native-desc (SHA256SUMS there). This is
the lane's one targeted module; the batch's image run is the claim.

## Not done (PKT-573) and the decision (PKT-574)

**R3, Xref:full.** Design: the ninth overview field `Xref: SERVER group:n ...`
(RFC 3977 §8.3.2 "full" form, RFC 5536 §3.2.14), SERVER the connection's
posting agent (`fn-inj-config-agent`, the path-identity by
`fn-oag-post-config-agent-is-the-path-identity`), the pairs the article's
`fn-article-memberships` restricted to available numbers
(`fn-nntp-article-number`), local numbers only; OVERVIEW.FMT gains
`Xref:full`. Rendered as overview metadata, never spliced into ARTICLE/HEAD
octets (peering §2.3 serves stored octets as held). The listing seam this lane
added carries it without another arity change: put the agent in
`fn-oag-listing` and read it from `fn-nntp-env-listing`. The work is
threading the environment into the OVER/XOVER arms
(`fn-nntp-over-range-indexed`, `fn-nov-lines-for-numbers`, `fn-nov-line`)
and re-proving their keystones (OVER = XOVER, indexed = fold, clean lines;
17 books name these functions). A lane.

**P2, Injection-Info.** Design: `Injection-Info: AGENT; posting-account="H";
mail-complaints-to="ADDR"` (RFC 5536 §3.2.8), H a keyed hash of the login, the
address from a durable `policy set complaints-to ADDR` slot (the
path-identity precedent; omitted when unset, never invented). It changes
`fn-inj-injection-info-line`, the D25 inverse `fn-inj-source-of` (which must
still recognize the one-agent line every stored article carries: no
migration), `fn-oag-names-agentp` (an infix of `AGENT CRLF` today), and needs
the login threaded from the auth session into `fn-inj-decide`, and a keyed
hash through the crypto seam. A lane after PKT-574.

**PKT-574 (decision for ember): where the posting-account key comes from.**
Trace: RFC 5536 §3.2.8 posting-account; the operator must be able to answer a
friend about their own post, and a stranger must not recover the login.
Constraints: no key in a configuration record (`show` prints them, backups
and checkpoints replay them); no migration; D35 (no Python). Default: a
32-octet secret generated at `init` into the node's key directory beside the
signing keys, read by the owner at start; rotation changes later values only.
Rejected: deriving it from the node's signing secret (ties the account hash to
key succession, and a signing-key compromise then also reveals logins by
dictionary); an unkeyed hash (a stranger can test candidate logins). Affected:
`books/injection.lisp`, the injected block's inverse, `fn-oag-post-config`.
What continues without it: everything in this lane, and R3.
