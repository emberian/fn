# reader-clients (2026-09-26)

Lane reader-clients, from the NNTP gap inventory
(`planning/nntp-gap-inventory-2026-09-26.md` on lane/nntp-gap-inventory,
sections 2 and 3): pan and Thunderbird in the v0 matrix, R4 (HELP), O5 (two
stale operator.md passages) and the R1 probe (measurement only). Ids:
PRF-194, NNT-038, SCN-123, PKT-571. PKT-572 was not needed.

## 1. pan and Thunderbird in the v0 matrix

Eight rows, `V0-CLIENT-{THUNDERBIRD,PAN}-{READ,REPLY,POST,CANCEL}`
(`tools/v0_matrix.py`, phase `reader_clients`, run after `tin_client`).
Verdicts come only from the node's reply lines between `--- action NAME`
markers (`client_wire_outcomes`, tested by `tests/test_v0_matrix.py`
`ClientWireTests`). No client-specific server behaviour was added.

Driver: `tools/reader_clients_phase.py` starts a scratch owner through
`packaging/fn-native` with an implicit-TLS listener (a scratch CA, SAN
`IP:127.0.0.1`), `[auth] required`, `protected_only`, groups
`local.general control.cancel`; issues an invitation (`operator CONFIG account
invite`); a stdlib prelude verifying the scratch CA sends `XREDEEM CODE LOGIN`
and `XREDEEM PASS`, then logs in with AUTHINFO on a new connection and posts a
seed. `tools/thunderbird_drive.py` (stdlib Marionette client) drives
Thunderbird 156.0 (snap, `--headless --marionette`) on a fresh profile.

Trusting the scratch CA (Thunderbird): in chrome context
`nsIX509CertDB.addCertFromBase64(<CA DER base64>, "C,,")` makes the CA an SSL
trust anchor in the profile's NSS store; the node's certificate is then
verified, not overridden (no `cert_override.txt`). The account is created
through `MailServices.accounts` (socketType SSL, `always_authenticate`), the
login in the login manager. Read: `getNewMessages` then `streamMessage`.
Reply and post: a real compose window (`cmd_sendNow`). Cancel:
`cancelMessage(hdr, urlListener, msgWindow)` with `news.cancel.confirm=false`.
The wire is Thunderbird's own NNTP logger (`mailnews.nntp.loglevel=All`, the
node's replies after decryption), secrets redacted.

The run: persvati, image `fn-host` from hbox `qual-69046a76` (dev behaviour;
the client rows do not depend on this lane's HELP change), system libssl
3.5.3. Wire log `persvati:/home/ember/fn-scratch/reader-clients/run-20260926/thunderbird-wire.log`
sha256 `01e892fb1860dc69a5b133af53365f2e7b8256a687a37615b0f10fda5bed1d7c`;
`phase.json` sha256 `d215eefcc84067db94dea9a38f9445f5971a0e40194185f9bd182d50ac070438`.

| row | verdict | the node's reply line |
| --- | --- | --- |
| prelude redeem | accepted | `381 send the password with XREDEEM PASS`, `281 account bound; authenticate with AUTHINFO on a new connection` |
| Thunderbird login | accepted | `381 password required`, `281 authentication accepted` (over TLS) |
| V0-CLIENT-THUNDERBIRD-READ | accepted | `220 1 <seed-thunderbird-3bb204b7@matrix.example.invalid> article follows` |
| V0-CLIENT-THUNDERBIRD-REPLY | accepted | `340`, `240 article received OK`; the node's XOVER serves References = the seed |
| V0-CLIENT-THUNDERBIRD-POST | accepted | `340`, `240 article received OK` |
| V0-CLIENT-THUNDERBIRD-CANCEL | accepted (filed; no effect) | `240 article received OK`; HEAD of the target stays `221`: an unsigned cancel from a newsreader carries no authority (the inventory's P1) |
| V0-CLIENT-PAN-{READ,REPLY,POST,CANCEL} | not exercised | see below |

pan: unexercised. pan 0.162 runs without root on persvati (`apt-get
download` pan, libgspell-1-3, libgmime-3.0-0t64; `dpkg -x`), but `pan
--no-gui news:MID` exits 0 in 0.1 s without opening a socket (strace), the GUI
under xvfb rejects the node's certificate ("no known issuer") even with the CA
in `PAN_HOME/ssl_certs`, and `--debug --debug` logs no NNTP lines. It would
need xdotool (unpackable the same way) plus a way to read window state, pan's
certificate-trust format, and a TLS-terminating relay for a transcript
(`PAN_BLOCKER` in tools/v0_matrix.py).

Where these rows can run: only persvati has Thunderbird; on hbox the
Thunderbird rows come out not exercised. `planning/v0-matrix.json` carries the
eight rows as planned (`--plan-rows`); the observed verdicts above are this
record's.

Findings for later lanes (not fixed here):
- A Thunderbird reply's stored subject lacks "Re:" (Thunderbird keeps a flag);
  the phase's follow-up HEAD lookup was fixed to use the flag after the run and
  has not been rerun.
- Before login, the greeting is `201` (this connection may not post yet) and
  `MODE READER` answers `200 posting allowed` on the same connection. The
  greeting keystone (PRF-039) ties the greeting to the POST label; MODE
  READER's answer is not tied to the authentication state. PKT-571.
- A plain newsreader cancel is filed and does nothing (inventory P1).

## 2. R4: HELP lists the served command table (PRF-194, NNT-038, SCN-123)

HELP (RFC 3977 section 7.2) listed only books/nntp.lisp's reader verbs. It
now prints the six rows of `*fn-nntp-served-command-table*`
(books/nntp-help.lisp): `CAPABILITIES HELP QUIT MODE DATE POST`, `AUTHINFO
STARTTLS XREDEEM`, `GROUP LISTGROUP LIST NEXT LAST NEWGROUPS NEWNEWS`,
`ARTICLE HEAD BODY STAT`, `OVER XOVER HDR XHDR XPAT`, `IHAVE CHECK TAKETHIS`.
RFC requirement: HELP exists, text free. fn guarantee: the list is exact.
Local policy: the grouping and order. HELP's text is the only served-byte
change.

Assurance chain: native entry host/native/owner.lisp `fnn-owner-serve-client`
-> `fn-own-read` -> `fn-served-step` -> `fn-served-feed` ->
`fn-served-dispatch` -> **`fn-auth-step-pinned`** (the subject) ->
`fn-nntp-help` (books/nntp-responses.lisp) for HELP. No relation is carried:
the keystone is a per-step fact over any session satisfying the
command-mode hypotheses.

- KEYSTONE `fn-auth-step-pinned-answers-500-to-a-keyword-help-does-not-list`:
  if `(fn-auth-sessionp as)`, not handshaking, no transit article awaited, no
  POST body awaited, the reader session open, `(fn-nntp-command-inputp line)`,
  its first token a keyword token, the arguments within bound, and the keyword
  not `fn-nntp-served-keywordp`, then the step's effects are
  `(fn-auth-single as "500 command not recognized")`, its submission nil and
  its session `as`.
- `fn-nntp-help-renders-the-served-command-table-by-definition`: HELP =
  `fn-nntp-multi` of `(fn-nntp-help-table-lines *fn-nntp-served-command-table*)`.
- `fn-nntp-served-keywordp-unfolds`: the table as the disjunction of
  `fn-nntp-keywordp` tests the dispatchers make.

Teeth (tests/acl2/nntp-help-tests.lisp): HELP over the served step equals the
block assembled from RFC text; the reachable witness `XPATH <a@b.invalid>` on
a served session (antecedent and whole conclusion evaluated); a `must-fail`
per hypothesis (nine) with the keystone's hints; concrete removal values for
seven hypotheses (handshaking, POST body awaited, closed after QUIT, a
607-octet line, `9XPATH`, a 498-octet argument, a listed keyword XHDR); the
two without a served value (non-session; transit article awaited, which needs
a peer mid-IHAVE) have only the must-fail. The converse, every listed
keyword draws a reply other than 500, is checked by evaluation for all 28 and
is not a theorem (PKT-571).

Runs: REPL on persvati (`~/fn-gates/reader-clients-repl`). `books/nntp-responses`
admitted (339 forms, session nr). `books/nntp-help` (20 forms) and
`tests/acl2/nntp-help-tests` admitted in session nh against dev's cached
closure with `fn-nntp-help` redefined in-session to the new lines (the cached
closure carries the old HELP; the rendering theorem is the only form that
needs it). Keystone 0.5 s; slowest must-fail 5.6 s. Downstream
`fn-nntp-effects-help`'s statement re-proved over the new HELP in-session.
Not certified: the batch certifies (345 affected roots, nntp-responses being
deep). Also changed: tests/acl2/nntp-legacy-tests.lisp and tests/test_reader.py
(the expected HELP block).

## 3. O5: docs/operator.md

- "Add a group" said the service must stop (the Python-era `fn group`). The
  native `operator CONFIG group create|retire` applies live through the
  owner's control socket (`fn-native-admin-plan-deltas`,
  tests/test_native_live_reconfiguration.py) and offline otherwise.
- The profile table gave `max-article-octets` 32,768 (and R 196,608, G 16:
  the format-7 figures); the next paragraph and `*fn-bs-profile-defaults*`
  give 16 MiB (R 64 MiB, G 4096). The table now says so.
- `python3 tools/docs_check.py --write` regenerated
  tests/acl2/docs-operator-grammar-tests.lisp.

## 4. R1 probe (measurement only; the fix is held)

`tests/test_native_reader_freshness.py`: a reader that selected `fn.test`
before the article existed, then (a) another connection's POST (240), (b) a
source-address peer's IHAVE (235; the reader connects from 127.0.0.2); after
each, the long-lived reader and a fresh connection send GROUP, LISTGROUP,
STAT and ARTICLE; every reply is printed as `R1-OBSERVED` JSON. Assertions are
the controls only.

NOT RUN by this lane: the lane's one native module was the client phase
(Thunderbird is only on persvati). The batch runs
`tests.test_native_reader_freshness` on hbox and records the module log's
SHA-256. What the model says it will see: specs/nntp.md "Read-back" and
books/owner.lisp `fn-own-outcome` -- only the poster is re-pinned after its
240 (`fn-own-durable-outcome-repins-the-poster`); every other connection
keeps the version pinned at open (`fn-own-outcome-touches-only-its-connection`,
`fn-own-pinned-prefix-survives-any-trace`), and tests/test_native_owner.py
already says "deliberately retains its pinned archive snapshot". Expected:
the long-lived reader's GROUP is unchanged and STAT of the new article is
430, for both arrivals. A prediction, not an observation.

## PKT-571: what remains

1. R1 observed natively (the batch), then the design lane's fix (re-pin at
   GROUP/LISTGROUP between commands) under the consolidation's delta
   interface.
2. The converse of PRF-194 as a theorem (each listed keyword never 500).
3. pan: xdotool + certificate trust + a TLS-terminating relay.
4. The Thunderbird reply-lookup fix rerun; the phase on the batch image.
5. MODE READER `200 posting allowed` before login under `[auth] required`
   against the 201 greeting.
6. P1: a newsreader cancel does nothing (inventory).
