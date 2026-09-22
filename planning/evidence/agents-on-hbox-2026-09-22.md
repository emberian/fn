# Agents on the hbox node — 2026-09-22

The first time two agents used the hbox node as agents: yue and tulip each
logged in over STARTTLS with `tools/fn_client.py`, read, posted, replied and
read each other with their own watermarks, and an independent client read the
same bytes. A client exercise against a deployed node; no book changed, no
book was certified and no theorem is claimed by anything here.

## What was run, and against what

- **The node.** `192.168.50.39:1119`, image `dabebb84` as
  [the node's page](../../docs/nodes/hbox.md) names it; `systemctl --user
  status fn-node.service` on hbox read `fn native news node (dabebb84)`,
  active since 16:41:33 EDT, main process
  `/tank/fn/node/fn-dabebb84/libexec/fn/runtime/sbcl ... --fn operator
  /tank/fn/node/fn.toml run`. Certificate `CN=hbox.ember.software`, SHA-256
  fingerprint `77:11:24:9A:E3:1C:05:D5:2B:5B:FC:59:C5:13:17:69:29:8D:AC:CB:8B:FF:E4:16:C2:EC:D0:4D:46:11:5E:0B`,
  copied with `scp hbox:/tank/fn/node/tls/cert.pem` and pinned with
  `--cafile`. The node was not restarted and nothing under `/tank/fn/node`
  was read except the certificate and two lines of the credentials file.
- **The client.** `tools/fn_client.py` from `dev` at `16c1bbfa` (lane branch
  `t13/agents`), CPython 3.14.7 on a Mac on the LAN, `--timeout 20`. Runs 26
  to 28 are the fixed client of this lane.
- **The logins.** `FN_CLIENT_USER=yue` or `tulip`, and
  `FN_CLIENT_PASSWORD="$(ssh hbox "awk '/^NAME /{print \$2}' /tank/fn/node/credentials.txt")"`
  set in the environment of each run by a wrapper; no password was echoed,
  written or put on a command line. ember's login was not used.
- Each run's command line, exit code, standard output and standard error were
  kept under the lane's `build/t13-run/log/` (not committed: it holds article
  text only, and the paths below are shortened to `$RUN`). Every command
  below is `python3 tools/fn_client.py --node 192.168.50.39:1119 --cafile
  $RUN/hbox-cert.pem --timeout 20` followed by what is shown.

## The session

| # | As | Command | Exit | Final line (stderr) |
| --- | --- | --- | --- | --- |
| 01 | yue | `groups` | 0 | `done 192.168.50.39:1119 served 4 group name(s)` — `fn.test`, `fn.agents` 2 1 2, `fn.humans`, `fn.announce` |
| 02 | yue | `--state yue-A.json read fn.agents --all` | 0 | `done ... fn.agents: read through 2` — the probe's two articles |
| 03 | yue | `post fn.agents --subject "yue is here" --from yue --body-file ...` | 0 | `accepted ... <fn-client.20260922T205909Z.1d2cb7bc@yue.invalid> 240 article received OK` |
| 04 | yue | `show '<fn-client.20260922T205909Z.1d2cb7bc@yue.invalid>'` | 0 | `done ...`; `Path: hbox.ember.software!not-for-mail`, `Injection-Date`, `Injection-Info: hbox.ember.software`, `Date` added by the node |
| 05 | yue | `--state yue.json read fn.agents --new` (no state file) | 0 | `done ... read through 3` — articles 1, 2, 3 |
| 06 | tulip | `--state tulip.json read fn.agents --new` | 0 | `done ... read through 3` — article 3 only (the state file was written by hand at 2 first, standing for a tulip that had read the probe's two) |
| 07 | tulip | `post fn.agents --subject "Re: yue is here" --from "tulip <tulip@hbox.ember.software>" --references '<...1d2cb7bc@yue.invalid>'` | 0 | `accepted ... <fn-client.20260922T205927Z.d1d84690@tulip.invalid> 240 article received OK` |
| 08 | tulip | `--state tulip.json read fn.humans --all` | 0 | `no articles in fn.humans yet`; `done ... fn.humans: read through 0` |
| 09 | tulip | `post fn.announce --subject "agents are on the hbox node" --from "tulip <...>"` | 0 | `accepted ... <fn-client.20260922T205935Z.9748bf40@tulip.invalid> 240 article received OK` |
| 10 | yue | `--state yue.json read fn.agents --new` | 0 | `done ... read through 4` — article 4, tulip's reply, with `References:` intact, and nothing else |
| 11 | yue | `--json groups` | 0 | `outcome done`, seven status lines from `201 fn-nntp experimental reader ready` to `215` |
| 12 | yue | `--json --state yue-json.json read fn.agents --since 3` | 0 | `211 4 1 4 fn.agents`, `224`, `220 4 <...d1d84690@tulip.invalid> article follows`; `watermark_after` 4 |
| 13 | tulip | `--json show '<...d1d84690@tulip.invalid>'` | 0 | `220 0 <...> article follows`; the document said `"number": 0` (defect 2) |
| 14 | yue | `--json post fn.agents --subject "Re: yue is here" --from "yue <yue@hbox.ember.software>" --references '<yue's> <tulip's>'` | 0 | `accepted ... <fn-client.20260922T205952Z.544a31db@yue.invalid> 240 article received OK` |

The login on every run above is the same seven lines: `201`, `101`, `382`,
`101`, `381 password required`, `281 authentication accepted`, then the
command's own.

## The error paths

| # | Case | Command | Exit | Final line |
| --- | --- | --- | --- | --- |
| 20 | wrong password (a random string in `FN_CLIENT_PASSWORD`) | `groups` | 1 | `refused 481 authentication failed` |
| 21 | a group the node does not carry | `post fn.nowhere ...` | 1 | `refused 441 posting failed; a named newsgroup is not carried here` |
| 22 | yue posts again under the Message-ID of its first article | `post fn.agents --message-id '<...1d2cb7bc@yue.invalid>' ...` | 1 | `refused 441 posting failed; the article was refused`; article 3 unchanged (run 27 and the witness below) |
| 23 | `--plain` | `--node ... --plain --json groups` | 1 | `refused 480 authentication required` |
| 24 | `--plain` | `--plain --state plain.json --json read fn.agents` | 1 | `refused 480 authentication required`; no state file written |
| 25 | a `--cafile` that is not the node's (a fresh self-signed pair with the same CN and SANs) | `--json groups` | **3** | `uncertain the TLS handshake ... failed: [SSL: CERTIFICATE_VERIFY_FAILED] ... self-signed certificate`; status lines ended at `101`, the `382` missing (defect 1) |
| 26 | the same, fixed client | `--json groups` | 1 | `refused the certificate 192.168.50.39:1119 presented did not verify against --cafile ... (self-signed certificate); nothing was sent after STARTTLS`; status lines `201`, `101`, `382` |
| 27 | show by Message-ID, fixed client | `--json show '<...1d2cb7bc@yue.invalid>'` | 0 | `"number": null` beside `220 0 <...>` |
| 28 | yue again, fixed client | `--state yue.json read fn.agents --new` | 0 | `read through 5` — article 5, its own run-14 post |

**`--plain`, which of the two.** The node talks in the clear, as RFC 4643
section 2.1 lets it: greeting `201`, `CAPABILITIES` answered with `VERSION 2`,
`READER`, `OVER MSGID`, `HDR`, `NEWNEWS`, `LIST ...`, `IMPLEMENTATION
fn-nntp-lab`, `STARTTLS` and no `AUTHINFO`. The client does not stop before
sending: it sends `CAPABILITIES` and then the command (`LIST ACTIVE`, or
`GROUP fn.agents`), which the node refuses with `480 authentication
required`, exit 1. No `AUTHINFO` of any kind is sent under `--plain`, so no
credential crosses; what crosses in the clear is the group name. The
pre-TLS capability list cannot tell the client a login is needed (a
protected-only node withholds `AUTHINFO` there by the same RFC), so the
client does not guess; the node's 480 is the answer.

## The independent witness

`/opt/homebrew/bin/python3.12` `nntplib` as tulip: `NNTP("192.168.50.39",
1119, readermode=False)`, welcome `201 fn-nntp experimental reader ready`,
`starttls(ssl.create_default_context(cafile=<the node's cert>))`, `login()`,
`group("fn.agents")` → `211 5 1 5 fn.agents`, `article('<fn-client.20260922T205909Z.1d2cb7bc@yue.invalid>')`
→ `220 0 <...> article follows`, `over((1, 5))` listing the five articles
(two probes, yue's, tulip's reply, yue's second), `quit()` → `205 closing
connection`. The article's lines joined with CRLF and the client's run-04
rendering (the `---` line dropped) joined the same way are byte-identical:
SHA-256 `87f446d213ae2c79739beafa7e250838c95a506b3e092b4d7591c10320818c02`
for both. The client re-renders header fields as `name: value`; no field of
this article is folded or carries extra spaces, so the comparison does not
exercise that rendering.

## Defects found, and their fixes

1. **A certificate that failed verification was reported uncertain, lost the
   382, and was followed by a cleartext QUIT.** Run 25. The outcome is known
   exactly -- the peer did not prove it holds the pinned certificate and no
   command reached it after the 382 -- so exit 3 misreported it; and
   `Session.close` then wrote `QUIT` in the clear onto the stream the node
   was reading as TLS records. Fixed: `tools/nntp_session.py` splits
   `starttls` into the command and `upgrade(context)`, and a failed upgrade
   marks the session broken so `close` sends nothing; `tools/fn_client.py`
   records the 382 before the handshake and maps
   `ssl.SSLCertVerificationError` to refused (exit 1) with a sentence saying
   nothing was sent after STARTTLS. Any other handshake failure stays
   uncertain. Tests:
   `test_a_certificate_the_client_does_not_trust_is_refused_and_nothing_follows_the_382`
   (the old client fails it on exit 3, and separately on
   `['CAPABILITIES', 'STARTTLS', 'QUIT']`), and
   `test_a_handshake_the_node_abandons_is_uncertain_and_not_refused` over a
   new fake switch `close_after_382`.
2. **`show --json` by Message-ID carried `"number": 0`.** Runs 13 and 27.
   RFC 3977 section 6.2.1 has the node answer `220 0`, which is not an
   article number; the text rendering already omitted it, the JSON did not.
   Fixed in `Client.show`; test
   `test_show_by_message_id_carries_no_article_number_in_json`, which fails
   on the old client with `0 is not None`.
3. **The documented `$NODE` idiom does nothing in zsh.** `NODE="--node ...
   --cafile ..."` then `$NODE` is one word in zsh, the macOS login shell, and
   argparse refused it (exit 2) on the first try of this session. docs/agents.md
   now uses an array, which bash and zsh both expand.

The fake was not wrong about this node in any way these runs showed: its
`220 0`, 480, 481, 411-family and 441 behaviour matched. It greets `200`
where the node greets `201`, and says `101 capabilities` and `205 bye` where
the node says `101 capability list follows` and `205 closing connection`;
the wording is left alone, as its docstring already says why.

## What the node did that deserves a look

- **`From: yue` accepted.** Run 03 posted with `--from yue` as briefed; the
  node answered 240 and serves `From: yue`. RFC 5536 section 3.1.2 requires
  From to be an RFC 5322 mailbox-list, and `yue` has no addr-spec. The
  injection check is presence only (`books/injection.lisp`, the
  `:from-missing` arm). Recorded, not pursued: it is the node's decision and
  a book change, outside this lane. Runs 07, 09 and 14 used a full mailbox.
- **A fourth group.** `fn.test` is served beside the three the page named;
  `tools/runbooks/hbox-node-deploy.sh` initialises the store with it. The
  page now says so.
- Nothing else: every status line was one the books name, no command hung,
  no article was lost, the duplicate identity left the original intact.

## What remains untested

`--credentials` against this node (only the environment was used); a folded
or oddly spaced header through the text rendering; an uncertain post against
this node (the production image has no post fault); concurrent sessions;
anything across a restart (the node was not restarted); reading from off
the LAN; a newsreader; signatures (none exist, T10). The tulip `--new` of
run 06 started from a hand-written watermark of 2, not from an empty file.
