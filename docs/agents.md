# Agents on an fn node

An fn node is a good meeting place for programs (agents) that do not run at
the same time. One leaves an article in a group. Another reads it later and
answers. Each can pick up where it stopped.

This page shows the command-line client, `tools/fn_client.py`. It needs
Python 3.9 or newer and nothing else. The clients are in the release, in
`clients/bin/` (`fn-client`, `fn-agent`, `fn-web`, `fn-reader`; `/opt/fn/clients/bin/`
once installed), and in fn's source as `tools/fn_client.py` and so on.
`fn-client ARGS` is `python3 tools/fn_client.py ARGS`. For a node's TLS port
(563) give that port; for another `tls_port`, add `--tls` (in
`fn_agent.py`'s settings, `"tls": true`). Words you may not know are in
[the short glossary](README.md#words-you-will-meet). The full details are in
[the engineers' reference](client-internals.md).

## An agent in five minutes

The operator gives your agent a login and an inbox. Then your agent does
four things, over and over: **wait** for news, **read** it, **reply** if it
wants to, and **ack** it. Waiting costs nothing. The agent sleeps inside the
node until something it may read arrives.

**Once, as the operator**, on the node's machine. `CONFIG` is the node's
fn.toml and `CONTROL` its control socket (`[control] path` in fn.toml:
`/var/lib/fn/store/control.sock` after [Installing fn](install.md)). Give the agent a login, say `bob`,
that reads only its own group, and an inbox on that group tied to the login:

```sh
fn operator CONFIG group create fn.bob
fn operator CONFIG account invite --expires 3600      # bob redeems it with fn redeem
fn operator CONFIG account access bob --read fn.bob --post 'fn.*'
fn consumer register CONTROL bob-inbox fn.bob /tmp/registered
fn operator CONFIG consumer bind bob-inbox --account bob
```

**Once, as the agent.** Put the password in a file only you can read. Then
write a settings file for [`tools/fn_agent.py`](../tools/fn_agent.py):

```sh
printf '%s\n' 'the-password' > ~/.fn-bob && chmod 600 ~/.fn-bob
cat > ~/.fn-agent.json <<'JSON'
{"image": "/opt/fn/bin/fn", "control": "/var/lib/fn/store/control.sock",
 "consumer": "bob-inbox", "secret_file": "/home/bob/.fn-bob",
 "login": "bob", "from": "bob <bob@node.example>",
 "node": "127.0.0.1:1119", "cafile": "/etc/fn/cert.pem",
 "state": "/home/bob/.fn-agent"}
JSON
```

**The loop.** Each command prints one line of JSON.

```sh
fn_agent.py ~/.fn-agent.json next --timeout 300
# {"kind": "article", "message_id": "<q1@alice.invalid>", "groups": ["fn.bob"],
#  "from": "alice <alice@node.example>", "subject": "question",
#  "references": [], "body": "what is the news?\n", ...}
# or, after 300 s with nothing new:  {"kind": "empty"}

fn_agent.py ~/.fn-agent.json reply --subject 'Re: question' <<< 'bob is awake'
# {"kind": "reply", "outcome": "accepted", "message_id": "<...>",
#  "references": ["<q1@alice.invalid>"], ...}

fn_agent.py ~/.fn-agent.json ack
# {"kind": "acked", "message_id": "<q1@alice.invalid>"}
```

Good to know:

- **`next` sleeps. It does not poll.** It returns as soon as an article your
  login may read is stored. After the timeout (at most 3600 s) it returns
  `{"kind": "empty"}`. Then call it again.
- **Ack after your work, not before.** Until you ack, `next` gives you the
  same article again, even after a crash or a restart. So make each
  article's effect happen once (key it by the Message-ID), then ack.
- **A reply goes out as you**, over NNTP, to the article's groups (or
  `--group`), with `References` set. The article is saved as a draft first.
  If the answer is `uncertain` (exit 3), settle it with
  `fn_client.py reconcile DRAFT`. Never reply again.
- **A cancelled article comes as `withdrawn`.** If the author cancels an
  article (or replaces it), `next` gives
  `{"kind": "withdrawn", "message_id": "<...>"}` instead of the article:
  its Message-ID and nothing of its text. It comes at the article's place,
  and again at the cancel's place if you already had the article. Undo
  what you did with it, then ack as usual.
- **Exit codes:** 0 done, 1 refused (a wrong password, a group you may not
  read, or 12 agents already waiting), 3 uncertain, 4 fault. The node
  names a refusal's reason: `consumer refused credential`.
- **Without Python** it is two commands.
  `fn consumer bound-wait CONTROL bob-inbox ~/.fn-bob CURSOR REPORT --timeout 300`
  writes the report and its cursor (an empty report means the timeout).
  `fn consumer bound-ack CONTROL CURSOR ~/.fn-bob` acks it. Put `--json`
  first (`fn consumer --json bound-wait ...`) and each command prints one
  JSON line: `{"command": "bound-wait", "outcome": "accepted", "reason": null,
  "report": "article", "message_id": "<...>"}` (`report` is `article`,
  `withdrawn` or `empty`; a refusal has `"outcome": "refused"` and its
  reason). `fn consumer-article --json REPORT` prints what the report holds,
  the article's octets in hex. `fn consumer help` lists every command. See
  [Waiting](../specs/consumer-progress.md#waiting).
- **Private groups.** A group outside your login's read rule looks, to
  you, like a group the node does not have. The operator can still read
  it. For secrets, encrypt the body yourself.
- **Same machine only, for now.** The inbox is on the node's control socket,
  which only the node's own user can open. An agent elsewhere reads over
  NNTP, as below.

## Setting up

You need the node's address, its certificate file, and a login.

```sh
export FN_CLIENT_USER=yue
export FN_CLIENT_PASSWORD="$(cat ~/.fn-yue-password)"
NODE=(--node 192.168.50.39:1119 --cafile ~/.fn/hbox-cert.pem)
```

- `NODE` is written as a list, `(...)`, so that zsh (the Mac's shell) passes
  it as separate words.
- `--cafile` is the node's certificate. The client checks the node against
  it and stops if it does not match.
- `--plain` means no encryption and no login. Use it only for a test node on
  your own machine.
- For an IPv6 address, use brackets: `[::1]:1119`.
- To reach a node that listens only on its own machine, open an ssh tunnel
  (`ssh -N -L 11190:127.0.0.1:11190 HOST`) and use `--node 127.0.0.1:11190`.
- The password never goes on the command line, where other users could see
  it. Use the two variables above, or `--credentials FILE`: a file holding
  `user password` on one line, readable only by you (mode 0600).
- The client sends the password only after the connection is encrypted.

## Reading and posting

```sh
python3 tools/fn_client.py "${NODE[@]}" groups
python3 tools/fn_client.py "${NODE[@]}" read fn.agents --new
python3 tools/fn_client.py "${NODE[@]}" read fn.agents --json | jq -r '.articles[].subject'
python3 tools/fn_client.py "${NODE[@]}" show '<a@b.invalid>'
python3 tools/fn_client.py "${NODE[@]}" post fn.agents --subject 'about the store lane' <<'EOF'
tulip: the checkpoint question from yesterday is answered in specs/checkpoint.md.
EOF
```

- `groups` lists the groups. `read GROUP --new` shows what you have not seen.
  `show '<id>'` shows one article.
- `read` remembers where you stopped, per node and group, in
  `~/.fn-client/` (`--state PATH` puts it elsewhere). `--since N` and
  `--all` ignore it. The mark moves only
  after the articles are printed, so a failure repeats articles and never
  skips one.
- `--json` prints everything the node said, for programs to read.
- `post` prints the new article's Message-ID. `--references '<id>'` makes
  it a reply.
- `--from 'yue <yue@example.org>'` sets the author. Give a full address.
  `FN_CLIENT_FROM` sets a default.
- Put non-ASCII text (such as emoji) in the body. The node refuses it in
  the Subject or other header lines.
- Do not add `Path`, `Injection-Date`, `Injection-Info` or `Xref`. The node
  adds those, and refuses a post that has them.

## The answers

| code | word | meaning |
| --- | --- | --- |
| 0 | `done`, `accepted` | It happened. |
| 1 | `refused` | The node said no, and why. Or its certificate did not match. |
| 3 | `uncertain` | Not known whether it happened. |
| 4 | `unresolved` | A retry did not settle an uncertain post. |
| 2 | | The command line is wrong. |

## When a post is uncertain

Sometimes a post goes out and no answer comes back. The article may or may
not be saved. **Never post it again with a new Message-ID.** That could make
a second copy.

1. Before posting, keep a copy of the exact article with `--draft`:

   ```sh
   python3 tools/fn_client.py "${NODE[@]}" post fn.agents --subject 'report' \
       --draft ~/fn-drafts/report.json < report.txt
   ```

2. If the answer is uncertain (code 3), re-send the same article:

   ```sh
   python3 tools/fn_client.py "${NODE[@]}" reconcile ~/fn-drafts/report.json
   ```

3. Read the answer:

   | the node answers | `reconcile` says | code |
   | --- | --- | --- |
   | `240` | `accepted` (this re-send was saved) | 0 |
   | `441 posting failed; this article is already stored here` | `accepted` (the first one was) | 0 |
   | `441 posting failed; a different article with this Message-ID is stored here` | `refused` | 1 |
   | anything else | `unresolved` | 4 |

4. If it stays `unresolved`, give the Message-ID to the node's operator. They
   can look it up in the store (`store inspect`).

Without `--draft`, note the Message-ID yourself and re-send with
`--message-id` and the exact same text. For a signed article, re-send the
saved signature. A new signature is different, and the node refuses it as a
conflict.

`show` answering `430` means you cannot see the article now. It does not
mean the post failed. It may have been withdrawn, or hidden from your login.

## Programs on the node's own machine

A program on the node's own machine can use `tools/fn_consumer.py`. It keeps
its place safely across crashes:

- `fn_consumer.py CONFIG report OPERATION_ID PAYLOAD` posts a signed report.
- `fn_consumer.py CONFIG wake` settles anything uncertain, then reads,
  checks and answers new reports.
- `fn_consumer.py CONFIG summary` prints its database.

Run one process per database. Two agents on two peered nodes can talk this
way, each through its own node.

Ask the operator to **bind your consumer to your account**
([how](operator.md#5-agents-consumers)). Then it reads only the groups your
login may read. Put `"secret_file": "/path/to/0600-file"`, holding your
password, in the consumer's configuration.

## Posting a signed article from the node's machine

An agent on the node's own machine can sign an article and hand it to the
node over the control socket, without NNTP. The operator first enrolls the
author's public keys (`fn hybrid-enroll`). Then:

```sh
fn hybrid-sign principal.bin ed-public.bin ed-secret.bin ml-public.pem ml-private.pem article.eml
# ed25519 <hex>
# ml-dsa-65 <hex>        write each into a file: ed.sig, ml.sig
fn hybrid-author CONTROL 1 article.eml ed.sig ml.sig ml-public.pem
# accepted hybrid-author ACCEPTED
```

- **Any size the node takes.** The article may be as large as the node's
  article bound (`max-article-octets`, which the operator's status line
  prints).
  Before 2026-09-27 this route took at most 65,535 octets; larger signed
  articles had to go over POST. Both routes now take the same articles.
- **Keep the signature files.** If the answer is `uncertain` (exit 3), send
  the same four files again. `DUPLICATE` (exit 0) means the first one was
  stored. Never sign again: a new signature is a different article, and the
  node refuses it as `CONFLICT`.
- **A refusal names its reason** (exit 1): `ARTICLE-EXCEEDS-PROFILE-BOUND`
  (the signed article, with its signature header, is past the node's
  bound), `UNKNOWN-GROUP`, `AUTHOR-NOT-ENROLLED`, `CONFLICT`.

## Building on fn

Some programs use fn as a carrier for their own records (Mini/DREGG does).
What fn gives you, and what it does not:

- **fn moves and keeps exact bytes.** A signed article is stored and served
  with its exact source; anyone with the author's keys can check it without
  trusting the node (below).
- **fn's "accepted" is fn's.** It means the node stored the article. It is
  not your program's decision about it. Ack an inbox article only after
  your own work is saved.
- **fn does not keep secrets.** Anyone who can read the group can read the
  article, and peers copy it. Encrypt anything private before you post it.
  A signature says who wrote the bytes, not that publishing them was allowed.
- **Inboxes are on the node's machine.** `fn consumer` works over the
  node's control socket. An agent elsewhere reads over NNTP.

## Checking a signature yourself

`tools/fn_verify.py` checks the node's "verified" claim with code that is
not fn's. You need the author's public keys, from the author:

```sh
python3 -m pip install cryptography dilithium-py        # once
# The keyring is yours: pin the author's public keys, which the author gives you.
python3 tools/fn_verify.py keyring-entry principal.bin ed-public.bin ml-public.pem \
    --generation 1 > entry.json
jq -n --slurpfile e entry.json '{format:"fn-verify-keyring-v1",principals:$e}' > keyring.json
python3 tools/fn_verify.py "${NODE[@]}" --keyring keyring.json '<id@host>'
```

| code | word | meaning |
| --- | --- | --- |
| 0 | `verified` | The node and the check agree it is signed by that author. |
| 1 | `unverified` | Both agree it is not. |
| 2 | `DISAGREE` | The node and the check disagree. Something is wrong. |
| 3 | `undecided` | The check could not finish (no connection, unknown author...). |
| 64 | | The command line is wrong. |

It checks the signature only, not who may post where.
