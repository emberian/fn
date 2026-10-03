# Read it in your browser

The short version is a Usenet article: [fn FAQ, part 11: the web page](articles/fn-faq-11.txt).
This page is the full reference.

Your node has a web page where you and your friends read and write in its
groups, from any browser, phone included. It is part of the node: no other
program, account or service, and no Python. Your friends need only a
browser; they make their own account from an invitation code.

Words you may not know are in [the short glossary](articles/fn-faq-1.txt).
How to use the pages is in [the friends' reader](reader.md).

## What you need

- Your node, installed and set up ([Installing fn](install.md), through
  `mission`).
- A web name for it, like `news.example.org`, that points at this machine,
  with ports 80 and 443 reaching it. Your friends type this name.
- Caddy, which gives the page its padlock (HTTPS): `apt install caddy`
  (OpenBSD: `pkg_add caddy`).

## 1. Turn the page on

As root, after `mission` has written `fn.toml`:

```sh
sh /opt/fn/install.sh --reader
```

It adds this table to `/var/lib/fn/fn.toml` (OpenBSD: `/var/fn/fn.toml`),
once:

```
[web]
port = 8920
host = "127.0.0.1"
proxied = true
site = "Friends news"
domain = "news.example.org"
```

Change `site` to the name your friends see at the top of every page, and
`domain` to your web name: a post made on the page is from
`NAME <NAME@DOMAIN>`. Then restart the node:

```sh
systemctl restart fn     # OpenBSD: rcctl restart fn
```

The node prints `LISTENING-WEB 8920` when the page is up. If it does not
accept the `[web]` table, it does not start, and says why (for example
`the [web] table is refused: port-taken` when `port` is one the node's
newsreader ports already use).

The other keys, if you need them:

- `tls = true`: the node serves HTTPS itself, with the certificate in
  `[listener]`, instead of Caddy. Use it without `proxied`.
- `idle_seconds = 43200`: how long a signed-in page stays signed in
  without use (12 hours).
- `max_sessions = 64`: how many people can be signed in at once. Each
  signed-in person is one connection to the node, counted like a
  newsreader's. This also bounds the HTTP connections the page can serve at
  once; extra connections wait in the listener's backlog. A browser waiting
  on a slow request does not block the other connections.

## 2. Give it a padlock with Caddy

Caddy answers your friends' browsers over HTTPS and passes them to the
node. It gets the certificate for your web name by itself.

1. Copy the block from `/opt/fn/share/fn/caddy/fn-web.caddy` into
   `/etc/caddy/Caddyfile`, and put your web name in place of
   `news.example.org`:

   ```
   news.example.org {
   	reverse_proxy 127.0.0.1:8920
   }
   ```

2. Reload Caddy: `systemctl reload caddy`.

   **On OpenBSD** Caddy runs without privileges. The package's
   `/etc/caddy/Caddyfile` begins with a block that makes it listen on this
   machine only, on ports 8080 and 8443. Keep that block and add yours
   after it; replacing the whole file makes Caddy fail at start. Then remove
   the block's `default_bind` line, and send ports 80 and 443 to it with
   `pf`, in `/etc/pf.conf` (then `pfctl -f /etc/pf.conf`):

   ```
   pass in on egress inet proto tcp to port 80 rdr-to 127.0.0.1 port 8080
   pass in on egress inet proto tcp to port 443 rdr-to 127.0.0.1 port 8443
   ```

3. Open `https://news.example.org/` in your browser. You see the sign-in
   page.

With `proxied = true` the node takes the browser's address from the last
`X-Forwarded-For` Caddy adds, and only when the request comes from this
machine. So a friend who types a wrong password many times is paused on
their own address, not everyone's.

## 3. Invite your friends

Make one invitation code per friend. It works once. Without `--expires`, it
lasts a week:

```sh
fn operator /var/lib/fn/fn.toml account invite
```

Send your friend the web address and the code, over a channel you trust.
They open the page, press **Make your account**, type the code, and choose
a name and a password. Then they are in. The same name and password work in
a newsreader like tin, too. Accounts made with `principal set-password`
sign in here as well.

## If it goes wrong

- **The page does not load at all.** Check Caddy (`systemctl status
  caddy`), that your web name points at this machine, and that the node
  printed `LISTENING-WEB`.
- **"Signing in needs a protected connection"**. The page was opened with
  `http://`, not through Caddy. Use `https://`.
- **"That name and password don't match."** The node refused the login.
- **"Too many tries from here just now."** Someone typed a wrong password
  many times from that address. Wait a few minutes.
- **"That invitation code didn't work"**. The code was used, has expired or
  was mistyped, or the name is taken. Make a new code.
- **"We couldn't tell whether the server took it."** The post may be up.
  Look at the group before sending it again.

## What the page can and cannot do

- It is the node itself. Every sign-in is the node's own login check
  (AUTHINFO), every account the node's own invitation (XREDEEM), every post
  and removal the node's own answer. What a friend may read and post is
  what their newsreader may: the page shows only what the node answered
  on that friend's own connection.
- Each page is made by the node's ACL2 core from those answers; text from
  articles is always escaped, and the pages carry no scripts
  (`Content-Security-Policy: default-src 'none'`).
- It never writes a password down. A friend's session lives in the node's
  memory and ends when they sign out, after `idle_seconds`, or when the
  node restarts.
- By default it listens only on this machine (`host = "127.0.0.1"`). Only
  Caddy talks to it.

Not on the page yet: conversations as threads, search, marking what you
have read, moderation, and your own check of a signed article
(`fn-verify` in `clients/` does that). The design and its proofs are in
[the client specification](../specs/human-client.md) (WEB-005) and
[the engineers' reference](operator-internals.md#the-friends-web-reader).

## Check readiness over the network

`GET /health` on the configured web listener answers in the running node,
without an account, a reader connection or a second image process. `HEAD /health` returns the same status and Content-Length with no body. A ready
node answers `200` and `ready` followed by a newline; a stalled or full disk,
or a deferred checkpoint publication, answers `503` with `unavailable disk`
or `unavailable checkpoint`. A missing or malformed observation answers
`503` with `unobserved`. Replies are plain text, at most 23 body octets, and
carry `Cache-Control: no-store`.

This is the current owner's disk/checkpoint readiness check. A slow barrier
follows the existing health policy and remains clear until it stalls. It
walks no history, groups or peers. Use the operator's `health` command for
the complete namespace, profile, route, peer and receipt diagnostics.
The endpoint uses the web listener's existing TLS and request limits;
other methods on this path are refused. This readiness policy is fn's,
not a requirement imposed by HTTP.


Native ARTICLE/OVER/LIST pages now scan and replay captured NNTP plans through
bounded Web windows, retaining article/overview virtual spans or one dynamic
LIST row plan. Both HTML passes retain the response pin through final socket
drain. WEB-006 and SCN-1113/1114/1115 distinguish this extra-collector removal
from original NNTP producer materialization, which remains the complete tariff
frontier. Programs PRF-1283/1284/1285 still await guard/refinement and matching
image evidence; no universal allocation or full event fairness claim.


Streaming Web command and await plans enter a fixed-worker `:ready` phase before
replay capture. `fnn-owner-ready-plan-step` resolves one shared ARTICLE framing
preflight quantum; yielded/raw and cold continuations are retained without
publication. Only READY stores the immutable original plan for both HTML passes.
No preflight/selection scan is replayed during count or emit. The consumer pairs
with Access source e7624ab8a/e41b22c21 and Served a3bd4513f; its raw adversarial
owner adapter checks cold/yield/READY capture custody, not producer semantics.
Actual composed source execution and complete Web tariff remain pending.
