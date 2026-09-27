# Read it in your browser

The short version is part of a Usenet article: [fn FAQ, part 2: reading and posting](articles/fn-faq-2.txt).
This page stays the full reference; what changed after the articles were
written (batch AY) is here first and folds into the articles next.

Your node comes with a web page where you and your friends read and write
in its groups, from any browser, phone included. We call it the web reader.
It runs on the same machine as your node, beside it. Your friends need only
a browser: nothing to install, and they make their own account from an
invitation code.

Words you may not know are in
[the short glossary](README.md#words-you-will-meet). How to use the pages
once they are up is in [the friends' reader](reader.md).

## What you need

- Your node, installed and running ([Installing fn](install.md)).
- A web name for it, like `news.example.org`, that points at this machine,
  with ports 80 and 443 reaching it. Your friends type this name.
- Python 3 for the reader: `apt install python3` (OpenBSD:
  `pkg_add python3`). The node itself never uses Python.
- Caddy, which gives the page its padlock (HTTPS): `apt install caddy`.

The reader is in the release you installed, in `/opt/fn/clients/`
(OpenBSD: `/usr/local/fn/clients/`).

## 1. Install the reader

As root. If you are installing fn now, add `--reader`:

```sh
sh fn/install.sh --reader
```

If fn is already installed, run the installed copy with `--reader`:

```sh
sh /opt/fn/install.sh --reader
```

It makes an account `fn-reader` and a folder `/var/lib/fn-reader` (OpenBSD:
`_fnreader` and `/var/fn-reader`). The folder holds the reader's settings,
`reader.conf`, and a copy of your node's certificate. It installs the
service. It starts nothing yet.

## 2. Tell it where your node is

Open `/var/lib/fn-reader/reader.conf` in an editor. Change two lines:

- `node =` your node's name or address, as its certificate names it, then
  `:` and its TLS port. That is `563` if you added `tls_port = 563` to
  `fn.toml` ([how](install.md#reading-and-posting-from-another-machine)).
  Its plain port (the `--port` you gave `mission`, like `119`) works too: the
  reader then switches to TLS itself. A TLS port other than 563 (on OpenBSD,
  where the node cannot use ports below 1024, the `tls_port` is one like
  `11564`) needs the line `tls = yes` as well; without it the reader
  speaks STARTTLS to that port, and making an account fails with
  `refused redeem connection: the server closed or did not answer`.
- `site =` the name your friends see at the top of every page.

If your node's certificate is from Let's Encrypt (or another public
authority), also remove the `tls-cert` line and the `#` before
`system-ca = yes`. If you made the certificate yourself, leave them as they
are: the installer copied it.

Every friend reaches your node through the reader, so to your node they all
come from one address: this machine's. Tell the node that address is yours,
so it does not count them as one busy visitor. Use the address you gave
`mission --host`, as the service account:

```sh
fn operator /var/lib/fn/fn.toml policy set exposure-trusted 203.0.113.7/32
```

## 3. Start it

```sh
systemctl enable --now fn-reader     # OpenBSD: rcctl enable fn_reader && rcctl start fn_reader
systemctl status fn-reader
```

The status ends with a line like:

```
fn reader: news.example.org:563 (TLS) for Our news; open http://127.0.0.1:8920/ behind the HTTPS proxy
```

## 4. Give it a padlock with Caddy

Caddy answers your friends' browsers over HTTPS and passes them to the
reader. It gets the certificate for your web name by itself.

1. Copy the block from `/opt/fn/clients/share/caddy/fn-reader.caddy` into
   `/etc/caddy/Caddyfile`, and put your web name in place of
   `news.example.org`:

   ```
   news.example.org {
   	reverse_proxy 127.0.0.1:8920
   }
   ```

2. Reload Caddy:

   ```sh
   systemctl reload caddy
   ```

   **On OpenBSD** (`pkg_add caddy`; start it with `rcctl enable caddy &&
   rcctl start caddy`), Caddy runs without privileges. The package's
   `/etc/caddy/Caddyfile` begins with a block of settings that make it
   listen on this machine only, on ports 8080 and 8443. Keep that block
   and add yours after it; replacing the whole file makes Caddy fail at
   start (`caddy(failed)`: it may not use ports 80 and 443). Then remove
   the block's `default_bind` line, so browsers can reach it, and send
   ports 80 and 443 to it with `pf`, in `/etc/pf.conf` (then
   `pfctl -f /etc/pf.conf`):

   ```
   pass in on egress inet proto tcp to port 80 rdr-to 127.0.0.1 port 8080
   pass in on egress inet proto tcp to port 443 rdr-to 127.0.0.1 port 8443
   ```

   Tested on OpenBSD 7.9: Caddy with the package's block and a site block
   served the reader over HTTPS on port 8443. The `pf` rules and Caddy's
   own certificate from Let's Encrypt were not tested.

3. Open `https://news.example.org/` in your browser. You see the sign-in
   page.

## 5. Invite your friends

Make one invitation code per friend. It works once. Without `--expires`, it
lasts a week:

```sh
fn operator /var/lib/fn/fn.toml account invite
```

Send your friend the web address and the code, over a channel you trust.
They open the page, press **Make your account**, type the code, and choose
a name and a password. Then they are in. The same name and password work in
a newsreader like tin, too.

To make yourself an account, do the same. Accounts made with
`principal set-password` sign in here as well.

## If it goes wrong

- **"We can't reach the server right now."** The reader cannot reach your
  node. Check that the node runs (`fn operator /var/lib/fn/fn.toml health`)
  and that `node =` in `reader.conf` has the right name and port. Then
  `systemctl restart fn-reader`. `journalctl -u fn-reader` shows what the
  reader said.
- **"We couldn't confirm the server is the real one."** The reader did not
  send the password, because your node's certificate did not match. The
  name in `node =` must be one the certificate names. If you replaced the
  certificate, copy the new one to `/var/lib/fn-reader/node-cert.pem`
  (or use `system-ca = yes` for a public certificate), then restart the
  reader.
- **"Too many tries."** Someone typed a wrong password many times. Wait a
  few minutes.
- **The page does not load at all.** That is Caddy: `systemctl status caddy`.
  Your web name must point at this machine, and ports 80 and 443 must reach
  it.
- **"The server did not accept that"** when making an account: the code was
  used, has expired, or the name is taken. Make a new code.

After you change `reader.conf`, restart the reader:
`systemctl restart fn-reader`.

## What the reader can and cannot do

- It runs as its own account. It cannot open your node's folder: not the
  articles, not the control socket, not the passwords, not the node's keys.
- It signs in to your node as each friend, with that friend's own name and
  password, like a newsreader would. Your node checks every password and
  decides every group, post and removal.
- It knows a friend's password only while they are signed in, in memory.
  It never writes a password down.
- It keeps, in `/var/lib/fn-reader`, what each friend has read and a copy of
  what each sent.
- It listens only on this machine. Only Caddy talks to it.

The details are in
[the engineers' reference](operator-internals.md#the-friends-web-reader).

## A reader on your own computer

`fn-web` is a smaller reader for one person, on their own computer, where
only that computer can open it. It is in `clients/bin/` of any unpacked
release. It needs Python 3, the node's address, its certificate file (from
its operator) and your login:

```sh
fn/clients/bin/fn-web --node news.example.org:563 --tls-cert ~/node-cert.pem --user carol --outbox ~/.fn-web/outbox
```

Type your password when asked, then open the address it prints
(`http://127.0.0.1:8919/`). Port 563 is the node's TLS port; its plain port
(119) works too. `fn-web --help` lists the options. Posts it could not
confirm are kept in `--outbox`, so an uncertain post can be settled later
by sending the same article again, never a second copy.

It exits `1` if the node refused the login or the certificate did not
match, `3` if the node could not be reached, and `2` for no password or a
wrong option.
