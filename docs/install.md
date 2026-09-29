# Installing fn

The short version is a Usenet article: [fn FAQ, part 3: installing a node](articles/fn-faq-3.txt),
with [the OpenBSD follow-up](articles/fn-faq-3-openbsd.txt). Reinstalling
and new releases: [part 5](articles/fn-faq-5.txt).
This page stays the full reference; what changed after the articles were
written (batch AY) is here first and folds into the articles next.

This page takes you from the download to a running node that others can
reach safely. Words you may not know are in
[the short glossary](articles/fn-faq-1.txt).

## What you need

- A Linux machine (x86-64, with systemd) or an OpenBSD 7.9 machine (amd64).
- On Linux: glibc 2.36 or later (Debian 12, Ubuntu 24.04 or newer) and
  OpenSSL 3.0 or later. A minimal Debian 12 lacks three packages the steps
  below use: `apt install libssl3 openssl sudo`. On OpenBSD, nothing
  extra.
- Root access, for the install and the service.
- A disk that really saves data when asked. Read
  [storage](operator.md#1-choose-the-disk-for-the-store) before you begin.
  On OpenBSD this matters most: the store needs its own FFS1 partition.

Each release is one file per platform, `fn-VERSION-linux-x86_64.tar.gz` or
`fn-VERSION-openbsd-amd64.tar.gz`, with a `SHA256SUMS` file beside it. The
first release is 6.6.0. Releases follow a fixed sequence, not the size of
the number: 6.6.0 to 6.6.5, then the 6.7.x series (6.7.0, 6.7.1, and so
on), then 6.6.6, the final release, and after it one more `.6` each time
(6.6.6.6). So 6.6.6 is newer than 6.7.12. The list and its rule are in
[the release sequence](../planning/release-sequence.json). The release brings everything it needs except
the system's TLS library.

## 1. Check, unpack and install

As root, on Linux:

```sh
sha256sum -c --ignore-missing SHA256SUMS
tar -xzf fn-VERSION-linux-x86_64.tar.gz
sh fn/install.sh
```

As root, on OpenBSD, unpack under `/usr/local` (not `/tmp` or `/root`:
the installer runs the unpacked copy, and there it halts with
`RWX mmap not supported`):

```sh
sha256 -C SHA256SUMS fn-VERSION-openbsd-amd64.tar.gz
mkdir -p /usr/local/src && tar -xzf fn-VERSION-openbsd-amd64.tar.gz -C /usr/local/src
sh /usr/local/src/fn/install.sh
```

Unpack under `/usr/local`: the installer runs fn once, and OpenBSD lets it
run only from a file system mounted `wxallowed`.

You will see the version, like `fn 6.6.0 (REV)`. The installer:

- checks every file of the release;
- copies fn to `/opt/fn` (OpenBSD: `/usr/local/fn`);
- makes a service account `fn` (OpenBSD: `_fn`);
- makes the node folder `/var/lib/fn` (OpenBSD: `/var/fn`);
- installs the service. It starts nothing yet.

If it goes wrong:

- **It refuses because `/opt/fn` exists.** fn is never installed over itself.
  See [Reinstalling](#4-reinstalling).
- **You want other places.** Use `--prefix DIR`, `--node DIR` or
  `--user NAME`. `--no-service` skips the account and the service (for
  running fn under your own account).
- **OpenBSD says `Cannot allocate memory` at start.** fn must live on a file
  system mounted `wxallowed`. `/usr/local` is, by default.
- **OpenBSD: the start fails with `Socket error in "bind": 13 (Permission
  denied)` in `/var/log/daemon`.** The service runs as `_fn`, without
  privileges, so it cannot listen below port 1024. Give `mission` a `--port`
  of 1024 or more (and a `tls_port` of 1024 or more), or send 119 and 563 to
  it with `pf`.

`/opt/fn/bin/fn --version` prints the version at any time. `fn` alone lists
the commands, and `fn operator CONFIG help VERB` explains one command.

## 2. Set up the first node

1. Open a shell as the service account, in the node folder:

   ```sh
   sudo -u fn sh -c 'cd /var/lib/fn && PATH=/opt/fn/bin:$PATH exec sh'
   ```

   On OpenBSD (no `doas` is set up on a fresh system):
   `su -s /bin/sh _fn -c 'cd /var/fn && PATH=/usr/local/fn/bin:$PATH exec sh'`.

2. Write the settings file. Put your server's own address after `--host`
   (`0.0.0.0` is refused: name the address you mean) and the port after
   `--port`:

   ```sh
   fn operator /var/lib/fn/fn.toml mission small-community --host 203.0.113.7 --port 119
   ```

   `small-community` means: logins are required, only over an encrypted
   connection, and the groups `local.general` and `local.test` are served,
   with `control.cancel`, where readers' own cancels go.

   On OpenBSD the service runs as `_fn`, which cannot use a port below
   1024. Use a port like `11563` there.

3. Give the node a TLS certificate. Copy one you have (for example from
   Let's Encrypt) to `tls/cert.pem` and `tls/key.pem`, with the key at mode
   0600. Or make your own. Use the name or address people will dial, and
   give them the certificate file:

   ```sh
   openssl req -x509 -newkey ec -pkeyopt ec_paramgen_curve:P-256 -nodes -days 3650 -subj /CN=news.example.org -addext subjectAltName=DNS:news.example.org,IP:203.0.113.7 -keyout tls/key.pem -out tls/cert.pem
   chmod 600 tls/key.pem
   ```

4. Create the store, name the node, and add a login that may post. The
   password is asked twice:

   ```sh
   fn operator /var/lib/fn/fn.toml init   # docs-check: skip (init under the mission fn.toml above; the grammar book configuration names no mission)
   fn operator /var/lib/fn/fn.toml policy set path-identity news.example.org
   fn operator /var/lib/fn/fn.toml account set-password alice --posting
   ```

   `init` also makes the node's secret key file, and sizes the store for
   this machine. It prints how much memory it will use when the store is
   full, so the node always starts again on this machine. If you named
   limits this machine cannot hold, `init` refuses, prints both numbers
   (`reservation=` what the store needs, `budget=` what the machine has)
   and makes nothing; exit code 1. The node's name (`path-identity`) should
   be its public host name.

   If the service runs under a memory limit (the unit's `MemoryMax`, a
   container's `mem_limit`), the store must be sized for that limit, not
   for the machine: run `init` under the same limit, or name the limit in
   MiB with `FN_INIT_BUDGET_MB=1536` in `init`'s environment. With a named
   budget below what this machine gives, `init` sizes the store for the
   named budget and says so on stderr with both numbers:
   `fn: warning init-budget-below-machine named-budget=1536 MB machine-budget=5818 MB: ...`.
   With neither, `init` sizes for the whole machine and the service then
   refuses to start under its limit (`machine-cannot-hold-profile`).

5. Leave the account's shell. As root, start the service:

   ```sh
   systemctl enable --now fn          # OpenBSD: rcctl enable fn && rcctl start fn
   ```

6. Check it:

   ```sh
   fn operator /var/lib/fn/fn.toml status
   fn operator /var/lib/fn/fn.toml health
   ```

   `status` shows the store's figures. Its line `capacity articles-left=N`
   says about how many more posts fit.
   `health` prints one line per possible problem. Every line should say
   `clear`. If not, see [the table below](#when-the-node-refuses-something).

The log is `log/fn.log` in the node folder. On OpenBSD it goes to syslog.

### Reading and posting from another machine

Any newsreader that supports STARTTLS can connect. It connects, switches to
TLS, checks the certificate, then logs in. fn refuses a login before TLS
(answer `483`), so a password never travels unencrypted.

Some readers (tin, for one) want TLS from the very start, on port 563. For
them, add `tls_port = 563` under `[listener]` in `fn.toml`, then restart the
service. See [newsreaders](human-web-client.md).

### Read it in your browser

The node has a web page too: you and your friends read and write in a
browser, phone included, and a friend makes their own account there from
an invitation code. It is part of the node itself; nothing else runs
beside it. Turn it on with `sh /opt/fn/install.sh --reader` (it adds a
`[web]` table to `fn.toml`), put Caddy in front of it for HTTPS, and
restart the node. Then follow [Read it in your browser](web.md).

## 3. Friends and accounts

- To connect your node with a friend's node, follow
  [Peering with a friend](peering-with-a-friend.md). Do all of it: after
  its step 2 the link is set up but carries nothing. Its step 3
  ([the feed, both ways](peering-with-a-friend.md#3-turn-on-the-encrypted-feed-both-ways))
  starts the articles flowing: each of you gives the other a login and
  adds the other as an encrypted peer, and each node fetches from the
  other with `peer pull`. Step 4 ([check it](peering-with-a-friend.md#4-check-it))
  posts on one node and reads the article on the other. Your friends are
  connected when that article arrives and each `log/fn.log` shows
  `accepted feed peer=...` and `pull peer=... round=done`. To copy what
  your friend's node held before you connected, add
  [catching up](peering-with-a-friend.md#catching-up).
- To give a person an account, make an invitation code. It is shown once:

  ```sh
  fn operator /var/lib/fn/fn.toml account invite --expires 86400
  ```

  The person uses it once to choose a login and password: on your
  [web page](web.md)'s **Make your account** page,
  or with fn's own command on their machine (it asks for the password):

  ```sh
  fn redeem news.example.org CODE carol --cafile cert.pem
  ```

  A node on another port than 119 (every OpenBSD node: its service cannot
  use a port below 1024) is named with its port:
  `fn redeem news.example.org:11563 CODE carol --cafile cert.pem`.

  See [accounts](operator.md#accounts-and-invitation-codes).

## 4. Reinstalling

fn is never upgraded in place. A new release is a fresh install, and the
store folder stays where it is. See
[new releases](operator.md#new-releases). A release opens only a store of
its own format; there are no migrations. A store of another format is
refused (`open refused reason=store-format: not an fn store of this
release: redeploy fresh`): set the node up again with `init`.

`store export` and `store import` move a store between installs of the same
format, for example to raise a limit fixed at `init`. Export before you
remove the installed release:

1. Stop the service and export the store, with the release still
   installed. The export runs as root, because the service account cannot
   make a folder in `/var/lib`; the `chown` lets the service account read it:

   ```sh
   systemctl stop fn                                                    # OpenBSD: rcctl stop fn
   /opt/fn/bin/fn operator /var/lib/fn/fn.toml store export /var/lib/fn-export
   chown -R fn:fn /var/lib/fn-export                                    # OpenBSD: _fn:_fn
   mv /var/lib/fn /var/lib/fn.old
   rm -rf /opt/fn
   sh fn/install.sh
   ```

   On OpenBSD, `/var/fn` is its own FFS1 partition, and `mv` refuses it
   (`cannot rename a mount point`). Move what is in it instead, then
   unpack the new release under `/usr/local/src` as in step 1:

   ```sh
   mkdir /var/fn.old && mv /var/fn/* /var/fn.old/
   rm -rf /usr/local/fn /usr/local/src/fn
   ```

   Below, read `/var/fn` for `/var/lib/fn` and `/var/fn.old` for
   `/var/lib/fn.old`.

2. As the service account, write the settings again (or copy `fn.toml`,
   `tls/` and `log/` from the old folder: without `log/` the service stops
   at start with `No such file or directory: '/var/lib/fn/log/fn.log'`).
   Then import instead of `init`:

   ```sh
   cp -Rp /var/lib/fn.old/fn.toml /var/lib/fn.old/tls /var/lib/fn.old/log /var/lib/fn/
   fn operator /var/lib/fn/fn.toml store import /var/lib/fn-export
   ```

3. Copy the node's secret keys and the logins back, then start the
   service. Without the keys the node refuses to start
   (`node secret .../store/keys/node-secret.key is missing`); without
   `auth.toml` every login is gone. The node then serves the same articles,
   numbers, Message-IDs and logins:

   ```sh
   cp -Rp /var/lib/fn.old/store/keys /var/lib/fn.old/store/auth.toml /var/lib/fn/store/
   cp -Rp /var/lib/fn.old/keys /var/lib/fn/                             # only if you ran peer keygen
   ```

   Copy back, too, every file a `peer add` named (its login file and the
   friend's certificate, such as `friend.fnauth` and `friend-cert.pem`):
   the peers are in the export, the files they name are not.

   The export does not carry them (see
   [the node's secret](operator.md#the-nodes-secret-key)). Do not make a
   new secret instead: it breaks cancels of earlier posts.

An export is **not a backup**. It holds the store's history only. It leaves
out the TLS keys, passwords, the node's secret keys, peer queues and program
state kept outside the store. Copy those yourself. The export's `MANIFEST`
checks each file, but cannot tell you whether it is the newest export.

If an import was interrupted, the next one refuses and names the folder it
left: `reason=interrupted-import` (nothing was set up: remove that folder
and import again) or `reason=publication-uncertain` (a store is there: run
`recover`, then remove that folder). An archive of another format is
refused (`reason=profile store-format`). `install.sh` asks the new release
about the existing node folder before copying anything, and refuses a store
of another format: redeploy fresh.

To remove fn: stop and disable the service. Then remove `/opt/fn`, the
service file (`/etc/systemd/system/fn.service` or `/etc/rc.d/fn`), the node
folder and the account.

## When the node refuses something

fn never guesses. When it cannot do something, it names the reason. The same
word shows in the reply, in `status` or `health`, and in the log. Every word it can print, made from fn's own code (the health
codes and the POST refusals): [fn FAQ, part 6](articles/fn-faq-6.txt).
