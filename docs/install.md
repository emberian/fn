# Installing fn

This page takes you from the download to a running node that others can
reach safely. Words you may not know are in
[the short glossary](README.md#words-you-will-meet).

## What you need

- A Linux machine (x86-64, with systemd) or an OpenBSD 7.9 machine (amd64).
- On Linux: glibc 2.36 or later (Debian 12, Ubuntu 24.04 or newer) and
  OpenSSL 3.0 or later. On OpenBSD, nothing extra.
- Root access, for the install and the service.
- A disk that really saves data when asked. Read
  [storage](operator.md#1-choose-the-disk-for-the-store) before you begin.
  On OpenBSD this matters most: the store needs its own FFS1 partition.

Each release is one file per platform, `fn-6.7.N-linux-x86_64.tar.gz` or
`fn-6.7.N-openbsd-amd64.tar.gz`, with a `SHA256SUMS` file beside it. N goes
up by one with each release. The release brings everything it needs except
the system's TLS library.

## 1. Check, unpack and install

As root, on Linux:

```sh
sha256sum -c --ignore-missing SHA256SUMS
tar -xzf fn-6.7.N-linux-x86_64.tar.gz
sh fn/install.sh
```

As root, on OpenBSD:

```sh
sha256 -C SHA256SUMS fn-6.7.N-openbsd-amd64.tar.gz
tar -xzf fn-6.7.N-openbsd-amd64.tar.gz
sh fn/install.sh
```

You will see the version, like `fn 6.7.N (REV)`. The installer:

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

`/opt/fn/bin/fn --version` prints the version at any time. `fn` alone lists
the commands, and `fn operator CONFIG help VERB` explains one command.

## 2. Set up the first node

1. Open a shell as the service account, in the node folder:

   ```sh
   sudo -u fn sh -c 'cd /var/lib/fn && PATH=/opt/fn/bin:$PATH exec sh'   # OpenBSD: doas -u _fn ...
   ```

2. Write the settings file. Put your server's own address after `--host`
   (`0.0.0.0` is refused: name the address you mean) and the port after
   `--port`:

   ```sh
   fn operator /var/lib/fn/fn.toml mission small-community --host 203.0.113.7 --port 119
   ```

   `small-community` means: logins are required, only over an encrypted
   connection, and the groups `local.general` and `local.test` are served.

3. Give the node a TLS certificate. Copy one you have (for example from
   Let's Encrypt) to `tls/cert.pem` and `tls/key.pem`, with the key at mode
   0600. Or make your own. Use the name or address people will dial, and
   give them the certificate file:

   ```sh
   openssl req -x509 -newkey ec -pkeyopt ec_paramgen_curve:P-256 -nodes -days 3650 -subj /CN=news.example.org -addext subjectAltName=DNS:news.example.org,IP:203.0.113.7 -keyout tls/key.pem -out tls/cert.pem
   ```

4. Create the store, name the node, and add a login that may post. The
   password is asked twice:

   ```sh
   fn operator /var/lib/fn/fn.toml init   # docs-check: skip (init under the mission fn.toml above; the grammar book configuration names no mission)
   fn operator /var/lib/fn/fn.toml policy set path-identity news.example.org
   fn operator /var/lib/fn/fn.toml principal set-password alice --posting
   ```

   `init` also makes the node's secret key file. The node's name
   (`path-identity`) should be its public host name.

5. Leave the account's shell. As root, start the service:

   ```sh
   systemctl enable --now fn          # OpenBSD: rcctl enable fn && rcctl start fn
   ```

6. Check it:

   ```sh
   fn operator /var/lib/fn/fn.toml status
   fn operator /var/lib/fn/fn.toml health
   ```

   `status` shows the store's figures and whether the node is serving.
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

## 3. Friends and accounts

- To connect your node with a friend's node, follow
  [Peering with a friend](peering-with-a-friend.md).
- To give a person an account, make an invitation code. It is shown once:

  ```sh
  fn operator /var/lib/fn/fn.toml account invite --expires 86400
  ```

  The person uses it once, over TLS, to choose a login and password. See
  [accounts](operator.md#accounts-and-invitation-codes).

## 4. Reinstalling

fn is never upgraded in place. A new release is a fresh install, and the
store folder stays where it is. See
[new releases](operator.md#new-releases). Only when a release cannot open
the old store do you move the data through an export:

1. Stop the service and export the store, with the old release still
   installed:

   ```sh
   systemctl stop fn                                                    # OpenBSD: rcctl stop fn
   fn operator /var/lib/fn/fn.toml store export /var/lib/fn-export
   mv /var/lib/fn /var/lib/fn.old
   rm -rf /opt/fn
   sh fn/install.sh
   ```

2. As the service account, write the settings again (or copy `fn.toml` and
   `tls/` from the old folder). Then import instead of `init`:

   ```sh
   fn operator /var/lib/fn/fn.toml store import /var/lib/fn-export
   ```

3. Copy the node's secret keys back, then start the service. The node
   serves the same articles, numbers and Message-IDs:

   ```sh
   cp -Rp /var/lib/fn.old/store/keys /var/lib/fn/store/keys
   ```

   The export does not carry them (see
   [the node's secret](operator.md#the-nodes-secret-key)).

An export is **not a backup**. It holds the store's history only. It leaves
out the TLS keys, passwords, the node's secret keys, peer queues and program
state kept outside the store. Copy those yourself. The export's `MANIFEST`
checks each file, but cannot tell you whether it is the newest export.

If an import was interrupted, the next one refuses and names the folder it
left: `reason=interrupted-import` (nothing was set up: remove that folder
and import again) or `reason=publication-uncertain` (a store is there: run
`recover`, then remove that folder). A release refuses a store of another
format (`reason=store-format`). `install.sh` asks the new release about the
existing node folder before copying anything.

To remove fn: stop and disable the service. Then remove `/opt/fn`, the
service file (`/etc/systemd/system/fn.service` or `/etc/rc.d/fn`), the node
folder and the account.

## When the node refuses something

fn never guesses. When it cannot do something, it names the reason. The same
word shows in the reply, in `status` or `health`, and in the log. These two
tables are made from fn's own code, so they list every word it can print.

<!-- generated by docs_check --write: reasons (do not edit by hand) -->

`health` ends with the code of the first problem it found, in this order. 0 means no problem. 19 means fn could not check something (the two peer checks need the node running):

| code | problem | what it means, what to do |
| --- | --- | --- |
| 20 | `fenced` | something holds the store: the node is starting, or another command runs, or the node does not answer. Wait and ask again. Never delete the lock |
| 21 | `exhausted` | the store used up a counter (transactions or held space) that nothing raises in place |
| 22 | `unqualified-profile` | the store uses the test settings. Make the node again with a `mission` |
| 23 | `space-pressure` | the store is nearly full. `capacity` says which part; release what is held, or move to larger settings |
| 24 | `no-route` | articles wait to be forwarded and no BP route is set |
| 25 | `stranded-transfer` | a peer kept refusing an article and fn stopped offering it. Fix the peer |
| 26 | `unavailable-peer` | a peer has articles waiting and is not connected. Check its address and port (`peer list`) and that it is running |
| 27 | `receipt-debt` | articles were forwarded and wait for the receipts that confirm them |

When fn refuses a post, the reply starts `441` and the log line starts `refused` and names the reason:

| reason | the reply |
| --- | --- |
| `unparsable` | `441 posting failed; the article is not valid syntax` |
| `header-fields-limit` | `441 posting failed; the header has more fields than the profile's max-header-fields` |
| `header-lines-limit` | `441 posting failed; the header has more lines than the profile's max-header-lines` |
| `header-octets-limit` | `441 posting failed; the header has more octets than the profile's max-header-octets` |
| `group-read-only` | `441 posting failed; a group this article names is read-only here (LIST ACTIVE status n)` |
| `approval-not-moderator` | `441 posting failed; Approved is accepted only from a moderator of each moderated group named (LIST ACTIVE status m)` |
| `moderation-unavailable` | `441 posting failed; a moderated group is named and the article could not be forwarded to its moderation queue` |
| `injection-info` | `441 posting failed; Injection-Info must not be supplied` |
| `xref` | `441 posting failed; Xref must not be supplied` |
| `injection-date-present` | `441 posting failed; Injection-Date must not be supplied` |
| `path-present` | `441 posting failed; Path must not be supplied` |
| `path-malformed` | `441 posting failed; Path is not a valid path` |
| `path-duplicate` | `441 posting failed; Path appears more than once` |
| `path-posted` | `441 posting failed; Path must not carry a POSTED diagnostic` |
| `newsgroups-missing` | `441 posting failed; Newsgroups is required` |
| `newsgroups-duplicate` | `441 posting failed; Newsgroups appears more than once` |
| `newsgroups-invalid` | `441 posting failed; Newsgroups is not a valid newsgroup list` |
| `message-id-duplicate` | `441 posting failed; Message-ID appears more than once` |
| `message-id-invalid` | `441 posting failed; Message-ID is not a valid identifier` |
| `from-missing` | `441 posting failed; From is required` |
| `from-duplicate` | `441 posting failed; From appears more than once` |
| `from-invalid` | `441 posting failed; From is not a valid mailbox list` |
| `subject-missing` | `441 posting failed; Subject is required` |
| `subject-duplicate` | `441 posting failed; Subject appears more than once` |
| `date-duplicate` | `441 posting failed; Date appears more than once` |
| `no-groups` | `441 posting failed; no newsgroup was named` |
| `unknown-group` | `441 posting failed; a named newsgroup is not carried here` |
| `oversize` | `441 posting failed; the article exceeds the configured size` |
| `clock-unusable` | `441 posting failed; this server has no usable clock reading` |
| `clock-out-of-range` | `441 posting failed; this server clock is outside the modelled range` |
| `posting-disallowed` | `441 posting failed; posting is not permitted` |

<!-- end generated reasons -->
