# Installing fn

fn is a news server: it speaks NNTP (the Usenet protocol) to readers and to
other fn nodes, and it keeps what it accepts in a store of its own. Every
decision it makes about an article, a login, a peer or its store is taken
by executable ACL2 code that ships inside the program. A node is one
directory of files, one configuration file and one service. This page takes
you from the download to a node that others reach over TLS.

A release is one file per platform, `fn-REV-linux-x86_64.tar.gz` or
`fn-REV-openbsd-amd64.tar.gz` (REV is the first twelve digits of the source
revision it was built from), with a `SHA256SUMS` file beside it. The tarball
carries its own Lisp runtime, libsodium and the ML-DSA-65 library; it uses
your system's TLS library (OpenSSL 3.0 or later on Linux, LibreSSL on
OpenBSD). It needs no Python, no compiler and nothing else from the build.

## 1. Download, verify, unpack, install

Linux (x86-64, systemd), as root:

```sh
sha256sum -c --ignore-missing SHA256SUMS
tar -xzf fn-REV-linux-x86_64.tar.gz
sh fn/install.sh
```

OpenBSD (amd64), as root:

```sh
sha256 -C SHA256SUMS fn-REV-openbsd-amd64.tar.gz
tar -xzf fn-REV-openbsd-amd64.tar.gz
sh fn/install.sh
```

`install.sh` checks every file of the release against `fn/SHA256SUMS`,
prints the revision (`fn REV...`, the full 40 digits), copies the release to
`/opt/fn` (OpenBSD: `/usr/local/fn`), creates the service account `fn`
(OpenBSD: `_fn`) and the node directory `/var/lib/fn` (OpenBSD: `/var/fn`),
and installs the service: `/etc/systemd/system/fn.service` or
`/etc/rc.d/fn`. It starts nothing. It refuses to install over an existing
`/opt/fn`: an installation is one directory (see
[Reinstalling](#4-reinstalling-and-moving-data)). `--prefix DIR`, `--node
DIR` and `--user NAME` choose other places; `--no-service` installs no
account and no unit and writes the rendered unit into the node directory
instead (for a machine where you run the node yourself).

On OpenBSD the directory must be on a file system mounted `wxallowed` (the
Lisp runtime maps writable code; `/usr/local` is mounted so by default).

`/opt/fn/bin/fn --version` prints the revision at any time; `fn` alone
prints the operator's usage, and `fn operator CONFIG help VERB` the grammar
of one verb.

## 2. The first node

Every command below runs as the service account, in the node directory,
with the release on the path. Start a shell that way:

```sh
sudo -u fn sh -c 'cd /var/lib/fn && PATH=/opt/fn/bin:$PATH exec sh'   # OpenBSD: doas -u _fn ...
```

Write the configuration. `mission small-community` is a node for a group of
people: logins are required and only after TLS, `local.general` and
`local.test` are served, the TLS pair and the log live under the node
directory. `--host` is the address the node listens on (a numeric address;
the wildcard `0.0.0.0` is refused, so you name the interface you put in
service) and `--port` its NNTP port:

```sh
fn operator /var/lib/fn/fn.toml mission small-community --host 203.0.113.7 --port 119
```

The node needs a TLS certificate and key at the two paths `fn.toml` names
(`tls/cert.pem`, `tls/key.pem`). Use one you have (Let's Encrypt or your
own CA: copy the pair there, key mode 0600), or make a self-signed one whose
subjectAltName is the name or address others dial (they verify against
exactly this certificate, so give it to them):

```sh
openssl req -x509 -newkey ec -pkeyopt ec_paramgen_curve:P-256 -nodes -days 3650 -subj /CN=news.example.org -addext subjectAltName=DNS:news.example.org,IP:203.0.113.7 -keyout tls/key.pem -out tls/cert.pem
```

Create the store, name the node, and add a login that may post (the
password is read twice, from the terminal or from two lines of standard
input):

```sh
fn operator /var/lib/fn/fn.toml init   # docs-check: skip (init under the mission fn.toml above; the grammar book configuration names no mission)
fn operator /var/lib/fn/fn.toml policy set path-identity news.example.org
fn operator /var/lib/fn/fn.toml principal set-password alice --posting
```

Leave the account's shell and start the service as root:

```sh
systemctl enable --now fn          # OpenBSD: rcctl enable fn && rcctl start fn
```

That is the whole installation. Check it:

```sh
fn operator /var/lib/fn/fn.toml status
fn operator /var/lib/fn/fn.toml health
```

`status` prints the store's figures and whether the node is serving;
`health` prints one line per condition and exits with the code of the first
one held ([the table below](#when-the-node-refuses-something)). Under
systemd the node logs to its log file (`log/fn.log` in the node directory);
under rc.d to syslog.

### Reading and posting from another machine

Any NNTP client that speaks STARTTLS (RFC 4642) reaches the node: it
connects to the port, sends `STARTTLS`, verifies the certificate, then logs
in with `AUTHINFO USER` and `AUTHINFO PASS` (RFC 4643). Before TLS the node
answers a login with `483`, so a password never crosses in the clear. A
client that only speaks TLS from the first byte (port 563, as `tin` does)
needs `tls_port = 563` added to `[listener]` in `fn.toml`; restart the
service after editing it.

## 3. Peering with a friend

Two nodes peer by exchanging one signed invitation and one signed
acceptance. Each node first makes its own keys (an Ed25519 pair and an
ML-DSA-65 pair, in a new directory it makes with mode 0700; it prints the
node's principal):

```sh
fn operator /var/lib/fn/fn.toml peer keygen /var/lib/fn/keys
```

You invite your friend: the friend's name, the groups you offer, the
friend's address and port and path identity, your key directory, the file
to write, and your own address and port (carried in the invitation, signed,
so the friend's node can configure yours):

```sh
fn operator /var/lib/fn/fn.toml peer invite friend 'local.*' 198.51.100.9 119 friend.example.net /var/lib/fn/keys /var/lib/fn/invitation-for-friend 203.0.113.7 119
```

Send the invitation file (it holds public keys only). The friend accepts it
with their key directory, their own path identity and address, and the file
to write back:

```sh
fn operator /var/lib/fn/fn.toml peer accept /var/lib/fn/invitation-for-friend /var/lib/fn/keys friend.example.net 198.51.100.9:119 /var/lib/fn/acceptance-for-you
```

You confirm with the acceptance they send back and your invitation:

```sh
fn operator /var/lib/fn/fn.toml peer confirm /var/lib/fn/acceptance-for-you /var/lib/fn/invitation-for-friend
fn operator /var/lib/fn/fn.toml peer list
```

Each side now enrols the other's principal and knows its address. To carry
the feed over TLS with each node logging in to the other, each side gives
the other a login bound to the other node's principal and replaces the peer
record with its STARTTLS form; `fn operator CONFIG help peer` prints the
whole grammar of `peer add`, whose last words are `starttls SERVER-NAME
ANCHOR-PEM` (the name the peer's certificate carries, and that certificate
as the only anchor).

An account for a person rather than a node is one code, printed once:

```sh
fn operator /var/lib/fn/fn.toml account invite --expires 86400
```

The person redeems it over TLS with `XREDEEM CODE LOGIN` then `XREDEEM PASS
PASSWORD`, and from then on logs in as LOGIN.

## 4. Reinstalling, and moving data

A node is never upgraded in place. A new release is installed fresh, and
the data that must survive travels as an export: the exact records the
store committed, its profile and its identity. With the old release still
installed:

```sh
systemctl stop fn                                                    # OpenBSD: rcctl stop fn
fn operator /var/lib/fn/fn.toml store export /var/lib/fn-export
mv /var/lib/fn /var/lib/fn.old
rm -rf /opt/fn
sh fn/install.sh
```

Then, as the service account in the new node directory: write the
configuration again (`mission`, the TLS pair; or copy `fn.toml` and `tls/`
from the old directory) and import instead of `init`:

```sh
fn operator /var/lib/fn/fn.toml store import /var/lib/fn-export
```

and start the service. The imported store answers with the same articles,
numbers and Message-IDs. A release refuses to open a store of another store
format by name (`reason=store-format`), and `install.sh` asks the new
release about an existing node directory before it copies anything, so a
reinstall over an incompatible store stops before it starts.

To remove fn entirely: stop and disable the service, then remove `/opt/fn`,
the unit (`/etc/systemd/system/fn.service` or `/etc/rc.d/fn`), the node
directory and the account.

## When the node refuses something

fn never guesses. A request it cannot honour is refused with a reason word,
and the same word appears in the reply, in `status` or `health`, and in the
log. The two tables below are generated from the tables inside the program
(the ACL2 books the release was built from), so they list every word it can
print for these two things.

<!-- generated by docs_check --write: reasons (do not edit by hand) -->

`health` exits with the code of the first condition held, in this order (0: every condition clear; 19: some condition could not be observed, as the two feed conditions cannot while the node is stopped):

| exit | condition | what it means, what to do |
| --- | --- | --- |
| 20 | `fenced` | a process holds the store (the node is starting, or another command runs), or the owner does not answer: wait and ask again; never delete the lock |
| 21 | `exhausted` | the store reached a counter's ceiling (a transaction id or the retention count); nothing raises it in place |
| 22 | `unqualified-profile` | the store runs the development profile, which is for tests: make the node again with a `mission` |
| 23 | `space-pressure` | free headroom is low on transactions, history or retention: `capacity` says which; release obligations or move to a larger profile |
| 24 | `no-route` | forwarding obligations wait and no BP route is configured |
| 25 | `stranded-transfer` | a peer refused an article past its retry bound: fix the peer |
| 26 | `unavailable-peer` | a peer has articles waiting and no connection: check its address and port (`peer list`) and that it is up |
| 27 | `receipt-debt` | forwarding obligations wait for the receipts that release them |

A refused POST is answered `441` with the reply below, and the log line for it starts `refused` and names the reason word:

| reason | the reply |
| --- | --- |
| `unparsable` | `441 posting failed; the article is not valid syntax` |
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
