# Peering with fn.fg-goose.online

How to peer a news server with ember's public fn node,
`fn.fg-goose.online` (fsn1; its coordinates are in
[docs/nodes/fsn1.md](../../../docs/nodes/fsn1.md)). No outside peer is
named yet. It follows
[peering with a friend](../../../docs/peering-with-a-friend.md), which ran
between two real machines on 2026-09-26. The one difference is that this
node has a Let's Encrypt certificate: you verify it by its name against the
Let's Encrypt roots, not by a copy of its certificate. Of section A, only
the NAT case has run against the public node: hbox pulls from it since
2026-09-28 (its push stalls, PKT-882; `docs/nodes/hbox.md`). The steps
marked CHECK AT DEPLOY are ones the release docs do not yet show working.

## 0. What the public node is

| | |
| --- | --- |
| name | `fn.fg-goose.online`, A record 88.99.126.35 (no AAAA) |
| path identity | `fn.fg-goose.online` |
| port 119 | NNTP; `STARTTLS` is advertised, and `AUTHINFO` answers `483` until TLS is up |
| port 563 | NNTP over TLS from the first octet (`tls_port`) |
| certificate | Let's Encrypt, ECDSA P-256, renewed about every 60 days with a **new key** |
| login | required for everything except CAPABILITIES, HELP, DATE, MODE, QUIT, AUTHINFO and STARTTLS (`anonymous none`) |
| per-address limit | 4 connections from one address (`exposure-per-address 4`); a fifth gets `400 too many connections from this address` |
| total | 31 connections |
| silence | closed after 60 s with no first command, or after 600 s idle |
| failed logins | 10 per address per minute, then `400 too many authentication failures` |
| posting rate | 60 articles a minute per login; past that the connection waits and nothing is refused |
| groups carried | local.general, local.test, fn.general, fn.test, fn.announce, fn.docs; the peered hierarchy is ember's choice (section 4) |

There is no separate transit port. A peer connects to 119 or 563 like a
reader and logs in as the login ember bound to its node's principal. The
node decides a connection's role when it accepts it, from its peer table.

**Anchoring the certificate.** Every renewal brings a new certificate and a
new key. Do not pin the leaf certificate: your peer record would break
within about 60 days. Anchor on both Let's Encrypt roots in one file:

```sh
cat /etc/ssl/certs/ISRG_Root_X1.pem /etc/ssl/certs/ISRG_Root_X2.pem > isrg-roots.pem
# or: curl -sO https://letsencrypt.org/certs/isrgrootx1.pem; curl -sO https://letsencrypt.org/certs/isrg-root-x2.pem
openssl s_client -connect fn.fg-goose.online:563 -servername fn.fg-goose.online \
  -CAfile isrg-roots.pem -verify_return_error </dev/null 2>/dev/null | grep -E 'Verify return|subject='
```

This works because fn's client loads the anchor file with
`SSL_CTX_load_verify_locations` and checks the name with `SSL_set1_host`
(host/native/tls.lisp). A file of two roots anchors the node the same way a
single certificate does.

## A. Your node runs fn (the release tarball)

Your side follows
[peering with a friend](../../../docs/peering-with-a-friend.md) section 1:
bring a node up from the tarball, with its own path identity, TLS pair and
`peer keygen`. Your node must be reachable from the internet on the port
you name, or the public node cannot push to you. If it is not, see
"a node behind NAT" below.

In the commands below, `$F` is `bin/fn` and `$C` is `fn.toml`. `ME` is ember
on the public node, and `YOU` is the peer's operator; `friend` below is
their peer name. `N=/var/lib/fn` on the public node.

### A1. The invitation (ember)

```sh
# ME: the last two words are the public node's own address, signed into the invitation
$F operator $C peer invite friend 'local.*' YOUR-HOST YOUR-PORT \
    fn.fg-goose.online $N/keys $N/exchange/invitation-for-friend \
    fn.fg-goose.online 119
```

Ember sends you the file over a channel you both trust. It holds public
keys only.

CHECK AT DEPLOY: the release has run `MY-HOST` only as an IP literal. The
outbound dial resolves names (`fnn-connect-address`, host/native/io.lisp),
but no run has shown that `peer invite` and `peer accept` accept a name. If
either refuses the name, use the public IPv4 instead. That address changes
when the home ISP changes it (gap packet d).

### A2. The acceptance (you)

```sh
# YOU
$F operator $C peer accept invitation-for-friend $N/keys \
    YOUR-PATH-IDENTITY YOUR-HOST:YOUR-PORT acceptance-for-goose
$F operator $C peer list      # fn.fg-goose.online ... inbound=local.* outbound=- auth=principal:<ember's node principal>
```

Send `acceptance-for-goose` back to ember.

### A3. The confirm (ember)

```sh
# ME
$F operator $C peer confirm $N/exchange/acceptance-for-friend $N/exchange/invitation-for-friend
$F operator $C peer list      # friend ... auth=principal:<your node principal>
```

### A4. The protected feed both ways

Each side creates a login for the other node, bound to that node's
principal, and gives the other side the password out of band.

```sh
# ME: a login for your node, bound to your node's principal
printf 'PW-FOR-FRIEND\nPW-FOR-FRIEND\n' | $F operator $C principal set-password friend-node \
    --principal YOUR-NODE-PRINCIPAL-HEX --posting
# ME: how the public node logs in at yours
umask 077; printf 'FNAUTH1\ngoose-node\nPW-FOR-GOOSE\n' > $N/exchange/friend.fnauth
$F operator $C peer add friend YOUR-PATH-IDENTITY YOUR-HOST YOUR-PORT \
    'local.*' 'local.*' principal YOUR-NODE-PRINCIPAL-HEX \
    $N/exchange/friend.fnauth false true starttls YOUR-CERT-NAME $N/exchange/friend-cert.pem

# YOU: the mirror image; your anchor for the public node is isrg-roots.pem, not a leaf
printf 'PW-FOR-GOOSE\nPW-FOR-GOOSE\n' | $F operator $C principal set-password goose-node \
    --principal EMBER-NODE-PRINCIPAL-HEX --posting
umask 077; printf 'FNAUTH1\nfriend-node\nPW-FOR-FRIEND\n' > exchange/goose.fnauth
$F operator $C peer add fn.fg-goose.online fn.fg-goose.online fn.fg-goose.online 119 \
    'local.*' 'local.*' principal EMBER-NODE-PRINCIPAL-HEX \
    exchange/goose.fnauth false true starttls fn.fg-goose.online exchange/isrg-roots.pem
$F operator $C peer pull fn.fg-goose.online 20
```

The words of `peer add` are: name, path identity, address, port, inbound
wildmat, outbound wildmat, `principal HEX`, the credential profile, `false`
(never send the credential in the clear), `true` (`MODE STREAM`), and
`starttls NAME ANCHOR`. Your `YOUR-CERT-NAME` and `friend-cert.pem` are
the name and certificate your own node presents. If yours is self-signed,
send ember the certificate. If it is a CA's, send the CA roots, as above.

Streaming: `MODE STREAM` is enabled from the release carrying 5e52ea1e (the
served read yields after each submission, so two `TAKETHIS` in one socket
read are both taken: PKT-600, PRF-213); it is rejected at the boundary on any
older image.

### A5. Check it (both)

- Post to `local.general` on your node. The article appears on the public
  node, and your log shows `accepted feed peer=fn.fg-goose.online ...
  code=239`.
- Ember posts on the public node, and it appears on yours.
- Each side's log shows `pull peer=... round=done cursor=advanced
  transport=tls`.
- `$F operator $C health` on both reads clean. The public node's three
  `exposure` lines name the limits in force.
- A reader connected before the article arrived sees it after its next
  `GROUP`, or at least after a reconnect. Which of the two holds depends on
  whether reader-freshness has landed in the release.

### A node behind NAT

If the public node cannot reach you, A1 still names a real address for you:
`peer invite` refuses `-` for the invitee's HOST and PORT ("ACL2 refused the
invitation's words"; books/peer-invite.lisp `fn-pinv-hosts-okp` allows `-`
only for the inviter's own address, the last two words). Give your LAN
listener (for example `192.168.50.39 563`); it is only recorded, because the
public node's row for you gets `outbound=-` and never dials it (PKT-883,
planning/evidence/node-migrate-2026-09-28.md). Then give the public node an
inbound half only, and pull from it: `peer pull fn.fg-goose.online SECONDS`
on a timer. One
credential slot serves both directions of a peer, so a credentialed pull
needs outbound groups as well (PKT-431). The public node never dials you.

## B. Your node runs INN

INN's `innfeed` (2.7.4, the version fn's INN lab pins) sends `AUTHINFO` but
has no TLS. The public node answers `AUTHINFO` with `483` until TLS is
active, and it answers `IHAVE`/`CHECK` with `480` to a login-less
connection. So **INN cannot push to the public node** (gap packet b).
Until that is decided, the public node dials in both directions:

- **Public node to you, push:** ember adds your INN as a source-address
  peer. The feed is clear, sends no credential, and streams:

  ```sh
  # ME
  $F operator $C peer add friend YOUR-PATH-IDENTITY YOUR-INN-HOST 119 \
      'local.*' 'local.*' source-address YOUR-INN-ADDRESS true
  ```

  Your INN accepts it by address, in `incoming.conf`:

  ```
  peer goose {
      hostname: "fn.fg-goose.online"
      patterns: "local.*"
  }
  ```

  `innd` resolves the name when it loads the file. If the public IPv4
  changes, run `ctlinnd reload incoming.conf 'goose moved'`.

- **You to the public node, pull:** the public node pulls from your
  `nnrpd` with `NEWNEWS`/`ARTICLE` (`peer pull friend 60` on a timer).
  Your `readers.conf` must let the public node's address read `local.*`,
  and `inn.conf` must keep `allownewnews: true`. If `nnrpd` has TLS (port
  563, or `STARTTLS`), a TLS pull with a login is better than a clear one.
  CHECK AT DEPLOY: fn's pull has run against fn nodes over TLS and against
  the INN lab over loopback, but never against a remote INN.

Section "What the fn side has to answer" of
[the INN interop lab](../../../docs/interop-inn.md) lists which of fn's
answers `innfeed` retries and which it drops.

## Accounts for people

To give a person a reading and posting account, ember runs `$F operator $C
account invite --expires 86400`. The person then sends `XREDEEM CODE LOGIN`
and `XREDEEM PASS PASSWORD` over TLS, and afterwards logs in with
AUTHINFO. See [peering with a friend](../../../docs/peering-with-a-friend.md),
"An account for the friend on your node".

A newsreader such as tin connects to `fn.fg-goose.online` port 563 over
TLS. It verifies against the system trust store, so it needs no
certificate file.

## 4. Feed policy (ember decides)

The wildmat must name groups the public node carries. Its
small-community mission created `local.general` and `local.test`, and
`fn.general`, `fn.test`, `fn.announce` and `fn.docs` were added; hbox
peers on `fn.*`. The commands above write `local.*`: replace it with the
hierarchy ember picks. Cancels travel with the groups they name (PRF-163), so
`local.*` also carries an author's signed cancel of a `local.*` article.
A shared hierarchy with a more distinctive name (for example `goose.*`)
needs `group create` on every node before the first article. Ember names
the groups. Until she does, the default stands.
