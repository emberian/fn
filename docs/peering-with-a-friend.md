# Peering with a friend

This page takes a friend who has only the release tarball from a machine
with no fn on it to a node that peers with yours: one invitation each way,
articles flowing both ways over STARTTLS, each node logging in to the other
as the other's enrolled principal. Every command below ran on 2026-09-26
between two real machines on one LAN (the friend: persvati, Ubuntu 25.10;
you: an hbox scratch node, Ubuntu 24.10), from the release
`fn-8fb3768e8439-linux-x86_64.tar.gz`; the record is
[friends-peer](../planning/evidence/friends-peer-2026-09-26.md). It is a
walk of `bin/fn` as shipped, not a deployment claim.

In the commands, `ME` is your node and `FRIEND` the friend's. Replace the
addresses, ports and path identities with yours:

| | you (the inviter) | the friend |
| --- | --- | --- |
| address, port | 192.168.50.39, 11991 | 192.168.50.120, 11990 |
| path identity | `hbox-scratch.friends.fn.invalid` | `persvati.friends.fn.invalid` |
| node directory `N` | `/tank/fn/scratch/friends-peer/hnode` | `/home/ember/fn-node-friends` |

## 1. Bring a node up from the tarball (both of you)

You need Linux on x86-64 and, for the TLS pair below, an `openssl` command
(any version with EC keys). Nothing else: the tarball carries its Lisp
runtime, OpenSSL 3.5 and libsodium, and runs from wherever it is unpacked.
`$F` alone prints the operator's usage; `$F --version` prints the source
revision the tarball was built from.

```sh
cd $N
sha256sum -c fn-8fb3768e8439-linux-x86_64.tar.gz.sha256    # the sum you were given
tar xzf fn-8fb3768e8439-linux-x86_64.tar.gz
(cd fn-8fb3768e8439 && sha256sum -c --quiet SHA256SUMS)   # every file in it
F=$N/fn-8fb3768e8439/bin/fn
C=$N/node/fn.toml
mkdir -p node
$F operator $C mission small-community --host 192.168.50.120 --port 11990
```

`mission` writes `fn.toml`: the listener on that address, `[auth] required`
and `protected_only` (a login is needed, and only after STARTTLS), a TLS
pair under `node/tls/`, the log under `node/log/`. It does not make the TLS
pair. Make one whose subjectAltName is the address the other node will dial
(the other node verifies the handshake against this certificate and that
name):

```sh
openssl req -x509 -newkey ec -pkeyopt ec_paramgen_curve:P-256 -nodes -days 3650 \
  -subj /CN=persvati.friends.fn.invalid -addext subjectAltName=IP:192.168.50.120 \
  -keyout node/tls/key.pem -out node/tls/cert.pem
chmod 600 node/tls/key.pem
$F operator $C init                                   # local.general, local.test
$F operator $C policy set path-identity persvati.friends.fn.invalid
printf 'PASSWORD\nPASSWORD\n' | $F operator $C principal set-password ember --posting
```

`set-password` reads the password twice, from the terminal or from two lines
of standard input. Then the node's own keys, the principal that signs its
invitation or acceptance. `peer keygen` draws both pairs through the
tarball's own libsodium and OpenSSL 3.5, so no `openssl` command is needed:

```sh
$F operator $C peer keygen $N/keys            # prints: principal HEX
systemd-run --user --unit fn-friends -p MemoryMax=8G $F operator $C run
```

`keygen` refuses a directory that exists (it never overwrites keys), makes
it mode 0700 with every file 0600, and runs `peer genesis` over it. A key
directory made by hand (the `openssl genpkey` commands for Ed25519 and
ML-DSA-65, then `peer genesis KEYDIR`) works the same.

The key directory layout (`ed-public.bin` 32 octets, `ed-secret.bin` the
32-octet seed then the public key, the two ML-DSA-65 PEM files) is what
`peer genesis`, `invite` and `accept` read. The node answers from another
machine at once: `tools/node_probe.py 192.168.50.120 11990 --cafile cert.pem
--group local.general` with `FN_PROBE_USER`/`FN_PROBE_PASSWORD` set checks
the 483 before STARTTLS, the handshake, the login and a post read back.

## 2. One invitation, one acceptance, one confirm

You invite the friend. The last two words are your own address; the
invitation carries them, signed, so the friend's node can configure you:

```sh
# ME
$F operator $C peer invite persvati 'local.*' 192.168.50.120 11990 \
    hbox-scratch.friends.fn.invalid $N/keys $N/exchange/invitation-for-persvati \
    192.168.50.39 11991
```

Send the invitation file to the friend (it holds public keys only). The
friend accepts; this enrols your principal on the friend's node and, in one
configuration record before that enrolment, configures you as a peer:

```sh
# FRIEND
$F operator $C peer accept $N/exchange/invitation-for-persvati $N/keys \
    persvati.friends.fn.invalid 192.168.50.120:11990 $N/exchange/acceptance-for-hbox
$F operator $C peer list
hbox-scratch.friends.fn.invalid path-identity=hbox-scratch.friends.fn.invalid address=192.168.50.39 port=11991 security=clear inbound=local.* outbound=- auth=principal:70fc9ddc...
```

The friend sends the acceptance back. You confirm: one record consumes the
invitation and configures the friend, then the friend's principal is
enrolled here:

```sh
# ME
$F operator $C peer confirm $N/exchange/acceptance-for-hbox $N/exchange/invitation-for-persvati
$F operator $C peer list
persvati path-identity=persvati.friends.fn.invalid address=192.168.50.120 port=11990 security=clear inbound=local.* outbound=- auth=principal:60779285...
```

An invitation made with `- -` in place of your address still enrols you at
the friend's node, and configures nothing there.

## 3. The protected feed both ways

The records `accept` and `confirm` write are clear-transport and inbound
only. Each side now gives the other a login bound to the other node's
principal (the `HEX` its `peer list` shows), keeps the password the other
side gave it in a credential profile, and replaces the peer record with its
STARTTLS form and both halves. Exchange the passwords and certificates out
of band.

```sh
# ME: a login for the friend's node, bound to its principal
printf 'PW-FOR-FRIEND\nPW-FOR-FRIEND\n' | $F operator $C principal set-password persvati-node \
    --principal 607792851af81f99899a21cb728087edcb137e42883e11d83e9fc458d4d33033 --posting
# ME: how I log in at the friend's node (the login the friend made for me)
umask 077; printf 'FNAUTH1\nhbox-node\nPW-FOR-ME\n' > $N/exchange/persvati.fnauth
$F operator $C peer add persvati persvati.friends.fn.invalid 192.168.50.120 11990 \
    'local.*' 'local.*' \
    principal 607792851af81f99899a21cb728087edcb137e42883e11d83e9fc458d4d33033 \
    $N/exchange/persvati.fnauth false true starttls 192.168.50.120 $N/exchange/persvati-cert.pem
$F operator $C peer pull persvati 20
```

`peer add` reaches the running node through its control socket and
replaces the record `accept` or `confirm` wrote without a restart (the
live reconfiguration path; observed in tests/test_native_friends_feed.py).
The friend does the mirror image (a login `hbox-node` bound to your
principal, a profile naming `persvati-node` and the password you gave, `peer
add hbox-scratch.friends.fn.invalid ... starttls 192.168.50.39 hbox-cert.pem`,
`peer pull hbox-scratch.friends.fn.invalid 20`). The words of `peer add`, in
order: name, path identity, address, port, inbound wildmat, outbound
wildmat, `principal HEX` (who the peer is when it logs in here), the
profile file this node logs in to the peer with, `false` (never send the
credential in the clear), `true` (stream with `MODE STREAM`), then `starttls
SERVER-NAME ANCHOR-PEM` (the name the peer's certificate must carry, and its
certificate as the only anchor).

**A cancel travels with the groups it names.** A control article is filed
under `control.cancel`, and it is offered to a peer whose outbound wildmat
matches its Newsgroups names *or* its filing group (RFC 5537 sections 3.6
and 5.3; PRF-163). With `local.*` alone, the author's signed cancel of a
`local.general` article reaches the friend and withdraws the target there.
Before PRF-163 it was offered under `control.cancel` alone and never left
the origin (observed: `<friends-t1@persvati.invalid>`).

What you should then see in each `node/log/fn.log`:

```
accepted feed peer=persvati message-id=<...> code=239 ...       # pushed, TAKETHIS accepted
pull peer=persvati round=done cursor=advanced transport=tls     # pulled over STARTTLS as a principal
```

## 4. Check it

Post on one node and read on the other (`tools/fn_client.py post
local.general --node 192.168.50.120:11990 --cafile persvati-cert.pem`, then
`read local.general --all --node 192.168.50.39:11991 --cafile
hbox-cert.pem`). The article keeps its Message-ID and its authored source
(the article without Path, Xref, Injection-Date, Injection-Info and
FN-Authorship); its Path grows by the relaying node, and its local article
number is each node's own. The session's table is
`planning/evidence/friends-peer-2026-09-26/identity-after-restart.txt`.

A node restarted, or running with a skewed clock, resumes both feeds from
where they were: the push queue re-offers what the peer has not taken
(`438` for what it already has), and the pull cursor is kept in the *remote*
node's clock (the round asks the peer `DATE` first, RFC 3977 section 7.1),
so a ten-minute skew on one side neither skips nor repeats an article.
Observed with the friend's node at +10 minutes and both nodes restarted:
seven articles, each stored exactly once on each node.

A signed article withdrawn on its origin by its author's signed cancel
answers `430 withdrawn` on the other node too, once the cancel arrives
there: the other node verifies the cancel under the author's enrolled keys
(the node principals are enrolled by the exchange above).

A friend who rotates keys posts a signed succession to `fn.keys` (the
node needs a `keys` grant for the friend's principal: `operator CONFIG
control grant PRINCIPAL-HEX keys fn.keys`). If the statement arrived before
the grant, it declined; after granting, `operator CONFIG keys redecide
MESSAGE-ID` enrols the successor without a restart (docs/operator.md, "Re-decide
a declined key statement").

Each node decides a cancel again under its own grants. The author's own
cancel withdraws on both nodes; a moderator's cancel of someone else's
unsigned article withdraws only on the node where you ran `control grant`
for that moderator over the article's group, so grant it on both nodes if
you both want it honoured. The order does not matter: a cancel that
arrives before its article hides the article from its first appearance, a
restart between the two changes nothing, and a reader already connected
keeps seeing what it saw until it posts or reconnects
(`tests/test_native_control_across_peers.py`, SCN-100).

`hybrid-author` names its refusal: a signed article whose `Newsgroups`
names a group this node does not carry is refused `UNKNOWN-GROUP` (exit
1); ask your friend to create the group, or post to one you both carry.

## What is not here

- A stranger's own account on your node: today you make it
  (`principal set-password`) and tell them the password. An invitation-code
  flow (the operator issues a code, the stranger redeems it over the reader
  port) is specified, not built (PKT-401).
- A view in which every article is withdrawn (two cancels by one author
  naming each other) answers the plain `430 no article with that
  message-id` rather than `430 withdrawn`; and the BP receiver's refusal
  line of an unfiled control article reads `reason=none` (PKT-443).
- A friend whose server keeps listing an article it cannot produce (it
  answers `ARTICLE` with 430) no longer stalls your pull: the other articles
  arrive in the same round, the pull asks from the same instant for a few
  rounds (`peer pull NAME SECONDS ROUNDS`; 5 when ROUNDS is left out)
  and then moves on, logging `dropped=<id>` once. What is not here yet: a
  friend's server that refuses `MODE STREAM` is still stopped per process
  (a restart spends one `MODE STREAM` again) and is not fed with IHAVE on
  the same connection; set its peer record's streaming word to `false`
  (PKT-431).
- One credential slot per peer serves both directions, so a credentialed
  pull needs outbound groups too (PKT-431).
