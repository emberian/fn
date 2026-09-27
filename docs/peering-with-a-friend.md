# Peering with a friend

This page connects your node with a friend's node. Afterwards, articles
posted on either node appear on both. The link is encrypted, and each node
logs in to the other. The steps were tested between two real machines in
September 2026. Words you may not know are in
[the short glossary](README.md#words-you-will-meet).

The examples use these values. Replace them with yours:

| | you | your friend |
| --- | --- | --- |
| address and port | 203.0.113.7, 119 | 198.51.100.9, 119 |
| node name (path identity) | `news.example.org` | `friend.example.net` |
| peer name for the other node | `friend` (you choose it in `peer invite`) | `news.example.org` (`peer accept` files you under your node name) |

## 1. Both of you: set up a node

Each of you follows [Installing fn](install.md), steps 1 and 2. Then each of
you makes the node's peering keys. The command prints the node's identity,
`principal HEX`. Note it:

```sh
fn operator /var/lib/fn/fn.toml peer keygen /var/lib/fn/keys
```

`peer keygen` makes a new private folder. It refuses a folder that exists,
so it never overwrites keys.

## 2. Invite, accept, confirm

1. **You** write an invitation. The words are: your friend's peer name, the
   groups you offer, your friend's address and port, YOUR OWN node name (the
   one you set with `policy set path-identity`: your friend's node files you
   under it), your keys folder, the file to write, and your own address and
   port. An address may be a host name or an IPv4 address:

   ```sh
   fn operator /var/lib/fn/fn.toml peer invite friend 'local.*' 198.51.100.9 119 news.example.org /var/lib/fn/keys /var/lib/fn/invitation-for-friend 203.0.113.7 119
   ```

   `'local.*'` also offers a private group whose name starts `local.`.
   Keep private groups out: `'local.*,!local.private*'`.

2. Send the invitation file to your friend. It holds no secrets.

3. **Your friend** accepts it. The words are: the invitation, their keys
   folder, their node name, their address, and the file to write back:

   ```sh
   fn operator /var/lib/fn/fn.toml peer accept /var/lib/fn/invitation-for-friend /var/lib/fn/keys friend.example.net 198.51.100.9:119 /var/lib/fn/acceptance-for-you
   ```

4. Your friend sends the acceptance file back.

5. **You** confirm, then check:

   ```sh
   fn operator /var/lib/fn/fn.toml peer confirm /var/lib/fn/acceptance-for-you /var/lib/fn/invitation-for-friend
   fn operator /var/lib/fn/fn.toml peer list
   ```

   `peer list` now shows your friend, with their address and identity.

If it goes wrong:

- `already-enrolled`: the invitation was already accepted. Nothing is left
  to do.
- `not-current-keys` or `revoked`: your friend signed with keys they have
  since replaced or withdrawn. Ask for a new acceptance.
- `genesis`: your node has never known this friend, and the keys are not
  the ones they started with. Start again with a fresh invitation.

## 3. Turn on the encrypted feed, both ways

So far the link is set up for one direction only, and not encrypted. Now each
of you gives the other a login and switches the link to encrypted.
Exchange passwords and certificate files by a channel you trust.

**You** do these steps. Your friend does the same, with the names swapped:
their peer name for you is your node name (`news.example.org`), as
`peer list` on their node shows.

1. Make a login for your friend's node, tied to its identity (the HEX from
   `peer list`). Choose a password and give it to your friend:

   ```sh
   fn operator /var/lib/fn/fn.toml principal set-password friend-node --principal PRINCIPAL-HEX --posting
   ```

2. Save the login your friend made for you, in a file only you can read. Its
   three lines are `FNAUTH1`, the login, the password:

   ```sh
   umask 077; printf 'FNAUTH1\nme-node\nPASSWORD-FROM-FRIEND\n' > /var/lib/fn/friend.fnauth
   ```

3. Replace the peer with its encrypted form, then start fetching from it
   every 20 seconds:

   ```sh
   fn operator /var/lib/fn/fn.toml peer add friend friend.example.net 198.51.100.9 119 'local.*' 'local.*' principal PRINCIPAL-HEX /var/lib/fn/friend.fnauth false true starttls 198.51.100.9 /var/lib/fn/friend-cert.pem
   fn operator /var/lib/fn/fn.toml peer pull friend 20
   ```

4. Check the login from step 1: its last word is `applied` when the node
   was running (the node took the password at once), or
   `effective-at-next-start` when it was not. If it said `restart-required`
   (your `fn.toml` names no `[control] path`), restart the node (as root:
   `systemctl restart fn`; OpenBSD: `rcctl restart fn`). A pull that fails
   says why in the log, for example
   `pull peer=friend round=failed cursor=held at=preamble reason=login-refused code=481 phase=auth-pass`:
   your friend's node refused the login you saved in step 2.

The words of `peer add`, in order: peer name, node name, address, port,
groups you take, groups you send, `principal HEX` (who logs in as this
peer), your login file for their node, `false` (never send the password
unencrypted), `true` (fast "streaming" mode; use `false` if their server
cannot stream), then `starttls`, the name on their certificate, and their
certificate file. `fn operator CONFIG help peer` prints the full list.

**A friend with a host name and a public certificate** (such as Let's
Encrypt) can be added by name. Then no certificate file is needed, and a
friend who changes address is found again:

```sh
fn operator /var/lib/fn/fn.toml peer add friend friend.example.net news.friend.example 563 'local.*' 'local.*' principal PRINCIPAL-HEX /var/lib/fn/friend.fnauth false true implicit - -
```

`implicit` means TLS from the first byte, as on port 563. The two `-` mean:
check the host's own name, against the system's public certificates. If the
name does not match or cannot be found, the log says so
(`outcome=name-mismatch` or `outcome=unresolved`) and fn tries again later.
`peer invite` also takes host names.

## 4. Check it

Post on one node and read on the other. With the [client](agents.md):

```sh
python3 tools/fn_client.py --node 198.51.100.9:119 --cafile friend-cert.pem post local.general --subject hello < note.txt
python3 tools/fn_client.py --node 203.0.113.7:119 --cafile my-cert.pem read local.general --all
```

The article keeps its Message-ID. Its article number is each node's own.
Each node's `log/fn.log` shows lines like:

```
accepted feed peer=friend message-id=<...> code=239 ...
pull peer=friend round=done cursor=advanced transport=tls
```

After a restart, or with a clock that is wrong by minutes, both feeds carry
on where they were. Nothing is skipped or repeated. An article dated more
than a day ahead of your node's clock is refused as "dated in the future".
If you see that, check both clocks.

## Catching up

A new node starts empty, and a node that was switched off for a while has
missed what its friend received. The feed from step 3 only carries new
articles. To copy everything your friend's node already holds, turn on
catching up:

```sh
fn operator /var/lib/fn/fn.toml peer catch-up friend 3600
```

The number is how often, in seconds, your node checks again. Your node then
asks your friend's node for its articles in large batches. It checks each
batch with a digest before using any of it, and then takes each article as
if your friend had just sent it: your node's own rules decide, articles it
already has are skipped, and the article numbers are your node's own. It
uses the same connection settings as `peer add` (address, encryption,
login). It reads only what your login on your friend's node may read, and only
the groups you take from your friend (`peer add`'s groups). An article in a
group your node does not have is refused and counted as `refused`: create
the group first.

Each round writes one line to `log/fn.log`:

```
catch-up peer=friend round=done position=1000 end=1000 imported=998 duplicate=2 refused=0 digest=... transport=tls
```

`position` is how far into your friend's articles your node has come, and
`end` is how many your friend's node has. When they are equal, you have
caught up. After that, each round only fetches what is new. If your node is
stopped in the middle, it carries on from the last batch it finished.

If it goes wrong:

- `reason=digest-mismatch`: a batch arrived damaged. Nothing from it was
  used. The next round asks for it again.
- `reason=peer-lacks-catch-up`: your friend's node is older and does not
  know how to send batches. Use `peer pull` instead.
- `reason=local-deferred`: your own node asked to try an article later.
  The next round tries again.

To stop: `fn operator /var/lib/fn/fn.toml peer catch-up friend 0`.

## Accounts, cancels and keys

- **An account for your friend** on your node, to read and post as
  themselves: make an invitation code (`account invite`, see
  [accounts](operator.md#accounts-and-invitation-codes)).
- **Cancels travel** with the groups they name. An author's signed cancel
  withdraws the article on both nodes. A moderator's cancel works only on a
  node where that moderator was given the right (`control grant`). Grant it
  on both nodes if you both want it.
- **New keys.** A friend who changes keys posts a signed notice to
  `fn.keys`. Your node needs to allow it:
  `fn operator CONFIG control grant PRINCIPAL-HEX keys fn.keys`. If the
  notice arrived first, decide it again with `keys redecide`
  ([how](operator.md#why-was-an-article-withdrawn)).
- **A group only one of you has.** A signed post to it is refused
  `UNKNOWN-GROUP`. Ask your friend to create the group.

## Known gaps

- A friend's server that cannot stream stops being fed until restart. Set
  its streaming word to `false`.
- One login file per peer serves both directions, so fetching with a login
  needs outbound groups too.
- If two cancels withdraw each other, the answer is a plain `430` rather
  than `430 withdrawn`.
