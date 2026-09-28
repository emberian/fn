# The friends' reader

A web page where your friends read and write in your node's groups. They
need only a browser, on a computer or a phone. Nothing to install.

## For a friend

1. Open the address you were given.
2. The first time, press **Make your account**, type the invitation code
   you were given, and choose a name and a password. After that, sign in
   with them. They are the same ones a newsreader like tin uses.
3. Pick a group. New posts are marked **new**. Open a conversation to read
   it; replies sit under the post they answer.
4. **Reply** under any post, or **Write a new post** at the top of a group.
5. You can remove a post you wrote here: open it and press **Remove my
   post**. It disappears from this server. Copies other servers already
   have may stay.
6. **Light**, **Dark** or **Automatic** colours are at the bottom of every
   page. **Sign out** is at the top.

After you post, the page says one of three things:

- **Posted!** It is up. (In a group with a moderator: **Sent!** A
  moderator looks at it first.)
- **Not posted.** The server did not take it and says why. Nothing was
  published. You can edit it and try again.
- **Not sure yet.** The answer got lost on the way. Do not write it again:
  press **Check now**. It sends the very same post, so it can never appear
  twice.

If you moderate a group, its waiting posts are in a group of their own.
Open one and press **Approve and publish**. Turning a post down is not
possible from the web yet. The person running the node can do it.

Groups you are not allowed to see do not appear, and their addresses say
"We couldn't find that group". The server decides that, not this page.

## For the person running the node

The release carries the reader and its service: follow
[Read it in your browser](web.md). What follows is the same reader run by
hand from fn's source.

Run the reader next to your node. It needs Python 3, the node's
certificate, and a certificate for the web side (friends type their
passwords into it):

```sh
python3 tools/fn_reader.py --node news.example.net:1119 --tls-cert node-cert.pem --state /var/lib/fn-reader --listen 0.0.0.0:8443 --https-cert web-cert.pem --https-key web-key.pem --site 'Our news' --mail-domain example.net
```

Without `--https-cert` it serves plain HTTP on `127.0.0.1` only, for a TLS
proxy or an ssh tunnel in front of it. It refuses to serve plain HTTP on
any other address.

Invite each friend as usual (`account invite`). They redeem the code once,
on the reader's **Make your account** page (the reader runs the node's own
`fn redeem`, so start it with `--fn /opt/fn/bin/fn` when it is not the
release's `clients/bin/fn-reader`), or with `fn redeem`
([how](articles/fn-faq-4.txt); the full reference: [operator.md](operator.md#accounts-and-invitation-codes)), and then sign in here. The reader adds no accounts and no
permissions of its own: the node checks every password and decides every
group, post, approval and removal. The reader keeps, per login, only what
the friend has read, their display name and a record of what they sent, in
`--state`. Passwords stay in memory while someone is signed in, and are
never written down.

What the reader does and why is in `tools/fn_reader.py` and the contract
WEB-003 in [the client specification](../specs/human-client.md).
