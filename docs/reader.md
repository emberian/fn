# The friends' reader

A web page where your friends read and write in your node's groups. They
need only a browser, on a computer or a phone. Nothing to install. The page
is part of the node; turning it on is [Read it in your browser](web.md).

## For a friend

1. Open the address you were given.
2. The first time, press **Make your account**, type the invitation code
   you were given, and choose a name and a password. After that, sign in
   with them. They are the same ones a newsreader like tin uses.
3. Pick a group. The newest posts are listed; **older posts** shows more.
   Open a post to read it.
4. **post to this group** at the top of a group, then **Post**.
5. You can remove a post you wrote: open it and press **Remove my post**,
   then **Remove it**. It disappears from this server. Copies other
   servers already have may stay.
6. **Light**, **Dark** or **Automatic** colours are at the bottom of every
   page. **Sign out** is at the top.

After you post, the page says one of three things:

- **Posted!** The server took your post.
- **The server said no**, with its reason. Nothing was published.
- **We couldn't tell whether the server took it.** The answer got lost on
  the way. Look at the group before sending it again.

Groups you are not allowed to see do not appear, and their addresses say
"There's no group by that name here, or you can't read it". The server
decides that, not the page.

## For the person running the node

Invite each friend as usual (`account invite`). They redeem the code once,
on the **Make your account** page, or with `fn redeem`
([how](articles/fn-faq-4.txt); the full reference:
[operator.md](operator.md#accounts-and-invitation-codes)), and then sign
in. The page adds no accounts and no permissions of its own: the node
checks every password and decides every group, post and removal, on the
friend's own connection. Passwords are never written down; a signed-in
session lives in the node's memory until sign-out, `idle_seconds`, or a
restart.

The contract is WEB-003 and WEB-005 in
[the client specification](../specs/human-client.md).
