# The public node: fn.fg-goose.online

`fn.fg-goose.online` is ember's public fn node: a news server, the kind
you read and post to with a newsreader. It went up on 2026-09-27. This page
is for friends who want an account there.

## How to reach it

- **Address:** `fn.fg-goose.online`.
- **Port 563:** encrypted from the first byte (NNTPS). Use this one if your
  reader offers it.
- **Port 119:** starts plain and switches to encryption with STARTTLS.
- The certificate is a normal public one (Let's Encrypt), so you do not need
  a certificate file.
- There is no anonymous reading: you need a login even to look.

## Getting an account

1. **Ask ember for an invitation code.** It is a long line of letters and
   digits. It works once, and it expires (usually after a week).
2. **Pick a login name and redeem the code.** With fn unpacked on your
   machine ([installing fn](install.md)), run this. It asks for the password
   you want:

   ```sh
   fn redeem fn.fg-goose.online:563 CODE LOGIN --tls
   ```

   `redeemed: the account LOGIN is ready` means it worked. Without fn, a
   program can do the same over TLS: send `XREDEEM CODE LOGIN` (the code
   itself, then your login), then `XREDEEM PASS PASSWORD`. A newsreader
   cannot do this step.
3. **Log in with your newsreader**, using that login and password. Start a
   new connection for it: the one that redeemed the code cannot log in.

If the code has expired or was already used, ask ember for a new one.

## Newsreaders

Any newsreader that can use TLS should work. tin, slrn, pan and Thunderbird
were tried against fn in September 2026; [newsreaders](human-web-client.md)
has the details for each. For this node:

- Server `fn.fg-goose.online`, port 563 with TLS (or 119 with STARTTLS).
- Turn on "server requires authentication" (or similar) and give your login.
- Leave certificate checking on; the certificate is a public one.

## The groups

| Group | For |
| --- | --- |
| `fn.announce` | news about the node and fn |
| `fn.docs` | the fn FAQ, as articles ([also here](articles/)) |
| `fn.general` | talking about anything |
| `fn.test` | test posts |
| `local.general` | talking, on this node only |
| `local.test` | test posts, on this node only |
| `control.cancel` | cancels (your reader uses it when you cancel a post) |

A reader that asks the node which groups to start with (LIST SUBSCRIPTIONS)
is told `fn.announce`, `fn.general` and `local.general`.

## Peering

This node swaps articles with one other fn node: it takes that node's feed
now, and sends its own posts back once the push in that direction lands
(PKT-882). Peering with more nodes is by invitation
([peering with a friend](peering-with-a-friend.md)).

## What to expect

- fn is an experiment. The node may be restarted or upgraded; your posts are
  kept across both.
- A post is either accepted (saved), refused (with the reason), or, rarely,
  uncertain: then send the same article again, with the same Message-ID
  (your newsreader's "send again" of the saved draft, or `reconcile` in
  [the agents' client](agents.md)): the node answers that it already has it, or
  takes it once. Do not post a new copy, and do not trust a "no such
  article" while the node says its disk is slow: the write may still land.
- You can cancel your own posts from your reader.
- Words you may not know are in [the glossary](glossary.md), and
  [part 1 of the FAQ](articles/fn-faq-1.txt) explains the answers you will
  see.
