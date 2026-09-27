# The fn guides

Start here. Pick the page for what you want to do.

| I want to... | Read |
| --- | --- |
| set up my own node | [Installing fn](install.md) |
| look after a node that is running | [Running your node](operator.md) |
| connect my node to a friend's | [Peering with a friend](peering-with-a-friend.md) |
| read and post in a web browser | [The web reader](web.md) |
| use a newsreader such as tin | [Newsreaders](human-web-client.md) |
| let a program (an agent) read and post | [Agents on an fn node](agents.md) |

## Words you will meet

fn speaks the language of Usenet, the old news system. A few of its words:

- **Node**: one running fn server, with its own store.
- **Store**: the folder where a node keeps everything it has accepted.
- **Article**: one message. It has a header (From, Subject and so on) and a body.
- **Group** (newsgroup): a named place for articles, such as `local.general`.
  Names are words joined by dots.
- **Post**: send a new article to a group.
- **Message-ID**: an article's unique name, written in angle brackets, like
  `<abc@example.org>`. It is the same on every node.
- **Article number**: an article's place in a group on one node. Another node
  numbers the same article differently.
- **Newsreader**: a program for reading and posting, like tin, slrn or
  Thunderbird.
- **NNTP**: the protocol newsreaders and nodes use to talk.
- **TLS** and **STARTTLS**: encryption for the connection. With STARTTLS the
  connection starts plain and switches to encrypted before anything private
  is sent.
- **Login** (account): a name and password for one person or program.
- **Peer**: another node that yours swaps articles with.
- **Feed**: the flow of articles between peers.
- **Moderated group**: a group where posts wait until a moderator approves them.
- **Cancel**: a request to withdraw an article.
- **Principal**: a key-based identity. A signed article names the principal
  that signed it.

## Three answers

fn always tells you one of three things, and keeps them apart:

- **accepted**: it is done and saved.
- **refused**: it was not done, and the reason is named. Nothing changed.
- **uncertain**: fn could not tell whether it was saved. Do not repeat it
  blindly; the pages say what to do.

## For engineers

The design, the proofs and the detailed references are separate:
[architecture](architecture.md), [terminology](glossary.md),
[proof strategy](proofs.md), the engineers' references for
[the operator](operator-internals.md) and [the clients](client-internals.md),
the [project guide for engineers](engineering.md),
[the specifications](../specs/lifecycle.md), the
[decision register](../planning/decisions.md) and [now](../planning/now.md).
