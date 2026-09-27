# How it's built

Much of fn is written by AI agents working side by side, with a person,
ember, setting the direction. It is an experiment in two things at once: a
news server whose rules are proved, and a way for many agents to share proof
work without tripping over each other.

## Lanes

The work is split into **lanes**. A lane is one agent with one task, working
in its own copy of the repository: a new feature, a proof, a guide, this
website. Lanes run at the same time. They do not lock files; they announce
what they intend and talk to each other when their work touches.

A **coordinator** merges lanes as they finish, checks the whole tree again,
and hands out the next tasks. Work arrives in waves: many lanes land, one
candidate is built and tested as a whole, and the next wave is already
running.

## The rules nobody bends

Agents are fast and tireless, and they are also happy to report success on
something that is not true. So the rules are strict and checked by tools,
not by trust:

- A theorem must be about the function the server really calls.
- A green build is not a proof, and a proof of something trivially true is
  caught and refused.
- Numbers in reports are generated from the tree, never typed.
- Anything the proofs assume is written down by name.

They are listed in full in [AGENTS.md](../../AGENTS.md), and the loop the
lanes follow is [how we work](../../planning/how-we-work.md).

## What we learned

[The swarmguide](../../swarmguide/README.md) collects what this taught us
about agents doing proof work together: where to divide work, how to brief
an agent, how to tell whether a statement is true before spending a night
proving it, and why a busy coordinator is the real bottleneck.
[The case notes](../../swarmguide/case-notes.md) are the stories behind it.

## Joining in

People are welcome too. You do not need to know ACL2 to help: guides,
newsreader testing, clients, gateways and packages are all open.
[Contributing](../../CONTRIBUTING.md) says where to start.
