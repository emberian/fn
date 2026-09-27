# Proofs, in plain words

fn makes promises, and some of them are proved. This page says what that
means, what it does not mean, and how to tell a proved promise from a hoped-for
one. The engineers' version is [the proof strategy](../../docs/proofs.md).

## The rules are a program you can reason about

Every decision a node makes is written in ACL2: whether to accept an article,
what to reply, what number the article gets in a group, what to keep and when
to let it go. ACL2 is a programming language and a theorem prover at once. A
function written in it can run, and a theorem about that function is checked
by the prover, step by step, before it is accepted.

The rest of the server, the part that opens sockets and writes files, is thin.
It reads bytes, asks ACL2 what to do, and does it. It never makes a decision of
its own that ACL2 also makes.

## Proofs about the code that runs

A common way to prove things about software is to prove them about a model, a
simplified sketch, and then write the real program separately and hope the two
agree. fn does not count that. A theorem counts only when it is about the
function the running server actually calls, or when another theorem shows the
two are the same.

Some of the promises this gives, stated loosely:

- A post is confirmed only after it is saved. If the power goes out after fn
  said yes, the post is still there.
- When fn says no, nothing changed.
- When fn cannot tell whether something was saved, it says so ("uncertain")
  instead of guessing.
- A change to a node's settings takes effect all at once: no reader sees half
  of it.
- A problem on one connection costs that connection, not the others.

Each of these has an exact statement, with its conditions, in the books; the
loose wording here is a summary, not the promise.

## What a proof cannot promise

A proof is about a model of the world, and the world can disagree. A proof
cannot promise that your disk keeps its word when it says a write is done,
that a hash function is unbroken, or that a peer tells the truth. fn writes
those down as named assumptions, and the theorems that rely on one mention it.

The real thing is tested separately. Power is cut on real machines while
posts are arriving, and the tests count what survives; the front page quotes
the current figure with the setup it was measured on.

## Proved, built, tested, running

A claim about fn names which of four things it is about, and they are kept
apart because none implies another:

- **Implemented**: the server's code calls the function the theorem is about.
- **Proved**: the prover checked the theorem against exactly the current code.
  Editing that code makes the theorem unproved again until it is re-checked.
- **Qualified**: a built server containing exactly that code passed its tests.
- **Deployed**: that built server is what a live node runs.

The project keeps a generated table of these for each promise,
[the current view](../../planning/current.md), and a generated
[ledger](../../planning/ledger.md) of every theorem. Nobody types those
numbers by hand, so they cannot quietly drift.

## Not everything is proved

fn is an experiment. Some promises are proved, some are only tested, and some
are still open work. The open ones are listed, not hidden: see
[the proof registry](../../planning/proofs.json) and
[the proof strategy](../../docs/proofs.md). If you work in formal methods and
want to look closer, [the architecture](../../docs/architecture.md) and
[the decisions](../../planning/decisions.md) are the place to start, and
`books/` holds the definitions and theorems themselves.
