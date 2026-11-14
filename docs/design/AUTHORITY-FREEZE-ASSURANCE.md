# Temporal authority: freeze boundary and remaining evidence

The declared contract is final-check authority, not admission-time authority.
`AUTHORITY-20261105.md:177–179` invalidates read/wait/ack views on **any**
authority revision, requires checks after park and before carrier handoff, and
places answer linearization at final check/freeze. This note traces source at
`06b1785df`; it does not qualify the later permission or membership repairs.

## Boundary recommendation

Treat successful publication of a complete reply extent by
`fn2-cns-post-reply` as answer freeze. Its current body checks CTL generation,
request identity and waiting phase, encodes the answer, then publishes `tx-off`
and `tx-len`. Put the final coherent-head validation and successful extent
publication in one non-yielding ACL2 transition. The observed event must carry
the principal, request generation, authority revision and full page identity.

CTL `:waiting` subsequently notices that extent and enters `:reply`; `:reply`
issues `fn2-issue-send`, possibly across several sends. A revocation after freeze
must not change the frozen answer, including its remaining chunks. This gives
“carrier handoff” a precise implementation meaning and avoids making the
contract depend on socket throughput. The spec's exemption for already-issued
bytes does not itself identify whether a posted extent counts as issued: adopt
this mapping explicitly before claiming served refinement. If issuance instead
means the first Send, validation must move there; checking each later chunk
would permit incoherent partial responses.

A successful asynchronous authority lookup is not sufficient: the scheduler may
publish a new revision between its final head read and reply publication. Either
compare a synchronously accessible publication revision in the freeze transition,
or use a publication-invalidated certificate that the freeze transition checks.
Do not add an unbounded historical scan or hold disk I/O inside an atomic step.

## Source seams, not newly executed failure claims

* `fn2-cns-authority-allows` in `books/authority.lisp` reads head, current grant,
  grant value, then head again; a changed head restarts that decision. This
  establishes coherence for that lookup, not for the later page.
* CNS `:check` performs admission before selection. `:page` and article I/O can
  yield after that check. Initial consume repair belongs to the authorization
  lane and does not by itself close this interval.
* CNS `:park` wake paths resume at `:read`. They need a fresh authority check,
  including timeout/empty answers and a changed consume grant.
* CNS `answer` clears wait state; `hand` may release a lease and yield before
  calling `fn2-cns-post-reply`. A check before that release still leaves a gap.
* `fn2-cns-post-reply` currently checks CTL identity/liveness but no authority
  head. CTL `:reply` also has no authority check.
* `fn2-cns-lookup-cursor` reads position/version and frontier. That read alone
  does not establish that a bound cursor belongs to the current authority view.

All delivered items must have evidence under the **same final revision**, using
immutable membership in each article's original streams. A page built partly
under two heads must be discarded/rebuilt or refused as a whole. Merely checking
the last item under the current head is insufficient. Membership publication and
initial permission checks are owned by the authorization lane.

Append outcome retry is a separate contract: recorded exact-operation outcomes
precede current grants. Revocation does not erase durable acceptance. This
read/wait freeze oracle deliberately does not judge append retries, cursor
mutation durability, fetch policy, or the membership representation itself.

## Independent controls and their limits

`tests/authority-freeze-oracle.lisp` consumes publication snapshots and freeze/send
events without calling the authority handler, CNS, or consumer model. Its nine
concrete assertions cover accepted-before-revoke and refused-after-revoke twins,
a stale accepted response, unrelated-revision invalidation, mixed-head items,
article-stream intersection, send without freeze, and duplicate request freeze.
Multiple original streams are allowed when any one grants read.

The event request key must include generation. Publication snapshots must be
obtained independently from actual committed state, not reconstructed from the
answer under examination. Item-head evidence is a claim to be checked against
observed selection and immutable membership; this file cannot authenticate its
own inputs. It is a specification control, **not a served-path theorem**.

Validation: `sbcl --script tests/authority-freeze-oracle-sbcl.lsp` from the
repository root evaluated nine assertions under SBCL using only Common
Lisp equivalents of `member-equal`, `assoc-equal`, `len`, and `assert-event`.
No ACL2 admission, guard verification, certification, remote run, or served
schedule has been performed for this package.

## Remaining integration obligation

Once the defensive authorization repair is qualified and a compute slot is
allocated, connect actual publication and reply-freeze observations to this
independent oracle. The required schedule must run real admission/turns, preserve
the device store across rounds, and place a committed head change between item
selection and freeze. Include a whole-antecedent allowed twin, a refused twin,
and a post-freeze change that leaves the frozen reply intact. A phase-injected
CNS row or a substituted handler does not establish the served-path claim.

The eventual keystone needs the actual composed subject (or a named refinement),
positive whole antecedent, hypothesis-removal witnesses, and current closure
certification. Authorization qualification remains a prerequisite for that
integration work.
