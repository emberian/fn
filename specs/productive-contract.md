# The productive contract

Status: specified and proved for the served POST (PRF-1001, PRF-1002);
the served read and the peer transfer are stated (section 5) and open. From
GPT-6's second review, `warranty-quality-proof-engineering.md` section 1
("make the warranty reject useless-but-safe implementations") and section
9; row W6 of the pre-6.6.0 list. Books: `books/productive-contract.lisp`
(`fn-pcx-`), `books/productive-observer.lisp`; teeth
`tests/acl2/productive-contract-tests.lisp`; scenario SCN-207.

## 1. Why a safety theorem is not enough

`fn-own-240-follows-consumed-completion` (`books/owner-served-invariants.lisp`,
PRF-060's P2) says that every 240 the served path renders was earned: the
Store's completion was enabled and consumed, the completed row names the
in-flight submission through the arena, and the pair is in the durable
history. An implementation that never answers 240 satisfies it. fn was that
implementation once: the completed row's payload position is a handle into
the entry's arena, and comparing the handle against the staged octets was
false on every completion, so every served POST finished `:fault` and the
client read the uncertain 441 (the comment above
`fn-own-completion-names-submission-p`).

The warranty therefore pairs the safety theorem with a productive one
(section 3) and requires every uncertain answer to name its cause (section
4). Neither pretends disks always answer: both are conditional on the
specified successful primitive completions, and say what the machine does
when those conditions hold.

## 2. Valid, authorized, funded: the contract's terms

The productive theorem's antecedent is stated over the owner's state after
the writer took the submission (`:take`), because that is the point where
the request has been read off the wire, parsed and authorized, and the
Store is about to be driven. Its terms:

- **Valid.** The record `r` the served prepare would stage is a held row
  (`fn-held-p`, `books/held-record.lisp`; the article parser's acceptance,
  `specs/article-parser.md`) with a non-legacy stamp, interned under the
  keyring generation in force, whose coordinates are the next ones
  (`fn-sf-candidatep`: sequence = the history's length, txid = the frontier
  the reservation will hold, generation = txid), and whose extension of the
  history the configured replay accepts (`fn-sf-history-recoverablep`,
  `specs/storage.md`). The consumer projection accepts it
  (`fn-cpe-projection-step`, `specs/consumer-progress.md`) and the topic
  prefix accepts it (`fn-th-prefix-step`, `specs/topic-history.md`). The
  node binds it (`fn-sn-record-bindsp`: its Message-ID is fresh, its groups
  are served, its numbers fit RFC 3977 section 6's bound -- the three
  refusals `fn-psrv-prepare` names, `books/owner-prepare-served.lisp`).
  Together: `fn-pcx-admissiblep s r` plus the topic condition.
- **Authorized.** The submission in flight for connection `id` exists: the
  served read only enqueues a POST the session may post
  (`fn-auth-postingp`, `books/nntp-auth.lisp`, `specs/nntp-audit.md`), so a
  submission in flight IS the authorization decision, carried with its login
  and account (`fn-own-sub-login`, `fn-own-sub-account`). The theorem takes
  `(fn-own-inflight o)` with `(fn-own-sub-id sub) = id` and the connection
  present.
- **Funded.** The budget gate `fn-sbud-admitp` (`books/owner-store-budget.lisp`)
  is transparent below the profile's budget
  (`fn-sbud-prepare-below-budget-is-the-owner-prepare`), and the charge is a
  field of the record the node binds (`fn-record-charge`; `specs/retention.md`).
  An unfunded request is refused by name (`:unaffordable`) before the prepare
  and never reaches the theorem's antecedent. The theorem is stated at the
  Store's admission, where funding has already been decided; the bridge
  from the profile's budget to `fn-pcx-admissiblep` is the named chain
  `fn-psrv-prepare` -> `fn-prc-sbud-prepare` -> `fn-sbud-prepare` ->
  `fn-opc-prepare` -> `fn-own-store-step (:prepare r)` -> `fn-sn-prepare`
  (`fn-psrv-prepare-when-served`, `fn-prc-sbud-prepare-is-pidx-sbud-prepare`,
  `fn-opc-owner-prepare-equals-owner-store-step-under-relation`).
- **The record names the submission.** Read through the arena
  (`fn-row-wire-of`), the record's Message-ID and payload are the
  submission's (`fn-own-sub-msgid`, `fn-own-sub-stored-octets`). This is
  the hypothesis the regression violated, and the mutation witness removes.

These are the specification's predicates, cited from their books. They are
not the host's word: the host reports `:prepared` or a refusal kind
(`fn-pout-prepare-article`), and nothing in the theorem is conditioned on
that report.

## 3. The productive theorem for the served POST (PRF-1001)

The specified successful primitive completions are the nine events of the
served step function `fn-own-step` after `:take`
(`fn-pcx-post-script (list :prepare r)`, `*fn-pcx-post-steps*` = 9):

    (:store (:io :start-frontier nil))     the frontier is staged
    (:store (:io :frontier-file :ok))       the frontier file is durable
    (:store (:io :frontier-replace :ok))    the frontier is replaced
    (:store (:io :frontier-directory :ok))  the directory is durable: reserved
    (:store (:prepare r))                   the prepare ACL2 decided stages r
    (:store (:io :record-file :ok))         the record file is durable
    (:store (:io :record-link :ok))         the record is linked
    (:store (:io :record-directory :ok))    the directory is durable: completing
    (:complete)                             the completion is delivered

**`fn-pcx-post-productive`.** Under section 2's antecedent, after those
nine steps: the host's finish word (`fn-own-finish`) is `:durable`; the
completion is consumed (`fn-own-completion-consumedp`); the ledger and the
Store's successes each gain exactly `r`'s pair; `r` is in the durable
history (`fn-sf-records`); and the outcome the host renders for `id`
(`fn-own-outcome o9 id :durable`) is `fn-served-post-outcome`'s `:durable`
effects -- the 240 line, whose octets section 6 names. The bound is the
step count: nine steps of `fn-own-step`, then the outcome.

Its parts, each a theorem: the Store reaches `:completing` with `r` as the
completion record and the successes untouched
(`fn-pcx-store-run-fields`, `fn-pcx-store-run-completion-enabled`); the
owner's `(:store E)` steps are the Store's with every other field kept
(`fn-pcx-own-run-store`); the finish word is `:durable`
(`fn-pcx-post-finish-word`).

**Teeth.** `tests/acl2/productive-contract-tests.lisp`: the reachable
witness is owner-tests' plain served POST (`*own-taken*`, connection 4,
"Hello, news."), the record its own octets intern at sequence 2, the
arena holding the journal's prior; the complete antecedent and the
complete conclusion are asserted per literal theorem. Hypothesis removal:
a record at the wrong sequence is not admissible and the nine steps do
not reach `:completing`. Mutation: the regression's shape -- the handle
compared against the staged octets -- makes the finish word `:fault`, and
the theorem's conclusion fails for it.

## 4. The uncertainty justification (PRF-1002)

`fn-own-outcome-completion o word` is the one place the served POST and the
peer transfer (`fn-own-transit-outcome`, kind `:want`) decide between
durable, refused, clock-refused and uncertain. **`fn-pcx-uncertain-cause`**
names the cause of an uncertain answer from the owner's state and the
host's word:

| cause | when | what is unresolved |
|---|---|---|
| `:effect-failed-after-publication` | a completion was consumed after the take and the word is not a durable one | an effect after publication failed (the OS error raised after publication, campaign W2 2026-09-24); the record stands, the reply is what is lost |
| `:completion-outstanding` | no completion was consumed after the take and the word names no refusal and is not `:clock-unusable` | the completion is outstanding: a `:durable` claim the ledger does not confirm, or a `:fault` that stopped the sequence before the completion was delivered |

**`fn-pcx-uncertain-has-a-named-cause`.** The outcome is `:uncertain` if
and only if the cause is one of the two. No uncertain answer is an escape
without a cause; no cause is reported for a durable, refused or
clock-refused outcome.

A fence (`:fenced-frontier`, `:fenced-record`) never reaches this
function: the host recovers instead of finishing (`specs/store-node.md`),
so the fenced outcome is the restart's, not an uncertain reply. It is
listed in section 7 as a lifecycle prefix, not as a cause here.

Teeth: a positive witness per cause on the real served trace
(`*osi-completing*` before and after `(:complete)`), the three outcomes
with no cause, the must-fail for an uncertain with no cause, and a mutant
cause function that drops the outstanding-completion case and leaves the
unconfirmed `:durable` claim without one.

## 5. The served read and the peer transfer (open)

The same shape is owed for ARTICLE by number and by Message-ID and for an
accepted IHAVE/TAKETHIS; both are stated here and unproved.

- **Read.** A pinned reader (`fn-own-conn-version`) whose view holds the
  article (by number in a selected group, or by Message-ID) and whose
  session may read it (`fn-auth-access-read`) is answered the 220 line and
  the article's octets by one `fn-own-read-step` -- one step of the served
  step function -- with the view unchanged; and a read of a number the
  view does not hold is answered 423/430 by the same one step, never
  uncertain. The subject is `fn-own-read-step` (host: `fn-owner-read`).
- **Transfer.** A peer submission the transit decision wants
  (`fn-peer-decision :want`), admissible at the Store as in section 2 and
  naming the submission through the arena, reaches 235 (IHAVE) or 239
  (TAKETHIS) by the same nine steps and `fn-own-transit-outcome`, with
  the record in the durable history. The subject is
  `fn-own-transit-outcome`; the store and owner parts of section 3 are
  shared, only the finish word and the rendering differ.

## 6. The external observer (PRF-1003)

`fn-pcx-post-productive` names the outcome by the effects
`fn-served-post-outcome` produces. What the client sees is the octets the
host writes: `fn-served-reply-octets` of those effects
(`books/served.lisp`, the projection the host takes). The observer book
states the connection: for a served connection whose session is the
POST-composed one, the reply octets of the `:durable` outcome are exactly

    240 article received OK\r\n

(`*fn-pcx-240-line*`, RFC 3977 section 6.3.1; the text is fn's), and the
outside-in suite's observation `expect("240")`
(`tests/test_native_outside_in.py`, `test_a06_post_to_a_group`) reads the
first three octets of that line. The test cites this book; the book cites
the test. Nothing else may claim the 240.

## 7. Lifecycle

The prefixes of one warranted lifecycle, which of them this contract
covers and which are open, are in `specs/lifecycle.md`, "The warranted
lifecycle".
