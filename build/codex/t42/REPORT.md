# t42 — current DATE observation

## Inventory (written before implementation)

Source: origin/dev 4aa332295c85f03f5a97d7b0ac2228f9b95ab1e9.
Search: all three named accessors in books/ and host/; theorem/hint uses
are not additional executable consumers. Host served entry is
`host/owner-host.lisp:fn-owner-chunk-span-at` -> `fn-mca-read-span`, through
owner reader/catalog spans to `fn-scr-dispatch-core`. The unrestricted arm
runs `fn-scr-auth-delegate` -> `fn-scr-peer-step` -> `fn-scr-post-step` ->
`fn-scr-step` -> `fn-nntp-archive-command-cat`; a read-restricted arm uses
`fn-scar-peer-step-pinned` (cached view or reference view), then
`fn-pix-post-step-pinned` -> `fn-pix-step-pinned` (equated by
`fn-pix-post-step-pinned-is-post-step-pinned` to `fn-nntp-post-step-pinned`). Both reach the shared
DATE/NEWGROUPS/NEWNEWS response functions. The reference owner read runs
`fn-own-read` -> `fn-own-served-conn` -> `fn-served-step`.

| Consumer / carried field | Classification | Reason and reach |
| --- | --- | --- |
| `fn-nntp-date-response` -> env observation | SHOULD-BE-CURRENT | RFC 3977 §7.1 reports current UTC, not connection acceptance. Both served routes above. Fix using the existing injection reading. |
| `fn-nntp-newgroups-response` -> observed year | SHOULD-BE-CURRENT | RFC 3977 §7.3.2 interprets YY using the current year. Creation facts remain historical; only parsing requires now. Same served routes and same clock-selection fix. |
| `fn-nntp-newnews-response`, `fn-nnw-response` -> observed year | SHOULD-BE-CURRENT, open row | Same §7.3.2 year rule via §7.4. NEWNEWS shares its env observation with the legacy horizon below; changing the entire observation would change that policy. Needs separate parser-current and horizon inputs; cursor/no-miss implementation is explicitly outside t42. |
| `fn-nntp-newnews-reader-horizon` | PINNED-CORRECT under existing NNT-008 policy | Conservative fallback for unstamped legacy articles at the reader view; not an expiry or current-time comparison. Current schema has natural acceptance stamps. Changing it belongs with NEWNEWS policy/cursor work. |
| `fn-nntp-envp` | PINNED-CORRECT (shape check) | Checks observation shape, does not choose or report time. |
| `fn-rcompat-held-env` | PINNED-CORRECT (transport) | Preserves whichever observation its caller selected while restricting listing/closed groups; no new clock decision. |
| `fn-post-reader-env` | Mixed envelope | Observation plus pinned creation facts, posting bit, descriptions/MOTD/Xref listing and closed groups. Only the observation may be current; configuration/auth decisions stay pinned for coherent permission and response policy. Called by both post dispatchers and the catalog post dispatcher. |
| `fn-own-reader-context`, `fn-ocar-own-reader-context`, `fn-own-served-conn`, `fn-own-read-step-full` | PINNED-CORRECT (transport) | Carry accepted configuration and clock into served connection; separately carry `fn-own-clock` as injection. Reached by configured owner open/read and host chunk entry. The defect is a downstream consumer choosing the wrong slot. |
| `fn-served-dispatch-core`, `fn-scar-dispatch-core`, `fn-scr-dispatch-core` | PINNED-CORRECT (transport), downstream DATE fixed | Pass both observations to auth/peer/post dispatch, then preserve them in the returned connection. Reference/carried/catalog versions of the host read. |
| `fn-served-conn-with-wire`, `fn-served-pin-verdicts`, `fn-served-pin-group-index`, `fn-served-repin`, `fn-scr-repin`, `fn-scl-with-live` | PINNED-CORRECT (transport) | Copy the accept-time slot across wire/pin/live-view changes. A catalog refresh is not a new clock observation. Host read/open chain. |
| `fn-own-finish-read`, `fn-scar-finish-read`, `fn-own-advance-result`, `fn-acar-own-advance-result` | PINNED-CORRECT (transport) | Write back the session/view while preserving connection observation. Host read completion/advance. |
| `fn-own-outcome`, `fn-own-transit-outcome`, `fn-apc-own-outcome`, `fn-acar-own-outcome`, `fn-oop-outcome`, `fn-oop-transit-outcome`, `fn-oct-outcome`, `fn-oct-transit` | PINNED-CORRECT (transport) | Preserve connection metadata after durable completion; completion outcome does not render a time. Host post/peer completion. |
| `fn-octl-reply`, `fn-pb-served-reply` | PINNED-CORRECT (transport) | Assemble served connection for control/duplicate reply; no wall-time decision. Host control/submission path. |
| `fn-orcp-repin-conn` | PINNED-CORRECT (transport) | Rebuilds retained view metadata while preserving observation. Reclaim is out of scope; no current-time consumer here. |
| Injection-Date, generated Date/Message-ID | SHOULD-BE-CURRENT, already correct | Post/article arm uses `injection`, sourced from owner current clock per read; `fn-inj-decide`/group-status gate do not substitute pinned reader observation. RFC 5537 §3.4. |
| Expiry / clock contradiction / creation timestamps | No pinned reader consumer | Retention has no automatic expiry (D03). Owner clock observation/declare-group use owner current clock; historical creation provenance stays historical. `fn-own-observe` may drop the current clock; DATE must then refuse despite a usable pinned reading. |

## Acceptance (verbatim)

- each new/changed event admitted in a proof_repl session (show the summary lines);
- python3 tools/ledger.py --check and python3 tools/current_view.py --check if they run locally in under 5 minutes
  (else say so);
- git diff --stat origin/dev...HEAD; the list of books changed (the liaison certifies --affected-by each).

## Work and validation

Implemented and source-admitted below. Native execution and certification are assigned to the liaison. No push, deployment or publication was performed.

Inventory correction during composition checking: `fn-pix-post-step-pinned`
(books/peer-offer-indexed.lisp) independently constructs the reader env on
the restricted carried route. Its existing equality theorem caught the
missed current-clock threading. It is fixed in exactly the same shape;
the reference, pinned reference, carried restricted and catalog post arms
now all call the shared selector.


## Implementation and theorem scope

- `fn-post-command-env` selects the existing per-read `injection` observation
  only for DATE and NEWGROUPS. It uses the bounded reader tokenizer; all
  other environment fields still come from the pinned configuration. There
  is no fallback from a missing current clock to a previously good clock.
- All four environment-construction sites now use it: `fn-nntp-post-step`,
  `fn-nntp-post-step-pinned`, `fn-pix-post-step-pinned` and `fn-scr-post-step`.
  Existing exact carried/reference and expanded catalog/reference theorems
  keep their names and statements and admitted again.
- `fn-post-date-result-independent-of-pinned-observation` and
  `fn-scr-date-result-independent-of-pinned-observation` equate the complete
  DATE results for arbitrary sessions, archives, configs and pinned
  observations, with the same current reading. They have no hypotheses.
- `fn-served-step-date-uses-current-reading` is over `fn-served-step`, called
  directly by `host/reader-host.lisp:fn-reader-chunk`. It equates the complete
  DATE effects of a reachable fresh empty reader with the current clock's
  renderer; arbitrary pinned/current readings include nil, malformed and
  no-wall. `fn-served-step-date-ignores-pinned-reading` instantiates that law
  twice. The witnesses additionally change the current reading by one second
  and assert the reply changes; changing a subsecond component alone is not
  claimed to change a seconds-resolution DATE reply.
- Native host subject: `fn-mca-read-span`, called in
  `host/owner-host.lisp:fn-owner-chunk-span-evaluate` from
  `fn-owner-chunk-span-at`. The owner supplies `fn-own-clock` through
  `fn-own-served-conn`. The catalog post correspondence and
  `fn-pix-post-step-pinned-is-post-step-pinned` connect both native routes
  to the changed decision. This lane does not claim native image qualification.
- All prior exported theorem statements are preserved. In particular
  `fn-auth-fold-post-awaiting-implies-reader-offer` still mentions the old
  pinned env, because its antecedent implies POST, whose clock selection
  is unchanged. A new local lemma and reordered proof establish precisely
  that old statement. Grepping planning/proofs.json found no literal PRF
  citation of this theorem. PRF-033 and NNT-008 are the existing DATE-related
  registry rows updated; no new ID was claimed or written.

### Remaining observation rows

1. NEWNEWS two-digit-year parsing (both `fn-nntp-newnews-response` and
   `fn-nnw-response`) remains SHOULD-BE-CURRENT. Separating it from the
   pinned legacy horizon is necessary; changing the whole env would alter
   NNT-008. The task explicitly excludes cursor/no-miss work. Spec and
   NNT-008 now name this open correction rather than silently implying it
   is current. No claim of a DATE-to-NEWNEWS no-miss theorem is made.
2. `host/reader-host.lisp`'s legacy standalone reader is a separate input
   adapter: `fn-reader-reset` supplies the same clock to both slots, and
   `fn-reader-observe-clock` updates only its global for a later reset.
   Unlike the native owner it does not rebuild a current reading per chunk.
   Its clock-refresh integration remains open; the served-step theorem is
   a theorem about supplied inputs, not proof that this adapter supplies a
   fresh wall observation. Native owner routes are the fixed task routes.

## REPL admission output

Every ACL2 command used `tools/proof_repl.py`, with `start --host hbox`
(no auto/laptop/persvati, certification, farm, make or direct ssh).
These are source admissions, not certificates. The liaison owns affected
root certification of the committed bytes.

```
t42-date: LOADED books/nntp-post: 56 forms (up to fn-nntp-post-step)
#57 defun fn-post-command-env: ACL2 time 0.00 s (guards admitted)
#59 defun fn-nntp-post-step: ACL2 time 0.01 s
#60-#104: 45 forms, 0 refused; ACL2 time 1.11 s; prover steps 377,665
#79 verify-guards fn-nntp-post-step: ACL2 time 0.00 s
#102 defun fn-nntp-post-step-pinned: ACL2 time 0.00 s
#103 verify-guards fn-nntp-post-step-pinned: ACL2 time 0.00 s
#104 fn-post-step-pinned-preserves-consistent-session: 0.03 s; 8,259 steps

t42-served: LOADED books/served: 283 forms
from source: nntp-post, nntp-pinned-effects, peer-inbound, group-access, nntp-auth
loading cost ACL2 time 36.40 s; prover steps 7,578,314
fn-post-date-result-independent-of-pinned-observation: 0.03 s; 306 steps
fn-served-step-date-uses-current-reading: 0.54 s; 564,135 steps
fn-served-step-date-ignores-pinned-reading: 0.00 s; 0 steps
served-date-current-tests #3-#11: 9 forms, 0 refused; all 5 assert-event :PASSED

t42-catalog: LOADED books/served-catalog-chain through fn-scr-post-step-is-post-step-pinned
38 loaded forms; source dependency closure through group-access-cache admitted
loading cost ACL2 time 93.82 s; prover steps 16,646,912
fn-scr-post-step-is-post-step-pinned: admitted (unchanged statement)
verify-guards fn-scr-post-step: 0.00 s; 107 steps
fn-scr-date-result-independent-of-pinned-observation: 0.10 s; 9,934 steps
served-date-catalog-tests #3 assert-event: :PASSED

t42-fold: LOADED books/nntp-auth-fold: 39 forms
through fn-auth-fold-post-awaiting-implies-reader-offer
loading cost ACL2 time 57.51 s; prover steps 8,774,037
```

Intermediate refusals were investigated, not waived: one send-range skipped
five prerequisite forms, then resumed from #60 and passed; the first catalog
load refuted the omitted carried `fn-pix-post-step-pinned` change, repaired
above; two served proof attempts hit 60-second rewrite limits, then a
minimal theory with executable counterparts and explicit record accessors
proved the same statement in 0.54 seconds. An unknown hint rune was removed.
No theorem was weakened because proof search failed.

## Local checks and liaison commands

- Python AST parsing passed for all three edited native test modules; no
  native test was executed. Lisp forms parsed; `git diff --check` passed.
- `python3 tools/ledger.py --check` exceeded five minutes (stopped at
  approximately 5m45s), with no verdict. Per TASK this check is deferred to
  the liaison; no ledger waiver or baseline change.
- Initial `python3 tools/current_view.py --check` reported stale current.md.
  `python3 tools/current_view.py --write` regenerated it; the M5 cache-only
  wording is generated from existing evidence, not a new reclaim claim.
  Final check output is recorded below when complete.

Native regression commands (liaison on hbox, newly built matching images):

```sh
FN_NATIVE_DEVELOPER_HOST=/absolute/path/to/fn-host-developer python3 -m unittest -v tests.test_native_owner.NativeOwnerTests.test_date_on_connection_older_than_a_minute_is_current
FN_NATIVE_HOST=/absolute/path/to/fn-host FN_NATIVE_DEVELOPER_HOST=/absolute/path/to/fn-host-developer python3 -m unittest -v tests.test_native_group_access
```

The owner test holds one socket >61 seconds, keeps it active to avoid idle
policy, and checks its DATE is within three seconds of the before/after UTC
clock. The access scenario does the same simultaneously for unrestricted
Alice and read-restricted Bob, on both production and developer images.
The existing group-policy source assertion was updated for the new shared
selector; no test was deleted.

Liaison: certify the changed books with `--affected-by` each (list below),
plus both new ACL2 witness books, and their affected includers. Run ledger
and current-view checks on the integrated bytes; archive/index the certify
manifest by the usual project tooling. No certificate, native success or
qualified/deployed coordinate is asserted by this report.

### Final theorem and additional checks

The stronger host-called theorem
`fn-served-step-date-any-session-ignores-pinned-reading` also admitted. It
keeps the session/archive/config/current clock/indexes arbitrary and
constructs only the clean wire command boundary and the two different
pinned observations. Its conclusion equates DATE effects. Thus the
noninterference result is not confined to the fresh empty reader used to
witness the exact timestamp. The exported DATE noninterference
keystones have **no hypotheses**: there are no omitted-hypothesis witnesses
to manufacture. The exact-clock theorem and arbitrary-session theorem
are listed under existing PRF-033; its status stays uncertified-at-current-digest.

```
fn-date-post-direct-canonical-pinned: 0.04 s; 394 steps
fn-date-auth-canonical-pinned: 0.03 s; 874 steps
fn-served-step-date-any-session-ignores-pinned-reading: 1.01 s; 571,473 steps
```

The initial arbitrary-session attempt exposed an unindexed restricted arm
(`fn-peer-step`, already fixed through `fn-nntp-post-step`) and a reflexive
canonicalization rewrite loop. Factoring the proof at the auth result and
restricting that proof-only rewrite syntactically resolved both; the
statement did not change. A broad 443-subgoal expansion took 51.10 s and
failed; the factored proof takes 1.01 s. This is proof-discovery output,
not a production cost measurement.

Final `python3 tools/current_view.py --check` was bounded by a Python
subprocess timeout of 300 seconds and did not finish: **no final verdict**.
`--write` completed before that attempt. `current-view.json` requires no
new coordinate: no image, certification manifest or deployment changed.
The liaison must run both registry checks at integration.

No new IDs, waivers, baseline bumps, deleted tests, cache deletions, native
executions, certificate runs, pushes or edits outside this worktree.
Remote hbox trees were created only by the sanctioned proof_repl wrapper.

```
fn-post-command-env-ordinary-unfolds: admitted; 0.03 s; 165 steps
served-date-current-tests #12-#13: both assert-event :PASSED
Changed/deleted prior exported theorem statements: []
```

The last statement comparison parsed every prior/current top-level defthm
in changed books and compared its literal proposition; no prior proposition
changed or disappeared. A shared `-unfolds` lemma preserves proof clients
that instantiate the old env for commands other than DATE/NEWGROUPS; it is
not cited as a keystone.

All started REPL sessions were stopped: t42-date, t42-served, t42-catalog
(including its first failed startup), and t42-fold.

## Changed books for liaison certification

- books/nntp-post.lisp
- books/nntp-pinned-effects.lisp
- books/peer-offer-indexed.lisp
- books/served-catalog-chain.lisp
- books/nntp-auth-fold.lisp
- books/served.lisp (clock-field documentation only)
- books/served-date-current.lisp
- tests/acl2/served-date-current-tests.lisp
- tests/acl2/served-date-catalog-tests.lisp

Apply `--affected-by` to each changed books/ root, and include both new
witness roots explicitly. The liaison, not this lane, runs certification.

## Diff stat

`git diff --stat origin/dev...HEAD` (verified against the final commit):

```text
 books/nntp-auth-fold.lisp                 |  40 ++++-
 books/nntp-pinned-effects.lisp            |   2 +-
 books/nntp-post.lisp                      |  68 ++++++--
 books/peer-offer-indexed.lisp             |   2 +-
 books/served-catalog-chain.lisp           |  17 +-
 books/served-date-current.lisp            | 187 ++++++++++++++++++++
 books/served.lisp                         |   5 +-
 build/codex/t42/REPORT.md                 | 276 ++++++++++++++++++++++++++++++
 planning/current.md                       |   6 +-
 planning/proofs.json                      |  15 +-
 planning/requirements.json                |   2 +-
 specs/nntp.md                             |  15 +-
 tests/acl2/served-date-catalog-tests.lisp |  28 +++
 tests/acl2/served-date-current-tests.lisp | 108 ++++++++++++
 tests/test_native_group_access.py         |  23 +++
 tests/test_native_group_policy.py         |   2 +-
 tests/test_native_owner.py                |  24 +++
 17 files changed, 786 insertions(+), 34 deletions(-)
```
