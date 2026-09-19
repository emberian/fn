# HANDOFF w3-fragment-container

Branch `w3/fragment-container` from `dev` (parent `9321344`). HEAD is the
commit that carries this file together with the work below. Worktree
`/Users/ember/dev/fn/build/lanes/w3-fragment-container`. The local baseline
`make certify` was terminated by the coordinator at load 98 (nineteen ACL2
processes on the laptop) and rerun on a remote box at the same absolute path;
see "Baseline" below. No shared book was edited: `transfer*.lisp`,
`frame.lisp`, `node.lisp`, `identity.lisp`, `records.lisp` and every other
book are byte-identical to `dev`.

## Per book

| Book | Status | Evidence dir (`build/acl2/`) | Theorems |
| --- | --- | --- | --- |
| `books/transfer-journal.lisp` | **certified** | `certify-20260919T215540Z-3210` | 26 |
| `books/transfer-journal-invariants.lisp` | **certified** | `certify-20260919T221000Z-26241` | |
| `tests/acl2/transfer-journal-tests.lisp` | **certified** | `certify-20260919T221011Z-26555` | 0 (44 assert-event witnesses) |
| `books/container.lisp` | **certified** | `certify-20260919T222336Z-62495` | 2 |
| `books/container-invariants.lisp` | **certified** | `certify-20260919T222528Z-64811` | 12 |
| `tests/acl2/container-tests.lisp` | **certified** | `certify-20260919T222528Z-64811` | 0 (62 assert-event witnesses) |

Makefile roots added after `tests/acl2/transfer-tests`, in that order.
`docs/prefixes.md` rows `fn-tj-` and `fn-ct-`. `python3 tools/ledger.py
--write` run; `make check` green. No `skip-proofs`, `defaxiom` or `defttag`.

## Baseline

`make certs-install` on the realigned tree installed nothing usable: it
reported `installed 0, kept identical local 24, no cached pair 164`, and the
certificates already in the worktree are **not relocatable** -- certifying
`books/transfer-journal` against them failed with "its certificate requires
the book .../w3-fragment-container/books/acceptance.lisp, but ... the book
.../dep-core/books/acceptance.lisp ... has been included". The cache is keyed
by content but the certificates record the absolute path of the worktree that
produced them. **This is a tooling defect worth a board entry**: a lane that
trusts `certs-install` gets a green-looking worktree in which nothing can
certify.

The baseline this lane therefore built itself: the twenty books of the
include closure, certified from source in this worktree, one ACL2 process at
a time, all passing --
`build/acl2/certify-20260919T201615Z-65567`: acceptance-alloc, acceptance,
acceptance-invariants, retention, node, node-invariants, cbor,
cbor-invariants, wildmat, records, identity, frame-octets, frame-fields,
frame-journal, frame, frame-invariants, transfer, transfer-reservation,
transfer-union, transfer-invariants. ACL2 8.7, SBCL 2.6.8, this laptop,
co-tenant with three other lanes.

## Why the lane had never certified (measured, not guessed)

1. **No named measure on the folds.** `fn-tj-journal`, `fn-tj-run`,
   `fn-tj-replay-records`, `fn-tj-replay-frames`, `fn-tj-replay-frames-with`
   and `fn-ct-publish-list` all recur on a list *and* thread a kernel state.
   ACL2 guesses a measure over the first formal, so refuting the guess opens
   the whole transfer kernel (`fn-transfer-complete-fromp`,
   `fn-transfer-replace-entry-with-chunks`) inside the termination proof:
   measured at **1800 s timeout, still at Subgoal 51.2.5**. With
   `:measure (acl2-count <list>)` named, `books/transfer-journal` certifies in
   seconds. The same guess would have opened the acceptance and retention
   kernels under `fn-ct-publish-list`.
2. **The node guard.** Core's realignment put `(fn-node-statep s)` on
   `fn-node-prepare`/`fn-node-complete`, so `fn-ct-publish-article` cannot
   verify guards without carrying it, and `fn-ct-publish-list` needs
   `fn-ct-publish-article-preserves-node-statep` to carry it across the
   recursion rather than re-checking the recognizer.
3. **The frame vocabulary is not free.** Enabling `fn-frame-octet-vocabulary`
   book-wide (the `len`-backchaining cascade codecs measured at 108 s on one
   `append` goal) is what made the admission explode; it is now enabled in
   exactly one event, the guard proof of `fn-tj-decode`.

4. **The guard of `fn-ct-deps-resolvep` never needed the profile.** The two
   checkpoints of the failing conjecture were `(integerp fuel)` and
   `(<= 0 fuel)`: the guard of `zp` on `fuel`, which the guard did not carry.
   `(natp fuel)` in the guards of `fn-ct-deps-resolvep`, `fn-ct-dep-resolvep`
   and `fn-ct-article-validp` closes it in 0.03 s; every caller passes
   `(len articles)`. `fn-ct-profilep-forward-fields` and the opaque readers
   stay as they were.

## Container half closed (2026-09-19, second owner)

The branch merged `dev` at `fc51e46` (ledger regenerated on the conflict).
The merge changed `books/identity.lisp` and `books/records.lisp` under the
container, so their certificates failed the content hash; both were deleted
and certified in place (`certify-20260919T222129Z-61060`, with
`books/container`, which certified again at `certify-20260919T222336Z-62495`
after comment-only edits). The merge also changed
`books/transfer-invariants.lisp`, so `books/transfer-journal.cert` and its two
dependents are stale by hash and were not recertified here (not roots of this
task; their evidence rows above predate the merge).

Three forms of `books/container-invariants.lisp` had never reached ACL2 (the
book failed before them):

- `fn-ct-identity-okp-is-spec-okp`: `dev` moved `fn-id-subject-of-payload`
  to hash the subject preimage (`fn-id-subject-preimage` of the octets,
  length-prefixed), so the hypothesis `digest = (fn-frame-digest octets)`
  became false to the definition. The hypothesis now names the preimage, the
  same shape as `fn-id-subject-is-subject-of-payload` in
  `books/identity-invariants.lisp`. This is the one statement that changed;
  it tracks the identity spec, and `specs/container.md` says so.
- `fn-ct-accepted-is-complete-of-prepare`: `:rule-classes nil`. Its conjunct
  `(equal completion :durable)` is not a legal rewrite rule and its trigger
  carries six free variables; the book already consumes it by `:use`.
- `fn-ct-provider-self-dependency-never-resolves` (local): ACL2 refuses
  `:induct` and `:use` on one subgoal; the membership instance moved to
  `"Subgoal *1/2"` and `"Subgoal *1/1"`.

## Subject and host line

Packet A composes the two public kernel transitions the transfer tests
drive, `fn-transfer-reserve` and `fn-transfer-add-chunk`
(`books/transfer.lisp:489`, `:626`); no host file calls them yet
(`specs/transfer-public-bound.md` records the same for
`fn-transfer-missing-ranges`). The journal therefore governs no served path
until the proposed `tools/run_transfer.py` exists; the handoff says so and the
specs say so. Packet B composes `fn-node-prepare` (`books/node.lisp:227`) and
`fn-node-complete` (`:257`), which `host/store-host.lisp` drives through the
store adapter; the container calls them with the transaction id read from the
node (`fn-state-next-txid`) and the host's completion observation, exactly as
the adapter does.

## Keystones, verbatim (packet A, `books/transfer-journal-invariants.lisp`)

```
(defthm fn-tj-replay-of-journal-is-run
  (implies (natp index)
           (equal (fn-tj-replay-records st (fn-tj-journal st inputs) index)
                  (list :ok (fn-tj-run st inputs) (+ (len inputs) index)))))
```
Hypotheses: `(natp index)` only. `st` and `inputs` are arbitrary: a
malformed input is journaled with the kernel's refusal and replays to it. The
original draft carried `(fn-tj-inputsp inputs)`; it was vacuous once the
record shape was made explicit, so it was removed rather than left as a
hypothesis without teeth.

```
(defthm fn-tj-run-preserves-statep
  (implies (fn-transfer-statep st)
           (fn-transfer-statep (fn-tj-run st inputs))))

(defthm fn-tj-replay-sealed-journal-is-run
  (implies (and (natp index)
                (fn-tj-records-okp (fn-tj-journal st inputs)))
           (equal (fn-tj-replay-frames
                   st (fn-tj-seal-journal (fn-tj-journal st inputs)) index)
                  (list :ok (fn-tj-run st inputs) (+ (len inputs) index)))))

(defthm fn-tj-corrupt-frame-ends-replay-at-typed-fault
  (implies (and (natp index)
                (fn-tj-records-okp (fn-tj-journal st inputs))
                (not (fn-frame-result-okp (fn-tj-open bad))))
           (equal (fn-tj-replay-frames
                   st
                   (append (fn-tj-seal-journal (fn-tj-journal st inputs))
                           (cons bad rest))
                   index)
                  (list :fault
                        (list :corrupt (fn-frame-item 1 (fn-tj-open bad)))
                        (fn-tj-run st inputs)
                        (+ (len inputs) index)))))

(defthm fn-tj-refused-record-replays-to-same-state
  (implies (and (not (equal (fn-tj-outcome r) :reserved))
                (not (equal (fn-tj-outcome r) :stored)))
           (equal (fn-frame-item 1 (fn-tj-apply st r)) st)))

(defthm fn-tj-decode-of-encode
  (implies (and (fn-tj-record-okp r) (fn-frame-digestp digest))
           (equal (fn-tj-decode (fn-tj-encode r digest) digest)
                  (fn-frame-ok *fn-tj-magic* *fn-tj-version* (fn-tj-kind r) (cdr r)))))

(defthm fn-tj-open-of-seal
  (implies (fn-tj-record-okp r)
           (equal (fn-tj-open (fn-tj-seal r))
                  (fn-frame-ok *fn-tj-magic* *fn-tj-version* (fn-tj-kind r) (cdr r)))))

(defthm fn-tj-replay-frames-with-is-replay-frames
  (implies (equal digests (fn-tj-digests-of frames))
           (equal (fn-tj-replay-frames-with st frames digests index)
                  (fn-tj-replay-frames st frames index))))
```
Hypothesis stacks: A-CRYPTO (`fn-frame-digest`, shape only) under every
`fn-tj-open`/`fn-tj-seal` statement; `fn-transfer-reserve-preserves-statep`
and `fn-transfer-add-chunk-preserves-statep` under `fn-tj-run-preserves-statep`;
`fn-transfer-reserve-refusal-no-overwrite-general`,
`fn-transfer-reserve-refusal-no-overwrite` and
`fn-transfer-add-chunk-refusal-or-conflict-no-overwrite` under the refusal
keystone; `fn-frame-decode-of-encode`, `fn-frame-protected-prefix-of-encode`
and `fn-frame-fields-parse-of-octets` under the frame pair. Corollaries named
as such: `fn-tj-restart-reproduces-missing-ranges` (of the first keystone),
`fn-tj-candidate-is-unverified-by-definition`.

Covered scope: the logical journal and its frames; durability of the write
(`fsync`), the host's SHA-256, and splitting a file into frames are host work
(A-DURABILITY, A-CRYPTO, A-HOST). Reorder and byte-identical overlap are
kernel properties the witness exercises
(`fn-transfer-add-chunk-retains-union`,
`fn-transfer-complete-entry-candidate-correct`); this lane adds no theorem
about them beyond replay.

## Keystones, verbatim (packet B, `books/container-invariants.lisp`)

```
(defthm fn-ct-identity-okp-is-spec-okp
  (implies (equal digest (fn-frame-digest
                          (fn-id-subject-preimage (fn-ct-article-octets a))))
           (equal (fn-ct-identity-okp a digest) (fn-ct-identity-spec-okp a))))

(defthm fn-ct-receipt-implies-validated
  (implies (fn-ct-receiptp
            (fn-ct-result-receipt
             (fn-ct-publish-article s a digest articles digests store profile
                                    generation groups evidence obligation-digest completion)))
           (fn-ct-article-validp a digest articles digests store profile (len articles))))

(defthm fn-ct-accepted-is-complete-of-prepare
  (implies (equal (fn-ct-result-status (fn-ct-publish-article s a digest articles digests store
                                          profile generation groups evidence obligation-digest completion))
                  :accepted)
           (and (fn-ct-article-validp a digest articles digests store profile (len articles))
                (equal completion :durable)
                (not (equal (fn-node-prepare s generation (fn-ct-article-msgid a) (fn-ct-article-octets a) groups
                                             (fn-ct-obligation-string obligation-digest)
                                             (fn-ct-subject-string a) evidence (fn-ct-charge a))
                            s))
                (equal (fn-ct-result-state (fn-ct-publish-article ...same arguments...))
                       (fn-node-complete
                        (fn-node-prepare s generation (fn-ct-article-msgid a) (fn-ct-article-octets a) groups
                                         (fn-ct-obligation-string obligation-digest)
                                         (fn-ct-subject-string a) evidence (fn-ct-charge a))
                        (fn-state-next-txid (fn-node-acceptance s))
                        generation :durable)))))

(defthm fn-ct-invalid-article-leaves-node-unchanged
  (implies (not (fn-ct-article-validp a digest articles digests store profile (len articles)))
           (and (equal (fn-ct-result-status (fn-ct-publish-article ...)) :invalid)
                (equal (fn-ct-result-state (fn-ct-publish-article ...)) s)
                (equal (fn-ct-result-receipt (fn-ct-publish-article ...)) nil))))

(defthm fn-ct-accepted-article-is-in-the-node
  (implies (equal (fn-ct-result-status (fn-ct-publish-article ...)) :accepted)
           (fn-acceptedp (fn-ct-article-msgid a)
                         (fn-state-articles (fn-node-acceptance (fn-ct-result-state (fn-ct-publish-article ...)))))))

(defthm fn-ct-store-resolved-verdict-ignores-siblings
  (implies (fn-ct-all-in-store (fn-ct-article-deps a) store)
           (equal (fn-ct-article-validp a digest articles digests store profile fuel)
                  (fn-ct-article-validp a digest nil nil store profile fuel))))

(defthm fn-ct-self-dependency-never-validates
  (implies (and (not (member-equal id store))
                (member-equal id (fn-ct-article-deps (car (fn-ct-find-provider id articles digests)))))
           (not (fn-ct-article-validp (car (fn-ct-find-provider id articles digests))
                                      digest articles digests store profile fuel))))

(defthm fn-ct-conflict-is-evidence
  (implies (and (member-equal a candidates) (member-equal b articles)
                (equal (fn-ct-article-msgid a) (fn-ct-article-msgid b))
                (not (equal (fn-ct-article-content-id a) (fn-ct-article-content-id b))))
           (member-equal a (fn-ct-conflict-evidence candidates articles))))

(defthm fn-ct-invalid-head-does-not-block-siblings
  (implies (and (consp candidates)
                (not (fn-ct-article-validp (car candidates) (if (consp digests) (car digests) nil)
                                           articles all-digests store profile (len articles))))
           (equal (fn-frame-item 0 (fn-ct-publish-list s candidates digests obligation-digests completions
                                                        articles all-digests store profile generation groups evidence))
                  (fn-frame-item 0 (fn-ct-publish-list s (cdr candidates) (cdr-or-nil digests) (cdr-or-nil obligation-digests)
                                                        (cdr-or-nil completions) articles all-digests store profile
                                                        generation groups evidence)))))

(defthm fn-ct-unknowns-are-never-consulted
  (implies (and (fn-ct-unknowns-okp us profile) (fn-ct-unknowns-okp us2 profile))
           (equal (fn-ct-publish-container s (fn-ct-make-container v as us) ...)
                  (fn-ct-publish-container s (fn-ct-make-container v as us2) ...))))
```
(`...` elides repeated argument lists; `cdr-or-nil` stands for
`(if (consp x) (cdr x) nil)` exactly as in the book. The book is the
statement of record.)

Hypothesis stacks: A-CRYPTO under `fn-ct-identity-okp-is-spec-okp` and the
identity rule of `books/identity.lisp` (`fn-id-subject-of-payload`);
`fn-node-prepare-preserves-state` and the acceptance definitions
(`fn-accept-prepare`, `fn-install-pending`) opened one layer each under
`fn-ct-accepted-article-is-in-the-node`; nothing else outside the book.

Covered scope: validation and publication of the logical container; the
byte grammar (D08/D15), signatures and authorization are not here. Stated
limitation: dependency lists are container metadata, not identified octets,
and the first identity-checked provider of a content id wins
(`specs/container.md`; the tooth `ct-teeth-cycle-without-self-dependency`
exhibits it).

## Teeth

`tests/acl2/transfer-journal-tests.lisp`: the two-fragment restart trace
(reserve, tail, head, crash, replay, exact missing ranges `((2 1) (3 1))`,
resume to `(:unverified (1 2 3 4 5 6))`); duplicate, differing overlap,
byte-identical overlap, reorder, malformed input; three corruptions
(truncated frame, wrong trailer, lying outcome), each a typed fault with the
prefix state; `must-fail` per hypothesis of every keystone (non-natural
index; unencodable empty label for `fn-tj-records-okp`; an opening frame for
the corrupt keystone; `:reserved` and `:stored` records for the refusal
keystone; `:junk` for `fn-tj-run-preserves-statep`; foreign digests for the
host entry point; a bad record and a short digest for the frame pair).

`tests/acl2/container-tests.lisp`: a container with a tampered article (A's
identity over other octets), a valid A, a valid B depending on A, and an
unknown object; T refused with no receipt, A and B published through
`fn-node-prepare`/`fn-node-complete`, unknown carried; version refusal,
missing dependency, a two-article cycle, an oversized article, an aborted
completion, a retention refusal, one Message-ID with two content ids
(evidence returned, second refused); `must-fail` per hypothesis of every
keystone.

## Proposals (host work, not claims)

- `tools/run_transfer.py`: append `fn-tj-encode` of `fn-tj-write` to
  `transfer.fntj` with `fsync` before adopting the kernel state; replay with
  `fn-tj-replay-frames-with` at start. The BP side maps a reassembled bundle
  payload (`books/bp-fragment.lisp`) to a `:chunk` input (C2-08).
- `tools/run_container.py` and a container byte grammar in the
  `records.lisp` style, golden vector plus round-trip theorem as its gate
  (`specs/container.md`).
- D08/D15: carry the dependency list inside the identified, signed object
  so a container cannot attach a different dependency list to the same
  content id.
- `planning/proofs.json` is not owned by this lane: the journal keystones are
  candidates for PRF-007/011/016 and SCN-009/013/015, the container keystones
  for PRF-001/005/011/016 and SCN-009/012/013, once a host caller exists for
  the journal.
