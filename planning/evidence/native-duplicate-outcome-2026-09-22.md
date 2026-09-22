# The second submission of one Message-ID — 2026-09-22

`V0-OUT-REFUSED` read *refused* on node A and *accepted, DUPLICATE* on node B
in the native matrix run of 03:08Z, and the two swapped over freshly
provisioned stores at 03:21Z, with every other row and count identical
([`native-matrix-915-2026-09-22.md`](native-matrix-915-2026-09-22.md)). That
reads as D13 failing on the native `post` path: one operation, two outcomes,
exit 0 or exit 1 by chance.

**It is the harness.** `tools/v0_matrix.py`'s `article()` re-stamped `Date`
from `datetime.now()` on every call, and `native_outcomes` built the article
twice — once for the accepted row and once for the "refused" row. The two
submissions carried the same Message-ID and different octets whenever the
second build crossed a second boundary, which is about half the time at the
gate's step rate. A node that is handed different octets under a Message-ID it
already holds refuses them, correctly. Nothing in the node was
nondeterministic, and the exit codes were right for the inputs they were
given.

## The experiment

On persvati, against the same immutable production image the matrix ran
against.

| | |
| --- | --- |
| image | `/home/ember/fn-gates/freeze-f7190d69/build/images/915d5c729877eddee7dd3f72eadad21cca463d1a/fn-host` (core 303 730 928 octets) |
| image source manifest | `build-source.sha256`, sha256 `eb0051343d388901b48e7f1de281ba3d1f6079cab062f25060b186cf01e3aaa4` |
| runtime | `/home/ember/fn-tools/sbcl/bin/sbcl` |
| node | fresh store per run (`store init fn.letters` through the image), loopback listener on 11317 and 11318, own control socket |
| owner | `nohup env FN_NATIVE_HOST=IMG packaging/fn-native operator CFG run`, stopped with `SIGTERM` by recorded pid |
| submissions | `packaging/fn-native operator CFG post --message-id ID --payload FILE --group fn.letters`, the matrix's own verb |
| scripts and raw output | [`native-duplicate-outcome-2026-09-22/`](native-duplicate-outcome-2026-09-22/) -- `dup-exp.sh` (E1--E3, E5), `dup-exp2.sh` (E4), and each run's whole log |

Every article was built by hand with an explicit `Date`, so the octets are the
experiment's variable rather than the clock's.

**E1 — the same octets, ten times.** One acceptance, then nine resubmissions
of a byte-identical file (digest `f619508034cd85d8`, unchanged at the end).

```
[E1 submit 1]                    rc=0 accepted operator post ACCEPTED
[E1 submit 2..10 identical]      rc=0 accepted operator post DUPLICATE   (x9)
```

Nine identical trials, nine identical words. There is no race between the
existing-article check and `fn-owner-prepare`.

**E2 — one second of `Date`.** The same Message-ID and body, `Date` one second
later, is the only difference between the two files.

```
[E2 submit 1]                            rc=0 accepted operator post ACCEPTED
[E2 with Date+1s, try 1..3]              rc=1 refused operator post REFUSED  (x3)
[E2 the original bytes again]            rc=0 accepted operator post DUPLICATE
```

The node's word is a function of the octets, and it goes back.

**E3 — a different body.** Same Message-ID, edited body: `rc=1 refused
operator post REFUSED`.

**E4 — the driver's own pattern, twelve trials.** Each trial regenerates the
article from `date -u` immediately before each of the two submissions, exactly
as `article()` did, with the gap between them swept across a second boundary
(0, 0.25, 0.4, 0.5, 0.6, 0.75, 0.8, 0.9, 1.0, 1.2, 1.25 s).

| `Date` equal | trials | second submission |
| --- | --- | --- |
| yes | 2 | `rc=0 accepted operator post DUPLICATE` |
| no | 10 | `rc=1 refused operator post REFUSED` |

Twelve for twelve. The word tracks the octets and nothing else — not the node,
not the store, not the order, not the clock except through the bytes it wrote.

**E5 — what the node holds.** In the E1--E3 store, the 158 octets submitted
for `<e1@…>` appear verbatim at offset 42 of the 483-octet transaction record:
the node stores the authored article as it arrived and adds nothing to it (D01
keeps `Path` and injection provenance in separate projections, and
`fn-owner-prov-post` builds that provenance as the record's *evidence*, not as
payload). The E4 store, after twelve trials and twenty-four submissions,
reports `transactions=12 articles=12`: no duplicate created an acceptance and
no conflict created one either.

So of the three hypotheses the finding named — (a) the two nodes hold
different copies because one arrived by transit, (b) a race inside the owner
between the existing-action check and prepare, (c) the driver sends different
bytes — (c) is confirmed and (a) and (b) are refuted. (a) was also impossible
by construction: `native_outcomes` runs per node before either transit phase,
each node submits its own Message-ID, and the peer records carry outbound `-`.

## What ACL2 says the word is

The octets are compared by `fn-store-article-match`
(`host/store-host.lisp:138`), which the owner reaches through
`fn-owner-existing-action` (`host/owner-host.lisp:945`) and the native host
calls at `host/native/owner.lisp:635`. It compares the submitted payload with
`(fn-article-payload article)` — the article as accepted — and the submitted
group selection with `(fn-article-groups article)`: equal on both gives
`:duplicate`, a held Message-ID with anything else gives `:conflict`.

From there every decision is ACL2's, and it is one decision each:

- `fn-duplicate-accepted-prepare-is-no-op` (`books/acceptance.lisp:348`) —
  for a `fn-statep` state, `(fn-acceptedp msgid (fn-state-articles s))`
  implies `fn-accept-prepare` returns the state unchanged. A Message-ID the
  node holds gets no second acceptance, whatever the octets are.
- `fn-own-control-outcome-result` (`books/owner.lisp:1566`) keeps `:duplicate`
  as its own word: "a duplicate is a refusal to create a new acceptance, while
  remaining an idempotent success for the posting client."
- `fn-own-control-accepted-uses-owner-completion`
  (`books/owner-invariants.lisp:947`) — a control result of `:accepted`
  implies `(fn-own-outcome-completion o word)` is `:durable`, so a duplicate
  can never be dressed as a fresh acceptance.
- `fn-native-control-status-class` and `fn-native-control-status-exit-code`
  (`books/native-control.lisp:273` and `:281`) project the five words onto the
  three outcomes: `:duplicate` joins `:accepted` at exit 0, `:busy` joins
  `:refused` at exit 1, `:uncertain` is 3, anything else is 4.

The host adds nothing: `fnn-operator-execute-post`
(`host/native/operator.lisp:131`) asks ACL2 for both the class and the code
and prints `<class> operator post <STATUS>`, which is why the two words differ
on the wire (`accepted operator post DUPLICATE` is not `accepted operator post
ACCEPTED`) while sharing an exit code. `fn-nop-parse-post`
(`books/native-operator.lisp:101`) only parses.

So the answer to the question the finding asked: **a byte-identical
resubmission is `DUPLICATE`, an idempotent acceptance, exit 0; a submission of
different octets under a held Message-ID is `REFUSED`, exit 1.** Both are
deterministic, both are ACL2's, and the three outcomes stay distinct. The
specification agrees — `specs/nntp.md` NNT-005: "The duplicate POST response
is a policy/profile decision; idempotent storage effects do not imply
identical wire replies."

## What changed

- `tools/v0_matrix.py`. `article_stamp` holds one `Date` per Message-ID for
  the life of a run, so `article()` is a function of its arguments and no row
  can vary octets it means to hold fixed. `native_submit` takes a `tag` that
  gives a deliberate variant its own file. `native_outcomes` now makes three
  submissions of one Message-ID — new, byte-identical, and edited — and
  `V0-OUT-REFUSED` observes the third, a genuine conflicting-Message-ID
  refusal, rather than a resubmission that was supposed to be identical. Its
  `limit` said "the same submission a second time, refused by the Message-ID
  binding", which was both the wrong mechanism and the wrong prediction; it
  now names the octets. The idempotent duplicate is recorded as the
  `duplicate resubmission <node>` fact with its word and exit code.
- `tests/test_native_v0_matrix.py`. `DuplicateOutcomeTests`: one Message-ID
  keeps one `Date` across a forced second boundary (and a different
  Message-ID still gets its own), the two identical submissions push
  byte-identical octets to one path, the conflicting one pushes different
  octets to its own path, and the row's `limit` no longer claims the refusal
  comes from an identical resubmission.
- `tests/acl2/native-control-tests.lisp`. The book asserted exit codes for
  `:accepted`, `:refused`, `:uncertain` and `:fault` and had no case for
  `:duplicate` at all — the word at the centre of this finding was untested.
  Added: `:duplicate` is in the reply vocabulary, its class is `:accepted` and
  its code 0, `:busy` is `:refused` and 1, the sealed reply round-trips
  `:duplicate` and `:refused` so the operator can print them, and the teeth —
  exit 0 needs the accepted-class hypothesis, since a word outside the
  vocabulary is 4 and every other outcome keeps its own code.
- `planning/ledger.json`, `planning/ledger.md`. Regenerated by
  `tools/ledger.py --write`: `assert-event` checks 7054 → 7068, this test book
  29 → 43.

## Certification — requested, and blocked by a red that is not this lane's

`tools/farm.py submit persvati tests/acl2/native-control-tests --closure
--jobs 8 --timeout-seconds 1800 --remote-root /home/ember/fn-gates/w31-duplicate
--acl2 /home/ember/fn-gates/toolchains/w25/acl2-literal --cache
/home/ember/fn-certcache`, run `run-20260922T034331Z-0a75`, exit 1. Manifest:
[`certify-20260922T034334Z-3389043.json`](manifests/certify-20260922T034334Z-3389043.json).

Eighteen books failed and seventeen of them failed on `include-book`. The one
real failure is `books/hybrid-store`: the guard conjecture for
`FN-HSIG-KEYRING-SNAPSHOT-VALUE` does not prove ("No induction schemes are
suggested by \*7"). `books/native-control` reaches it through `native-admin` →
`node-config` → `config-records` → `replay` → `hybrid-store`, so the test book
never got as far as its own forms.

**That red is on `dev` and predates this lane.** It is the single failure of
[`certify-20260922T024624Z-85648.json`](manifests/certify-20260922T024624Z-85648.json)
(02:46Z, from nextop.local) and it is in the failure list of the 02:15Z and
02:29Z hbox freeze runs as well. This lane changed no book and no book this
lane touched is implicated. **The fourteen new `assert-event`s have therefore
not been evaluated by ACL2**, and this book has to be recertified once
`hybrid-store` is green.

What they assert is not in doubt, though, because the running image performed
it: the 915 operator answered `accepted operator post DUPLICATE` with exit 0
and `refused operator post REFUSED` with exit 1 across the forty-one
submissions above, which is `fn-native-control-status-class` and
`fn-native-control-status-exit-code` executing on the projection the new
assertions name.

## What remains open

- **The duplicate/conflict split is not in a book.** `fn-store-article-match`
  is `:program`-mode host code and no theorem names it, yet it is the
  comparison that decides between an idempotent acceptance and a refusal. The
  words it produces and their exit codes are ACL2's; the predicate over the
  octets is not. Under "one owner per decision, and it is ACL2" that is a gap,
  and it is not this lane's fix: moving the comparison into `books/acceptance`
  next to `fn-find-article` re-proves everything that includes that book.
  Recorded here, not claimed away.
- **The fix is not verified inside a native image.** The experiment above ran
  the *node* against the 915 image and settled what the node does; the changed
  driver has not been run end to end, because the matrix rerun is the matrix
  lane's and `build/lanes/w31-freeze/IMAGE-READY.txt` had not appeared. The
  next native matrix run is what turns `V0-OUT-REFUSED` into a deterministic
  row on the record.
- **The scratch directory is gone.** The experiment ran under
  `/home/ember/fn-gates/w31-duplicate/` on persvati and the certification
  submit later rsynced a repository tree over it, which is why the scripts and
  logs are committed here instead. Anything rerunning them should pick a
  directory that is not a farm `--remote-root`, and should keep the port out
  of the ranges the other lanes use (this lane used 11317 and 11318). No
  process, socket or store of this lane is left on persvati.
- **`V0-OUT-UNCERTAIN` is still not-built** on the production image, so D13's
  third outcome remains unobserved on the operator surface; that is unchanged
  by this lane.
