# Representation, boundary 6: the octet buffer as an abstract stobj, and the prepare path reads it by index, 2026-09-25

Lane `lane/rep-octets-stobj`, from dev `e366c633`. Commit `219fd392` (the
stobj, the consumer, the teeth, the host lines, the registry) and the
evidence commit that carries this record and `rep-octets-2026-09-25/`.
Design: `planning/design-2026-09-25-representation.md` §5, wave B,
boundary 6. The spike `spike/representation` prototyped the same stobj
with its obligations deferred (`skip-proofs`, D28); nothing from it is
taken unproved: every obligation and every vocabulary theorem it deferred
is proved here, and its prefix-equality theorem was false as stated (see
Findings).

## What the cost was

On the served POST path the payload the owner produced is handed back to
ACL2 as a fresh octet list three times per article: the subject digest
(`fnn-subject-id`, host/native/io.lisp:923), the existing-article test
(`fn-owner-existing-action`, host/native/owner.lisp:762 to 764) and the
prepare (`fn-owner-prepare`, :776 to 779). Each is `fnn-octet-list`, one
cons per octet, and the existing-article test walks its copy through
`fn-inj-source-of` (the Path, Injection-Date and Injection-Info strips)
and `equal`. The chunk read (`fn-owner-chunk`, :1520) makes one more list
per socket read, which the owner's wire machine consumes into the
submission's logical octets. Boundary 6 in the design is the base the
payload boundaries share: one buffer the host fills from the byte array
and the codecs read by index.

## The stobj (`books/octets-stobj.lisp`, prefixes `fn-oct-`, `fn-octets-`)

`fn-octets` is a `defabsstobj`: recognizer `fn-cbor-octet-listp`, creator
nil, executable a concrete stobj with a resizable `(unsigned-byte 8)`
array and a natural fill count. Exports: `fn-octets-len` (`len`),
`fn-octets-get` (`nth`), `fn-octets-put` (`update-nth`),
`fn-octets-append-octet` (`append` of one octet; the array doubles from
1024 when full), `fn-octets-clear`, `fn-octets-reserve` (grow the array,
the value unchanged: what the host calls before its raw fill),
`fn-octets-list` (the list, consed once, tail-recursively) and
`fn-octets-from-list`. The abstraction relation `fn-octets$corr`: the
concrete object is well formed, the abstraction is an octet list, the fill
count is within the array, and the array's first FILL cells read in order
are the abstraction (`fn-oct-list-from`).

| Theorem | Statement | Host line |
| --- | --- | --- |
| `create-fn-octets{correspondence}` | the creator's array corresponds to the empty list | the stobj is created with the image; `fnn-live-octets` (io.lisp) is the state's entry |
| `fn-octets-get{correspondence}`, `{guard-thm}` | under `fn-octets$corr` and the guard (`natp i`, `i < len`): the array read is `nth` on the abstraction, and the exec guard holds | every derived reader |
| `fn-octets-put{correspondence}`, `{guard-thm}`, `{preserved}` | the array write corresponds to `update-nth`; the abstraction stays an octet list | - |
| `fn-octets-append-octet{correspondence}`, `{guard-thm}`, `{preserved}` | the write at the fill count, through the doubling resize, corresponds to `append` of the octet (`fn-oct-append-octet-step` is the lemma: the abstraction extends by one, the concrete invariant is kept) | `fn-oct-write-list`, hence `fn-octets-from-list` |
| `fn-octets-list{correspondence}`, `{guard-thm}` | the tail-recursive read (`fn-oct-buf-list-down`) is the abstraction | `fn-owner-prepare-buffer` (the record's payload, once) |
| `fn-octets-from-list{correspondence}`, `{guard-thm}`, `{preserved}` | clear then write corresponds to the list written (`fn-oct-write-list-steps`) | the teeth's local buffers; the escape hatch for a caller not yet rewritten |
| `fn-octets-clear{…}`, `fn-octets-reserve{…}`, `fn-octets-len{…}` | fill := 0 is nil; a resize keeping the range keeps the value; the count is `len` | `fnn-octets-fill` calls the exec of reserve |
| `fn-oct-slice-list-is-take-nthcdr` | `(fn-oct-slice-list i n st)` is `(take (- n i) (nthcdr i st))` for a true list, `i ≤ n ≤ len` | the Injection-Date octets in `fn-pbb-source-index`; the first line in `fn-pbb-line` |
| `fn-oct-prefix-equalp-is-list-prefixp` | the in-place prefix test is "opens with", the list-model shape `fn-inj-strip` has (not `take`: past the end `take` pads with nil, and a prefix holding nil would then match where the buffer has nothing) | - |
| `fn-oct-suffix-equalp-is-equal` | the in-place suffix test is `(equal (nthcdr i st) xs)` for a true list | `fn-pbb-same-articlep`, both compares |
| `fn-oct-line-end-bounds` | the line end is within `[i, len]` | `fn-pbb-line`'s guard |

Every executable function is guard-verified (`fn-octets$c-*`, the readers,
`fn-pbb-*`: asserted in the test book). `nth` and `update-nth` stay closed
from the correspondence on, and the abstraction `fn-oct-list-from` stays
closed once its lemmas are proved; the obligations are proved from the
list lemmas and the built-in `nth-update-nth`, `len-update-nth`.

## The consumer (`books/poster-bytes-buffer.lisp`, prefix `fn-pbb-`)

| Theorem | Statement | Host line |
| --- | --- | --- |
| `fn-pbb-existing-action-is-pb-existing-action` (keystone) | `(implies (fn-octets-p st) (equal (fn-pbb-existing-action msgid st groups s) (fn-pb-existing-action msgid st groups s)))`: the buffer function equals the list function on the buffer's logical value, for every store `s`, Message-ID and group list; the one hypothesis is the stobj's recognizer, which every live buffer satisfies | `host/owner-host.lisp` `fn-owner-existing-action-buffer` (line 1508) and `fn-owner-prepare-buffer` (line 473), called from `host/native/owner.lisp` `fnn-owner-attempt` (lines 769 and 783) after `fnn-octets-fill` (line 768) |
| `fn-pbb-strip-at-is-inj-strip` | `(fn-inj-strip prefix (nthcdr i st))` is `:no` when the index walk answers `:no`, else the suffix at the walk's index | inside every strip of the source walk |
| `fn-pbb-source-index-is-inj-source-of` | `(fn-inj-source-of st agent msgid)` is nil when the index walk answers nil, else `(cons t (nthcdr k st))` for the walk's index k | `fn-pbb-same-articlep` |
| `fn-pbb-line-is-pb-line`, `fn-pbb-path-agent-is-pb-path-agent`, `fn-pbb-same-articlep-is-pb-same-articlep` | each twin equals its reference on a true list | the keystone's proof |
| `fn-pbb-buffer-is-octet-listp` | a buffer value is `fn-octet-listp` (the acceptance model's recognizer): the list entry's test that the buffer entry drops | `fn-owner-prepare-buffer` |

**No statement of any existing theorem changed.** `fn-pb-existing-action`,
`fn-inj-source-of` and their callers are untouched; the twins are the
only new definitions and the correspondences the only new obligations.

**The exponent, from the definitions.** `fn-pb-existing-action` over a
list copy costs L conses at the boundary plus the walk; `fn-pbb-existing-action`
conses the first line (at most the Path line, bounded by the payload's
first LF) and the 31 Injection-Date octets, and walks the rest by index:
O(L) time, O(line) conses. The prepare's record still holds the payload
as a list (`fn-octets-list`, L conses, once): that copy is the store
record's own field and goes with wave C, not with this boundary.

## Teeth (`tests/acl2/octets-stobj-tests.lisp`)

- **The exec path.** `ost-exec-run` on a live local buffer: from-list,
  len, get, put, append, list, clear, the values as the list model gives
  them; `ost-exec-big`: 3,000 octets through the doubling resize from a
  10-cell reserve, the list read back equal, a slice, both prefix
  answers, both suffix answers, the line end.
- **Each obligation on ground values.** `*ost-c*` = `((5 6 7 0) 3)`,
  `*ost-a*` = `(5 6 7)`, corresponding. For get: without the
  correspondence (fill 5 over a 4-cell array) the cell past the array is
  nil against the abstraction's 0; without `natp i` (i = -1 on an empty
  buffer) the array's first cell against nothing; without the bound (i =
  3) the spare 0 against nil. For put: without the correspondence the
  fill stays beyond the array; without `natp` the abstraction grows a
  cell the array does not; without the bound the write lands past the
  fill; without the octet (300) the array is no longer well formed. For
  append: a mismatching abstraction, and 300. For list: fill beyond the
  array. For from-list: without octets (300); the correspondence
  hypothesis beyond the concrete recognizer carries nothing (writing a
  list resets the buffer): `ost-w-from-list-needs-only-the-recognizer`
  is the weakened theorem, proved, and an object that is not a concrete
  buffer is refused by the stobj primitives before a step runs, so that
  conjunct's removal is not evaluable. Each is an `assert-event` or a
  ground `defthm` plus a `must-fail` of the theorem's instance.
- **The readers' hypothesis.** `(1 2 . 3)` against `(1 2)`: the buffer
  reads to its length and says equal, the list model says not.
- **The keystone.** The completing owner's store
  (`*osi-completing*` finished: the article connection 4 injected):
  duplicate on the held payload; duplicate on the same source
  re-injected under another Injection-Date (other octets, the source
  path); conflict on a changed body octet; conflict on other groups; nil
  on an absent Message-ID; the list function and the buffer function
  (run on a live local buffer) agree on all five. The recognizer
  hypothesis: the held payload with an improper tail is `:conflict` for
  the list function and `:duplicate` for the buffer function
  (`ost-t-improper-buffer-reads-to-its-length`), and the instance is
  `must-fail`.

## Certification (persvati, ACL2 8.7 `acl2-literal`, 300 s)

- Iteration: `tools/proof_repl.py` on persvati in the mirrored lane
  (`/home/ember/fn-gates/rep-octets-e366c633`), then `certify_books.py
  --jobs 1` there for the three books:
  `certify-20260925T092014Z-3165400` (octets-stobj, poster-bytes-buffer)
  and `certify-20260925T092843Z-3251464` (octets-stobj-tests), all
  passed.
- Farm run `run-20260925T092933Z-d21c` (2 jobs, 300 s, incremental,
  140 of 143 books installed from the box's cache), manifest
  `planning/evidence/manifests/certify-20260925T092949Z-3263283.json`:
  the three roots certified at commit `219fd392`'s bytes, 3 of 3 passed,
  exit 0.

## Measurement (hbox, developer images, 2026-09-25 05:21 to 05:36 UTC)

Both trees certified in place on hbox (ACL2 8.7 `acl2-literal-4g`, 8 jobs,
`swarm-build`, incremental from `/tank/fn/certcache`) and both images
built in the same session by the scripts in `rep-octets-2026-09-25/`
(`setup.sh`, `build.sh`, `round.sh`, `load_sized.py`), scratch
`/tank/fn/scratch/rep-octets/`: before = dev `e366c633`
(`hbox-base-certify-20260925T092116Z-3016494.json`, 1 certified, the rest
from the cache); after = lane `219fd392`
(`hbox-after-certify-20260925T092928Z-3039230.json`: `octets-stobj`,
`poster-bytes-buffer`, `native-operator` certified, the rest from the
cache); image digests in `images-and-certs.txt`. Box load 6 to 16, other
lanes measuring, no fn tenant. Three rounds, before and after alternated
(`rounds.sh`), work directories on tmpfs `/dev/shm`.

**POST wall at N = 120** (`load_sized.py`, one NNTP connection, every POST
timed; medians of the last quarter, milliseconds; two runs per round at
160 octets, the sprof run and the call-count run, both listed):

| round | 160 octets, before | after | 2 KiB, before | after |
| ---: | ---: | ---: | ---: | ---: |
| 1 | 0.769, 0.765 | 0.805, 1.182 | 2.067 | 2.174 |
| 2 | 0.741, 0.738 | 0.700, 0.763 | 2.032 | 2.107 |
| 3 | 0.768, 0.767 | 0.734, 0.751 | 2.096 | 2.042 |

Loading 120 articles of 160 octets: 1.10 to 1.12 s before, 1.10 to 1.11 s
after; of 2 KiB: 0.275 to 0.287 s before, 0.270 to 0.293 s after (the
2 KiB loads were run without the profiling image's sampler thread, hence
faster). **The POST wall does not move at this boundary: every before and
after range overlaps, in both sizes, in all three rounds.** That is what
the design's share said for boundary 6 alone (`fnn-octet-list` under 1%
self, the payload recognition 1.5 to 2.7% at 160 octets); the two list
copies this lane removes are a small fraction of a 0.75 ms POST, and the
digest's list copy and the record's own list remain. The value of the
boundary is the base it gives boundaries 7 to 9 and wave C, not a figure
of its own.

**RSS after load** (`VmRSS`, no forced GC): 383.6 to 384.3 MiB before,
384.9 to 385.4 MiB after at 160 octets; 388.7 to 389.0 before, 389.5 to
389.8 after at 2 KiB. The slope from the quarter point to the end is 498 to
506 KiB per article at 160 octets and 181 to 190 KiB at 2 KiB, the same
before and after: SBCL's garbage headroom, as `rep-heap-2026-09-25.md`
measured (the live slope there is 6.1 KiB per 160-octet article). The
after image holds the buffer's array (1 KiB at rest, grown to the largest
payload seen) once.

**CPU profile** (`prof.sh`-style sprof at 1 ms over the last 48 POSTs,
`post-{base,after}-n120-r{1,2,3}-{flat,graph}.txt`): 32 to 41 samples per
run, 0.7 to 0.85 per POST, too few for a share of anything under a tenth
of the POST; the samples sit in the frame write and the publish
(`fnn-owner-publish-prepared`, `rename`, `__write`), the record recognizer
(`fn-cbor-octet-listp`) and the list appends, on both images.
`fnn-octet-list` and `fn-pb-existing-action` appear in no round's flat
profile on either image.

**`fnn-octet-list` calls per POST.** Not measured: the scratch profiling
hook's deterministic mode (`FN_DPROF`, `sb-profile:report`) wrote nothing
on this image in six runs (`calls-*.out`, `stderr-*` kept from the owner's
stderr), so the count is from the code path, not from a counter. Before:
per served POST the payload is converted at the subject digest
(io.lisp:923), the existing-article test (owner.lisp:764) and the prepare
(:777), plus one conversion per socket read at the chunk (:1520): 3 +
chunks. After: the digest (:923) and the chunks: 1 + chunks; the record's
own list is consed once inside the prepare (`fn-octets-list`). The
Message-ID, obligation, subject and evidence strings are converted as
before (short, one per POST each). A counting hook that works is the first
thing the next measurement should add.

**N = 10,000 and 32 KiB: not measured.** The default store profile
(`store init`, `:development`) refuses the 129th article of a 10,000
load ("441 posting failed; the store has no capacity for this article",
`round-*.out`) and any 32 KiB article ("the article exceeds the configured
size"); the CLI `init` verb takes no profile, so those two points need the
offline profile upgrade (`fnn-upgrade-profile-write`) in the harness
first. The 2 KiB point at N = 120 stands in for the size axis.

## What `make check` says on the lane

`tools/ledger.py --check` reports PRF-087 as "events but proof-events.json
does not cover the target" and the ledger stale: the coordinator's
regeneration after the merge (this lane does not edit `planning/ledger.*`).
Two export-hygiene warnings on this lane's books were resolved by
withdrawing the flagged equalities (`fn-oct-octets-p-is-octet-listp`,
`fn-pbb-line-is-pb-line`, `fn-pbb-path-agent-is-pb-path-agent` are
disabled after use).

## Findings

- The spike's `fn-oct-prefix-equalp-is-equal` (stated with `take`) is
  false: `take` pads with nil past the end, so a prefix ending in nil
  matches a buffer that has nothing there. The true statement is against
  a list-level "opens with" predicate, the shape `fn-inj-strip` has.
- A linear rule whose conclusion is `(<= (f i st) (len st))` has `(len
  st)` among its trigger terms and fires on every length in the world with
  `i` free (it broke a plain `nthcdr` lemma in the consumer's world);
  every bounds rule here names its trigger term.
- Constant-index `nth`/`update-nth` and the abstraction at index 0 open
  into car/cdr/cons forms that no lemma is about (as rep-sha256 found for
  the word arrays); both stay closed from the correspondence on.
- The concrete-side functions and the readers take the stobj variable at
  the top level, so ground witnesses over plain values are theorems
  (`ost-w-*`, `ost-r-*`), proved by evaluation, and the exec path runs
  under `with-local-stobj` inside a function.
- `proof_repl.py send` drops a top-level `local`; the hint macros and
  local lemmas were sent unwrapped and the book keeps them local.

## What remains (for wave C and the sibling boundaries)

- The chunk read (`fn-owner-chunk`, owner.lisp:1520) still converts each
  socket read to a list: its consumer is the owner's wire machine
  (`fn-scar-step-counted-fast`) and the accumulated body is the
  submission's logical octets. That is the owner state's representation,
  wave C.
- The subject digest (`fnn-subject-id`, io.lisp:923) still hands a list
  to `fn-store-subject-id-of-payload`: `fn-frame-digest` is the attached
  seam over lists, and a digest of the buffer needs a third message
  reader in `books/sha256-stobj.lisp` (`fn-shs-*-buf`, by index beside
  the string and list readers) with the correspondence stated as
  `fn-sha256-of-string-is-sha256-of-octets` is. That is rep-sha256's
  "digest of a buffer slice" entry.
- The record encoder, the frame and the article parser over the buffer
  are boundaries 7 to 9; the escape hatch `fn-octets-list` is what a
  caller not yet rewritten uses.
