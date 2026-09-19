# Lane `twins-into-acl2` — packet C1-13, bytes into ACL2

Branch `lane/twins-into-acl2`, branched from `0bd0b5c`.
Head: see `git rev-parse HEAD` line at the end of this file.

## 1. What this lane removed

Every twin named in this packet is gone. Python no longer decides framing,
where the integrity trailer goes, content identity, the Message-ID bound, the
group table or the charge policy. It hashes byte strings it does not interpret
(A-CRYPTO), moves bytes, and calls ACL2.

| Deleted Python decision | Was | Replacement bridge call |
| --- | --- | --- |
| FNST framing | `run_store.py:134-155` `frame`/`unframe` built magic, length and SHA-256 trailer | `fn-store-frame-store-protected` then host `seal`; `fn-store-frame-store-decode` |
| FNWF record grammar | `workflow_journal.py:112-175` `KINDS`, `FIELDS`, `STATUSES`, `PHASES`, `RESULTS`, `_text`, `_nat`, `encode_record`, `decode_record` | `fn-store-frame-workflow-protected` / `-decode`, schema from `fn-store-frame-workflow-schema` |
| FNRJ record grammar | `receipt_journal.py:25-70` `KINDS`, `NAMES`, `FIELDS`, `OUTCOMES`, `_s`, `_b`, `encode_receiver_record`, `decode_receiver_record` | `fn-store-frame-receipt-protected` / `-decode`, schema from `fn-store-frame-receipt-schema` |
| FNBI framing | `workflow_journal.py:459-476` `encode_inbound`/`decode_inbound` | `fn-store-frame-inbound-prefix` / `fn-store-frame-inbound-open` |
| Content identity | `run_store.py:771-775` derived `sha256:`/`archive:` strings and the `msgid‖0x00‖subject` preimage | `fn-store-subject-id`, `fn-store-obligation-preimage`, `fn-store-obligation-id` |
| Message-ID bound | `run_store.py:793` (1..250, ≤127, no bracket check) | `fn-store-post-boundary` → `fn-store-msgid-octetsp` → `fn-af-message-idp` |
| Payload / group-count / charge-range bounds | `run_store.py:794-799` | the same one `fn-store-post-boundary` call |
| Group table | `run_store.py:31` `DEFAULT_CONFIG["groups"]` and `:778-785` `group_codes` | `fn-store-group-names`, `fn-store-group-table-id`, `fn-store-group-codes` over `books/store-config` |
| Charge policy | `run_store.py:788` `1 + ceil(len/4096)` | `fn-store-charge` → `fn-charge-for-payload` |
| `host/store-host.lisp` group table | `*fn-store-groups*`, `fn-store-group-code`, `fn-store-groups-from-codes` defined in the host | all three now come from `books/store-config` |

Two host constants remain in Python and are now *checked* rather than
duplicated: `run_store.MAGIC`/`TRAILER_BYTES` and the journal record caps.
`frame_bridge.FrameSession._check_host_constants` compares each against
`fn-store-frame-constants` when a session opens, so a divergence is a startup
failure, not a second grammar.

## 2. The SHA-256 measurement and the decision it drove

Measured once, as the packet directed:

```
$ ACL2_CUSTOMIZATION=NONE acl2 <<EOF
(ld ".../kestrel/crypto/sha-2/package.lsp")
(ld ".../kestrel/crypto/padding/package.lsp")
(include-book "kestrel/crypto/sha-2/sha-256" :dir :system)
(defconst *probe* (make-list 32768 :initial-element 0))
(time$ (len (sha2::sha-256-bytes *probe*)))
EOF
; (EV-REC *RETURN-LAST-ARG3* ...) took
; 0.06 seconds realtime, 0.06 seconds runtime
; (37,273,680 bytes allocated).
32
```

**0.06 s for 32 KiB, well under the packet's two-second threshold.** The
computation is fast enough. It is nevertheless not usable, for two reasons,
and the lane took the constrained-function branch.

1. **The book is uncertified and so is its whole dependency chain.** A plain
   `(include-book "kestrel/crypto/sha-2/sha-256" :dir :system)` fails:
   `There is no certificate on file for .../sha-256.lisp`. The measurement
   above only runs because the two portcullis package files are `ld`-ed first
   and the book is then included *uncertified* — which `certify-book` refuses,
   so no book in this tree can include it. `kestrel/{bv,bv-lists,
   arithmetic-light,lists-light,typed-lists-light,crypto/padding,crypto/sha-2}`
   hold 465 `.lisp` files and 16 `.cert` files in this installation. Making it
   available means certifying that chain into a Homebrew-managed directory
   shared by every lane on this machine.
2. **The cost does not stay at 32 KiB.** 0.06 s and 37 MB at 32 KiB
   extrapolates to roughly 7.7 s and 4.7 GB at the 4 MiB inbound bundle bound,
   on a laptop shared by ten lanes; and every octet would also have to cross
   the decimal-octet bridge twice.

So `fn-frame-digest` is an `encapsulate` in `books/frame.lisp` whose only
constraints are output shape (`fn-cbor-octet-listp` and length 32), with a
local witness proving them satisfiable. It is recorded as A-CRYPTO in
`specs/encoding.md` and `specs/store-experiment.md`. **The upgrade path is
already open and costs no theorem change**: a certified guard-verified
SHA-256 can be attached to `fn-frame-digest` with `defattach`, which needs no
trust tag, and every theorem below keeps its statement while A-CRYPTO becomes
a discharged assumption rather than an assumed one. That is the right shape
for a later packet that decides to certify the kestrel chain.

## 3. Keystone theorems, verbatim, with the host line that calls the subject

### Frame, value direction

```lisp
(defthm fn-frame-decode-of-encode
  (implies (and (fn-frame-inputp magic version kind payload max-payload)
                (fn-frame-digestp digest))
           (equal (fn-frame-decode
                   (fn-frame-encode magic version kind payload digest)
                   digest max-payload)
                  (fn-frame-ok magic version kind payload))))
```

Hypothesis stack: `fn-frame-inputp` (magic is 4 octets, version and kind are
octets, payload is an octet list no longer than the caller's cap, the cap is
at most `*fn-frame-max-payload*`) and `fn-frame-digestp` (32 octets).
Subject: `fn-frame-decode` and `fn-frame-encode`.
Host line: `host/store-host.lisp` `fn-store-frame-store-decode` calls
`fn-frame-store-decode`, which calls `fn-frame-decode`; `tools/run_store.py`
`unframe` calls it through `frame_bridge.FrameSession.store_unframe`.

### Frame, byte direction (canonicality)

```lisp
(defthm fn-frame-encode-of-decode
  (implies (and (fn-cbor-octet-listp octets)
                (fn-frame-digestp digest)
                (fn-frame-result-okp (fn-frame-decode octets digest
                                                      max-payload)))
           (equal (fn-frame-encode
                   (fn-frame-result-magic (fn-frame-decode octets digest
                                                           max-payload))
                   (fn-frame-result-version (fn-frame-decode octets digest
                                                             max-payload))
                   (fn-frame-result-kind (fn-frame-decode octets digest
                                                          max-payload))
                   (fn-frame-result-payload (fn-frame-decode octets digest
                                                             max-payload))
                   digest)
                  octets)))
```

Every accepted octet string is the unique encoding of the value it decodes to.
Same subject and same host line.

### Frame, bound direction

```lisp
(defthm fn-frame-decode-refuses-oversize-before-validation
  (implies (and (natp max-payload)
                (<= max-payload *fn-frame-max-payload*)
                (not (fn-cbor-at-mostp octets
                                       (+ *fn-frame-overhead-octets*
                                          max-payload))))
           (equal (fn-frame-decode octets digest max-payload)
                  (fn-frame-error :limit))))
```

There is no hypothesis about `octets` at all, which is the content: the
refusal happens in the cons preflight, before octet validation and before any
split allocates. `tests/acl2/frame-tests.lisp` exhibits a 43-cons witness that
is not an octet list and still answers `:limit`, and the 42-cons sibling that
reaches `:malformed`, so the refusal separates by the bound and not by shape.

### A-CRYPTO seam

```lisp
(defthm fn-frame-encode-is-seal
  (implies (equal digest
                  (fn-frame-digest
                   (fn-frame-protected magic version kind payload)))
           (equal (fn-frame-encode magic version kind payload digest)
                  (fn-frame-seal magic version kind payload))))

(defthm fn-frame-decode-is-open
  (implies (equal digest (fn-frame-digest (fn-frame-protected-prefix octets)))
           (equal (fn-frame-decode octets digest max-payload)
                  (fn-frame-open octets max-payload))))

(defthm fn-frame-open-of-seal
  (implies (fn-frame-inputp magic version kind payload max-payload)
           (equal (fn-frame-open (fn-frame-seal magic version kind payload)
                                 max-payload)
                  (fn-frame-ok magic version kind payload))))
```

The first two name the constrained function and state exactly the host's
obligation; the third is the round trip with no host obligation left, both
sides using the constrained digest. Host line: `tools/frame_bridge.py`
`FrameSession.seal` and `FrameSession.digest_of` are the two places where the
host discharges that hypothesis.

### What the host may do with a protected prefix

```lisp
(defthm fn-frame-store-encode-is-protected-plus-digest
  (implies (and (fn-cbor-octet-listp record)
                (fn-cbor-at-mostp record *fn-frame-max-store-payload*)
                (fn-frame-digestp digest))
           (equal (fn-frame-store-encode record digest)
                  (append (fn-frame-store-protected record) digest))))
```

with `fn-frame-workflow-encode-is-protected-plus-digest` and
`fn-frame-receipt-encode-is-protected-plus-digest` alongside it. This is why
`FrameSession.seal` — the one line of host code that touches a frame's bytes —
produces exactly `fn-frame-encode`.

### Journal record fields, both directions

```lisp
(defthm fn-frame-fields-parse-of-octets
  (implies (and (fn-frame-spec-listp specs)
                (fn-frame-values-okp specs values))
           (equal (fn-frame-fields-parse
                   specs (fn-frame-fields-octets specs values))
                  (fn-frame-parse-ok values nil))))

(defthm fn-frame-fields-octets-of-parse
  (implies (and (fn-frame-spec-listp specs)
                (fn-cbor-octet-listp octets)
                (fn-frame-parse-okp (fn-frame-fields-parse specs octets)))
           (equal (fn-frame-fields-octets
                   specs (fn-frame-parse-value
                          (fn-frame-fields-parse specs octets)))
                  octets)))
```

Host line: `host/store-host.lisp` `fn-store-frame-workflow-protected` and
`fn-store-frame-workflow-decode`, called from `tools/workflow_journal.py`
`encode_record` / `decode_record` and `tools/receipt_journal.py`
`encode_receiver_record` / `decode_receiver_record`.

### Content identity

```lisp
(defthm fn-id-unhex-of-hex-octets
  (implies (fn-cbor-octet-listp octets)
           (equal (fn-id-unhex (fn-id-hex-octets octets)) octets)))

(defthm fn-id-hex-octets-of-unhex
  (implies (and (fn-id-hex-listp octets)
                (equal (mod (len octets) 2) 0))
           (equal (fn-id-hex-octets (fn-id-unhex octets)) octets)))

(defthm fn-id-hex-octets-injective
  (implies (and (fn-cbor-octet-listp a) (fn-cbor-octet-listp b)
                (equal (fn-id-hex-octets a) (fn-id-hex-octets b)))
           (equal a b))
  :rule-classes nil)
```

Injectivity is the load-bearing one: an identity-string collision is a digest
collision and nothing else. Digest collision resistance itself is A-CRYPTO and
is claimed nowhere. Host line: `host/store-host.lisp` `fn-store-subject-id`
and `fn-store-obligation-id`, called from `tools/run_store.py` `metadata`.

### Charge policy

```lisp
(defthm fn-charge-for-payload-posp
  (posp (fn-charge-for-payload length)))

(defthm fn-charge-for-payload-monotone
  (implies (and (natp m) (natp n) (<= m n))
           (<= (fn-charge-for-payload m) (fn-charge-for-payload n))))
```

Host line: `host/store-host.lisp` `fn-store-charge`, called from
`tools/run_store.py` `conservative_charge`.

### Group table

```lisp
(defthm fn-store-group-code-of-name
  (implies (fn-store-group-of-name name)
           (equal (fn-store-group-code (fn-store-group-of-name name)) name)))

(defthm fn-store-group-name-of-code
  (implies (fn-store-group-code code)
           (equal (fn-store-group-of-name (fn-store-group-code code)) code)))

(defthm fn-store-codes-from-groups-inverts
  (implies (and (true-listp names)
                (not (equal (fn-store-codes-from-groups names) :bad)))
           (equal (fn-store-groups-from-codes
                   (fn-store-codes-from-groups names))
                  names)))
```

The third is the one the boundary actually composes: `group_codes` sends names
and `fn-store-sn-prepare` turns the codes back into names. Host line:
`host/store-host.lisp` `fn-store-group-codes`, and
`host/store-node-host.lisp:47,142` `fn-store-groups-from-codes`.

## 4. Files changed

New books, in dependency order (all added to the Makefile root list in that
order, after `tests/acl2/article-fields-tests`):

- `books/store-config.lisp` — the group table and the name/code mapping.
- `books/frame.lisp` — the frame grammar, the journal field grammar, the
  A-CRYPTO `encapsulate`, and the guard-verified host entry points.
- `books/frame-invariants.lisp` — round trip, canonicality, bounds, the
  A-CRYPTO seam theorems, and the protected-prefix obligations.
- `books/identity.lisp` — hexadecimal, subject and obligation identity, the
  obligation preimage, and the charge policy.
- `books/identity-invariants.lisp` — both hexadecimal directions,
  injectivity, identity shapes, charge positivity and monotonicity.
- `tests/acl2/frame-tests.lisp`, `tests/acl2/identity-tests.lisp` — golden
  vectors generated from the pre-migration Python encoders, concrete refusals
  for every decoder decision, and `must-fail` siblings.

`books/store-config.lisp` is the packet's `host/store-config.lisp` under a
different path, deliberately: `tools/certify_books.py` only accepts roots
matching `books/` or `tests/acl2/`, and a book under `host/` could never be
certified, so nothing in `books/` could include it. Putting the table in a
certified book is also what makes the two directions of the mapping provable
rather than merely shared. `host/store-host.lisp` includes it.

Host:

- `host/store-host.lisp` — includes `../books/replay`, `../books/store-config`,
  `../books/identity` and `../books/article-fields` (it no longer depends on
  the caller having included `replay` first); `fn-store-msgid-octetsp`
  delegates to `fn-af-message-idp`; the group table and its two mappings moved
  out to the book; new marshalling wrappers `fn-store-frame-*`,
  `fn-store-subject-id`, `fn-store-obligation-preimage`,
  `fn-store-obligation-id`, `fn-store-charge`, `fn-store-msgid-validp`,
  `fn-store-post-boundary`, `fn-store-group-names`, `fn-store-group-table-id`,
  `fn-store-group-codes`.

No edits were made to `host/store-node-host.lisp`, `host/workflow-host.lisp`,
`host/bp-receipt-journal-host.lisp` or `host/bp-ingress-host.lisp`: every
function they use (`*fn-store-groups*`, `fn-store-groups-from-codes`,
`fn-store-group-code`, `fn-store-text-octetsp`, `fn-store-msgid-octetsp`) is
still in scope with the same name, now sourced from `books/store-config`.

Python:

- `tools/frame_bridge.py` (new) — the one place that talks to ACL2 about
  frames, identity, bounds, groups and charge; computes SHA-256 over byte
  strings it does not interpret; checks the surviving host slice constants
  against the model at session open.
- `tools/run_store.py` — `MAGIC` is now the six-octet magic/version/kind
  prefix so that the slice arithmetic at `durable_records` and in the
  corruption tests still matches the header; `DEFAULT_CONFIG` format is
  `fn-store-experiment-3` and carries `group_table` instead of `groups`;
  `frame`, `unframe`, `metadata`, `group_codes`, `conservative_charge` and
  `validate_post_boundary` are bridge calls; the unused `hmac` import is gone.
- `tools/workflow_journal.py` — the record kind, field, status, phase and
  result tables and the `_text`/`_nat` field writers are deleted;
  `encode_record`, `decode_record`, `encode_inbound` and `decode_inbound` are
  bridge calls.
- `tools/receipt_journal.py` — same for `KINDS`, `NAMES`, `FIELDS`,
  `OUTCOMES`, `_s`, `_b`, `encode_receiver_record`,
  `decode_receiver_record`.

Specifications and registry:

- `specs/encoding.md` — the frame grammar is now a chosen layout with its
  proved properties named, A-CRYPTO is recorded, and the non-domain-separated
  identity preimage is stated as a defect with a concrete v1 profile to adopt.
- `specs/store-experiment.md` — a new "Framing: what is proved and what is
  assumed" section, and the group/Message-ID/charge ownership change.
- `docs/prefixes.md` — rows for `fn-frame-`, `fn-id-`/`fn-charge-`, and the
  `fn-store-` tag as used by `books/store-config`.
- `Makefile` — seven new roots.

## 5. The format change, and what it costs

FNWF and FNRJ frames are **byte-identical** to what the Python encoders wrote:
`tests/acl2/frame-tests.lisp` asserts eight full records, trailer included,
against vectors generated from those encoders before they were replaced. No
existing workflow or receiver journal changes.

FNST changes: the frame gains the one-octet record kind the Python framing
lacked, so a store transaction file is one octet longer and the store
configuration format moves to `fn-store-experiment-3`. An existing store fails
`_load_config` with "unsupported store configuration" — a loud refusal, not a
misread. FNBI changes: the BID length moves into a payload text field, so an
inbound frame is two octets longer; inbound frames are staged and deleted
within one exchange, so nothing durable depends on them.

`DEFAULT_CONFIG` drops `groups` and gains `group_table`. Nothing durable is
lost: a transaction record stores group *names*, not codes.

## 6. Known defects and remaining gaps

- **Two ACL2 processes per store command.** `frame_bridge.session()` opens its
  own `Acl2Store` because none of the functions this lane owns is called with
  a live bridge in scope and editing the call sites is outside the lane's
  ownership. `frame_bridge.adopt(store)` exists and takes one line to call;
  the proposal is in §7.
- **`fn-frame-inbound-prefix` is two octets stricter than Python was.** Python's
  `MAX_INBOUND_BUNDLE` allows a bundle of exactly 4 MiB; the ACL2 payload cap
  of 4 MiB has to cover the two-octet BID length as well, so a 4 MiB bundle is
  now refused. Nothing in the tree produces one.
- **The evidence label is still a host constant.** `metadata` returns
  `b"unsigned-legacy-v0"`; ACL2 only compares it. That is D9's territory
  (the policy verdict is not durable) and belongs to C1-11, not here.
- **The identity preimage is not domain separated.** Stated in
  `specs/encoding.md` with the v1 profile to adopt; deliberately unchanged
  because existing lab stores and `tests/test_workflow_live.py:23-24` and
  `tests/bp-dtn7/fn_sender_lab.py:67` depend on the exact bytes.
- **No fixture or test loses its Message-ID.** Every Message-ID used anywhere
  in `tests/`, `tools/`, `host/` and `docs/` was checked against
  `fn-af-message-idp`'s grammar. The only strings that fail it —
  `<a..b@example>`, `<a@ex..ample>`, `<a@[x\y]>`, `<a@[]>x` — appear solely as
  negative vectors inside `tests/acl2/article-fields-tests.lisp`, where
  rejection is the assertion. The bound tightens from the host's 512 octets to
  the RFC 5536 250; the longest Message-ID in the tree is 25 octets.
- **A guard-audit test book for the new functions does not exist.** The
  repo has `tests/acl2/*-guards-tests.lisp` books that check
  `:common-lisp-compliant` for other graphs; `books/frame` and
  `books/identity` verify guards at definition but no book asserts it
  independently. That is a natural C1-16 addition.

## 7. Proposals for files this lane does not own

| File and line | Now | Replacement |
| --- | --- | --- |
| `tools/run_store.py` `Acl2Store.__init__`, after the three `ld` calls | nothing | `frame_bridge.adopt(self)` — one line, removes the second ACL2 process from every store, ingress and receive command |
| `host/bp-ingress-host.lisp:8-10` | `*fn-bpi-host-group-map*` lists `fn.letters` and `fn.test` as octet/name pairs | `(include-book "../books/store-config")` and build the map from `*fn-store-groups*` with a `fn-store-group-octet-map` helper |
| `host/reader-host.lisp:5` | `(defconst *fn-reader-groups* '("fn.letters"))` | `(include-book "../books/store-config")` and `(defconst *fn-reader-groups* (list (fn-store-group-code 0)))` |
| `tools/workflow_bridge.py:8-18` | `_FIXED` and `_ORDER` restate the record kinds and field order | `frame_bridge.session().schema("workflow", kind)` returns both, from `books/frame` |
| `tools/receipt_bridge.py:5-9` | `ORDER` restates the receiver field order | `frame_bridge.session().schema("receipt", kind)` |
| `tools/certify_books.py` `DEFAULT_BOOKS` | does not list the seven new roots | add them in the same order as the Makefile, or generate the list from the Makefile |
