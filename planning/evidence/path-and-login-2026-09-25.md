# D32 supplied Path, login binding, and a policy fold fix — 2026-09-25

Lane `path-and-login` (branch `lane/path-and-login`, from dev `24591e11`).
Commits: `4d848b4d` (login binding), `694935ab` (D32), `bba8bb15` (the
config policy fold). The native part was run in a scratch area,
`/tank/fn/scratch/path-login/` on hbox. It was not a deployed node.

## 1. D32: a supplied Path (NNT-012, PRF-090, SCN-050)

**Recipe v3.**
- `fn-inj-decide` accepts one Path field if two things hold. Its unfolded
  value must be RFC 5536 §3.1.5 syntax (`fn-inj-path-valuep`,
  `books/injection-path.lisp`, one bounded pass split at "!"). Its content
  must begin one SP after the colon on a header line of the source octets
  (`fn-inj-path-scan`).
- The node inserts `AGENT!` there (`fn-inj-splice`). The injected block is
  recipe v2's block without its Path line (`fn-inj-block`). So the article
  has one Path, in the place the poster put it:
  `Path: fn.example.invalid!not-for-mail` ([article-p1.log](path-and-login-2026-09-25/article-p1.log)).
- It refuses by name, each with its own 441:
  - `:path-malformed` ("Path is not a valid path"). This includes extra WSP
    before the content, a stated narrowing of the RFC grammar.
  - `:path-duplicate`
  - `:path-posted`, a local policy: RFC 5537 §3.4.1's SHOULD NOT.
  - `:xref` stays.
- fn writes no `!.POSTED`, because RFC 5537 §3.2.1 item 2 is a SHOULD.

**The inverse.** `fn-inj-source-of` reads v2 (and v1) records as before. A
record that does not open with the agent's Path line is read as v3: the
agent's Path line followed by the record reads as v2, and removing the
insertion (`fn-inj-unsplice`) gives the source. The keystone
`fn-inj-source-of-inverts-the-injection` keeps the same statement it had,
with no new hypothesis. It covers every clock reading, all four
generated-field cases, and a Path either supplied or not. It rests on:
- `fn-inj-unsplice-of-a-splice`
- `fn-inj-path-scan-of-a-kept-prefix`: the scan reads nothing at or past
  the offset it returns.
- `fn-inj-injected-octets-are-the-block-and-the-prefixed-source`

**What changed.**
- `fn-inj-injected-article-retains-the-source-octets` and the two
  exact-octet item-11 theorems gain the hypothesis "no Path supplied". Each
  has a v3 twin (`...-with-a-path`).
- `fn-inj-reinjectionp` is now exactly `fn-inj-source-of ... = (t . source)`.
- `fn-pb-path-agent` reads a v3 record's agent from its block's
  Injection-Info line. With that, `fn-pb-one-source-at-two-clocks-is-one-article`
  and `fn-pb-two-sources-are-two-articles` cover a supplied Path: a resend
  at any clock is a duplicate, and a changed Path is a conflict.
- The hybrid carrier route (`fn-hsig-injected-carrier-plan`) still refuses a
  carrier that supplies Path (`:path-present`). Its exact signed source
  therefore stays a suffix, and `fn-hsig-injected-carrier-retains-exact-signed-source`
  is unchanged.
- A served POST of a signed carrier with a Path is accepted. Its
  `fn-hc-received-plan` authored source is the poster's signed source (the
  `hybrid-store-tests` witness), so the carrier projection is unchanged.

**Teeth.**
- `tests/acl2/injection-tests.lisp`:
  - the exact v3 octets for tin's shape, and the same octets at a second
    clock;
  - the parsed Path is `fnA.hbox.test!not-for-mail`;
  - all four inverse cases with the Path first or fourth;
  - a changed Path is not a reinjection;
  - another agent reads nothing;
  - the grammar's accepted forms (tin's three and the RFC 5537 §3.2.2
    example) and seven refused forms;
  - each refusal through `fn-inj-decide`;
  - must-fails for the suffix theorem without its new hypothesis, for
    `fn-inj-unsplice-of-a-splice` without an offset, and for the scan lemma
    without a hit.
- `tests/acl2/poster-bytes-tests.lisp`: through the real Store, the tin
  article held and then resent at another clock is `:duplicate`, where the
  byte decision would say `:conflict`; a changed Path is `:conflict`; a
  Path-less resend is `:conflict`.

## 2. Login binding (NNT-013, PRF-109, SCN-051)

The design and theorems are in `books/login-binding.lisp`, specs/identity.md
and the commit `4d848b4d`:
- The gate `fn-lb-owner-gate` is called by host/owner-host.lisp
  `fn-owner-login-gate` from host/native/owner.lisp `fnn-owner-attempt-served`.
- The keystone is `fn-lb-bound-login-accepted-signed-article-carries-its-principal`.
- "Policy off changes nothing" is `fn-lb-policy-off-never-refuses`.
- The verdict and its service-log line name the login. The Store's kind-4
  record does not; that remains open.

**A defect found natively and fixed here (`bba8bb15`).** On hbox,
`policy set posting-policy open` after `bound-logins` was accepted and
changed nothing. The node kept answering the not-bound 441
([probe-open.log](path-and-login-2026-09-25/probe-open.log), first block).
- The cause was in the configuration fold, not in the gate. `:set-policy`
  used `fn-cfg-row-upsert`, keyed on (slot, value), so a second value
  appended a row that `fn-cfg-policy` (the slot's first row) never read.
  The first value set stayed in force for good; the same held for
  `path-identity`.
- `:set-policy` now folds with `fn-cfg-row-replace-key`. The keystone is
  `fn-cfg-set-policy-sets-the-policy` over `fn-cfg-apply-delta`, with no
  hypothesis. `tests/acl2/config-tests.lisp` witnesses bound-logins, then
  open, then bound-logins, and contrasts it with the old fold.
- The durable records are unchanged. Only their fold is, so a store that
  set a slot twice now replays to the later value.

## Certification (persvati, `w25/acl2-literal`, identity `1b4169e9…`, 2 jobs, 300 s)

| run | source | scope | result | manifest |
| --- | --- | --- | --- | --- |
| `run-20260925T092122Z-f678` | `694935ab` | `--affected-by` injection-path, login-binding, native-auth-profile, native-auth-admin, native-admin, peer-authored-accept: 239 books (233 roots) | **passed**, 239 of 239 | [`certify-20260925T092155Z-3183327`](manifests/certify-20260925T092155Z-3183327.json) |
| `run-20260925T094304Z-ee65` | `bba8bb15` | `--affected-by books/config`: 253 books (248 roots) | **passed**, 253 of 253 | [`certify-20260925T094334Z-3395289`](manifests/certify-20260925T094334Z-3395289.json) |

Seconds per book in run 1 for the books this lane touched:

| books | seconds |
| --- | --- |
| injection-path, injection | 0.4, 0.5 |
| injection-invariants, injection-tests | 2.1, 0.8 |
| poster-bytes, poster-bytes-invariants, poster-bytes-tests | 2.6, 6.4, 4.8 |
| hybrid-store-injected, hybrid-store-invariants, hybrid-store-tests | 2.0, 1.8, 2.6 |
| nntp-post | 4.1 |
| login-binding, login-binding-tests | 5.1, 4.7 |
| native-auth-profile, native-auth-admin, native-admin | 7.1, 4.2, 6.6 |
| peer-authored-accept | 4.1 |

`books/owner-invariants` took **12.5 s** in run 1 and 15.0 s in run 2 (where 16 books this lane did not edit were also over 10 s); it was 10.2 s in the D25 run. Run 2's config books: config 1.2 s, config-invariants 1.2 s, config-tests 1.9 s, native-admin 7.4 s. Its
certify log shows `include-book "owner"` at 4.4 s and no event over 0.8 s.
This lane's one edit there is a `:use` hint in
`fn-own-a-reinjection-is-not-absent`. It is over the ten-second rule, and
that is not fixed here. Other books over 10 s in run 1 are ones this lane
did not edit: bp-report-guards, byte-store-k0-step-bridge,
bp-node-progress-premises, bp-node-forward-lower-guards,
bp-node-forward-retry and config-owner-live.

## Native, hbox (scratch `/tank/fn/scratch/path-login/`)

**Images.**
- Developer images were built from `git archive` of the lane head under
  `swarm-build`, with w28 and `/tank/fn/certcache`:
  - img from `694935ab`: `fn-host-developer.core` `0cebecce…`
    ([image.sha256](path-and-login-2026-09-25/image.sha256))
  - img2 from `bba8bb15`: `.core` `4d0f0091…`
    ([image2.sha256](path-and-login-2026-09-25/image2.sha256))
- The node is the reader spike's launcher on port 11929
  ([pl_node.py](path-and-login-2026-09-25/pl_node.py)): Store `fn.agents`
  `fn.test` (and later `control.cancel`), `[auth] required`, logins `ember`
  and `guest` with hybrid keys. It runs under
  `systemd-run --user -p MemoryMax=24G`.
- The probes are [pl_probe.py](path-and-login-2026-09-25/pl_probe.py). They
  use the spike's fn_web client and local `hybrid-sign-carrier`.
- tin 2.6.2 is the one the reader spike built, in
  `/tank/fn/scratch/spike-reader/tin/inst`. The spike's tmux driver and wire
  logger ran it.

**Supplied Path** ([probe-path.log](path-and-login-2026-09-25/probe-path.log), img):

| row | reply |
| --- | --- |
| P1 `Path: not-for-mail`, Date and Message-ID supplied | 240; stored `Path: fn.example.invalid!not-for-mail` |
| P2 the exact octets again 1.5 s later | 441 this article is already stored here |
| P3 the same with `Path: example.org!elsewhere` | 441 a different article with this Message-ID is stored here |
| P4, P5 Date-less, resent 2.2 s later | 240, then already stored here |
| P6 `Path: a b`; P10 `Path:  not-for-mail` | 441 Path is not a valid path |
| P7 two Path fields | 441 Path appears more than once |
| P8 `x.example!.POSTED!not-for-mail` | 441 Path must not carry a POSTED diagnostic |
| P9 Path with Xref | 441 Xref must not be supplied |
| P11 a signed carrier with `Path: not-for-mail` prepended | 240, `verified 9261767a…` (ember) |

**tin** ([tin-wire.log](path-and-login-2026-09-25/tin-wire.log) is the final
run on img2; [tin-wire-run1.log](path-and-login-2026-09-25/tin-wire-run1.log)
is the first, on img).
- The followup (`References: <pl-dateless-…>`), the new post and the cancel
  each send `Path: not-for-mail`, and each is answered **240**.
- The cancel's `Control: cancel <…56629.fn@fn.example.invalid>` names tin's
  own post (the Message-ID fn generated for "tin run five zqx"). It is
  filed under C1 as `control.cancel` article 1
  ([cancel-check.log](path-and-login-2026-09-25/cancel-check.log)).
- The target is still served. control-c2c3 is not on this lane's base, so
  nothing withdraws it.
- Before `control.cancel` existed, the cancel was answered
  `441 … control-not-filed` (run 3 on img; hbox `logs/tin-wire-run3.log`).
- Aligning tin's keys took four drives. The early runs' extra POSTs are in
  the hbox logs (SHA256SUMS).

**Login binding** ([admin-bind.log](path-and-login-2026-09-25/admin-bind.log),
[probe-bound.log](path-and-login-2026-09-25/probe-bound.log),
[probe-open.log](path-and-login-2026-09-25/probe-open.log),
[service-final.log](path-and-login-2026-09-25/service-final.log)).
- Offline binding goes through the native operator,
  `fn-host-developer --fn operator fn.toml principal bind`:
  - `nobody` is refused `unknown-login` (exit 1);
  - `ember 07` is usage (exit 5);
  - `ember 9261767a…` is accepted and restart-required, and `principal list`
    shows `signing=9261767a…`.
- `bin/fn` has no `principal bind`, and the docs now name the native
  operator. The operator needs `FN_OPENSSL_PREFIX` (it refused without
  OpenSSL 3.5).

| row | policy | reply | service log |
| --- | --- | --- | --- |
| B1 ember signs as ember | bound-logins | 240, verified 9261767a… | `post login=ember bound=9261767a…` |
| B2 ember signs with guest's key | bound-logins | 441 the login is not bound to this signing principal | `refused login-not-bound` |
| B3 ember unsigned | bound-logins | 441 this login posts only articles signed by its bound principal | `refused login-unsigned` |
| B4 guest unsigned, B5 guest signs | bound-logins | 240, 240 (B5 verified bdfb1bc1…) | `login=guest unbound` |
| O1, O2 (img, after `policy set … open`) | still bound-logins: **defect** | the two 441s again | refused |
| O1, O2 (img2, after restart; replayed bound-logins then open) | open | 240, 240; O1 verified bdfb1bc1… (guest) | |
| B1–B5 again (img2, `bound-logins` set live) | bound-logins | as above | |
| O1, O2 (img2, `open` set live) | open | 240, 240 | |

## Limitations

- A single scratch node, not a deployed node, and not the two-node matrix.
- tin was built without TLS and logs in over plain NNTP on loopback.
- The INN lab gained `fn-post-supplied-path-240` but did not run in this
  lane.
- dev's `tools/v0_matrix.py` has no tin rows. The spike's four
  `V0-CLIENT-TIN-*` rows live on `spike/mega`, and none of them pinned the
  refusal on dev.
- `owner-invariants` is 12.5 s, over the ten-second rule.
- `planning/ledger.*` has not been regenerated (coordinator).
