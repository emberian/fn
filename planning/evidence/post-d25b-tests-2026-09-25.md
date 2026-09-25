# post-d25b tests: the INN lab's item-11 check and the cross-entry retry (2026-09-25)

Lane `lane/post-d25b-tests`, from dev `db8e3d86`. The change is at
`4246509a`. It closes findings F2 and F3 of
[qual c3420013](qual-c3420013-2026-09-25.md). No book, host file or image
changed. Every run used the frozen c3420013 images
(`/tank/fn/gates/qual-c3420013-20260925/build/images/c3420013/`, SHA-256s in
that record). No farm run was needed.

## F2: the INN lab asks for what RFC 5537 §3.5 item 11 requires

**What was wrong.** `operator-post-feeds-inn` (`tools/inn_lab.py`) required
all three of Path, Injection-Date and Injection-Info on the article fed to
innd. RFC 5537 §3.5 item 11 says that when the proto-article had both
Message-ID and Date, an Injection-Date "MUST NOT be added". The lab's article
(`article()`) always supplies both. So fn under injection recipe v2 was
right, and the assertion was left over from before the injection inverse.

**The check now.** `expected_injection(posted)` works out the fields from the
submitted octets:
- Path and Injection-Info are always expected (items 8 to 10).
- Injection-Date is expected when the submission already had one, or when it
  lacked Date or Message-ID (item 11).

The check requires the fed header set to equal that expectation exactly. The
Path must still name fn's path identity, and innd must still answer 335/235
(or 238/239). The assertion's sentence in `ASSERTIONS` says the same. The
fact row `operator post injection` records the expected and fed sets.
- The fake image in `tests/test_inn_lab.py` stores `operator post` with no
  Path, so it still violates the check. The module passes 30 of 30 on the
  laptop.
- **Only the dated branch was run on the real image.** The lab's `operator
  post` supplies Date and Message-ID, so this run does not exercise an
  undated submission, which should draw an Injection-Date.

**Run.** This is the matrix's INN phase command, run directly. `v0_matrix.py`
has no row selection, and its INN phase is exactly this command, with the
rows derived from the findings by `v0_matrix.inn_rows`:
`python3 tools/inn_lab.py 4246509a --host hbox --tree post-d25b
--native-image $I/fn-host --native-openssl-prefix $I/openssl --lab-root
/tank/fn/scratch/post-d25b/inn-lab --evidence
planning/evidence/post-d25b-tests/inn-lab.md`, where `I` is the c3420013
image directory. Results:
- rc 0, steps 82, **33 held**, 0 violated, 0 not exercised.
- The fed operator-post article: expected Path=yes, Injection-Date=no,
  Injection-Info=yes, and fed exactly that. Path `fnA.hbox.test!not-for-mail`.
  innd answered `IHAVE: 335 Send it / 235 Article transferred OK`.

| row (`v0_matrix.inn_rows`) | qual c3420013 | now |
| --- | --- | --- |
| V0-INN-OPERATOR-POST | violated (F2) | accepted |
| V0-INN-INTEROP | lab verdict violated (32 held, 1 violated) | accepted (33 held) |
| every other V0-INN-* row | as before | unchanged verdicts |

The matrix was not republished (`--publish-current` was not run). The
current matrix view still carries the qual run's two rows until the next
full matrix.

## F3: one payload through the two entries is a conflict

**The decision: the conflict is correct and the test was wrong.** The
records settle it:
- `store ROOT post` (`fnn-command-post`, `host/native/io.lisp`) is the Store's
  developer write seam. It stores the payload as read, with no injection
  block. Production refuses it (`prod-raw-store-post-guard`). It exists so
  the cut and crash campaigns can put known octets in the Store, and
  `reread` checks its record is the payload octet for octet. It is not a
  posting agent's entry, and fn is not an injecting agent there.
- The inverse the D25 owner merged
  ([d25-injection-inverse](d25-injection-inverse-2026-09-24.md);
  `books/poster-bytes.lisp` `fn-pb-same-articlep`, `fn-pb-subject`) compares
  sources only when both copies give one back under the submission's own
  injecting agent. Otherwise it compares octets. The two arms are tagged, "so
  a source can never equal a payload compared exactly". A raw record has no
  block, so it gives no source. A poster's source compared with it is
  therefore an octet comparison, which fails.
- That is the "never widen across profiles" rule. Rows I1, I2 and V2 of the
  D25 review matrix accept the same answer, a conflict, for another injecting
  identity and for an ambiguous v1 record. A record with no injection
  profile is the extreme case of both.
- The duplicate expectation came from post-d25-tests
  ([record](post-d25-tests-2026-09-24.md)). It was written against d25-dup's
  four-field projection, which the inverse replaced. Before d25-dup the
  campaign expected this conflict.
- Making `store post` inject would turn the Store's raw seam into a second
  posting entry. It would change what every cut campaign writes and reads
  back, all to satisfy one assertion. The campaign cares that a retry
  through the entry that submitted the payload is one article, and it keeps
  that.

**What changed.** `tests/campaign/native_operator_campaign.py`
(`cross-entry-retry-{store-then-operator,operator-then-store}`) now runs four
submissions per order, with no fault:
1. `first`: the payload through entry A.
2. `again`: the same payload through A. This is new, the same-entry retry.
3. `second`: the same payload through the other entry, B.
4. `changed`: one changed Subject byte under the same Message-ID, through A.
   Before, it went through B, where it would conflict for the cross-entry
   reason alone. Through A it separates.

`test_native_operator_campaign.py` expects:
- `again` is the duplicate: rc 0, `DUPLICATE` or `duplicate`.
- `second` and `changed` are the conflict: rc 1, `REFUSED` through the
  operator entry, `conflicting immutable Message-ID` through the store entry.
- The store snapshot after each of `again`, `second` and `changed` equals the
  one after `first`. Transactions, staging and frontier are byte-identical,
  so nothing was written.

The `reread` docstring says so too.

**Runs on hbox**, in a `git archive 4246509a` tree under
`/tank/fn/scratch/post-d25b/tree`, with `FN_NATIVE_IMAGES` set to the
c3420013 image directory:
- `python3 -m unittest -v tests.campaign.test_native_operator_campaign`:
  **10 of 10**, 26.9 s, rc 0 (qual: 9 of 10, F3).
- `python3 -m tests.campaign.native_operator_campaign` in full: rc 0. The
  cross-entry rows:

| order | first | again | second | changed | snapshots equal `after_first` |
| --- | --- | --- | --- | --- | --- |
| store then operator | rc 0 `committed sequence=1` | rc 0 `duplicate` | rc 1 `refused operator post REFUSED` | rc 1 `store: conflicting immutable Message-ID` | again, second, changed: yes |
| operator then store | rc 0 `ACCEPTED` | rc 0 `DUPLICATE` | rc 1 `store: conflicting immutable Message-ID` | rc 1 `refused operator post REFUSED` | again, second, changed: yes |

**What an operator should know.** An article first written by the developer
`store post` cannot be retried through a served POST or `operator post`.
The retry answers "a different article". Production has no raw `store post`,
so this does not reach a deployed node.

## Files

In [`post-d25b-tests/`](post-d25b-tests/), hashes in
[`SHA256SUMS`](post-d25b-tests/SHA256SUMS):

| file | SHA-256 |
| --- | --- |
| `inn-lab.md` | `812046dfc04e4d0c9939bbe236b8ac2bc057ca1a178469f9b05ad402b89001d1` |
| `inn-lab.findings.json` | `2239be8e2973fc380419eeff08ff1c46f55f8a98b9f66b6984055a70eaf70c2f` |
| `inn-lab.log` | `c9f99c32b3f161f263c7af1c9a440c7911f9cf057477041df8287d84a4eb06a1` |
| `image-gated-test.log` | `47e6d9af498c6bf2e47250510cdb70cf9e3b21c21dcc512af047bac7bcdbf8b7` |
| `campaign.log` | `0107665b4c0ac7a1377aa5d54a8e889d98763a8c657d4866f478df6e6e57d80a` |
| `campaign.json.gz` | `e31b9b4bc1f411dfdc1057cee8bb9255fa62013ad3fabf0717b5fbe9545bb20d` |
| `driver.sha256` (the two campaign files as run) | `f900477f22e0a0f9a74d76294fd028b943fbcb11a7c165f154c96337939c0c19` |
