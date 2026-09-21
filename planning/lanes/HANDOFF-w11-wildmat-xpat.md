# w11/wildmat-xpat: OB-XPAT-SPACE closed, and the three invariants books it re-opened

Branch `w11/wildmat-xpat`, worktree `build/lanes/w11-wildmat-xpat`, from dev
`dbf1aa7`, merged with dev `e4fb8bc`. Decision **D19** in
`planning/decisions.md`.

## The defect and the decision

RFC 2980 §2.9 joins XPAT's trailing arguments "separated by a single space to
form one complete pattern", so **every multi-token XPAT pattern carries an
SP**. `fn-nntp-xpat-response` handed the join to `fn-wildmat-parse`, which
enforces RFC 3977 §4.1's `<wildmat-exact>`; SP is %x20 and is excluded; so
every one of them was `501` and `fn-nntp-xpat-join`'s multi-token branch could
never produce a match.

**Which of the three the 501 was: a local policy choice, and an unintended
one.** §2.9.1's response list is `221 / 430 / 502` and has no 501 in it. §4.1's
grammar governs `newsgroup-name = 1*wildmat-exact` (§9.8) and §4.1 says why its
exclusions are acceptable — "This should not be a problem, since these
characters cannot occur in newsgroup names, which is the only current use of
wildmats" — which is exactly the assumption XPAT breaks. So the 501 was not an
RFC requirement and not a guarantee anyone chose; it was the consequence of
reusing the newsgroup-name grammar in a position the RFC did not put it in. It
is withdrawn rather than defended.

**§4.3 licenses the cure and fn discharges its proviso rather than asserting
it**: "An NNTP server or extension MAY extend the syntax or semantics of
wildmats provided that all wildmats that meet the requirements of Section 4.1
have the meaning ascribed to them by Section 4.2."

**Selected: a second character profile over ONE parser.** The scanner scans
the wider set; `fn-wildmat-parse` recovers §4.1 with a precheck
(`fn-wildmat-rfc3977-codepointsp`) on the decoded code points before scanning.
No arity changes, so no statement in `books/wildmat-matcher-invariants` moved
and the twelve subgoal hints of `fn-wm-parse-one-success-pattern-listp` did not
move either. The alternatives cost more: a separate parser duplicates that
twelve-hint induction, and a profile parameter changes the arity every theorem
in two books mentions. Measured: all five wildmat roots certified on the first
attempt after the predicate rename.

**The profile, in one rule.** A pattern is a fragment of a command line, so
every printable US-ASCII character, SP, and every UTF-8 non-ASCII character is
a literal, less the four metacharacters `!` `*` `,` `?`. Controls and DEL stay
out, as they are out of §4.1. Against `<wildmat-exact>` that is exactly four
more code points, `%x20 SP` `%x5B [` `%x5C \` `%x5D ]`, and
`fn-wildmat-text-exactp-adds-exactly-four-code-points` proves it is no larger.

**The cost, named.** §4.1 omitted `[`, `\` and `]` because "A future extension
to this specification may provide semantics for these characters". Reading them
as literals in the **header** profile spends that reserved syntax there; the
newsgroup-name profile keeps all three reserved, and §4.1 conformance is
untouched either way because no §4.1 wildmat can contain them. Spent knowingly:
`[PATCH]` in a Subject is the ordinary case and refusing it is the same defect
as refusing SP.

## The three invariants books, enumerated, with a verdict each

Nothing was weakened and nothing was removed. Where a lemma's *subject* became
the wider scanner, the §4.1-restricted statement is proved beside it.

### `books/wildmat-utf8-invariants.lisp` (31 theorems; 12 touched)

| form | verdict |
| --- | --- |
| `fn-wildmat-unicode-scalarp-implies-codepointp`, the six `fn-wildmat-utf8-next-*`, `fn-wildmat-octet-listp-implies-true-listp`, `fn-wildmat-codepoint-listp-{revappend,reverse}`, `fn-wildmat-len-{revappend,reverse}`, the four `fn-wildmat-decode*` | UNTOUCHED. UTF-8 decoding is below the grammar and the character set does not reach it. |
| `fn-wildmat-items-p-revappend`, `fn-wildmat-items-p-reverse` | KEPT VERBATIM. No longer serve the scanner; they now serve the §4.1 preservation proof. |
| `fn-wildmat-text-items-p-revappend`, `-reverse` | ADDED, the scanner's versions. |
| `fn-wildmat-scan-end-success-items`, `fn-wildmat-scan-more-success-items` | RESTATED over `fn-wildmat-text-items-p`. The subject function now scans the wider set, so this is the true statement about it; the §4.1-restricted one is `fn-wm-scan-{end,more}-rfc3977-items` in the parser book. |
| `-end-success-items-consp`, `-more-success-items-consp` | STRENGTHENED. Conclusion (`consp`) unchanged; the `items-rev` hypothesis is now the weaker `fn-wildmat-text-items-p`. |
| `-end-success-items-valid`, `-more-success-items-valid` | RESTATED, as their parents. |
| `fn-wildmat-scan-nil-end-items-consp`, `fn-wildmat-scan-nil-more-items-consp` | STATEMENT UNCHANGED (no item predicate occurs in them); hint vocabulary only. |
| `fn-wildmat-scan-nil-end-items-valid`, `fn-wildmat-scan-nil-more-items-valid` | RESTATED, as their parents. |

### `books/wildmat-parser-invariants.lisp` (9 theorems before; 17 after)

| form | verdict |
| --- | --- |
| `fn-wm-scan-end-nil-items`, `fn-wm-scan-more-nil-items`, `-valid` ×2 | RESTATED over `fn-wildmat-text-items-p`, as above. |
| `fn-wm-scan-end-nil-items-consp`, `fn-wm-scan-more-nil-items-consp` | STATEMENT UNCHANGED. |
| `fn-wm-scan-more-excludes-end` | UNTOUCHED. No character-set dependence; a scan result is `:more` or `:end`, never both. |
| `fn-wm-parse-one-success-pattern-listp` | STATEMENT UNCHANGED, and its twelve subgoal hints unchanged. `fn-wildmat-pattern-listp` is a **record shape** recognizer and was widened in place, so the theorem now says the same words about the wider shape. |
| `fn-wildmat-successful-parse-parsedp` | STATEMENT UNCHANGED, same reason. |
| `fn-wildmat-parse-yields-rfc3977-patterns` | **ADDED, and it is the content this book had before D19**: a successful `fn-wildmat-parse` yields a nonempty list of patterns every item of which is an RFC 3977 §4.1 `<wildmat-item>`. This is why nothing is lost by widening the shape recognizers. |
| `fn-wm-rfc3977-codepointsp-cdr`, `fn-wm-scan-rest-rfc3977`, `fn-wm-scan-{end,more}-rfc3977-items`, `fn-wm-scan-nil-{end,more}-rfc3977-items`, `fn-wm-parse-one-rfc3977-pattern-listp` | ADDED, the chain under it. |

### `books/wildmat-matcher-invariants.lisp` (18 theorems; 0 statements changed)

| form | verdict |
| --- | --- |
| `fn-wm-reference` (the independent backtracking reference, a `defun`) | CHANGED: its literal test reads `fn-wildmat-text-exactp`, in lockstep with `fn-wildmat-item-character-matchp`. The two must move together or the correspondence is about a matcher fn does not run. |
| `fn-wm-reference-boolean`, `-row-consp`, `-row-car`, `-row-length`, `-row-boolean`, `fn-wm-character-{aux-,}correspondence`, `fn-wm-star-{aux-,}correspondence`, `fn-wm-pattern-row-correspondence`, `fn-wm-empty-pattern-row-tail`, `fn-wm-initial-row-correspondence`, `fn-wm-last-reference-row`, `fn-wildmat-pattern-matchp-is-anchored-reference`, `fn-wildmat-matcher-row-{length,boolean}` | STATEMENTS UNCHANGED and reproved unchanged. Only `fn-wm-character-aux-correspondence`'s hint moved, from `(disable fn-wildmat-exactp)` to `(disable fn-wildmat-text-exactp)` — it treated the set opaquely already, which is why the fan did not arrive. |
| `fn-wm-selection-correspondence`, `fn-wildmat-rightmost-match-is-last-reference-match`, `fn-wildmat-match-codepoints-is-reference-decision` | STATEMENTS UNCHANGED and **STRICTLY STRONGER**: they hypothesise `fn-wildmat-pattern-listp`, which now admits header-profile patterns. Before D19 they said nothing about a pattern containing SP. |

**The fan did not arrive.** The prediction in `HANDOFF-w10-nntp-tests.md` was
that fixing this re-opens three invariants books; it does, but the cost was a
predicate rename in two of them and a hint vocabulary change in the third. The
precheck design is why: the scanner's recursion, the induction scheme and the
case split are the same functions in the same shapes, so no subgoal name moved.

**`books/wildmat-work.lisp` is a fourth dependant** and was not in the
prediction: it mirrors `fn-wildmat-item-character-matchp` for work counting at
`:47`. Its statements are unchanged and it certified unchanged.

## What is new in `books/wildmat.lisp`

`fn-wildmat-text-exactp` / `-text-itemp` / `-text-items-p`;
`fn-wildmat-rfc3977-codepointp` / `-codepointsp`; `fn-wildmat-rfc3977-patternp`
/ `-pattern-listp`; `fn-wildmat-parse-text`. `fn-wildmat-exactp`,
`fn-wildmat-itemp` and `fn-wildmat-items-p` are UNCHANGED and remain the §4.1
citation. `fn-wildmat-patternp` / `-pattern-listp` / `-parsedp` are widened in
place (record shape, not conformance). Keystones:
`fn-wildmat-item-character-matchp-is-rfc3977-on-rfc3977-items` (the previous
body verbatim as its right-hand side),
`fn-wildmat-text-exactp-adds-exactly-four-code-points`,
`fn-wildmat-text-exactp-is-strictly-wider`, and the three inclusions.
Registered in `planning/proof-events.json` under PRF-006 (the conservation
keystone) and PRF-016 (the §4.1 result shape).

The book is now 820 lines, over the 800-line split guidance. Its seams are
marked; splitting it is a separate packet and is NOT done here.

## The second divergence, confirmed undisturbed

fn reads `,` in an XPAT pattern as wildmat alternation where INN's
`uwildmat_simple` reads it as a literal, and §2.9's "At least one pattern in
wildmat must be specified" is on fn's side. **D19 cannot touch it**: 44 is an
exact item in neither profile, so the comma is the separator in both.
Measured after the change: `fn-wildmat-parse-text '(42 84 44 42 116 42)`
(`*T,*t*`) is two positive constituents, and it matches `"Test"`. The assertion
that pins it is unchanged.

## Open

- **The wide certification of the merged tree.** The hbox run below was
  submitted from the lane tree before dev `e4fb8bc` was merged in; dev changed
  `books/owner.lisp`, `books/owner-invariants.lisp`, `books/nntp-post.lisp`
  and two test books in the meantime. The wildmat and XPAT results stand on
  their own sources, and the merged tree needs one more narrow run over the
  same roots with hbox's now-warm cache.
- No socket witness of a matching multi-token XPAT. `tests/test_reader.py`'s
  seed article has no header value containing an SP, and changing it moves the
  byte counts of six other transcripts. The matching case is end-to-end in
  `tests/acl2/nntp-legacy-tests.lisp` over a second one-article archive whose
  Subject is a phrase, through the same acceptance definitions.
