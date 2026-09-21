# RFC 3977 wildmat

Status: executable bounded matching component, integrated into the experimental
reader's `LIST ACTIVE` and `LIST NEWSGROUPS` optional-wildmat paths.  This does
not advertise READER or LIST capability bundles, and it is not a complete NNTP
conformance claim.

## Contract

`books/wildmat.lisp` accepts a wildmat and a target as ACL2 lists of octets.
`fn-wildmat-parse` returns `(:ok patterns)` or `(:error reason)`.  Each parsed
pattern is `(:positive items)` or `(:negative items)`, where `42` and `63`
represent `*` and `?`; all other items are decoded Unicode scalar values.
`fn-wildmat-match` parses and evaluates source plus target and returns `(:ok
boolean)` or an error.  `fn-wildmat-match-parsed` evaluates a successful parser
value against a separately supplied target.  Its `patterns` argument has the
precondition that it is the value from a successful `fn-wildmat-parse` call;
it is an internal reuse API, not an external unbounded parsed-form ingestion
API.  Callers receiving untrusted pattern octets use `fn-wildmat-match` or
`fn-wildmat-parse` first.

RFC 3977 §4.1 is the grammar authority:

```text
wildmat = wildmat-pattern *("," ["!"] wildmat-pattern)
wildmat-pattern = 1*wildmat-item
```

The implemented base grammar accepts only exact characters plus `*` and `?`.
It rejects empty patterns, `!` outside the optional post-comma position, commas
that do not separate nonempty patterns, and the reserved ASCII punctuation
`!`, `,`, `[`, `\`, and `]` as exact items.  There are no bracket-set,
backslash-quoting, or other §4.3 extensions.

## Two character profiles, one grammar (decision D19)

§4.1's exclusions are justified in the RFC itself by the use it had in mind:
"This should not be a problem, since these characters cannot occur in
newsgroup names, which is the only current use of wildmats."  RFC 2980 §2.9's
XPAT is the other use.  It matches a **header value**, which is prose, which
contains SP, and whose pattern §2.9 builds by joining the trailing command
arguments "separated by a single space" — so every multi-token XPAT pattern
carries an SP that §4.1 excludes.  §4.3 permits the widening: "An NNTP server
or extension MAY extend the syntax or semantics of wildmats provided that all
wildmats that meet the requirements of Section 4.1 have the meaning ascribed
to them by Section 4.2."

The grammar's structure — comma alternation, post-comma `!`, `*`, `?` — is one
implementation.  Only the literal set is profiled.

| | newsgroup-name profile | header-value profile |
| --- | --- | --- |
| literal set | `fn-wildmat-exactp`, RFC 3977 §4.1 `<wildmat-exact>` verbatim | `fn-wildmat-text-exactp` |
| entry point | `fn-wildmat-parse` | `fn-wildmat-parse-text` |
| callers | `LIST ACTIVE`, `LIST NEWSGROUPS`, `LIST ACTIVE.TIMES`, peer feed patterns, owner feed patterns | `XPAT` only |

The header-value profile is one rule: a pattern is a fragment of a command
line, so every printable US-ASCII character, SP, and every UTF-8 non-ASCII
character is a literal, less the four wildmat metacharacters `!` `*` `,` `?`.
Controls and DEL are excluded from both.  Against `<wildmat-exact>` that is
exactly four more code points — `%x20 SP`, `%x5B [`, `%x5C \`, `%x5D ]` —
and `fn-wildmat-text-exactp-adds-exactly-four-code-points` proves the
difference is no larger.  §4.1 reserved `[`, `\` and `]` for a possible future
extension; reading them as literals in the header profile spends that reserved
syntax there, which D19 records as a knowing local cost.

**How §4.3's proviso is discharged rather than asserted.** The scanner scans
the wider set and `fn-wildmat-parse` recovers §4.1 with a precheck
(`fn-wildmat-rfc3977-codepointsp`) on the decoded code points, so it accepts
and refuses exactly the octet lists it accepted and refused before the second
profile existed, with the same `:error` reason.
`fn-wildmat-parse-yields-rfc3977-patterns` is the §4.1 result shape it still
produces.  The matcher's literal test reads the wider set — that is what makes
a matched SP a match at all — and
`fn-wildmat-item-character-matchp-is-rfc3977-on-rfc3977-items` states that on
every §4.1 item it computes what it computed before, with the previous body
verbatim as the right-hand side.

`fn-wildmat-patternp`, `fn-wildmat-pattern-listp` and `fn-wildmat-parsedp`
recognize a pattern *record*, not grammar conformance, and carry the wider
item set so that one matcher serves both profiles; every theorem that
hypothesises one is thereby stronger than before.  The §4.1-profiled record
shape is `fn-wildmat-rfc3977-pattern-listp`.

RFC 3977 §4.2 controls semantics.  Each constituent pattern is anchored to the
whole target.  `?` matches one decoded Unicode scalar value and `*` matches zero
or more scalar values.  The rightmost pattern that matches decides inclusion:
a positive rightmost pattern includes, a negative one excludes, and no matching
pattern excludes.  A multibyte UTF-8 character therefore satisfies one `?`,
and `*` cannot consume part of its byte sequence.

## UTF-8 and bounds

The local fn profile applies the RFC 3977 §3.1 argument limit of 497 octets to
both wildmat source and target.  Before traversing octet values, the component
preflights the proper-list shape through 498 cells at most.  It then requires
every value to be an octet and decodes only RFC 3629 forms incorporated by RFC
3977 §9: two-byte leading bytes C2–DF; the restricted three-byte E0/ED cases;
and the restricted four-byte F0/F4 cases.  It rejects malformed continuation,
truncated, overlong, surrogate, and greater-than-U+10FFFF sequences.  This is a
stronger local rejection policy than RFC 3977 §12.5's permitted recovery
choices; it gives callers an explicit `:malformed-utf8` result rather than
silently substituting a character.

The matcher keeps a dynamic-programming reachability row for each pattern item.
For a pattern with `m` decoded items and a target with `n` decoded characters,
it uses O(m*n) list work and O(n) row space per item.  The fixed octet cap bounds
both dimensions.  It does not use exponential `*` backtracking, the Lisp
reader, evaluation, symbols derived from input, or host string decoding.

RFC 3977 §3.1 says command lines that permit non-ASCII MUST NOT use U+FEFF BOM
and instead uses U+2060 Word Joiner for the Zero Width No-Break Space meaning.
That is an NNTP command-line boundary rule, not a transformation rule for §4
matching.  This generic component neither removes nor introduces a BOM: valid
UTF-8 U+FEFF is an exact non-ASCII wildcard item or target character.  The
experimental NNTP command boundary rejects a BOM before tokenizing and only
allows strict UTF-8 in the optional wildmat positions of `LIST ACTIVE` and
`LIST NEWSGROUPS`; command keywords and the profile's other legacy arguments
remain ASCII-validated.

## NNTP use

`books/nntp.lisp` parses a LIST wildmat once, then passes the successful parsed
value only to its internal configured-group filter.  It decodes each
projection-guarded group name and calls the ACL2 matcher; the host adapter does
not perform a regex, glob, or second matching implementation.  A matching
failure produces an ordinary empty 215 multiline response.  A malformed
wildmat or UTF-8 sequence returns 501 and does not change the selected group or
current article.  Bare `LIST`, `LIST ACTIVE`, and `LIST NEWSGROUPS` retain their
unfiltered behavior.

The command boundary enforces a maximum of 510 content octets before the wire
CRLF (RFC 3977 §3.1's 512-octet total) and 497 octets for each actual argument
token.  LIST and MODE have a second command keyword, so `ACTIVE` is excluded
from the `LIST ACTIVE wildmat` argument budget; a 497-octet wildmat therefore
fits the 511-octet framed command, while 498 reaches the generic matcher's
local limit.  The complete-line cap independently bounds separators and every
token.  The boundary preflights the bounded proper-list shape before token
traversal.  The loopback host uses a 510-octet `fn-wire` command-line limit so
physical framing has the same limit.
Known but unmaintained `ACTIVE.TIMES`, `DISTRIB.PATS`, `HEADERS`, and
`OVERVIEW.FMT` variants return 503 only for their RFC 3977 §9.6-valid arity;
unknown or malformed LIST variants return 501.

## Evidence and limits

`tests/acl2/wildmat-tests.lisp` covers the §4.4 examples, whole-character
multibyte `?`, negative/rightmost precedence, empty-star anchoring, grammar
rejections, reserved punctuation, profile boundary lengths, a many-star input,
and invalid UTF-8 classes.  It also covers the two profiles against each
other: the joined XPAT pattern `*T *t*` refused by `fn-wildmat-parse` and
parsed by `fn-wildmat-parse-text`, matching `T st` and not `Test` — the same
two answers INN 2.7.4's `uwildmat_simple` gives for the same pattern
([the measurement](../planning/evidence/inn-xpat-2026-09-20.md)) — a phrase
pattern over a phrase value, `[PATCH]`, and HTAB, DEL and a leading `!`
refused by both.  The UTF-8/parser/matcher invariant books now prove successful-step Unicode
scalar validity and strict progress, decoded output bounds, successful parser
recognition, and actual DP equivalence to independent anchored semantics with
rightmost precedence. These results are in the
[assurance checkpoint](../tests/evidence/2026-09-18-assurance.md). Complete
parser/matcher work bounds, guards and NNTP session refinement are separate work.

`tests/acl2/nntp-tests.lisp`, socket tests, and the recovered-store independent
`nntplib` probe add LIST filtering, malformed command, boundary, and session
preservation cases.  The current reader continues to advertise only
VERSION/IMPLEMENTATION.  Completing the reader profile, all LIST variants,
general parser work/resource proofs, and NNTP session refinement remains open.
