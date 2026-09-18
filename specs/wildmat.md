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
and invalid UTF-8 classes.  The book contains the small certified fact that a
star matches an empty target.  It does not yet prove the full parser grammar,
UTF-8 decoder, DP recurrence, resource bound, or NNTP session refinement.

`tests/acl2/nntp-tests.lisp`, socket tests, and the recovered-store independent
`nntplib` probe add LIST filtering, malformed command, boundary, and session
preservation cases.  The current reader continues to advertise only
VERSION/IMPLEMENTATION.  Completing the reader profile, all LIST variants,
general parser work/resource proofs, and NNTP session refinement remains open.
