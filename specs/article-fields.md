# Semantic article fields

Status: executable bounded semantic extraction over the successful views from
`fn-article-parse`. This is a narrow preparation step for a future injector. It
does not validate every RFC 5536 mandatory field, make an article injectable,
choose a native envelope, generate dates/identifiers/trace fields, or make a
durable admission decision.

## Input boundary and preservation

`books/article-fields.lisp` accepts an article view only after a successful
`fn-article-parse`; callers must pass `fn-article-result-article` from such a
result. The syntax parser remains the sole source parser and supplies its
32,768-octet source, 16,384-octet header, 256-line, and 64-field local bounds.
This book does not reparse source bytes, invoke the Lisp reader, intern names,
or use host text/regular-expression processing.

The input article's raw header, source, field order, raw field lines, and
unfolded values are retained by the article view. Semantic results return the
participating field view, so later injection/provenance code can retain the
original bytes. Unknown fields and duplicate fields are never deleted or
rewritten by this layer.

The standalone `fn-af-message-idp` applies the RFC 5536 250-octet maximum
before octet traversal. `fn-af-newsgroup-list-parse` similarly preflights its
value against its own narrower 8,192-octet field limit. These are bounded
octet functions, independent of host character encoding.

## Message-ID

RFC 5536 §3.1.3 defines:

```text
msg-id      = "<" id-left "@" id-right ">"
id-left     = dot-atom-text
id-right    = dot-atom-text / no-fold-literal
```

with a maximum of 250 octets including angle brackets. The implementation uses
RFC 5322 `atext`/`dot-atom-text`, RFC 5536 `mdtext` for bracketed literals, and
requires the field's exact `Message-ID:` grammar: one initial SP after the
colon, optional outer SP/HTAB, then one valid identifier. Its field grammar has
`*WSP`, not `FWS`, so a folded Message-ID field is rejected. This is the RFC
form supported here, not an added fn restriction.

`fn-af-message-id-status` returns `(:missing)`, `(:duplicate fields)`,
`(:invalid field)`, or `(:single identifier field)`. A semantic consumer must
accept only `:single`; extraction does not select a first duplicate. The exact
identifier is an octet list with no lowercasing, quote processing, or domain
interpretation. `fn-af-message-id-equalp` is exact octet equality when both
operands are valid, as required by RFC 3977 Appendix A.2 and OBJ-002.

## Newsgroups

RFC 5536 §3.1.4 defines a comma-separated ordered list of names made of
nonempty dot-separated components. Component bytes are ASCII letters, digits,
`+`, `-`, and `_`. `fn-af-newsgroups-status` has the same missing/duplicate/
invalid/single classification as Message-ID; a successful result returns the
ordered original-octet names and the source field view. It accepts optional
SP/HTAB around commas, including folding represented by the article parser's
unfolded value, as RFC 5536 requires receivers to accept optional FWS. It does
not lowercase names, remove duplicate names, interpret reserved names, or check
the configured group set. Those are policy/admission questions.

The existing article syntax parser permits a post-colon tab as its local broad
header syntax. This semantic layer requires the RFC-defined initial SP for both
supported field forms; that is a stricter fn acceptance policy for these two
semantic fields, documented here rather than silently normalized.

## Proto-article routing subset

`fn-af-proto-article-check` implements only the relevant RFC 5537 §3.4.1
conditions: Newsgroups must be one valid, nonduplicate field; a Message-ID may
be absent but, if present, must be one valid field; and Injection-Info and Xref
must be absent. It returns `(:ok message-id-or-nil ordered-groups message-id-
field-or-nil newsgroups-field)` or a tagged error. Missing Message-ID is left
for a later injector, which must generate it under a separately selected policy.

This is not a claim that its input is a complete proto-article. `From`,
`Subject`, `Date`, `Path` (including `POSTED`), MIME, moderation, authorization,
configured-group admission, duplicate history, local number allocation, and
durable transaction effects remain outside this book. In particular, the
all-configured-groups atomic admission rule stays node work, and no source or
identifier is globally normalized or merged.
