# Bounded article syntax parser

Status: executable local syntax profile.  This specification defines a bounded
view over received article octets.  It is not an RFC 5536 article validator, an
RFC 5537 injecting agent, a posting policy, or a native fn article envelope.

## Input and bounds

`fn-article-parse` accepts one proper list of octets with at most 32,768
octets.  It checks that bound before octet traversal.  The parser then applies
these local resource limits:

| Limit | Value | Status |
| --- | ---: | --- |
| complete source | 32,768 octets | local policy |
| header section before the blank separator | 8,192 octets | local policy |
| physical header line excluding CRLF | 998 octets | local policy, aligned with RFC 5536 §2.2's generation limit |
| physical header lines | 128 | local policy |
| header fields | 64 | local policy |

The input uses CRLF line framing throughout.  A bare CR or bare LF anywhere in
the source is an `:invalid-header` syntax error.  Body bytes otherwise remain
opaque: bytes such as NUL, 0xff, non-UTF-8 sequences, and text that looks like
Lisp are retained exactly and are neither decoded nor evaluated.  This
strict-CRLF transport rule is a local parser policy, not a MIME or body-content
validation claim.

The first empty CRLF-framed line terminates the header section.  Absence of that
separator is `:missing-separator`; invalid header syntax and mixed line endings
are `:invalid-header`; a source, header, line, field, or physical-line limit is
`:limit`.  Parsing never interns a header name or invokes the Lisp reader.

## Header syntax and retained views

Header fields follow the RFC 5536 §2.2/RFC 5322 field-name shape used here:

```text
field       = field-name ":" WSP field-body *(CRLF WSP field-body)
field-name  = 1*ftext
ftext       = %d33-57 / %d59-126
WSP         = SP / HTAB
field-body  = *(WSP / VCHAR), containing at least one VCHAR
```

Every initial field line therefore has a colon followed by WSP, and every
continuation starts with WSP.  Header bytes are US-ASCII only: each is SP, HTAB,
or VCHAR.  A continuation without a preceding field, an empty body, a control
byte, a non-ASCII byte, or a malformed name is rejected.  This is deliberately
stricter than RFC 5536's permission for receivers to accept a missing post-colon
space; the strict requirement is local policy.  The parser admits the full
`ftext` octet domain for unknown field names, rather than an identifier subset.

The parsed article view exposes `source`, `header`, `body`, and `fields`.
`header` is the exact pre-separator header octets, preserving original field
order and folding; `body` is the exact post-separator octets; and `source` is
their exact `header ++ CRLF ++ body` recomposition.  Each field view is
`(raw-lines lower-name unfolded-value)`: `raw-lines` keeps every
physical line without its CRLF, `lower-name` ASCII-lowercases only A--Z, and
`unfolded-value` removes each folding CRLF while retaining its continuation WSP.
Unknown and duplicate fields remain separate field views in source order.

`fn-article-get-header` returns the first matching view; `fn-article-get-headers`
returns all matching views.  Matching uses the lowercased ftext octet name only.
Neither helper gives a semantic meaning to a field.

## Deliberate exclusions

RFC 5536 §2.2 says compliant generation has a space after a colon, uses
US-ASCII headers, and constrains nonempty folded body lines; §2.3 discusses MIME
conformance.  RFC 5537 §2 transports article octets unchanged, and §3.4.1 says
a proto-article may omit Message-ID, Date, and Path while forbidding
Injection-Info and Xref.  This parser implements only the bounded byte/header
syntax above.  It does not check required fields, duplicate requirements,
Message-ID/Date/address/Newsgroups grammar, MIME semantics, proto-article
trace-field restrictions, injection, authorization, provenance, or durable
acceptance.  Those remain separate parser, policy, and node work.

The invariant book proves `fn-article-successful-parse-preserves-source`: every
successful parse reconstructs its exact arbitrary input. Scanner partition and
parser reconstruction lemmas establish this by induction, beyond the constructor
relation `source = header ++ CRLF ++ body`. The test suite also checks mixed
folded/binary inputs and rejection boundaries. The
[integrated evidence](../tests/evidence/2026-09-18-articles.md) records certification.
The [property book](../books/article-properties.lisp) additionally proves that
successful parsing establishes `fn-article-syntax-p`, source/body length at most
32,768, header length at most 8,192 and at most 64 fields, from the sole success
hypothesis. These results are in the [assurance checkpoint](../tests/evidence/2026-09-18-assurance.md).
Full parser work/allocation proofs and other semantic fields remain open.
None of these properties establishes full RFC article validity.
