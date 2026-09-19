# Reference map

The repository began with the RFC copies listed below. Preserve them as supplied.
The linked official documents provide stable section references. Before an
interoperability claim, review applicable updates and errata and record the
specific audited profile. This list is a reading map, not that audit.

| Source | Use |
| --- | --- |
| [RFC 3977](https://www.rfc-editor.org/rfc/rfc3977.html), [local copy](../rfc3977.txt) | NNTP framing, capabilities, commands, cursor semantics; §§3, 5–8, Appendix B |
| [RFC 5536](https://www.rfc-editor.org/rfc/rfc5536.html), [local copy](../rfc5536.txt) | Article format, Message-ID, required fields, MIME relationships |
| [RFC 5537](https://www.rfc-editor.org/rfc/rfc5537.html), [local copy](../rfc5537.txt) | Injection, trace headers, history, duplicate suppression; §§3.2–3.5 |
| [RFC 2980](../rfc2980.txt) | Older extensions; consult current replacements before adopting behavior |
| [RFC 4643](../rfc4643.txt) | NNTP authentication |
| [RFC 4644](../rfc4644.txt) | Streaming feeds, a later capability |
| [RFC 6048](../rfc6048.txt) | Additional LIST facilities |
| [RFC 8054](../rfc8054.txt) | Compression, a later capability |
| [RFC 4707](../rfc4707.txt) | News administration; outside the first profile |
| [RFC 8315](../rfc8315.txt) | Cancel locks; relevant to later cancellation policy |
| [tin reference collection](https://www.tin.org/docs.html) | Discovery index; not itself a conformance specification |
| [RFC 5325](https://www.rfc-editor.org/rfc/rfc5325.html) | LTP motivation and long-delay link assumptions |
| [RFC 5326](https://www.rfc-editor.org/rfc/rfc5326.html) | LTP specification, reliable red data and link session semantics |
| [RFC 9171](https://www.rfc-editor.org/rfc/rfc9171.html), [local copy](../rfc9171.txt) | BPv7 bundle format and processing; §4.2 data structures, §4.3.1 primary block, §4.4 extension blocks, §5.5 expiration, §5.8–5.9 fragmentation and reassembly. Application acceptance remains separate |
| [RFC 9172](https://www.rfc-editor.org/rfc/rfc9172.html), [local copy](../rfc9172.txt) | BPSec; Block Integrity Blocks are the precondition RFC 9171 §4.3.1 attaches to a zero CRC type. Transport protection is distinct from portable application statements |
| [RFC 9173](https://www.rfc-editor.org/rfc/rfc9173.html), [local copy](../rfc9173.txt) | BPSec default security contexts; not selected, and no fn book depends on it |
| [RFC 8949](https://www.rfc-editor.org/rfc/rfc8949.html) | CBOR, especially deterministic profiles in §4.2 |
| [RFC 9052](https://www.rfc-editor.org/rfc/rfc9052.html) | COSE structures, a candidate for signed-statement encoding |
| [RFC 9420](https://www.rfc-editor.org/rfc/rfc9420.html) | MLS, candidate group encryption; no selection implied |
| [RFC 9750](https://www.rfc-editor.org/rfc/rfc9750.html) | MLS architecture, particularly §5.2's commit/epoch ordering |
| [Megolm specification](https://spec.matrix.org/unstable/olm-megolm/megolm/) | Group-ratchet tradeoffs; linked document is the unstable specification |
| [ACL2 guard introduction](https://acl2.org/doc/index-seo.php?xkey=ACL2____GUARD-INTRODUCTION) | Conditions relating logical and raw Lisp execution |
| [ACL2 abstract stobjs](https://acl2.org/doc/index-seo.php?xkey=ACL2____DEFABSSTOBJ) | Logical/concrete correspondence and efficient execution |
| [SQLite atomic commit analysis](https://www.sqlite.org/atomiccommit.html) | Reference on filesystem assumptions and barrier ordering, not a chosen backend |
| [NASA DTN overview](https://www.nasa.gov/reference/delay-disruption-tolerant-networking-overview/) | Context and integration terminology |

Follow references from the core article RFCs to their normative dependencies
when implementing their parsers, particularly RFC 5322, MIME, ABNF, and wildmat.
Do not mistake this locally supplied collection for a complete dependency set.

BPv7 does not make a generic transport/status acknowledgment into fn's durable
retention promise. In particular, do not import older Bundle Protocol custody
semantics by assumption; RFC 9171 Appendix A describes changes from RFC 5050.
