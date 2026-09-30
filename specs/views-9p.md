# A bounded9P2000 view of a committed store

HST-043 / PRF-1177 / SCN-1064. Selected interface: read-only base9P2000,
loopback. Current realization is additive source work, not an activated server.
The retired `tools/fn9p.py`, `host/ninep-host.lisp` and old whole-view adapter
are not current implementations or evidence.

## The tree

```
/status
/groups/<group>/<localnumber>
/by-id/<message-id-octets-hex>
```

ACL2 owns configured group names, membership, local number rendering,
Message-ID hex encoding, qids, lengths, lookup outcomes and reply bytes.
Local numbers remain local to the selected committed group/number source.
An ordinal0 lookup is valid, distinct from missing. The two article paths
select the same article through the registered immutable publication.

Article reads contain exact stored source octets: no NNTP status line,
dot-stuffing or terminating dot. An unsupported stored framing degrades only
that article: directory membership remains visible, stat length0 and open
refuses with the corresponding stored-framing reason. There is no overview,
header index, wildmat, NEWNEWS or history projection until its actual shared
core source exists.

## Protocol and bounds

Follow base [9P intro(5)](https://9p.io/magic/man2html/5/0intro),
[version(5)](https://9p.io/magic/man2html/5/version),
[walk(5)](https://9p.io/magic/man2html/5/walk),
[read(5)](https://9p.io/magic/man2html/5/read) and
[stat(5)](https://9p.io/magic/man2html/5/stat).
Integers are little-endian. The framing header is size4/type1/tag2 and size
includes itself. Strings carry unsigned16 byte lengths. Version uses NOTAG;
all other outstanding tags are unique. Twalk's MAXWELEM16 is a protocol limit,
not a limit on path depth across requests. Rstat contains the outer stat
length and the directory entry's inner size field.

Version, Attach, Walk, read-only Open, Read, Clunk, Stat and Flush are the
selected operations. No writes: Create, Write, Remove, Wstat and modes that
request mutation are refused. Auth receives the base protocol error for no
authentication required. No9P2000.u or9P2000.L extension semantics; compatible
version negotiation offers base9P2000, unknown versions receive unknown.
No per-user access policy is invented. Bind loopback; reachable clients can
read the selected projection.

Message size is negotiated within the operator's supported, representable
profile. Check the peer-declared frame size before allocating or reading its
body. `fn-9p-header-at` performs seven concrete-buffer reads and has a literal
wire-reference theorem; it does not assert that a body is already present.
Each parser/emitter/provider action has a bounded scheduling quantum and an
issued allocation/read grant. Exhaustion yields without truncating a name,
article or directory. No whole-store heap snapshot, decimal-octet bridge or
arbitrary whole-view/article ceiling is part of this realization.

Directory Read emits integral stat entries. Offset is zero or the previous
page's offset plus its returned length; other seeks refuse. A retained cursor
makes offsets stable. The host does not reconstruct or sort a group-wide
listing per request.

## Immutable committed capture and custody

Attach must obtain an actual issued registered committed publication and a
mount-lifetime source pin. Pub19's committed C/F/V, tableID, rowID, numberID,
arena incarnation and prefix stay distinct. Registration, a source-shaped
host tuple or latest READY pointer is not durable capture authority. A missing
installed constructor/runtime/profile/source relation is unavailable.

The mount retains one immutable generation for its lifetime. Later commits
remain invisible; remount acquires a newer capture. Each fid derives its
selection from that same source. A writer is not blocked by materializing or
holding a whole-store lock for the mount lifetime.

Read uses the actual retained selected-query/QPG source byte and length
interfaces. Each outstanding physical read retains its issued authority and
source aliases until its definite completion. Flush cancels reply publication;
it does not infer physical completion or release a worker's grant. Clunk,
disconnect and Version reset release mount/fid ownership only after dependent
borrowed reads and query/response/worker aliases have actually settled.

Current provider ingredients are guarded grouped number lookup,
registered row read and selected-query/QPG byte interfaces. Operational mount
issuance, rendered group-name/member enumeration, durable source correspondence and
native registration remain open shared integration subjects. The protocol
machine must not replace them with a host callback or flat catalog.

## Evidence scope

The concrete header and resumable body-field codecs, version negotiation and
exact reply bytes have normal narrow source certificates. A bounded group-trie
walker preserves the ordered directory while borrowing persistent bit paths
and actual group values; it does not yet render names/stat entries or issue a
mount. Full parser refinement, fid state, actual provider composition and
native client scenarios remain open; this is not a served mount claim.
SCN-1064 requires an external client on a scratch store, tiny message sizes,
exact binary/dotted/long article ranges through both paths, paged directories,
commit invisibility, reclamation while source is held, readonly refusals,
partial walks and Flush/disconnect cleanup. Source, committed proof manifests,
qualified image and deployment remain separate coordinates.
