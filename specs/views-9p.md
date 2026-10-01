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

For this immutable projection, qid.path identifies exported nodes within the
captured filesystem instance. Multiple attaches on the same versioned
connection share its retained source and qid registry. The core assigns
injective unsigned64 path numbers: repeated selection of the same exported
node returns the same number; different directories and group-specific
virtual files have different keys. No hash or truncation derives these IDs.
An independent remount exports a new filesystem instance; persistence across
independent mounts or process restart is not an fn guarantee. Exhausting the
supported registry/codec representation refuses admission and retains work,
without truncating stored articles or names. This is the local realization of
the qid requirements in [intro(5)](https://9p.io/magic/man2html/5/intro).

Per [flush(5)](https://9p.io/magic/man2html/5/flush), Rflush releases the old
wire tag. A cancelled physical request therefore remains in its own slot
while a new request may use that tag. Its exact issued receipt still governs
return; an old callback cannot clear a reused slot or decrement the new
borrow. A partially successful Twalk leaves both fid bindings unchanged;
only a complete walk installs newfid, as required by
[walk(5)](https://9p.io/magic/man2html/5/walk).

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

The actual `fn-ninep-refusal-reply` delegates to guarded `fn-9p-refusal-reply`: core emits fixed Rerror octets for read-only, no-authentication and mount-unavailable outcomes. Tag must be below NOTAG and the complete reply must fit the negotiated msize; otherwise the core directs close. Reply metadata/text is at most26 octets, independent of stored article size. This emitter does not decide mount authorization or install a listener. Native caller allocation and runtime funding remain open.

The concrete `fn-ninep-transport` owns its framing/parser/reply cursor and
internally provisioned input quantum. `fn-ninep-transport-step` returns a
receive count bounded by that quantum, and does not call body parsing before
all declared bytes are observed. Its ordinary host correspondence includes
all concrete outputs and unchanged STATE. Version reset invokes actual bounded
draining and waits for the real mount return. Current reply return clears the
input once; a duplicate return in another phase refuses unchanged. Normal
035212 certifies this source and host boundary; normal040010 certifies six
complete internal wire/custody witnesses (PRF-1202). The 13.315-second transport
proof is a separate D26 cost defect. The internal native I/O adapter is
source-only and still lacks the genuine per-action admission composition;
public start refuses before constructors. These results do not fulfill the
external-client SCN-1064 or activate a listener.


The registered mount getter `fn-ninep-mounted-source` reads the actual held
MIO generation row and requires its pin, token and retained live/retiring
phase. It returns that row's Pub19, including the immutable visibility
bucket root. A newer CURRENT pointer and an independently retained session
copy cannot substitute for it. Group enumeration advances one bucket per
action; group lookup compares one source name byte per action. The actual
owner visibility publication carries visible buckets; completeness for
configured empty groups remains a separate source requirement (PRF-1206).

Mount issue, unpinned abort and definitive return use the split SAMEpool
DATA6 counter transaction. MODE intent/recovery encloses actual session
stores and, on return, the real generation drop. Modes restore last.
Unfinished intent refuses new mount entry; unknown pin/drop cuts retain
source and debit. Complete internal fixtures are source-qualified, without
normal certification of the modern mount include closure.

The stat stream follows [stat(5)](https://9p.io/magic/man2html/5/stat)'s inner
size and outer Rstat size, and [read(5)](https://9p.io/magic/man2html/5/read)'s
integral directory entries. One action appends one actual output octet.
Zero timestamps and empty uid/gid/muid are immutable presentation policy;
readonly permissions are 0555 on directories and 0444 on files. An entry
that cannot fit the negotiated message or Tread count refuses without
partial entry or name truncation; the small-count refusal is fn policy.
A completion-position mutation cannot mark an un-emitted stat body ready.
This codec is PRF-1207, separate from real mounted source/QID derivation and
operation funding. Full provider, native listener and external-client
SCN-1064 remain open.
