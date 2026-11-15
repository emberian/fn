# CNS source-window packet

The OUTPUT source is connected through the actual CNS and CTL actors. It has
not been admitted or executed by ACL2 or a native node. The exact source,
changed files, unchanged foundation blobs and checks are in the adjacent receipt.

The base is delivery `86f919a16`. Current pool, columns, core, machine compiler,
machine arms, pinned I/O leaf and inbound stream helper remain byte-identical.
Apply the named OUTPUT hunks; never replace a newer whole `cns.lisp` file.
The independently staged precise receive-cap change (`5439fd2e0` / `666b7b7ab`)
is intentionally excluded. It is required for the coalesced full-session test;
this packet does not relabel the frozen INPUT gate.

The actual flow is selection/capture → root promise → manifest coverage → MID
match/prefix → pinned unit reads → unit verification → bounded stored hashing →
copy/Send → checked EOF → final trailer Send return → promise release → handoff
→ CNS lease release → FREE. There is no caller-supplied completion flag.

`cns-source-capture` copies the complete location vector, original SOURCE and
stored SOURCE from the same live typed READ into an initialized 160-byte prefix.
It acquires the root promise in the same callback before releasing that READ.
The unchanged item workspace is 10294 bytes; prefix, manifest unit and data unit
end at 8352. A named declaration theorem states their fit and nonoverlap. The
actual actor keeps its existing pool lease; there is no additional pool loan.

`cns-source-raw` queues the existing pinned BREAD primitive and routes exact
operation/cell/generation completion through the registered global prefinish
hook. READ observers only wake the CNS actor. Unit verification and <=1024-byte
stored-stream hashing are separate CNS phases. The public `source-next` only
appends <=1024 checked/hashed bytes to CTL staging, with a 2048-byte copy charge.
It rejects stale destination offsets. Hash progress advances by actual USED;
Send retries cannot rehash a unit. EOF requires both copied and hashed length
to equal the selected total, the actual stored-source comparison and live lease.

`cns-source-manifest` authenticates every complete location unit before decoding.
Header identity is original SOURCE; final stream identity is stored SOURCE.
Preflight claims every contiguous authenticated descendant before output begins.
READY replay can only confirm existing exact claims, never expand coverage.
Expected hash/CV spans remain in the first window while data enters the second.
The old cursor and new reader use one factored manifest decoder implementation.

The query region appends E*N rows after the existing checkpoint edge region.
One exact identity per query/extent deduplicates repeated references. A changed
handle in that slot refuses. After actual SEND/cancellation handback, RELEASING
checks physical quiescence and scans one owned row per step. RELEASED retains
the tuple; HANDOFF acknowledges transport before CNS releases its own lease
through its declared operation, then clears its job. Uncertain reads retain
claims/lease and stop rather than use the normal cleanup path.

One authoritative row map reserves paired upload source/stored contexts at
3+2s/4+2s, sealer 3+2W, CTL 4+2W+s at the floor, per-CNS contexts next, then five
existing tail jobs. The floor is 9+2W+C+N. Runtime CTL/CNS selectors are end-relative;
actual callbacks check FC=B3 dimensions and source-job count=CNS count. The
ordinary block row F-2 is synchronous scratch, copied to the owner's page before
yield. The minimal paired producer/sealer consumers are included; broader
rolling-input and fixed-SOURCE-copy protocol changes are not.

Producer dependencies include physical stride16, physical data groups16 and the
shared raw threshold12288. Raw and manifest-root commitments remain at most
three units (96 bytes); the journal's write-resource count remains three.
The reader adds no private article limit or global stored-history ceiling.

The real `cns-stream-fetch-unit` posts, persists and FETCHes 6144 exact bytes
through the ordinary actors without seeding a source descriptor or phase. It
remains unexecuted. A narrower two-unit reader witness drives actual allocation,
pinned operations, completion primitives, B3, a reused 4 KiB output window and EOF;
its selected typed READ premise is explicitly synthetic. Retention and hash
interleaving witnesses likewise state their scope and are unexecuted.

Forty-five targeted Python source controls pass. Advisory checks cover 139 actual
lower calls/43 known MV bindings and 9 lower-derived faces/20 direct plus 14 DSL
source calls. The literal 235-book union has no missing files or include cycles.
These are source checks, not guard admission, certificate or runtime evidence.
