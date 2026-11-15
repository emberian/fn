# Startup and one-POST physical envelope

`fn2-checkpoint-service-demand-vector(profile, pool)` is one pure class vector
for physical startup and one foreground POST. It does not reserve resources or
promise completion. The aggregate configuration/profile check must consume this
same vector together with actual working and B-row drain demand before mutation.

Upload sizing comes from the actual shared `upload-page-geometry` functions.
`fn2-upload-bound` delegates to `fn2-upload-input-bound`; the input configuration
and service formula use the same `fn2-upload-profile-article-max`. The existing
input bound, Message-ID allowance and page packing remain unchanged. Identity
scratch/default arena geometry likewise has one definition used by the actual
C initializer. POST arena count comes from the existing typed schema IDs for
the actual writer families, checked against the producer source; it is not a
new stored-data limit.

For each class, the vector takes the maximum of these source-derived overlaps:

| Phase | Generic physical leases beyond separately protected credits |
| --- | --- |
| Fresh startup through prefix recovery | Boot pack/rx + recovery window/workspace (four journal-sized slots), one persistent bind scratch if NAME is nonempty, one arena per nonempty group/principal NAME role |
| Cold startup through recovery | The same four journal-sized slots and one checkpoint root page |
| Fresh ready plus one POST | Retained NAME arenas, one bind scratch total, one arena per distinct POST writer schema, two upload chunks, one actual maximum store page |
| Cold ready plus one POST | One bind scratch, POST arenas/chunks/store page, and the currently retained cold root page |

The current cold source releases recovery's two slots and boot's pack/rx, but
no root-slot release was found at READY. That retained page is explicit in this
vector until the owning boot path releases it. Query references pin their
underlying physical slot and source debt protects extents; neither is a new
pool slot. Actual free counts exclude held physical buffers, so adding their
reference counts again would double charge capacity.

For the node's two-class layout and 4 KiB arena, bare POST demand is eleven
4 KiB slots plus three 64 KiB slots. With both fresh NAME roles retained, fresh
ready demand is thirteen plus three; current cold ready demand is eleven plus
four. The component maximum is thirteen plus four. These are source-prepared
sizing witnesses, not executed assertions or a liveness theorem.

Actual new upload claims begin at TAKE in NNTP and CNS. TAKE reserves two
chunks; the store page and C scratch/spares are acquired later. C stage first
checks schema room, then acquires scratch/spares sequentially and can retain
partials on `:full`. A read-only free-count check at TAKE is not a claim across
interleavings. Late stage happens after payload IO and cannot use an empty
no-IO abort rule. A protected service floor without a redemption path would
also block the existing generic consumers.

The dynamic policy therefore still needs exact owned physical claims before
new work, or an equivalent admission protocol. C schema pressure remains
explicit backpressure: it can require sealer work even with a funded physical
vector. Sealer output pages move into cache and remain held until retirement;
one fixed page does not establish general progress, and reserving every data
page is not the intended solution. Runtime pool policy belongs to the capacity
owner; no policy or pool schema change is made here.

`tools/upload_page_geometry_source_test.py` preserves the original 22 production
forms once; `tools/checkpoint_service_geometry_source_test.py` connects writer
families and the C initializer to this geometry. ACL2 sizing assertions,
aggregate exact-fit refusal/sufficient profile controls and composed runtime
qualification are pending. The pure service book/unit closures are 41/42 local
books; no compute was allocated for this source work.
