# Selected BP creator object units

PRF-1184 / A-SELECTED-RUNTIME-BP-CREATORS is a conditional constructor-object
unit, not an admission contract. The actual public BP record constructor and
workspace installation gate remain unavailable before allocation. A matching
source/body coordinate is a qualification requirement, never installed authority.

The callable `fn-srbc-constructor-object-request(kind,coordinate)` returns four
values: status, cumulative object-request octets, request count, and retained
owned-object octets. Unsupported kinds or coordinates return
`:unavailable,NIL,NIL,NIL`. Successful fixed-unit rows are:

| Kind | Request octets | Requests | Retained owned octets |
| --- | ---: | ---: | ---: |
| `:record12` | 144 | 2 | 144 |
| `:digest16` | 672 | 2 | 672 |
| `:carry6` | 64 | 1 | 64 |
| `:node16`, `:left16`, `:right16` | 704 | 10 | 608 |

The native record includes its fresh mutex and retains the immutable actual job
token. The digest includes its fresh64-pointer frame vector. Nodes are raw hash
tables directly; each owns128-byte table,304-byte KV vector,80-byte index vector
and96-byte next vector. EQ's NIL hash vector is borrowed, not a new object.
The ACL2 default-hash wrapper creates two size cells, APPEND2 copies those two,
then creates two test cells: six16-byte temporary requests. They add to epoch
allocation debt even though only the608-byte graph survives return.

The named assumption scopes definitely successful fixed creator object paths.
It excludes full keyword entry/caller frames, invalid-argument/fault construction,
allocator slow paths/TLAB slack/automatic GC, first-use/code/cache work, child
publication/GET/HASH mutation, I/O and complete cleanup. The ordinary allocator
geometry unit consumes request octets and count separately. Logical release does
not reduce allocation debt; retained borrowed tokens, plans, stages and graphs
remain separate lifetime obligations.

Declaration-created USER-STOBJ-ALIST defaults are separate retained image roots:
carry64 + three nodes3*608 + digest672 =2560 object octets in this isolated
cohort. These actual objects cannot be silently reused as charged factory
objects or transferred into another image. The arithmetic subtotal is not a
qualified image baseline.

Factory source obtains SAME-pool stored constructing intent before its creator;
root/missing-child turns create exactly one object and return. Neither that
intent, compiled callback presence nor this object row authorizes allocation.
The genuine installer must additionally supply all missing frame/first-use/GC/
fault/publication units and bind the current pool and full operation source.
