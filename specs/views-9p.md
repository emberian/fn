# A 9P2000 view of a committed store

Status: experimental, read-only, loopback. This is a second *interface* over the
NNTP projection defined in [the NNTP contract](nntp.md) and implemented in
`books/nntp.lisp`. It is not a second projection: no acceptance, numbering,
membership or framing decision is made here or in the host.

The server is [`tools/fn9p.py`](../tools/fn9p.py); the ACL2 adapter it reads
through is [`host/ninep-host.lisp`](../host/ninep-host.lisp).

## The tree

```
/status                          the snapshot's generation and sizes
/groups/<group>/<number>         one article, the exact stored source octets
/by-id/<message-id-hex>          the same articles, named by identifier
```

`<group>` is a configured group name; `<number>` is a decimal local article
number; `<message-id-hex>` is the lowercase hexadecimal encoding of the stored
Message-ID's octets, which keeps an identifier's angle brackets and punctuation
out of a file name. Hexadecimal encoding is done by the ACL2 adapter
(`fn9p-hex`), so the host never rewrites a stored identifier.

There is no `.overview` file. An overview projection is an `OVER`/`HDR`
question, and this tree has no `fn-nntp-over-*` helpers to serve it from; a
view built by tab-joining fields in the host would be exactly the second
implementation this project forbids. The file appears when those helpers do.

## Where every byte comes from

| Path | ACL2 function that produces the bytes |
| --- | --- |
| `/groups` listing | `fn-state-groups`, rendered by `fn-nntp-string-octets` |
| `/groups/<g>` listing | `fn-nntp-group-range-numbers` over the full article-number range, rendered by `fn-nntp-number-lines` — LISTGROUP's list, by LISTGROUP's function |
| `/groups/<g>/<n>` | `fn-nntp-find-group-number` then `fn-article-payload`, guarded by `fn-nntp-article-idp` and `fn-nntp-article-framedp` |
| `/by-id` listing | `fn-nntp-projection-articlep` filters `fn-state-articles`; `fn9p-hex` names them |
| `/by-id/<hex>` | `fn-article-payload` of that article |
| `/status` | `fn-state-next-txid`, `fn-state-articles`, `fn-state-groups`, rendered by `fn-nntp-decimal-field` |

The archive these run over is the one `fn-reader-use-store` selects: the
actual-node acceptance projection of the store the ACL2 replay reconstructed.
`fn-reader-use-store` refuses a configuration `fn-nntp-projectionp` rejects, so
a store the NNTP reader would refuse to serve is a store no mount can obtain.

An article file holds the stored payload, not a wire block: no status line, no
dot-stuffing, no terminating `.` line. That is what makes the correspondence
checkable byte for byte. For any servable article,

```
ARTICLE <n> reply = "220 <n> <message-id> article follows" CRLF
                    + dot-stuffed(file bytes) + "." CRLF
```

and the file bytes are the payload `fn-nntp-article-response` stuffs.
`tests/test_fn9p.py` asserts that equality against a live reader over the same
store for payloads that need no stuffing.

## Degradation, not refusal

A committed article whose stored bytes the projection cannot frame degrades
only itself, exactly as it does over NNTP. `/groups/<g>` lists it, because
LISTGROUP lists it; `stat` reports length 0; `open` fails with the same reason
NNTP reports as `503 stored article framing unavailable`. It does not deny the
directory, the group, or the mount.

## The fixed-generation rule

A mount shows one committed generation for its whole life.

The server acquires the shared store lock, replays the committed transaction
history through the same `Store.recover` path as
[the reader](../tools/run_reader.py), materializes *every byte of the whole
view* through the adapter, and only then releases the lock, the bridge and the
ACL2 process. From that moment the served tree is a frozen copy: no later
commit is visible through it, `/status` keeps naming the generation it was
built from, and a reader who wants a newer generation mounts again.

Two consequences are deliberate:

- A live mount does not block a writer. The reader holds its shared lock for
  the life of the process, so a post is refused while it runs; a mount can last
  days, and blocking a writer for days to serve a snapshot it has already
  copied would be a worse trade.
- Materialization cost is paid once, before the listener accepts anything. The
  per-article recomputation of a group's number list happens there, never on a
  served read, so the served path does no whole-state work (AGENTS.md, "no
  whole-state revalidation on a served path").

The snapshot is bounded before it is built: `--max-bytes` (64 MiB by default)
caps the octets of the whole view, and a larger store is refused rather than
served by a host that has already committed to holding it.

## What is not served

- No writes. `create`, `write`, `remove`, `wstat` and any non-read `open` mode
  are refused. Posting is NNTP's and the store's business.
- No authentication, no per-user access control, no `access=client` identity.
  `Tauth` is answered with an error, which is the protocol's "none required".
  Bind it to loopback; anyone who can reach the port reads everything.
- No `9P2000.u` or `9P2000.L` extensions. A client asking for either is
  answered with base `9P2000` and is expected to fall back.
- No change notification, no `qid.version` movement, no leases: a frozen tree
  has nothing to invalidate.
- No overview, no header index, no wildmat matching, no NEWNEWS, no history:
  those are NNTP commands, and a file interface for them waits for the
  projection functions that answer them.

## Trust boundary

The host is trusted for transport and framing only: accepting connections,
decoding 9P messages, bounds-checking them, copying octet ranges, and refusing
what it does not implement. It parses no article, derives no number, compares
no identifier, and decides no membership; every value it emits arrived from
ACL2 as a list of octets. An adapter defect can therefore misaddress or
truncate a file, and that is what `tests/test_fn9p.py` and the kernel-client
transcript in [the evidence note](../tests/evidence/2026-09-19-nine-p.md) test;
it cannot invent an article, renumber one, or show a group an article does not
belong to.

`host/ninep-host.lisp` is an experimental adapter in ACL2's program mode, like
`host/reader-host.lisp`. It is not certified, and nothing here is a proof
claim; its whole content is addressing and octet plumbing over certified
projection functions.

## Mounting

Linux mounts this with the in-kernel client:

```
python3 tools/fn9p.py --store /path/to/store --port 5640 &
mount -t 9p -o trans=tcp,port=5640,version=9p2000,uname=fn,access=any,msize=8192 \
      127.0.0.1 /mnt/fn
```

macOS has no kernel 9P client; the test suite drives the server with its own
client instead, and the kernel-client transcript is recorded on Linux.
