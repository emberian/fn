# fn extension: DEFLATE with a preset dictionary named by digest

Status: fn extension, specified (NNT-055 for the wire, STO-037 for the
store). The store's half is implemented. The wire negotiation below is
specified but not served yet: `CAPABILITIES` does not advertise it.

fn compresses with one format in two places. It uses standard DEFLATE
(RFC 1951) with a preset dictionary (RFC 1950 section 2.2's FDICT) that is
named by its digest. RFC 9842 uses the same shape for HTTP: a dictionary
both ends already hold, identified by a hash, over an ordinary compressed
stream. Nothing here is a new codec. A decoder that implements RFC 1951 and
can load a preset window decodes every fn payload and every fn stream.

- **The store.** A stored article payload is a raw DEFLATE stream made over
  a shipped dictionary. Its frame names the dictionary by DICT-ID
  (`books/payload-lz-record.lisp`; `specs/storage.md`, STO-037).
- **The wire.** This is an NNTP `COMPRESS DEFLATE` session (RFC 8054) in
  which both ends preset the same dictionary. Between fn peers, a stored
  payload also travels as its stored octets through its own command, so it
  is never decoded and re-encoded. (This is the specified half; see
  "Negotiation".)

Both directions decode through the same verified inflater,
`books/deflate-inflate.lisp`. The wire uses `fn-zin-feed`. The store uses
`fn-zin-payload-with` and `fn-pzd-decode`.

## Dictionaries

A dictionary is an octet string of at most 64 KiB. The inflater presets its
last 32 KiB (RFC 1951's window). Its digest is BLAKE3 (`books/blake3.lisp`)
over its octets. Its DICT-ID is the first four octets of that digest, read
big-endian. DICT-ID 0 is the empty dictionary. A frame's DICT-ID resolves
only through the node's table, and the table holds the full digest.

The table is shipped with the release (`books/payload-lz-dicts.lisp`). Its
rules are these:

- It is **append-only and kept forever.** A payload made under a dictionary
  stays readable by every later release. Nothing is transcoded at rest.
- There are **no learned, per-group or on-node dictionaries.** A dictionary
  trained on the node's own articles was measured and dropped: it gained 8
  percent and leaked what the node carries. The shipped table is the same
  on every node, so a DICT-ID means the same octets everywhere.
- It is built **from text fn owns.** The measurement corpus (20news) is never
  a training input.
- New payloads are made under the **current** dictionary
  (`fn-lzd-current-id`), which is the latest shipped one.

ACL2 computes each shipped dictionary's digest when the book is certified.
It checks the digest against the recorded one and checks that no two IDs
collide. So the DICT-ID in a frame is the one ACL2 computed, not one the
builder asserts.

## The baseline dictionary (baseline 1)

| | |
| --- | --- |
| octets | 32,768 |
| BLAKE3 | `845aa5e18680ef219a9b0f0d0b959cd8886d5eabc12236aae19f301aed9de75e` |
| DICT-ID | 2220533217 (`0x845aa5e1`) |
| SHA-256 | `7350734dbc0f867a9bb4d04aacc1f87b954842af13cd459da644c2ba32123121` |
| artifact | `books/payload-lz-dict-1.lisp` (generated), `planning/evidence/compress-dict/baseline-1.bin` |
| manifest | `planning/evidence/compress-dict/baseline-1.json` (the 120 inputs and their SHA-256) |

### Recipe

`python3 tools/build_compress_dict.py OUT --lisp books/payload-lz-dict-1.lisp`
runs the recipe. It is deterministic, uses no trained model and reads no
third-party corpus.

1. **Inputs.** The RFC texts in the repository root (`rfc*.txt`), then
   `docs/**/*.md`, `docs/articles/*.txt` and `specs/*.md`, each group sorted
   by path. These are the RFCs fn implements and fn's own prose, including
   its own articles with their headers. Every line end is made CRLF, the wire
   form.
2. Count every 8-octet substring (d-gram) of the whole input.
3. Cut every file into 64-octet segments at 64-octet offsets. A segment
   scores the sum of the counts of its distinct d-grams that no chosen
   segment already holds.
4. Take the best segment. Ties go to the earlier file, then to the earlier
   offset. Mark its d-grams as held, and repeat until 32,768 octets are
   chosen. Scoring is lazy: a popped segment is re-scored, and it is pushed
   back unless its score did not drop.
5. Lay the chosen segments out in ascending score. The most valuable text
   then sits at the end, nearest the payload, where DEFLATE's distances to
   it are shortest.

To reproduce baseline 1, run the recipe over the inputs listed in its
manifest. The inputs are identified by their SHA-256, and a checkout whose
files differ builds a different dictionary. A new dictionary is a new table
entry (baseline 2); the existing one is never replaced.

### Measured

On the survey's 9,733 held-out 20news articles (zlib 9, raw DEFLATE, one
stream per article; `planning/evidence/compress-2026-09-28/gate-result.md`),
the ratio is:

- 2.13 with baseline 1;
- 2.07 with a naive "last 32 KiB of the RFCs and docs";
- 2.15 with the survey's zstd-trained dictionary of owned text (32 KiB);
- 1.97 with no dictionary.

The DEFLATE payload decoder takes a median of 148 us per article on hbox.
The recipe's parameters (64-octet segments, 8-octet grams) measured best
among 32/64/128 and 6/8/12.

## Negotiation (wire; specified, not served)

The negotiation is shaped after RFC 9842's `Available-Dictionary`, carried
over NNTP. RFC 8054 is unchanged, and a client that knows nothing of this
extension sees plain `COMPRESS DEFLATE`.

- `CAPABILITIES` lists `COMPRESS DEFLATE` and, on its own line,
  `XFN-DICT <b3-hex> ...`, which names the full BLAKE3 digests of the
  dictionaries the server holds, newest first.
- `COMPRESS DEFLATE <b3-hex>` asks for a session whose two streams are
  preset with that dictionary. The server answers `206` only for a digest it
  listed. An unknown digest gets `503`. Without an argument the session is
  plain RFC 8054.
- In a dictionary session, both streams start with the dictionary's last
  32 KiB as history (zlib `deflateSetDictionary` / `inflateSetDictionary`
  in raw mode). The inflater loads it (`fn-zin-load-preset`) before the
  first octet.
- **Stored payloads as they are stored.** Inside a session, a stored
  payload cannot simply be spliced into the stream. Its back-references
  assume the dictionary sits directly before its first octet, but in a
  session the earlier traffic is in between. Its final block would also end
  the session. Carrying stored octets unchanged is therefore a separate fn
  command: `XFN-ZARTICLE <message-id>` answers `220`-shaped with the
  payload's DICT-ID and its raw stream as a dot-stuffed multi-line body. A
  peer that holds that dictionary stores the stream as received, after
  decoding it with the verified decoder and comparing it with the article's
  identity. A peer that does not hold it asks with `ARTICLE`. The sender
  never decodes anything to answer.

The decisions are ACL2's (`books/nntp-compress-dict.lisp`, PRF-974):
`fn-zdn-capability-line` makes the `XFN-DICT` line, `fn-zdn-request`
parses `XFN-ZARTICLE <message-id> <b3-hex> [<b3-hex> ...]` (the request
lists the digests the asking peer holds, so no session state is needed),
and `fn-zdn-choose` decides each reply: the stored frame as it is stored
when the peer listed the digest the shipped table records for the frame's
DICT-ID, otherwise the article decoded here and sent as `ARTICLE` sends it
(raw, or inside the connection's `COMPRESS DEFLATE` layer). Open for the
wiring: the frame is binary, so the reply line carries its octet count and
the receiver checks the unstuffed body against it (dot-stuffing alone is
not octet-transparent at the body's end).

Security (RFC 8054 section 7) is unchanged. A dictionary is public, and it
adds no secret to the compressed lengths.
