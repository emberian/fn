# Reader partition and connection-reset matrix

Status: bounded executable evidence for the implemented experimental reader
bridge.  It exercises serialized client handling and does not claim concurrent
listener service or full NNTP conformance.

The matrix uses one persistent, real ACL2-backed `Acl2Reader` and the
production `serve_client` socket adapter over local socket pairs.  Every
connection invokes the adapter's real reader reset.  Expected replies are
independent byte strings in the test; no result is obtained by comparing one
partitioned run with another.

The reset is also where the whole-archive projection recognizer runs.
`fn-reader-reset` builds the session with `fn-nntp-open-session`, which
evaluates `fn-nntp-projectionp` once and stores its verdict in the session; no
command in the connection recomputes it.  Each connection in this matrix
therefore pays that recognizer exactly once, and each command afterwards pays
only for what it reads.  See the served-path section of
[the NNTP checklist](nntp-audit.md).

The valid multicommand corpus is `GROUP fn.letters`, `STAT`, and `QUIT`, with
all 31 two-piece cuts, including each CRLF boundary.  A UTF-8 wildmat corpus
uses `LIST ACTIVE fn.ñ*` followed by `QUIT`, with all 27 cuts, including the
two cuts inside the `C3 B1` encoding.  The matrix also feeds the multicommand
corpus bytewise and coalesced directly to the bridge, calls it with empty octet
chunks between events, rejects a bare-LF command and a 511-octet command,
verifies that a `QUIT` suffix is ignored after the closing reply, and drops a
partial command both orderly and with an actual loopback TCP reset.  A subsequent connection must
receive the greeting and `412 no newsgroup selected`, proving that partial
session state was not reused.

Run the test with:

```text
python3 tests/test_reader_partitions.py -v
```

The bounded run completed 7 tests and 65 serialized socket connections in
0.148 seconds on the local ACL2 8.7 / SBCL 2.6.8 toolchain.  It passed the
independent transcripts, CRLF and UTF-8 split cuts, malformed and over-limit
close behavior, QUIT suffix handling, and next-connection reset cases.

This evidence does not cover concurrent clients, network scheduling, listener
backlog behavior, arbitrary command corpora, or complete RFC 3977 coverage.
