# Bounded pinned BPA receive boundary

Status: integrated local interoperability and boundary tests passed on
2026-09-18. [Exact inputs, versions and results](2026-09-18-bpa-boundary.json)
record revision `27071be` plus the changed source digests.

`tools/bpa_dtn7.py` uses the pinned dtn7-rs HTTP inventory, non-destructive raw
bundle download and explicit delete routes. It caps the response while reading,
before JSON decoding or writing a raw bundle file. The ingress lab permits only
IPv6 loopback, at most 8,192 inventory entries, 512-octet BIDs, 64 KiB raw bundles
and 32 KiB extracted article ADUs. Socket operations have a two-second timeout;
the payload-extractor process has a ten-second timeout.

The small Rust extractor delegates to the existing pinned `bp7::Bundle::try_from`
and payload-block accessor. It introduces no BP codec. The build hook verifies
the pinned checkout revision and builds this additional binary with
`cargo build --release --locked -p dtn7 --bin fn_bpa_payload_extract`.

The integrated actual-BPA lab passed receiver restart, article acceptance,
and a distinct-BID exact-article retry. Both recovered snapshots contain one
transaction, one article and one archive pin with identical source bytes. Eight
mock HTTP tests passed in 4.043 seconds, including declared and actual chunked
oversize, timeout, refusal, malformed inventory and query delimiter handling.

This is a bounded laboratory adapter, not a proof of the upstream BP parser or
of physical durability. Per-operation socket timeouts do not bound an entire
slow transfer. The native parser's allocation and CPU behavior remain outside
the ACL2 argument. This run still uses a BPA fixture as sender and emits no fn
application receipt. Earlier evidence remains unchanged.
