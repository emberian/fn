# Frozen native shared-owner cost profile — 2026-09-21

This bounded run measured the existing production saved image at source revision
`8c231978`, `/home/ember/fn-gates/freeze-f7190d69/build/fn-host` on `persvati`.
The image SHA-256 was
`4fe51b69b65530868a168b38454c1929f90e82d987eabbe3614ea6b86b35837e`.
Its qualification and build provenance are recorded in
`planning/evidence/native-freeze-gate-2026-09-21.md`.  The harness SHA-256 was
`5a42d67bd8db7ea9c486086acefb3f97191d9f913308824c7c6ea4839c85857d`.

One production operator owner held one task-local store.  Each post invoked the
production `operator CONFIG post` client against that owner's Unix control
socket and had to return `accepted operator post`.  Each read opened a loopback
NNTP connection, issued `ARTICLE <message-id>`, consumed the complete dot-ended
response, and had to receive status 220.  No existing service or store was
used.  The input comprised 128 unique, valid articles of exactly 1,202 bytes
each (153,856 bytes total), with a 1,024-byte body; the JSON records every
Message-ID and article SHA-256.  At each history size, 20 deterministically
spread message IDs were read.  Percentiles use nearest-rank p95.  RSS is the
owner's Linux `VmRSS`, sampled after the reads.

| Accepted articles | Posts in interval | post p50 | post p95 | NNTP read p50 | NNTP read p95 | owner RSS |
|---:|---:|---:|---:|---:|---:|---:|
| 1 | 1 | 72.763 ms | 72.763 ms | 0.301 ms | 0.570 ms | 318,844 KiB |
| 16 | 15 | 76.786 ms | 81.875 ms | 0.443 ms | 0.834 ms | 345,408 KiB |
| 64 | 48 | 79.406 ms | 82.746 ms | 0.722 ms | 0.934 ms | 422,088 KiB |
| 128 | 64 | 78.214 ms | 82.755 ms | 1.796 ms | 1.987 ms | 526,740 KiB |

Empty-store initialization took 89.527 ms and initial owner startup took
62.939 ms.  After an orderly stop at 128 articles, reopening took 211.392 ms,
reported 406,272 KiB RSS, and retrieved the last article in 4.016 ms.  These
single startup/reopen observations are not latency distributions.

The served Message-ID path calls `fn-nntp-msgid-retrieval` in
`books/nntp-responses.lisp`, which calls recursive `fn-find-article` over
`fn-state-articles`; its definition in `books/acceptance.lisp` is a linear list
search.  The measured read median rose from 0.443 ms at 16 articles to 1.796 ms
at 128 articles, consistent with that scan being a growing served-path cost.
This small run does not establish an asymptotic rate or isolate network,
connection, ACL2, and response-framing costs.  Post medians remained within
76.8–79.4 ms from 16 through 128, but each sample includes production client
process startup and durable commit work, so it does not identify a dominant
post component.  The owner recovery code also decodes and replays the retained
record sequence at startup; the one reopen observation only shows its cost at
this 128-article profile.

The adjacent JSON is the complete machine-readable result.  This evidence is
scoped to this byte-identical frozen image, host, input profile, and one run; it
does not prove scalability or predict larger histories.
