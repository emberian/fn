# Actual rolling upload caller frontier

At canonical source `6701dbac50678ced466358a13dc43c704bba03b4`, the actual
`conn-schema`, `tls-kind` and `conn-kind` now pass whole-source author checks
at original-event limits of 2,000,000 steps and 20 seconds, then record
certification. Every leaf used its own minimal exported parent ENTRY in a
fresh session; later leaf contracts were not preloaded into earlier proofs.

The qualified union is the exact `conn-kind` 46-book closure: 43 previously
genuine parents reused and three newly certified books. Individual record
runs covered schema39 (38 reused, 17.782 seconds), TLS31 (30 reused, 2.976
seconds), and connection46 (45 reused, 5.136 seconds). The schema remains
above the ten-second book-performance target in this one-job run.
[The receipt](receipts/rolling-caller-qualified46.json) binds each phase's
raw sources, keys, exported ENTRY, author results, manifest and qualified
certificate/FASL payloads. The effective cap was 2 GiB with swap disabled;
owned PIDs and scope are gone.

The original whole `upload-kind` DEFMACHINE macro still refuses at its
20-second limit after 750,968 steps. The generated ILEN setter's preservation
proof was interrupted by the inherited macro deadline; that child did not
receive a fresh quota. No upload-kind certificate was claimed or published.
Consumer-local theory performance is under investigation, with statements,
runtime and guards preserved. Full actual rolling served upload remains the
destination; this receipt establishes only the three qualified caller leaves.

A fresh minimal105-parent metadata session found compile defaults already
`(NIL :BOOKS)`: `:compile-fns` is NIL and `compiler-enabled` is :BOOKS.
Adding a local NIL compile policy would therefore change no relevant behavior;
no such source edit or repeated upload macro attempt was made. Stock SBCL
EVAL also compiles DEFUN bodies independently of this ACL2 table flag.
[The release receipt](receipts/rolling-caller-release.json) confirms all sixteen
recorded campaign/probe PIDs absent, both owned transient-unit patterns gone,
and all five session holders empty. The named 2 GiB reservation was released
under a fresh ledger lock. The upload-kind whole-macro performance obstruction
remains open for a real generator or consumer-theory improvement.
