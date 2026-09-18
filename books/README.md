# ACL2 books

Reserved for executable definitions and their proofs. No ACL2 books are present
yet. The [M1 plan](../planning/milestones.md#m1-executable-model) first pins the
toolchain and defines the logical records/event interface.

Proposed dependency order: data recognizers and identity domains; local article
acceptance and allocation; obligations; transitions and trace invariants; codecs;
storage/recovery; NNTP; replication; GC/compaction; concrete refinements. Split
books by actual dependencies as the definitions emerge rather than creating an
empty file per possible subsystem.

Use the [proof registry](../planning/proofs.json) to map targets to real theorem
events when introduced. Keep pure certification independent of raw host adapters.
