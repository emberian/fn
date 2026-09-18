# Host adapter

The deterministic [simulator](simulator.lisp) executes the actual acceptance
definitions in ACL2. Run it with `python3 tools/run_simulator.py` after certification.
The local reader bridge is being integrated separately. Read the
[host contract](../specs/host.md) before changing packaging or an event loop.

The first socket experiment is a loopback-only, seeded in-memory reader. It is
independent of the qualified storage adapter and cannot accept durable posts.
Record supported ACL2/Lisp versions and platform barriers.
Do not create a second implementation of core semantics to make the host easier
to package. Runtime configuration, authentication, and deployment are later
deliverables tied to the first usable service milestone.
