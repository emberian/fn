# Host adapter

Reserved for the Common Lisp I/O adapter and simulator integration. No daemon or
executable entry point is present. Read the [host contract](../specs/host.md) before
choosing packaging or an event loop.

First implement a deterministic model host, then the qualified storage adapter,
then the socket adapter. Record supported ACL2/Lisp versions and platform barriers.
Do not create a second implementation of core semantics to make the host easier
to package. Runtime configuration, authentication, and deployment are later
deliverables tied to the first usable service milestone.
