# Composed store and assurance checkpoint — 2026-09-18

`make test` passed at revision `80afcbe008f3475d27d4376e1b9f205eb080a9e2`:
75 ACL2 logical/assertion roots, the actual-core simulator, and 67 Python tests.
The tracked input set was unchanged throughout the run. The
[machine-readable record](2026-09-18-composed-store.json) retains source/tool
digests, exact commands, versions and outcomes. Tools were ACL2 8.7 / SBCL 2.6.8
and Python 3.14.7 on the macOS development host.

## What this batch establishes

- Actual node traces preserve prior article/archive bindings. Mixed live
  file/node traces include refusal, known abort, uncertain commit and recovery;
  ready/recovered states agree with replay of surviving records and frontier.
- The observed-image loader uses actual recovery, invents no acknowledgements
  or barriers, and remains gated until all five recovery barriers complete.
- The physical store now reports allocator, publication and recovery outcomes
  through that composed ACL2 machine. Its one-use completion opportunity is
  consumed before calling the core; lost/rejected replies require recovery.
- Implemented NNTP command and finite-session cursor preservation, plus effect
  typing, pass certification. Socket partition and malformed-store tests extend
  the existing fault, process-death and ownership tests.
- Whole wildcard matching and public transfer missing-range operations have
  value-corresponding work bounds under their published cost models. The latter
  includes malformed-input validation, lookup and structural equality.
- Fifteen base books have 533 guard-verified functions. The logical bodies of
  452 pre-existing functions in the added graphs are unchanged; executable/domain
  helpers and MBE equality obligations are proved. This count excludes unfinished
  isolated graphs and does not claim that every function in the project is guarded.

The old parallel stateful store bridge was removed. The host uses the composed
machine for publication and recovery; remaining host code marshals bounded
values, performs I/O and enforces ownership/effect-delivery gates.

An independent Python 3.9.6 `nntplib` client passed against a freshly reopened
store: cross-posts, exact article/body bytes, GROUP/STAT, LISTGROUP ranges and
filtered listings. Exact commands and source hashes are in the record.

The current adapter also passed the maximum-profile probe: 128 articles of
32,768 octets, all cross-posted, reopened with all 128 archive pins and exact
payloads. Commit time was 227.52 seconds and reopen 11.68 seconds on this host;
these are experiment measurements, not a performance or power-loss guarantee.

## Remaining boundary

These are conditional logical results and concrete adapter tests, not a proof
of syscalls, cryptographic primitives, peer honesty or storage hardware.
Process death retains operating-system caches; power loss remains a separate
qualification task. Byte-accurate physical reservation, rollback freshness,
physical checkpoint/compaction, native signatures and full NNTP posting remain
open. No entire implementation/proof milestone is closed.

BPv7 is now an [active architectural path](../../specs/bp-path.md). Its new
workflow journal, receipt handling and real-agent interoperability are subsequent
work, not retroactively covered by this frozen 75-root batch.
