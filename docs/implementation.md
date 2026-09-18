# Executable development status

fn has executable ACL2 components and a deterministic simulator. It is still an
experimental implementation: the components are not yet a durable, authenticated
news service. The broader contracts in `specs/` remain the target.

## Current components

| Component | Executable scope | Remaining boundary |
| --- | --- | --- |
| [Acceptance](../books/acceptance.lisp) | Atomic local allocation, immutable Message-ID binding, staged publication, stale completion rejection, uncertainty fencing | Durable completion and recovery observations are abstract inputs; no physical disk is involved |
| [Acceptance invariants](../books/acceptance-invariants.lisp) | Mechanically checked preservation lemmas over the acceptance definitions | See the proof registry and certification evidence for the exact current theorem scope |
| [Wire framing](../books/wire.lisp) | Incremental CRLF lines, dot stuffing, article terminators, bounded retained input | Session dispatch and command conformance are separate; the bulk feed helper alone cannot decide when to enter article mode |
| [CBOR primitives](../books/cbor.lisp) | Deterministic uint32 and definite byte strings, canonicality checks, bounded decoding | No native object, signature, batch, or disk schema is frozen |
| [Retention](../books/retention.lisp) | Finite abstract accounting, distinct archive/forward pins, evidence-gated release, permanent duplicate history | Evidence is already authorized input; charging units are abstract, not measured physical bytes |
| [Simulator](../host/simulator.lisp) | Fixed traces executing the actual acceptance functions in ACL2 | No shadow semantics, network listener, or real disk adapter |

Run the current integrated checks from the repository root:

```sh
make check
make certify
python3 tools/run_simulator.py
```

`make check` validates documents and registries. `make certify` invokes real ACL2
and certifies the explicitly listed books and executable assertion books. The
simulator emits traces and result records from those same logical functions.
These commands have different meanings; none is a substitute for the others.

## Toolchain and evidence

The development toolchain is ACL2 8.7 on SBCL 2.6.8, installed on macOS using the
Homebrew `acl2` formula (8.7_6). Python 3.10 or later drives the tooling. Override
the ACL2 executable with `FN_ACL2`; the runner records the executable path/hash,
reported ACL2/Lisp versions, source/dependency hashes, drivers, certificates,
process results, and logs under `build/acl2/`. Missing ACL2 or failed proof events
fail the command. Custom ACL2 startup files are disabled for certification.

Books use ordinary ACL2 events, without proof-skipping, added axioms, or trust
tags. A certified book contains proved events and admitted definitions; it does
not imply that all its functions have verified guards or that its whole subsystem
contract has been established. Read theorem hypotheses as part of each claim.

## Deliberate limitations

- The acceptance model stores exact Message-ID strings and octet payloads. It
  does not yet validate RFC article syntax, sign native messages, or distinguish
  duplicate versus conflicting-ID rejection in its return value.
- The boolean acceptance pin and the richer retention ledger are currently
  separate components. Their transactional composition requires its own checks.
- Limits in the byte primitives are experimental local bounds. They do not
  select a permanent interoperable format or deployment resource profile.
- Cryptographic verification, peer honesty, physical persistence, backup
  freshness, and eventual contact are environmental concerns with explicit
  assumptions, not conclusions of these small model proofs.
- There is no production deployment or flight qualification. The selected
  native-signature capability remains a requirement for the first usable release.

The [current work page](../planning/now.md) records the active implementation
batch. The [proof registry](../planning/proofs.json) keeps larger proof targets
open while component results accumulate.
