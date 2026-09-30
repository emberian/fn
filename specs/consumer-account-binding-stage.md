# Durable signing-binding preparation

The account adoption producer must durably retain the signing decision selected
with each winning credential. A prepared account row alone does not contain this
provenance. These FNCE stages prepare the replacement configuration privately;
only the joint typed C adoption commit may publish it together with the account
root. This is an fn format rule, not an NNTP or BP RFC requirement.

The event retains the five-field envelope:

```
(:consumer-authority sequence txid keyring-generation
 (:authority-binding candidate-id base-authority-revision login-octets
                     provenance mode principal32))
```

The operation has seven fields including its tag. Its legal decisions are:

| Provenance | Mode | Meaning |
| --- | --- | --- |
| 0: static | 1: delete | Explicitly remove the login's signing binding. |
| 0: static | 2: bind | Install the selected signing principal. |
| 1: redeemed | 0: preserve | Retain the binding from the captured base configuration. |
| 2: tombstone | 1: delete | Remove an orphaned old binding. |

Every other pair refuses. Non-bind stages require an exact 32-zero-octet
placeholder, making their representation canonical. A bind carries the parsed
signing principal, which need not equal the credential principal. Selection
must preserve the whole winning tuple: static-first and first duplicate wins;
a later credential must never donate its signing principal to an earlier one.
The codec checks the field domains and decision matrix. It cannot establish
that this tuple was selected by the authentic candidate producer.

Bytes begin with `fnce` (102, 110, 99, 101), explicit version 3 and code 7.
Three big-endian u64 event coordinates follow, then candidate ID (one length
byte plus 1–64 octets), base authority revision (u64), login (one length byte
plus 1–64 octets), one-byte provenance, one-byte mode and the 32-byte principal.
The derived maximum is 202 octets: 30 + 65 + 8 + 65 + 1 + 1 + 32.
`fn-cab-event-charge` is the actual encoded length. This bounds one stage,
not account-table size; u64 representation does not widen allocator admission.
The decoder bounds external input before traversal, requires exact consumption,
and refuses unknown versions/codes, malformed fields and trailing bytes.

Version 2 account stages remain unchanged and use their existing decoder.
The physical E dispatcher must explicitly route version 3/code 7 to this codec
and the matching prepared-configuration transition. A contextless or legacy
interpreter refuses it; decoding alone never changes current account authority.

The semantic producer must check the exact pending candidate and base revision,
include binding stages in its content count/digest, and update the private
configuration in bounded funded steps. Preserve mode reads the captured base;
ordinary C publication invalidates preparation. Recovery must replay the same
stages and recover the same prepared pair. The final C commit validates and
installs that pair atomically; partial stages cannot authorize credentials or
bindings. Checkpoint/reclamation must retain the preparation sources until
commit, durable discard or ordinary-C invalidation. Those integration properties
remain with the account transaction owner, separate from the codec proof.
