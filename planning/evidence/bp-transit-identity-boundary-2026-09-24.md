# Native BP transit identity representations

The b074 native N03 and interrupted-fragment cases reached a `string=` call
with an octet vector. The first repair, `ca68b5a1`, converted both planned
values as octet sequences; its raw regression incorrectly modeled the plan
as lists. The 863c image then exposed that wrong assumption: `#\6` could not
be placed in an unsigned-byte array. Neither image passed those BP cases.

`books/bp-transit-join.lisp`, `fn-bpaj-transit-plan`, stores rendered identity
**strings** in slots 8 and 9 via `fn-record-octets-string`.
`host/bp-native-app-host.lisp` exports them unchanged, while `fnn-metadata`
returns identity text as octet vectors. The corrected native comparison
requires the plan strings and encodes them using `fnn-string-octets` before
comparing the exact octets. No identity derivation moves into the host.

The raw SBCL regression executes the shipped transit completion function with
these actual boundary types. A matching pair reaches durable completion;
independent changed identity/subject strings and wrongly typed plan values
fault before the transit decision or Store attempt. It passes locally.
This is a boundary unit test with recording stubs, not a native end-to-end
pass or an ACL2 proof. Both image failures remain in the qualifier's logs;
the corrected native path still needs its matching-image rerun.
