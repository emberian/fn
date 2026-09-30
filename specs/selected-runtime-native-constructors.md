# Selected native constructor owned-object contract

`PRF-1153` supplies the connection operation builder with an ACL2-owned subtotal through `fn-srnc-connection-owned-request`. It accepts exact immutable unit source coordinates and the selected fresh native SBCL compiler coordinate at installation; mismatch or invalid counts returns `:unavailable` and NIL. `:native-owned-row` does not mean admitted. A served body must consume the carried installed family association, rather than compare source hashes or reconstruct this roster each call.

A-SELECTED-RUNTIME-NATIVE-CONSTRUCTORS is isolated in `books/assumptions-selected-runtime-native-constructors.lisp`. Its local zero witness establishes consistency only. The conditional unit request constrains native owned objects, not the physical allocator reservation or every allocation made by Lisp signaling and compilation. The existing compiler/host trust boundary remains necessary.

The current Linux X86-64 SBCL 2.6.8 native component, with the recorded binary/core and optimize policy, has these retained objects:

| Subject | Owned object octets | Scope |
| --- | ---: | --- |
| service | 848 | service432 plus three mutex32, two waitqueue32, two hash128 |
| custody node | 48 | all five fields; token is an existing core-issued pointer |
| mux connection | 256 | entire current object, including custody field |
| fixed-tag fault | 80 | fixed condition object and existing cause pointer |
| collection observation | 64 | installation-only preallocated seven-field carrier |
| collection binding | 48 | five pointers, copier disabled |
| bound collector factory | 112 | one binding plus its SAME64 sample, callback selection separate |

The shared default hash backing is an existing 48-byte image root, not two fresh service arrays. Constants, classes, default global roots and compiler first-use belong to the installation baseline. One service plus one unbound collector sample is 912 octets. The actual installed binding factory creates one sample itself: service plus binding/sample is 960, without counting the sample twice. A retained service, mux, two old/new nodes and one fixed fault subtotal is 1280. Actual core disposition permits node release; socket close, native phase or GC does not refund charge. Constructor escape retains the raw token, including after a node was allocated but could not be published.

The fresh fixture covers intrusive live/retiring overlap and release, constructor faults before/after allocation, and exact fixed-tag callback error/throw paths with a condition printer trap. It preserves source identity and records ARM64/Darwin separately: node64 and fault96 fail the Linux node/fault request. Batching is an allocation refuter only; TLAB accounting and concurrent/GC allocation mean `get-bytes-consed` differences are not a physical upper bound.

The complete connection operation additionally needs existing/new token constructor requests, socket/channel/TLS and input/output buffers, raw declaration/table first-use, XEP/caller and ERROR/&rest/PCL frames, signaling scratch and arbitrary original cause construction, allocator reservation and GC baseline/resumption. Those units remain separate. No unit in this book silently prices them at zero. The installed receipt, common operation trace/census, funding authority and served activation are outside this component.
