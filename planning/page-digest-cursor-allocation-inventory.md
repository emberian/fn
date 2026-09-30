# Digest continuation allocation inventory

Source coordinate: executable cursor from de785cd62, domain/guard leaves through
e8dc2a84e. This inventory counts source list constructors conservatively. It is
not a measured selected-runtime allocation theorem or a physical-byte charge.
The funding/runtime lane owns that named assumption and matching measurement.

The actual stobj `pgs-digest-state` has16 fields and a64-slot T frame array.
Begin replaces scalars without clearing the array. Frames above current depth
remain reachable from that array even after pop or a later begin, so count all64
slots at their worst retained shape. A left frame has5 cons, a right frame has5
plus its8-word CV: at most832 frame cons in the retained array. The current CV
can cost8 more. The output descriptor has5 cons plus its16-word block and a
separate8-word input CV. That input CV can differ from current CV after the
left return resets the right child's state. Sharing may reduce allocation;
conservative inventory must charge both. Total retained list cells:869, plus
array slots and the stobj representation. Captured token/lease and immutable
source ownership are separately funded by their controller; the core only
retains their supplied references. Answer is at most a256-bit natural.

Compression source in `books/blake3.lisp` executes56 `fn-b3-g` calls returning4
values, seven `fn-b3-round` calls returning16, one final8-value result, and an
8-word result list. Treating each potential MV tuple as an allocated list gives
224+112+8+8=352 potential cons per compression. Tail returns do not require
another copy in this source model. Actual compiled MV representation may remove
these allocations; this inventory deliberately does not assume elimination.

| Actual primitive phase | Conservative new potential cons |
| --- | ---: |
| Nonfinal chunk | 352 compression +16 padding +5 descriptor +2 step MV =375 |
| Final chunk / exact-byte tail | 16 padding +5 descriptor +2 step MV =23 |
| Return-left | 352 compression +5 replacement frame +2 step MV =359 |
| Return-right | 352 compression +8 cv8 normalization +8 append prefix +5 descriptor +2 step MV =375 |
| ROOT step | 352 compression +8 reverse +32 octets +2 step MV =394 |
| Byte result-octets getter | 352 compression +8 reverse +32 octets =392 |

The supplied16-u32 caller block is separate. Old retained state may coexist with
these temporary allocations: old/new frame overlap, old output descriptors and
CVs are covered by charging retained highwater plus the complete new allocation
count. The result-octets getter performs an additional ROOT compression; a
composed controller that calls it in the same scheduling step as ROOT must fund
two compressions, or yield between them. A primitive's bound is not a composed
host-call bound.

Compression values are u32; additions of three words stay below2^34 and the
largest rotation shift below2^57, within the positive fixnum range of the
selected64-bit runtime. The ROOT natural conversion performs32 multiplications
by256 and32 additions, with up-to256-bit results and old/new accumulator overlap.
The current directory format has B<2^46, words<2^43 and counters<2^36. A generic
u64-word profile may require64-bit scalar bignums and intermediate products up
to67 bits. Scalar source expressions are fixed per phase; funding has been told
to reserve conservatively128 possible scalar arithmetic result objects per
step, plus64 ROOT accumulator operations, pending its explicit runtime model.
This last reserve is an intentionally generous source inventory, not an admitted
compiler allocation bound. Guard division/ceiling, boxing, compiler temporary
objects and GC/arena behavior belong in the selected-runtime assumption.
