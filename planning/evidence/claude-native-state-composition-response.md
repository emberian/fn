# Disposition: native journal lifetime and retained history

The [independent Claude review](claude-native-state-composition-review.md)
inspected `622df08` in the requested interactive tmux. It found no reachable
standalone handler using the wrong Store image. Its structural warning matters
for the pending owner callback: the owner stores state in `fn-owner`, while the
standalone journal wrappers read `fn-store-sn`. A raw Store struct and a held
lock do not establish those logical images agree. The callback must take its
node from the actual owner with an explicit binding contract. A raw epoch
counter alone is not that correspondence proof.

The avoidable retained-history copy is real: the raw adapter appended each
record to a list only used for initialization checks. The repair removes the
slot and reads the already-carried ACL2 `fn-aj-initializedp` frontier instead.
It does not add a second host count or initialization policy. Recovery still
reads and validates the journal once. A reinitialization regression preserves
existing bytes and outstanding work; its integrated-image run remains pending.
The review is source inspection, not throughput or whole-program assurance.
