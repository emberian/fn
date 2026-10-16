# OWED: the proof-debt ledger of cut/breaking

Ledger, not gate (CUT-LEAD-20261016 §5). Every theorem or book deleted or
broken on this branch gets a row: the claim it carried, where it lived, and
the replacement path (or "none: the code it was about is gone"). ACL2
certification runs for information. A book that no longer certifies and is
not on the survivors list is deleted, not repaired; a survivor book that
breaks gets a one-line hint repair when that is cheap, else a red row here
and the work continues. The 5.4 series picks this ledger up.

Rows are appended by the commit that creates the debt, one line each,
newest last. `G4` is the line `tools/cut_measure.sh` printed for that commit.

| commit | book or theorem | claim it carried | replacement path | state |
|---|---|---|---|---|
