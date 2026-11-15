# Exact checkpoint planning — source state

Owner: Sol capacity lane. Source only; no ACL2 execution/certification, runtime
activation, or full maintenance-progress claim follows from these changes.

The actual master enters allocator phase3 after C closes/drains and owns the
27 working leases and real descriptor reservation. Phase3 preserves phase1
map-copy and phase2 installation meanings. Ordinary allocator mutation and B
member admission remain closed. The owner-scoped reserve/cancel calls use the
same allocator transition bodies as ordinary calls.

Root1 preview and materialization use the same entry codecs, room predicate,
restart arithmetic, bounded builder work, sealing, promotion and manifest
fields. Preview records identities/layout/hash in private recipe tables;
it never installs physical completion or publication authority. Root1's
first-pass empty directory still goes through the actual special finish/page
producer. A changed second-pass layout/hash refuses before physical issue.

After preview, one ticket-demand fixedpoint iteration runs per turn. Demand
uses actual root1 pages plus the descriptor, actual cut-derived event pages,
frontier, E-derived map pages and ticket-derived arena pages. A second bounded
phase walks one free link per suffix identity, in actual producer order:
role3 descending ordinal, role4, role2, role5, role6. Builder, fixed-slot and
journal-ticket recipe modes are explicit; fixed slots have no invented seal.
Actual event and plan reservation producers consume the same identity provider.

The directory check uses actual PROPOSED via commit-directory-headroom and
requires the exact settled C cut. Refusal distinguishes changed cut, invalid
directory state and insufficient rows. Phase3 owns this interval: ordinary
keyed/transaction admission is frozen; raw commit-start's maintenance route
requires phase2 in future-bind and ticket-take; ordinary retirement admission
refuses an active checkpoint. The recipe is checked again at materialization
and full consumption before phase1. No stale count is accepted as a lease.

Cancellation scans one actual candidate construction row per call. Only exact
unissued/uncompleted/unclaimed reservations can cancel. Actual page BIND marks
possible IO before worker handoff; possible issue stops the core for recovery
and retains protection. CANCEL-EMPTY keeps phase3 closed. Candidate/build/ref
cleanup and source-cursor reset belong to their owners before internal planning
end and normal snapshot/27-lease cleanup; no generic thaw was added here.

Prepared controls: checkpoint-planning-unit (real empty-directory builder twice,
stale cut/frontier/owner, changed bytes, pins and cancellation), schedule-unit
(actual fixedpoint expansion from explicit synthetic arithmetic inputs), and
commit-frozen-admission-unit (actual phase3 generic/raw/retirement refusal).
These ACL2 fixtures are unexecuted. Python source-boundary/rewrite controls,
source arity/MV checks, reader, structural and secrets checks were run.

## Remaining admission work

Exact HELD planning is insufficient if foreground storage already consumed its
space. Foreground admission still needs an owner-sensitive maintenance credit
and a proved mutation-growth envelope before durable acceptance. Directory
lifetime exhaustion also remains real; no speculative rebase credit is used.

Actual mutation map: successor STAGE precedes B admission; bind-slot writes
through ov-insert into batch-private overlays; publish-overlays freezes those
sources. Published successor sources are immutable. Sealer run-install,
install-filter, install-range, retire and reclaim change the resident source
catalog. Group bootstrap inserts are a separate startup mutation path.

A useful next design is per-source generation-bound packing provenance,
updated at those producers, with exact pre-admission forecast of only changed
private sources and the source-directory entries. Overlay FILL is unsuitable:
replacement leaves dead arena bytes; the live index is authoritative. Existing
immutable leaf packing is independent of new physical Ref identities, but
parent index/directory packing is not. Globally ordered new identities can
cross varint boundaries when a source is inserted. Cached page counts alone
are therefore insufficient. Stable per-source/level credit identities or a
same-builder index/directory forecast is required before using such a cache as
admission authority. No new aggregate or growth bound is implemented from this
observation. The current global planning identity provider must not be silently
replaced by guessed per-source counts or entries-times-levels arithmetic.
