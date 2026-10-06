"""The shared rule for every baseline-rewriting tool: a baseline only SHRINKS.

A tool's ``--write`` (``--write-baseline``, ``--baseline``) may lower a row or
drop it; it may not raise a row or add one unless the tree's
planning/repair/ACKS.md carries a line naming it:

    ratchet:<tool>:<row> <em dash> reason <em dash> who/what un-parks it

``<tool>`` is the tool's module name (``loop_call_check``) and ``<row>`` the
baseline row key (a file path, a book, a name; spaces written as ``_``).  The
ACK is the written decision; the same commit that raises the baseline adds it,
because the tool reads the tree it is run in.  No baseline file yet (``old is
None``) is the one initial capture and is allowed.  Semantics follow
tools/lock_discipline_check.py's write_baseline (``grown``), which refuses to
raise; the ACK line is the only way past, never a flag.

``refused(tool, old, new)`` returns the rows a write must not make, each with
the token that would let it through.  ``scaling_limit`` is the same rule for
tools/scaling_baseline.json: the declared target is the ceiling, and a
ceiling above it needs an ACK.
"""
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
ACKS = ROOT / "planning/repair/ACKS.md"
DASH = "—"


def token(tool, row):
    return f"ratchet:{tool}:{str(row).replace(' ', '_')}"


def acked(acks=None):
    """The set of ratchet ids with a well-formed ACK line; none if unreadable."""
    try:
        text = Path(acks or ACKS).read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError):
        return set()
    out = set()
    for line in text.splitlines():
        parts = [p.strip() for p in line.split(DASH)]
        if len(parts) == 3 and all(parts) and parts[0].startswith("ratchet:") and " " not in parts[0]:
            out.add(parts[0])
    return out


def refused(tool, old, new, acks=None):
    """Rows `new` raises or adds over `old` with no ACK; [] for an initial capture."""
    if old is None:
        return []
    ok = acked(acks)
    out = []
    for row in sorted(new):
        raised = new[row] > old.get(row, 0) if row in old else new[row] > 0
        if raised and token(tool, row) not in ok:
            out.append(f"{row}: {old.get(row, 'absent')} -> {new[row]} (needs an ACKS.md line "
                       f"'{token(tool, row)} {DASH} reason {DASH} who/what un-parks it')")
    return out


def report(tool, rows):
    """Print the refusal; True when there is one."""
    if rows:
        print(f"{tool}: refusing to raise the baseline (it only shrinks):")
        for r in rows[:20]:
            print("  " + r)
    return bool(rows)


def scaling_limit(baseline, acks=None):
    """The ratio the scaling gate enforces: the target, or the ceiling if ACKed."""
    target, ceiling = baseline["article_ratio_target"], baseline["article_ratio_ceiling"]
    if ceiling > target and token("scaling_baseline", "article_ratio_ceiling") in acked(acks):
        return ceiling
    return target
