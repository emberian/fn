#!/usr/bin/env python3
"""Apply REPL-checked -fast proposals to hints only; theorem text cannot change."""
from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import lisp_rewrite as lr


def transform(source, proposals):
    old = lr.parse(source)
    new = lr.parse(proposals)
    edits = []
    for m in lr.match("_", new.forms, head="defthm"):
        event = m.node
        name = event.items[1].low
        assert name.endswith("-fast"), name
        matches = lr.match("_", old.forms, head="defthm", name=name[:-5])
        assert len(matches) == 1, name
        target = matches[0].node
        assert lr.emit(event.items[2]) == lr.emit(target.items[2]), name
        assert len(event.items) == 5 and event.items[3].low == ":hints", name
        # These proposals have no rule-class changes or other event options.
        assert len(target.items) in (3, 5), name
        hint = proposals[event.items[4].start:event.items[4].end]
        if len(target.items) == 3:
            edits.append((target.end - 1, target.end - 1, "\n   :hints " + hint))
        else:
            assert target.items[3].low == ":hints", name
            edits.append((target.items[4].start, target.items[4].end, hint))
    return lr.write(source, edits), len(edits)


def fixtures():
    old = '(local (defthm probe (equal x x) :hints (("Goal" :in-theory nil))))\n'
    proposal = '(local (defthm probe-fast (equal x x) :hints (("Goal" :in-theory t))))\n'
    new, count = transform(old, proposal)
    assert count == 1 and new == old.replace(':in-theory nil', ':in-theory t')
    assert transform(new, proposal) == (new, 1)
    bare = '(local (defthm probe (equal x x)))\n'
    added, n = transform(bare, proposal)
    assert n == 1 and ':hints' in added
    assert transform(added, proposal) == (added, 1)
    try:
        transform(old, proposal.replace('(equal x x)', '(equal x y)'))
    except AssertionError:
        pass
    else:
        raise AssertionError('changed theorem must be refused')


if __name__ == '__main__':
    fixtures()
    path = Path('books/post-header-local.lisp')
    proposals = Path(sys.argv[1]).read_text()
    new, count = transform(path.read_text(), proposals)
    assert count == 6, count
    lr.parse(new)
    path.write_text(new)
    print(f'{path}: {count} hint replacements; statements identical')
