"""Bind owned stobj transitions before MV; do not emit raw calls as MV args."""
from pathlib import Path
import lisp_rewrite as lr


def transformed(text):
    edits = []
    def walk(node):
        if isinstance(node, lr.Lst):
            if node.items and getattr(node.items[0], 'text', '') == 'mv':
                last = node.items[-1]
                if isinstance(last, lr.Lst) and last.items and getattr(last.items[0], 'text', '') == 'fn2-release-live-uncertain':
                    args = text[node.items[0].end:last.start].strip()
                    call = text[last.start:last.end]
                    edits.append((node.start, node.end,
                                  '(let ((fn2-core '+call+')) (mv '+args+' fn2-core))'))
                    return
            for child in node.items:
                walk(child)
        elif isinstance(node, lr.Pre):
            walk(node.node)
    for form in lr.parse(text).forms:
        walk(form)
    for start, end, replacement in reversed(edits):
        text = text[:start]+replacement+text[end:]
    return text, len(edits)


if __name__ == '__main__':
    import argparse
    p = argparse.ArgumentParser()
    p.add_argument('source', type=Path)
    args = p.parse_args()
    result, count = transformed(args.source.read_text())
    args.source.write_text(result)
    print(count, 'owned stobj MV arguments bound')
