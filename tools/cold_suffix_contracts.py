"""Generate shared cold settlement shape contracts from their actual wrappers."""
from lisp_rewrite import Atom, Lst, match, parse, write
MAPPING = {
 'fn2-checkpoint-suffix-allocation-begin': ('fn2-checkpoint-suffix-allocation-begin-record', 2, ' extent epoch allocation owner-kind owner'),
 'fn2-checkpoint-suffix-allocation-step': ('fn2-checkpoint-suffix-allocation-walk', 0, ''),
 'fn2-checkpoint-suffix-allocation-existing': ('fn2-checkpoint-suffix-allocation-existing-record', 1, ' e epoch allocation owner-kind owner'),
}
def extend(text):
    parsed = parse(text)
    contracts = []
    for node in parsed.forms:
        if (isinstance(node, Lst) and len(node.items) >= 3 and
            isinstance(node.items[0], Atom) and node.items[0].low.endswith('-preserves') and
            isinstance(node.items[1], Atom) and isinstance(node.items[2], Lst)):
            contracts.append(node)
    present = {(x.items[0].low, x.items[1].low) for x in contracts}
    additions = []
    for node in contracts:
        macro, function, args = node.items[:3]
        if function.low not in MAPPING: continue
        target, after, scalar_args = MAPPING[function.low]
        if (macro.low, target) in present: continue
        edits = [(function.start-node.start, function.end-node.start, target)]
        if scalar_args:
            at = args.items[after-1].end-node.start
            edits.append((at, at, scalar_args))
        additions.append(write(text[node.start:node.end], edits))
    return text + ('\n' + '\n'.join(additions) + '\n' if additions else '')
if __name__ == '__main__':
    from pathlib import Path
    for name in ('checkpoint-suffix-allocation', 'checkpoint-suffix-settlement'):
        path = Path('books') / (name+'.lisp')
        path.write_text(extend(path.read_text()))
