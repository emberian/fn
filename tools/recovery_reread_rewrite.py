"""Scoped Lisp-symbol rename for the shared payload/replay reread helper class."""
from pathlib import Path
from lisp_rewrite import Atom, Lst, Pre, Str, match, parse, write
RENAMES = {
 'fn2-rp-replay-row-p': 'fn2-rp-current-unit-row-p',
 'fn2-rp-replay-auth-p': 'fn2-rp-current-unit-auth-p',
 'fn2-recovery-replay-open': 'fn2-recovery-current-unit-open',
}
def rewrite(text):
    parsed = parse(text)
    edits = []
    def visit(node):
        if isinstance(node, Lst):
            for item in node.items: visit(item)
        elif isinstance(node, Pre): visit(node.node)
        elif isinstance(node, Atom) and not isinstance(node, Str) and node.low in RENAMES:
            edits.append((node.start, node.end, RENAMES[node.low]))
    for form in parsed.forms: visit(form)
    return write(text, edits)
def install_digest_fields(text):
    parsed = parse(text)
    if match('(rc-auth-h0 :u32)', parsed.forms):
        return text
    hits = match('(rc-auth-roff :u32)', parsed.forms)
    if len(hits) != 1:
        raise ValueError('expected one actual recovery auth range field')
    fields = ' '.join(f'(rc-auth-h{i} :u32)' for i in range(8))
    return write(text, [(hits[0].start, hits[0].start, fields + '\n          ')])

if __name__ == '__main__':
    path = Path('books/recovery-payload.lisp')
    path.write_text(rewrite(path.read_text()))
    fields = Path('books/machines-b.lisp')
    fields.write_text(install_digest_fields(fields.read_text()))
