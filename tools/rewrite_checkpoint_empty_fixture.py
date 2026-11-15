#!/usr/bin/env python3
"""Scope the new explicit boot-obligation premise to existing typed tests."""
from pathlib import Path
from lisp_rewrite import parse,match,write
PATTERN='(fn2-checkpoint-publication-init 1 fn2-checkpoint-publication)'
REPLACEMENT='(fn2-checkpoint-test-empty-publication fn2-checkpoint-publication)'
def quoted(node):
    if hasattr(node,'prefix'):
        yield (node.start,node.end)
    elif hasattr(node,'items'):
        for x in node.items:yield from quoted(x)
def rewrite(source):
    parsed=parse(source)
    spans=[(m.start,m.end) for m in match('(quote ?*xs)',parsed.forms)]
    spans += [x for n in parsed.forms for x in quoted(n)]
    hits=[h for h in match(PATTERN,parsed.forms) if not any(a<=h.start<h.end<=b for a,b in spans)]
    if not hits:return source
    edits=[(h.start,h.end,REPLACEMENT) for h in hits]
    if '(include-book "checkpoint-bank-fixture")' not in source:
        package=match('(in-package "ACL2")',parsed.forms,deep=False)
        if len(package)!=1:raise ValueError('one ACL2 package required')
        edits.append((package[0].end,package[0].end,'\n(include-book "checkpoint-bank-fixture")'))
    return write(source,edits)
if __name__=='__main__':
    import sys
    for name in sys.argv[1:]:
        p=Path(name);s=p.read_text();out=rewrite(s)
        if out!=s:p.write_text(out)
        print(name+(': updated' if out!=s else ': unchanged'))
