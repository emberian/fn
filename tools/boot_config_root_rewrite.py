"""Move the actual ROOT boot declaration to its shared lower state boundary."""
import lisp_rewrite as lr

def project(text):
    edits=[]
    for pattern in ('(defconst *fn2-boot-group-entry-bytes* ?*body)',
                    '(defcolumns fn2-boot-config ?*body)'):
        ms=lr.match(pattern,lr.parse(text).forms,deep=False)
        if len(ms)>1:raise ValueError('duplicate actual declaration')
        for m in ms:edits.append((m.node.start,m.node.end,''))
    text=lr.write(text,edits)
    if '(include-book "boot-config-state")' not in text:
        n=lr.match('(fn2-book-layer :b)',lr.parse(text).forms,deep=False)
        if len(n)!=1:raise ValueError('one actual lower BOOT declaration layer')
        text=lr.write(text,[(n[0].node.start,n[0].node.start,'(include-book "boot-config-state")\n')])
    return text
