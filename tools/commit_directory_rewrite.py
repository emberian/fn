"""Scoped concrete commit-directory index migration; no Lisp is evaluated."""
import lisp_rewrite as lr

def replace_batch_indices(text,scope,heads,expected_index,replacement,expected_count):
    parsed=lr.parse(text)
    scopes=lr.match('(defun ?name ?*body)',parsed.forms,name=scope)
    if len(scopes)!=1:raise ValueError(f'{scope}: expected one definition, found {len(scopes)}')
    region=scopes[0];edits=[]
    for head in heads:
        for match in lr.match('(?*xs)',parsed.forms,head=head):
            if not(region.start<=match.start and match.end<=region.end):continue
            arg=match.node.items[1];source=text[arg.start:arg.end]
            if source=='0':continue
            if source!=expected_index:raise ValueError(f'{scope}/{head}: unexpected batch index {source!r}')
            edits.append((arg.start,arg.end,replacement))
    if len(edits)!=expected_count:raise ValueError(f'{scope}: expected {expected_count} replacements, found {len(edits)}')
    return lr.write(text,edits)
