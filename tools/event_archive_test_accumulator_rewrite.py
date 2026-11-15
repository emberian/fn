"""Compose accumulator binding after prior exact-replay recipe stages."""
import ast


def rewrite(source,name):
    if 'import event_archive_accumulator_rewrite as acc' in source:return source
    starts=[];offset=0
    for line in source.splitlines(keepends=True):starts.append(offset);offset+=len(line)
    edits=[]
    for n in ast.walk(ast.parse(source)):
        if not isinstance(n,ast.Call) or not isinstance(n.func,ast.Attribute):continue
        if not isinstance(n.func.value,ast.Name):continue
        owner=n.func.value.id;method=n.func.attr;kind=None
        if owner=='fixed' and method=='rewrite':
            if name=='event_archive_member_rewrite_test.py':
                kind=repr(n.args[0].func.attr)
            elif name=='event_archive_frontier_begin_rewrite_test.py':kind='name'
            elif name=='event_archive_reach_bind_rewrite_test.py':kind="'boot'"
            elif name=='event_archive_visit_rewrite_test.py':
                kind="'boot'" if isinstance(n.args[0],ast.Call) else 'path'
        elif name=='event_archive_reach_bind_rewrite_test.py' and owner=='member' and method=='boot':kind="'boot'"
        if kind:
            text=ast.get_source_segment(source,n)
            edits.append((starts[n.lineno-1]+n.col_offset,starts[n.end_lineno-1]+n.end_col_offset,
                          'acc.project('+kind+', '+text+')'))
    expected={'event_archive_member_rewrite_test.py':4,
              'event_archive_frontier_begin_rewrite_test.py':1,
              'event_archive_visit_rewrite_test.py':2,
              'event_archive_reach_bind_rewrite_test.py':2}[name]
    if len(edits)!=expected:raise ValueError('accumulator replay source drift')
    for a,b,text in sorted(edits,reverse=True):source=source[:a]+text+source[b:]
    if name=='event_archive_member_rewrite_test.py':
        old="self.assertEqual(len(calls(s,'(assert-event (fn2-eamcu-test ?fault))')),5)"
        if source.count(old)!=1:raise ValueError('member fixture assertion count drift')
        source=source.replace(old,old[:-2]+'7)',1)
    return source.replace('import lisp_rewrite as lr\n',
                         'import lisp_rewrite as lr\nimport event_archive_accumulator_rewrite as acc\n',1)
