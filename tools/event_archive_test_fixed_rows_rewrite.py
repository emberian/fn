"""Compose the later fixed-row program transformation into exact replay tests."""
import ast


def rewrite(source, name):
    if 'import event_archive_fixed_rows_rewrite as fixed' in source:
        return source
    lines=source.splitlines(keepends=True);starts=[];offset=0
    for line in lines:
        starts.append(offset);offset+=len(line)
    edits=[]
    for node in ast.walk(ast.parse(source)):
        if not isinstance(node,(ast.Call,ast.IfExp)):continue
        text=ast.get_source_segment(source,node)
        selected=(name=='event_archive_member_rewrite_test.py' and isinstance(node,ast.Call) and
                  isinstance(node.func,ast.Attribute) and
                  isinstance(node.func.value,ast.Name) and node.func.value.id=='rw' and
                  node.func.attr in ('cursor','boot'))
        selected|=(name=='event_archive_frontier_begin_rewrite_test.py' and
                   text=="member.cursor(after) if name=='cursor' else after")
        selected|=(name=='event_archive_visit_rewrite_test.py' and
                  (text=='member.boot(after)' or
                   text=="member.cursor(before) if path=='event-archive-cold-cursor' else before"))
        if selected:
            start=starts[node.lineno-1]+node.col_offset
            end=starts[node.end_lineno-1]+node.end_col_offset
            edits.append((start,end,'fixed.rewrite('+text+')'))
    expected={'event_archive_member_rewrite_test.py':4,
              'event_archive_frontier_begin_rewrite_test.py':1,
              'event_archive_visit_rewrite_test.py':2}[name]
    if len(edits)!=expected:raise ValueError('replay-test source drift')
    for start,end,text in sorted(edits,reverse=True):source=source[:start]+text+source[end:]
    return source.replace('import lisp_rewrite as lr\n',
        'import lisp_rewrite as lr\nimport event_archive_fixed_rows_rewrite as fixed\n',1)
