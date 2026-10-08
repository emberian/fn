"""Structural transformation used to split the completion history readers.

Only executable calls and guard calls change. Each generated definition is
paired with an admitted equality in history-served-finish.lisp; this utility
neither generates proof claims nor treats a transformation as a proof.
"""
from lisp_rewrite import Atom, Lst, Pre, parse, write


def replace_calls(text, mapping, formals, stobj='fn-hist'):
    """Rename mapped calls and append the resident stobj when newly needed."""
    tree = parse(text)
    edits = []

    def walk(node):
        if isinstance(node, Pre):
            if node.prefix != "'":
                walk(node.node)
            return
        if not isinstance(node, Lst) or not node.items:
            return
        head = node.items[0]
        if isinstance(head, Atom) and head.low == 'quote':
            return
        if isinstance(head, Atom) and head.low in mapping:
            edits.append((head.start, head.end, mapping[head.low]))
            if stobj not in formals[head.low]:
                edits.append((node.end - 1, node.end - 1, ' ' + stobj))
        for child in node.items:
            walk(child)

    for node in tree.forms:
        walk(node)
    return write(text, edits)


def carried_exec_definition(text, carried_guard, exec_mapping=None):
    """Add a carried guard and, optionally, an MBE execution-only substitution.

    The logical body remains byte-for-byte intact. ACL2 must verify the MBE
    equality under the new guard; the transformer grants no proof authority.
    """
    tree = parse(text)
    form = tree.forms[0]
    declaration = form.items[3]
    xargs = declaration.items[1]
    guard_index = next(i for i, n in enumerate(xargs.items)
                       if isinstance(n, Atom) and n.low == ':guard') + 1
    guard = xargs.items[guard_index]
    edits = [(guard.start, guard.end,
              '(and ' + text[guard.start:guard.end] + ' ' + carried_guard + ')')]
    if exec_mapping:
        body = form.items[-1]
        original = text[body.start:body.end]
        # These replacements have the same arity. Suppress stobj insertion.
        executed = replace_calls(original, exec_mapping,
                                 {n: ['fn-hist'] for n in exec_mapping})
        edits.append((body.start, body.end,
                      '(mbe :logic ' + original + '\n       :exec ' + executed + ')'))
    return write(text, edits)


def replace_dispatch_targets(text, dispatcher, mapping):
    """Change only literal quoted targets at the named native dispatcher."""
    edits = []

    def walk(node):
        if isinstance(node, Pre):
            return
        if not isinstance(node, Lst):
            return
        if (len(node.items) > 1 and isinstance(node.items[0], Atom)
                and node.items[0].low == dispatcher):
            target = node.items[1]
            if (isinstance(target, Pre) and target.prefix == "'"
                    and isinstance(target.node, Atom)
                    and target.node.low in mapping):
                edits.append((target.node.start, target.node.end,
                              mapping[target.node.low]))
        for child in node.items:
            walk(child)

    for form in parse(text).forms:
        walk(form)
    return write(text, edits)
