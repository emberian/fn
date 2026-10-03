"""Bind an actual loaded-world signature dump to its recorded source inputs.

BINDING is supplied by the owner image/admission run, never manufactured from
current files after the fact: {world_coordinate, source_files:{path:sha256}}.
The dump may contain additional touched callees outside selected source files;
those must be added before thread.prepare can produce a complete output.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
from . import sexp
from .thread import Refused


def atom(node):
    if node.kind != 'atom':
        raise Refused('world dump: expected an atom')
    result = node.val.lower()
    if result.startswith('acl2::'):
        result = result[6:]
    if result.startswith('"'):
        raise Refused('world dump: unexpected string in function signature')
    return result


def symbols(node, nil_is_empty=False):
    if nil_is_empty and node.kind == 'atom' and atom(node) == 'nil':
        return []
    if node.kind != 'list':
        raise Refused('world dump: expected a signature list')
    return [atom(kid) for kid in node.kids]


def bind(dump, binding):
    if not binding.get('world_coordinate') or not binding.get('source_files'):
        raise Refused('a recorded world coordinate and exact source inputs are required')
    if any(not isinstance(path,str) or not isinstance(digest,str) or
           len(digest) != 64 or any(c not in '0123456789abcdef' for c in digest)
           for path,digest in binding['source_files'].items()):
        raise Refused('invalid recorded source hash')
    forms = sexp.read_all(dump)
    if len(forms) != 1 or forms[0].kind != 'list':
        raise Refused('world dump must contain one complete data object')
    children = forms[0].kids
    if len(children) != 4 or atom(children[0]) != ':direct' or atom(children[2]) != ':functions':
        raise Refused('unrecognized loaded-world signature dump')
    direct = symbols(children[1], True)
    functions = {}
    rows = children[3]
    if rows.kind != 'list':
        raise Refused('world dump has no function rows')
    for row in rows.kids:
        if row.kind != 'list' or len(row.kids) != 6:
            raise Refused('world dump: malformed function row')
        name = atom(row.kids[0])
        if name in functions:
            raise Refused(f'world dump: duplicate function {name}')
        formals=symbols(row.kids[1], True)
        ins=symbols(row.kids[2], True)
        outs=symbols(row.kids[3], True)
        if len(formals) != len(ins) or ins.count('state') != 1:
            raise Refused(f'world dump: incompatible state signature for {name}')
        writer=atom(row.kids[5])
        if writer not in ('t','nil') or (writer=='t') != ('state' in outs):
            raise Refused(f'world dump: writer/output disagreement for {name}')
        functions[name]=dict(formals=formals,
                             ins=[None if x=='nil' else x for x in ins],
                             outs=[None if x=='nil' else x for x in outs],
                             writer=writer=='t',touch=True,
                             source_class=atom(row.kids[4]))
    if not set(direct).issubset(functions):
        raise Refused('direct authority access is absent from closure rows')
    return dict(schema='fn-owner-carrier-world-v1',
                world_coordinate=binding['world_coordinate'],
                source_files=binding['source_files'],direct=direct,functions=functions)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--world-dump',type=Path,required=True)
    parser.add_argument('--binding',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    try:
        snapshot=bind(args.world_dump.read_text(),json.loads(args.binding.read_text()))
        # Exclusive creation keeps an earlier snapshot and every input intact.
        with args.output.open('x') as output:
            json.dump(snapshot,output,indent=2);output.write('\n')
    except (Refused,ValueError,KeyError,OSError) as error:
        parser.exit(2,f'owner-carrier snapshot: refused: {error}\n')

if __name__=='__main__':main()
