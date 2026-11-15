#!/usr/bin/env python3
"""Repair the two endpoint carriers' actual generated PUT macro call class.

Columns PUT takes (row (field expression) ...), implicitly threading its named
stobj. Convert the old function-shaped quoted/backquoted alist without changing
field evaluation order or the expressions inside top-level unquotes. Refuse
splices, nested unquotes, comments and malformed fields rather than guess.
"""
from pathlib import Path
import argparse
from lisp_rewrite import parse,match,write,Atom,Str,Lst,Pre,NUMBER
FIELDS={
 'fn2-c-source-control':{'phase','readers','next-receipt','writer-kind','writer-owner','writer-gen','writer-token','cut-commit','cut-event','wake-pending'},
 'fn2-c-source-readers':{'live','serial'},
}
def fieldpair(node, allowed):
 if not isinstance(node,Lst) or len(node.items)!=2 or not isinstance(node.items[0],Atom) or node.items[0].low not in allowed:
  raise ValueError('PUT requires exactly one declared field and expression per pair')
 return node.items

def transform(text):
 edits=[]
 for table,allowed in FIELDS.items():
  op=table+'-put'
  for found in match(f'({op} ?*args)',parse(text).forms):
   node=found.node
   if len(node.items)==4 and isinstance(node.items[-1],Atom) and node.items[-1].low==table:
    quoted=node.items[2]
    if not isinstance(quoted,Pre) or quoted.prefix not in ("'",'`') or not isinstance(quoted.node,Lst) or quoted.node.has_comment:
     raise ValueError('old PUT must carry a simple quoted/backquoted alist')
    pairs=[];seen=set()
    for pair in quoted.node.items:
     field,value=fieldpair(pair,allowed)
     if field.low in seen:raise ValueError('duplicate PUT field')
     seen.add(field.low)
     if isinstance(value,Pre) and value.prefix==',' and quoted.prefix=='`':
      expr=text[value.node.start:value.node.end]
     else:
      raw=text[value.start:value.end]
      if ',' in raw:raise ValueError('nested unquote is outside this repair class')
      expr=raw if isinstance(value,Str) or (isinstance(value,Atom) and (NUMBER.fullmatch(value.text) or value.text.startswith('#\\'))) else "'"+raw
     pairs.append('('+field.text+' '+expr+')')
    row=node.items[1]
    edits.append((node.start,node.end,'('+op+' '+text[row.start:row.end]+'\n        '+'\n        '.join(pairs)+')'))
   else:
    if len(node.items)<3:raise ValueError('PUT has no field pairs')
    seen=set()
    for pair in node.items[2:]:
     field,value=fieldpair(pair,allowed)
     if field.low in seen:raise ValueError('duplicate PUT field')
     seen.add(field.low)
 return write(text,edits),len(edits)

if __name__=='__main__':
 parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--write',action='store_true');parser.add_argument('files',nargs='+');args=parser.parse_args()
 for filename in args.files:
  p=Path(filename);before=p.read_text();after,n=transform(before)
  if args.write:p.write_text(after)
  elif n:raise SystemExit(f'{filename}: {n} old PUT forms require repair')
  print(f'{filename}: {n} repaired PUT forms')
