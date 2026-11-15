"""Canonical declaration inventory for source transformations and test snapshots."""
from pathlib import Path
import lisp_rewrite as lr
BOOKS={'fn2-run-installed':'books/runs.lisp','fn2-run-cache':'books/runs.lisp',
       'fn2-overlays':'books/overlay.lisp','fn2-pool':'books/pool.lisp','fn2-seals':'books/sealer.lisp'}
def one(pattern,source):
 found=lr.match(pattern,lr.parse(source).forms,deep=False)
 if len(found)!=1:raise ValueError('expected one '+pattern)
 return found[0].node
def from_books(sources):
 declarations={}
 for carrier,book in BOOKS.items():
  source=sources[book];node=one(f'(defcolumns {carrier} ?*args)',source)
  declarations[carrier]=source[node.start:node.end]
 return {'declarations':declarations}
def current(root):return from_books({book:(Path(root)/book).read_text() for book in set(BOOKS.values())})
def declaration(schema,carrier):return one(f'(defcolumns {carrier} ?*args)',schema['declarations'][carrier])
def columns(schema,carrier):return declaration(schema,carrier).items[2].items
def extra_fields(schema,carrier):
 n=declaration(schema,carrier)
 for i,item in enumerate(n.items):
  if getattr(item,'low',None)==':extra-fields':return n.items[i+1].items
 return []
def extras(schema,carrier):
 scalar=[];arrays=[]
 for field in extra_fields(schema,carrier):
  names=field.items;kind=next(names[i+1] for i,n in enumerate(names[:-1]) if getattr(n,'low',None)==':type')
  array=bool(getattr(kind,'items',None) and getattr(kind.items[0],'low',None)=='array')
  (arrays if array else scalar).append(names[0].low)
 return scalar,arrays
def has_physical(schema):
 matches=[c for c in columns(schema,'fn2-run-installed') if c.items[0].low=='physical']
 if not matches:return False
 if len(matches)!=1 or getattr(matches[0].items[1],'low',None)!=':bool':raise ValueError('physical fence requires canonical bool column')
 return True
def validate_before(before,schema):
 for carrier in ('fn2-run-installed','fn2-run-cache','fn2-seals'):
  source=before[BOOKS[carrier]];n=one(f'(defcolumns {carrier} ?*args)',source)
  if source[n.start:n.end]!=schema['declarations'][carrier]:raise ValueError('before-schema differs from actual '+carrier)
