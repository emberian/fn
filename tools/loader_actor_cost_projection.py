"""Project only root1 source/consume byte charges; other master states stay intact."""
from pathlib import Path
import sys
import lisp_rewrite as lr
TURN='*fn2-checkpoint-root1-turn-bytes*'
def transform(text):
 parsed=lr.parse(text)
 source=lr.match('(:root1-source ?*body)',parsed.forms,deep=True)
 consume=lr.match('(:page-consume ?*body)',parsed.forms,deep=True)
 if len(source)!=1 or len(consume)!=1:raise ValueError('Expected actual unique root1 source and page consume arms')
 branches=lr.match('((equal row-source 1) ?*body)',[consume[0].node],deep=True)
 if len(branches)!=1:raise ValueError('Expected actual root1 page consumer branch')
 edits=[]
 for parent in [source[0].node,branches[0].node]:
  for m in lr.match('(:charge :bytes ?bytes ?*tail)',[parent],deep=True):
   value=m.captures['bytes']
   if isinstance(value,lr.Atom) and value.low=='4096':edits.append((value.start,value.end,TURN))
   elif not isinstance(value,lr.Atom) or value.low!=TURN:raise ValueError('Unreviewed byte charge')
 if len(edits) not in (0,6):raise ValueError('Expected six root1 charge sites')
 return lr.write(text,edits)
if __name__=='__main__':
 p=Path(sys.argv[1]);p.write_text(transform(p.read_text()))
