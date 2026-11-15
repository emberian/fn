"""Connect only the named physical-anchor transfer continuation class."""
from pathlib import Path
import argparse
import lisp_rewrite as lr
PHASES = (':teardown-cold-next', ':teardown-cold-begin', ':teardown-cold-copy', ':teardown-cold-ack')
ARMS = '''
  (:teardown-cold-next :on-refusal ((:next :teardown-uncertain) (:charge :steps *fn2-work-small* :runnable t))
   (:do (code next physicalslot) (fn2-checkpoint-teardown-cold-next-op row-scan) :accept () :case
    (((:pending) (:set (scan next) (source physicalslot)) (:next :teardown-cold-begin) (:charge :steps *fn2-work-stage* :runnable t))
     ((:more) (:set (scan next)) (:charge :steps *fn2-work-small* :runnable t))
     ((:end) (:next :done) (:charge :steps *fn2-work-small* :runnable t))
     (:otherwise (:next :teardown-uncertain) (:charge :steps *fn2-work-small* :runnable t)))))
  (:teardown-cold-begin :on-refusal ((:next :teardown-uncertain) (:charge :steps *fn2-work-small* :runnable t))
   (:do (code candidate) (fn2-checkpoint-teardown-cold-begin-op row-source row-token *fn2-checkpoint-master-kind* id row-generation) :accept () :case
    (((:copy) (:set (debt-scan candidate)) (:next :teardown-cold-copy) (:charge :bytes 192 :steps *fn2-work-stage* :runnable t))
     ((:copied) (:set (debt-scan candidate)) (:next :teardown-cold-ack) (:charge :bytes 192 :steps *fn2-work-stage* :runnable t))
     (:otherwise (:next :teardown-uncertain) (:charge :steps *fn2-work-small* :runnable t)))))
  (:teardown-cold-copy :on-refusal ((:next :teardown-uncertain) (:charge :steps *fn2-work-small* :runnable t))
   (:do (code) (fn2-checkpoint-teardown-cold-step-op row-source row-debt-scan row-token *fn2-checkpoint-master-kind* id row-generation) :accept () :case
    (((:more) (:charge :bytes 4 :steps *fn2-work-stage* :runnable t))
     ((:copied) (:next :teardown-cold-ack) (:charge :bytes 192 :steps *fn2-work-stage* :runnable t))
     (:otherwise (:next :teardown-uncertain) (:charge :steps *fn2-work-small* :runnable t)))))
  (:teardown-cold-ack :on-refusal ((:next :teardown-uncertain) (:charge :steps *fn2-work-small* :runnable t))
   (:do (code) (fn2-checkpoint-teardown-cold-ack-op row-source) :accept (:transferred))
   (:next :teardown-cold-next) (:charge :bytes 192 :steps *fn2-work-stage* :runnable t))
'''

def kind(text):
    edits=[]
    for m in lr.match('(defmachine fn2-checkpoint-master ?*body)', lr.parse(text).forms, deep=False):
        xs=m.captures['body']
        for i,x in enumerate(xs[:-1]):
            key=getattr(x,'low','')
            if key not in (':states',':arms'):
                continue
            seq=xs[i+1]
            names={getattr(y,'low','') if isinstance(y,lr.Atom) else getattr(y.items[0],'low','') for y in seq.items}
            if all(x in names for x in PHASES):
                continue
            if any(x in names for x in PHASES):
                raise ValueError('partial cold continuation class')
            added=' '.join(PHASES) if key==':states' else ' '.join('('+x+')' for x in PHASES)
            edits.append((seq.end-1,seq.end-1,'\n          '+added))
    return lr.write(text,edits),len(edits)


def arms(text):
    if '(:teardown-cold-copy :on-refusal' in text:
        return text,0
    edits=[]
    for phase in (':teardown-transfer-begin',':teardown-transfer-copy'):
        matches=lr.match('('+phase+' :on-refusal ?*body)',lr.parse(text).forms,deep=True)
        if len(matches)!=1:
            raise ValueError('Require exact existing runtime transfer arm: '+phase)
        node=matches[0].node
        src=text[node.start:node.end]
        if src.count('(:next :done)') != 1:
            raise ValueError('Ambiguous runtime terminal')
        out=src.replace('(:next :done)', '(:set (scan 0)) (:next :teardown-cold-next)')
        if out==src:
            raise ValueError('Missing exact runtime terminal')
        edits.append((node.start,node.end,out))
        if phase==':teardown-transfer-copy':
            edits.append((node.end,node.end,'\n'+ARMS))
    for m in lr.match('(include-book "checkpoint-teardown-sweep")',lr.parse(text).forms,deep=False):
        edits.append((m.node.end,m.node.end,'\n(include-book "checkpoint-teardown-cold-transfer")\n(include-book "checkpoint-bank-transfer")'))
    out=lr.write(text,edits)
    lr.parse(out)
    return out,len(edits)

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--write',action='store_true')
    args=p.parse_args()
    root=Path(__file__).resolve().parents[1]
    for name,fn in [('checkpoint-master-state',kind),('checkpoint-master-arms',arms)]:
        path=root/'books'/f'{name}.lisp'
        out,n=fn(path.read_text())
        print(name,n)
        if args.write:path.write_text(out)
