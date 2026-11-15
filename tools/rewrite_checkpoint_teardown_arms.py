"""Scoped Lisp-AST continuation rewrite for the actual retained teardown actor."""
from pathlib import Path
import argparse
import lisp_rewrite as lr

PHASES = (':teardown-transfer-begin', ':teardown-transfer-copy', ':teardown-select')

def rewrite(text):
    if '(:teardown-transfer-copy :on-refusal' in text:
        return text, 0
    s=text.replace('(include-book "checkpoint-teardown")','(include-book "checkpoint-teardown-sweep")');edits=[]
    for phase in [':idle',':snapshot-release',':teardown-begin',':teardown-source',':teardown-submit',':teardown-wait',':teardown-drop',':teardown-retained']:
     m=lr.match('('+phase+' ?*body)',lr.parse(s).forms,deep=True)
     m=[x for x in m if len(x.captures['body'])>0][0];old=s[m.node.start:m.node.end];out=old
     if phase==':idle':
      out='''(:idle :on-refusal ((:next :uncertain) (:charge :steps *fn2-work-small* :runnable t))
       (:if *fn2-checkpoint-activation-qualified*
        ((:do (notify cleanup) (fn2-checkpoint-teardown-needed-op))
         (:if cleanup
          ((:do (begin) (fn2-checkpoint-teardown-sweep-begin-op id row-generation) :accept (:more))
           (:set (debt-scan 0) (scan 0)) (:next :teardown-select) (:charge :steps *fn2-work-stage* :runnable t))
          ((:do (code needed retirement) (fn2-checkpoint-master-pressure-op row-retirement-seen))
           (:if needed
            ((:set (scan 0) (highest 0) (candidate 0) (candidate-found 0))
             (:next :catalog) (:charge :steps *fn2-work-small* :runnable t))
            ((:park :checkpoint-needed))))))
        ((:next :disabled) (:charge :steps *fn2-work-small*))))'''
     elif phase==':snapshot-release':out=out.replace('(:next :teardown-begin)','(:next :teardown-transfer-begin)')
     elif phase==':teardown-begin':out='''(:teardown-begin (:set (scan 0) (debt-scan 0)) (:next :teardown-select) (:charge :steps *fn2-work-small* :runnable t))'''
     elif phase==':teardown-source':
      out=out.replace('fn2-checkpoint-teardown-inspect-op row-token','fn2-checkpoint-teardown-inspect-op row-debt-scan row-token')
      out=out.replace('((:none) (:next :done)', '((:none) (:next :teardown-retained)')
     elif phase==':teardown-submit':
      out=out.replace('fn2-checkpoint-teardown-submit row-token','fn2-checkpoint-teardown-submit row-debt-scan row-token')
      out=out.replace('((:busy :exhausted) (:yield))','((:busy :exhausted) (:park :checkpoint-needed))')
     elif phase==':teardown-wait':out=out.replace('fn2-checkpoint-teardown-poll *fn2-checkpoint-master-kind*','fn2-checkpoint-teardown-poll row-debt-scan row-token *fn2-checkpoint-master-kind*')
     elif phase==':teardown-drop':out=out.replace('fn2-checkpoint-teardown-drop-op row-token','fn2-checkpoint-teardown-drop-op row-debt-scan row-token')
     elif phase==':teardown-retained':out='''(:teardown-retained
       (:if (< row-debt-scan *fn2-alloc-none*)
        ((:set (debt-scan (+ 1 row-debt-scan)) (scan 0)) (:next :teardown-select)
         (:charge :steps *fn2-work-small* :runnable t))
        ((:next :teardown-uncertain) (:charge :steps *fn2-work-small* :runnable t))))'''
     edits.append((m.node.start,m.node.end,out))
    addition='''
      (:teardown-transfer-begin :on-refusal ((:next :teardown-uncertain) (:charge :steps *fn2-work-small* :runnable t))
       (:do (code candidate) (fn2-checkpoint-teardown-transfer-begin-op row-token *fn2-checkpoint-master-kind* id row-generation)
        :accept () :case
        (((:none) (:next :done) (:charge :steps *fn2-work-small* :runnable t))
         ((:copy :duplicate) (:set (debt-scan candidate)) (:next :teardown-transfer-copy) (:charge :bytes 160 :steps *fn2-work-stage* :runnable t))
         (:otherwise (:next :teardown-uncertain) (:charge :steps *fn2-work-small* :runnable t)))))
      (:teardown-transfer-copy :on-refusal ((:next :teardown-uncertain) (:charge :steps *fn2-work-small* :runnable t))
       (:do (code) (fn2-checkpoint-teardown-transfer-step-op row-debt-scan row-token *fn2-checkpoint-master-kind* id row-generation)
        :accept () :case
        (((:more) (:charge :bytes 4 :steps *fn2-work-stage* :runnable t))
         ((:transferred) (:next :done) (:charge :bytes 160 :steps *fn2-work-stage* :runnable t))
         (:otherwise (:next :teardown-uncertain) (:charge :steps *fn2-work-small* :runnable t)))))
      (:teardown-select :on-refusal ((:next :teardown-uncertain) (:charge :steps *fn2-work-small* :runnable t))
       (:do (code next token extent epoch allocation batch event phase)
        (fn2-checkpoint-teardown-select-op row-debt-scan *fn2-checkpoint-master-kind* id row-generation)
        :accept () :case
        (((:more) (:set (debt-scan next)) (:charge :steps *fn2-work-small* :runnable t))
         ((:done) (:next :done) (:charge :steps *fn2-work-small* :runnable t))
         ((:source) (:set (token token) (scan 0)) (:next :teardown-source) (:charge :steps *fn2-work-stage* :runnable t))
         ((:drop) (:set (token token) (teardown-extent extent) (teardown-epoch epoch) (teardown-allocation allocation) (batch batch) (event event))
          (:next :teardown-drop) (:charge :steps *fn2-work-stage* :runnable t))
         (:otherwise (:next :teardown-uncertain) (:charge :steps *fn2-work-small* :runnable t)))))
    '''
    m=[x for x in lr.match('(:teardown-begin ?*body)',lr.parse(s).forms,deep=True) if len(x.captures['body'])>0][0];edits.append((m.node.start,m.node.start,addition+'\n  '))
    s=lr.write(s,edits);lr.parse(s);return s,len(edits)

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    path = Path(__file__).resolve().parents[1] / 'books/checkpoint-master-arms.lisp'
    out, count = rewrite(path.read_text())
    print('retained teardown continuation seams:', count)
    if args.write:
        path.write_text(out)
