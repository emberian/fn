"""Factor active/pending catalog subjects through one parameterized reader.
Uses the shared structural Lisp reader; the active0 wrapper keeps root binding.
"""
import lisp_rewrite as lr
def rewrite_catalog_subject(source):
    s=source;n=lr.match('(defun fn2-event-catalog-current-p ?*body)',lr.parse(s).forms)[0].node
    argnames=[x.text for x in n.items[2].items];subjectargs=[a for a in argnames if a!='fn2-commit-root'];body=s[n.items[-1].start:n.items[-1].end]
    body=body.replace('(< 0 (fn2-commit-root-rows fn2-commit-root))','(natp r)')
    # Derive subject arithmetic from the exact authority; root matching belongs
    # only to the active runtime wrapper, not the pending installation subject.
    body=body.replace('(fn2-commit-root-base-batch 0 fn2-commit-root)','(fn2-checkpoint-summary-authority-cut-commit r fn2-checkpoint-summary-authority)').replace('(fn2-commit-root-base-event 0 fn2-commit-root)','(fn2-checkpoint-summary-authority-cut-event r fn2-checkpoint-summary-authority)')
    parsed=lr.parse(body);edits=[]
    for m in lr.match('(?head ?*args)',parsed.forms):
     x=m.node;head=getattr(x.items[0],'low','')
     if head.startswith('fn2-checkpoint-summary-authority-') and len(x.items)>=2 and getattr(x.items[1],'low',None)=='0':
      edits.append((x.items[1].start,x.items[1].end,'r'))
    body=lr.write(body,edits).replace('(fn2-event-catalog-descriptor-p 0 ', '(fn2-event-catalog-subject-descriptor-p r 0 ')
    subject='(defun fn2-event-catalog-subject-p (r '+' '.join(subjectargs)+')\n (declare (xargs :stobjs ('+' '.join(subjectargs)+')\n :guard (and '+' '.join('('+a+'-wfp '+a+')' for a in subjectargs)+')))\n '+body+')\n'
    wrapper='(defun fn2-event-catalog-current-p ('+' '.join(argnames)+')\n (declare (xargs :stobjs ('+' '.join(argnames)+')\n :guard (and '+' '.join('('+a+'-wfp '+a+')' for a in argnames)+')))\n (and (< 0 (fn2-commit-root-rows fn2-commit-root))\n  (fn2-event-catalog-subject-p 0 '+' '.join(subjectargs)+')\n  (= (fn2-checkpoint-restore-events-cut-commit 1 fn2-checkpoint-restore-events) (fn2-commit-root-base-batch 0 fn2-commit-root))\n  (= (fn2-checkpoint-restore-events-cut-event 1 fn2-checkpoint-restore-events) (fn2-commit-root-base-event 0 fn2-commit-root))))\n'
    s=s[:n.start]+subject+wrapper+s[n.end:]
    # Parameterize the single descriptor implementation; preserve its active0 API.
    n=lr.match('(defun fn2-event-catalog-descriptor-p ?*body)',lr.parse(s).forms)[0].node;t=s[n.start:n.end];t=t.replace('fn2-event-catalog-descriptor-p','fn2-event-catalog-subject-descriptor-p');t=t.replace('(i fn2-checkpoint-summary-authority', '(r i fn2-checkpoint-summary-authority',1);t=t.replace('(fn2-checkpoint-summary-authority-descriptori i ', '(fn2-checkpoint-summary-authority-descriptori (+ (* 32 r) i) ');t=t.replace('(natp i) (<= i 32)', '(natp r) (< r 2) (natp i) (<= i 32)');t=t.replace('(fn2-event-catalog-subject-descriptor-p (+ 1 i)', '(fn2-event-catalog-subject-descriptor-p r (+ 1 i)')
    wrapper='''(defun fn2-event-catalog-descriptor-p (i fn2-checkpoint-summary-authority fn2-checkpoint-restore-events)
     (declare (xargs :stobjs (fn2-checkpoint-summary-authority fn2-checkpoint-restore-events)
     :guard (and (fn2-checkpoint-summary-authority-wfp fn2-checkpoint-summary-authority) (fn2-checkpoint-restore-events-wfp fn2-checkpoint-restore-events) (natp i) (<= i 32))))
     (fn2-event-catalog-subject-descriptor-p 0 i fn2-checkpoint-summary-authority fn2-checkpoint-restore-events))
    '''
    s=s[:n.start]+t+'\n'+wrapper+s[n.end:];return s
