"""Named actual MASTER/late-emitter bank admission projection.

This does not transplant a master declaration, activate maintenance, or create
an alternate controller. It adds one bounded preallocation continuation to
the owning source supplied by the integrator.
"""
import lisp_rewrite as lr

def once(text,old,new):
    if text.count(old)!=1:raise ValueError('one named boundary '+old[:80])
    return text.replace(old,new,1)

def event(text,pattern):
    found=lr.match(pattern,lr.parse(text).forms,deep=True)
    if len(found)!=1:raise ValueError('one actual event '+pattern)
    return found[0].node

def project_state(text):
    if '*fn2-master-bank-step-turn-steps*' in text:return text
    text=once(text,'(include-book "checkpoint-master-work")',
      '(include-book "checkpoint-bank-master-work")')
    machine=event(text,'(defmachine fn2-checkpoint-master ?*body)')
    edits=[]
    for i,n in enumerate(machine.items):
        if getattr(n,'low','')==':states':
            a=machine.items[i+1];edits.append((a.end-1,a.end-1,' :bank-begin :bank-scan'))
        elif getattr(n,'low','')==':arms':
            a=machine.items[i+1];edits.append((a.end-1,a.end-1,' (:bank-begin) (:bank-scan)'))
    if len(edits)!=2:raise ValueError('actual state and arm inventories')
    text=lr.write(text,edits)
    n=event(text,'(defconst *fn2-checkpoint-master-step-budget* ?*value)')
    old=n.items[2]
    if not isinstance(old,lr.Lst) or getattr(old.items[0],'low','')!='max':
        raise ValueError('actual master budget MAX expected')
    values=[text[x.start:x.end] for x in old.items[1:]]
    values+=['*fn2-master-bank-begin-turn-steps*','*fn2-master-bank-step-turn-steps*']
    # ACL2's MAX is binary. Preserve the original operands, not the donor's
    # erroneous variadic invocation, and append the exact new arm bounds.
    value=values[-1]
    for a in reversed(values[:-1]):value='(max '+a+' '+value+')'
    return lr.write(text,[(old.start,old.end,value)])

BANK_ARMS='''
  (:bank-begin :on-refusal ((:stop :checkpoint) (:charge :steps *fn2-work-stage*))
   (:do (code) (fn2-checkpoint-bank-admission-begin-op row-token *fn2-checkpoint-master-kind* id row-generation) :accept (:more))
   (:next :bank-scan) (:charge :steps *fn2-work-stage* :runnable t))
  (:bank-scan :on-refusal ((:stop :checkpoint) (:charge :steps *fn2-work-stage*))
   (:do (code) (fn2-checkpoint-bank-admission-step-op row-token *fn2-checkpoint-master-kind* id row-generation) :accept () :case
    (((:more) (:charge :steps *fn2-work-stage* :runnable t))
     ((:ready) (:next :reserve) (:charge :steps *fn2-work-stage* :runnable t))
     ((:resources) (:next :abort-empty) (:charge :steps *fn2-work-stage* :runnable t))
     (:otherwise (:stop :checkpoint) (:charge :steps *fn2-work-stage*)))))
'''

def project_arms(text):
    if '(fn2-checkpoint-bank-admission-begin-op ' in text:return text
    poll=event(text,'(:snapshot-poll :on-refusal ?*body)')
    poll_source=text[poll.start:poll.end]
    held=event(poll_source,'((:held) ?*body)')
    # Only the actual snapshot HELD branch may route into bank admission.
    h=poll_source[held.start:held.end]
    changed=once(h,'(:next :reserve)','(:next :bank-begin)')
    poll_source=lr.write(poll_source,[(held.start,held.end,changed)])
    text=lr.write(text,[(poll.start,poll.end,poll_source)])
    reserve=event(text,'(:reserve :on-refusal ?*body)')
    return lr.write(text,[(reserve.start,reserve.start,BANK_ARMS)])

def project_emitter(text):
    ms=lr.match('(fn2-run-loader-core-face-events ?*args)',lr.parse(text).forms,deep=True)
    matches=[]
    for m in ms:
        s=text[m.node.start:m.node.end]
        if 'fn2-checkpoint-live-replace-finish-op' in s:matches.append(m.node)
    if len(matches)!=1:raise ValueError('one actual late typed face emitter')
    n=matches[0];s=text[n.start:n.end]
    if 'fn2-checkpoint-bank-admission-begin-op' in s:return text
    s=once(s,'fn2-checkpoint-live-replace-finish-op',
      'fn2-checkpoint-bank-admission-begin-op fn2-checkpoint-bank-admission-step-op fn2-checkpoint-live-replace-finish-op')
    return lr.write(text,[(n.start,n.end,s)])

def project(book,text):
    return {'checkpoint-master-state':project_state,
            'checkpoint-master-arms':project_arms,
            'assembly-callbacks-e-cns':project_emitter}[book](text)
