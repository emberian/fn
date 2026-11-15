"""Named live-catalog bank projection; no replacement of surrounding providers."""
from pathlib import Path
import lisp_rewrite as lr

def once(text, old, new):
    if old == new:
        return text
    if text.count(old) != 1:
        raise ValueError('expected one named source boundary: ' + old[:100])
    return text.replace(old, new, 1)

def project(book, text):
    if book == 'checkpoint-summary-state':
        if '(bank :bool)' in text:
            return text
        return once(text, '(priority-base :u60) (application-stage :u8)',
                    '(priority-base :u60) (bank :bool) (application-stage :u8)')
    if book == 'checkpoint-live-install':
        if '; Replacement-bank ownership is retained across every bounded turn.' in text:
            return text
        text = once(text, '    (< 0 (fn2-id-engine-rows fn2-id-engine))',
          '    (fn2-run-installed-bank-geometry-p fn2-run-installed)\n'
          '    (< 0 (fn2-id-engine-rows fn2-id-engine))')
        text = once(text, '   (cursor 0) (target 0) (free-count 0)',
          '   ; Replacement-bank ownership is retained across every bounded turn.\n'
          '   (bank (if (= (fn2-checkpoint-summary-phase 0 fn2-checkpoint-summary) *fn2-checkpoint-summary-phase-applied*)\n'
          '             (- 1 (fn2-checkpoint-summary-bank 0 fn2-checkpoint-summary)) 0))\n'
          '   (cursor 0) (target 0) (free-count 0)')
        text = once(text, '  (stage (fn2-checkpoint-summary-application-stage 1 fn2-checkpoint-summary))',
          '  ((unless (fn2-run-installed-bank-geometry-p fn2-run-installed))\n'
          '   (mv :bounds fn2-checkpoint-summary fn2-checkpoint-metadata-manifest fn2-run-installed))\n'
          '  (bank (fn2-checkpoint-summary-bank 1 fn2-checkpoint-summary))\n'
          '  (start (fn2-run-installed-bank-start bank fn2-run-installed))\n'
          '  (end (+ start (fn2-run-installed-bank-capacity fn2-run-installed)))\n'
          '  (stage (fn2-checkpoint-summary-application-stage 1 fn2-checkpoint-summary))')
        text = once(text, '(<= (fn2-checkpoint-summary-count 1 fn2-checkpoint-summary) (fn2-checkpoint-summary-free-count 1 fn2-checkpoint-summary))',
          '(= (fn2-checkpoint-summary-free-count 1 fn2-checkpoint-summary) (fn2-run-installed-bank-capacity fn2-run-installed))\n'
          '                    (<= (fn2-checkpoint-summary-count 1 fn2-checkpoint-summary) (fn2-run-installed-bank-capacity fn2-run-installed))')
        text = once(text, '(application-stage *fn2-live-replace-stage-install*) (cursor 0) (target 0)',
          '(application-stage *fn2-live-replace-stage-install*) (cursor 0) (target start)')
        text = once(text, '(if (= (fn2-run-installed-state i fn2-run-installed) *fn2-run-installed-state-free*) 1 0)',
          '(if (and (fn2-run-installed-bank-row-p bank i fn2-run-installed)\n'
          '                       (= (fn2-run-installed-state i fn2-run-installed) *fn2-run-installed-state-free*)\n'
          '                       (= (fn2-run-installed-physical i fn2-run-installed) 0)) 1 0)')
        text = once(text, '(and (< r (fn2-run-installed-rows fn2-run-installed)) (unsigned-byte-p 32 (+ 1 r)))',
          '(and (fn2-run-installed-bank-row-p bank r fn2-run-installed) (< r end) (unsigned-byte-p 32 (+ 1 r)))')
        # FIT established the entire target bank drained under EXCLUSIVE. A
        # later occupied row is a violated continuation, never a reason to use
        # the active bank or consume a resident slot.
        text = once(text,
          '     ((unless (= (fn2-run-installed-state r fn2-run-installed) *fn2-run-installed-state-free*))\n'
          '      (let ((fn2-checkpoint-summary (fn2-checkpoint-summary-set-target 1 (+ 1 r) fn2-checkpoint-summary)))\n'
          '       (mv :more fn2-checkpoint-summary fn2-checkpoint-metadata-manifest fn2-run-installed)))',
          '     ((unless (and (= (fn2-run-installed-state r fn2-run-installed) *fn2-run-installed-state-free*)\n'
          '                   (= (fn2-run-installed-physical r fn2-run-installed) 0)))\n'
          '      (mv :changed fn2-checkpoint-summary fn2-checkpoint-metadata-manifest fn2-run-installed))')
        text = once(text, '(cursor (+ 1 i)) (target 0) (installed count)',
                    '(cursor (+ 1 i)) (target (+ 1 r)) (installed count)')
        return text
    if book == 'checkpoint-live-finish':
        if '(bank (fn2-checkpoint-summary-bank 1 fn2-checkpoint-summary))' in text:
            return text
        text = once(text, '          (priority-base (fn2-checkpoint-summary-priority-base 1 fn2-checkpoint-summary))',
          '          (bank (fn2-checkpoint-summary-bank 1 fn2-checkpoint-summary))\n'
          '          (priority-base (fn2-checkpoint-summary-priority-base 1 fn2-checkpoint-summary))')
        text = once(text, '   (= (fn2-checkpoint-summary-priority-base 0 fn2-checkpoint-summary)',
          '   (= (fn2-checkpoint-summary-bank 0 fn2-checkpoint-summary) (fn2-checkpoint-summary-bank 1 fn2-checkpoint-summary))\n'
          '   (= (fn2-checkpoint-summary-priority-base 0 fn2-checkpoint-summary)')
        text = once(text, '   (priority-base 0)', '   (bank 0)\n   (priority-base 0)')
        return text
    raise ValueError(book)

def project_receipt(text):
    """Append the actual prepublication receipt to the sole typed BEGIN."""
    if '(fn2-checkpoint-bank-admission-ready-p' in text:
        return text
    matches=lr.match('(defun fn2-checkpoint-live-replace-begin ?*body)',lr.parse(text).forms,deep=True)
    if len(matches)!=1:raise ValueError('one actual typed BEGIN')
    f=matches[0].node
    source=text[f.start:f.end]
    # Append one readonly child without altering any existing argument order,
    # mutable result, guard conjunct or producer precondition.
    edits=[]
    args=f.items[2]
    edits.append((args.end-1,args.end-1,' fn2-checkpoint-bank-admission'))
    xargs=f.items[3].items[1]
    for i,item in enumerate(xargs.items):
        key=getattr(item,'low','')
        if key==':stobjs':
            n=xargs.items[i+1];edits.append((n.end-1,n.end-1,' fn2-checkpoint-bank-admission'))
        elif key==':guard':
            n=xargs.items[i+1];edits.append((n.end-1,n.end-1,' (fn2-checkpoint-bank-admission-wfp fn2-checkpoint-bank-admission)'))
    text=lr.write(text,edits)
    old='  ((mv code fn2-c-source-control) (fn2-c-source-writer-begin '
    check='''  ((unless (fn2-checkpoint-bank-admission-ready-p
   (fn2-checkpoint-summary-generation 1 fn2-checkpoint-summary)
   (fn2-checkpoint-summary-owner-kind 1 fn2-checkpoint-summary)
   (fn2-checkpoint-summary-owner-slot 1 fn2-checkpoint-summary)
   (fn2-checkpoint-summary-owner-gen 1 fn2-checkpoint-summary)
   fn2-csnapshot fn2-checkpoint-summary fn2-run-installed fn2-checkpoint-bank-admission))
   (mv :admission fn2-checkpoint-summary fn2-c-source-control))
'''
    text=once(text,old,check+old)
    text=once(text,'''(bank (if (= (fn2-checkpoint-summary-phase 0 fn2-checkpoint-summary) *fn2-checkpoint-summary-phase-applied*)
             (- 1 (fn2-checkpoint-summary-bank 0 fn2-checkpoint-summary)) 0))''',
      '(bank (fn2-checkpoint-bank-admission-bank 0 fn2-checkpoint-bank-admission))')
    # Only BEGIN consumes this receipt. INSTALL subsequently owns SUMMARY1's
    # exact chosen bank under EXCLUSIVE, and retirement changes SUMMARY0 phase.
    ms=lr.match('(defcost fn2-checkpoint-live-replace-begin-op ?*body)',lr.parse(text).forms,deep=False)
    if len(ms)!=1:raise ValueError('one actual typed BEGIN face')
    cost=ms[0].node
    for i,item in enumerate(cost.items):
        if getattr(item,'low','')==':tables':
            n=cost.items[i+1]
            text=lr.write(text,[(n.end-1,n.end-1,' fn2-core-checkpoint-bank-admission')])
            break
    return once(text,'(include-book "c-source-observer")',
      '(include-book "c-source-observer")\n(include-book "checkpoint-bank-admission")')

if __name__ == '__main__':
    import argparse
    p=argparse.ArgumentParser();p.add_argument('root',type=Path);a=p.parse_args()
    for book in ('checkpoint-summary-state','checkpoint-live-install','checkpoint-live-finish'):
        path=a.root/'books'/(book+'.lisp');new=project(book,path.read_text())
        if book=='checkpoint-live-install':new=project_receipt(new)
        lr.parse(new)
        path.write_text(new)
