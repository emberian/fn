"""Migrate the actual format dispatcher class to one bounded phase predicate."""
from pathlib import Path
import lisp_rewrite as lr
PATTERN='(member-equal ?phase (list *fn2-event-read-phase-frame-seal* *fn2-event-read-phase-semantic-seal* *fn2-event-read-phase-frame-records*))'
def dispatch(source,expected):
 nodes=lr.match(PATTERN,lr.parse(source).forms)
 if not nodes:
  if len(lr.match('(fn2-event-read-format-phase-p ?phase)',lr.parse(source).forms))==expected:return source
  raise ValueError('dispatch class drift')
 if len(nodes)!=expected:raise ValueError('dispatcher count drift')
 return lr.write(source,[(m.node.start,m.node.end,'(fn2-event-read-format-phase-p '+source[m.captures['phase'].start:m.captures['phase'].end]+')') for m in nodes])
def state(source):
 if '(defun fn2-event-read-format-phase-p ' in source:return source
 if source.count(':frame-seal :semantic-seal')!=1:raise ValueError('reader state declaration drift')
 source=source.replace(':frame-seal :semantic-seal',':frame-seal :seal-span :seal-tail :semantic-seal')
 source=source.replace('(body-off :u32) (body-len :u32)', '(body-off :u32) (body-len :u32)\n  (seal-span-started :bool) (seal-span-next :u32) (seal-span-length :u32)')
 anchor=lr.match('(defun fn2-event-read-harvest ?*body)',lr.parse(source).forms,deep=False)[0].node
 helper='''; Format work owns one bounded source visit; callers yield before it at zero.
(defun fn2-event-read-format-phase-p (phase)
 (declare (xargs :guard t))
 (and (member-equal phase (list *fn2-event-read-phase-frame-seal* *fn2-event-read-phase-seal-span* *fn2-event-read-phase-seal-tail*
                               *fn2-event-read-phase-semantic-seal* *fn2-event-read-phase-frame-records*)) t))

'''
 return lr.write(source,[(anchor.start,anchor.start,helper)])
if __name__=='__main__':
 root=Path(__file__).resolve().parents[1]
 p=root/'books/event-read-state.lisp';p.write_text(state(p.read_text()))
 for name,count in [('books/event-producer.lisp',2),('books/checkpoint-restore-events.lisp',1),('tests/event-read-verified-unit.lisp',1)]:
  p=root/name;p.write_text(dispatch(p.read_text(),count))
