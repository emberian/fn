"""Copy signed theorem terms into defteeth claims; ACL2 checks exact binding."""
from pathlib import Path
import sys
ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'tools'))
import lisp_rewrite as rw

def term(file,name):
 s=(ROOT/'books'/file).read_text()
 h=rw.match('_',rw.parse(s).forms,head='defthm',name=name,deep=False)[0]
 x=h.node.items[2];assert x.items[0].low=='implies'
 return [s[t.start:t.end] for t in x.items[1:]]

def emit(file,name,subject,witness,broken,mutation=None):
 hyp,conclusion=term(file,name)
 mut=('((:early-release (:conclusion '+mutation+') '+witness+
      ' :fault "Releasing the appended tail before its own barrier."))') if mutation else '(:not-applicable "The construction has no release effect; its invalid-input removal is checked below.")'
 return f'''(defteeth {name}
 :claim (((:invariant {hyp})) {conclusion})
 :subject {subject}
 :witness {witness}
 :breaks ((:invariant {broken}))
 :mutations {mut})\n'''

rows=[
 ('store-log-pipeline.lisp','fn-lgk-append-behind-safe','fn-lgk-append-behind',
  '((p (nth 0 *gc-preappend*)) (h (nth 3 *gc-preappend*)) (unit 512) (extent 65536))',
  '((p (nth 0 *gc-early-ack*)) (h (nth 3 *gc-early-ack*)) (unit 512) (extent 65536))',
  '(equal (fn-lgk-pipe-acked (fn-lgk-behind-state p unit extent)) (len h))'),
 ('store-log-pipeline.lisp','fn-lgk-pipe-fence-safe','fn-lgk-pipe-fence',
  '((p (nth 0 *gc-pipelined*)) (h (nth 3 *gc-pipelined*)) (unit 512))',
  '((p (nth 0 *gc-early-ack*)) (h (nth 3 *gc-early-ack*)) (unit 512))',
  '(equal (fn-lgk-pipe-d (fn-lgk-pipe-fence p unit)) (len h))'),
 ('owner-commit-durability.lisp','fn-ocp-gc-linkedp-initially','fn-ocp-gc-init',
  '((unit 512) (extent 65536) (bmax 2) (omax 4096))',
  '((unit 0) (extent 65536) (bmax 2) (omax 4096))',None),
 ('owner-commit-durability.lisp','fn-ocp-gc-linkedp-preserved','fn-ocp-gc-host-step',
  "((x *gc-preappend*) (event '(:append-issue)))",
  "((x *gc-early-ack*) (event '(:reader)))",
  '(equal (fn-lgk-pipe-acked (nth 0 (fn-ocp-gc-host-step x event))) (len (nth 3 x)))'),
 ('owner-commit-durability.lisp','fn-ocp-gc-reveals-are-durable','fn-ocp-gc-host-step',
  "((x *gc-pipelined*) (event '(:reader)))",
  "((x *gc-bad-view*) (event '(:reader)))",
  '(equal (nth 8 (fn-ocp-gc-host-step x event)) (list (fn-ocvm-w (nth 2 x))))'),
 ('owner-commit-durability.lisp','fn-ocp-gc-failure-fences-both-batches','fn-ocp-gc-host-step',
  '((x *gc-pipelined*) (events *gc-late-events*))',
  '((x *gc-resolved*) (events nil))',
  "(equal (nth 9 (fn-ocp-gc-host-step x '(:io :current :uncertain))) '(:rendered :rendered))"),
 ('store-log-pipeline.lisp','fn-olr-gc-membership-and-profile-bounds','fn-lgk-pipe-take',
  "((h (nth 3 *gc-a*)) (p (nth 0 *gc-a*)) (record '(67)) (txid 3) (count 0) (octets 0) (bmax 2) (omax 4096) (unit 512))",
  "((h (nth 3 *gc-preappend*)) (p (nth 0 *gc-preappend*)) (record '(68)) (txid 4) (count 0) (octets 5) (bmax 1) (omax 4096) (unit 512))",None)]
if __name__=='__main__':
 text='; Generated claims bind to the signed formulas; witnesses run under guards.\n(in-package "ACL2")\n(include-book "gc-pipeline-tests")\n(include-book "../../books/owner-commit-durability")\n(include-book "../../books/defkeystone")\n\n'
 text+='\n'.join(emit(*r) for r in rows)
 text+='\n(value-triple :seven-keystone-teeth-bound-and-evaluated)\n'
 (ROOT/'tests/acl2/gc-pipeline-teeth.lisp').write_text(text)
