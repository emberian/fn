"""Project actual writer setup into a cold semantic-verifier boundary unit.

The old fixture's explicit synthetic page/reach premise is retained. New bytes
are produced/sealed by the same commit packer and format-run, not another codec.
"""
from pathlib import Path
import lisp_rewrite as lr
import event_archive_seal_rewrite as seal
import event_archive_batch_rewrite as batch
ROOT=Path(__file__).resolve().parents[1]
INPUT=ROOT/'tests/event-archive-cold-member-unit.lisp'
XR=seal.XR
OUT=seal.OUT

def helpers():
 return '''(defun fn2-easc-format (fuel kind row slot gen off len base previous fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)
 (declare (xargs :stobjs (fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests) :verify-guards nil :measure (nfix fuel)))
 (if (zp fuel) (mv :fuel fn2-fc fn2-b3 fn2-fields fn2-pool fn2-digests)
  (b* (((mv code fn2-fc fn2-b3 fn2-fields fn2-pool fn2-digests)
        (fn2-format-run kind t row slot gen off len base 1 2 3 *fn2-commit-unit-bytes* fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests))
       ((unless (eq code :more)) (mv code fn2-fc fn2-b3 fn2-fields fn2-pool fn2-digests)))
   (fn2-easc-format (- fuel 1) kind row slot gen off len base previous fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests))))

(defun fn2-easc-snapshot (@XR@)
 (declare (xargs :stobjs (@XR@) :verify-guards nil))
 (list (fn2-event-archive-copy fn2-event-archive) (fn2-event-read-copy fn2-event-read)
       (fn2-journal-members-copy fn2-journal-members) (fn2-fc-copy fn2-fc) (fn2-fc-context-copy fn2-fc-context)
       (fn2-b3-copy fn2-b3) (fn2-fields-copy fn2-fields) (fn2-pool-copy fn2-pool) (fn2-digests-copy fn2-digests)))

(defun fn2-easc-drive (fuel @XR@)
 (declare (xargs :stobjs (@XR@) :verify-guards nil :measure (nfix fuel)))
 (if (zp fuel) (mv :fuel @OUT@)
  (b* ((phase (fn2-event-archive-batch-phase 1 fn2-event-archive))
       (fetch (fn2-event-archive-batch-fetch-next 1 fn2-event-archive))
       (reader (fn2-event-read-phase 0 fn2-event-read))
       (record-fetch (fn2-event-read-record-fetch-next 0 fn2-event-read))
       ((mv code @OUT@) (fn2-event-archive-cold-batch-seal-step 1 @XR@))
       ((unless (and (or (not (= phase *fn2-event-archive-batch-phase-expected*))
                        (= (fn2-event-archive-batch-fetch-next 1 fn2-event-archive) (+ fetch 1)))
                    (or (not (= reader *fn2-event-read-phase-record-digest*))
                        (= (fn2-event-read-record-fetch-next 0 fn2-event-read) (+ record-fetch 1))))) (mv :overrun @OUT@))
       ((unless (eq code :more)) (mv code @OUT@)))
   (fn2-easc-drive (- fuel 1) @XR@))))

'''.replace('@XR@',XR).replace('@OUT@',OUT)


def setup(source):
 n=batch.node(source,'(defun fn2-eamcu-body ?*body)')
 b=n.items[-1]
 if getattr(b.items[0],'low',None)!='b*':raise ValueError('actual writer fixture binding form drift')
 bindings=b.items[1].items
 stop=[i for i,x in enumerate(bindings) if isinstance(x,lr.Lst) and getattr(x.items[0],'low',None)=='premise']
 if len(stop)!=1:raise ValueError('actual setup premise drift')
 selected=bindings[:stop[0]+1]
 text='\n      '.join(source[x.start:x.end] for x in selected)
 old="(batch-mode (member-eq fault '(:batch-header :batch-commit :batch-tail :batch-copy)))"
 if text.count(old)!=1:raise ValueError('actual witness writer mode drift')
 text=text.replace(old,'(batch-mode t)')
 text=text.replace('(if (eq fault :batch-commit) 2 1)','1')
 anchor='(fn2-fc (fn2-fc-init 8 fn2-fc))'
 if text.count(anchor)!=1:raise ValueError('actual row initializer drift')
 text=text.replace(anchor,anchor+'\n      (fn2-fc-context (fn2-fc-context-init 8 fn2-fc-context))\n      (fn2-event-read (fn2-event-read-init 1 fn2-event-read))')
 fs=batch.node(text,'((mv fs send fn2-fields fn2-pool) ?*body)')
 writer='''; Rebuild the same original records writer input, seal it with the real
      ; frame engine, and preserve its full bytes for the later relation control.
      (writer-row (fn2-b-event-row 8)) (writer-base (* 128 writer-row))
      (writer-previous (fn2-b-event-previous-digest 8 3))
      (writer-hash (fn2-digest-slot writer-row *fn2-fc-hash*))
      (writer-result (fn2-digest-slot writer-row *fn2-fc-result*))
      (writer-geometry (fn2-digest-slot writer-row *fn2-fc-geometry*))
      ((mv frame-zero fn2-pool) (fn2-run-zero *fn2-commit-unit-bytes* accumulator agen 0 1 2 3 fn2-pool))
      ((mv frame-header fn2-pool) (fn2-pool-copy-range scratch sg 256 accumulator agen 0 (- fend 256) 1 2 3 fn2-pool))
      ((mv frame-members fn2-pool) (fn2-pool-copy-range page pg 4096 accumulator agen (- fend 256) (- rend 4096) 1 2 3 fn2-pool))
      ((mv frame-tag fn2-pool) (fn2-pool-write accumulator agen *fn2-commit-frame-trailer* 1 1 2 3 fn2-pool))
      (fn2-fc-context (fn2-rec-context writer-row 1 1 2 3 1 writer-hash writer-previous writer-geometry 17 19 fn2-fc-context))
      ((mv frame-sealed fn2-fc fn2-b3 fn2-fields fn2-pool fn2-digests)
       (fn2-easc-format (fn2-format-fuel *fn2-commit-unit-bytes*) :frame writer-row accumulator agen 0 *fn2-commit-unit-bytes* writer-base writer-previous fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests))
      (original-frame (fn2-pool-logical-octets *fn2-commit-unit-bytes* (fn2-pool-base accumulator fn2-pool) fn2-pool))
      (original-records (fn2-digest-list writer-result fn2-digests))
      ((mv records-stored fn2-pool) (fn2-digest-store *fn2-commit-digest-bytes* writer-result scratch sg *fn2-commit-scratch-records* 1 2 3 fn2-digests fn2-pool))
      '''
 text=lr.write(text,[(fs.start,fs.start,writer)])
 fs=batch.node(text,'((mv fs send fn2-fields fn2-pool) ?*body)')
 seal_writer='''
      (fn2-fc-context (fn2-rec-context writer-row 1 2 2 3 1 writer-hash writer-previous writer-geometry 17 19 fn2-fc-context))
      ((mv seal-sealed fn2-fc fn2-b3 fn2-fields fn2-pool fn2-digests)
       (fn2-easc-format (fn2-format-fuel *fn2-format-sealed-batch-max-size*) :seal writer-row scratch sg 512 (- send 512) writer-base writer-previous fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests))
      (original-seal (fn2-digest-list writer-result fn2-digests))
      ((mv changed fn2-pool)
       (if (member-eq fault '(:hash :namespace))
        (let ((at (if (eq fault :hash) (- send 1) 512)))
         (mv-let (read byte) (fn2-pool-read scratch sg at 1 2 3 fn2-pool)
          (if (eq read :ok) (fn2-pool-write scratch sg at (logxor 1 byte) 1 2 3 fn2-pool) (mv read fn2-pool))))
        (if (eq fault :tail) (fn2-pool-write scratch sg send 0 1 2 3 fn2-pool) (mv :ok fn2-pool))))
      '''
 text=lr.write(text,[(fs.end,fs.end,seal_writer)])
 ref=batch.node(text,'(fn2-fields-put (+ eb *fn2-event-archive-member-entry-field-original-sealed-batch*) ?*body)')
 span=batch.node(text[ref.start:ref.end],'(ref-len ?*body)')
 old=text[ref.start+span.start:ref.start+span.end]
 # The exact body span is used except the deliberate extra zero-tail control.
 if old!='(ref-len (if batch-mode (- send 512) 0))':raise ValueError('actual body witness span drift')
 text=lr.write(text,[(ref.start+span.start,ref.start+span.end,'(ref-len (+ (- send 512) (if (eq fault :tail) 1 0)))')])
 return [x.low for x in n.items[2].items[1:]],text


def local_wrapper(children,call):
 def emit(i):
  if i==len(children):return call
  result='answer' if i==0 else '(mv answer '+' '.join(children[:i])+')'
  return '(with-local-stobj '+children[i]+'\n  (mv-let (answer '+' '.join(children[:i+1])+')\n   '+emit(i+1)+'\n   '+result+'))'
 return emit(0)


def generate(source):
 children,prefix=setup(source)
 children+=['fn2-fc-context','fn2-event-read']
 body='''(defun fn2-easc-body (fault @CHILDREN@)
 (declare (xargs :stobjs (@CHILDREN@) :verify-guards nil))
 (b* (@PREFIX@
      ((mv header fn2-event-archive fn2-fields) (fn2-eabh-run @FIRST@))
      ((mv copied fn2-event-archive fn2-pool) (if (eq header :header-checked) (fn2-eabs-run @FIRST@) (mv header fn2-event-archive fn2-pool)))
      (whole (and premise (eq a :ok) (eq b :ok) (eq ar :ok) (eq z :ok) (eq sz :ok)
                  (eq rh :ok) (eq rb :ok) (eq fh :ok) (eq fs :ok) (eq h :ok)
                  (eq frame-zero :ok) (eq frame-header :ok) (eq frame-members :ok) (eq frame-tag :ok)
                  (eq frame-sealed :ok) (eq records-stored :ok) (eq seal-sealed :ok) (eq changed :ok)
                  (eq encoded :ok) (eq decoded :ok) (equal next end)
                  (eq header :header-checked) (eq copied :seal-copied)
                  (fn2-event-archive-cold-batch-first-page-p @FIRST@)
                  (equal (fn2-event-archive-batch-phase 1 fn2-event-archive) *fn2-event-archive-batch-phase-seal-span*)
                  (equal (fn2-event-read-phase 0 fn2-event-read) *fn2-event-read-phase-idle*)))
      (before (fn2-easc-snapshot @XR@))
      ((mv zero @OUT@) (fn2-event-archive-cold-batch-seal-step 0 @XR@))
      (zero-same (and (eq zero :more) (equal before (fn2-easc-snapshot @XR@))))
      ((mv code @OUT@) (fn2-easc-drive (fn2-format-fuel *fn2-format-sealed-batch-max-size*) @XR@))
      (saved-seal (fn2-b-event-root-digest 8 3))
      (hash (fn2-digest-slot writer-row *fn2-fc-hash*))
      (good (if fault
                (and (member-eq code '(:bad-hash :wrong-history :seal-span :seal))
                     (equal (fn2-event-archive-batch-phase 1 fn2-event-archive) *fn2-event-archive-batch-phase-uncertain*))
              (and (eq code :seal-checked)
                   (equal (fn2-event-archive-batch-phase 1 fn2-event-archive) *fn2-event-archive-batch-phase-records-zero*)
                   (equal (fn2-digest-list saved-seal fn2-digests) original-seal)
                   (equal (fn2-digest-list hash fn2-digests) original-records)
                   (equal (fn2-event-read-phase 0 fn2-event-read) *fn2-event-read-phase-idle*)))))
  (mv (and whole zero-same good (equal (len original-frame) *fn2-commit-unit-bytes*)
           (equal (fn2-event-archive-next-event 1 fn2-event-archive) 1)
           (equal (fn2-event-archive-phase 1 fn2-event-archive) *fn2-event-archive-phase-cold-members*)
           (equal (fn2-event-archive-entry-pending 1 fn2-event-archive) 1)
           (equal (fn2-mk-size writer-row fn2-mk) 0)) @CHILDREN@)))
'''.replace('@CHILDREN@',' '.join(children)).replace('@PREFIX@',prefix).replace('@FIRST@',batch.CHILDREN).replace('@XR@',XR).replace('@OUT@',OUT)
 wrapper='''(defun fn2-easc-test (fault)
 (declare (xargs :verify-guards nil))
 '''+local_wrapper(children,'(fn2-easc-body fault '+' '.join(children)+')')+')\n'
 return '''; Actual writer -> actual schema20 -> selected-source semantic verifier.
; Synthetic page/reach premise is explicit; all ACL2 assertions UNRUN.
; This is not original-frame/root4/prefix transfer authority.
(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "event-archive-cold-member-unit")

'''+helpers()+body+'\n'+wrapper+'''\n(assert-event (fn2-easc-test nil))
(assert-event (fn2-easc-test :hash))
(assert-event (fn2-easc-test :namespace))
(assert-event (fn2-easc-test :tail))
'''

if __name__=='__main__':
 (ROOT/'tests/event-archive-cold-seal-unit.lisp').write_text(generate(INPUT.read_text()))
