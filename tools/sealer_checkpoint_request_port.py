"""Named sealer admission→canonical checkpoint request/resume projection."""
from pathlib import Path
import lisp_rewrite as lr
ROOT=Path(__file__).resolve().parents[1]
FIX=ROOT/'tools/fixtures/sealer-checkpoint'
def once(s,a,b):
 if s.count(a)!=1:raise ValueError('sealer request boundary: '+a[:90])
 return s.replace(a,b,1)
def project_kind(s):
 s=once(s,':range :yield)',':range :yield :checkpoint-required)')
 s=once(s,'fn2-core-reads fn2-core-succ-txns)\n :doc \"One bounded seal step', 'fn2-core-reads fn2-core-succ-txns fn2-core-run-loads fn2-core-checkpoint-summary-leases)\n :doc \"One bounded seal step')
 s=s.replace(':states (:sealing :binding :loading :reading :draining :stopped)', ':states (:sealing :binding :loading :reading :draining :stopped :checkpointing)')
 s=once(s,'(retry-pool :bool))','(retry-pool :bool) (checkpoint-tag :u60))')
 s=once(s,':arms ((:sealing) (:binding) (:loading) (:reading) (:draining) (:stopped))',':arms ((:sealing) (:binding) (:loading) (:reading) (:draining) (:stopped) (:checkpointing))')
 at=s.index('(defcost fn2-sealer-refuse')
 s=s[:at]+'''(defcost fn2-sealer-checkpoint-request :answers (:ok :busy :owner)
 :tables (fn2-core-machines fn2-core-sealer fn2-core-checkpoint-master fn2-core-seals fn2-core-overlays fn2-core-run-installed fn2-core-pool
          fn2-core-run-loads fn2-core-checkpoint-summary-leases fn2-core-checkpoint-summary
          fn2-core-csnapshot fn2-core-c-source-control)
 :doc "Capture actual quiescent sealer request and validated maintenance target before any prefix allocation.")
(defcost fn2-sealer-checkpoint-resume :answers (:ok :wait :owner)
 :tables (fn2-core-machines fn2-core-sealer fn2-core-seals fn2-core-run-loads
          fn2-core-checkpoint-summary-leases fn2-core-checkpoint-summary fn2-core-checkpoint-predecessor-control
          fn2-core-csnapshot fn2-core-c-source-control)
 :doc "Resume only after actual new catalog adoption, original retirement and cut/observer release.")
'''+s[at:]
 return s
CORE='''
   (defun fn2-sealer-checkpoint-needed (fn2-core)
    (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
    (and (fn2-sealer-boot-closed-p fn2-core) (fn2-sealer-source-actor-p fn2-core)
         (fn2-sealer-source-startable-p fn2-core)
     (stobj-let ((fn2-seals (fn2-core-seals fn2-core)) (fn2-overlays (fn2-core-overlays fn2-core))
                 (fn2-run-installed (fn2-core-run-installed fn2-core)) (fn2-pool (fn2-core-pool fn2-core))
                 (fn2-run-loads (fn2-core-run-loads fn2-core))
                 (fn2-checkpoint-summary-leases (fn2-core-checkpoint-summary-leases fn2-core))) (yes)
      (fn2-sealer-checkpoint-work-p fn2-seals fn2-overlays fn2-run-installed fn2-pool fn2-run-loads fn2-checkpoint-summary-leases) yes)))
   (defun fn2-sealer-checkpoint-request (fn2-core)
    (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
    (b* ((id (fn2-machine-kind-base *fn2-sealer-kind* fn2-core))
         (target (fn2-machine-kind-base *fn2-checkpoint-master-kind* fn2-core))
         ((unless (and (fn2-sealer-checkpoint-needed fn2-core)
                       (eq (fn2-sealer-snapshot-read-code id fn2-core) :ok)
                       (= (fn2-machine-phase id fn2-core) *fn2-sealer-state-sealing*)))
          (mv :busy *fn2-none* 0 0 fn2-core))
         ((unless (and (not (= target *fn2-none*)) (fn2-machine-idp target fn2-core)
                       (eq (fn2-checkpoint-master-snapshot-read-code target fn2-core) :ok)
                       (= (fn2-machine-kind target fn2-core) *fn2-checkpoint-master-kind*)
                       (= (fn2-machine-stopped target fn2-core) 0)))
          (mv :owner *fn2-none* 0 0 fn2-core))
         (tag (stobj-let ((fn2-checkpoint-summary (fn2-core-checkpoint-summary fn2-core))) (v)
               (if (< 0 (fn2-checkpoint-summary-rows fn2-checkpoint-summary))
                   (fn2-checkpoint-summary-tag 0 fn2-checkpoint-summary) 0) v)))
     (mv :ok target (fn2-machine-generation target fn2-core) tag fn2-core)))
   (fn2-core-preserves fn2-sealer-checkpoint-request (fn2-core) :position 4 :rows nil)
   (defun fn2-sealer-checkpoint-resume (fn2-core)
    (declare (xargs :stobjs fn2-core :guard (fn2-core-wfp fn2-core)))
    (b* ((id (fn2-machine-kind-base *fn2-sealer-kind* fn2-core))
         ((unless (and (not (= id *fn2-none*)) (fn2-machine-idp id fn2-core)
                       (eq (fn2-sealer-snapshot-read-code id fn2-core) :ok)
                       (= (fn2-machine-phase id fn2-core) *fn2-sealer-state-checkpointing*)
                       (= (fn2-machine-stopped id fn2-core) 0))) (mv :owner fn2-core))
         (slot (fn2-machine-slot id fn2-core))
         (yes (stobj-let ((fn2-sealer (fn2-core-sealer fn2-core)) (fn2-seals (fn2-core-seals fn2-core))
                 (fn2-run-loads (fn2-core-run-loads fn2-core)) (fn2-checkpoint-summary-leases (fn2-core-checkpoint-summary-leases fn2-core))
                 (fn2-checkpoint-summary (fn2-core-checkpoint-summary fn2-core))
                 (fn2-checkpoint-predecessor-control (fn2-core-checkpoint-predecessor-control fn2-core))
                 (fn2-csnapshot (fn2-core-csnapshot fn2-core)) (fn2-c-source-control (fn2-core-c-source-control fn2-core))) (v)
          (and (natp slot) (< slot (fn2-sealer-rows fn2-sealer))
               (fn2-sealer-checkpoint-resumed-p (fn2-sealer-checkpoint-tag slot fn2-sealer)
                fn2-seals fn2-run-loads fn2-checkpoint-summary-leases fn2-checkpoint-summary
                fn2-checkpoint-predecessor-control fn2-csnapshot fn2-c-source-control)) v)))
     (mv (if yes :ok :wait) fn2-core)))
   (fn2-core-preserves fn2-sealer-checkpoint-resume (fn2-core) :position 1 :rows nil)
'''
def project_events(s):
 s=once(s,'(include-book "sealer-physical-loader")','(include-book "sealer-physical-loader")\n(include-book "sealer-checkpoint-request")')
 s=once(s,'     ((:need-loader)', '''     ((:checkpoint-required)
      (:do (request target targetgen tag) (fn2-sealer-checkpoint-request) :accept (:ok))
      (:set (checkpoint-tag tag)) (:next :checkpointing) (:wake-row target)
      (:charge :steps *fn2-work-stage* :runnable t))
     ((:need-loader)''')
 s=once(s,'  (:stopped (:idle)))','''  (:checkpointing :on-refusal ((:stop :machine-phase))
   (:do (resumed) (fn2-sealer-checkpoint-resume) :accept () :case
    (((:ok) (:next :sealing) (:charge :steps *fn2-work-stage* :runnable t))
     ((:wait) (:wait :completion :steps *fn2-work-small*))
     (:otherwise (:do () (fn2-sealer-refuse resumed)) (:set (stopped 1)) (:next :stopped)))))
  (:stopped (:idle)))''')
 # Helpers precede public step; established observer functions are untouched.
 at=s.index('   ; The public step below acquires')
 s=s[:at]+CORE+s[at:]
 s=once(s,'(b* (((mv code fn2-core) (fn2-sealer-source-acquire fn2-core))', '''(b* (((when (fn2-sealer-checkpoint-needed fn2-core)) (mv :checkpoint-required fn2-core))
         ((mv code fn2-core) (fn2-sealer-source-acquire fn2-core))''')
 return s
EXPECTED={ 'machines-c-sealer-kind':project_kind((FIX/'kind-before.lisp').read_text()),
           'machines-c-sealer-events':project_events((FIX/'events-before.lisp').read_text())}
if __name__=='__main__':
 import sys
 for book,s in EXPECTED.items():
  lr.parse(s);p=ROOT/'books'/(book+'.lisp')
  if '--apply' in sys.argv:p.write_text(s)
  elif p.read_text()!=s:raise ValueError('unexpected sealer source mutation: '+book)
