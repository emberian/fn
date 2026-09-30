from pathlib import Path
import hashlib,json
root=Path('/Users/ember/dev/fn/build/lanes/operability-3')
out=Path('/Users/ember/dev/fn/build/coordinator/retire-observer-review')
sources={}
forms={}
def take(file,name,kind='defun'):
 s=(root/file).read_text(); sources[file]=hashlib.sha256(s.encode()).hexdigest()
 start=s.index('('+kind+' '+name+' '); depth=0; string=False; comment=False; escape=False
 for i in range(start,len(s)):
  c=s[i]
  if comment:
   if c=='\n': comment=False
   continue
  if string:
   if escape: escape=False
   elif c=='\\': escape=True
   elif c=='"': string=False
   continue
  if c==';':comment=True
  elif c=='"':string=True
  elif c=='(':depth+=1
  elif c==')':
   depth-=1
   if depth==0:
    form=s[start:i+1]; forms[name]=form; return form.replace('(declare (xargs :guard t))','')
 raise Exception(name)
parts=['''(defpackage "ACL2" (:use "CL"))
(in-package "ACL2")
(defun nfix (x) (if (and (integerp x) (<= 0 x)) x 0))
(defstruct fnn-owner-service retire stopping (roster (sb-thread:make-mutex)))
(defvar *fnn-sigterm-requested* nil)
(defvar *semantic-lock* (sb-thread:make-mutex))
(defvar *clock* 0)
(defvar *hold-clock* nil)
(defvar *clock-observed* (sb-thread:make-semaphore))
(defvar *release-clock* (sb-thread:make-semaphore))
(defvar *semantic-calls* 0)
(defun snapshot (n) (list nil nil (list n)))
(defun fnn-owner-sched-snapshot (service)
 (declare (ignore service))
 (let ((s (snapshot *clock*)))
  (when *hold-clock*
   (sb-thread:signal-semaphore *clock-observed*)
   (assert (sb-thread:wait-on-semaphore *release-clock* :timeout 3)))
  s))
(defun fnn-owner-serialized (&rest args)
 (declare (ignore args)) (incf *semantic-calls*)
 (sb-thread:with-mutex (*semantic-lock*) (error "Unexpected semantic call")))
(defun fnn-fault (&rest args) (error "unexpected fault ~s" args))
''']
for n in ['fn-otm-clock','fn-otm-c-now','fn-otm-now']:parts.append(take('books/owner-time-model.lisp',n))
parts.append(take('books/owner-stop-drain.lisp','fn-osd-elapsed'))
for n in ['fn-ort-window-step','fn-ort-retire-observer-action','fn-ort-retire-publish']:parts.append(take('books/owner-retire-counted.lisp',n))
parts.append('''(defun fnn-core (name &rest args)
 (assert (member name '(fn-ort-window-step fn-ort-retire-observer-action fn-ort-retire-publish)))
 (apply (symbol-function name) args))''')
parts.append(take('host/native/owner.lisp','fnn-with-roster','defmacro'))
parts.append(take('host/native/owner.lisp','fnn-owner-maybe-retire'))
parts.append('''
(defun join-checked (worker)
 (multiple-value-bind (value status) (sb-thread:join-thread worker :timeout 2 :default :timeout)
  (declare (ignore value)) (assert (null status))))
(defun fresh-service () (make-fnn-owner-service :retire (list (snapshot 0) 1)))
;; A semantic mutex held across both observations must not block the observer.
(let ((service (fresh-service)))
 (setq *fnn-sigterm-requested* nil)
 (sb-thread:with-mutex (*semantic-lock*)
  (join-checked (sb-thread:make-thread (lambda () (let ((*clock* 0)) (fnn-owner-maybe-retire service)))))
  (assert (null *fnn-sigterm-requested*))
  (join-checked (sb-thread:make-thread (lambda () (let ((*clock* 2000)) (fnn-owner-maybe-retire service)))))
  (assert (eq (third (fnn-owner-service-retire service)) :deadline))
  (assert *fnn-sigterm-requested*)
  (assert (zerop *semantic-calls*)))
 (format t "PASS held-semantic-mutex before-and-after-deadline~%"))
;; Force an old clock observation to resume only after deadline publication.
(dotimes (i 25)
 (let ((service (fresh-service)) (stale nil))
  (setq *fnn-sigterm-requested* nil)
  (sb-thread:with-mutex (*semantic-lock*)
   (setq stale (sb-thread:make-thread
    (lambda () (let ((*clock* 0) (*hold-clock* t)) (fnn-owner-maybe-retire service)))))
   (assert (sb-thread:wait-on-semaphore *clock-observed* :timeout 2))
   (join-checked (sb-thread:make-thread (lambda () (let ((*clock* 2000)) (fnn-owner-maybe-retire service)))))
   (let ((completed (fnn-owner-service-retire service)))
    (assert (eq (third completed) :deadline))
    (assert *fnn-sigterm-requested*)
    (sb-thread:signal-semaphore *release-clock*)
    (join-checked stale)
    (assert (eq completed (fnn-owner-service-retire service)))
    (assert *fnn-sigterm-requested*)
    ;; Complete observations skip clock I/O altogether.
    (let ((*clock* 0) (*hold-clock* t)) (fnn-owner-maybe-retire service))
    (assert (eq completed (fnn-owner-service-retire service)))))))
(format t "PASS forced-stale-wait-after-deadline 25 iterations~%")
;; Both observers have captured pending metadata before either can publish.
(dotimes (i 25)
 (let ((service (fresh-service)) (workers nil))
  (setq *fnn-sigterm-requested* nil)
  (dotimes (j 2)
   (push (sb-thread:make-thread
    (lambda () (let ((*clock* 2000) (*hold-clock* t)) (fnn-owner-maybe-retire service)))) workers))
  (dotimes (j 2) (assert (sb-thread:wait-on-semaphore *clock-observed* :timeout 2)))
  (sb-thread:signal-semaphore *release-clock* 2)
  (mapc #'join-checked workers)
  (assert (equal (fnn-owner-service-retire service) (list (snapshot 0) 1 :deadline)))
  (assert *fnn-sigterm-requested*)))
(assert (zerop *semantic-calls*))
(format t "PASS two-concurrent-deadline-observers 25 iterations~%")
''')
fixture='\n\n'.join(parts)+'\n'
(out/'actual-observer.lisp').write_text(fixture)
(out/'source-forms.json').write_text(json.dumps(forms,indent=2)+'\n')
(out/'coordinate.json').write_text(json.dumps({'source_root':str(root),'sources':sources,'fixture_sha256':hashlib.sha256(fixture.encode()).hexdigest(),'scope':'Actual native function and roster macro; actual ACL2 decision bodies evaluated as Common Lisp with xargs declarations removed. Recording clock/dispatch, minimal service struct, actual SBCL synchronization. Not ACL2 proof, complete scheduler, image, native disk, funding or shutdown qualification.'},indent=2)+'\n')
