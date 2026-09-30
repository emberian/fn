from pathlib import Path
import hashlib, json, re
root=Path(__file__).resolve().parents[4]
out=Path(__file__).resolve().parent
forms={}; sources={}
def take(file,name):
 s=(root/file).read_text(); sources[file]=hashlib.sha256(s.encode()).hexdigest()
 start=s.index('(defun '+name+' '); depth=0; string=False; comment=False; escape=False
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
  if c==';': comment=True
  elif c=='"': string=True
  elif c=='(': depth+=1
  elif c==')':
   depth-=1
   if depth==0:
    f=s[start:i+1]; forms[name]=f
    return re.sub(r'\(declare \(xargs :guard (?:t|\(natp i\)|\(and \(integerp prior\) \(integerp uncertain\)\))\)\)', '', f)
 raise RuntimeError(name)
parts=['''(defpackage "ACL2" (:use "CL"))
(in-package "ACL2")
(defun natp (x) (and (integerp x) (<= 0 x)))
(defun nfix (x) (if (natp x) x 0))
(defun zp (x) (not (and (integerp x) (> x 0))))
(defparameter *fn-log-sink-close-wait-seconds* 10)
(defvar *fnn-log-queue-mutex* (sb-thread:make-mutex))
(defvar *fnn-log-queue-ready* (sb-thread:make-waitqueue))
(defvar *fnn-log-queue-head* nil)
(defvar *fnn-log-queue-tail* nil)
(defvar *fnn-log-sink* nil)
(defvar *fnn-log-writer* nil)
(defvar *fnn-owner-log-fd* nil)
(defvar *fnn-owner-retained-service* nil)
(defvar *fnn-owner-retained-settlement* :held)
(defvar *fnn-owner-reserving-thread* nil)
(defvar *fnn-owner-caller-reservation* nil)
(defparameter +fnn-lock-un+ 8)
(defstruct fnn-log fd spare)
(defstruct fnn-store log lock-fd completion-pending fenced)
(defstruct fnn-owner-service store)
(defvar *recorded* nil)
(defvar *fail-close* nil)
(defvar *entered* (sb-thread:make-semaphore))
(defvar *release* (sb-thread:make-semaphore))
(defun alive () (and *fnn-log-writer* (sb-thread:thread-alive-p *fnn-log-writer*)))
(defun fnn-close (fd) (push (list :close fd (alive)) *recorded*)
 (when (eql fd *fail-close*) (error "recording physical close uncertainty")))
(defun fnn-flock (fd mode) (push (list :flock fd mode (alive)) *recorded*))
(defun fnn-lstat (path) (declare (ignore path)) t)
(defun fnn-unlink (path) (push (list :unlink path (alive)) *recorded*))
(defun fnn-fault (&rest args) (error "fault ~s" args))
(defun fnn-indeterminate (&rest args) (error "uncertain ~s" args))
(defun fnn-log-write-item (destination octets)
 (sb-thread:signal-semaphore *entered*)
 (assert (sb-thread:wait-on-semaphore *release* :timeout 30))
 (push (list :journal-write destination (length octets)) *recorded*) :written)
''']
for n in ['fn-log-sink-field','fn-log-sink-pending-octets','fn-log-sink-pending-lines','fn-log-sink-dropped','fn-log-sink-written','fn-log-sink-offered','fn-log-sink-init','fn-log-sink-offer','fn-log-sink-take','fn-log-sink-close-wait-seconds']:
 parts.append(take('books/log-sink.lisp',n))
for n in ['fn-ort-log-close-action','fn-ort-log-close-exit','fn-ort-report-close-action','fn-ort-store-close-action','fn-ort-service-settlement-action','fn-ort-service-start-action','fn-ort-service-claim-action','fn-ort-service-start-reason']:
 parts.append(take('books/owner-retire-settlement.lisp',n))
parts.append('''(defun fnn-core (name &rest args) (apply (symbol-function name) args))''')
for n in ['fnn-log-queue-push','fnn-log-sink-accept','fnn-log-writer-loop','fnn-log-writer-start','fnn-log-writer-stop','fnn-log-discard-spare','fnn-store-close']:
 parts.append(take('host/native/io.lisp',n))
for n in ['fnn-owner-run-admission','fnn-owner-claim-run-authority','fnn-owner-retain-run-authority','fnn-owner-store-settlement']:
 parts.append(take('host/native/owner.lisp',n))
parts.append('''
(let* ((store (make-fnn-store :log (make-fnn-log :fd 401) :lock-fd 402 :completion-pending :owed))
       (service (make-fnn-owner-service :store store)))
 (assert (eq (fnn-owner-run-admission) :start))
 (fnn-owner-claim-run-authority)
 ;; Initial reservation rejects another caller; only its dynamic owner-entry
 ;; token can consume it before installing the service.
 (assert (handler-case (progn (fnn-owner-claim-run-authority nil) nil) (error () t)))
 (let ((worker (sb-thread:make-thread
          (lambda () (handler-case (progn (fnn-owner-claim-run-authority t) nil) (error () t))))))
  (assert (eq (sb-thread:join-thread worker) t)))
 (fnn-owner-claim-run-authority t)
 (fnn-owner-retain-run-authority service)
 (fnn-log-writer-start)
 (sb-thread:with-recursive-lock (*fnn-log-queue-mutex*)
  (dotimes (i 2)
   (let ((answer (fnn-core 'fn-log-sink-offer *fnn-log-sink* 3 1048576)))
    (assert (eq (first answer) :queue))
    (fnn-log-sink-accept (second answer) :fixture)
    (fnn-log-queue-push (cons :journal '(65 66 10))))))
 (assert (sb-thread:wait-on-semaphore *entered* :timeout 2))
 (assert (eq (fnn-log-writer-stop) :timeout))
 (assert (alive))
 (assert *fnn-log-queue-head*)
 (assert (= (fn-log-sink-pending-lines *fnn-log-sink*) 2))
 (assert (= (fn-log-sink-pending-octets *fnn-log-sink*) 6))
 (let ((settlement (fn-ort-log-close-action :timeout 2 6 t)))
  (assert (eq settlement :held))
  (assert (eq (fnn-owner-store-settlement service settlement) :held)))
 (assert (null *recorded*))
 (assert (eq *fnn-owner-retained-service* service))
 (assert (= (fnn-store-lock-fd store) 402))
 (assert (= (fnn-log-fd (fnn-store-log store)) 401))
 (assert (eq (fnn-owner-run-admission) :held))
 (assert (handler-case (progn (fnn-owner-claim-run-authority) nil) (error () t)))
 (assert (eq *fnn-owner-retained-service* service))
 (format t "PASS queued-timeout retains actual writer/service/Store descriptors and startup fence~%")
 (sb-thread:signal-semaphore *release*)
 (assert (sb-thread:wait-on-semaphore *entered* :timeout 2))
 (sb-thread:signal-semaphore *release*)
 (assert (eq (fnn-log-writer-stop) :joined))
 (assert (null *fnn-log-writer*))
 (assert (null *fnn-log-queue-head*))
 (assert (= (fn-log-sink-pending-lines *fnn-log-sink*) 0))
 (assert (= (fn-log-sink-pending-octets *fnn-log-sink*) 0))
 (let ((settlement (fn-ort-report-close-action
                     (fn-ort-log-close-action :joined 0 0 nil) :closed)))
  (setq *fnn-owner-log-fd* 403)
  (assert (eq (fnn-owner-store-settlement service settlement) :joined))
  (assert (eq *fnn-owner-retained-service* service))
  (assert (= (fnn-store-lock-fd store) 402))
  (assert (eq (fnn-owner-run-admission) :held))
  (assert (= (length *recorded*) 2))
  (fnn-close *fnn-owner-log-fd*)
  (setq *fnn-owner-log-fd* nil)
  (assert (eq (fnn-owner-store-settlement service settlement) :joined)))
 (assert (null *fnn-owner-retained-service*))
 (assert (null (fnn-store-log store)))
 (assert (null (fnn-store-lock-fd store)))
 (assert (null (fnn-store-completion-pending store)))
 (assert (eq (fnn-owner-run-admission) :start))
 (assert (= (count '(:close 401 nil) *recorded* :test #'equal) 1))
 (assert (= (count '(:close 402 nil) *recorded* :test #'equal) 1))
 (assert (= (count '(:flock 402 8 nil) *recorded* :test #'equal) 1))
 (format t "PASS joined writer, caller defer, actual Store teardown exactly once~%"))
;; A failed record-log close cannot silently count as :closed or erase
;; its actual handle. A lock close fault preserves recovery authority but
;; makes no claim that the already-attempted unlock left the lock held.
(dolist (failing-fd '(503 501 502))
 (let* ((store (make-fnn-store :log (make-fnn-log :fd 501
                   :spare (and (= failing-fd 503) (list 1 "/recording-stage" 503))) :lock-fd 502))
        (service (make-fnn-owner-service :store store))
        (*fnn-owner-retained-service* nil)
        (*fnn-owner-retained-settlement* :held)
        (*fail-close* failing-fd))
  (fnn-owner-claim-run-authority)
  (fnn-owner-retain-run-authority service)
  (assert (eq (fnn-owner-store-settlement service :joined) :held))
  (assert (eq *fnn-owner-retained-service* service))
  (assert (= (fnn-store-lock-fd store) 502))
  (when (member failing-fd '(501 503))
   (assert (= (fnn-log-fd (fnn-store-log store)) 501)))
  (when (= failing-fd 503)
   (assert (equal (fnn-log-spare (fnn-store-log store)) '(1 "/recording-stage" 503))))
  (assert (eq (fnn-owner-run-admission) :held))
  (assert (fnn-store-fenced store))
  ;; Existing continuation carries :held, so it never retries/reuses an
  ;; ambiguously closed descriptor. These are independent recording Stores.
  (let ((count-before (length *recorded*)))
   (assert (eq (fnn-owner-store-settlement service *fnn-owner-retained-settlement*) :held))
   (assert (= count-before (length *recorded*))))))
(format t "PASS physical-close uncertainty preserves handles/recovery authority; no held-lock inference~%")
(format t "STORE-AUTHORITY-PASS ~s~%" (reverse *recorded*))
''')
(out/'actual-store-authority.lisp').write_text('\n\n'.join(parts)+'\n')
(out/'source-forms.json').write_text(json.dumps(forms,indent=2)+'\n')
(out/'coordinate.json').write_text(json.dumps({'sources':sources,'scope':'Actual writer loop/start/stop/queue/sink, owner authority helpers and Store close; real SBCL semaphore/thread/join. Literal ACL2 scalar/sink functions with xargs removed. Recording filesystem calls and journal write; no actual disk/native image/ACL2 proof claim.'},indent=2)+'\n')
# Compose the actual outer caller with the same actual Store-authority helpers.
# Reuse only the recording configuration/I/O prelude of the earlier caller
# fixture; its old simulated owner callback/function bodies are excluded.
prelude=(root/'tests/recording/retirement/caller-repair.lisp').read_text().split('(defun fnn-control-owner-run-normalized')[0].replace('UNEXPECTED ~a', 'RECORDING condition ~a')
caller=[f'(load "{out / "actual-store-authority.lisp"}")',prelude,
'''(defparameter +fnn-exit-uncertain+ 3)
(defvar *caller-mode* :held)
(defvar *caller-service* nil)
(defun fnn-core (name &rest args)
 (case name
  ((fn-native-health-host-run-started-line fn-native-health-host-run-stopped-line) '(65))
  (otherwise (if (fboundp name) (apply (symbol-function name) args) nil))))
(defun fnn-control-owner-run-normalized (&rest args)
 (declare (ignore args))
 (fnn-owner-claim-run-authority *fnn-owner-caller-reservation*)
 (setq *caller-service* (make-fnn-owner-service
         :store (make-fnn-store :log (make-fnn-log :fd 601) :lock-fd 602)))
 (fnn-owner-retain-run-authority *caller-service*)
 (if (eq *caller-mode* :held)
  (progn
   (fnn-log-writer-start)
   (sb-thread:with-recursive-lock (*fnn-log-queue-mutex*)
    (let ((answer (fn-log-sink-offer *fnn-log-sink* 3 1048576)))
     (fnn-log-sink-accept (second answer) :caller)
     (fnn-log-queue-push (cons :journal '(65 66 10)))))
   (assert (sb-thread:wait-on-semaphore *entered* :timeout 2))
   (assert (eq (fnn-log-writer-stop) :timeout))
   (assert (eq (fnn-owner-store-settlement *caller-service* :held) :held))
   3)
  (progn
   (assert (eq (fnn-owner-store-settlement *caller-service* :joined) :joined)) 0)))
''', take('host/native/operator.lisp','fnn-operator-log-run-line'),take('host/native/operator-live.lisp','fnn-operator-execute-run'),
'''(setq *recorded* nil *caller-mode* :held)
(assert (= (fnn-operator-execute-run nil) 3))
(assert (alive))
(assert (= *fnn-owner-log-fd* 123))
(assert (eq *fnn-owner-retained-service* *caller-service*))
(assert (= (fnn-store-lock-fd (fnn-owner-service-store *caller-service*)) 602))
(assert (equal (reverse *recorded*) '((:write 123 nil))))
(let ((before *recorded*))
 (assert (= (fnn-operator-execute-run nil) 99))
 (assert (eq before *recorded*)))
(sb-thread:signal-semaphore *release*)
(assert (eq (fnn-log-writer-stop) :joined))
;; Recording recovery continuation supplies a fresh definite journal-settled
;; observation after actual writer join, then relinquishes caller descriptor.
(setq *fnn-owner-retained-settlement* :joined)
(fnn-close *fnn-owner-log-fd*)
(setq *fnn-owner-log-fd* nil *fnn-owner-log-path* nil)
(assert (eq (fnn-owner-store-settlement *caller-service* :joined) :joined))
(setq *recorded* nil *caller-mode* :joined)
(assert (= (fnn-operator-execute-run nil) 0))
(assert (null *fnn-owner-log-fd*))
(assert (null *fnn-owner-retained-service*))
(assert (equal (reverse *recorded*)
 '((:write 123 nil) (:write 123 nil) (:close 123 nil)
   (:close 601 nil) (:flock 602 8 nil) (:close 602 nil))))
(format t "PASS actual outer caller: held writer bypasses stop write/FD/Store close; reentry fenced; joined exact teardown~%")
(format t "STORE-CALLER-PASS ~s~%" (reverse *recorded*))
''']
(out/'actual-store-caller.lisp').write_text('\n\n'.join(caller)+'\n')
(out/'source-forms.json').write_text(json.dumps(forms,indent=2)+'\n')
(out/'coordinate.json').write_text(json.dumps({'sources':sources,'scope':'Actual writer loop/start/stop/queue/sink, owner authority helpers, spare/Store close and outer operator caller; real SBCL semaphore/thread/join. Literal ACL2 scalar/sink functions with xargs removed. Recording filesystem calls and journal writes, configuration projections and owner callback. No actual disk/native image/ACL2 proof claim.'},indent=2)+'\n')
