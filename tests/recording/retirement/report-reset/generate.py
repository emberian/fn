from pathlib import Path
import hashlib, json, re
root = Path(__file__).resolve().parents[4]
out = Path(__file__).resolve().parent
forms, sources = {}, {}
def take(file, name, acl2=False, kind="defun"):
    s = (root / file).read_text()
    sources[file] = hashlib.sha256(s.encode()).hexdigest()
    start = re.search(r'\(' + re.escape(kind) + r'\s+' + re.escape(name) + r'(?=\s|\))', s).start()
    depth = 0; string = comment = escape = False
    for i in range(start, len(s)):
        c = s[i]
        if comment:
            if c == '\n': comment = False
            continue
        if string:
            if escape: escape = False
            elif c == '\\': escape = True
            elif c == '"': string = False
            continue
        if c == ';': comment = True
        elif c == '"': string = True
        elif c == '(': depth += 1
        elif c == ')':
            depth -= 1
            if depth == 0:
                form = s[start:i+1]; forms[name] = form
                if acl2 and '(declare (xargs' in form:
                    a = form.index('(declare (xargs'); d = 0
                    for b in range(a, len(form)):
                        if form[b] == '(': d += 1
                        elif form[b] == ')':
                            d -= 1
                            if d == 0: break
                    form = form[:a] + form[b+1:]
                return form
    raise RuntimeError(name)
parts = ['''(require :sb-posix)
(defpackage "ACL2" (:use "CL"))
(in-package "ACL2")
(declaim (notinline sb-posix:unlink))
(defun member-eq (x xs) (member x xs :test #'eq))
(defstruct fnn-owner-service retire stopping)
(defmacro fnn-with-roster ((service) &body body) (declare (ignore service)) `(progn ,@body))
(defun fnn-owner-space-preobserve (service force) (declare (ignore service force)) nil)
(defun fnn-owner-sched-snapshot (service) (declare (ignore service)) :clock)
(defun fnn-owner-retire-report-path (service) (declare (ignore service)) "prior-report")
(defun fnn-log-line (line) (declare (ignore line)) nil)
(defun fnn-fault (format &rest args) (error (apply #'format nil format args)))
(defun fnn-core (name &rest args)
 (if (eq name 'fn-nret-begin-log-line) :line (apply (symbol-function name) args)))
(defvar *fences* 0)
(defvar *barrier-fails* nil)
(defvar *barriers* 0)
(defun fnn-owner-service-store (service) (declare (ignore service)) :store)
(defun fnn-store-root (store) (declare (ignore store)) "root")
(defun fnn-fsync-dir (path) (declare (ignore path)) (incf *barriers*)
 (when *barrier-fails* (error 'fnn-os-error :errno 5 :path "root")))
(defun fnn-owner-fence-service (service)
 (incf *fences*) (setf (fnn-owner-service-stopping service) t))
''']
parts.append(take('books/native-retire.lisp','fn-nret-begin-answer',True))
parts.append(take('books/operator-report-reset.lisp','fn-orr-reset-action',True))
parts.append(take('host/native/io.lisp','fnn-os-error',kind='define-condition'))
parts.append(take('host/native/io.lisp','fnn-store-error',kind='define-condition'))
parts.append(take('host/native/io.lisp','fnn-store-indeterminate',kind='define-condition'))
parts.append(take('host/native/io.lisp','fnn-indeterminate'))
parts.append(take('host/native/owner.lisp','fnn-owner-retire-begin'))
parts.append('''
(defun exercise (mode &optional barrier-fails)
 (let ((old (symbol-function 'sb-posix:unlink))
       (service (make-fnn-owner-service)) (calls 0) (answer nil) (uncertain nil))
  (setf *fences* 0 *barriers* 0 *barrier-fails* barrier-fails)
  (unwind-protect
    (progn
     (setf (symbol-function 'sb-posix:unlink)
       (lambda (path) (declare (ignore path)) (incf calls)
         (case mode (:removed 0)
           (:missing (error 'sb-posix:syscall-error :errno sb-posix:enoent :name "unlink"))
           (:failed (error 'sb-posix:syscall-error :errno sb-posix:eacces :name "unlink")))))
     (handler-case (setf answer (fnn-owner-retire-begin service 4))
       (fnn-store-indeterminate () (setf uncertain t)))
     (assert (equal (fnn-owner-retire-begin service 4)
                    '(:reason :refused :already-retiring)))
     (assert (= calls 1))
     (assert (fnn-owner-service-retire service))
     (format t "RESET ~s answer=~s uncertain=~s fences=~s intent=~s~%"
       mode answer uncertain *fences* (fnn-owner-service-retire service))
     (when (and (not barrier-fails) (member mode '(:removed :missing)))
       (assert (equal answer '(:reason :accepted :draining))) (assert (not uncertain)))
     (when (or (eq mode :failed) barrier-fails)
       (if EXPECT-REPAIR
         (progn (assert uncertain) (assert (null answer))
                (assert (= *fences* 1)) (assert (fnn-owner-service-stopping service)))
         (assert (equal answer '(:reason :accepted :draining))))))
    (setf (symbol-function 'sb-posix:unlink) old))))
(exercise :removed)
(exercise :missing)
(exercise :failed)
(exercise :removed t)
(exercise :missing t)
''')
parts[-1]=parts[-1].replace('EXPECT-REPAIR', 't' if 'fn-orr-reset-action' in forms['fnn-owner-retire-begin'] else 'nil')
# Expected recording outcome is selected from the literal source coordinate.
(out/'actual-reset.lisp').write_text('\n'.join(line.rstrip() for line in '\n'.join(parts).splitlines())+'\n')
(out/'coordinate.json').write_text(json.dumps({'sources':sources,'forms_sha256':{k:hashlib.sha256(v.encode()).hexdigest() for k,v in forms.items()}},indent=2)+'\n')
