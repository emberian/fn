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
(defmacro mv (&rest xs) `(values ,@xs))
(defun member-eq (x xs) (member x xs :test #'eq))
(defun natp (x) (and (integerp x) (<= 0 x)))
(deftype fnn-octets () '(simple-array (unsigned-byte 8) (*)))
(defun assoc-equal (x xs) (assoc x xs :test #'equal))
(defvar *allocations* nil)
(defvar *actions* nil)
(defvar *rewind-hook* nil)
(defun fnn-call (name &rest args) (multiple-value-list (apply (symbol-function name) args)))
(defun fnn-core (name &rest args)
 (let ((value (first (apply #'fnn-call name args))))
  (when (eq name 'fn-oru-reader-action)
   (push value *actions*)
   (when (and (eq value :rewind) *rewind-hook*) (funcall *rewind-hook*))) value))
''']
parts.append(take('books/outcome-class.lisp', '*fn-outcome-codes*', kind='defconst').replace('(defconst ', '(defparameter ', 1))
for n in ['fn-outcome-code','fn-outcome-of-host-condition','fn-outcome-host-condition-exit-code']:
    parts.append(take('books/outcome-class.lisp', n, True))
for n in ['fnn-store-error','fnn-store-fault','fnn-store-indeterminate','fnn-usage-error']:
    parts.append(take('host/native/io.lisp', n, kind='define-condition'))
parts.append(take('host/native/io.lisp', '+fnn-exit-ok+', kind='defconstant'))
for n in ['fnn-fault','fnn-exit-code-for']:
    parts.append(take('host/native/io.lisp', n))
for n in ['fn-cbor-octetp','fn-cbor-octet-listp','fn-cbor-at-mostp']:
    parts.append(take('books/cbor.lisp', n, True))
for n in ['fn-wildmat-octetp','fn-wildmat-octet-listp','fn-wildmat-at-mostp',
          'fn-wildmat-ok','fn-wildmat-error','fn-wildmat-result-okp',
          'fn-wildmat-result-value','fn-wildmat-utf8-ok','fn-wildmat-utf8-rest',
          'fn-wildmat-utf8-tailp','fn-wildmat-utf8-2p','fn-wildmat-utf8-3-tailsp',
          'fn-wildmat-utf8-4-tailsp','fn-wildmat-utf8-2-value',
          'fn-wildmat-utf8-3-value','fn-wildmat-utf8-4-value','fn-wildmat-utf8-next']:
    parts.append(take('books/utf8.lisp', n, True))
for n in ['fn-oru-lead-width','fn-oru-cursor','fn-oru-ready-p','fn-oru-start',
          'fn-oru-step','fn-oru-reader-phasep','fn-oru-reader-action','fn-oru-reader-step']:
    parts.append(take('books/operator-report-reader.lisp', n, True))
for n in ['fnn-make-octets','fnn-octets','fnn-string-octets','fnn-octets-string']:
    parts.append(take('host/native/io.lisp', n))
parts.append(take('host/native/io.lisp','fnn-os-error',kind='define-condition'))
parts.append(take('host/native/io.lisp','fnn-os-fail'))
parts.append(take('host/native/io.lisp','fnn-posix',kind='defmacro'))
for n in ['fnn-replace','fnn-unlink','fnn-fstat']:
    parts.append(take('host/native/io.lisp',n))
parts.append(take('host/native/operator.lisp','fnn-operator-read-retire-report-bounded'))
parts.append('''
(let ((actual (symbol-function 'fnn-make-octets)))
 (setf (symbol-function 'fnn-make-octets)
       (lambda (n) (push n *allocations*) (funcall actual n))))
(defun test-case (octets validp)
 (let ((input #p"reader-input.bin") (output #p"reader-output.bin")
       (status nil) (failed nil) (result nil))
  (unwind-protect
   (progn
    (with-open-file (s input :direction :output :if-exists :supersede
                       :element-type '(unsigned-byte 8))
     (write-sequence (fnn-octets octets) s))
    (setf *allocations* nil *actions* nil)
    (with-open-file (in input :element-type '(unsigned-byte 8))
     (with-open-file (out output :direction :output :if-exists :supersede
                          :element-type '(unsigned-byte 8))
      (handler-case (setf status (fnn-operator-read-retire-report-bounded in out))
       (error (c) (setf failed t status (fnn-exit-code-for c))))))
    (assert (null *allocations*))
    (with-open-file (s output :element-type '(unsigned-byte 8))
     ;; Whole arrays below belong only to this fixture's reference observer.
     (let ((v (make-array (file-length s) :element-type '(unsigned-byte 8))))
      (read-sequence v s) (setf result (coerce v 'list))))
    (if validp
     (progn (assert (and (not failed) (eql status (fn-outcome-code :accepted)) (equal result octets)))
      (assert (= (count :rewind *actions*) 1))
      (assert (= (count :read-validate *actions*) (1+ (length octets))))
      (assert (= (count :read-copy *actions*) (1+ (length octets))))
      (assert (equal (coerce (fnn-string-octets (fnn-octets-string octets)) 'list) octets)))
     (progn (assert failed) (assert (= status (fn-outcome-code :fault))) (assert (null result))
      (assert (not (member :rewind *actions*)))
      (assert (not (member :read-copy *actions*)))
      (assert (eql status (handler-case (progn (fnn-octets-string octets) nil)
                           (error (c) (fnn-exit-code-for c)))))))
    (format t "PASS input=~d valid=~s output=~d exit=~d reader-explicit-vector-allocations=~d~%"
            (length octets) validp (length result) status 0))
   (ignore-errors (delete-file input)) (ignore-errors (delete-file output)))))
(format t "Runtime ~a ~a~%" (lisp-implementation-type) (lisp-implementation-version))
(test-case nil t)
(test-case '(0 65 127 194 128 223 191 224 160 128 237 159 191
             239 191 191 240 144 128 128 244 143 191 191) t)
(test-case (make-list 600 :initial-element 65) t)
(test-case '(239 187 191 65 239 183 144 239 191 190 239 187 191) t)
(dolist (bad '((192 128) (224 128 128) (237 160 128) (244 144 128 128)
               (240 144 128) (255)))
 (test-case (append (make-list 600 :initial-element 65) bad) nil))

(defun descriptor-test (mode)
 (let ((input #p"descriptor-input.bin") (stage #p"descriptor-stage.bin")
       (output #p"descriptor-output.bin")
       (old '(65 194 128 224 160 128 244 143 191 191))
       (new '(78 69 87)) (result nil) (fired nil))
  (unwind-protect
   (progn
    (dolist (item (list (cons input old) (cons stage new)))
     (with-open-file (s (car item) :direction :output :if-exists :supersede
                        :element-type '(unsigned-byte 8))
      (write-sequence (fnn-octets (cdr item)) s)))
    (with-open-file (in input :element-type '(unsigned-byte 8))
     (with-open-file (out output :direction :output :if-exists :supersede
                          :element-type '(unsigned-byte 8))
      (let* ((fd (sb-sys:fd-stream-fd in))
             (inode (sb-posix:stat-ino (fnn-fstat fd)))
             (*rewind-hook*
               (lambda ()
                (assert (not fired)) (setf fired t)
                (assert (= (file-position out) 0))
                (ecase mode
                 (:replace (fnn-replace (namestring stage) (namestring input))
                           (assert (/= inode (sb-posix:stat-ino
                                              (sb-posix:stat (namestring input))))))
                 (:unlink (fnn-unlink (namestring input))
                          (assert (not (probe-file input)))))
                (assert (= inode (sb-posix:stat-ino (fnn-fstat fd)))))))
       (assert (= (fnn-operator-read-retire-report-bounded in out)
                  (fn-outcome-code :accepted)))
       (assert fired))))
    (with-open-file (s output :element-type '(unsigned-byte 8))
     (loop for byte = (read-byte s nil nil) while byte do (push byte result)))
    (assert (equal (reverse result) old))
    (format t "PASS real descriptor ~s at rewind: original inode/bytes retained, exit0~%" mode))
   (dolist (path (list input stage output)) (ignore-errors (delete-file path))))))
(defun nonseekable-test ()
 (multiple-value-bind (read-fd write-fd) (sb-posix:pipe)
  (let ((output #p"descriptor-pipe-output.bin") (status nil) (*actions* nil))
   (unwind-protect
    (progn
     (with-open-stream (write-stream (sb-sys:make-fd-stream write-fd :output t
                                      :element-type '(unsigned-byte 8) :buffering :none))
      (write-sequence (fnn-octets '(65 194 128)) write-stream))
     (with-open-stream (in (sb-sys:make-fd-stream read-fd :input t
                              :element-type '(unsigned-byte 8) :buffering :none))
      (with-open-file (out output :direction :output :if-exists :supersede
                           :element-type '(unsigned-byte 8))
       (handler-case (setf status (fnn-operator-read-retire-report-bounded in out))
        (error (condition) (setf status (fnn-exit-code-for condition))))
       (assert (= (file-position out) 0))))
     (assert (= status (fn-outcome-code :fault)))
     (assert (member :rewind *actions*))
     (assert (not (member :read-copy *actions*)))
     (format t "PASS actual nonseekable binary descriptor: validated, rewind refused, output0 exit4~%"))
    (ignore-errors (delete-file output))))))
(descriptor-test :replace)
(descriptor-test :unlink)
(nonseekable-test)

(format t "PASS actual bounded host consumer / real binary streams; extracted ACL2 bodies and recording dispatcher, no activation/funding claim~%")
''')
(out / 'actual-reader.lisp').write_text('\n'.join(line.rstrip() for line in '\n'.join(parts).splitlines()) + '\n')
(out / 'coordinate.json').write_text(json.dumps({
    'scope': 'Actual additive host reader, actual SBCL binary streams/codecs; xargs removed from exact ACL2 bodies, MV mapped to CL values, trailing whitespace stripped, recording dispatcher. Finite differential witnesses, not library proof/native qualification/funding/activation.',
    'sources': sources, 'forms_sha256': {k: hashlib.sha256(v.encode()).hexdigest() for k,v in forms.items()},
}, indent=2) + '\n')
