;;; Debug-only retained graph observation; never an admission tariff.
;;; PRIMITIVE-OBJECT-SIZE is direct object storage, not allocator/GC overhead.
(in-package "ACL2")

(defun fnmg-graph (roots)
  "Distinct EQ heap objects reachable from ROOTS. Symbols are global leaves;
fixnums and characters immediate. Refuse unsupported types rather than omit."
  (let ((seen (make-hash-table :test 'eq)) (pending (copy-list roots)))
    (loop while pending for object = (pop pending) do
      (unless (or (symbolp object) (characterp object)
                  (typep object 'fixnum) (gethash object seen))
        (unless (or (consp object) (stringp object)
                    (typep object 'bignum) (typep object '(simple-array (unsigned-byte 8) (*))))
          (error "unsupported retained graph type: ~s" (type-of object)))
        (setf (gethash object seen) t)
        (when (consp object) (push (car object) pending) (push (cdr object) pending))))
    seen))

(defun fnmg-owned (graph borrowed &optional constants)
  "Subtract borrowed roots and static/read-only space, not GC-managed immobile
or permgen objects. Caller supplies any additional dynamic constant graph."
  (let ((owned (make-hash-table :test 'eq)))
    (maphash (lambda (object ignored)
               (declare (ignore ignored))
               (unless (or (gethash object borrowed)
                           (and constants (gethash object constants))
                           (member (sb-ext:heap-allocated-p object) '(:static :read-only)))
                 (setf (gethash object owned) t))) graph)
    owned))

(defun fnmg-union (left right)
  (let ((union (make-hash-table :test 'eq)))
    (dolist (graph (list left right))
      (maphash (lambda (object ignored) (declare (ignore ignored))
                 (setf (gethash object union) t)) graph))
    union))

(defun fnmg-summary (graph)
  (let ((conses 0) (strings 0) (bignums 0) (octet-vectors 0) (bytes 0))
    (maphash (lambda (object ignored)
               (declare (ignore ignored))
               (incf bytes (sb-ext:primitive-object-size object))
               (cond ((consp object) (incf conses)) ((stringp object) (incf strings))
                     ((typep object 'bignum) (incf bignums)) (t (incf octet-vectors)))) graph)
    (list :objects (hash-table-count graph) :conses conses :strings strings
          :bignums bignums :octet-vectors octet-vectors :direct-bytes bytes)))

(defun fnmg-json-summary (graph)
  (let ((summary (fnmg-summary graph)))
    (format nil "{~{~a~^,~}}"
            (loop for (key value) on summary by #'cddr
                  collect (format nil "~s:~d" (string-downcase (symbol-name key)) value)))))
