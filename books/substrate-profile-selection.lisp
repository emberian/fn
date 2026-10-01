; Profile-aware retained carrier/group selection, no authority grant.
(in-package "ACL2")
(include-book "substrate-profile-entry")
(defun fn-stpr-project (selected profile cfg generation keyring)
 (declare (xargs :guard t))
 (list :fn-stpr profile (fn-stcp-at 1 selected) (fn-stcp-at 2 selected)
       cfg generation keyring))
; A selected carrier starts only after a caller has carried its statement
; invariant. The group and pinned policy source remain separate fields.
(defun fn-stpr-entry-start (cursor group statement)
 (declare (xargs :guard (fn-stmt-p statement)
                 :guard-hints (("Goal" :in-theory (e/d (fn-stmt-p) (fn-stpe-resume fn-stpe-resume-model fn-stpr-entry-start fn-stcp-at))))))
 (fn-stpe-start (fn-stcp-at 1 cursor) group statement))
; Each selection step visits one group/statement boundary. Decoder resumes use
; the selected profile quantum. No authority decision is made by projection.
(defun fn-stpr-select-start (projection)
 (declare (xargs :guard t))
 (list :fn-stpr-select projection (fn-stcp-at 2 projection)
       (fn-stcp-at 3 projection) nil))
(defun fn-stpr-select-resume (cursor)
 (declare (xargs :guard
  (or (fn-stcp-at 4 cursor) (atom (fn-stcp-at 2 cursor))
      (atom (fn-stcp-at 3 cursor))
      (fn-stmt-p (car (fn-stcp-at 2 cursor))))
  :guard-hints (("Goal" :in-theory (e/d (fn-stmt-p) (fn-stpe-resume fn-stpe-resume-model fn-stpr-entry-start fn-stcp-at))))))
 (let ((projection (fn-stcp-at 1 cursor))
       (statements (fn-stcp-at 2 cursor))
       (groups (fn-stcp-at 3 cursor))
       (entry (fn-stcp-at 4 cursor)))
  (cond
   (entry
    (mv-let (word next envelope used) (fn-stpe-resume entry)
     (if (equal word :yield)
         (mv :yield (list :fn-stpr-select projection statements groups next)
             nil used)
       (mv word (list :fn-stpr-select projection statements (fn-cbor-ag-cdr groups) nil)
           envelope used))))
   ((atom statements) (mv :exhausted cursor nil 0))
   ((atom groups)
    (mv :yield (list :fn-stpr-select projection (cdr statements)
                    (fn-stcp-at 3 projection) nil) nil 1))
   (t
    (mv :yield (list :fn-stpr-select projection statements groups
                    (fn-stpr-entry-start projection (car groups) (car statements)))
        nil 1)))))

(defun fn-stpr-select-resume-model (cursor)
 (declare (xargs :guard
  (or (fn-stcp-at 4 cursor) (atom (fn-stcp-at 2 cursor))
      (atom (fn-stcp-at 3 cursor))
      (fn-stmt-p (car (fn-stcp-at 2 cursor))))
  :guard-hints (("Goal" :in-theory (e/d (fn-stmt-p) (fn-stpe-resume fn-stpe-resume-model fn-stpr-entry-start fn-stcp-at))))))
 (let ((projection (fn-stcp-at 1 cursor))
       (statements (fn-stcp-at 2 cursor))
       (groups (fn-stcp-at 3 cursor))
       (entry (fn-stcp-at 4 cursor)))
  (cond
   (entry
    (mv-let (word next envelope used) (fn-stpe-resume-model entry)
     (if (equal word :yield)
         (mv :yield (list :fn-stpr-select projection statements groups next)
             nil used)
       (mv word (list :fn-stpr-select projection statements (fn-cbor-ag-cdr groups) nil)
           envelope used))))
   ((atom statements) (mv :exhausted cursor nil 0))
   ((atom groups)
    (mv :yield (list :fn-stpr-select projection (cdr statements)
                    (fn-stcp-at 3 projection) nil) nil 1))
   (t
    (mv :yield (list :fn-stpr-select projection statements groups
                    (fn-stpr-entry-start projection (car groups) (car statements)))
        nil 1)))))

(defthm fn-stpr-select-resume-refines-model
 (equal (fn-stpr-select-resume cursor)
        (fn-stpr-select-resume-model cursor))
 :hints (("Goal"
  :use ((:instance fn-stpe-resume-refines-model
                   (cursor (fn-stcp-at 4 cursor))))
  :in-theory (union-theories (theory 'minimal-theory)
                            '(fn-stpr-select-resume
                              fn-stpr-select-resume-model)))))
