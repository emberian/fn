; A world book name for fn's provenance checks and diagnostic dumps.
; Use ACL2's project mapping, never a basename or an unqualified sysfile cdr:
; :SYSTEM and other projects must not impersonate a book of :FN. Unmapped
; absolute names retain their directory, including a foreign tree's root.
(in-package "ACL2")

(defun book-name-relative (book projects)
  (declare (xargs :mode :logic :guard t))
  (let ((name (filename-to-book-name-1 book projects)))
    (cond ((stringp name) name)
          ((sysfile-p name)
           (if (eq (car name) :fn)
               (cdr name)
             (concatenate 'string ":" (string-downcase (symbol-name (car name)))
                          "/" (cdr name))))
          (t nil))))
