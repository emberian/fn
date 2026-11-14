(in-package "ACL2")
(include-book "../books/columns")
(include-book "std/testing/must-fail" :dir :system)
(defcolumns fn2-fixed-array ((value :u8))
 :extra-fields ((fn2-fixed-directory :type (array (unsigned-byte 32) (16))
                 :initially 0 :why "Fixed-cardinality directory guard fixture.")))
(in-theory (disable fn2-fixed-arrayp fn2-fixed-directoryi fn2-fixed-directory-length))
; The raw list-length theorem alone cannot discharge an opaque accessor guard.
(must-fail
 (encapsulate ()
  (local (in-theory (disable fn2-fixed-directory-length-fixed)))
  (defun fn2-fixed-array-without-bridge (i fn2-fixed-array)
   (declare (xargs :stobjs fn2-fixed-array
                   :guard (and (natp i) (< i 16))))
   (+ 1 (fn2-fixed-directoryi i fn2-fixed-array)))))
(defun fn2-fixed-array-plus (i fn2-fixed-array)
 (declare (xargs :stobjs fn2-fixed-array :guard (and (natp i) (< i 16))))
 (+ 1 (fn2-fixed-directoryi i fn2-fixed-array)))
; The bridge must preserve the actual array boundary, not invent a total accessor.
(must-fail
 (defun fn2-fixed-array-past-end (fn2-fixed-array)
  (declare (xargs :stobjs fn2-fixed-array))
  (+ 1 (fn2-fixed-directoryi 16 fn2-fixed-array))))
(defun fn2-fixed-array-live ()
 (declare (xargs :guard t))
 (with-local-stobj fn2-fixed-array
  (mv-let (answer fn2-fixed-array)
   (let ((fn2-fixed-array (update-fn2-fixed-directoryi 15 7 fn2-fixed-array)))
    (mv (and (equal (fn2-fixed-directory-length fn2-fixed-array) 16)
             (equal (fn2-fixed-array-plus 0 fn2-fixed-array) 1)
             (equal (fn2-fixed-array-plus 15 fn2-fixed-array) 8)) fn2-fixed-array))
   answer)))
(assert-event (fn2-fixed-array-live))
