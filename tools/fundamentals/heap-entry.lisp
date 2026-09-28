; tools/fundamentals: a measurement-only hook for the developer image, loaded
; by build_heap_image.sh just before host/native/build.lisp's save-exec.
; It wraps fnn-main so that the file FN_PROF_LOAD names (hook.lisp or
; heap.lisp: the live-heap hooks F1 and F6 read) is loaded at start, before
; the owner runs; the entry itself is build.lisp's, whatever it is at the
; tree's revision.  The image it makes is an instrument, never a release.
(in-package "ACL2")
(let ((main (symbol-function 'fnn-main)))
  (setf (symbol-function 'fnn-main)
        (lambda (&rest arguments)
          (let ((extra (sb-ext:posix-getenv "FN_PROF_LOAD")))
            (when (and extra (plusp (length extra)))
              (load extra)))
          (apply main arguments))))
