; Exact geometry admission, separate from full service quota admission.
(in-package "ACL2")
(include-book "../books/upload-page-geometry")
(include-book "../books/pool")
(assert-event (fn2-upload-window-profilep '((:pool-classes . ((2 . 32768))))))
; Missing physical capacity: a body-fitting class does not fit the header.
(assert-event (not (fn2-upload-window-profilep '((:pool-classes . ((2 . 16384)))))))
(assert-event (not (fn2-upload-window-profilep '((:pool-classes . ((2 . bad)))))))
; Zero count satisfies geometry, never the actual reservation below.
(defun fn2-uwp-pool (count)
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-pool
  (mv-let (ok fn2-pool)
   (let* ((classes (list (cons count 32768)))
         (fn2-pool (fn2-pool-init classes 1 100 fn2-pool)))
   (mv (and (fn2-upload-window-profilep (list (cons :pool-classes classes)))
            (not (< *fn2-upload-chunk-class* (len classes)))
            (equal (fn2-pool-class-for *fn2-upload-header-workspace-bytes* fn2-pool) 0)
            (equal (fn2-pool-class-for *fn2-upload-body-window-bytes* fn2-pool) 0)
            (equal (fn2-pool-reservable-count 0 fn2-pool) count)
            (fn2-pool-wfp fn2-pool)) fn2-pool)) ok)))
(assert-event (fn2-uwp-pool 2))
(assert-event (fn2-uwp-pool 0))
