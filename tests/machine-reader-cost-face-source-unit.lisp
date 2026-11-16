; PREPARED UNEXECUTED actual-world consumer gate. Source checks do not run it.
; No handwritten generation/kind/slot runtime face or macro expansion twin.
(in-package "ACL2")
(include-book "../books/assembly-callbacks-c")
(local (defun fn2-cost-reader-call-count (name tree)
 (declare (xargs :guard t))
 (if (or (atom tree) (eq (car tree) 'quote)) 0
  (+ (if (eq (car tree) name) 1 0)
     (fn2-cost-reader-call-count name (car tree))
     (fn2-cost-reader-call-count name (cdr tree))))))
(make-event
 (let* ((world (w state))
        (generation (fn2-operation-row 'fn2-machine-generation world))
        (generation-code (fn2-operation-row 'fn2-machine-generation-read-code world))
        (kind (fn2-operation-row 'fn2-machine-kind world))
        (gd (car (last (car (fn2-decl-get :definition generation)))))
        (gc (car (last (car (fn2-decl-get :definition generation-code)))))
        (kd (car (last (car (fn2-decl-get :definition kind))))))
  ; Definitions are taken from the SAME operation rows registered by the real
  ; machine-field/index emitters, not from a source-only expanded replacement.
  (if (and generation generation-code kind
           (equal (fn2-decl-get :calling-convention generation) '(id fn2-core))
           (not (fn2-machine-directory-fieldp 'generation))
           (= (fn2-cost-reader-call-count 'fn2-machine-generation-read-code gd) 1)
           (= (fn2-cost-reader-call-count 'fn2-machine-slot gd) 1)
           (= (fn2-cost-reader-call-count 'fn2-machine-kind gd) 1)
           (= (fn2-cost-reader-call-count 'fn2-machine-idp gc) 1)
           (= (fn2-cost-reader-call-count 'fn2-machine-slot gc) 1)
           (= (fn2-cost-reader-call-count 'fn2-machine-kind gc) 1)
           (= (fn2-cost-reader-call-count 'fn2-machine-slot kd) 0)
           (= (fn2-cost-reader-call-count 'fn2-machine-kind kd) 0))
      (value '(value-triple :actual-machine-reader-shapes))
    (er soft 'machine-reader-cost "Actual registered reader shapes changed."))))
