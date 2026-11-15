; Formula-bound evidence for the exact complete core-release component.
; No callback/reference world and no replacement application obligation.
(in-package "ACL2")
(include-book "../books/square-evidence")
(include-book "cns-release-refinement-unit")

; A source drift in either H or C must not silently redirect evidence.
(make-event
 (let* ((world (w state))
        (row (fn2-decl-row '(:square fn2-cns-core-release-independent) world))
        (formula (fn2-decl-statement-body (fn2-decl-get :statement row) world))
        (theorem (getpropc 'fn2-cns-core-release-independent 'theorem nil world)))
  (if (and theorem (equal formula theorem))
      (value '(value-triple :same-complete-release-formula))
    (er soft 'cns-release-evidence "Release row/theorem H or C differs."))))

(defun fn2-cns-core-release-evidence-payload ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-core
    (mv-let (payload fn2-core)
      (fn2-cns-core-release-law-run :snapshot fn2-core) payload)))

(make-event
 (let* ((payload (fn2-cns-core-release-evidence-payload))
        (slot (nth 0 payload)) (gen (nth 1 payload))
        (sibling (nth 2 payload)) (before (nth 4 payload))
        (bindings (list (list 'slot (list 'quote slot))
                        (list 'gen (list 'quote gen))
                        (list 'id ''10) (list 'ogen ''1)
                        (list 'core (list 'quote before))))
        (removed (list (list 'slot (list 'quote slot))
                       (list 'gen (list 'quote (+ 1 (nfix gen))))
                       (list 'id ''10) (list 'ogen ''1)
                       (list 'core (list 'quote before)))))
  (if (not (and (equal (len payload) 5) (natp slot) (natp gen)
                (natp sibling) (not (equal slot sibling)) (consp before)))
      (er soft 'cns-release-evidence "Actual initialized release setup failed.")
    (value
     (fn2-square-evidence-events-with-correspondence
      'fn2-cns-core-release-independent bindings
      (list :kind :hypothesis-removal
            :remove '(fn2-cns-drain-releasablep slot gen id ogen (fn2-core-pool core))
            :bindings removed)
      nil nil (w state))))))
(fn2-assert-square-evidence fn2-cns-core-release-independent)
; Evidence establishes concrete instances only. Universal discharge is not
; inferred from source declarations, runtime controls, or these ground facts.
(assert-event
 (equal (fn2-decl-get :proof
          (fn2-decl-row '(:square fn2-cns-core-release-independent) (w state)))
        '(:owed)))
