; SOURCE teeth for the projected MBE scanner; all assertions/theorems UNRUN.
; Compile the two compared terms from the SAME generator's returned event,
; rather than writing an independent scanner. No second runtime is admitted.
(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "../../tests/layout-payload-span-unit")

(defun fn2-span-find-event (head name events)
 (declare (xargs :verify-guards nil))
 (if (atom events) nil
  (if (and (eq (caar events) head) (eq (cadar events) name)) (car events)
   (fn2-span-find-event head name (cdr events)))))

(defun fn2-span-teeth-build (term fuel end corrupt-index corrupt-value)
 (declare (xargs :verify-guards nil))
 `(mv-let (setup f p)
    (fn2-span-case 16 4096 (create-fn2-fields) (create-fn2-pool))
   (let* ((slot (fn2-fields-ref-slot 1 f)) (gen (fn2-fields-ref-gen 1 f))
          (f (fn2-fields-init 8 f)) (f (fn2-span-fixture-start 0 f)))
    (mv-let (first first-next f)
      (fn2-span-fixture-decode-step 0 slot gen 0 24 1 0 1 5 f p)
     (let* ((p ,(if corrupt-index
                    `(update-fn2-pool-datai (+ (fn2-pool-base slot p) ,corrupt-index) ,corrupt-value p)
                  'p))
            (fuel ,fuel) (base 0) (phase (fn2-fields-decode-phase 0 f))
            (pos (fn2-fields-decode-pos 0 f)) (v (fn2-fields-decode-acc 0 f))
            (hi (fn2-fields-decode-high 0 f)) (size (fn2-fields-decode-size 0 f))
            (ref (fn2-fields-decode-ref 0 f)) (payload (fn2-fields-decode-payload 0 f))
            (next (fn2-fields-decode-next 0 f)) (end ,end) (okind 1) (oslot 0) (ogen 1))
      (and setup (eq first :more) (= first-next 5) ,term))))))

(make-event
 (let* ((events (cddr (fn2-codec-events 'fn2-span-fixture
                   '((code :u8) (body (:octets32 6144)) (tail (:zero 3))) 60)))
        (scan (fn2-span-find-event 'defun 'fn2-span-fixture-scan events))
        (hyp (fn2-span-find-event 'defun 'fn2-span-fixture-scan-exec-hyps events))
        (body (car (last scan)))
        (exec (cadr (member-eq :exec body)))
        (whole (car (last hyp)))
        (without-pool-type (list 'and (cadr whole) (cadddr whole)))
        (args '(fuel base phase pos v hi size ref payload next slot gen end okind oslot ogen f p))
        (left (list 'mv-list 3 (cons 'fn2-span-fixture-scan args)))
        (right (list 'mv-list 3 (subst 'p 'fn2-pool (subst 'f 'fn2-fields exec))))
        (whole (subst 'p 'fn2-pool (subst 'f 'fn2-fields whole)))
        (without-pool-type (subst 'p 'fn2-pool (subst 'f 'fn2-fields without-pool-type)))
        (same (list 'equal left right))
        (positive (list 'and whole same))
        (removed (list 'and '(not (fn2-poolp p)) '(fn2-pool-wfp p)
                       without-pool-type (list 'not same))))
  (if (not (and (eq (car body) 'mbe) (eq (cadr body) :logic)
                (eq (car whole) 'and) (equal (caddr whole) '(fn2-poolp p))))
      (er soft 'fn2-span-refinement-teeth "Projected scanner/hypothesis shape changed.")
   (value
    `(progn
      ; Each case asserts the complete actual guard domain and equality of ALL
      ; three returned values, including the entire fields stobj, not a view.
      (defthm fn2-span-exec-partial-whole-h
       ,(fn2-span-teeth-build positive 8 24 nil nil) :rule-classes nil)
      (defthm fn2-span-exec-field-end-whole-h
       ,(fn2-span-teeth-build positive 16 24 nil nil) :rule-classes nil)
      (defthm fn2-span-exec-input-end-whole-h
       ,(fn2-span-teeth-build positive 19 24 nil nil) :rule-classes nil)
      (defthm fn2-span-exec-zero-fuel-whole-h
       ,(fn2-span-teeth-build positive 0 24 nil nil) :rule-classes nil)
      (defthm fn2-span-exec-truncated-whole-h
       ,(fn2-span-teeth-build positive 8 12 nil nil) :rule-classes nil)
      (defthm fn2-span-exec-typed-fault-whole-h
       ,(fn2-span-teeth-build positive 19 24 23 9) :rule-classes nil)
      ; Removing exactly POOLP permits a nonoctet in an otherwise unchanged,
      ; owned readable payload. Original logic rejects; unchecked span skips it.
      (defthm fn2-span-exec-pool-type-removal
       ,(fn2-span-teeth-build removed 8 24 6 256) :rule-classes nil))))))
