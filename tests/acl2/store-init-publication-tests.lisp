; Teeth for books/store-init-publication (PKT-647): init's cut names over the
; import's program and the admission.  The plan's keystone is PRF-268's
; (tests/acl2/store-init-log-publication-tests.lisp).
(in-package "ACL2")
(include-book "must-fail-checked")
(include-book "../../books/store-init-publication")

; The renaming: every cut of the import's program becomes init's, every other
; step is kept, over a one-subdirectory, one-file plan.
(defconst *init-t-import*
  (fn-bs-imp-program "store.init-1" "store" '(("staging" . :staging))
                     (list (list* :stage "config.json" '(1 2 3)))))
(defun init-t-cuts (steps)
  (if (consp steps)
      (if (equal (car (car steps)) :cut)
          (cons (nth 1 (car steps)) (init-t-cuts (cdr steps)))
        (init-t-cuts (cdr steps)))
    nil))
(defun init-t-non-cuts (steps)
  (if (consp steps)
      (if (equal (car (car steps)) :cut)
          (init-t-non-cuts (cdr steps))
        (cons (car steps) (init-t-non-cuts (cdr steps))))
    nil))
(assert-event
 (equal (init-t-cuts (fn-bs-init-pub-rename-cuts *init-t-import*))
        '("init-stage-created" "init-subdir-created"
          "init-file-created" "init-file-written" "init-file-durable"
          "init-subdir-durable" "init-staged-durable" "init-validated" "init-published"
          "init-durable")))
(assert-event (equal (init-t-cuts *init-t-import*)
                     (strip-cars *fn-bs-init-pub-cut-names*)))
(assert-event (equal (init-t-non-cuts (fn-bs-init-pub-rename-cuts *init-t-import*))
                     (init-t-non-cuts *init-t-import*)))

; The admission: every arm reachable, and it proceeds only on nothing.
(assert-event (equal (fn-bs-init-pub-admission nil nil) :proceed))
(assert-event (equal (fn-bs-init-pub-admission (fn-bs-imp-classify t nil) nil)
                     '(:refused :interrupted-init)))
(assert-event (equal (fn-bs-init-pub-admission (fn-bs-imp-classify t t) t)
                     '(:refused :publication-uncertain)))
(assert-event (equal (fn-bs-init-pub-admission nil t) '(:refused :store-path-exists)))

; Teeth for fn-bs-init-pub-admission-decides-by-what-is-present (PRF-942),
; over the antecedent as the host composes it (the classification of a
; leftover stage, nil without one).  Reachable positive witness: nothing
; present, :proceed.  Hypothesis removal: each name present alone, and both,
; is the refusal by that name and never :proceed.
(defun init-t-admission (stage-present root-present)
  (fn-bs-init-pub-admission
   (and stage-present (fn-bs-imp-classify stage-present root-present))
   root-present))
(assert-event (equal (init-t-admission nil nil) :proceed))
(assert-event (equal (init-t-admission t nil) '(:refused :interrupted-init)))
(assert-event (equal (init-t-admission nil t) '(:refused :store-path-exists)))
(assert-event (equal (init-t-admission t t) '(:refused :publication-uncertain)))
(assert-event (and (not (equal (init-t-admission t nil) :proceed))
                   (not (equal (init-t-admission nil t) :proceed))
                   (not (equal (init-t-admission t t) :proceed))))
