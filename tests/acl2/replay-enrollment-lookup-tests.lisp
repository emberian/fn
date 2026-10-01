(in-package "ACL2")
(include-book "../../books/replay-enrollment-lookup")

; Test scheduling only, never a served loop.
(defun fn-rse-test-lookup-run (fuel s)
 (declare (xargs :guard t :verify-guards nil :measure (nfix fuel)))
 (if (zp (nfix fuel)) (mv :yield s)
  (mv-let (word next) (fn-rse-lookup-step s)
   (if (eq word :working) (fn-rse-test-lookup-run (1- (nfix fuel)) next)
    (mv word next)))))
(defconst *fn-rse-lookup-test-spans*
 '((:bytes 7 3 (11 12 13 99)) (:bytes 20 2 (21 22 88))
   (:bytes 30 3 (31 32 33 77))))
(defconst *fn-rse-lookup-test-entry*
 (fn-rse-evidence :literal-snapshot :enrolled *fn-rse-lookup-test-spans* :row-source))
(defconst *fn-rse-lookup-test-entries*
 (list (fn-rse-evidence :invalid-profile :none nil :prior-source)
       *fn-rse-lookup-test-entry*))
(defconst *fn-rse-lookup-test-keys* '((:ed25519 21 22) (:ml-dsa-65 31 32 33)))
(defconst *fn-rse-lookup-test-begin*
 (fn-rse-lookup-begin '(11 12 13) *fn-rse-lookup-test-keys*
                      *fn-rse-lookup-test-entries* :issued-source))
(assert-event
 (and (fn-rse-keys-shapep *fn-rse-lookup-test-keys*)
      (fn-rse-evidence-ledgerp *fn-rse-lookup-test-entries*)
      (fn-rse-lookup-invariantp *fn-rse-lookup-test-begin*)
      (equal (fn-rse-lookup-outcome *fn-rse-lookup-test-begin*)
       (fn-rse-enrolled-model '(11 12 13) *fn-rse-lookup-test-keys*
                              *fn-rse-lookup-test-entries*))))
(assert-event
 (mv-let (word next) (fn-rse-lookup-step *fn-rse-lookup-test-begin*)
  (and (fn-rse-lookup-invariantp *fn-rse-lookup-test-begin*)
       (eq word :working) (fn-rse-lookup-invariantp next)
       (equal (fn-rse-lookup-outcome next)
              (fn-rse-lookup-outcome *fn-rse-lookup-test-begin*))
       (equal (fn-rsc-at 3 next) (cdr *fn-rse-lookup-test-entries*))
       (equal (fn-rsc-at 5 next) :issued-source))))
(assert-event
 (mv-let (word next) (fn-rse-test-lookup-run 0 *fn-rse-lookup-test-begin*)
  (and (eq word :yield) (equal next *fn-rse-lookup-test-begin*))))
(assert-event
 (mv-let (word next) (fn-rse-test-lookup-run 12 *fn-rse-lookup-test-begin*)
  (and (eq word :yield) (eq (fn-rsc-at 0 next) :compare)
       (fn-rse-lookup-invariantp next) (fn-rse-lookup-outcome next)
       (equal (fn-rsc-at 5 next) :issued-source))))
(assert-event
 (mv-let (word next) (fn-rse-test-lookup-run 13 *fn-rse-lookup-test-begin*)
  (and (eq word :done) (eq (fn-rsc-at 0 next) :found)
       (fn-rse-lookup-invariantp next)
       (equal (fn-rsc-at 6 next) *fn-rse-lookup-test-entry*)
       (equal (fn-rsc-at 5 next) :issued-source))))
(assert-event
 (mv-let (word next) (fn-rse-test-lookup-run 20
  (fn-rse-lookup-begin '(11 12 0) *fn-rse-lookup-test-keys*
                       *fn-rse-lookup-test-entries* :issued-source))
  (and (eq word :done) (eq (fn-rsc-at 0 next) :done)
       (fn-rse-lookup-invariantp next) (not (fn-rse-lookup-outcome next))
       (null (fn-rsc-at 3 next)) (null (fn-rsc-at 6 next)))))
(assert-event
 (let ((s (fn-rse-lookup-begin '(11 12 13) *fn-rse-lookup-test-keys*
           '((:snapshot :none (:unexpected) :source)) :issued-source)))
  (mv-let (word next) (fn-rse-lookup-step s)
   (and (eq word :refused) (equal next s)))))
; Mutation: all shape/ledger/equality invariants hold, but the CURRENT
; comparison outcome does not correspond to this actual evidence row.
(defconst *fn-rse-lookup-test-false-comparison*
 (fn-rse-lookup-state :compare '(0 12 13) *fn-rse-lookup-test-keys*
  (list *fn-rse-lookup-test-entry*)
  (fn-rse-equality-state :done *fn-rse-lookup-test-keys*
    *fn-rse-lookup-test-spans* nil nil 0 :issued-source t)
  :issued-source nil))
(assert-event
 (let ((s *fn-rse-lookup-test-false-comparison*))
  (mv-let (word next) (fn-rse-lookup-step s)
   (and (fn-rsc-widthp 7 s) (fn-rse-keys-shapep (fn-rsc-at 2 s))
        (fn-rse-evidence-ledgerp (fn-rsc-at 3 s))
        (eq (fn-rsc-at 0 s) :compare) (consp (fn-rsc-at 3 s))
        (fn-rse-equality-invariantp (fn-rsc-at 4 s))
        (not (equal (fn-rse-equality-outcome (fn-rsc-at 4 s))
          (equal (list (fn-rsc-at 1 s) (fn-rsc-at 2 s))
                 (fn-rse-evidence-value (car (fn-rsc-at 3 s))))))
        (not (fn-rse-lookup-invariantp s)) (eq word :done)
        (not (equal (fn-rse-lookup-outcome next) (fn-rse-lookup-outcome s)))
        (not (fn-rse-lookup-invariantp next))))))
