; Structural continuation/custody teeth. These do not establish parsed
; enrollment provenance, a genuine issued grant, or whole public replay.
(in-package "ACL2")
(include-book "../../books/replay-revoked-enrollment")
(defun fn-rse-test-revoked-run (fuel s)
 (declare (xargs :guard t :verify-guards nil :measure (nfix fuel)))
 (if (zp fuel) (mv :yield s)
  (mv-let (word next) (fn-rse-revoked-step s)
   (if (eq word :working) (fn-rse-test-revoked-run (1- fuel) next)
    (mv word next)))))
(defun fn-rse-test-revoked-next (s)
 (declare (xargs :guard t :verify-guards nil))
 (mv-let (word next) (fn-rse-revoked-step s) (declare (ignore word)) next))
(defun fn-rse-test-revoked-run-next (fuel s)
 (declare (xargs :guard t :verify-guards nil))
 (mv-let (word next) (fn-rse-test-revoked-run fuel s) (declare (ignore word)) next))
(defconst *fn-rse-revoked-test-source* '(:issued 17 4 9))
(defconst *fn-rse-revoked-test-spans*
 '((:bytes 7 3 (11 12 13 99)) (:bytes 20 2 (21 22 88))
   (:bytes 30 3 (31 32 33 77))))
(defconst *fn-rse-revoked-test-keys* '((:ed25519 21 22) (:ml-dsa-65 31 32 33)))
(defconst *fn-rse-revoked-test-snapshot*
 (list 0 0 0 7 *fn-hsig-revoked-profile* '(11 12 13)))
(defconst *fn-rse-revoked-test-context*
 (fn-stxk-context :ok 0 (list *fn-rse-revoked-test-snapshot*) nil 7 nil))
(defconst *fn-rse-revoked-test-child* '(0 0 0 nil :revoked (11 12 13) 7 nil))
(defconst *fn-rse-revoked-test-ledger*
 (list (fn-rse-evidence 'borrowed-enrollment-snapshot :enrolled
        *fn-rse-revoked-test-spans* *fn-rse-revoked-test-source*)))
(defconst *fn-rse-revoked-test-begin*
 (fn-rse-revoked-begin *fn-rse-revoked-test-context* *fn-rse-revoked-test-child*
  *fn-rse-revoked-test-keys* *fn-rse-revoked-test-ledger* *fn-rse-revoked-test-source*))
; Complete antecedent and conclusion of the actual custody theorem.
(assert-event
 (let* ((s *fn-rse-revoked-test-begin*)
        (next (fn-rse-test-revoked-next s)))
  (and (fn-rsc-widthp 9 s) (fn-rsc-widthp 9 next)
       (equal (fn-rsc-at 1 next) (fn-rsc-at 1 s))
       (equal (fn-rsc-at 2 next) (fn-rsc-at 2 s))
       (equal (fn-rsc-at 3 next) (fn-rsc-at 3 s))
       (equal (fn-rsc-at 4 next) (fn-rsc-at 4 s))
       (equal (fn-rsc-at 5 next) (fn-rsc-at 5 s))
       (eq (fn-rsc-at 0 next) :profile))))
(assert-event
 (mv-let (word next) (fn-rse-test-revoked-run 0 *fn-rse-revoked-test-begin*)
  (and (eq word :yield) (equal next *fn-rse-revoked-test-begin*))))
(assert-event
 (let ((next (fn-rse-test-revoked-run-next 1 *fn-rse-revoked-test-begin*)))
  (and (eq (fn-rsc-at 0 next) :profile)
       (equal (fn-rsc-at 5 next) *fn-rse-revoked-test-source*)
       (eq (fn-rse-revoked-readout next) :pending))))
(assert-event
 (let ((next (fn-rse-test-revoked-run-next 100 *fn-rse-revoked-test-begin*)))
  (and (eq (fn-rsc-at 0 next) :done)
       (equal (fn-rse-revoked-readout next)
        (list :produced
         (fn-stxk-context :ok 1 (list *fn-rse-revoked-test-snapshot*)
                         (list *fn-rse-revoked-test-child*) 7 nil)
         *fn-rse-revoked-test-child* *fn-rse-revoked-test-source*))
       (mv-let (word retained) (fn-rse-revoked-step next)
        (and (eq word :done) (equal retained next))))))
; Literal selected generation is absent: no enrolled lookup or parser runs.
(assert-event
 (let ((s (fn-rse-revoked-begin (fn-stxk-context :ok 0 nil nil 7 nil)
           *fn-rse-revoked-test-child* *fn-rse-revoked-test-keys*
           *fn-rse-revoked-test-ledger* *fn-rse-revoked-test-source*)))
  (equal (fn-rsc-at 8 (fn-rse-test-revoked-next s))
         (fn-stxk-fault (fn-stxk-context :ok 0 nil nil 7 nil) :composite-binding))))
; Wrong selected profile / principal / enrolled keys each preserves source.
(assert-event
 (let* ((ctx (fn-stxk-context :ok 0 (list '(0 0 0 7 (0) (11 12 13))) nil 7 nil))
        (s (fn-rse-revoked-begin ctx *fn-rse-revoked-test-child*
             *fn-rse-revoked-test-keys* *fn-rse-revoked-test-ledger*
             *fn-rse-revoked-test-source*))
        (next (fn-rse-test-revoked-run-next 100 s)))
  (and (equal (fn-rsc-at 8 next) (fn-stxk-fault ctx :composite-binding))
       (equal (fn-rsc-at 5 next) *fn-rse-revoked-test-source*))))
(assert-event
 (let* ((ctx (fn-stxk-context :ok 0
              (list (list 0 0 0 7 *fn-hsig-revoked-profile* '(11 99 13))) nil 7 nil))
        (s (fn-rse-revoked-begin ctx *fn-rse-revoked-test-child*
             *fn-rse-revoked-test-keys* *fn-rse-revoked-test-ledger*
             *fn-rse-revoked-test-source*)))
  (equal (fn-rsc-at 8 (fn-rse-test-revoked-run-next 100 s))
         (fn-stxk-fault ctx :composite-binding))))
(assert-event
 (let ((s (fn-rse-revoked-begin *fn-rse-revoked-test-context*
           *fn-rse-revoked-test-child* '((:ed25519 99 22) (:ml-dsa-65 31 32 33))
           *fn-rse-revoked-test-ledger* *fn-rse-revoked-test-source*)))
  (equal (fn-rsc-at 8 (fn-rse-test-revoked-run-next 100 s))
         (fn-stxk-fault *fn-rse-revoked-test-context* :composite-binding))))
(assert-event (mv-let (word next) (fn-rse-revoked-step '(:bad))
 (and (eq word :refused) (equal next '(:bad)))))
(assert-event (eq (fn-rse-revoked-readout '(:bad)) :refused))
; Hypothesis-removal: without fixed9, the complete custody conclusion fails.
(assert-event
 (let* ((s '(:bad)) (next (fn-rse-test-revoked-next s)))
  (and (not (fn-rsc-widthp 9 s)) (not (fn-rsc-widthp 9 next))
       (equal (fn-rsc-at 1 next) (fn-rsc-at 1 s))
       (equal (fn-rsc-at 2 next) (fn-rsc-at 2 s))
       (equal (fn-rsc-at 3 next) (fn-rsc-at 3 s))
       (equal (fn-rsc-at 4 next) (fn-rsc-at 4 s))
       (equal (fn-rsc-at 5 next) (fn-rsc-at 5 s)))))
