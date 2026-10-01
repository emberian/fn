; Actual parser/producer executions, scoped separately from public semantic
; correspondence, native custody, installed authority and allocation funding.
(in-package "ACL2")
(include-book "../../books/replay-enrollment-bootstrap")
(defun fn-rse-test-repeat (n byte)
 (declare (xargs :guard t :verify-guards nil :measure (nfix n)))
 (if (zp n) nil (cons byte (fn-rse-test-repeat (1- n) byte))))
(defun fn-rse-test-produced-run (fuel s)
 (declare (xargs :guard t :verify-guards nil :measure (nfix fuel)))
 (if (zp fuel) (mv :yield s)
  (mv-let (word next) (fn-rse-produced-step s)
   (if (eq word :working) (fn-rse-test-produced-run (1- fuel) next)
    (mv word next)))))
(defun fn-rse-test-produced-next (fuel s)
 (declare (xargs :guard t :verify-guards nil))
 (mv-let (word next) (fn-rse-test-produced-run fuel s) (declare (ignore word)) next))
(defun fn-rse-test-bootstrap-run (fuel s)
 (declare (xargs :guard t :verify-guards nil :measure (nfix fuel)))
 (if (zp fuel) (mv :yield s)
  (mv-let (word next) (fn-rse-bootstrap-step s)
   (if (eq word :working) (fn-rse-test-bootstrap-run (1- fuel) next)
    (mv word next)))))
(defconst *fn-rse-produced-test-source* '(:issued 19 4 10))
(defconst *fn-rse-produced-test-principal* (fn-rse-test-repeat 32 11))
(defconst *fn-rse-produced-test-ed* (fn-rse-test-repeat 32 21))
(defconst *fn-rse-produced-test-ml* (fn-rse-test-repeat 1952 31))
(defconst *fn-rse-produced-test-payload*
 (append '(88 32) *fn-rse-produced-test-principal* '(1 88 32)
         *fn-rse-produced-test-ed* '(2 89 7 160) *fn-rse-produced-test-ml*))
(defconst *fn-rse-produced-test-snapshot*
 (list 0 0 0 7 *fn-hsig-profile-tag* *fn-rse-produced-test-payload*))
(defconst *fn-rse-produced-test-old* (fn-stxk-context :ok 0 nil nil nil nil))
(defconst *fn-rse-produced-test-checked*
 (fn-stxk-context :ok 1 (list *fn-rse-produced-test-snapshot*) nil 7 nil))
(defconst *fn-rse-produced-test-packet*
 (list *fn-rse-produced-test-checked* nil :unavailable :snapshot
       *fn-rse-produced-test-snapshot* nil))
(defconst *fn-rse-produced-test-begin*
 (fn-rse-produced-begin *fn-rse-produced-test-old* *fn-rse-produced-test-packet*
                        nil *fn-rse-produced-test-source*))
; Complete antecedent and conclusion of the actual producer custody theorem.
(assert-event
 (mv-let (word next) (fn-rse-produced-step *fn-rse-produced-test-begin*)
  (declare (ignore word))
  (let ((s *fn-rse-produced-test-begin*))
   (and (fn-rsc-widthp 9 s) (fn-rsc-widthp 9 next)
        (equal (fn-rsc-at 1 next) (fn-rsc-at 1 s))
        (equal (fn-rsc-at 2 next) (fn-rsc-at 2 s))
        (equal (fn-rsc-at 3 next) (fn-rsc-at 3 s))
        (equal (fn-rsc-at 4 next) (fn-rsc-at 4 s))
        (equal (fn-rsc-at 5 next) (fn-rsc-at 5 s))))))
(assert-event
 (mv-let (word next) (fn-rse-test-produced-run 0 *fn-rse-produced-test-begin*)
  (and (eq word :yield) (equal next *fn-rse-produced-test-begin*)
       (eq (fn-rse-produced-readout next) :pending))))
; Actual legacy-size principal/algorithm/key fields, original borrowed tails.
(assert-event
 (let* ((next (fn-rse-test-produced-next 5000 *fn-rse-produced-test-begin*))
        (readout (fn-rse-produced-readout next))
        (entry (car (fn-rsc-at 3 readout))) (spans (fn-rsc-at 2 entry)))
  (and (eq (fn-rsc-at 0 next) :enrolled)
       (equal (fn-rsc-at 1 readout) *fn-rse-produced-test-old*)
       (equal (fn-rsc-at 2 readout) *fn-rse-produced-test-packet*)
       (equal (fn-rsc-at 4 readout) *fn-rse-produced-test-source*)
       (equal (fn-rsc-at 0 entry) *fn-rse-produced-test-snapshot*)
       (equal (fn-rse-span-tail (car spans)) (cddr *fn-rse-produced-test-payload*))
       (equal (fn-rse-evidence-value entry)
        (list *fn-rse-produced-test-principal*
         (list (cons :ed25519 *fn-rse-produced-test-ed*)
               (cons :ml-dsa-65 *fn-rse-produced-test-ml*)))))))
; Duplicate/no-change evidence is borrowed, not reparsed or reconstructed.
(assert-event
 (let* ((ledger 'borrowed-old-ledger)
        (packet (list *fn-rse-produced-test-old* nil :unavailable :none nil nil))
        (s (fn-rse-produced-begin *fn-rse-produced-test-old* packet ledger
                                 *fn-rse-produced-test-source*)))
  (and (eq (fn-rsc-at 0 s) :unchanged)
       (equal (fn-rse-produced-readout s)
        (list :produced *fn-rse-produced-test-old* packet ledger
              *fn-rse-produced-test-source*))
       (mv-let (word next) (fn-rse-produced-step s)
        (and (eq word :done) (equal next s))))))
; Refused nested decode establishes :none, never a successful enrollment.
(assert-event
 (let* ((snapshot (list 0 0 0 7 *fn-hsig-profile-tag* '(255)))
        (packet (list *fn-rse-produced-test-checked* nil :unavailable :snapshot snapshot nil))
        (s (fn-rse-produced-begin *fn-rse-produced-test-old* packet nil
                                 *fn-rse-produced-test-source*))
        (next (fn-rse-test-produced-next 20 s)))
  (and (eq (fn-rsc-at 0 next) :none)
       (equal (fn-rsc-at 2 (car (fn-rsc-at 3 (fn-rse-produced-readout next)))) nil)
       (equal (fn-rsc-at 4 next) *fn-rse-produced-test-source*))))
; Cold bootstrap consumes exact original snapshot order and source.
(assert-event
 (let* ((bad (list 1 1 0 8 *fn-hsig-profile-tag* '(255)))
        (ctx (fn-stxk-context :ok 2 (list *fn-rse-produced-test-snapshot* bad) nil 8 nil))
        (s (fn-rse-bootstrap-begin ctx *fn-rse-produced-test-source*)))
  (mv-let (word next) (fn-rse-test-bootstrap-run 10000 s)
   (let* ((readout (fn-rse-bootstrap-readout next))
          (ledger (fn-rsc-at 2 readout)))
    (and (eq word :done) (equal (fn-rsc-at 1 readout) ctx)
         (equal (fn-rsc-at 3 readout) *fn-rse-produced-test-source*)
         (equal (fn-rsc-at 0 (car ledger)) *fn-rse-produced-test-snapshot*)
         (eq (fn-rsc-at 1 (car ledger)) :enrolled)
         (equal (fn-rsc-at 0 (cadr ledger)) bad)
         (eq (fn-rsc-at 1 (cadr ledger)) :none))))))
(assert-event
 (mv-let (word next) (fn-rse-produced-step '(:bad))
  (and (eq word :refused) (equal next '(:bad))
       (eq (fn-rse-produced-readout next) :refused))))
(assert-event
 (mv-let (word next) (fn-rse-bootstrap-step '(:bad))
  (and (eq word :refused) (equal next '(:bad))
       (eq (fn-rse-bootstrap-readout next) :refused))))
