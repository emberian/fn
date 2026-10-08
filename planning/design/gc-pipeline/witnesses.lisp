; Ground tests only; do NOT load statements.lisp before running these.
; REPL attempt 2026-10-07: blocked before ACL2 startup by sandbox denial of
; /Users/ember/.cache/fn-acl2-slots/slot-000. None of these has a REPL PASS.
(in-package "ACL2")
(include-book "contracts")
(include-book "../../../tests/acl2/must-fail-checked")

(defconst *gc-h* '((65) (66) (67)))
(defconst *gc-head* '(0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
                     0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0))
(defconst *gc-events* '((:start 1) (:complete) (:start 1) (:next 1)))
(defconst *gc-m* (fn-ocvm-run (fn-ocvm-init) *gc-events*))
(defconst *gc-s1* (mv-nth 1 (fn-ocp-commit-event (fn-ocp-init) :started)))
(defconst *gc-s* (mv-nth 1 (fn-ocp-commit-event *gc-s1* :next-started)))
; Valid logical split snapshots; not witnesses of the byte-store relation
; or of two physical appends overlapping fdatasync (not implemented yet).
(defconst *gc-before*
  (fn-lgk-make '((65)) *gc-head* 512 4 '((67)) '((66)) 1 :appended))
(defconst *gc-after*
  (fn-lgk-make '((65) (66)) *gc-head* 1024 4 '((67)) nil 1 :fenced))

; REVEALS positive: the ENTIRE antecedent and conclusion, before and after
; the fence. Nonempty durable prefix, nonempty current AND next batch.
(assert-event
 (and (fn-ocvm-legal-run-p (fn-ocvm-init) *gc-events*)
      (fn-ocp-gc-linkedp *gc-h* *gc-m* *gc-before* *gc-s* :next-none :append :ok)
      (fn-ocp-gc-reveals-okp *gc-h* *gc-before*
        (fn-ocp-gc-cuts *gc-m* *gc-s* :next-none :append :ok))
      (equal (fn-ocp-gc-cuts *gc-m* *gc-s* :next-none :append :ok) '(1 0 0 0))))
(assert-event
 (and (fn-ocp-gc-linkedp *gc-h* *gc-m* *gc-after* *gc-s* :fenced :fence :ok)
      (fn-ocp-gc-reveals-okp *gc-h* *gc-after*
        (fn-ocp-gc-cuts *gc-m* *gc-s* :fenced :fence :ok))
      (equal (fn-ocp-gc-cuts *gc-m* *gc-s* :fenced :fence :ok) '(1 2 2 2))
      (equal (fn-ocs-member-releases
               (mv-nth 0 (fn-ocp-commit-event *gc-s* :fenced)) '((:accepted t)))
             '(:rendered))))

; REVEALS tooth 1: remove receipt-to-durability coupling. A forged :fenced
; at APPEND releases the rendered reply while record 66 is still beyond D.
; The explicit negation evaluates the counterexample, not a failed search.
(assert-event
 (and (not (fn-ocp-gc-linkedp *gc-h* *gc-m* *gc-before* *gc-s* :fenced :append :ok))
      (equal (fn-ocs-member-releases
               (mv-nth 0 (fn-ocp-commit-event *gc-s* :fenced)) '((:accepted t)))
             '(:rendered))
      (not (fn-ocp-gc-reveals-okp *gc-h* *gc-before*
             (fn-ocp-gc-cuts *gc-m* *gc-s* :fenced :append :ok)))))
(must-fail-checked
 (assert-event
  (fn-ocp-gc-reveals-okp *gc-h* *gc-before*
    (fn-ocp-gc-cuts *gc-m* *gc-s* :fenced :append :ok))))

; REVEALS tooth 2: remove the captured-view invariant. A read at the working
; view exposes 66 and 67. The native equivalent is bypassing at-reader-view.
(defconst *gc-unpinned* (fn-ocvm-make 3 1 1 1 nil))
(assert-event
 (and (not (fn-ocvm-inv *gc-unpinned*))
      (not (fn-ocp-gc-linkedp *gc-h* *gc-unpinned* *gc-before* *gc-s* :next-none :append :ok))
      (equal (fn-ocv-reader-view (fn-ocvm-views *gc-unpinned*) 3) 3)
      (not (fn-ocp-gc-reveals-okp *gc-h* *gc-before*
             (fn-ocp-gc-cuts *gc-unpinned* *gc-s* :next-none :append :ok)))))
(must-fail-checked
 (assert-event
  (fn-ocp-gc-reveals-okp *gc-h* *gc-before*
    (fn-ocp-gc-cuts *gc-unpinned* *gc-s* :next-none :append :ok))))

; FAILURE positive: both nonempty batches, even after 100 attempted ACKs.
(defconst *gc-a* '((:accepted t)))
(defconst *gc-b* '((:accepted nil)))
(assert-event
 (and (fn-ocp-gc-failure-hyp *gc-s* *gc-before* *gc-a* *gc-b*)
      (fn-ocp-gc-failure-okp *gc-s* *gc-before* *gc-a* *gc-b* 100)
      (equal (fn-ocs-member-releases
               (mv-nth 0 (fn-ocp-commit-event *gc-s* :failed))
               (append *gc-a* *gc-b*))
             '(:uncertain-reply :close))))
; Hypothesis-removal tooth: a previous ACK-at-append is not repaired by a
; later failed barrier. ACKED=3 > D=1; the other failure hypotheses hold.
(defconst *gc-early-acked*
  (fn-lgk-make '((65)) *gc-head* 512 4 '((67)) '((66)) 3 :appended))
(assert-event
 (and (not (fn-ocp-gc-failure-hyp *gc-s* *gc-early-acked* *gc-a* *gc-b*))
      (not (fn-ocp-gc-failure-okp *gc-s* *gc-early-acked* *gc-a* *gc-b* 100))))
(must-fail-checked
 (assert-event (fn-ocp-gc-failure-okp *gc-s* *gc-early-acked* *gc-a* *gc-b* 100)))
; Mutation tooth: incorrectly completing the next batch after the failure
; emits :rendered for its accepted member, violating the uncertain contract.
(assert-event
 (not (subsetp-equal (fn-ocs-member-releases :complete *gc-b*)
                    '(:own-uncertain :uncertain-reply :close))))
(must-fail-checked
 (assert-event (subsetp-equal (fn-ocs-member-releases :complete *gc-b*)
                             '(:own-uncertain :uncertain-reply :close))))

; MEMBERSHIP positive: old record 65, batch in flight 66, take 67 behind it.
(defconst *gc-take-base*
  (fn-lgk-make '((65)) *gc-head* 512 3 nil '((66)) 1 :appended))
(assert-event
 (and (fn-olr-gc-membership-hyp '((65) (66)) *gc-take-base* '(67) 3 0 0 2 4096 512)
      (fn-olr-gc-membership-okp '((65) (66)) *gc-take-base* '(67) 3 0 0 2 4096 512)
      (equal (fn-lgk-batch
               (cadr (fn-olr-take *gc-take-base* '(67) 3 0 0 2 4096 512))) '((67)))))
; A real current append closes the exact suffix when no earlier batch is in
; flight. This is why allowing append-behind needs a new kernel operation.
(defconst *gc-seal-base*
  (fn-lgk-make '((65)) *gc-head* 512 3 '((66)) nil 1 :fenced))
(defconst *gc-seal-take*
  (fn-olr-take *gc-seal-base* '(67) 3 1 5 2 4096 512))
(assert-event
 (and (fn-olr-gc-membership-hyp '((65) (66)) *gc-seal-base* '(67) 3 1 5 2 4096 512)
      (fn-olr-gc-membership-okp '((65) (66)) *gc-seal-base* '(67) 3 1 5 2 4096 512)
      (fn-lgc-append-admitsp (fn-lgc-of (cadr *gc-seal-take*)) 512 4096)
      (equal (fn-lgc-inflight
               (fn-lgc-append (fn-lgc-of (cadr *gc-seal-take*)) 512 4096))
             '((66) (67)))))

; MEMBERSHIP tooth: remove exact COUNT correspondence. Current TAKE trusts
; count=0, so a second record joins a supposedly one-record batch.
(assert-event
 (and (equal (car (fn-olr-take *gc-before* '(68) 4 0 5 1 4096 512)) :taken)
      (not (fn-olr-gc-membership-hyp *gc-h* *gc-before* '(68) 4 0 5 1 4096 512))
      (not (fn-olr-gc-membership-okp *gc-h* *gc-before* '(68) 4 0 5 1 4096 512))))
(must-fail-checked
 (assert-event (fn-olr-gc-membership-okp *gc-h* *gc-before* '(68) 4 0 5 1 4096 512)))
; Remove encoded-octet preflight: singleton is taken even at OMAX=1.
; OMAX=5 fits packed bytes exactly, yet still excludes framing/padding.
(assert-event
 (and (equal (car (fn-olr-take *gc-take-base* '(67) 3 0 0 2 1 512)) :taken)
      (not (fn-olr-gc-membership-hyp '((65) (66)) *gc-take-base* '(67) 3 0 0 2 1 512))
      (not (fn-olr-gc-membership-okp '((65) (66)) *gc-take-base* '(67) 3 0 0 2 1 512))
      (equal (car (fn-olr-take *gc-take-base* '(67) 3 0 0 2 5 512)) :taken)
      (not (fn-olr-gc-membership-okp '((65) (66)) *gc-take-base* '(67) 3 0 0 2 5 512))))
(must-fail-checked
 (assert-event (fn-olr-gc-membership-okp '((65) (66)) *gc-take-base* '(67) 3 0 0 2 1 512)))
