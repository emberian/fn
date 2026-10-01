(in-package "ACL2")
(include-book "../../books/replay-enrollment-span-equality")

(defconst *fn-rse-test-spans*
 '((:bytes 7 3 (11 12 13 99)) (:bytes 20 2 (21 22 88))
   (:bytes 30 3 (31 32 33 77))))
(defconst *fn-rse-test-keys*
 '((:ed25519 21 22) (:ml-dsa-65 31 32 33)))
(defconst *fn-rse-test-source* '(:issued 5 8 12 :snapshot))
(defconst *fn-rse-test-begin*
 (fn-rse-equality-begin '(11 12 13) *fn-rse-test-keys*
                         *fn-rse-test-spans* *fn-rse-test-source*))

; Complete literal establishment antecedent and conclusion.
(assert-event
 (and (fn-rse-keys-shapep *fn-rse-test-keys*)
      (fn-rse-spans-provenance-shapep *fn-rse-test-spans*)
      (fn-rse-equality-invariantp *fn-rse-test-begin*)
      (equal (fn-rse-equality-outcome *fn-rse-test-begin*)
       (equal (list '(11 12 13) *fn-rse-test-keys*)
              (fn-rse-enrollment-model *fn-rse-test-spans*)))))
; Full one-step result/invariant/borrow and strict work decrease.
(assert-event
 (mv-let (word next) (fn-rse-equality-step *fn-rse-test-begin*)
  (and (fn-rse-equality-invariantp *fn-rse-test-begin*)
       (eq word :working) (fn-rse-equality-invariantp next)
       (equal (fn-rse-equality-outcome next)
              (fn-rse-equality-outcome *fn-rse-test-begin*))
       (equal (fn-rsc-at 3 next) '(12 13 99))
       (equal (fn-rsc-at 6 next) *fn-rse-test-source*)
       (< (fn-rse-equality-workleft next)
          (fn-rse-equality-workleft *fn-rse-test-begin*)))))
; Budget zero yields exactly; ten ticks yield, the eleventh completes.
(assert-event
 (mv-let (word next) (fn-rse-equality-run 0 *fn-rse-test-begin*)
  (and (eq word :yield) (equal next *fn-rse-test-begin*))))
(assert-event
 (mv-let (word next) (fn-rse-equality-run 10 *fn-rse-test-begin*)
  (and (eq word :yield) (eq (fn-rsc-at 0 next) :ml-dsa-65)
       (equal (fn-rsc-at 5 next) 0) (fn-rse-equality-outcome next)
       (equal (fn-rsc-at 6 next) *fn-rse-test-source*))))
(assert-event
 (mv-let (word next) (fn-rse-equality-run 11 *fn-rse-test-begin*)
  (and (eq word :done) (eq (fn-rsc-at 7 next) t)
       (fn-rse-equality-invariantp next)
       (equal (fn-rsc-at 6 next) *fn-rse-test-source*))))
; First, middle, last octet mismatch; neither payload prefix is truncated.
(assert-event
 (mv-let (word next) (fn-rse-equality-run 11
  (fn-rse-equality-begin '(0 12 13) *fn-rse-test-keys*
                         *fn-rse-test-spans* *fn-rse-test-source*))
  (and (eq word :done) (not (fn-rsc-at 7 next)))))
(assert-event
 (mv-let (word next) (fn-rse-equality-run 11
  (fn-rse-equality-begin '(11 0 13) *fn-rse-test-keys*
                         *fn-rse-test-spans* *fn-rse-test-source*))
  (and (eq word :done) (not (fn-rsc-at 7 next)))))
(assert-event
 (mv-let (word next) (fn-rse-equality-run 11
  (fn-rse-equality-begin '(11 12 0) *fn-rse-test-keys*
                         *fn-rse-test-spans* *fn-rse-test-source*))
  (and (eq word :done) (not (fn-rsc-at 7 next)))))
(assert-event
 (mv-let (word next) (fn-rse-equality-run 11
  (fn-rse-equality-begin '(11 12) *fn-rse-test-keys*
                         *fn-rse-test-spans* *fn-rse-test-source*))
  (and (eq word :done) (not (fn-rsc-at 7 next)))))
(assert-event
 (mv-let (word next) (fn-rse-equality-run 11
  (fn-rse-equality-begin '(11 12 13 99) *fn-rse-test-keys*
                         *fn-rse-test-spans* *fn-rse-test-source*))
  (and (eq word :done) (not (fn-rsc-at 7 next)))))
; Empty fields do not require reading the borrowed trailing tails.
(assert-event
 (mv-let (word next) (fn-rse-equality-run 3
  (fn-rse-equality-begin nil '((:ed25519) (:ml-dsa-65))
   '((:bytes 0 0 (99)) (:bytes 1 0 (88)) (:bytes 2 0 (77))) :empty))
  (and (eq word :done) (eq (fn-rsc-at 7 next) t))))
; Refusal keeps an invalid cursor unchanged; terminal STEP is idempotent.
(assert-event
 (mv-let (word next) (fn-rse-equality-step '(:principal))
  (and (eq word :refused) (equal next '(:principal)))))
(assert-event
 (mv-let (word completed) (fn-rse-equality-run 11 *fn-rse-test-begin*)
  (mv-let (again next) (fn-rse-equality-step completed)
   (and (eq word :done) (eq again :done) (equal next completed)))))
; Corrupted-state provenance removal: every other invariant conjunct holds;
; missing actual octet-prefix evidence changes complete comparison outcome.
(defconst *fn-rse-test-bad-prefix*
 (fn-rse-equality-state :principal *fn-rse-test-keys* *fn-rse-test-spans*
                        nil '(nil) 1 *fn-rse-test-source* nil))
(assert-event
 (let ((s *fn-rse-test-bad-prefix*))
  (mv-let (word next) (fn-rse-equality-step s)
   (and (fn-rsc-widthp 8 s) (fn-rse-keys-shapep (fn-rsc-at 1 s))
        (fn-rse-spans-provenance-shapep (fn-rsc-at 2 s))
        (natp (fn-rsc-at 5 s)) (eq (fn-rsc-at 0 s) :principal)
        (not (fn-rse-octet-prefixp (fn-rsc-at 5 s) (fn-rsc-at 3 s)))
        (not (fn-rse-equality-invariantp s)) (eq word :done)
        (not (equal (fn-rse-equality-outcome next)
                    (fn-rse-equality-outcome s)))))))
; Length-free resident-tail phase used by revoked tombstone/detail binding.
(assert-event
 (let ((s (fn-rse-equality-begin-tails '(1 2 3) '(1 2 3) :same-issued)))
  (and (true-listp '(1 2 3)) (fn-rse-octet-prefixp 3 '(1 2 3))
       (fn-rse-equality-invariantp s)
       (equal (fn-rse-equality-outcome s) (equal '(1 2 3) '(1 2 3)))
       (equal (fn-rsc-at 6 s) :same-issued))))
(assert-event
 (mv-let (word next) (fn-rse-equality-run 3
  (fn-rse-equality-begin-tails '(1 2 3) '(1 2 3) :same-issued))
  (and (eq word :yield) (eq (fn-rsc-at 0 next) :tails)
       (null (fn-rsc-at 3 next)) (null (fn-rsc-at 4 next))
       (equal (fn-rsc-at 6 next) :same-issued))))
(assert-event
 (mv-let (word next) (fn-rse-equality-run 4
  (fn-rse-equality-begin-tails '(1 2 3) '(1 2 3) :same-issued))
  (and (eq word :done) (fn-rsc-at 7 next) (fn-rse-equality-invariantp next))))
(assert-event
 (mv-let (word next) (fn-rse-equality-run 4
  (fn-rse-equality-begin-tails '(1 2 3) '(1 0 3) :same-issued))
  (and (eq word :done) (not (fn-rsc-at 7 next)))))
(assert-event
 (mv-let (word next) (fn-rse-equality-run 4
  (fn-rse-equality-begin-tails '(1 2 3) '(1 2) :same-issued))
  (and (eq word :done) (not (fn-rsc-at 7 next)))))
(assert-event
 (mv-let (word next) (fn-rse-equality-run 4
  (fn-rse-equality-begin-tails '(1 2 3) '(1 2 3 4) :same-issued))
  (and (eq word :done) (not (fn-rsc-at 7 next)))))
(assert-event
 (mv-let (word next) (fn-rse-equality-run 1
  (fn-rse-equality-begin-tails nil nil :same-issued))
  (and (eq word :done) (fn-rsc-at 7 next))))
; Corruption/removal of resident octet domain, with every other invariant
; conjunct affirmative: equal non-octet tails must not get an equality claim.
(assert-event
 (let ((s (fn-rse-equality-begin-tails '(:not-octet) '(:not-octet) :same-issued)))
  (mv-let (word next) (fn-rse-equality-step s)
   (and (fn-rsc-widthp 8 s) (fn-rse-keys-shapep (fn-rsc-at 1 s))
        (fn-rse-spans-provenance-shapep (fn-rsc-at 2 s))
        (natp (fn-rsc-at 5 s)) (equal (fn-rsc-at 5 s) 0)
        (eq (fn-rsc-at 0 s) :tails) (true-listp (fn-rsc-at 3 s))
        (fn-rse-octet-prefixp 0 (fn-rsc-at 3 s))
        (not (fn-rse-octet-prefixp (len (fn-rsc-at 3 s)) (fn-rsc-at 3 s)))
        (not (fn-rse-equality-invariantp s)) (eq word :done)
        (not (equal (fn-rse-equality-outcome next) (fn-rse-equality-outcome s)))))))
; Removing :working from strict-progress theorem fails at a complete state.
(assert-event
 (mv-let (word terminal) (fn-rse-equality-run 1
  (fn-rse-equality-begin-tails nil nil :same-issued))
  (mv-let (again next) (fn-rse-equality-step terminal)
   (and (eq word :done) (fn-rse-equality-invariantp terminal)
        (not (eq again :working)) (equal next terminal)
        (not (< (fn-rse-equality-workleft next) (fn-rse-equality-workleft terminal)))))))
