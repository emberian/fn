; Teeth for books/bp-fragment-resume.lisp (PRF-250).
(in-package "ACL2")
(include-book "../../books/bp-fragment-resume")

; A 10-octet ADU in three fragments, out of order, overlapping at 4..5.
(defconst *bpfr-fs*
  (list (fn-bpf-make 6 '(7 8 9 10) 10)
        (fn-bpf-make 0 '(1 2 3 4 5 6) 10)
        (fn-bpf-make 4 '(5 6 7) 10)))
(defconst *bpfr-total* 10)
; The same family missing octets 8..9 (never completes).
(defconst *bpfr-gap-fs*
  (list (fn-bpf-make 0 '(1 2 3 4 5 6) 10)
        (fn-bpf-make 4 '(5 6 7 8) 10)))
; Two fragments disagreeing at 5.
(defconst *bpfr-conflict-fs*
  (list (fn-bpf-make 0 '(1 2 3 4 5 6) 10)
        (fn-bpf-make 5 '(99 7 8 9 10) 10)))

(defconst *bpfr-s0* (fn-bpfr-start *bpfr-fs* *bpfr-total*))
(defconst *bpfr-s1* (fn-bpfr-step (nth 0 *bpfr-s0*) (nth 1 *bpfr-s0*)
                                  (nth 2 *bpfr-s0*) (nth 3 *bpfr-s0*)
                                  (nth 4 *bpfr-s0*) 4))

(assert-event (equal (fn-bpfw-reassemble *bpfr-fs* *bpfr-total*)
                     (list :ok '(1 2 3 4 5 6 7 8 9 10))))

; KEYSTONE fn-bpfr-step-resumes (hypothesis-free): one step of 4 then the
; rest is the whole sweep.
(assert-event
 (equal (fn-bpfr-resume *bpfr-s1*)
        (fn-bpfw-sweep-acc (nth 0 *bpfr-s0*) (nth 1 *bpfr-s0*) 0 10 nil)))
(assert-event (equal (fn-bpfr-resume *bpfr-s1*) '(1 2 3 4 5 6 7 8 9 10)))

; fn-bpfr-step-is-bounded: 4 positions consumed, 4 cells emitted.
(assert-event
 (and (equal (nth 3 *bpfr-s1*) 6)
      (equal (nth 4 *bpfr-s1*) '(4 3 2 1))
      (equal (nth 2 *bpfr-s1*) 4)))
; Without (natp n): a left count of 5/2 is taken as none; the step
; consumes nothing, not min(5/2, 4).
(assert-event
 (with-guard-checking :none
  (let ((s (fn-bpfr-step nil (fn-bpfw-sort *bpfr-fs*) 0 5/2 nil 4)))
   (and (not (natp 5/2)) (natp 4) (true-listp nil)
        (not (equal (nth 3 s) (- 5/2 (min 5/2 4))))))))
; Without (natp quantum): a quantum of -1 consumes nothing, and
; n - min(n, -1) is n + 1.
(assert-event
 (with-guard-checking :none
  (let ((s (fn-bpfr-step nil (fn-bpfw-sort *bpfr-fs*) 0 10 nil -1)))
   (and (natp 10) (not (natp -1)) (true-listp nil)
        (not (equal (nth 3 s) (- 10 (min 10 -1))))))))

; fn-bpfr-finished-state-is-the-sweep.
(defconst *bpfr-done* (fn-bpfr-run *bpfr-s0* 3))
(assert-event (and (zp (nth 3 *bpfr-done*))
                   (equal (fn-bpfr-resume *bpfr-done*)
                          (reverse (nth 4 *bpfr-done*)))))
; Without (zp left): the start state's cells are none, its sweep ten.
(assert-event (and (not (zp (nth 3 *bpfr-s0*)))
                   (not (equal (fn-bpfr-resume *bpfr-s0*)
                               (reverse (nth 4 *bpfr-s0*))))))

; KEYSTONE fn-bpfr-run-is-reassemble, for quanta 1, 3, 4 and 64, over a
; complete, a never-completing and a conflicting family: the four outcomes
; stay distinct and equal the one-call reassembler's.
(defmacro bpfr-run-ok (fs total q)
  `(let ((s (fn-bpfr-run (fn-bpfr-start ,fs ,total) ,q)))
     (and (zp (nth 3 s))
          (equal (fn-bpfr-finish ,fs ,total s)
                 (fn-bpfw-reassemble ,fs ,total))
          (equal (fn-bpfr-finish ,fs ,total s)
                 (fn-bpfw-spec ,fs ,total)))))
(assert-event (and (bpfr-run-ok *bpfr-fs* 10 1) (bpfr-run-ok *bpfr-fs* 10 3)
                   (bpfr-run-ok *bpfr-fs* 10 4) (bpfr-run-ok *bpfr-fs* 10 64)))
(assert-event (and (bpfr-run-ok *bpfr-gap-fs* 10 3)
                   (equal (fn-bpfw-reassemble *bpfr-gap-fs* 10)
                          (list :missing 8 10))))
(assert-event (and (bpfr-run-ok *bpfr-conflict-fs* 10 3)
                   (equal (car (fn-bpfw-reassemble *bpfr-conflict-fs* 10))
                          :conflict)))
(assert-event (and (bpfr-run-ok *bpfr-fs* 11 3)
                   (equal (car (fn-bpfw-reassemble *bpfr-fs* 11)) :invalid)))
; Without (posp quantum): a quantum of 0 never moves; the run does not
; finish.
(assert-event
 (let ((s (fn-bpfr-run (fn-bpfr-start *bpfr-fs* 10) 0)))
   (and (not (posp 0)) (not (zp (nth 3 s))))))
