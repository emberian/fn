; Bounded continuation refuters over the real CK7 encoder's exact bytes.
(in-package "ACL2")
(include-book "../../books/bp-node-checkpoint-reader")
(include-book "bp-checkpoint-value-domain-tests")
(defconst *bpcrt-keyword-bytes* (fn-bpnr-enc :fn-bp-primary 100))
(defconst *bpcrt-keyword* (fn-bpcr-run (fn-bpcr-begin 100) *bpcrt-keyword-bytes* 100))
(assert-event (and (equal (fn-bpn-nth 1 (fn-bpn-nth 0 *bpcrt-keyword*)) :done) (equal (fn-bpn-nth 3 (fn-bpn-nth 0 *bpcrt-keyword*)) '(:fn-bp-primary)) (null (fn-bpn-nth 1 *bpcrt-keyword*)) (equal (fn-bpn-nth 10 (fn-bpn-nth 0 *bpcrt-keyword*)) (len *bpcrt-keyword-bytes*))))
; Entire real producer checkpoint, including reassembly lineage and handoff.
(defconst *bpcrt-depth* (fn-bpnr-depth-budget 8))
(defconst *bpcrt-bytes* (fn-bpnr-enc *bpcvt-checkpoint* *bpcrt-depth*))
(defconst *bpcrt-answer* (fn-bpcr-run (fn-bpcr-begin *bpcrt-depth*) *bpcrt-bytes* 100000))
(assert-event (and (fn-bpcv-valuep *bpcvt-checkpoint*) (consp *bpcrt-bytes*) (equal (fn-bpn-nth 1 (fn-bpn-nth 0 *bpcrt-answer*)) :done) (equal (fn-bpn-nth 3 (fn-bpn-nth 0 *bpcrt-answer*)) (list *bpcvt-checkpoint*)) (null (fn-bpn-nth 1 *bpcrt-answer*)) (equal (fn-bpn-nth 10 (fn-bpn-nth 0 *bpcrt-answer*)) (len *bpcrt-bytes*))))
; Literal quantum theorem: complete antecedent and all four conclusions.
(defconst *bpcrt-short* (fn-bpcr-run (fn-bpcr-begin *bpcrt-depth*) *bpcrt-bytes* 4))
(assert-event (and (natp 4) (natp (fn-bpn-nth 2 *bpcrt-short*)) (natp (fn-bpn-nth 3 *bpcrt-short*)) (<= (fn-bpn-nth 3 *bpcrt-short*) (fn-bpn-nth 2 *bpcrt-short*)) (<= (fn-bpn-nth 2 *bpcrt-short*) 4) (equal (fn-bpn-nth 1 (fn-bpn-nth 0 *bpcrt-short*)) :decoding)))
; Quantum premise omission is a logical invalid-guard witness only.
(assert-event (with-guard-checking :none (let ((a (fn-bpcr-run (fn-bpcr-begin 2) '(0) -1))) (and (not (natp -1)) (natp (fn-bpn-nth 2 a)) (natp (fn-bpn-nth 3 a)) (<= (fn-bpn-nth 3 a) (fn-bpn-nth 2 a)) (not (<= (fn-bpn-nth 2 a) -1))))))
; Octet-list reversal is itself resumable, not a hidden whole-leaf operation.
(defconst *bpcrt-octets* (fn-bpnr-enc '(65 66 67) 10))
(defconst *bpcrt-before-reverse* (fn-bpcr-run (fn-bpcr-begin 10) *bpcrt-octets* 12))
(assert-event (and (equal (fn-bpn-nth 4 (fn-bpn-nth 0 *bpcrt-before-reverse*)) :reverse) (null (fn-bpn-nth 1 *bpcrt-before-reverse*)) (equal (fn-bpn-nth 8 (fn-bpn-nth 0 *bpcrt-before-reverse*)) '(67 66 65)) (equal (fn-bpn-nth 2 *bpcrt-before-reverse*) 12) (equal (fn-bpn-nth 3 *bpcrt-before-reverse*) 12)))
(assert-event (let ((a (fn-bpcr-run (fn-bpn-nth 0 *bpcrt-before-reverse*) nil 1))) (and (equal (fn-bpn-nth 4 (fn-bpn-nth 0 a)) :reverse) (equal (fn-bpn-nth 8 (fn-bpn-nth 0 a)) '(66 65)) (equal (fn-bpn-nth 9 (fn-bpn-nth 0 a)) '(67)) (equal (fn-bpn-nth 2 a) 1) (equal (fn-bpn-nth 3 a) 0))))
(assert-event (let ((a (fn-bpcr-run (fn-bpn-nth 0 *bpcrt-before-reverse*) nil 10))) (and (equal (fn-bpn-nth 1 (fn-bpn-nth 0 a)) :done) (equal (fn-bpn-nth 3 (fn-bpn-nth 0 a)) '((65 66 67))) (equal (fn-bpn-nth 3 a) 0))))
; Unsupported real legacy codec families refuse before materialization.
(assert-event (let ((a (fn-bpcr-run (fn-bpcr-begin 20) (fn-bpnr-enc 'acl2::foreign-symbol 20) 100))) (and (equal (fn-bpn-nth 1 (fn-bpn-nth 0 a)) :refused) (equal (fn-bpn-nth 4 (fn-bpn-nth 0 a)) :unsupported-leaf) (equal (fn-bpn-nth 3 a) 1))))
(assert-event (let ((a (fn-bpcr-run (fn-bpcr-begin 20) (fn-bpnr-enc "foreign-string" 20) 100))) (and (equal (fn-bpn-nth 1 (fn-bpn-nth 0 a)) :refused) (equal (fn-bpn-nth 3 a) 1))))
(assert-event (let ((a (fn-bpcr-run (fn-bpcr-begin 20) (fn-bpnr-enc :foreign-keyword 20) 100))) (and (equal (fn-bpn-nth 1 (fn-bpn-nth 0 a)) :refused) (equal (fn-bpn-nth 4 (fn-bpn-nth 0 a)) :unknown-keyword))))

; Resume the real checkpoint from its four-turn interruption, exact output.
(assert-event (let ((a (fn-bpcr-run (fn-bpn-nth 0 *bpcrt-short*) (fn-bpn-nth 1 *bpcrt-short*) 100000))) (and (equal (fn-bpn-nth 1 (fn-bpn-nth 0 a)) :done) (null (fn-bpn-nth 1 a)) (equal (fn-bpn-nth 3 (fn-bpn-nth 0 a)) (list *bpcvt-checkpoint*)) (equal (fn-bpn-nth 10 (fn-bpn-nth 0 a)) (len *bpcrt-bytes*)))))
(defun bpcrt-all-keywords (symbols)
 (declare (xargs :guard t :verify-guards nil))
 (if (consp symbols)
  (let* ((bytes (fn-bpnr-enc (car symbols) 100))
         (a (fn-bpcr-run (fn-bpcr-begin 100) bytes 100)))
   (and (equal (fn-bpn-nth 1 (fn-bpn-nth 0 a)) :done)
        (equal (fn-bpn-nth 3 (fn-bpn-nth 0 a)) (list (car symbols)))
        (null (fn-bpn-nth 1 a)) (bpcrt-all-keywords (cdr symbols)))) t))
; Every actual vocabulary member, including shared-prefix keyword names.
(assert-event (bpcrt-all-keywords *fn-bpcv-keywords*))

; Literal continuation witness uses a real one-turn interruption.
; COMPLETE is non-executable and is checked as a logical theorem, while
; the actual bounded output/status assertions below remain executable.
(defthm bpcrt-one-turn-preserves-complete-literal
 (let* ((job (fn-bpcr-begin 2))
        (input '(0))
        (a (fn-bpcr-run job input 1)))
  (and (equal (fn-bpn-nth 1 (fn-bpn-nth 0 a)) :decoding)
       (null (fn-bpn-nth 1 a))
       (equal (fn-bpcr-complete (fn-bpn-nth 0 a) (fn-bpn-nth 1 a))
              (fn-bpcr-complete job input))))
 :hints (("Goal" :in-theory (enable fn-bpcr-complete fn-bpcr-run
                                  fn-bpcr-begin fn-bpcr-decode-tick
                                  fn-bpcr-action fn-bpcr-make fn-bpcr-leaf)))
 :rule-classes nil)

; Strict progress: real available read, both complete hypotheses and result.
(assert-event
 (let* ((job (fn-bpcr-begin 2)) (input '(5 0))
        (tick (fn-bpcr-decode-tick job 5)) (next (fn-bpn-nth 0 tick)))
  (and (equal (fn-bpcr-action job) :read) (consp input)
       (equal (fn-bpn-nth 1 next) :decoding)
       (< (fn-bpcr-measure next (cdr input))
          (fn-bpcr-measure job input)))))
; Remove input availability, retaining the next-decoding hypothesis.
; This is an intentionally incomplete external input, not a served read.
(assert-event
 (let* ((job (fn-bpn-nth 0 (fn-bpcr-decode-tick (fn-bpcr-begin 2) 5)))
        (next (fn-bpn-nth 0 (fn-bpcr-decode-tick job 0))))
  (and (equal (fn-bpcr-action job) :read) (not (consp nil))
       (equal (fn-bpn-nth 1 next) :decoding)
       (not (< (fn-bpcr-measure next nil) (fn-bpcr-measure job nil))))))
; Remove next-decoding, affirming availability for an already settled job.
(assert-event
 (let* ((job (fn-bpn-nth 0 (fn-bpcr-run (fn-bpcr-begin 2) '(0) 3)))
        (next (fn-bpn-nth 0 (fn-bpcr-decode-tick job 0))))
  (and (not (equal (fn-bpcr-action job) :read))
       (not (equal (fn-bpn-nth 1 next) :decoding))
       (not (< (fn-bpcr-measure next nil) (fn-bpcr-measure job nil))))))
