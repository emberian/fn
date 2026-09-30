(in-package "ACL2")
(include-book "../../books/bp-node-checkpoint-payload-reader")
(include-book "../../books/bp-checkpoint-reader-encoder-refinement")

; Actual producer, not a fabricated decoder row. The example is a typed pair;
; integrity/workspace authority is deliberately outside this internal fixture.
(defconst *bpprt-bytes* (fn-bpnr-enc '(0 . 1) 2))
(defconst *bpprt-answer*
 (fn-bpfr-payload-run (fn-bpcr-begin 2) (len *bpprt-bytes*)
                      *bpprt-bytes* 128))
(assert-event
 (and (natp 128)
      (equal (fn-bpn-nth 0 *bpprt-answer*) :decoded)
      (equal (fn-bpn-nth 2 *bpprt-answer*) nil)
      (equal (fn-bpn-nth 10 (fn-bpn-nth 1 *bpprt-answer*)) (len *bpprt-bytes*))
      (equal (car (fn-bpn-nth 3 (fn-bpn-nth 1 *bpprt-answer*))) '(0 . 1))
      (natp (fn-bpn-nth 3 *bpprt-answer*))
      (natp (fn-bpn-nth 4 *bpprt-answer*))
      (<= (fn-bpn-nth 4 *bpprt-answer*) (fn-bpn-nth 3 *bpprt-answer*))
      (<= (fn-bpn-nth 3 *bpprt-answer*) 128)))

; Actual scheduler interruption, followed by unchanged producer bytes.
(defconst *bpprt-first*
 (fn-bpfr-payload-run (fn-bpcr-begin 2) (len *bpprt-bytes*) *bpprt-bytes* 4))
(assert-event
 (and (equal (fn-bpn-nth 0 *bpprt-first*) :yield)
      (equal (fn-bpn-nth 3 *bpprt-first*) 4)
      (equal (fn-bpfr-payload-run (fn-bpn-nth 1 *bpprt-first*)
                                  (len *bpprt-bytes*)
                                  (fn-bpn-nth 2 *bpprt-first*) 128)
             (list :decoded (fn-bpn-nth 1 *bpprt-answer*) nil
                   (- (fn-bpn-nth 3 *bpprt-answer*) 4)
                   (- (fn-bpn-nth 4 *bpprt-answer*)
                      (fn-bpn-nth 4 *bpprt-first*))))))

; Length overrun (including a trailer byte) refuses before decoder work and
; retains both input and exact decoder. It never silently truncates.
(assert-event
 (equal (fn-bpfr-payload-run (fn-bpcr-begin 2) (len *bpprt-bytes*)
                             (append *bpprt-bytes* '(99)) 128)
        (list :refused (fn-bpcr-begin 2) (append *bpprt-bytes* '(99)) 0 0)))
; A complete shorter value cannot stand in for the declared payload.
(assert-event
 (equal (fn-bpn-nth 0 (fn-bpfr-payload-run (fn-bpcr-begin 2)
                       (+ 1 (len *bpprt-bytes*)) *bpprt-bytes* 128)) :refused))
; A valid source read larger than the fixed one-read64 workspace refuses.
(assert-event
 (equal (fn-bpfr-payload-run (fn-bpcr-begin 2) 65
                             (make-list 65 :initial-element 0) 128)
        (list :refused (fn-bpcr-begin 2) (make-list 65 :initial-element 0) 0 0)))

; Quantum hypothesis removal: explicitly invalid caller guard, not corrupt
; persisted state. There are no other hypotheses to retain.
(assert-event (with-guard-checking :none
 (let ((answer (fn-bpfr-payload-run (fn-bpcr-begin 2)
                  (len *bpprt-bytes*) *bpprt-bytes* -1)))
  (and (not (natp -1))
       (not (and (natp (fn-bpn-nth 3 answer)) (natp (fn-bpn-nth 4 answer))
                  (<= (fn-bpn-nth 4 answer) (fn-bpn-nth 3 answer))
                  (<= (fn-bpn-nth 3 answer) -1)))))))

; Whole actual CK7 is 70 bytes: two supported reads, not one oversized input.
; The test input split is fixture construction, never a served-path slice.
(defconst *bpprt-ck-value* (fn-bpnr-checkpoint 1 nil nil '(0 . 1) 8 0))
(defconst *bpprt-ck-depth* (fn-bpnr-depth-budget 8))
(defconst *bpprt-ck-bytes* (fn-bpnr-enc *bpprt-ck-value* *bpprt-ck-depth*))
(defconst *bpprt-ck-first*
 (fn-bpfr-payload-run (fn-bpcr-begin *bpprt-ck-depth*)
                      (len *bpprt-ck-bytes*) (take 64 *bpprt-ck-bytes*) 128))
(defconst *bpprt-ck-second*
 (fn-bpfr-payload-run (fn-bpn-nth 1 *bpprt-ck-first*)
                      (len *bpprt-ck-bytes*) (nthcdr 64 *bpprt-ck-bytes*) 128))
(assert-event
 (and (equal (len *bpprt-ck-bytes*) 70)
      (equal (fn-bpn-nth 0 *bpprt-ck-first*) :yield)
      (equal (fn-bpn-nth 2 *bpprt-ck-first*) nil)
      (equal (fn-bpn-nth 4 *bpprt-ck-first*) 64)
      (equal (fn-bpn-nth 0 *bpprt-ck-second*) :decoded)
      (equal (fn-bpn-nth 2 *bpprt-ck-second*) nil)
      (equal (fn-bpn-nth 4 *bpprt-ck-second*) 6)
      (equal (fn-bpn-nth 10 (fn-bpn-nth 1 *bpprt-ck-second*)) 70)
      (equal (car (fn-bpn-nth 3 (fn-bpn-nth 1 *bpprt-ck-second*)))
             *bpprt-ck-value*)))
