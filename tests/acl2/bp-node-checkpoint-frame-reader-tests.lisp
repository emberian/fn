; Bounded header source witnesses; no digest/recovery or funding authority.
(in-package "ACL2")
(include-book "../../books/bp-node-checkpoint-frame-reader")
(include-book "bp-checkpoint-reader-encoder-refinement-tests")
(defconst *bpfrt-count* (len *bpcret-bytes*))
(defconst *bpfrt-bound* 1048576)
(defconst *bpfrt-prefix* (fn-bpck-prefix *bpfrt-count*))
(defconst *bpfrt-job* (fn-bpfr-begin :unfunded-source-token 1 *bpcret-depth*
                                    *bpfrt-bound* (+ 46 *bpfrt-count*)))
(defconst *bpfrt-input* (append *bpfrt-prefix* '(65 66)))
(defconst *bpfrt-expected*
 (list (fn-bpfr-make :integrity-required :unfunded-source-token 1 *bpcret-depth*
                     *bpfrt-bound* (+ 46 *bpfrt-count*) 14 *bpfrt-count* nil)
       '(65 66) 14))
; Actual CK7 producer count, complete four hypotheses and entire result.
(assert-event
 (and (posp *bpfrt-count*) (<= *bpfrt-count* *fn-bpc-max-uint*)
      (natp *bpfrt-bound*) (<= (+ 46 *bpfrt-count*) *bpfrt-bound*)
      (equal (fn-bpfr-header-run *bpfrt-job* *bpfrt-input* 14) *bpfrt-expected*)))
; Real interruption after four source bytes, then exact ten-turn resume.
(defconst *bpfrt-short* (fn-bpfr-header-run *bpfrt-job* *bpfrt-input* 4))
(assert-event
 (and (natp 4) (natp (fn-bpn-nth 2 *bpfrt-short*))
      (<= (fn-bpn-nth 2 *bpfrt-short*) 4)
      (equal (fn-bpn-nth 2 *bpfrt-short*) 4)
      (equal (fn-bpn-nth 1 (fn-bpn-nth 0 *bpfrt-short*)) :header)
      (equal (fn-bpn-nth 7 (fn-bpn-nth 0 *bpfrt-short*)) 4)))
(assert-event
 (let ((a (fn-bpfr-header-run (fn-bpn-nth 0 *bpfrt-short*)
                             (fn-bpn-nth 1 *bpfrt-short*) 10)))
  (and (equal (fn-bpn-nth 0 a) (fn-bpn-nth 0 *bpfrt-expected*))
       (equal (fn-bpn-nth 1 a) '(65 66)) (equal (fn-bpn-nth 2 a) 10))))
; Remove positive count only. Zero payload is not a usable CK7 encoding.
(assert-event
 (let ((a (fn-bpfr-header-run (fn-bpfr-begin :unfunded-source-token 1 100 100 46)
                             (append (fn-bpck-prefix 0) '(65 66)) 14)))
  (and (not (posp 0)) (<= 0 *fn-bpc-max-uint*) (natp 100) (<= (+ 46 0) 100)
       (equal (fn-bpn-nth 1 (fn-bpn-nth 0 a)) :refused)
       (not (equal a (list (fn-bpfr-make :integrity-required :unfunded-source-token
                              1 100 100 46 14 0 nil) '(65 66) 14))))))
; Remove representation limit only, retaining all other hypotheses.
(defconst *bpfrt-wide* (+ 1 *fn-bpc-max-uint*))
(assert-event
 (let* ((bound (+ 46 *bpfrt-wide*))
        (a (fn-bpfr-header-run (fn-bpfr-begin :unfunded-source-token 1 100 bound bound)
                               (append (fn-bpck-prefix *bpfrt-wide*) '(65 66)) 14)))
  (and (posp *bpfrt-wide*) (not (<= *bpfrt-wide* *fn-bpc-max-uint*))
       (natp bound) (<= (+ 46 *bpfrt-wide*) bound)
       (not (equal a (list (fn-bpfr-make :integrity-required :unfunded-source-token
                             1 100 bound bound 14 *bpfrt-wide* nil) '(65 66) 14))))))
; Remove natural format bound only; this is an invalid profile witness.
(assert-event
 (let ((a (fn-bpfr-header-run (fn-bpfr-begin :unfunded-source-token 1 100 95/2 47)
                             (append (fn-bpck-prefix 1) '(65 66)) 14)))
  (and (posp 1) (<= 1 *fn-bpc-max-uint*) (not (natp 95/2)) (<= (+ 46 1) 95/2)
       (not (equal a (list (fn-bpfr-make :integrity-required :unfunded-source-token
                             1 100 95/2 47 14 1 nil) '(65 66) 14))))))
; Remove fitted frame only, retaining valid count/representation/natural bound.
(assert-event
 (let ((a (fn-bpfr-header-run (fn-bpfr-begin :unfunded-source-token 1 100 46 47)
                             (append (fn-bpck-prefix 1) '(65 66)) 14)))
  (and (posp 1) (<= 1 *fn-bpc-max-uint*) (natp 46) (not (<= (+ 46 1) 46))
       (not (equal a (list (fn-bpfr-make :integrity-required :unfunded-source-token
                             1 100 46 47 14 1 nil) '(65 66) 14))))))
; Quantum omission is a logical invalid-guard witness, not a native call.
(assert-event (with-guard-checking :none
 (let ((a (fn-bpfr-header-run *bpfrt-job* *bpfrt-input* -1)))
  (and (not (natp -1)) (natp (fn-bpn-nth 2 a))
       (not (<= (fn-bpn-nth 2 a) -1))))))
; Mutation witnesses: bad magic and observed length disagreement refuse;
; neither advances into payload construction or returns integrity authority.
(assert-event
 (let ((a (fn-bpfr-header-run *bpfrt-job* (cons 0 (cdr *bpfrt-input*)) 14)))
  (and (equal (fn-bpn-nth 1 (fn-bpn-nth 0 a)) :refused)
       (equal (fn-bpn-nth 9 (fn-bpn-nth 0 a)) :header)
       (equal (fn-bpn-nth 2 a) 1))))
(assert-event
 (let ((a (fn-bpfr-header-run
          (fn-bpfr-begin :unfunded-source-token 1 *bpcret-depth* *bpfrt-bound*
                         (+ 47 *bpfrt-count*)) *bpfrt-input* 14)))
  (and (equal (fn-bpn-nth 1 (fn-bpn-nth 0 a)) :refused)
       (equal (fn-bpn-nth 9 (fn-bpn-nth 0 a)) :payload-length)
       (equal (fn-bpn-nth 1 a) '(65 66)))))
