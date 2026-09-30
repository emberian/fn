(in-package "ACL2")
(include-book "../../books/history-page-metadata")

(defconst *hpmt-digest* (+ (expt 2 200) 55))
(assert-event
 (and (natp 2) (< 2 6) (unsigned-byte-p 64 19)
      (equal (fn-hpm-word 2 19 *hpmt-digest*)
             (nth 2 (pgs-entry-words (list 19 1 *hpmt-digest*))))))
; Corrupted component and address witnesses retain every other entry premise.
(assert-event
 (with-guard-checking :none
  (and (not (natp -1)) (< -1 6) (unsigned-byte-p 64 19)
       (not (equal (fn-hpm-word -1 19 *hpmt-digest*)
                   (nth -1 (pgs-entry-words (list 19 1 *hpmt-digest*))))))))
(assert-event
 (with-guard-checking :none
  (and (natp 6) (not (< 6 6)) (unsigned-byte-p 64 19)
       (not (equal (fn-hpm-word 6 19 *hpmt-digest*)
                   (nth 6 (pgs-entry-words (list 19 1 *hpmt-digest*))))))))
(assert-event
 (with-guard-checking :none
  (and (natp 0) (< 0 6) (not (unsigned-byte-p 64 18446744073709551616))
       (not (equal (fn-hpm-word 0 18446744073709551616 *hpmt-digest*)
                   (nth 0 (pgs-entry-words (list 18446744073709551616 1 *hpmt-digest*))))))))
(assert-event (equal (fn-hpm-request 3 2 9 10) '(:entry 3 2 13)))
(assert-event (equal (fn-hpm-request 9 0 9 10) '(:padding 0)))
(assert-event (equal (fn-hpm-request 1 0 9 18446744073709551615) '(:refused :address)))

(defun hpmt-fill (n ordinal component remaining fn-hpb)
 (declare (xargs :stobjs fn-hpb :verify-guards nil))
 (if (zp n) (mv ordinal component remaining fn-hpb)
  (mv-let (v ordinal component remaining fn-hpb)
   (fn-hpm-tick ordinal component remaining 342 10 *hpmt-digest* fn-hpb)
   (declare (ignore v))
   (hpmt-fill (1- n) ordinal component remaining fn-hpb))))

(defun hpmt-cross-page-tooth ()
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn-hpb
  (mv-let (out fn-hpb)
   (let ((fn-hpb (fn-hpb-begin '(capture 7) '(lease 9) fn-hpb)))
    (mv-let (ordinal component remaining fn-hpb) (hpmt-fill 2048 0 0 4096 fn-hpb)
     (let ((first (fn-hpb-prefix fn-hpb)))
      (mv-let (v ord2 comp2 rem2 fn-hpb)
       (fn-hpm-tick ordinal component remaining 342 10 *hpmt-digest* fn-hpb)
       (let* ((blocked (and (equal v :page-full) (equal ord2 ordinal)
                            (equal comp2 component) (equal rem2 remaining)
                            (equal first (fn-hpb-prefix fn-hpb))))
              (fn-hpb (fn-hpb-begin '(capture 7) '(lease 9) fn-hpb)))
        (mv-let (ord3 comp3 rem3 fn-hpb) (hpmt-fill 2048 ord2 comp2 rem2 fn-hpb)
         (let ((second (fn-hpb-prefix fn-hpb)))
          (mv-let (v4 ord4 comp4 rem4 fn-hpb)
           (fn-hpm-tick ord3 comp3 rem3 342 10 *hpmt-digest* fn-hpb)
           (mv (and blocked (equal ordinal 341) (equal component 2)
                    (equal remaining 2048) (equal v4 :done)
                    (equal ord4 ord3) (equal comp4 comp3) (equal rem4 0)
                    (equal second (fn-hpb-prefix fn-hpb))
                    (equal (append first second)
                           (pgs-encode-run
                            (fn-hpm-model-entries (make-list 342 :initial-element *hpmt-digest*) 10) 2))
                    (fn-hpbp fn-hpb)
                    (equal (fn-hpb-epoch fn-hpb) '(capture 7))
                    (equal (fn-hpb-lease fn-hpb) '(lease 9))) fn-hpb)))))))))
   out)))
(assert-event (hpmt-cross-page-tooth))

(defun hpmt-literal-effect-tooth (supplied)
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn-hpb
  (mv-let (out fn-hpb)
   (let* ((fn-hpb (fn-hpb-begin '(capture 7) '(lease 9) fn-hpb))
          (ds (list 7 *hpmt-digest*)) (base 10) (ordinal 1) (component 2)
          (entries (len ds)) (prior (fn-hpb-prefix fn-hpb))
          (used (fn-hpb-used fn-hpb)))
    (mv-let (v ordinal2 component2 remaining2 fn-hpb)
     (fn-hpm-tick ordinal component 4 entries base supplied fn-hpb)
     (mv (and (natp base) (natp ordinal) (< ordinal (len ds))
              (natp component) (< component 6)
              (unsigned-byte-p 64 (+ base ordinal))
              (equal entries (len ds)) (natp used) (equal v :stored)
              (equal ordinal2 1) (equal component2 3) (equal remaining2 3)
              (if (equal supplied (nth ordinal ds))
                  (equal (fn-hpb-prefix fn-hpb)
                         (append prior
                                 (list (nth (+ (* 6 ordinal) component)
                                            (pgs-encode-run (fn-hpm-model-entries ds base) 1)))))
                (and (not (equal supplied (nth ordinal ds)))
                     (not (equal (fn-hpb-prefix fn-hpb)
                                 (append prior
                                         (list (nth (+ (* 6 ordinal) component)
                                                    (pgs-encode-run (fn-hpm-model-entries ds base) 1)))))))))
         fn-hpb)))
   out)))
(assert-event (hpmt-literal-effect-tooth *hpmt-digest*))
; Source-misattribution witness: all retained effect hypotheses hold; only
; supplied digest equality fails and so does the exact encoded-run conclusion.
(assert-event (hpmt-literal-effect-tooth 0))
