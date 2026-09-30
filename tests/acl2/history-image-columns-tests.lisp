(in-package "ACL2")
(include-book "../../books/history-image-columns")

(assert-event
 (let ((r (fn-hcl-admit 1 8 1 1)))
  (and (equal (car r) :prepared) (unsigned-byte-p 61 1) (unsigned-byte-p 64 8)
       (posp (nth 1 r)) (< (* 16384 (nth 1 r)) 18446744073709551616)
       (equal (nth 1 r) (fn-hcc-pages 1 1)) (equal r '(:prepared 6)))))
; Regional fields fit while their rounded canonical image exceeds u64.
(assert-event
 (and (unsigned-byte-p 61 (expt 2 59)) (unsigned-byte-p 64 (expt 2 62))
      (equal (fn-hcl-admit (expt 2 59) (expt 2 62) (expt 2 48) (expt 2 48))
             '(:refused :canonical-extent))))
(assert-event (equal (fn-hcl-admit -1 0 0 0) '(:refused :domain)))

(defun hclt-effect-tooth ()
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn-hpb
  (mv-let (out fn-hpb)
   (let* ((fn-hpb (fn-hpb-begin '(capture 7) '(lease 9) fn-hpb))
          (ev '(1 2 3)) (salt 0) (column 3) (offset 8)
          (key (fn-hp-mkey ev salt)) (encoded (len (fn-scc-encode ev)))
          (prior (fn-hpb-prefix fn-hpb)) (used (fn-hpb-used fn-hpb))
          (well (fn-hpbp fn-hpb))
          (cell (mv-list 2 (fn-hcl-cell column key encoded offset))))
    (mv-let (v fn-hpb) (fn-hcl-put column key encoded offset fn-hpb)
     (mv (and (natp column) (< column 4) (natp offset)
              (equal key (fn-hp-mkey ev salt)) (equal encoded (len (fn-scc-encode ev)))
              (natp used) (< used 2048) (equal (car cell) :word)
              (equal v :stored)
              (equal (fn-hpb-prefix fn-hpb)
                     (append prior (list (nth column (fn-hp-cells-of ev salt offset)))))
              well (unsigned-byte-p 64 key) (unsigned-byte-p 64 encoded)
              (unsigned-byte-p 64 offset) (fn-hpbp fn-hpb)
              (equal (fn-hpb-epoch fn-hpb) '(capture 7))
              (equal (fn-hpb-lease fn-hpb) '(lease 9))) fn-hpb)))
   out)))
(assert-event (hclt-effect-tooth))
(assert-event
 (equal (mv-list 2 (fn-hcl-cell 3 0 18446744073709551615 0)) '(:refused 0)))
; Mutation: emitted codec length cannot replace its individually padded length.
(assert-event
 (let* ((ev '(1 2 3)) (encoded (len (fn-scc-encode ev)))
        (r (mv-list 2 (fn-hcl-cell 3 0 encoded 8))))
  (and (equal (car r) :word) (not (equal (cadr r) encoded))
       (equal (cadr r) (nth 3 (fn-hp-cells-of ev 0 8))))))
