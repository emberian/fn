(in-package "ACL2")
(include-book "../../books/history-image-header")

(assert-event
 (and (natp 17) (< 17 2048)
      (equal (fn-hch-word 17 2 24 1 1)
             (nth 17 (fn-hp-hdr2 2 (fn-hcc-lens 2 24)
                                  (fn-hcc-starts 1) (fn-hcc-pages 1 1))))))
(assert-event
 (with-guard-checking :none
  (and (not (natp -1)) (< -1 2048)
       (not (equal (fn-hch-word -1 2 24 1 1)
                   (nth -1 (fn-hp-hdr2 2 (fn-hcc-lens 2 24)
                                        (fn-hcc-starts 1) (fn-hcc-pages 1 1))))))))
(assert-event
 (with-guard-checking :none
  (and (natp 2048) (not (< 2048 2048))
       (not (equal (fn-hch-word 2048 2 24 1 1)
                   (nth 2048 (fn-hp-hdr2 2 (fn-hcc-lens 2 24)
                                          (fn-hcc-starts 1) (fn-hcc-pages 1 1))))))))

(defun hcht-fill (n fn-hpb)
 (declare (xargs :stobjs fn-hpb :verify-guards nil))
 (if (zp n) fn-hpb
  (mv-let (v fn-hpb) (fn-hch-tick 2 24 1 1 fn-hpb)
   (declare (ignore v)) (hcht-fill (1- n) fn-hpb))))

(defun hcht-effect-tooth ()
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn-hpb
  (mv-let (out fn-hpb)
   (let* ((fn-hpb (fn-hpb-begin '(capture 7) '(lease 9) fn-hpb))
          (fn-hpb (hcht-fill 17 fn-hpb))
          (k (fn-hpb-used fn-hpb)) (prior (fn-hpb-prefix fn-hpb))
          (well (fn-hpbp fn-hpb)))
    (mv-let (v fn-hpb) (fn-hch-tick 2 24 1 1 fn-hpb)
     (mv (and (natp k) (< k 2048) well
              (unsigned-byte-p 61 2) (unsigned-byte-p 64 24)
              (unsigned-byte-p 51 1)
              (equal v :stored)
              (equal (fn-hpb-prefix fn-hpb)
                     (append prior (list (nth k (fn-hp-hdr2 2 (fn-hcc-lens 2 24)
                                                (fn-hcc-starts 1) (fn-hcc-pages 1 1))))))
              (fn-hpbp fn-hpb)
              (equal (fn-hpb-epoch fn-hpb) '(capture 7))
              (equal (fn-hpb-lease fn-hpb) '(lease 9))
              ; Mutation: unpadded total16 cannot replace exact payload24.
              (not (equal (fn-hpb-prefix fn-hpb) (append prior '(16))))) fn-hpb)))
   out)))
(assert-event (hcht-effect-tooth))

(defun hcht-full-tooth ()
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn-hpb
  (mv-let (out fn-hpb)
   (let* ((fn-hpb (fn-hpb-begin '(capture 7) '(lease 9) fn-hpb))
          (fn-hpb (hcht-fill 2048 fn-hpb))
          (prior (fn-hpb-prefix fn-hpb)))
    (mv-let (v fn-hpb) (fn-hch-tick 2 24 1 1 fn-hpb)
     (mv (and (equal v :done) (fn-hpb-ready fn-hpb)
              (equal (fn-hpb-prefix fn-hpb) prior)
              (equal prior (fn-hp-hdr2 2 (fn-hcc-lens 2 24)
                                       (fn-hcc-starts 1) (fn-hcc-pages 1 1)))
              (natp (fn-hpb-used fn-hpb))
              (not (< (fn-hpb-used fn-hpb) 2048))
              (not (and (equal v :stored)
                        (equal (fn-hpb-prefix fn-hpb) (append prior '(nil)))))) fn-hpb)))
   out)))
(assert-event (hcht-full-tooth))
