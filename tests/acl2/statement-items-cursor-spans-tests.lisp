(in-package "ACL2")
(include-book "../../books/statement-items-cursor-spans")
; Reachable paid success, full source geometry and byte-domain conclusion.
(assert-event
 (let* ((source '(66 9 10 1))
        (c (fn-sic-begin 2 source 4 2))
        (d (fn-sic-run (fn-sic-completion-cost c) c))
        (item (car (fn-stmt-value (fn-sic-result d)))))
  (and (natp 2) (natp 4) (fn-stmt-okp (fn-sic-result d))
       (equal (fn-sic-result d) '(:ok ((:bytes 1 2 (9 10 1)) (:uint . 1))))
       (fn-sic-span-item-listp (fn-stmt-value (fn-sic-result d)) source)
       (fn-cbor-octet-listp source)
       (fn-sic-span-itemp item source)
       (equal (fn-cbor-ag-car item) :bytes)
       (natp 1) (< 1 (fn-sic-at 2 item))
       (equal (car (nthcdr 1 (fn-sic-at 3 item))) 10)
       (fn-cbor-octetp (car (nthcdr 1 (fn-sic-at 3 item)))))))
; Corrupted-source witness: every byte theorem premise except source domain.
(assert-event
 (let ((item '(:bytes 0 1 (256))) (source '(256)))
  (and (fn-sic-span-itemp item source)
       (equal (fn-cbor-ag-car item) :bytes)
       (natp 0) (< 0 (fn-sic-at 2 item))
       (not (fn-cbor-octet-listp source))
       (not (fn-cbor-octetp (car (nthcdr 0 (fn-sic-at 3 item))))))))
; Corrupted-descriptor witness: exact source provenance is necessary.
(assert-event
 (let ((item '(:bytes 0 1 (256))) (source '(1)))
  (and (equal (fn-cbor-ag-car item) :bytes)
       (fn-cbor-octet-listp source) (natp 0) (< 0 (fn-sic-at 2 item))
       (not (fn-sic-span-itemp item source))
       (not (fn-cbor-octetp (car (nthcdr 0 (fn-sic-at 3 item))))))))
; Boundary-removal witness: borrowed tail includes subsequent wire bytes.
(assert-event
 (let ((item '(:bytes 0 1 (1))) (source '(1)))
  (and (fn-sic-span-itemp item source)
       (equal (fn-cbor-ag-car item) :bytes)
       (fn-cbor-octet-listp source) (natp 1)
       (not (< 1 (fn-sic-at 2 item)))
       (not (fn-cbor-octetp (car (nthcdr 1 (fn-sic-at 3 item))))))))
; Resuming at a partial payload returns identical borrowed descriptors.
(assert-event
 (let* ((source '(66 9 10 1)) (c (fn-sic-begin 2 source 4 2))
        (q (fn-sic-completion-cost c)))
  (and (<= 6 q)
       (equal (fn-sic-run q c)
              (fn-sic-run (- q 6) (fn-sic-run 6 c))))))
