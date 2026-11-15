; Independent CNS source-owner wake and alias-query completion frames.
; The exact lookup scratch carriers are explicit; owned pool/query rows,
; all machine state and every other core child have prescribed effects.
(in-package "ACL2")
(include-book "cns-draining-model")

(defun fn2-cns-query-owner-livep (kind owner generation before)
  (let* ((dir (fn2-cns-drain-child 'fn2-machines before))
         (own (fn2-cns-drain-child 'fn2-cns before))
         (slot (fn2-cns-drain-cell 'fn2-machines-slot owner dir)))
    (and (equal kind *fn2-cns-kind*)
         (natp owner) (< owner (fn2-cns-drain-get 'fn2-machines-rows dir))
         (equal (fn2-cns-drain-cell 'fn2-machines-kind owner dir) kind)
         (natp slot) (< slot (fn2-cns-drain-get 'fn2-cns-rows own))
         (equal (fn2-cns-drain-cell 'fn2-cns-generation slot own) generation)
         (not (member-equal (fn2-cns-drain-cell 'fn2-cns-phase slot own)
                            (list *fn2-cns-state-free* *fn2-cns-state-retired*)))
         (equal (fn2-cns-drain-cell 'fn2-cns-stopped slot own) 0))))

(defun fn2-cns-query-carry-children (names after before)
  (if (atom names) before
    (fn2-cns-query-carry-children (cdr names) after
      (fn2-cns-drain-put-child (car names)
        (fn2-cns-drain-child (car names) after) before))))

; Concrete empty-index query slice: both descriptors reference SOURCE.
; Closing one query removes exactly two refs and stores its scalar DONE
; result. Other queries, all bytes, ownership and I/O borrows are framed.
; Lookup may change only its named scratch carriers; this is not a claim
; that these carriers' lookup semantics have been independently specified.
(defun fn2-cns-query-alias-done-framep (tx source before after)
  (let* ((queries (fn2-cns-drain-child 'fn2-id-decides before))
         (pool (fn2-cns-drain-child 'fn2-pool before))
         (dir (fn2-cns-drain-child 'fn2-machines before))
         (count (fn2-cns-drain-cell 'fn2-pool-query-ref-count source pool))
         (owner (fn2-cns-drain-cell 'fn2-id-decides-qs tx queries))
         (last (equal count 2))
         (live (fn2-cns-query-owner-livep
                 (fn2-cns-drain-cell 'fn2-id-decides-qk tx queries) owner
                 (fn2-cns-drain-cell 'fn2-id-decides-qg tx queries) before))
         (queries (fn2-cns-drain-put-cells
                    (list (list 'fn2-id-decides-phase *fn2-id-decide-phase-done*)
                          (list 'fn2-id-decides-qmask 0) (list 'fn2-id-decides-qwake 0)) tx queries))
         (pool (fn2-cns-drain-put-cell 'fn2-pool-query-ref-count source (- count 2) pool))
         (dir (if (and last live)
                  (fn2-cns-drain-put 'fn2-machines-wake-id owner dir) dir))
         (expected (fn2-cns-query-carry-children
                     '(fn2-succ-txns fn2-run-cursors fn2-run-paths fn2-fields) after before))
         (expected (fn2-cns-drain-put-child 'fn2-pool pool
                     (fn2-cns-drain-put-child 'fn2-id-decides queries
                       (fn2-cns-drain-put-child 'fn2-machines dir expected)))))
    (and (natp count) (<= 2 count) (equal after expected))))
