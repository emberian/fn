; B-verified and pinned run page -> exact inline Message-ID lookup.
; Caller verifies the page's parent-held physical hash/identity through
; fn2-format-check-page once, then retains its immutable range until done.
(in-package "ACL2")
(include-book "seal")
(defun fn2-sc-page-entry-lookup (qslot qgen qoff qlen slot gen row count dir
                                okind oslot ogen fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-fields fn2-pool) :verify-guards nil))
 (b* (((when (>= (nfix row) (nfix count))) (mv :absent row 0 fn2-fields))
      ((mv code next fn2-fields)
       (fn2-layout-decode *fn2-sc-run-offset* slot gen (+ dir (* 4 row))
                         (+ dir (* 4 (+ row 1))) okind oslot ogen fn2-fields fn2-pool))
      (- next)
      ((unless (eq code :ok)) (mv code row 0 fn2-fields))
      (offset (fn2-fields-value 0 fn2-fields))
      ((unless (and (<= 73 offset) (< offset dir))) (mv :offset row 0 fn2-fields))
      ((mv code next fn2-fields)
       ; The generic decoder's 4096-byte quantum would exceed this call's
       ; combined budget on a malformed unterminated varint. Constrain both
       ; its range and its work to the schema's maximum canonical size.
       (fn2-layout-decode-run *fn2-sc-run-entry* slot gen offset
        (min dir (+ offset (fn2-layout-max-size *fn2-sc-run-entry*))) okind oslot ogen
        (fn2-layout-max-size *fn2-sc-run-entry*) nil fn2-fields fn2-pool))
      (- next)
      (code (if (eq code :more) :malformed-entry code))
      ((unless (eq code :ok)) (mv code row 0 fn2-fields))
      (tag (fn2-fields-value 2 fn2-fields))
      ((unless (= qlen (fn2-fields-ref-len 3 fn2-fields))) (mv :different row tag fn2-fields))
      ((mv code work)
       (fn2-sc-compare qslot qgen qoff (fn2-fields-ref-slot 3 fn2-fields)
        (fn2-fields-ref-gen 3 fn2-fields) (fn2-fields-ref-off 3 fn2-fields)
        qlen okind oslot ogen fn2-pool))
      (- work))
  (mv (if (eq code :equal) :found code) row tag fn2-fields)))
(defun fn2-sc-page-lookup-loop (qslot qgen qoff qlen slot gen row count dir fuel
                               okind oslot ogen fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-fields fn2-pool) :verify-guards nil :measure (nfix fuel)))
 (cond ((>= (nfix row) (nfix count)) (mv :absent 0 row 0 fn2-fields))
       ((zp fuel) (mv :yield 0 row 0 fn2-fields))
       (t (mv-let (code found tag fn2-fields)
           (fn2-sc-page-entry-lookup qslot qgen qoff qlen slot gen row count dir
                                     okind oslot ogen fn2-fields fn2-pool)
           (if (eq code :different)
               (fn2-sc-page-lookup-loop qslot qgen qoff qlen slot gen (+ 1 (nfix row)) count dir
                                         (- fuel 1) okind oslot ogen fn2-fields fn2-pool)
            (mv code found (+ 1 (nfix row)) tag fn2-fields))))))
(defun fn2-sc-page-lookup (qslot qgen qoff qlen slot gen start fuel
                          okind oslot ogen fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-fields fn2-pool) :verify-guards nil))
 (b* (((unless (and (unsigned-byte-p 32 start) (natp fuel) (posp qlen) (<= qlen 250)
                    (unsigned-byte-p 32 qoff))) (mv :bounds 0 start 0 fn2-fields))
      (code (fn2-layout-range-code qslot qgen qoff (+ qoff qlen) nil okind oslot ogen fn2-pool))
      ((unless (eq code :ok)) (mv code 0 start 0 fn2-fields))
      ((mv code next fn2-fields)
       (fn2-layout-decode *fn2-sc-run-header* slot gen 64 73 okind oslot ogen fn2-fields fn2-pool))
      (- next)
      ((unless (eq code :ok)) (mv code 0 start 0 fn2-fields))
      (count (fn2-fields-value 1 fn2-fields))
      (dir (fn2-fields-value 2 fn2-fields))
      ((unless (= (fn2-fields-value 0 fn2-fields) 1)) (mv :schema 0 start 0 fn2-fields))
      ((unless (and (<= 73 dir) (<= (+ dir (* 4 count)) 65536))) (mv :directory 0 start 0 fn2-fields)))
  ; Header 9 B + <=4*(directory4 + record297 + compare500) <4096 reads.
  ; Entry fuel is also below the simultaneous 32 structural-step cap.
  (fn2-sc-page-lookup-loop qslot qgen qoff qlen slot gen start count dir (min 4 fuel)
                           okind oslot ogen fn2-fields fn2-pool)))
