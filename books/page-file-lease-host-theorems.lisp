; Moved from host/page-file-lease-host.lisp by tools/host_theorems.py; this book is their source now.
; They only restate that host book's definitions, which it keeps.
(in-package "ACL2")
(include-book "../host/page-file-lease-host")

(defthm fn-owner-page-file-pin-refines-prf-by-definition
  (implies (fn-owner-page-file-legacy-writablep fn-page-read-pool)
         (equal (mv-list 3 (fn-owner-page-file-pin file fn-page-read-pool))
         (if (not (equal (fn-owner-page-read-direct-mode fn-page-read-pool) :funded-pool))
             (list :read-resources-unavailable nil fn-page-read-pool)
           (let* ((ledger (fn-owner-page-read-ledger fn-page-read-pool))
                  (bookkeeping (+ (nfix (fn-prl-nth 1 (fn-prp-data fn-page-read-pool)))
                                  (fn-crl-token-integer-octets (fn-prl-nth 2 ledger) 0 file 0 0 0)))
                  (demand (list (* 2 bookkeeping) 0 1 0 1)))
             (list (mv-nth 0 (fn-prf-acquire ledger file demand))
                   (mv-nth 1 (fn-prf-acquire ledger file demand))
                   (fn-owner-page-read-keep-ledger
                    (mv-nth 2 (fn-prf-acquire ledger file demand)) fn-page-read-pool))))))
  :hints (("Goal" :in-theory '(fn-owner-page-file-pin mv-list mv-nth nth
                               (:executable-counterpart binary-+)
                               (:executable-counterpart zp))
           :expand ((:free (x) (mv-nth 1 x)) (:free (x) (mv-nth 2 x))
                    (:free (x) (nth 1 x)) (:free (x) (nth 2 x))))))
