; Charged checkpoint incarnation pins, independent of logical view pins.
(in-package "ACL2")
(include-book "page-read-host")
(include-book "../books/page-file-lease")

(defun fn-owner-page-file-pin (file fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool))
  (if (not (equal (fn-owner-page-read-direct-mode fn-page-read-pool) :funded-pool))
      (mv :read-resources-unavailable nil fn-page-read-pool)
    (let* ((ledger (fn-owner-page-read-ledger fn-page-read-pool))
           (bookkeeping (+ (nfix (fn-prl-nth 1 (fn-prp-data fn-page-read-pool)))
                           (fn-crl-token-integer-octets (fn-prl-nth 2 ledger) 0 file 0 0 0))))
      (mv-let (word token ledger1)
        (fn-prf-acquire ledger file (list (* 2 bookkeeping) 0 1 0 1))
        (let ((fn-page-read-pool (fn-owner-page-read-keep-ledger ledger1 fn-page-read-pool)))
          (mv word token fn-page-read-pool))))))

(defun fn-owner-page-file-pin-file (token fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool))
  (fn-prf-file (fn-owner-page-read-ledger fn-page-read-pool) token))

(defun fn-owner-page-file-unpin (token fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool))
  (mv-let (word ledger)
    (fn-prf-release (fn-owner-page-read-ledger fn-page-read-pool) token)
    (let ((fn-page-read-pool (fn-owner-page-read-keep-ledger ledger fn-page-read-pool)))
      (mv word fn-page-read-pool))))

(defthm fn-owner-page-file-unpin-refines-prf-by-definition
  (equal (mv-list 2 (fn-owner-page-file-unpin token fn-page-read-pool))
         (list (mv-nth 0 (fn-prf-release (fn-owner-page-read-ledger fn-page-read-pool) token))
               (fn-owner-page-read-keep-ledger
                (mv-nth 1 (fn-prf-release (fn-owner-page-read-ledger fn-page-read-pool) token))
                fn-page-read-pool))))

; The caller supplies only observed file base and an immutable core request.
; A separate discovery lease owns the raw page while the auth cursor borrows it.
(defun fn-owner-page-file-pin-read (token request base fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool))
  (mv-let (word file offset count)
    (fn-prf-page-placement (fn-owner-page-read-ledger fn-page-read-pool) token request base)
    (if (not (equal word :placed)) (mv word nil 0 0 nil fn-page-read-pool)
      (mv-let (admit buffer-token fn-page-read-pool)
        (fn-owner-page-read-discovery-admit file offset count fn-page-read-pool)
        (if (not (eq admit :admitted))
            (mv admit file offset count buffer-token fn-page-read-pool)
          (mv-let (recorded ledger)
            (fn-prf-note-admitted-read (fn-owner-page-read-ledger fn-page-read-pool)
                                       token request buffer-token)
            (let ((fn-page-read-pool (fn-owner-page-read-keep-ledger ledger fn-page-read-pool)))
              (mv (if (eq recorded :recorded) :admitted :read-admission-uncertain)
                  file offset count buffer-token fn-page-read-pool))))))))

(defthm fn-owner-page-file-pin-refines-prf-by-definition
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

(defun fn-owner-page-file-read-result (root request base buffer-token got io-status fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool))
  (fn-prf-read-result (fn-owner-page-read-ledger fn-page-read-pool)
                      root request base buffer-token got io-status))

(defun fn-owner-page-file-pin-ticket (token fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool))
  (fn-prf-ticket (fn-owner-page-read-ledger fn-page-read-pool) token))

(defun fn-owner-page-file-issued-count (root fn-page-read-pool)
  (declare (xargs :stobjs fn-page-read-pool))
  (fn-prf-issued-count (fn-owner-page-read-ledger fn-page-read-pool) root))
