; Corrupted-credit-state witness: owner queue comes from real POST input,
; then an empty ledger is paired with it deliberately. This does not claim
; reachability through the complete native credit admission machine.
(in-package "ACL2")
(include-book "productive-read-chain-tests")
(include-book "../../books/productive-read-credit")

(defthm
  pcrc-queued-post-denied-read-corrupted-credit-state-positive
  (let*
    ((r0
       (fn-oas-read-span
         *pcrt-clocked-queued-selected*
         nil
         0
         0
         (len (append (fn-nntp-string-octets "ARTICLE 1") (quote (13 10))))
         nil
         (fn-otm-init)
         32
         (append (fn-nntp-string-octets "ARTICLE 1") (quote (13 10)))
         (list *pcrt-payload*)
         *pcrt-cat*))
      (r1
        (fn-mca-refused-read
          *pcrt-clocked-queued-selected*
          nil
          0
          0
          (len (append (fn-nntp-string-octets "ARTICLE 1") (quote (13 10))))
          nil
          (fn-otm-init)
          (append (fn-nntp-string-octets "ARTICLE 1") (quote (13 10)))
          (list *pcrt-payload*)
          *pcrt-cat*))
      (p
        (car
          (fn-mca-read-span
            (fn-mcr-make 0 0 0 0 0 0 nil)
            *pcrt-clocked-queued-selected*
            nil
            0
            0
            (len (append (fn-nntp-string-octets "ARTICLE 1") (quote (13 10))))
            nil
            (fn-otm-init)
            32
            107552
            (append (fn-nntp-string-octets "ARTICLE 1") (quote (13 10)))
            (list *pcrt-payload*)
            *pcrt-cat*))))
    (and
      (and
        (not
          (equal
            (car
              (fn-mcr-resize
                (fn-mcr-make 0 0 0 0 0 0 nil)
                (fn-mca-conn-key 0)
                (fn-mca-need (fn-own-tls-result-owner r0) 0 107552)))
            :ok))
        (not
          (equal
            (car
              (fn-mcr-resize
                (fn-mcr-make 0 0 0 0 0 0 nil)
                (fn-mca-conn-key 0)
                (fn-mca-need (fn-own-tls-result-owner r1) 0 107552)))
            :ok)))
      (and
        (equal
          (fn-own-queue (fn-ocfg-owner (fn-own-tls-result-owner p)))
          (fn-own-queue (fn-ocfg-owner *pcrt-clocked-queued-selected*)))
        (equal
          (fn-own-tls-result-effects p)
          (list (fn-nntp-reply-effect *fn-oas-busy-line*) (fn-nntp-close-effect)))
        (equal
          (fn-own-tls-result-consumed p)
          (- (len (append (fn-nntp-string-octets "ARTICLE 1") (quote (13 10)))) 0)))
      (consp (fn-own-queue (fn-ocfg-owner *pcrt-clocked-queued-selected*)))))
  :rule-classes
  nil)
