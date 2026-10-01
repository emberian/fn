(in-package "ACL2")
(include-book "../../books/substrate-commit-profile-resume")
(defconst *stcpat-profile* (fn-stcp-profile 100 10 17))
(defconst *stcpat-commit* (fn-me-commit '(1) 4294967296 '(2) :remove '(3)))
(defconst *stcpat-wire* '(65 1 27 0 0 0 1 0 0 0 0 65 2 1 65 3))
; Literal complete conditional-induction statement at a reachable start.
(assert-event
 (mv-let (a au) (fn-stcp-enc-drive-acc *stcpat-profile* (fn-stcp-encode-start *stcpat-profile* *stcpat-commit*) 1000 0)
  (mv-let (r ru) (fn-stcp-enc-drive *stcpat-profile* (fn-stcp-encode-start *stcpat-profile* *stcpat-commit*) 1000)
   (and (equal a r) (acl2-numberp 0) (equal au (+ 0 ru))
        (equal (fn-stcp-enc-result a) (fn-stmt-ok *stcpat-wire*))))))
(assert-event
 (mv-let (a au) (fn-stcp-dec-drive-acc *stcpat-profile* (fn-stcp-decode-start *stcpat-profile* *stcpat-wire*) 1000 0)
  (mv-let (r ru) (fn-stcp-dec-drive *stcpat-profile* (fn-stcp-decode-start *stcpat-profile* *stcpat-wire*) 1000)
   (and (equal a r) (acl2-numberp 0) (equal au (+ 0 ru))
        (equal (fn-stcp-dec-result a) (fn-stmt-ok *stcpat-commit*))))))
; Corrupted-state logical witnesses: omitted numerical accumulator premise.
; The retained unconditional cursor equality holds, count equality fails.
(defthm stcpat-encoder-without-number-premise-fails
 (and (not (acl2-numberp :bad))
      (equal (mv-nth 0 (fn-stcp-enc-drive-acc nil '(:done) 17 :bad))
             (mv-nth 0 (fn-stcp-enc-drive nil '(:done) 17)))
      (not (equal (mv-nth 1 (fn-stcp-enc-drive-acc nil '(:done) 17 :bad))
                   (+ :bad (mv-nth 1 (fn-stcp-enc-drive nil '(:done) 17))))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-stcp-enc-drive-acc fn-stcp-enc-drive))))
(defthm stcpat-decoder-without-number-premise-fails
 (and (not (acl2-numberp :bad))
      (equal (mv-nth 0 (fn-stcp-dec-drive-acc nil '(:done) 17 :bad))
             (mv-nth 0 (fn-stcp-dec-drive nil '(:done) 17)))
      (not (equal (mv-nth 1 (fn-stcp-dec-drive-acc nil '(:done) 17 :bad))
                   (+ :bad (mv-nth 1 (fn-stcp-dec-drive nil '(:done) 17))))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-stcp-dec-drive-acc fn-stcp-dec-drive))))
; Actual resume wrappers always initialize the accumulator at zero.
(assert-event
 (mv-let (a au) (fn-stcp-encode-resume-acc *stcpat-profile* (fn-stcp-encode-start *stcpat-profile* *stcpat-commit*))
  (mv-let (r ru) (fn-stcp-encode-resume *stcpat-profile* (fn-stcp-encode-start *stcpat-profile* *stcpat-commit*))
   (and (equal a r) (equal au ru) (<= au 17)))))
(assert-event
 (mv-let (a au) (fn-stcp-decode-resume-acc *stcpat-profile* (fn-stcp-decode-start *stcpat-profile* *stcpat-wire*))
  (mv-let (r ru) (fn-stcp-decode-resume *stcpat-profile* (fn-stcp-decode-start *stcpat-profile* *stcpat-wire*))
   (and (equal a r) (equal au ru) (<= au 17)))))
