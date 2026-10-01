(in-package "ACL2")
(include-book "../../books/substrate-commit-profile-refinement")
(defconst *stcprt-profile* (fn-stcp-profile 100 10 1))
(defconst *stcprt-borrowed* (fn-stcp-decode-start *stcprt-profile* "A"))
; Full positive premise/conclusion, including cursor, work and result.
(defthm stcprt-resume-positive
 (and (stringp (fn-stcp-at 2 *stcprt-borrowed*))
      (equal (fn-stcp-dec-abstract (mv-nth 0 (fn-stcp-decode-resume *stcprt-profile* *stcprt-borrowed*)))
             (mv-nth 0 (fn-stcp-decode-resume *stcprt-profile* (fn-stcp-dec-abstract *stcprt-borrowed*))))
      (equal (mv-nth 1 (fn-stcp-decode-resume *stcprt-profile* *stcprt-borrowed*))
             (mv-nth 1 (fn-stcp-decode-resume *stcprt-profile* (fn-stcp-dec-abstract *stcprt-borrowed*))))
      (equal (fn-stcp-dec-result (mv-nth 0 (fn-stcp-decode-resume *stcprt-profile* *stcprt-borrowed*)))
             (fn-stcp-dec-result (mv-nth 0 (fn-stcp-decode-resume *stcprt-profile* (fn-stcp-dec-abstract *stcprt-borrowed*))))))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-stcp-decode-resume-borrowed-refinement
                         (p *stcprt-profile*) (c *stcprt-borrowed*)))
          :in-theory (disable fn-stcp-decode-resume fn-stcp-dec-abstract fn-stcp-dec-result))))
; Corrupted-state hypothesis-removal tooth: improper logical tail switches to
; a string after consumption. No remaining hypotheses in this theorem.
(defconst *stcprt-improper*
 (fn-stcp-dec-c :body 0 (cons 1 "A") 0 0 0 0 1 nil nil nil nil 0 nil))
(defthm stcprt-resume-without-borrowed-hypothesis-fails
 (and (not (stringp (fn-stcp-at 2 *stcprt-improper*)))
      (not (equal (fn-stcp-dec-abstract (mv-nth 0 (fn-stcp-decode-resume *stcprt-profile* *stcprt-improper*)))
                  (mv-nth 0 (fn-stcp-decode-resume *stcprt-profile* (fn-stcp-dec-abstract *stcprt-improper*))))))
 :rule-classes nil
 :hints (("Goal" :in-theory (enable fn-stcp-dec-abstract fn-stcp-source-abstract))))
