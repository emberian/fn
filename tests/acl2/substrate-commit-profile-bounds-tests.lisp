(in-package "ACL2")
(include-book "../../books/substrate-commit-profile-bounds")
(defconst *stcpbt-profile* (fn-stcp-profile 100 10 17))
(defconst *stcpbt-commit* (fn-me-commit '(1) 4294967296 '(2) :remove '(3)))
(defconst *stcpbt-wire* '(65 1 27 0 0 0 1 0 0 0 0 65 2 1 65 3))
; Full induction-keystone premises and conclusions, with reachable start states.
(assert-event
 (and (fn-stcp-enc-boundedp *stcpbt-profile* (fn-stcp-encode-start *stcpbt-profile* *stcpbt-commit*))
      (mv-let (c used) (fn-stcp-enc-drive *stcpbt-profile* (fn-stcp-encode-start *stcpbt-profile* *stcpbt-commit*) 1000)
       (declare (ignore used))
       (and (fn-stcp-enc-boundedp *stcpbt-profile* c)
            (equal (fn-stcp-enc-result c) (fn-stmt-ok *stcpbt-wire*))))))
(assert-event
 (and (fn-stcp-dec-boundedp *stcpbt-profile* (fn-stcp-decode-start *stcpbt-profile* *stcpbt-wire*))
      (mv-let (c used) (fn-stcp-dec-drive *stcpbt-profile* (fn-stcp-decode-start *stcpbt-profile* *stcpbt-wire*) 1000)
       (declare (ignore used))
       (and (fn-stcp-dec-boundedp *stcpbt-profile* c)
            (equal (fn-stcp-dec-result c) (fn-stmt-ok *stcpbt-commit*))))))
; Corrupted-state hypothesis-removal teeth. There are no retained hypotheses.
(defconst *stcpbt-bad-encoder*
 (fn-stcp-enc-c :done nil nil (+ 1 *fn-cbor-max-uint*) nil nil nil nil nil 0 nil))
(assert-event
 (and (not (fn-stcp-enc-boundedp *stcpbt-profile* *stcpbt-bad-encoder*))
      (mv-let (c used) (fn-stcp-enc-drive *stcpbt-profile* *stcpbt-bad-encoder* 17)
       (declare (ignore used)) (not (fn-stcp-enc-boundedp *stcpbt-profile* c)))))
(defconst *stcpbt-bad-decoder*
 (fn-stcp-dec-c :done 0 nil 0 0 0 (+ 1 *fn-cbor-max-uint64*) 0 nil nil nil nil 0 nil))
(assert-event
 (and (not (fn-stcp-dec-boundedp *stcpbt-profile* *stcpbt-bad-decoder*))
      (mv-let (c used) (fn-stcp-dec-drive *stcpbt-profile* *stcpbt-bad-decoder* 17)
       (declare (ignore used)) (not (fn-stcp-dec-boundedp *stcpbt-profile* c)))))
; Refusal paths stay in fixed native-width control bounds too.
(assert-event
 (mv-let (c used) (fn-stcp-dec-drive *stcpbt-profile*
                        (fn-stcp-decode-start *stcpbt-profile* '(255)) 17)
  (declare (ignore used))
  (and (fn-stcp-dec-boundedp *stcpbt-profile* c)
       (equal (fn-stcp-dec-result c) (fn-stmt-error :field)))))
