; Closed witnesses for the candidate-priced memory configuration.
(in-package "ACL2")
(include-book "../../host/owner-host")
(defconst *pb-p* (update-nth *fn-bs-pf-max-article-octets* 1 *fn-bs-profile-development*))

; Witnesses: only path-identity differs; source header limits stay the same.
(defconst *pb-v1* (fn-cfg-value-make nil 2 nil '(("path-identity" "a.invalid" "" 0)) nil nil nil nil nil nil))
(defconst *pb-v2* (fn-cfg-value-make nil 2 nil '(("path-identity" "longer.invalid" "" 0)) nil nil nil nil nil nil))
(defconst *pb-limits* (fn-article-limits 10 20 1000))
(assert-event (equal (fn-mm-cfg-header-octets
                     (fn-owner-memory-cfg *pb-v1* nil 0 0 nil nil *pb-p* 123 '(1 2 3) 0)) 123))
(defconst *pb-m1* (fn-owner-memory-cfg-of *pb-v1* nil 0 0 nil nil *pb-p* *pb-limits* 0))
(defconst *pb-m2* (fn-owner-memory-cfg-of *pb-v2* nil 0 0 nil nil *pb-p* *pb-limits* 0))
(assert-event (and (equal (fn-mm-cfg-header-octets *pb-m1*)
                          (nfix (fn-article-limit-octets (fn-o1-stored-header-limits *pb-limits* (fn-oag-agent (fn-cfg-make 0 *pb-v1*))))))
                   (equal (fn-mm-cfg-server-octets *pb-m1*) (len (fn-oag-agent (fn-cfg-make 0 *pb-v1*))))))
(assert-event (and (equal (fn-mm-cfg-header-octets *pb-m2*)
                          (nfix (fn-article-limit-octets (fn-o1-stored-header-limits *pb-limits* (fn-oag-agent (fn-cfg-make 0 *pb-v2*))))))
                   (equal (fn-mm-cfg-server-octets *pb-m2*) (len (fn-oag-agent (fn-cfg-make 0 *pb-v2*))))))
(assert-event (and (not (equal (fn-mm-cfg-header-octets *pb-m1*) (fn-mm-cfg-header-octets *pb-m2*)))
                   (not (equal (fn-mm-cfg-server-octets *pb-m1*) (fn-mm-cfg-server-octets *pb-m2*)))))

; The direct constructor's header lemma at the two candidate-specific HDRs.
(assert-event
 (let ((agent (fn-oag-agent (fn-cfg-make 0 *pb-v1*))))
   (equal (fn-mm-cfg-header-octets
           (fn-owner-memory-cfg *pb-v1* nil 0 0 nil nil *pb-p*
                                (fn-article-limit-octets (fn-o1-stored-header-limits *pb-limits* agent)) agent 0))
          (nfix (fn-article-limit-octets (fn-o1-stored-header-limits *pb-limits* agent))))))
(assert-event
 (let ((agent (fn-oag-agent (fn-cfg-make 0 *pb-v2*))))
   (equal (fn-mm-cfg-header-octets
           (fn-owner-memory-cfg *pb-v2* nil 0 0 nil nil *pb-p*
                                (fn-article-limit-octets (fn-o1-stored-header-limits *pb-limits* agent)) agent 0))
          (nfix (fn-article-limit-octets (fn-o1-stored-header-limits *pb-limits* agent))))))
