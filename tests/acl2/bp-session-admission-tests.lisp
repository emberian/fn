; One explicitly configured loopback boundary.  Every co-resident process is
; named in this profile; a claimed TCPCL EID cannot create a principal alone.
(in-package "ACL2")
(include-book "../../books/bp-session-admission")

(defconst *bpat-eid* (cons :dtn (fn-record-string-octets "//peer/")))
(defconst *bpat-other-eid* (cons :dtn (fn-record-string-octets "//other/")))
(defconst *bpat-channel* (list :tcp4 '(127 0 0 1) 4556 '(127 0 0 1)))
(defconst *bpat-rows*
  (list (fn-cfg-row-make "peer" "transport-bp" "dtn://peer/" 0)
        (fn-cfg-row-make "peer" "bp-trust" "network" 0)
        (fn-cfg-row-make "peer" "bp-boundary-listener" "127.0.0.1" 4556)
        (fn-cfg-row-make "peer" "bp-boundary-source" "127.0.0.1" 0)
        (fn-cfg-row-make "peer" "bp-boundary-translation" "none" 0)
        (fn-cfg-row-make "peer" "bp-boundary-originators"
                         "all-co-resident" 0)))
(defconst *bpat-cfg*
  (fn-cfg-make 7 (fn-cfg-value-make nil 0 nil nil nil *bpat-rows* nil)))
(defconst *bpat-no-trust*
  (fn-cfg-make 7 (fn-cfg-value-make nil 0 nil nil nil
                                  (cons (car *bpat-rows*)
                                        (cddr *bpat-rows*)) nil)))

(assert-event (fn-cfgp *bpat-cfg*))
(assert-event (fn-bpp-eidp *bpat-eid*))
(assert-event
 (equal (fn-bpaj-session-principal *bpat-cfg* *bpat-channel* *bpat-eid*)
        (list :admitted (fn-record-string-octets "peer") 7)))
(assert-event
 (equal (fn-bpaj-admitted-principal
         (fn-bpaj-session-principal *bpat-cfg* *bpat-channel* *bpat-other-eid*))
        nil))
(assert-event
 (equal (fn-bpaj-admitted-principal
         (fn-bpaj-session-principal *bpat-no-trust* *bpat-channel* *bpat-eid*))
        nil))
(assert-event
 (equal (fn-bpaj-admitted-principal
         (fn-bpaj-session-principal
          *bpat-cfg* (list :tcp4 '(127 0 0 1) 4556 '(127 0 0 2))
          *bpat-eid*))
        nil))
(assert-event
 (equal (fn-bpaj-admitted-principal
         (fn-bpaj-session-principal
          (fn-cfg-make 7
            (fn-cfg-value-make nil 0 nil nil nil
              (cons (fn-cfg-row-make "peer" "bp-trust" "network" 0)
                    *bpat-rows*) nil))
          *bpat-channel* *bpat-eid*))
        nil))
; An announced EID cannot disambiguate two profiles on one observed channel.
(assert-event
 (equal (fn-bpaj-admitted-principal
         (fn-bpaj-session-principal
          (fn-cfg-make 7
            (fn-cfg-value-make nil 0 nil nil nil
              (append *bpat-rows*
                (list (fn-cfg-row-make "other" "transport-bp" "dtn://other/" 0)
                      (fn-cfg-row-make "other" "bp-trust" "network" 0)
                      (fn-cfg-row-make "other" "bp-boundary-listener"
                                       "127.0.0.1" 4556)
                      (fn-cfg-row-make "other" "bp-boundary-source"
                                       "127.0.0.1" 0)
                      (fn-cfg-row-make "other" "bp-boundary-translation"
                                       "none" 0)
                      (fn-cfg-row-make "other" "bp-boundary-originators"
                                       "all-co-resident" 0))) nil))
          *bpat-channel* *bpat-eid*))
        nil))
(assert-event
 (equal (fn-bpaj-admitted-principal
         (fn-bpaj-session-principal
          (fn-cfg-make 7
            (fn-cfg-value-make nil 0 nil nil nil
              (append *bpat-rows*
                (list (fn-cfg-row-make "other" "transport-bp" "dtn://peer/" 0)
                      (fn-cfg-row-make "other" "bp-trust" "network" 0)
                      (fn-cfg-row-make "other" "bp-boundary-listener"
                                       "127.0.0.1" 4556)
                      (fn-cfg-row-make "other" "bp-boundary-source"
                                       "127.0.0.1" 0)
                      (fn-cfg-row-make "other" "bp-boundary-translation"
                                       "none" 0)
                      (fn-cfg-row-make "other" "bp-boundary-originators"
                                       "all-co-resident" 0))) nil))
          *bpat-channel* *bpat-eid*))
        nil))
