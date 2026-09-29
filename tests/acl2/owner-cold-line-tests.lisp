; Teeth for books/owner-cold-line.lisp (PRF-933, lane composed-owner-3):
; KEYSTONE fn-ocln-a-cold-line-is-answered-unavailable on the host's call,
; fn-ocln-unavailable-span, over a reached owner (owner-time-model-tests'
; *t2r-open*, the finished log's owner with posting on for connection 0).

(in-package "ACL2")
(include-book "../../books/owner-cold-line")
(include-book "owner-time-model-tests")
(include-book "must-fail-checked")

(defun oclnt-span (oc id octs since now limit)
  (declare (xargs :mode :program))
  (with-local-stobj fn-octets
    (mv-let (result fn-octets)
      (let ((fn-octets (fn-octets-from-list octs fn-octets)))
        (mv (fn-ocln-unavailable-span oc id 0 since now limit fn-octets) fn-octets))
      result)))

(defun oclnt-line (s) (append (fn-nntp-string-octets s) '(13 10)))
(defun oclnt-owner (r) (fn-own-tls-result-owner r))
(defun oclnt-conn (oc id) (fn-own-find-conn id (fn-own-conns (fn-ocfg-owner oc))))

(defconst *oclnt-l1* (oclnt-line "GROUP fn.letters"))
(defconst *oclnt-l2* (oclnt-line "ARTICLE 1"))
(defconst *oclnt-l3* (oclnt-line "STAT 1"))

; POSITIVE WITNESS, pipelined (RFC 3977 section 3.5): line 1 warm, line 2
; cold past its deadline (waited 5,200 ms of 5,000), line 3 warm.  Every
; conjunct of the keystone on line 2: the connection is in command mode
; (antecedent), the whole line and no more is consumed, one reply, 403, the
; owner is the line-start owner -- and here, the wire already at a line's
; start, EXACTLY the owner before the line (session unchanged).  Line 3's
; read from the owner after the 403 is line 3's read from the owner after
; line 1: the later line proceeds as if the cold one had only been answered.
(defconst *oclnt-r1* (t2r-host-read *t2r-open* *orrt-views* 0 *oclnt-l1* *t2-s1*))
(defconst *oclnt-oc1* (oclnt-owner *oclnt-r1*))
(defconst *oclnt-r2* (oclnt-span *oclnt-oc1* 0 (append *oclnt-l2* *oclnt-l3*) 100 5300 nil))
(defconst *oclnt-r3* (t2r-host-read (oclnt-owner *oclnt-r2*) *orrt-views* 0 *oclnt-l3* *t2-s1*))
(defconst *oclnt-r3-direct* (t2r-host-read *oclnt-oc1* *orrt-views* 0 *oclnt-l3* *t2-s1*))

(defun oclnt-code (r)
  (declare (xargs :mode :program))
  (let ((reply (cadr (car (fn-own-tls-result-effects r)))))
    (list (nth 0 reply) (nth 1 reply) (nth 2 reply))))

(assert-event (fn-ocln-commandp *oclnt-oc1* 0))
(assert-event (equal (fn-own-conn-wire (oclnt-conn *oclnt-oc1* 0))
                     (fn-ocln-line-state (fn-own-conn-wire (oclnt-conn *oclnt-oc1* 0)))))
(assert-event (equal (fn-own-tls-result-consumed *oclnt-r2*) (len *oclnt-l2*)))
(assert-event (equal (len (fn-own-tls-result-effects *oclnt-r2*)) 1))
(assert-event (equal (fn-own-tls-result-effects *oclnt-r2*)
                     (list (list :reply (fn-otb-unavailable-line 100 5300 nil)))))
(assert-event (equal (oclnt-code *oclnt-r2*) '(52 48 51)))
(assert-event (equal (fn-otb-dependency-step 100 5300 nil nil) :unavailable))
(assert-event (equal (oclnt-owner *oclnt-r2*) *oclnt-oc1*))
(assert-event (equal *oclnt-r3* *oclnt-r3-direct*))
(assert-event (consp (fn-own-tls-result-effects *oclnt-r3*)))

; POSITIVE WITNESS, a line split across reads: "GROUP fn.let" arrived in one
; read (the wire holds 12 octets of a line), "ters" CRLF in the next, which
; is cold past its deadline.  The whole line is consumed from the second
; read (6 octets), the wire returns to a line's start, the session is the
; one before the line, and the next command is answered exactly as it is
; from the owner that never saw the line.
(defconst *oclnt-rp* (t2r-host-read *t2r-open* *orrt-views* 0
                                    (fn-nntp-string-octets "GROUP fn.let") *t2-s1*))
(defconst *oclnt-ocp* (oclnt-owner *oclnt-rp*))
(defconst *oclnt-r2p* (oclnt-span *oclnt-ocp* 0 (append (oclnt-line "ters") *oclnt-l3*) 0 9000 nil))
(defconst *oclnt-r3p* (t2r-host-read (oclnt-owner *oclnt-r2p*) *orrt-views* 0 *oclnt-l3* *t2-s1*))
(defconst *oclnt-r3o* (t2r-host-read *t2r-open* *orrt-views* 0 *oclnt-l3* *t2-s1*))
(assert-event (fn-ocln-commandp *oclnt-ocp* 0))
(assert-event (equal (fn-wire-state-line-len (fn-own-conn-wire (oclnt-conn *oclnt-ocp* 0))) 12))
(assert-event (equal (fn-own-tls-result-consumed *oclnt-r2p*) 6))
(assert-event (equal (oclnt-code *oclnt-r2p*) '(52 48 51)))
(assert-event (equal (fn-own-conn-wire (oclnt-conn (oclnt-owner *oclnt-r2p*) 0))
                     (fn-ocln-line-state (fn-own-conn-wire (oclnt-conn *oclnt-ocp* 0)))))
(assert-event (not (equal (oclnt-owner *oclnt-r2p*) *oclnt-ocp*)))
(assert-event (equal (fn-own-conn-session (oclnt-conn (oclnt-owner *oclnt-r2p*) 0))
                     (fn-own-conn-session (oclnt-conn *oclnt-ocp* 0))))
(assert-event (equal (fn-own-tls-result-effects *oclnt-r3p*)
                     (fn-own-tls-result-effects *oclnt-r3o*)))
(assert-event (equal (oclnt-owner *oclnt-r3p*) (oclnt-owner *oclnt-r3o*)))

; HYPOTHESIS-REMOVAL WITNESS (fn-ocln-commandp omitted).  Connection 0 after
; its admitted POST (*t2r-open-admit*) is in article mode.  The retained
; hypotheses hold (I = 0 within the buffer), the omitted one fails, and the
; conclusion fails: nothing is answered, no line consumed (the result is nil).
(defconst *oclnt-oa* (oclnt-owner *t2r-open-admit*))
(defconst *oclnt-ra* (oclnt-span *oclnt-oa* 0 *oclnt-l2* 0 9000 nil))
(assert-event (natp 0))
(assert-event (not (fn-ocln-commandp *oclnt-oa* 0)))
(assert-event (equal (fn-wire-state-mode (fn-own-conn-wire (oclnt-conn *oclnt-oa* 0))) :article))
(assert-event (equal *oclnt-ra* nil))
(assert-event (not (equal (fn-own-tls-result-consumed *oclnt-ra*) (len *oclnt-l2*))))

; MUTATION: a keystone that claimed the whole buffer is consumed (the lines
; after the cold one dropped) is refuted by the pipelined witness.
(must-fail-checked
 (defthm oclnt-mutation-whole-buffer
   (implies (and (natp i) (<= i (fn-octets-len fn-octets)) (fn-ocln-commandp oc id))
            (equal (fn-own-tls-result-consumed
                    (fn-ocln-unavailable-span oc id i since now limit fn-octets))
                   (- (fn-octets-len fn-octets) i)))))
(assert-event (not (equal (fn-own-tls-result-consumed *oclnt-r2*)
                          (len (append *oclnt-l2* *oclnt-l3*)))))
