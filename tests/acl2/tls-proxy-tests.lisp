; Teeth for books/tls-proxy.lisp (PRF-986 item 4, lane tls-handshake-budget-3):
; the PROXY header on a trusted path only.  For each keystone: a reached
; positive witness asserting its antecedent and conclusion, and a must-fail
; where the antecedent is dropped and the conclusion fails.

(in-package "ACL2")
(include-book "../../books/tls-proxy")
(include-book "must-fail-checked")

(defmacro pxt-octets (s) `(fn-record-string-octets ,s))
(defconst *pxt-crlf* '(13 10))
(defconst *pxt-peers* (fn-exp-trusted-of-word "10.0.0.0/8,fd00::/8"))
(defconst *pxt-proxy* '(:inet 10 1 2 3))
(defconst *pxt-mapped-proxy* '(:inet6 0 0 0 0 0 0 0 0 0 0 255 255 10 1 2 3))
(defconst *pxt-public* '(:inet 192 0 2 1))

; --- KEYSTONE fn-pxy-direct-unless-trusted.
; Witness: the proxy (and its IPv4-mapped form) is read, WHY a listed
; matching range.
(assert-event (equal (fn-pxy-begin *pxt-proxy* *pxt-peers*)
                     (list :read 6 (car *pxt-peers*))))
(assert-event (equal (fn-pxy-begin *pxt-mapped-proxy* *pxt-peers*)
                     (list :read 6 (car *pxt-peers*))))
(assert-event (member-equal (caddr (fn-pxy-begin *pxt-proxy* *pxt-peers*)) *pxt-peers*))
(assert-event (fn-exp-cidr-matchp (caddr (fn-pxy-begin *pxt-proxy* *pxt-peers*)) *pxt-proxy*))
; A public peer is direct: nothing is read, whatever it would send.
(assert-event (equal (fn-pxy-begin *pxt-public* *pxt-peers*) (list :direct)))
(assert-event (not (fn-pxy-trusted-peer *pxt-public* *pxt-peers*)))
; The antecedent dropped: for the public peer the path is not :read and no
; WHY exists.
(must-fail-checked
 (assert-event (equal (car (fn-pxy-begin *pxt-public* *pxt-peers*)) :read)))
; No row (the default) trusts nobody, the proxy included.
(assert-event (equal (fn-pxy-begin *pxt-proxy* nil) (list :direct)))
(assert-event (equal (fn-pxy-config-peers (fn-cfg-value (fn-cfg-initial))) nil))

; --- KEYSTONE fn-pxy-step-reads-within-the-bound.
(defconst *pxt-v1* (append (pxt-octets "PROXY TCP4 198.51.100.7 10.0.0.1 51234 563")
                           *pxt-crlf*))
(defconst *pxt-v1-6* (append (pxt-octets "PROXY TCP6 2001:db8::7 fd00::1 51234 563")
                             *pxt-crlf*))
(defconst *pxt-v1-unknown* (append (pxt-octets "PROXY UNKNOWN") *pxt-crlf*))
; The v1 read: 6 octets, then one at a time until LF.
(assert-event (equal (fn-pxy-step nil) '(:more 6)))
(assert-event (equal (fn-pxy-step (take 6 *pxt-v1*)) '(:more 1)))
(assert-event (equal (fn-pxy-step (take 20 *pxt-v1*)) '(:more 1)))
(assert-event (equal (fn-pxy-step *pxt-v1*)
                     (list :header (len *pxt-v1*) '(:inet 198 51 100 7))))
(assert-event (equal (fn-pxy-step *pxt-v1-6*)
                     (list :header (len *pxt-v1-6*)
                           '(:inet6 32 1 13 184 0 0 0 0 0 0 0 0 0 0 0 7))))
(assert-event (equal (fn-pxy-step *pxt-v1-unknown*) (list :header 15 :local)))
; The v2 read: 16 octets, then exactly the length.
(defconst *pxt-v2-head* (append *fn-pxy-v2-signature* '(#x21 #x11 0 12)))
(defconst *pxt-v2* (append *pxt-v2-head* '(198 51 100 7 10 0 0 1 200 34 2 51)))
(defconst *pxt-v2-local* (append *fn-pxy-v2-signature* '(#x20 0 0 0)))
(assert-event (equal (fn-pxy-step (take 6 *pxt-v2*)) '(:more 10)))
(assert-event (equal (fn-pxy-step *pxt-v2-head*) '(:more 12)))
(assert-event (equal (fn-pxy-step *pxt-v2*) (list :header 28 '(:inet 198 51 100 7))))
(assert-event (equal (fn-pxy-step *pxt-v2-local*) (list :header 16 :local)))
; The bound's conclusion on the witnesses: every :more stays within 528.
(assert-event (<= (+ 16 12) *fn-pxy-max*))
(assert-event (<= (+ 20 1) *fn-pxy-max*))
; Refusals by name: oversize (a v1 line of 107 octets without LF; a v2
; length of 513), malformed (not a header; a bad address; a second LF),
; unsupported (v2 over UDP).
(assert-event (equal (fn-pxy-step (append (pxt-octets "PROXY ") (make-list 101 :initial-element 65)))
                     '(:refuse :proxy-oversize)))
(assert-event (equal (fn-pxy-step (append *fn-pxy-v2-signature* '(#x21 #x11 2 1)))
                     '(:refuse :proxy-oversize)))
(assert-event (equal (fn-pxy-step (pxt-octets "GET / ")) '(:refuse :proxy-malformed)))
(assert-event (equal (fn-pxy-step (append (pxt-octets "PROXY TCP4 198.51.100.300 10.0.0.1 1 2")
                                          *pxt-crlf*))
                     '(:refuse :proxy-malformed)))
(assert-event (equal (fn-pxy-step (append (pxt-octets "PROXY TCP4 198.51.100.7 10.0.0.1 1 65536")
                                          *pxt-crlf*))
                     '(:refuse :proxy-malformed)))
(assert-event (equal (fn-pxy-step (append *fn-pxy-v2-signature* '(#x21 #x12 0 12)
                                          (make-list 12 :initial-element 0)))
                     '(:refuse :proxy-unsupported)))
; The antecedent dropped: a refusal is no :more, and its second element is
; no count within the bound.
(must-fail-checked
 (assert-event (posp (cadr (fn-pxy-step (pxt-octets "GET / "))))))
; A header answer is exactly what was read: the conclusion fails for any
; other count.
(must-fail-checked
 (assert-event (equal (cadr (fn-pxy-step *pxt-v2*)) (+ 1 (len *pxt-v2*)))))

; --- KEYSTONE fn-pxy-handover-keeps-the-bound (and both charges).
(defconst *pxt-hl* (fn-hsb-limits-with 30 2 5000 nil))
(defconst *pxt-r0* (fn-hsb-admit (fn-hsb-initial) *pxt-hl* nil *pxt-proxy* 1000 nil))
(assert-event (equal (fn-hsb-verdict *pxt-r0*) :admit))
(defconst *pxt-s0* (fn-hsb-state *pxt-r0*))
(defconst *pxt-r1* (fn-pxy-handover *pxt-s0* *pxt-hl* (fn-hsb-detail *pxt-r0*) nil
                                    '(:inet 198 51 100 7) 1100))
; Witness: the okp antecedent, the handover admits the asserted source, the
; bound holds after it; the flight holds one handshake (the asserted
; source's); both sources' buckets were charged; two starts in the tick.
(assert-event (fn-hsb-okp *pxt-s0* *pxt-hl*))
(assert-event (equal (fn-hsb-verdict *pxt-r1*) :admit))
(assert-event (fn-hsb-okp (fn-hsb-state *pxt-r1*) *pxt-hl*))
(assert-event (equal (fn-hsb-flight (fn-hsb-state *pxt-r1*))
                     (list (cons (fn-hsb-detail *pxt-r1*) '(:inet 198 51 100 7)))))
(assert-event (fn-hsb-has *pxt-proxy* (fn-hsb-buckets (fn-hsb-state *pxt-r1*))))
(assert-event (fn-hsb-has '(:inet 198 51 100 7) (fn-hsb-buckets (fn-hsb-state *pxt-r1*))))
(assert-event (equal (fn-hsb-started (fn-hsb-state *pxt-r1*)) 2))
; The node-wide bound holds over both charges: with L = 2 a third start in
; the same tick waits (the handed-over id here is one no longer in flight).
(assert-event (equal (fn-hsb-verdict (fn-pxy-handover (fn-hsb-state *pxt-r1*) *pxt-hl*
                                                      (fn-hsb-detail *pxt-r0*) nil
                                                      '(:inet 198 51 100 8) 1200))
                     :wait))
; The antecedent dropped: from a state holding four handshakes under L = 2
; (not okp), the handover leaves three -- not within the bound.
(defconst *pxt-bad* (fn-hsb-make 4 1 0 (list (cons 0 *pxt-proxy*) (cons 1 *pxt-proxy*)
                                             (cons 2 *pxt-proxy*) (cons 3 *pxt-proxy*))
                                 0 nil))
(assert-event (not (fn-hsb-okp *pxt-bad* *pxt-hl*)))
(must-fail-checked
 (assert-event (fn-hsb-okp (fn-hsb-state (fn-pxy-handover *pxt-bad* *pxt-hl* 0 nil
                                                          '(:inet 198 51 100 7) 1100))
                           *pxt-hl*)))

; The lines.
(assert-event (equal (fn-pxy-refusal-line :proxy-malformed *pxt-proxy*)
                     "tls refused reason=proxy-malformed proxy=10.1.2.3"))
(assert-event (equal (fn-pxy-refusal-line :proxy-timeout *pxt-mapped-proxy*)
                     "tls refused reason=proxy-timeout proxy=10.1.2.3"))

; --- KEYSTONE fn-pxy-observe-keeps-the-read-bound.
; Real nonempty v1 and v2 header observations on each side of the deadline.
(defconst *pxt-deadline* (fn-pxy-deadline 100 2000 1000))
(assert-event (equal *pxt-deadline* 2100))
(assert-event (equal (fn-pxy-deadline 100 1 60) 101))
(assert-event (equal (fn-pxy-deadline 100 0 1000) nil))
(assert-event (equal (fn-pxy-deadline 100 2000 0) nil))

; Literal complete conclusion of fn-pxy-observe-keeps-the-read-bound.
(defmacro pxt-timed-conclusion (octets deadline now)
  `(let ((r (fn-pxy-observe ,octets ,deadline ,now)))
     (and (implies (equal (car r) :more)
                   (and (posp (cadr r))
                        (<= (+ (len ,octets) (cadr r)) *fn-pxy-max*)))
          (implies (equal (car r) :header)
                   (and (equal (cadr r) (len ,octets))
                        (<= (len ,octets) *fn-pxy-max*)
                        (natp ,deadline) (natp ,now) (< ,now ,deadline)))
          (member-equal (car r) '(:more :header :refuse)))))
(assert-event
 (and (equal (car (fn-pxy-observe *pxt-v1* *pxt-deadline* 2099)) :header)
      (pxt-timed-conclusion *pxt-v1* *pxt-deadline* 2099)))
(assert-event
 (and (equal (car (fn-pxy-observe *pxt-v2* *pxt-deadline* 2099)) :header)
      (pxt-timed-conclusion *pxt-v2* *pxt-deadline* 2099)))
(assert-event
 (and (equal (fn-pxy-observe (take 20 *pxt-v1*) *pxt-deadline* 2099) '(:more 1))
      (pxt-timed-conclusion (take 20 *pxt-v1*) *pxt-deadline* 2099)))
(assert-event
 (and (equal (fn-pxy-observe *pxt-v1* *pxt-deadline* 2100) '(:refuse :proxy-timeout))
      (pxt-timed-conclusion *pxt-v1* *pxt-deadline* 2100)))
(assert-event
 (and (equal (fn-pxy-observe (take 20 *pxt-v1*) *pxt-deadline* 2200) '(:refuse :proxy-timeout))
      (pxt-timed-conclusion (take 20 *pxt-v1*) *pxt-deadline* 2200)))
; Corrupted clock state refuses instead of lending a late header authority.
(assert-event (equal (fn-pxy-observe *pxt-v1* nil 2100) '(:refuse :proxy-clock)))
(assert-event (equal (fn-pxy-observe *pxt-v1* *pxt-deadline* -1) '(:refuse :proxy-clock)))
; Mutation: bypassing the clock with the untimed parser accepts at the
; exact deadline. The actual host-called decision refuses the same bytes.
(assert-event
 (and (equal (car (fn-pxy-step *pxt-v1*)) :header)
      (not (< 2100 *pxt-deadline*))
      (equal (fn-pxy-observe *pxt-v1* *pxt-deadline* 2100) '(:refuse :proxy-timeout))))
