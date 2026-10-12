; Teeth for books/connection-budget.lisp (PKT-605; lane connection-multiplexing,
; 2026-09-26): a served connection's heap and native terms, the TLS handshakes'
; scratch, PKT-640's line and the read of a served step.  The run's capacity
; (PRF-223) is the memory gate's since L-RUN-LAUNCH: its teeth are
; tests/acl2/admission-memory-tests.lisp (fn-adm-capacity-fits,
; fn-adm-capacity-is-the-most).
;
; A = 32,768, TLS loaded.

(in-package "ACL2")
(include-book "../../books/connection-budget")
(include-book "../../books/defkeystone")
(include-book "must-fail-checked")

(defconst *cbt-article* 32768)
; The handshakes' scratch of the default L (16) with a TLS context (PRF-986).
(defconst *cbt-hs* (fn-cbud-handshake-octets t nil))
(assert-event (equal *cbt-hs* (* 16 *fn-cbud-handshake-scratch-octets*)))
(assert-event (equal (fn-cbud-handshake-octets nil nil) 0))

; The figure: 161 KiB in the heap (the reply of a 32 KiB article rendered, 65
; KiB, and a COMPRESS layer's inflater, 56 KiB, dominate; the command line's list is 16 KiB; the two 4 KiB reads of a
; step, lane input-loop-2, are 8 KiB; an article's BODY in flight is the
; store figure's since lane zero-copy-commit: one of fn-heap-article-slots),
; 392 KiB outside it (a COMPRESS layer's zlib state is 56 KiB of it).
(assert-event (equal (fn-cbud-conn-heap-octets *cbt-article*) 164864))
(assert-event (equal (fn-cbud-conn-native-octets t) 401408))
(assert-event (equal (fn-cbud-conn-octets *cbt-article* t) 566272))
(assert-event (equal (fn-cbud-conn-octets *cbt-article* nil) 435200))

(defconst *cbt-v-empty* (fn-cfg-value (fn-cfg-initial)))

; PKT-640's line.
(assert-event (equal (fn-cbud-tls-refusal-line :timeout 7)
                     "tls refused reason=timeout connection=7"))
(assert-event (equal (fn-cbud-tls-refusal-line :busy 0)
                     "tls refused reason=busy connection=0"))

; -----------------------------------------------------------------------------
; The read of a served step (lane input-loop-2).  A public listener's limits
; carry the step rate (64 per second): a step reads 512 octets, the rate's
; unit.  A loopback listener's carry none: a step reads 4 KiB.
(defconst *cbt-public-lim*
  (fn-exp-limits *cbt-v-empty* *fn-exp-owner-connection-bound* t nil))
(defconst *cbt-loopback-lim*
  (fn-exp-limits *cbt-v-empty* *fn-exp-owner-connection-bound* nil nil))
; fn-cbud-step-read-octets-under-a-rate-by-definition.  H1 (posp (fn-exp-lim-steps lim)).
; Witness: the public limits, rate 64, read 512.
(assert-event (equal (fn-exp-lim-steps *cbt-public-lim*) 64))
(assert-event (equal (fn-cbud-step-read-octets *cbt-public-lim*) 512))
; H1 dropped: the loopback limits have no rate, and the read is not 512.
(assert-event (not (posp (fn-exp-lim-steps *cbt-loopback-lim*))))
(must-fail-checked
 (assert-event (equal (fn-cbud-step-read-octets *cbt-loopback-lim*) 512)))
; fn-cbud-step-read-octets-is-bounded and fn-cbud-read-covers-the-step (no
; hypotheses): the loopback read is the quantum, 4 KiB, and two of it are the
; figure's read term.
(assert-event (equal (fn-cbud-step-read-octets *cbt-loopback-lim*) 4096))
(assert-event (equal (* 2 (fn-cbud-step-read-octets *cbt-loopback-lim*))
                     *fn-cbud-read-octets*))
; An operator's row of 0 turns the rate off on a public listener: 4 KiB.
(defconst *cbt-v-norate*
  (fn-cfg-apply-delta *cbt-v-empty* 1 0 (fn-cfg-set-limit "exposure-steps-per-second" 0)))
(assert-event (equal (fn-cbud-step-read-octets
                      (fn-exp-limits *cbt-v-norate* *fn-exp-owner-connection-bound* t nil))
                     4096))
