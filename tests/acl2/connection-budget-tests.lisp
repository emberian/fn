; Teeth for books/connection-budget.lisp (PRF-223; PKT-605; lane
; connection-multiplexing, 2026-09-26).  For each keystone: a reachable
; witness asserting every hypothesis and the conclusion, and one must-fail
; per hypothesis in which the others hold and the conclusion fails.
;
; The machine of the witnesses is the friend's node (planning/evidence/
; image-floor-2026-09-26.md): 2 GiB; the small preset's heap figure (815 MB
; on that core), its core (192 MB), image-floor's 1,192 KiB stack, 30 fixed
; threads (12 + 2 loops + 16 control clients), A = 32,768, TLS loaded.

(in-package "ACL2")
(include-book "../../books/connection-budget")
(include-book "std/testing/must-fail" :dir :system)

(defconst *cbt-machine* 2147483648)
(defconst *cbt-hneed* (* 815 1048576))
(defconst *cbt-core* (* 192 1048576))
(defconst *cbt-threads* 30)
(defconst *cbt-stack* (* 1192 1024))
(defconst *cbt-article* 32768)

; The figure: 1,122 KiB in the heap (the parser's lists dominate: 32 octets of
; heap per octet of a 32 KiB article in flight), 336 KiB outside it.
(assert-event (equal (fn-cbud-conn-heap-octets *cbt-article*) 1148928))
(assert-event (equal (fn-cbud-conn-native-octets t) 344064))
(assert-event (equal (fn-cbud-conn-octets *cbt-article* t) 1492992))
(assert-event (equal (fn-cbud-conn-octets *cbt-article* nil) 1361920))
(assert-event (equal (fn-cbud-base-octets *cbt-hneed* *cbt-core* *cbt-threads* *cbt-stack*)
                     1218363392))

(defmacro cbt-bound (machine tlsp)
  `(fn-cbud-bound ,machine *cbt-hneed* *cbt-core* *cbt-threads* *cbt-stack*
                  *cbt-article* ,tlsp))

; The friend's node holds 622 TLS-capable connections beside the store.
(assert-event (equal (cbt-bound *cbt-machine* t) 622))
; Thread-per-connection would have held 60 threads of 5.2 MiB for the
; default 32 connections; the loops hold the capacity with 30 threads.

; -----------------------------------------------------------------------------
; KEYSTONE fn-cbud-bound-holds-its-connections.
;   H1 (<= (nfix n) bound)  H2 (<= base machine)
; Witness: n = the bound, 622; base and 622 connections within 2 GiB.
(assert-event (<= 622 (cbt-bound *cbt-machine* t)))
(assert-event (<= 1218363392 *cbt-machine*))
(assert-event (<= (+ 1218363392 (* 622 1492992)) *cbt-machine*))
; H1 dropped: 623 connections do not fit.
(assert-event (not (<= 623 (cbt-bound *cbt-machine* t))))
(must-fail
 (assert-event (<= (+ 1218363392 (* 623 1492992)) *cbt-machine*)))
; H2 dropped: a 1 GiB machine cannot hold the base; the bound is 0 and even
; no connection fits.
(assert-event (equal (cbt-bound 1073741824 t) 0))
(assert-event (not (<= 1218363392 1073741824)))
(must-fail
 (assert-event (<= (+ 1218363392 (* 0 1492992)) 1073741824)))

; fn-cbud-bound-is-the-most (no hypotheses): 623 does not fit.
(assert-event (< *cbt-machine* (+ 1218363392 (* (+ 1 622) 1492992))))

; -----------------------------------------------------------------------------
; KEYSTONE fn-cbud-run-decide-holds-the-capacity.
;   H1 (equal (car d) :hold)
(defmacro cbt-decide (capacity machine)
  `(fn-cbud-run-decide ,capacity ,machine *cbt-hneed* *cbt-core* *cbt-threads*
                       *cbt-stack* *cbt-article* t))
; Witness: the default capacity 31, and the most, 622, are held.
(assert-event (equal (cbt-decide 31 *cbt-machine*) '(:hold 622)))
(assert-event (equal (cbt-decide 622 *cbt-machine*) '(:hold 622)))
(assert-event (<= (+ 1218363392 (* 622 1492992)) *cbt-machine*))
; H1 dropped: 1,000 (the measurement's capacity) is refused on this machine,
; and 1,000 connections do not fit it.
(assert-event (equal (cbt-decide 1000 *cbt-machine*)
                     '(:refused :connections-exceed-memory 1000 622)))
(must-fail
 (assert-event (<= (+ 1218363392 (* 1000 1492992)) *cbt-machine*)))
; fn-cbud-run-decide-refuses-exactly-past-the-bound: 622 held, 623 refused,
; and a machine below the base refuses capacity 0.
(assert-event (equal (car (cbt-decide 623 *cbt-machine*)) :refused))
(assert-event (equal (car (cbt-decide 0 1073741824)) :refused))
; The lines.
(assert-event (equal (fn-cbud-refusal-line (cbt-decide 1000 *cbt-machine*)
                                           *cbt-article* t *cbt-machine*)
                     "refused connections-exceed-memory capacity=1000 holds=622 per-connection=1458 KiB machine=2048 MB"))
(assert-event (equal (fn-cbud-hold-line (cbt-decide 31 *cbt-machine*) *cbt-article* t)
                     "connections holds=622 per-connection=1458 KiB"))

; -----------------------------------------------------------------------------
; KEYSTONE fn-cbud-admitted-connections-fit-the-machine.
;   H1 (fn-cfg-limits-withinp (fn-cfg-limits v))
;   H2 (not (fn-exp-auth-refusesp xs lim address now))
;   H3 the admission decision is (:admit)
;   H4 (<= capacity bound)   H5 (<= base machine)
(defconst *cbt-v-empty* (fn-cfg-value (fn-cfg-initial)))
(defconst *cbt-v-cap622*
  (fn-cfg-apply-delta *cbt-v-empty* 1 0 (fn-cfg-set-limit "exposure-connections" 622)))
(defconst *cbt-v-cap700*
  (fn-cfg-apply-delta *cbt-v-empty* 1 0 (fn-cfg-set-limit "exposure-connections" 700)))
(defconst *cbt-a* '(:inet 192 168 1 7))
(defconst *cbt-lim622*
  (fn-exp-limits *cbt-v-cap622* *fn-exp-owner-connection-bound* nil nil))
(defconst *cbt-lim700*
  (fn-exp-limits *cbt-v-cap700* *fn-exp-owner-connection-bound* nil nil))
; Witness: 621 held (all from one loopback-trusted source would do; the
; non-public listener sets no per-address row), the 622nd admitted, and the
; 622 fit.
(assert-event (fn-cfg-limits-withinp (fn-cfg-limits *cbt-v-cap622*)))
(assert-event (not (fn-exp-auth-refusesp (fn-exp-initial) *cbt-lim622* *cbt-a* 5000)))
(assert-event (equal (fn-exp-admit-decision (fn-exp-initial) *cbt-lim622* 621 *cbt-a* 5000)
                     '(:admit)))
(assert-event (<= (fn-exp-connections-capacity *cbt-v-cap622*) (cbt-bound *cbt-machine* t)))
(assert-event (<= (+ 1218363392 (* (+ 1 621) 1492992)) *cbt-machine*))
; H3 dropped: at 622 held the 623rd is refused (busy), and 623 would not fit.
(assert-event (not (equal (fn-exp-admit-decision (fn-exp-initial) *cbt-lim622* 622
                                                 *cbt-a* 5000)
                          '(:admit))))
(must-fail
 (assert-event (<= (+ 1218363392 (* (+ 1 622) 1492992)) *cbt-machine*)))
; H4 dropped: a capacity of 700 (a live raise the owner refuses, below) admits
; the 680th, which does not fit.
(assert-event (equal (fn-exp-admit-decision (fn-exp-initial) *cbt-lim700* 679 *cbt-a* 5000)
                     '(:admit)))
(assert-event (not (<= (fn-exp-connections-capacity *cbt-v-cap700*)
                       (cbt-bound *cbt-machine* t))))
(must-fail
 (assert-event (<= (+ 1218363392 (* (+ 1 679) 1492992)) *cbt-machine*)))
; H5 dropped: below the base nothing fits (the H3 removal of the first
; keystone, reached through an admission of capacity 0's machine).
(must-fail
 (assert-event (<= (+ 1218363392 (* 1 1492992)) 1073741824)))
; H1 and H2 are PRF-211's; their removal witnesses are in
; tests/acl2/public-exposure-tests.lisp (a row past the width; ten 481s).

; -----------------------------------------------------------------------------
; fn-cbud-deltas-refusal-keeps-the-capacity-held (and the live refusal).
(defconst *cbt-raise-700* (list (fn-cfg-set-limit "exposure-connections" 700)))
(defconst *cbt-raise-600* (list (fn-cfg-set-limit "exposure-connections" 600)))
(assert-event (equal (fn-cbud-deltas-refusal *cbt-v-empty* 1 0 *cbt-raise-700* 622)
                     :connections-exceed-memory))
(assert-event (null (fn-cbud-deltas-refusal *cbt-v-empty* 1 0 *cbt-raise-600* 622)))
(assert-event (<= (fn-exp-connections-capacity (fn-cfg-apply *cbt-v-empty* 1 0 *cbt-raise-600*))
                  622))
; The refusal's hypothesis dropped: the raise to 700 leaves 700 > 622.
(must-fail
 (assert-event (<= (fn-exp-connections-capacity (fn-cfg-apply *cbt-v-empty* 1 0 *cbt-raise-700*))
                   622)))
; No bound installed (an ACL2 test entry): nothing refused here.
(assert-event (null (fn-cbud-deltas-refusal *cbt-v-empty* 1 0 *cbt-raise-700* nil)))

; -----------------------------------------------------------------------------
; The launcher's room.  The small preset's 815 MB grows by room for the 622
; connections the machine holds (heap parts), never shrinks.
(defconst *cbt-decision* (list :heap 815 "small" 2048))
(defconst *cbt-profile*
  (fn-bs-profile-resolve (fn-heap-init-request '(:small) *cbt-machine*) nil))
(assert-event (<= 815 (fn-heap-decision-mb
                       (fn-cbud-launch-decide *cbt-decision* *cbt-profile* *cbt-core*
                                              *cbt-threads* *cbt-stack*
                                              (list *cbt-machine*)))))
(assert-event (equal (fn-cbud-launch-decide '(:refused :machine-cannot-hold-profile 3000 2048)
                                            *cbt-profile* *cbt-core* *cbt-threads*
                                            *cbt-stack* (list *cbt-machine*))
                     '(:refused :machine-cannot-hold-profile 3000 2048)))

; PKT-632's line.
(assert-event (equal (fn-cbud-tls-refusal-line :timeout 7)
                     "tls refused reason=timeout connection=7"))
