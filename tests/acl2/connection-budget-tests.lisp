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
(include-book "must-fail-checked")

(defconst *cbt-machine* 2147483648)
(defconst *cbt-hneed* (* 815 1048576))
(defconst *cbt-core* (* 192 1048576))
(defconst *cbt-threads* 30)
(defconst *cbt-stack* (* 1192 1024))
(defconst *cbt-article* 32768)

; The figure: 161 KiB in the heap (the reply of a 32 KiB article rendered, 65
; KiB, and a COMPRESS layer's inflater, 56 KiB, dominate; the command line's list is 16 KiB; the two 4 KiB reads of a
; step, lane input-loop-2, are 8 KiB; an article's BODY in flight is the
; store figure's since lane zero-copy-commit: one of fn-heap-article-slots),
; 392 KiB outside it (a COMPRESS layer's zlib state is 56 KiB of it).
(assert-event (equal (fn-cbud-conn-heap-octets *cbt-article*) 164864))
(assert-event (equal (fn-cbud-conn-native-octets t) 401408))
(assert-event (equal (fn-cbud-conn-octets *cbt-article* t) 566272))
(assert-event (equal (fn-cbud-conn-octets *cbt-article* nil) 435200))
(assert-event (equal (fn-cbud-base-octets *cbt-hneed* *cbt-core* *cbt-threads* *cbt-stack*)
                     1218363392))

(defmacro cbt-bound (machine tlsp)
  `(fn-cbud-bound ,machine *cbt-hneed* *cbt-core* *cbt-threads* *cbt-stack*
                  *cbt-article* ,tlsp))

; The friend's node holds 1,640 TLS-capable connections beside the store.
(assert-event (equal (cbt-bound *cbt-machine* t) 1640))
; Thread-per-connection would have held 60 threads of 5.2 MiB for the
; default 32 connections; the loops hold the capacity with 30 threads.

; -----------------------------------------------------------------------------
; KEYSTONE fn-cbud-bound-holds-its-connections.
;   H1 (<= (nfix n) bound)  H2 (<= base machine)
; Witness: n = the bound, 1640; base and 1640 connections within 2 GiB.
(assert-event (<= 1640 (cbt-bound *cbt-machine* t)))
(assert-event (<= 1218363392 *cbt-machine*))
(assert-event (<= (+ 1218363392 (* 1640 566272)) *cbt-machine*))
; H1 dropped: 1641 connections do not fit.
(assert-event (not (<= 1641 (cbt-bound *cbt-machine* t))))
(must-fail-checked
 (assert-event (<= (+ 1218363392 (* 1641 566272)) *cbt-machine*)))
; H2 dropped: a 1 GiB machine cannot hold the base; the bound is 0 and even
; no connection fits.
(assert-event (equal (cbt-bound 1073741824 t) 0))
(assert-event (not (<= 1218363392 1073741824)))
(must-fail-checked
 (assert-event (<= (+ 1218363392 (* 0 566272)) 1073741824)))

; fn-cbud-bound-is-the-most (no hypotheses): 1641 does not fit.
(assert-event (< *cbt-machine* (+ 1218363392 (* (+ 1 1640) 566272))))

; -----------------------------------------------------------------------------
; The dynamic space caps the heap.  Two machines: the friend's node started by
; the launcher (DYNAMIC 4 GiB, past the machine: only the figure's way holds,
; the limit is the bound above), and a developer image on a 40 GiB cgroup
; with the default preset's 70 TiB figure (only the dynamic space's way
; holds: 32,000 MB of heap at most, and each connection's native part).
(defconst *cbt-dyn-launch* 4294967296)
(defconst *cbt-dyn-dev* (* 32000 1048576))
(defconst *cbt-hneed-default* (* 70 1099511627776))
(defconst *cbt-machine-40g* (* 40 1073741824))
(defconst *cbt-rest* 363773952)
(assert-event (equal (fn-cbud-rest-octets *cbt-core* *cbt-threads* *cbt-stack*) *cbt-rest*))

(defmacro cbt-limit (machine dynamic hneed)
  `(fn-cbud-limit ,machine ,dynamic ,hneed *cbt-core* *cbt-threads* *cbt-stack*
                  *cbt-article* t))
(defmacro cbt-resident (dynamic hneed n)
  `(fn-cbud-resident-octets ,dynamic ,hneed *cbt-core* *cbt-threads* *cbt-stack*
                            *cbt-article* t ,n))
(defmacro cbt-fits (machine dynamic hneed)
  `(fn-cbud-base-fitsp ,machine ,dynamic ,hneed *cbt-core* *cbt-threads* *cbt-stack*))

(assert-event (equal (cbt-limit *cbt-machine* *cbt-dyn-launch* *cbt-hneed*) 1640))
(assert-event (equal (cbt-limit *cbt-machine-40g* *cbt-dyn-dev* *cbt-hneed-default*) 22499))
(assert-event (equal (cbt-limit (* 24 1073741824) *cbt-dyn-dev* *cbt-hneed-default*) 0))

; KEYSTONE fn-cbud-limit-holds-its-connections.
;   H1 (<= (nfix n) limit)  H2 base-fitsp
; Witness (the figure's way): 1640 on the friend's node.
(assert-event (cbt-fits *cbt-machine* *cbt-dyn-launch* *cbt-hneed*))
(assert-event (<= (cbt-resident *cbt-dyn-launch* *cbt-hneed* 1640) *cbt-machine*))
; Witness (the dynamic space's way): 22,499 on the 40 GiB developer node.
(assert-event (cbt-fits *cbt-machine-40g* *cbt-dyn-dev* *cbt-hneed-default*))
(assert-event (<= (cbt-resident *cbt-dyn-dev* *cbt-hneed-default* 22499) *cbt-machine-40g*))
; H1 dropped: one more is not held, on either machine.
(must-fail-checked
 (assert-event (<= (cbt-resident *cbt-dyn-launch* *cbt-hneed* 1641) *cbt-machine*)))
(must-fail-checked
 (assert-event (<= (cbt-resident *cbt-dyn-dev* *cbt-hneed-default* 22500) *cbt-machine-40g*)))
; H2 dropped: on 24 GiB neither way holds the base; the limit is 0 and even
; no connection is held.
(assert-event (not (cbt-fits (* 24 1073741824) *cbt-dyn-dev* *cbt-hneed-default*)))
(must-fail-checked
 (assert-event (<= (cbt-resident *cbt-dyn-dev* *cbt-hneed-default* 0) (* 24 1073741824))))
; fn-cbud-limit-is-the-most (no hypotheses).
(assert-event (< *cbt-machine* (cbt-resident *cbt-dyn-launch* *cbt-hneed* 1641)))
(assert-event (< *cbt-machine-40g* (cbt-resident *cbt-dyn-dev* *cbt-hneed-default* 22500)))

; -----------------------------------------------------------------------------
; KEYSTONE fn-cbud-run-decide-holds-the-capacity.
;   H1 (equal (car d) :hold)
(defmacro cbt-decide (capacity machine)
  `(fn-cbud-run-decide ,capacity ,machine *cbt-dyn-launch* *cbt-hneed* *cbt-core*
                       *cbt-threads* *cbt-stack* *cbt-article* t))
; Witness: the default capacity 31, and the most, 1640, are held.
(assert-event (equal (cbt-decide 31 *cbt-machine*) '(:hold 1640)))
(assert-event (equal (cbt-decide 1640 *cbt-machine*) '(:hold 1640)))
(assert-event (<= (cbt-resident *cbt-dyn-launch* *cbt-hneed* 1640) *cbt-machine*))
; H1 dropped: 3,000 is refused on this machine,
; and 3,000 connections are not held by it.
(assert-event (equal (cbt-decide 3000 *cbt-machine*)
                     '(:refused :connections-exceed-memory 3000 1640)))
(must-fail-checked
 (assert-event (<= (cbt-resident *cbt-dyn-launch* *cbt-hneed* 3000) *cbt-machine*)))
; fn-cbud-run-decide-refuses-exactly-past-the-limit: 1641 refused, and the
; developer node on 24 GiB refuses the default capacity (bounds_join's case,
; which holds on 40 GiB).
(assert-event (equal (car (cbt-decide 1641 *cbt-machine*)) :refused))
(assert-event (equal (car (fn-cbud-run-decide 31 (* 24 1073741824) *cbt-dyn-dev*
                                              *cbt-hneed-default* *cbt-core*
                                              *cbt-threads* *cbt-stack* *cbt-article* t))
                     :refused))
(assert-event (equal (fn-cbud-run-decide 31 *cbt-machine-40g* *cbt-dyn-dev*
                                         *cbt-hneed-default* *cbt-core*
                                         *cbt-threads* *cbt-stack* *cbt-article* t)
                     '(:hold 22499)))
; The lines.
(assert-event (equal (fn-cbud-refusal-line (cbt-decide 3000 *cbt-machine*)
                                           *cbt-article* t *cbt-machine*)
                     "refused connections-exceed-memory capacity=3000 holds=1640 per-connection=553 KiB machine=2048 MB"))
(assert-event (equal (fn-cbud-hold-line (cbt-decide 31 *cbt-machine*) *cbt-article* t)
                     "connections holds=1640 per-connection=553 KiB"))
; The owner's line (fn-cbud-run-refusal-line, host/owner-host.lisp
; fn-owner-connection-budget): a base that fits keeps the line above; the raw
; developer image under a 24 GiB limit (its build's 32,000 MB dynamic space,
; the default profile's figure) names the parts that do not fit, where the
; line alone said only holds=0 (lane ops-fixes).
(assert-event (equal (fn-cbud-run-refusal-line (cbt-decide 3000 *cbt-machine*)
                                               *cbt-article* t *cbt-machine*
                                               *cbt-dyn-launch* *cbt-hneed* *cbt-core*
                                               *cbt-threads* *cbt-stack*)
                     (fn-cbud-refusal-line (cbt-decide 3000 *cbt-machine*)
                                           *cbt-article* t *cbt-machine*)))
(assert-event (equal (fn-cbud-run-refusal-line
                      (fn-cbud-run-decide 31 (* 24 1073741824) *cbt-dyn-dev*
                                          *cbt-hneed-default* *cbt-core*
                                          *cbt-threads* *cbt-stack* *cbt-article* t)
                      *cbt-article* t (* 24 1073741824) *cbt-dyn-dev*
                      *cbt-hneed-default* *cbt-core* *cbt-threads* *cbt-stack*)
                     "refused connections-exceed-memory capacity=31 holds=0 per-connection=553 KiB machine=24576 MB base-exceeds-machine heap-figure=73400320 MB dynamic=32000 MB fixed=347 MB"))

; -----------------------------------------------------------------------------
; KEYSTONE fn-cbud-admitted-connections-fit-the-machine.
;   H1 (fn-cfg-limits-withinp (fn-cfg-limits v))
;   H2 (not (fn-exp-auth-refusesp xs lim address now))
;   H3 the admission decision is (:admit)
;   H4 (<= capacity limit)   H5 base-fitsp
(defconst *cbt-v-empty* (fn-cfg-value (fn-cfg-initial)))
(defconst *cbt-v-cap1640*
  (fn-cfg-apply-delta *cbt-v-empty* 1 0 (fn-cfg-set-limit "exposure-connections" 1640)))
(defconst *cbt-v-cap2200*
  (fn-cfg-apply-delta *cbt-v-empty* 1 0 (fn-cfg-set-limit "exposure-connections" 2200)))
(defconst *cbt-a* '(:inet 192 168 1 7))
(defconst *cbt-lim1640*
  (fn-exp-limits *cbt-v-cap1640* *fn-exp-owner-connection-bound* nil nil))
(defconst *cbt-lim2200*
  (fn-exp-limits *cbt-v-cap2200* *fn-exp-owner-connection-bound* nil nil))
; Witness: 1,639 held, the 1,640th admitted, and the 1,640 are held by the machine.
(assert-event (fn-cfg-limits-withinp (fn-cfg-limits *cbt-v-cap1640*)))
(assert-event (not (fn-exp-auth-refusesp (fn-exp-initial) *cbt-lim1640* *cbt-a* 5000)))
(assert-event (equal (fn-exp-admit-decision (fn-exp-initial) *cbt-lim1640* 1639 *cbt-a* 5000)
                     '(:admit)))
(assert-event (<= (fn-exp-connections-capacity *cbt-v-cap1640*)
                  (cbt-limit *cbt-machine* *cbt-dyn-launch* *cbt-hneed*)))
(assert-event (cbt-fits *cbt-machine* *cbt-dyn-launch* *cbt-hneed*))
(assert-event (<= (cbt-resident *cbt-dyn-launch* *cbt-hneed* 1640) *cbt-machine*))
; H3 dropped: at 1,640 held the 1,641th is refused (busy), and 1641 are not held.
(assert-event (not (equal (fn-exp-admit-decision (fn-exp-initial) *cbt-lim1640* 1640
                                                 *cbt-a* 5000)
                          '(:admit))))
(must-fail-checked
 (assert-event (<= (cbt-resident *cbt-dyn-launch* *cbt-hneed* 1641) *cbt-machine*)))
; H4 dropped: a capacity of 2,200 (a live raise the owner refuses, below) admits
; the 2,200th, which is not held.
(assert-event (equal (fn-exp-admit-decision (fn-exp-initial) *cbt-lim2200* 2199 *cbt-a* 5000)
                     '(:admit)))
(assert-event (not (<= (fn-exp-connections-capacity *cbt-v-cap2200*)
                       (cbt-limit *cbt-machine* *cbt-dyn-launch* *cbt-hneed*))))
(must-fail-checked
 (assert-event (<= (cbt-resident *cbt-dyn-launch* *cbt-hneed* 2200) *cbt-machine*)))
; H5 dropped: the 24 GiB developer node, the default capacity 31 and its
; first admission: not held.
(assert-event (<= 31 (+ 31 (cbt-limit (* 24 1073741824) *cbt-dyn-dev* *cbt-hneed-default*))))
(must-fail-checked
 (assert-event (<= (cbt-resident *cbt-dyn-dev* *cbt-hneed-default* 1) (* 24 1073741824))))
; H1 and H2 are PRF-211's; their removal witnesses are in
; tests/acl2/public-exposure-tests.lisp (a row past the width; ten 481s).

; -----------------------------------------------------------------------------
; fn-cbud-deltas-refusal-keeps-the-capacity-held (and the live refusal).
(defconst *cbt-raise-2200* (list (fn-cfg-set-limit "exposure-connections" 2200)))
(defconst *cbt-raise-1500* (list (fn-cfg-set-limit "exposure-connections" 1500)))
(assert-event (equal (fn-cbud-deltas-refusal *cbt-v-empty* 1 0 *cbt-raise-2200* 1640)
                     :connections-exceed-memory))
(assert-event (null (fn-cbud-deltas-refusal *cbt-v-empty* 1 0 *cbt-raise-1500* 1640)))
(assert-event (<= (fn-exp-connections-capacity (fn-cfg-apply *cbt-v-empty* 1 0 *cbt-raise-1500*))
                  1640))
; The refusal's hypothesis dropped: the raise to 2,200 leaves 2,200 > 1,640.
(must-fail-checked
 (assert-event (<= (fn-exp-connections-capacity (fn-cfg-apply *cbt-v-empty* 1 0 *cbt-raise-2200*))
                   1640)))
; No bound installed (an ACL2 test entry): nothing refused here.
(assert-event (null (fn-cbud-deltas-refusal *cbt-v-empty* 1 0 *cbt-raise-2200* nil)))

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
