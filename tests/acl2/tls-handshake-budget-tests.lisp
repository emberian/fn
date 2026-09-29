; Witnesses and teeth for books/tls-handshake-budget.lisp (lane
; tls-handshake-budget, 2026-09-29; PRF-986).  The states are REACHED from
; fn-hsb-initial through the calls host/owner-host.lisp makes
; (fn-owner-handshake-admit -> fn-hsb-admit, fn-owner-handshake-done ->
; fn-hsb-done, fn-owner-handshake-leave -> fn-hsb-leave); corrupted states
; are labelled.
(in-package "ACL2")
(include-book "../../books/tls-handshake-budget")
(include-book "must-fail-checked")

; N = 3 per minute, L = 2 in flight, D = 5,000 ms.
(defconst *hsbt-hl* (fn-hsb-limits 3 2 5000))
(defconst *hsbt-a* '(:inet 192 0 2 1))
(defconst *hsbt-b* '(:inet 198 51 100 7))
(defconst *hsbt-v6* '(:inet6 32 1 13 184 0 0 0 1 0 0 0 0 0 0 0 9))

(defun hsbt-admit (s addr now q) (fn-hsb-admit s *hsbt-hl* nil addr now q))
(defun hsbt-s (r) (fn-hsb-state r))

; --- A reached run.  At 1,000 ms source A starts two handshakes (ids 1, 2);
; a third waits (two in flight); 1 ends; the waiting socket still waits (two
; started this second); at 2,000 ms it is admitted (id 3, A's third token);
; at 2,500 ms a fourth from A is refused by name (its bucket is empty), and
; after 2 ends, source B is admitted (id 4).
(defconst *hsbt-r1* (hsbt-admit (fn-hsb-initial) *hsbt-a* 1000 nil))
(assert-event (and (equal (fn-hsb-verdict *hsbt-r1*) :admit) (equal (fn-hsb-detail *hsbt-r1*) 1)))
(defconst *hsbt-r2* (hsbt-admit (hsbt-s *hsbt-r1*) *hsbt-a* 1000 nil))
(assert-event (and (equal (fn-hsb-verdict *hsbt-r2*) :admit) (equal (fn-hsb-detail *hsbt-r2*) 2)))
(defconst *hsbt-r3* (hsbt-admit (hsbt-s *hsbt-r2*) *hsbt-a* 1000 nil))
(assert-event (equal (fn-hsb-verdict *hsbt-r3*) :wait))
(assert-event (equal (fn-hsb-waiting (hsbt-s *hsbt-r3*)) 1))
(defconst *hsbt-s4* (fn-hsb-done (hsbt-s *hsbt-r3*) 1))
(defconst *hsbt-r5* (hsbt-admit *hsbt-s4* *hsbt-a* 1000 t))
(assert-event (equal (fn-hsb-verdict *hsbt-r5*) :wait))
(defconst *hsbt-r6* (hsbt-admit (hsbt-s *hsbt-r5*) *hsbt-a* 2000 t))
(assert-event (and (equal (fn-hsb-verdict *hsbt-r6*) :admit) (equal (fn-hsb-detail *hsbt-r6*) 3)
                   (equal (fn-hsb-waiting (hsbt-s *hsbt-r6*)) 0)))
(defconst *hsbt-r7* (hsbt-admit (hsbt-s *hsbt-r6*) *hsbt-a* 2500 nil))
(assert-event (and (equal (fn-hsb-verdict *hsbt-r7*) :refuse)
                   (equal (fn-hsb-detail *hsbt-r7*) :handshake-budget)))
(assert-event (equal (fn-hsb-refusal-line :handshake-budget *hsbt-a*)
                     "tls refused reason=handshake-budget source=192.0.2.1"))
(defconst *hsbt-r8* (hsbt-admit (fn-hsb-done (hsbt-s *hsbt-r7*) 2) *hsbt-b* 2500 nil))
(assert-event (and (equal (fn-hsb-verdict *hsbt-r8*) :admit) (equal (fn-hsb-detail *hsbt-r8*) 4)))
; A trusted source is exempt from the per-source budget (only).
(assert-event (equal (fn-hsb-verdict (fn-hsb-admit (fn-hsb-done (hsbt-s *hsbt-r7*) 2)
                                                   *hsbt-hl* t *hsbt-a* 2500 nil))
                     :admit))
; An IPv6 source is its /64.
(assert-event (equal (fn-hsb-source-key *hsbt-v6*) '(:inet6 32 1 13 184 0 0 0 1)))
(assert-event (equal (fn-hsb-refusal-line :busy *hsbt-v6*)
                     "tls refused reason=busy source=2001:0db8:0000:0001::/64"))
; Too many waiting: with L = 1 the queue holds 32; the 33rd is refused busy.
(defun hsbt-fill (s n)
  (if (zp n) s
    (hsbt-fill (fn-hsb-state (fn-hsb-admit s (fn-hsb-limits 3 1 5000) t *hsbt-b* 1000 nil))
               (1- n))))
(defconst *hsbt-full* (hsbt-fill (fn-hsb-initial) 33))
(assert-event (and (equal (len (fn-hsb-flight *hsbt-full*)) 1)
                   (equal (fn-hsb-waiting *hsbt-full*) 32)))
(assert-event (equal (fn-hsb-admit *hsbt-full* (fn-hsb-limits 3 1 5000) t *hsbt-b* 1000 nil)
                     (list :refuse *hsbt-full* :busy)))

; --- KEYSTONE fn-hsb-steps-keep-the-bound: a reached positive witness (the
; antecedent and every conjunct of the conclusion).
(defconst *hsbt-s* (hsbt-s *hsbt-r6*))
(assert-event (fn-hsb-okp *hsbt-s* *hsbt-hl*))
(assert-event (and (fn-hsb-okp (fn-hsb-state (hsbt-admit *hsbt-s* *hsbt-b* 2000 nil)) *hsbt-hl*)
                   (fn-hsb-okp (fn-hsb-done *hsbt-s* 2) *hsbt-hl*)
                   (fn-hsb-okp (fn-hsb-leave *hsbt-s*) *hsbt-hl*)))
; Hypothesis removal (CORRUPTED STATE, not reachable): three in flight under
; L = 2 -- the omitted (fn-hsb-okp s hl) fails, and so does the conclusion.
(defconst *hsbt-bad* (fn-hsb-make 9 1 0 '((6 . a) (7 . b) (8 . c)) 0 nil))
(assert-event (not (fn-hsb-okp *hsbt-bad* *hsbt-hl*)))
(assert-event (not (fn-hsb-okp (fn-hsb-state (hsbt-admit *hsbt-bad* *hsbt-b* 1000 nil)) *hsbt-hl*)))

; --- KEYSTONE fn-hsb-admits-per-tick-are-bounded: three sources offer a
; handshake each in tick 1 and a slot is freed between: two are admitted in
; the tick, exactly L.
(defconst *hsbt-events*
  (list (list :admit *hsbt-hl* nil *hsbt-a* 1000 nil)
        (list :admit *hsbt-hl* nil *hsbt-b* 1100 nil)
        (list :done 1)
        (list :admit *hsbt-hl* nil *hsbt-v6* 1200 nil)))
(assert-event (fn-hsb-events-under 2 *hsbt-events*))
(assert-event (equal (fn-hsb-admits-in-tick 1 (fn-hsb-initial) *hsbt-events*) 2))
; Hypothesis removal: under a claimed LMAX of 1 the events (decided at L = 2)
; are not under it, and the count 2 exceeds it.
(assert-event (not (fn-hsb-events-under 1 *hsbt-events*)))
(assert-event (< 1 (fn-hsb-admits-in-tick 1 (fn-hsb-initial) *hsbt-events*)))

; --- KEYSTONE fn-hsb-source-admits-are-bounded: A offers four handshakes
; within [0, 1000] at N = 3 (one slot freed after each): three are admitted,
; 3 x 60,000 <= 3 x 60,000 + 3 x 1,000.
(defconst *hsbt-flood*
  (list (list :admit *hsbt-hl* nil *hsbt-a* 0 nil) (list :done 1)
        (list :admit *hsbt-hl* nil *hsbt-a* 0 nil) (list :done 2)
        (list :admit *hsbt-hl* nil *hsbt-a* 1000 nil) (list :done 3)
        (list :admit *hsbt-hl* nil *hsbt-a* 1000 nil)))
(assert-event (and (fn-hsb-events-timed *hsbt-flood* 0 1000 3 (fn-hsb-source-key *hsbt-a*)) (<= 0 1000) (natp 3)))
(assert-event (equal (fn-hsb-source-admits (fn-hsb-source-key *hsbt-a*) (fn-hsb-initial) *hsbt-flood*) 3))
(assert-event (<= (* 60000 3) (+ (* 3 60000) (* 3 (- 1000 0)))))
; Hypothesis removal, each retained hypothesis holding and the omitted one
; failing, with the conclusion failing:
; (a) the times: the same flood spread to 180,000 ms is not within [0, 1000]
;     (the rate and T0 <= T1 hold), and 4 admissions exceed 3 x 60,000 + 3,000.
(defconst *hsbt-slow*
  (list (list :admit *hsbt-hl* nil *hsbt-a* 0 nil) (list :done 1)
        (list :admit *hsbt-hl* nil *hsbt-a* 0 nil) (list :done 2)
        (list :admit *hsbt-hl* nil *hsbt-a* 1000 nil) (list :done 3)
        (list :admit *hsbt-hl* nil *hsbt-a* 180000 nil)))
(assert-event (and (not (fn-hsb-events-timed *hsbt-slow* 0 1000 3 (fn-hsb-source-key *hsbt-a*)))
                   (fn-hsb-events-timed *hsbt-slow* 0 180000 3 (fn-hsb-source-key *hsbt-a*))))
(assert-event (< (+ (* 3 60000) (* 3 1000))
                 (* 60000 (fn-hsb-source-admits (fn-hsb-source-key *hsbt-a*) (fn-hsb-initial) *hsbt-slow*))))
; (b) the rate: decided at N = 3, claimed at N = 1: not timed at 1, and
;     3 admissions exceed 1 x 60,000 + 1 x 1,000.
(assert-event (not (fn-hsb-events-timed *hsbt-flood* 0 1000 1 (fn-hsb-source-key *hsbt-a*))))
(assert-event (< (+ 60000 1000)
                 (* 60000 (fn-hsb-source-admits (fn-hsb-source-key *hsbt-a*) (fn-hsb-initial) *hsbt-flood*))))
; (c) T0 <= T1: no events, T0 = 100,000 > T1 = 0: the bound is negative.
(assert-event (and (fn-hsb-events-timed nil 100000 0 3 (fn-hsb-source-key *hsbt-a*)) (not (<= 100000 0))))
(assert-event (< (+ (* 3 60000) (* 3 (- 0 100000))) 0))
; (d) (natp n): no events, N = -1: timed holds, the bound is negative.
(assert-event (and (fn-hsb-events-timed nil 0 1000 -1 (fn-hsb-source-key *hsbt-a*)) (not (natp -1))))
(assert-event (< (+ (* -1 60000) (* -1 (- 1000 0))) 0))

; --- fn-hsb-scratch-within-the-machine-term (PRF-986's term of PRF-223's
; machine).  Witness (reached): two in flight under L = 2 hold 256 KiB of
; scratch, exactly the term the run charges for L = 2, and within the
; scratch of 16 held slots.
(defconst *hsbt-two* (hsbt-s (hsbt-admit (hsbt-s *hsbt-r1*) *hsbt-b* 1000 nil)))
(assert-event (and (fn-hsb-okp *hsbt-two* (fn-hsb-limits 3 2 5000))
                   (equal (len (fn-hsb-flight *hsbt-two*)) 2)))
(assert-event (equal (fn-hsb-lim-in-flight (fn-hsb-limits 3 2 5000))
                     (fn-cbud-handshake-slots t 2)))
(assert-event (and (<= (* 2 *fn-cbud-handshake-scratch-octets*) (fn-cbud-handshake-octets t 2))
                   (equal (fn-cbud-handshake-octets t 2) 262144)
                   (<= (fn-cbud-handshake-slots t 2) 16)
                   (<= (* 2 *fn-cbud-handshake-scratch-octets*) (fn-cbud-slots-octets 16))))
; An absent row (nil) is the profile's L, 16: 2 MiB charged.
(assert-event (equal (fn-cbud-handshake-octets t nil) 2097152))
; No TLS context: nothing charged.
(assert-event (equal (fn-cbud-handshake-octets nil 2) 0))
; Hypothesis removal (CORRUPTED STATE): three in flight under L = 2 -- not
; within the bound, and 384 KiB exceed the 256 KiB term.
(assert-event (and (not (fn-hsb-okp *hsbt-bad* (fn-hsb-limits 3 2 5000)))
                   (< (fn-cbud-handshake-octets t 2)
                      (* (len (fn-hsb-flight *hsbt-bad*)) *fn-cbud-handshake-scratch-octets*))))
; The inner hypothesis removed: one held slot, below L = 2 (the flight within
; the bound): two in flight exceed one slot's scratch.
(assert-event (and (not (<= (fn-cbud-handshake-slots t 2) 1))
                   (< (fn-cbud-slots-octets 1)
                      (* (len (fn-hsb-flight *hsbt-two*)) *fn-cbud-handshake-scratch-octets*))))

; --- fn-hsb-mapped-address-is-one-source: ::ffff:192.0.2.1 is 192.0.2.1.
(defconst *hsbt-a-mapped* '(:inet6 0 0 0 0 0 0 0 0 0 0 255 255 192 0 2 1))
(assert-event (equal (fn-hsb-source-key *hsbt-a-mapped*) (fn-hsb-source-key *hsbt-a*)))
(assert-event (equal (fn-hsb-normal-address *hsbt-a-mapped*) *hsbt-a*))
; Decided as A itself: the same verdict, state and detail from the same state.
(assert-event (equal (hsbt-admit (hsbt-s *hsbt-r2*) *hsbt-a-mapped* 1000 nil)
                     (hsbt-admit (hsbt-s *hsbt-r2*) *hsbt-a* 1000 nil)))
(assert-event (equal (fn-hsb-refusal-line :handshake-budget *hsbt-a-mapped*)
                     "tls refused reason=handshake-budget source=192.0.2.1"))
; Not mapped: a different prefix stays an IPv6 /64.
(assert-event (equal (fn-hsb-source-key '(:inet6 0 0 0 0 0 0 0 0 0 0 255 254 192 0 2 1))
                     '(:inet6 0 0 0 0 0 0 0 0)))

;; --- KEYSTONE fn-hsb-buckets-are-bounded and the :sources-full refusal.
;; N = 1 a minute (a row lives 60 s), L = 2 (R = 128): 64 sources, two a
;; second, each take a row.  Then L is lowered live to 1 (R = 64): the 65th
;; new source is refused :sources-full, the table stays at 64 and nobody's
;; row is dropped; a source with a row is still decided by its own bucket.
(defconst *hsbt-l2* (fn-hsb-limits 1 2 5000))
(defconst *hsbt-l1* (fn-hsb-limits 1 1 5000))
(defun hsbt-src (i) (list :inet 10 0 0 (nfix i)))
(defun hsbt-events-from (i n)
  (declare (xargs :measure (nfix (- (nfix n) (nfix i)))))
  (if (< (nfix i) (nfix n))
      (list* (list :admit *hsbt-l2* nil (hsbt-src i) (* 1000 (+ 1 (floor (nfix i) 2))) nil)
             (list :done (+ 1 (nfix i)))
             (hsbt-events-from (+ 1 (nfix i)) n))
    nil))
(defconst *hsbt-64* (hsbt-events-from 0 64))
(defconst *hsbt-s64* (fn-hsb-run (fn-hsb-initial) *hsbt-64*))
(assert-event (and (fn-hsb-events-under 2 *hsbt-64*)
                   (equal (len (fn-hsb-buckets *hsbt-s64*)) 64)
                   (<= (len (fn-hsb-buckets *hsbt-s64*))
                       (max (len (fn-hsb-buckets (fn-hsb-initial))) (* 64 2)))))
(defconst *hsbt-r65* (fn-hsb-admit *hsbt-s64* *hsbt-l1* nil (hsbt-src 64) 33000 nil))
(assert-event (equal (fn-hsb-verdict *hsbt-r65*) :refuse))
(assert-event (equal (fn-hsb-detail *hsbt-r65*) :sources-full))
(assert-event (equal (fn-hsb-buckets (fn-hsb-state *hsbt-r65*)) (fn-hsb-buckets *hsbt-s64*)))
(assert-event (equal (fn-hsb-refusal-line :sources-full (hsbt-src 64))
                     "tls refused reason=sources-full source=10.0.0.64"))
(assert-event (equal (fn-hsb-detail (fn-hsb-admit *hsbt-s64* *hsbt-l1* nil (hsbt-src 63) 33000 nil))
                     :handshake-budget))
;; Hypothesis removal: the same 64 admissions claimed under LMAX 0 are not
;; under it, and 64 rows exceed max(0, 64 x 0).
(assert-event (and (not (fn-hsb-events-under 0 *hsbt-64*))
                   (< (max (len (fn-hsb-buckets (fn-hsb-initial))) (* 64 0))
                      (len (fn-hsb-buckets *hsbt-s64*)))))

; --- The CGNAT override (fn-hsb-source-rate; fn-hsb-overrides-of-word).
; A carrier NAT 203.0.113.9 listed at 600 a minute; 2001:db8::/64 at 90.
(defconst *hsbt-ov* (fn-hsb-overrides-of-word "203.0.113.9=600, 2001:db8::1/64=90" 64))
(assert-event (equal *hsbt-ov* '(((:inet 203 0 113 9) . 600)
                                 ((:inet6 32 1 13 184 0 0 0 0) . 90))))
(assert-event (equal (fn-hsb-overrides-of-word "none" 64) nil))
(assert-event (equal (fn-hsb-overrides-of-word "203.0.113.9=0" 64) :override-address))
(assert-event (equal (fn-hsb-overrides-of-word "203.0.113.9/24=5" 64) :override-address))
(assert-event (equal (fn-hsb-overrides-of-word "not-an-address=5" 64) :override-address))
; fn-hsb-overrides-of-word-is-bounded: two entries past a MOST of 1 are
; refused by name (the list is full), within 2 accepted.
(assert-event (equal (fn-hsb-overrides-of-word "203.0.113.9=600,192.0.2.1=5" 1) :overrides-full))
(assert-event (<= (len (fn-hsb-overrides-of-word "203.0.113.9=600,192.0.2.1=5" 2)) 2))
; The listed source's rate is its own; any other source keeps N; every
; global limit is the same (L, D, the queue, the table).
(defconst *hsbt-hlov* (fn-hsb-limits-with 3 2 5000 *hsbt-ov*))
(assert-event (equal (fn-hsb-source-rate *hsbt-hlov* '(:inet 203 0 113 9)) 600))
(assert-event (equal (fn-hsb-source-rate *hsbt-hlov* (fn-hsb-source-key *hsbt-a*)) 3))
(assert-event (equal (fn-hsb-source-rate *hsbt-hlov*
                                         (fn-hsb-source-key '(:inet6 32 1 13 184 0 0 0 0 1 2 3 4 5 6 7 8)))
                     90))
(assert-event (and (equal (fn-hsb-lim-in-flight *hsbt-hlov*) 2)
                   (equal (fn-hsb-lim-deadline *hsbt-hlov*) 5000)
                   (equal (fn-hsb-lim-sources *hsbt-hlov*) 128)))
; KEYSTONE fn-hsb-source-admits-are-bounded at the override: the NAT offers
; five handshakes a second apart (a slot freed after each): all five admitted
; (N = 3 would admit three), within 600 x 60,000 -- decided at its rate.
(defconst *hsbt-nat* '(:inet 203 0 113 9))
(defconst *hsbt-natflood*
  (list (list :admit *hsbt-hlov* nil *hsbt-nat* 0 nil) (list :done 1)
        (list :admit *hsbt-hlov* nil *hsbt-nat* 1000 nil) (list :done 2)
        (list :admit *hsbt-hlov* nil *hsbt-nat* 2000 nil) (list :done 3)
        (list :admit *hsbt-hlov* nil *hsbt-nat* 3000 nil) (list :done 4)
        (list :admit *hsbt-hlov* nil *hsbt-nat* 4000 nil)))
(assert-event (fn-hsb-events-timed *hsbt-natflood* 0 4000 600 *hsbt-nat*))
(assert-event (equal (fn-hsb-source-admits *hsbt-nat* (fn-hsb-initial) *hsbt-natflood*) 5))
; Hypothesis removal: claimed at N = 3 the events are not timed (decided at
; 600), and five admissions exceed 3 x 60,000 + 3 x 4,000.
(assert-event (not (fn-hsb-events-timed *hsbt-natflood* 0 4000 3 *hsbt-nat*)))
(assert-event (< (+ (* 3 60000) (* 3 4000))
                 (* 60000 (fn-hsb-source-admits *hsbt-nat* (fn-hsb-initial) *hsbt-natflood*))))
