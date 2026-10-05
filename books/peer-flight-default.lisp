; The default peer flight profile `init' writes (coordinator decision,
; 2026-10-04; plan lanedumps/catchup2.md "DECIDED, NOT STARTED", step 1): a
; fresh node peers out of the box.  ACL2 decides the figure from the store
; profile; the host writes fn-pfp-write of it as ROOT/peer-flight-profile
; inside init's publication (step 2).
;
; The six fields (books/peer-flight-reservation.lisp fn-pfr-policy-p):
;   heap     the policy's least heap: its bookkeeping for FLIGHTS and the
;            fixed backing (fn-pfr-bookkeeping, fn-pfr-fixed-backing); the
;            spool is on disk, not in the heap
;   disk     FLIGHTS spools
;   flights  *fn-pfd-flights*, workers *fn-pfd-workers*
;   spool    one batch: the first record (the profile's record bound) and the
;            request quantum beyond it (books/peer-catchup.lisp
;            *fn-cu-request-quantum*: a batch is spooled whole)
;   work     the lifetime metered work: four units per octet of the
;            profile's history bound (fn-csp-io-work-units: each spooled
;            octet is written, replayed and digested once; one more covers
;            the per-operation unit) -- a lifetime figure, renewal is open
; Every figure is clamped so the default is a policy for EVERY input; the
; clamps bind only at bounds beyond any admitted profile (2^61 octets).
;
; The other half (step 3, below, ahead of the arithmetic library): `peer catch-up NAME SECONDS' with
; SECONDS > 0 is admitted only on a node whose profile is a policy
; (fn-pfp-catch-up-admission); otherwise the verb refuses by name rather than
; configure rounds that each fail reason=peer-flight-unfunded.
(in-package "ACL2")
(include-book "peer-flight-profile")
(include-book "byte-store-frame")
(include-book "peer-catchup")
(include-book "heap-store-figure")
(include-book "heap-reservation")
(include-book "native-admin")

(defconst *fn-pfd-flights* 2)
(defconst *fn-pfd-workers* 1)
(defconst *fn-pfd-clamp* (expt 2 61))

(defun fn-pfd-spool (record-octets)
  (declare (xargs :guard t))
  (min (+ (nfix record-octets) *fn-cu-request-quantum*) *fn-pfd-clamp*))

(defun fn-pfd-work (history-octets)
  (declare (xargs :guard t))
  (min (* 4 (nfix history-octets)) *fn-rl-word-max*))

(defun fn-pfd-heap ()
  (declare (xargs :guard t))
  (+ (fn-pfr-bookkeeping *fn-pfd-flights*) (fn-pfr-fixed-backing)))

(defun fn-pfd-policy (record-octets history-octets)
  (declare (xargs :guard t))
  (list (fn-pfd-heap)
        (* *fn-pfd-flights* (fn-pfd-spool record-octets))
        *fn-pfd-flights*
        *fn-pfd-workers*
        (fn-pfd-spool record-octets)
        (fn-pfd-work history-octets)))

; The host-called entry: the default for the store profile VALUES.
(defun fn-pfp-default-policy (values)
  (declare (xargs :guard t))
  (fn-pfd-policy (fn-bs-profile-max-record-octets values)
                 (fn-bs-profile-max-history-octets values)))

; The octets init publishes.
(defun fn-pfp-default-octets (values)
  (declare (xargs :guard t))
  (fn-pfp-write (fn-pfp-default-policy values)))

; =============================================================================
; Step 3: the catch-up verb refuses an unfunded node by name.  Without a peer
; flight profile every catch-up round draws no lease and fails
; reason=peer-flight-unfunded (books/peer-catchup-spool.lisp fn-csp-begin),
; round after round, while the verb itself was accepted.  The plan
; (books/native-admin-peer.lisp, the "catch-up" arm) stays pure over the
; words; the host observes the store's profile (host/native/heap.lisp
; fnn-peer-flight-profile: nil when absent, a refusal by name when
; malformed) only for a plan ACL2 says needs it, and this decides.  The
; round-time reason stays: a profile removed after configuration.

; Some row sets a nonzero catch-up interval (0 stops catch-up: no funding).
(defun fn-pfp-catch-up-rowsp (rows)
  (declare (xargs :guard t))
  (if (consp rows)
      (or (and (equal (fn-cfg-row-b (car rows)) *fn-pcb-catch-up-interval-slot*)
               (posp (fn-cfg-row-n (car rows))))
          (fn-pfp-catch-up-rowsp (cdr rows)))
    nil))

; The plans the admission observes: an accepted peer extension whose rows
; start (or re-time) catch-up.  The host reads the profile for these only, so
; a malformed profile refuses no other verb.
(defun fn-pfp-catch-up-observes-p (plan)
  (declare (xargs :guard t))
  (and (equal (fn-native-admin-result-status plan) :accepted)
       (equal (fn-native-admin-result-kind plan) :extend-peer)
       (fn-pfp-catch-up-rowsp (fn-native-admin-result-value plan))))

; OBSERVED is fnn-peer-flight-profile's value: the policy, or nil.
(defun fn-pfp-catch-up-admission (plan observed)
  (declare (xargs :guard t))
  (if (and (fn-pfp-catch-up-observes-p plan) (not (fn-pfr-policy-p observed)))
      (fn-native-admin-result :refused :catch-up-unfunded nil nil 0 nil nil)
    plan))

(defun fn-pfp-catch-up-refusal-line ()
  (declare (xargs :guard t))
  "peer catch-up refused: no peer flight profile")

;; An observed plan is admitted exactly on a funded node; unfunded, by name.
(defthm fn-pfp-catch-up-observed-accepted-only-funded
  (implies (fn-pfp-catch-up-observes-p plan)
           (and (iff (equal (fn-native-admin-result-status
                             (fn-pfp-catch-up-admission plan observed))
                            :accepted)
                     (fn-pfr-policy-p observed))
                (implies (not (fn-pfr-policy-p observed))
                         (equal (fn-native-admin-result-reason
                                 (fn-pfp-catch-up-admission plan observed))
                                :catch-up-unfunded))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable fn-pfr-policy-p fn-pfp-catch-up-rowsp))))

;; The operator grammar's `peer catch-up NAME SECONDS' with SECONDS > 0 is an
;; observed plan (books/native-admin-peer.lisp, the "catch-up" arm).
(local (defthm pfd-catch-up-plan-is-the-extend-arm
  (implies (and (equal (car (fn-native-admin-words argv)) "peer")
                (equal (cadr (fn-native-admin-words argv)) "catch-up")
                (equal (len (fn-native-admin-words argv)) 4)
                (fn-native-admin-argvp argv))
           (equal (fn-native-admin-plan argv)
                  (fn-native-admin-peer-extend-plan (fn-native-admin-words argv))))
  :rule-classes nil
  :hints (("Goal" :expand ((fn-native-admin-plan argv))
           :in-theory (union-theories '(member-equal (:e member-equal) (:e equal) (:e len)
                                        fn-native-admin-complaints-wordsp)
                                      (theory 'minimal-theory))))))

(defthm fn-pfp-catch-up-verb-is-observed
  (implies (and (equal (car (fn-native-admin-words argv)) "peer")
                (equal (cadr (fn-native-admin-words argv)) "catch-up")
                (equal (len (fn-native-admin-words argv)) 4)
                (equal (fn-native-admin-result-status (fn-native-admin-plan argv)) :accepted)
                (posp (fn-native-admin-decimal-value
                       (coerce (cadddr (fn-native-admin-words argv)) 'list))))
           (fn-pfp-catch-up-observes-p (fn-native-admin-plan argv)))
  :rule-classes nil
  :hints (("Goal" :use (pfd-catch-up-plan-is-the-extend-arm)
           :expand ((fn-native-admin-plan argv))
           :in-theory (e/d (fn-native-admin-peer-extend-plan fn-pfp-catch-up-observes-p
                            fn-pfp-catch-up-rowsp)
                           (fn-native-admin-plan fn-native-admin-decimalp
                            fn-native-admin-decimal-value fn-native-admin-words
                            fn-cfg-labelp)))))

; KEYSTONE: `peer catch-up NAME SECONDS' that would start rounds (SECONDS >
; 0) is accepted exactly on a node whose observed peer flight profile is a
; policy; on any other node it is refused by name, :catch-up-unfunded.
(defthm fn-pfp-catch-up-verb-accepted-only-funded
  (implies (and (and (equal (car (fn-native-admin-words argv)) "peer")
                     (equal (cadr (fn-native-admin-words argv)) "catch-up")
                     (equal (len (fn-native-admin-words argv)) 4))
                (equal (fn-native-admin-result-status (fn-native-admin-plan argv)) :accepted)
                (posp (fn-native-admin-decimal-value
                       (coerce (cadddr (fn-native-admin-words argv)) 'list))))
           (and (iff (equal (fn-native-admin-result-status
                             (fn-pfp-catch-up-admission (fn-native-admin-plan argv) observed))
                            :accepted)
                     (fn-pfr-policy-p observed))
                (implies (not (fn-pfr-policy-p observed))
                         (equal (fn-native-admin-result-reason
                                 (fn-pfp-catch-up-admission (fn-native-admin-plan argv) observed))
                                :catch-up-unfunded))))
  :hints (("Goal" :use (fn-pfp-catch-up-verb-is-observed
                        (:instance fn-pfp-catch-up-observed-accepted-only-funded
                                   (plan (fn-native-admin-plan argv))))
           :in-theory (disable fn-native-admin-plan fn-native-admin-words fn-pfr-policy-p
                               fn-pfp-catch-up-admission fn-pfp-catch-up-observes-p
                               fn-native-admin-decimal-value))))

; KEYSTONE: the admission takes nothing else -- every plan that does not
; start catch-up (a refusal, another verb, `peer catch-up NAME 0'), and every
; plan on a funded node, is returned unchanged.
(defthm fn-pfp-catch-up-admission-is-identity-elsewhere
  (implies (or (not (fn-pfp-catch-up-observes-p plan)) (fn-pfr-policy-p observed))
           (equal (fn-pfp-catch-up-admission plan observed) plan))
  :hints (("Goal" :in-theory (disable fn-pfr-policy-p fn-pfp-catch-up-observes-p))))

(local (include-book "arithmetic-5/top" :dir :system))

; -----------------------------------------------------------------------------
; KEYSTONE: the default is a valid policy for every store profile.
(local (defthm fn-pfd-heap-value
  (equal (fn-pfd-heap) 11728)
  :hints (("Goal" :in-theory (enable (:e fn-pfd-heap))))))

(defthm fn-pfd-default-is-a-policy
  (fn-pfr-policy-p (fn-pfp-default-policy values))
  :hints (("Goal" :in-theory (e/d (fn-pfd-heap-value)
                                  (fn-pfd-heap fn-bs-profile-max-record-octets
                                   fn-bs-profile-max-history-octets
                                   fn-pfr-bookkeeping fn-pfr-fixed-backing)))))

; -----------------------------------------------------------------------------
; The u64 codec round trip (books/peer-u64-codec.lisp), then the profile's.
(local (defthm pfd-mod-qr
  (implies (and (natp q) (natp r) (< r 256) (posp m))
           (equal (mod (+ r (* 256 q)) (* 256 m)) (+ r (* 256 (mod q m)))))
  :rule-classes nil))
(local (defthm pfd-n-split
  (implies (natp n)
           (and (natp (floor n 256)) (natp (mod n 256)) (< (mod n 256) 256)
                (equal (+ (mod n 256) (* 256 (floor n 256))) n)))
  :rule-classes nil))
(local (defthm pfd-mod-split
  (implies (and (natp n) (posp m))
           (equal (mod n (* 256 m)) (+ (mod n 256) (* 256 (mod (floor n 256) m)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use (pfd-n-split (:instance pfd-mod-qr (q (floor n 256)) (r (mod n 256))))))))
(local (defthm pfd-step-arith
  (implies (and (acl2-numberp a) (acl2-numberp mm) (acl2-numberp x) (acl2-numberp r)
                (equal big (* 256 mm)) (equal modn (+ r (* 256 x))))
           (equal (+ (* 256 (+ (* a mm) x)) r) (+ (* a big) modn)))
  :rule-classes nil))
(local (defthm pfd-expt-step
  (implies (posp k) (equal (expt 256 k) (* 256 (expt 256 (+ -1 k)))))
  :rule-classes nil))
(local (defthm pfd-expt-posp
  (implies (natp j) (posp (expt 256 j)))
  :rule-classes nil))
(local (defthm pfd-mod-num (acl2-numberp (mod x y)) :rule-classes nil))
(local (defthm pfd-octets-value-cons
  (equal (fn-cu-octets-value (cons x xs) a)
         (fn-cu-octets-value xs (+ (* 256 a) (nfix x))))
  :hints (("Goal" :in-theory (enable fn-cu-octets-value)))))
(local (defthm pfd-octets-value-of-u64-aux
  (implies (and (natp k) (natp n) (natp a))
           (equal (fn-cu-octets-value (fn-cu-u64-octets-aux k n acc) a)
                  (fn-cu-octets-value acc (+ (* a (expt 256 k)) (mod n (expt 256 k))))))
  :hints (("Goal" :induct (fn-cu-u64-octets-aux k n acc)
           :in-theory (enable fn-cu-u64-octets-aux))
          ("Subgoal *1/2"
           :in-theory (union-theories '(fn-cu-u64-octets-aux pfd-octets-value-cons nfix natp posp zp)
                                      (theory 'minimal-theory))
           :use (pfd-n-split
                 (:instance pfd-expt-posp (j (+ -1 k)))
                 (:instance pfd-mod-num (x (floor n 256)) (y (expt 256 (+ -1 k))))
                 (:instance pfd-mod-split (m (expt 256 (+ -1 k))))
                 (:instance pfd-expt-step)
                 (:instance pfd-step-arith (mm (expt 256 (+ -1 k)))
                            (x (mod (floor n 256) (expt 256 (+ -1 k))))
                            (r (mod n 256)) (big (expt 256 k))
                            (modn (mod n (expt 256 k)))))))))
(local (defun pfd-u64-image (xs)
  (declare (xargs :guard t))
  (if (consp xs) (cons (mod (nfix (car xs)) (expt 2 64)) (pfd-u64-image (cdr xs))) nil)))
(local (defthm pfd-u64-round-trip
  (equal (fn-cu-octets-value (fn-cu-u64-octets n) 0) (mod (nfix n) (expt 2 64)))
  :hints (("Goal" :in-theory (enable fn-cu-u64-octets)
           :use ((:instance pfd-octets-value-of-u64-aux (k 8) (n (nfix n)) (acc nil) (a 0)))))))
(local (defthm pfd-u64-aux-len
  (equal (len (fn-cu-u64-octets-aux k n acc)) (+ (nfix k) (len acc)))
  :hints (("Goal" :in-theory (enable fn-cu-u64-octets-aux)))))
(local (defthm pfd-u64-aux-octets
  (implies (and (natp n) (fn-cbor-octet-listp acc))
           (fn-cbor-octet-listp (fn-cu-u64-octets-aux k n acc)))
  :hints (("Goal" :induct (fn-cu-u64-octets-aux k n acc)
           :in-theory (enable fn-cu-u64-octets-aux fn-cbor-octet-listp fn-cbor-octetp)))))
(local (defthm pfd-u64-aux-true-listp
  (equal (true-listp (fn-cu-u64-octets-aux k n acc)) (true-listp acc))
  :hints (("Goal" :in-theory (enable fn-cu-u64-octets-aux)))))
(local (defthm pfd-u64-octets-shape
  (and (true-listp (fn-cu-u64-octets n)) (equal (len (fn-cu-u64-octets n)) 8)
       (fn-cbor-octet-listp (fn-cu-u64-octets n)))
  :hints (("Goal" :in-theory (enable fn-cu-u64-octets)))))
(local (defthm pfd-take-drop-append
  (implies (and (natp n) (true-listp x) (equal (len x) n))
           (and (equal (fn-pfp-take n (append x y)) x)
                (equal (fn-pfp-drop n (append x y)) y)))
  :hints (("Goal" :induct (fn-pfp-take n x) :in-theory (enable fn-pfp-take fn-pfp-drop)))))
(local (defthm pfd-fields-shape
  (and (true-listp (fn-pfp-fields ps)) (equal (len (fn-pfp-fields ps)) (* 8 (len ps))))
  :hints (("Goal" :induct (fn-pfp-fields ps) :in-theory (e/d (fn-pfp-fields) (fn-cu-u64-octets))))))
(local (defthm pfd-octet-listp-append
  (implies (and (fn-cbor-octet-listp x) (fn-cbor-octet-listp y))
           (fn-cbor-octet-listp (append x y)))
  :hints (("Goal" :in-theory (enable fn-cbor-octet-listp)))))
(local (defthm pfd-fields-octets
  (fn-cbor-octet-listp (fn-pfp-fields ps))
  :hints (("Goal" :induct (fn-pfp-fields ps)
           :in-theory (e/d (fn-pfp-fields fn-cbor-octet-listp) (fn-cu-u64-octets))))))
(local (defun pfd-ind (k ps)
  (declare (xargs :measure (nfix k)))
  (if (zp k) (list k ps) (pfd-ind (1- k) (cdr ps)))))
(local (defthm pfd-values-of-fields
  (implies (equal (len ps) k)
           (equal (fn-pfp-values k (fn-pfp-fields ps)) (pfd-u64-image ps)))
  :hints (("Goal" :induct (pfd-ind k ps)
           :in-theory (e/d (fn-pfp-values fn-pfp-fields pfd-u64-image) (fn-cu-u64-octets))))))
(local (defthm pfd-at-is-nth
  (equal (fn-pfr-at n xs) (nth n xs))
  :hints (("Goal" :in-theory (enable fn-pfr-at nth)))))
(local (defthm pfd-u64-mod-id
  (implies (and (natp x) (< x 18446744073709551616))
           (equal (mod (nfix x) 18446744073709551616) x))))
(local (defthm pfd-six-image
  (implies (and (true-listp p) (equal (len p) 6)
                (natp (nth 0 p)) (< (nth 0 p) (expt 2 64)) (natp (nth 1 p)) (< (nth 1 p) (expt 2 64))
                (natp (nth 2 p)) (< (nth 2 p) (expt 2 64)) (natp (nth 3 p)) (< (nth 3 p) (expt 2 64))
                (natp (nth 4 p)) (< (nth 4 p) (expt 2 64)) (natp (nth 5 p)) (< (nth 5 p) (expt 2 64)))
           (equal (pfd-u64-image p) p))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(pfd-u64-image nth len pfd-u64-mod-id true-listp
                                        (:e expt) car-cons cdr-cons zp (:e zp) natp
                                        fix (:e fix) cons-car-cdr (:type-prescription len)
                                        (:e binary-+))
                                      (theory 'minimal-theory))
           :expand ((pfd-u64-image p) (pfd-u64-image (cdr p)) (pfd-u64-image (cddr p))
                    (pfd-u64-image (cdddr p)) (pfd-u64-image (cddddr p))
                    (pfd-u64-image (cdr (cddddr p)))
                    (len p) (len (cdr p)) (len (cddr p)) (len (cdddr p)) (len (cddddr p))
                    (len (cdr (cddddr p))) (len (cddr (cddddr p)))
                    (true-listp p) (true-listp (cdr p)) (true-listp (cddr p)) (true-listp (cdddr p))
                    (true-listp (cddddr p)) (true-listp (cdr (cddddr p))) (true-listp (cddr (cddddr p)))
                    (true-listp (cdddr (cddddr p))))))))
(local (defthm pfd-policy-image
  (implies (fn-pfr-policy-p p) (and (equal (pfd-u64-image p) p) (equal (len p) 6)))
  :hints (("Goal" :in-theory (e/d (fn-pfr-policy-p fn-pfr-slots fn-pfr-bookkeeping)
                                  (fn-pfr-fixed-backing pfd-u64-image nth))
           :do-not-induct t :use (pfd-six-image)))))

; The reader is the writer's inverse, for every policy.
(defthm fn-pfp-read-of-write
  (implies (fn-pfr-policy-p policy)
           (equal (fn-pfp-read t (fn-pfp-write policy)) policy))
  :hints (("Goal" :in-theory (e/d (fn-pfp-read fn-pfp-write)
                                  (fn-pfr-policy-p fn-pfp-fields fn-pfp-values fn-pfp-take fn-pfp-drop
                                   pfd-u64-image))
           :use ((:instance pfd-take-drop-append (n 4) (x (fn-pfp-prefix)) (y (fn-pfp-fields policy)))
                 pfd-policy-image))))

; KEYSTONE: what init writes decodes to the default.
(defthm fn-pfd-default-decodes-to-itself
  (equal (fn-pfp-read t (fn-pfp-default-octets values))
         (fn-pfp-default-policy values))
  :hints (("Goal" :in-theory (e/d (fn-pfp-default-octets)
                                  (fn-pfp-default-policy fn-pfp-read fn-pfp-write)))))

; -----------------------------------------------------------------------------
;; Every profile's record bound is within the codec ceiling (an invalid
;; profile reads as no bound), so the clamp never binds.
(local (defthm pfd-record-bound
  (<= (nfix (fn-bs-profile-max-record-octets values)) *fn-cbor-max-uint*)
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-bs-profile-max-record-octets fn-bs-profile-field
                                     fn-bs-profile-of fn-bs-profile-validp
                                     fn-bs-profile-invalid-reason)))))

; KEYSTONE: the spool holds one whole batch of the store's records: the first
; record at the profile's record bound and the quantum beyond it.
(defthm fn-pfd-default-spools-one-batch
  (<= (+ (nfix (fn-bs-profile-max-record-octets values)) *fn-cu-request-quantum*)
      (fn-pfr-at 4 (fn-pfp-default-policy values)))
  :hints (("Goal" :in-theory (e/d (fn-pfp-default-policy fn-pfd-policy fn-pfd-spool)
                                  (fn-pfd-heap fn-pfd-work fn-bs-profile-max-record-octets
                                   fn-bs-profile-max-history-octets))
           :use (pfd-record-bound))))

; -----------------------------------------------------------------------------
; The launch cost.  The launcher's probe (fn-pfr-extend-reservation) grows the
; runtime's dynamic space by the policy's heap E and adds its workers' threads.
; For the default that adds at most (fn-pfd-launch-extra STACK) octets over
; the base run reservation (BASE = (:heap MB _ _ STACK THREADS)): E; the
; re-solve's nursery slack, at most twice the least nursery trigger and
; ceiling((E + 15) / 7) (pfd-grow-tight: the trigger is at least D/16 or the
; nursery cap is already in D); one MiB of rounding; one worker's stack and
; runtime (4 MiB).  22 MiB beside a 1 MiB stack (it was ~134 MiB: twice the
; nursery cap).
(defun fn-pfd-launch-extra (stack-kib)
  (declare (xargs :guard t))
  (+ (fn-pfd-heap)
     (* 2 *fn-heap-nursery-least-octets*)
     (ceiling (+ (fn-pfd-heap) 15) 7)
     *fn-heap-mib*
     (* *fn-pfd-workers*
        (+ (* 1024 (nfix stack-kib)) *fn-heap-thread-runtime-octets*))))

(defun fn-pfd-base-octets (base core)
  (declare (xargs :guard t))
  (fn-heap-reservation-octets (fn-pfr-at 1 base) core (fn-pfr-at 4 base) (fn-pfr-at 5 base)))

(local (defthm pfd-ceil-mono
  (implies (and (rationalp a) (rationalp b) (<= a b)) (<= (ceiling a 7) (ceiling b 7)))
  :rule-classes nil))
(local (defthm pfd-ceil-shift
  (implies (and (integerp k) (rationalp a)) (equal (ceiling (+ a (* 7 k)) 7) (+ k (ceiling a 7))))
  :rule-classes nil))
(local (defthm pfd-ceil8-split
  (implies (natp x) (equal (ceiling (* 8 x) 7) (+ x (ceiling x 7))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance pfd-ceil-shift (a x) (k x)))
           :in-theory (disable ceiling)))))
(local (defthm pfd-floor16
  (implies (natp d) (and (<= (* 16 (floor d 16)) d) (<= d (+ 15 (* 16 (floor d 16))))
                         (natp (floor d 16))))
  :rule-classes nil))
(local (defthm pfd-tiny-case
  (implies (and (natp d) (natp e) (natp l))
           (<= (ceiling (* 8 e) 7) (+ d e (* 2 l) (ceiling (+ e 15) 7))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable ceiling)
           :use ((:instance pfd-ceil8-split (x e))
                 (:instance pfd-ceil-mono (a e) (b (+ e 15))))))))
(local (defthm pfd-small-linear
  (implies (and (rationalp x) (rationalp cx) (rationalp cb) (rationalp ce) (rationalp d)
                (rationalp e) (rationalp tt) (rationalp l) (<= 0 l)
                (equal c8 (+ x cx)) (<= cx cb) (equal cb (+ (* 2 tt) ce))
                (equal x (+ (- d (* 2 tt)) e)))
           (<= c8 (+ d e (* 2 l) ce)))
  :rule-classes nil))
(local (defthm pfd-small-case
  (implies (and (natp d) (natp e) (natp l) (natp tt) (<= l tt) (<= (* 2 tt) d)
                (<= d (+ 15 (* 16 tt))))
           (<= (ceiling (* 8 (+ (- d (* 2 tt)) e)) 7)
               (+ d e (* 2 l) (ceiling (+ e 15) 7))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories '(natp rationalp-implies-acl2-numberp
                                               (:type-prescription ceiling))
                                             (theory 'minimal-theory))
           :use ((:instance pfd-ceil8-split (x (+ (- d (* 2 tt)) e)))
                 (:instance pfd-ceil-mono (a (+ (- d (* 2 tt)) e)) (b (+ (+ e 15) (* 7 (* 2 tt)))))
                 (:instance pfd-ceil-shift (a (+ e 15)) (k (* 2 tt)))
                 (:instance pfd-small-linear (x (+ (- d (* 2 tt)) e))
                            (cx (ceiling (+ (- d (* 2 tt)) e) 7))
                            (cb (ceiling (+ (+ e 15) (* 7 (* 2 tt))) 7))
                            (ce (ceiling (+ e 15) 7))
                            (c8 (ceiling (* 8 (+ (- d (* 2 tt)) e)) 7)))))
          )))
(local (defthm pfd-k8-bound
  (implies (and (natp d) (natp e) (natp fd) (natp cc)
                (equal tt (max 8388608 (min cc fd)))
                (<= d (+ 15 (* 16 tt))))
           (<= (ceiling (* 8 (nfix (+ (nfix (+ d (- (* 2 tt)))) e))) 7)
               (+ d e 16777216 (ceiling (+ e 15) 7))))
  :rule-classes nil
  :hints (("Goal" :nonlinearp nil :do-not-induct t
           :cases ((<= (* 2 tt) d))
           :in-theory (union-theories '(nfix natp max min fix unicity-of-0 (:e binary-*)
                                        (:type-prescription ceiling))
                                      (theory 'minimal-theory))
           :use ((:instance pfd-small-case (l 8388608))
                 (:instance pfd-tiny-case (l 8388608)))))))
(local (defthm pfd-trigger-def2
  (implies (natp d)
           (equal (fn-heap-nursery-trigger d n)
                  (max 8388608 (min (nfix n) (floor d 16)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-heap-nursery-trigger)))))
(local (defthm pfd-grow-linear3
  (implies (and (natp d) (natp e) (natp fd) (natp cc) (natp ce) (rationalp k8)
                (equal tt (max 8388608 (min cc fd)))
                (<= (* 16 fd) d) (<= d (+ 15 (* 16 fd)))
                (implies (<= d (+ 15 (* 16 tt))) (<= k8 (+ d e 16777216 ce))))
           (<= (max (+ d e)
                    (max (+ (nfix (+ (nfix (+ d (- (* 2 tt)))) e)) 16777216)
                         (min k8 (+ (nfix (+ (nfix (+ d (- (* 2 tt)))) e)) (* 2 (max 8388608 cc))))))
               (+ d e 16777216 ce)))
  :rule-classes nil
  :hints (("Goal" :nonlinearp nil :in-theory (enable max min nfix)))))
(local (defthm pfd-ceil-natp
  (implies (natp e) (natp (ceiling (+ e 15) 7)))
  :rule-classes nil))
(local (defthm pfd-grow-tight
  (<= (fn-heap-grow-runtime-dynamic d e cap)
      (+ (nfix d) (nfix e) 16777216 (ceiling (+ (nfix e) 15) 7)))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (union-theories '(fn-heap-grow-runtime-dynamic fn-heap-with-nursery
                                        (:type-prescription ceiling) (:type-prescription nfix)
                                        (:type-prescription floor) (:type-prescription max)
                                        (:type-prescription min) natp (:e binary-*))
                                      (theory 'minimal-theory))
           :use ((:instance pfd-floor16 (d (nfix d)))
                 (:instance pfd-ceil-natp (e (nfix e)))
                 (:instance pfd-trigger-def2 (d (nfix d)) (n cap))
                 (:instance pfd-k8-bound (d (nfix d)) (e (nfix e)) (fd (floor (nfix d) 16))
                            (cc (nfix cap)) (tt (fn-heap-nursery-trigger (nfix d) cap)))
                 (:instance pfd-grow-linear3 (d (nfix d)) (e (nfix e)) (fd (floor (nfix d) 16))
                            (cc (nfix cap)) (ce (ceiling (+ (nfix e) 15) 7))
                            (tt (fn-heap-nursery-trigger (nfix d) cap))
                            (k8 (ceiling (* 8 (nfix (+ (nfix (+ (nfix d) (- (* 2 (fn-heap-nursery-trigger (nfix d) cap))))) (nfix e)))) 7))))))))
(local (defthm pfd-floor-mul
  (implies (and (natp y) (posp m)) (<= (* m (floor y m)) y))
  :rule-classes nil))
(local (defthm pfd-mb-of-bound
  (<= (* *fn-heap-mib* (fn-heap-mb-of x)) (+ (nfix x) *fn-heap-mib*))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-heap-mb-of) (floor))
           :use ((:instance pfd-floor-mul (y (+ (nfix x) (1- *fn-heap-mib*))) (m *fn-heap-mib*)))))))
(local (defthm pfd-default-fields
  (and (equal (fn-pfr-at 0 (fn-pfp-default-policy values)) (fn-pfd-heap))
       (equal (fn-pfr-at 3 (fn-pfp-default-policy values)) *fn-pfd-workers*)
       (fn-pfp-default-policy values))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-pfp-default-policy fn-pfd-policy)
                                  (fn-pfd-heap fn-pfd-spool fn-pfd-work pfd-at-is-nth))))))

; KEYSTONE: on a machine that holds the store's run reservation and the
; default's launch extra, the launcher's probe admits the default.
(defthm fn-pfd-default-launches-where-its-extra-fits
  (implies (and (equal (fn-pfr-at 0 base) :heap)
                (<= (+ (fn-pfd-base-octets base core)
                       (fn-pfd-launch-extra (fn-pfr-at 4 base)))
                    (fn-heap-machine-octets observations)))
           (equal (fn-pfr-at 0 (fn-pfr-extend-reservation
                                base (fn-pfp-default-policy values) core observations))
                  :heap))
  :hints (("Goal" :in-theory (e/d (fn-pfr-extend-reservation fn-pfd-base-octets
                                   fn-pfd-launch-extra fn-heap-reservation-octets)
                                  (fn-heap-grow-runtime-dynamic fn-heap-mb-of fn-pfr-policy-p
                                   fn-pfp-default-policy fn-heap-machine-octets fn-pfd-heap
                                   pfd-at-is-nth))
           :use (fn-pfd-default-is-a-policy pfd-default-fields
                 (:instance pfd-grow-tight (d (* *fn-heap-mib* (nfix (fn-pfr-at 1 base))))
                            (e (fn-pfd-heap))
                            (cap (* *fn-heap-mib* (fn-profile-limit :gc-nursery-mib))))
                 (:instance pfd-mb-of-bound
                            (x (fn-heap-grow-runtime-dynamic
                                (* *fn-heap-mib* (nfix (fn-pfr-at 1 base)))
                                (fn-pfd-heap)
                                (* *fn-heap-mib* (fn-profile-limit :gc-nursery-mib)))))))))

; =============================================================================
; Step 2b.2: init reserves the default's launch.  Every store init publishes
; carries the default profile (step 2), so every launch takes the peer
; extension; init now judges the store against the machine LESS the
; default's launch extra.  The thread stack is one figure for every profile
; (fn-heap-stack-octets ignores it), so the extra is one number,
; fn-pfd-launch-reserve (22 MiB).  The reservation is one more observation in
; init's LIMITS -- the machine init would judge, less the reserve -- so
; books/heap-reservation.lisp's init decision is called unchanged and its
; budget, choice and refusals all see the smaller machine.
(defun fn-pfd-launch-reserve ()
  (declare (xargs :guard t))
  (fn-pfd-launch-extra (fn-heap-stack-kib nil)))

(defun fn-pfd-init-limits (physical limits budget-mb)
  (declare (xargs :guard t))
  (let ((m (fn-heap-machine-octets
            (fn-heap-init-observations physical limits
                                       (fn-heap-init-explicit-budget budget-mb)))))
    (if (zp m)
        limits
      (cons (max 1 (- m (fn-pfd-launch-reserve))) limits))))

; The decision the host calls for `init' (host/native/heap.lisp
; fnn-heap-init-decision), in fn-heap-init-decide's shape.
(defun fn-pfd-init-decide (request core nursery physical limits budget-mb sizing-word)
  (declare (xargs :guard t))
  (fn-heap-init-decide request core nursery physical
                       (fn-pfd-init-limits physical limits budget-mb)
                       budget-mb sizing-word))

(local (defthm pfd-run-figure-at-most-full
  (<= (fn-heap-operation-figure-octets :run p core nursery observed)
      (fn-heap-operation-figure-octets :run p core nursery nil))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-heap-operation-figure-octets fn-heap-operation-observation)))))
(local (defthm pfd-mb-of-monotone
  (implies (<= (nfix a) (nfix b)) (<= (fn-heap-mb-of a) (fn-heap-mb-of b)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-heap-mb-of)))))
(local (defthm pfd-run-base-within-init
  (let ((b (fn-heap-reserve-operation-decide :run p core nursery obs k observed)))
    (implies (and (fn-bs-profile-admittedp p) (equal (car b) :heap))
             (and (<= (fn-pfd-base-octets b core) (fn-heap-init-reservation-octets p core nursery))
                  (equal (fn-pfr-at 4 b) (fn-heap-stack-kib nil)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-heap-reserve-operation-decide fn-heap-reserve-of
                                   fn-heap-operation-decide fn-pfd-base-octets
                                   fn-heap-init-reservation-octets fn-heap-reservation-octets
                                   fn-heap-thread-count fn-heap-stack-kib fn-heap-stack-octets
                                   fn-heap-decision-mb)
                                  (fn-heap-operation-figure-octets fn-heap-mb-of
                                   fn-bs-profile-admittedp fn-heap-machine-octets
                                   fn-heap-profile-word))
           :use ((:instance pfd-run-figure-at-most-full)
                 (:instance pfd-mb-of-monotone
                            (a (fn-heap-operation-figure-octets :run p core nursery observed))
                            (b (fn-heap-operation-figure-octets :run p core nursery nil))))))))
(local (defthm pfd-init-res-above-one
  (< 1 (fn-heap-init-reservation-octets p core nursery))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-heap-init-reservation-octets fn-heap-reservation-octets)
                                  (fn-heap-mb-of fn-heap-operation-figure-octets))))))
(local (defthm pfd-init-limits-budget
  (let ((m (fn-heap-machine-octets
            (fn-heap-init-observations physical limits (fn-heap-init-explicit-budget budget-mb)))))
    (<= (fn-heap-machine-octets
         (fn-heap-init-observations physical (fn-pfd-init-limits physical limits budget-mb)
                                    (fn-heap-init-explicit-budget budget-mb)))
        (if (zp m) 0 (max 1 (- m (fn-pfd-launch-reserve))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-pfd-init-limits fn-heap-init-observations)
                                  (fn-heap-machine-octets fn-pfd-launch-reserve
                                   fn-heap-available-physical-octets fn-heap-init-explicit-budget))
           :cases ((zp (fn-heap-machine-octets
                        (fn-heap-init-observations physical limits
                                                   (fn-heap-init-explicit-budget budget-mb))))))
          ("Subgoal 2" :use ((:instance fn-heap-machine-octets-is-at-most-each-observation
                              (x (max 1 (- (fn-heap-machine-octets
                                            (fn-heap-init-observations physical limits
                                                                       (fn-heap-init-explicit-budget budget-mb)))
                                           (fn-pfd-launch-reserve))))
                              (observations (fn-heap-init-observations
                                             physical (fn-pfd-init-limits physical limits budget-mb)
                                             (fn-heap-init-explicit-budget budget-mb)))))))))
(local (defthm pfd-machine-of-one-more
  (implies (posp (fn-heap-machine-octets (cons x rest)))
           (<= (fn-heap-machine-octets (cons x (cons y rest)))
               (fn-heap-machine-octets (cons x rest))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable fn-heap-machine-octets-of-cons)))))
(local (defthm pfd-init-limits-machine
  (implies (and (posp (fn-heap-machine-octets
                       (fn-heap-init-observations physical limits (fn-heap-init-explicit-budget budget-mb))))
                (posp (fn-heap-machine-octets (cons physical limits))))
           (and (posp (fn-heap-machine-octets (cons physical (fn-pfd-init-limits physical limits budget-mb))))
                (<= (fn-heap-machine-octets (cons physical (fn-pfd-init-limits physical limits budget-mb)))
                    (fn-heap-machine-octets (cons physical limits)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-pfd-init-limits) (fn-heap-machine-octets fn-pfd-launch-reserve
                                                        fn-heap-init-observations))
           :use ((:instance pfd-machine-of-one-more (x physical) (rest limits)
                            (y (max 1 (- (fn-heap-machine-octets
                                          (fn-heap-init-observations physical limits
                                                                     (fn-heap-init-explicit-budget budget-mb)))
                                         (fn-pfd-launch-reserve)))))
                 (:instance fn-heap-machine-octets-posp-with-a-posp-member
                            (x (max 1 (- (fn-heap-machine-octets
                                          (fn-heap-init-observations physical limits
                                                                     (fn-heap-init-explicit-budget budget-mb)))
                                         (fn-pfd-launch-reserve))))
                            (obs (cons physical (fn-pfd-init-limits physical limits budget-mb)))))))))

; KEYSTONE: a store init writes within this machine's budget (HELDP) is one
; whose launch with the default peer flight profile is admitted on the same
; machine (the physical memory and the same limits), whatever the store then
; holds (OBSERVED) and at any owner bound (K): the launcher's probe extends
; the run's reservation by the default and it still fits.  Scope: the
; cold-read, page-read startup and output extensions the launcher also
; applies are not counted by init (they were not before this step either);
; a `--budget' store made for another machine (HELDP nil) is not covered.
(defthm fn-pfd-init-reserves-the-default-launch
  (implies (and (and (equal (car (fn-pfd-init-decide request core nursery physical limits
                                                     budget-mb sizing-word))
                            :init)
                     (nth 6 (fn-pfd-init-decide request core nursery physical limits
                                                budget-mb sizing-word)))
                (posp (fn-heap-machine-octets (cons physical limits))))
           (equal (fn-pfr-at 0 (fn-pfr-extend-reservation
                                (fn-heap-reserve-operation-decide
                                 :run (fn-bs-profile-resolve
                                       (fn-heap-init-decision-request
                                        (fn-pfd-init-decide request core nursery physical limits
                                                            budget-mb sizing-word))
                                       nil)
                                 core nursery (cons physical limits) k observed)
                                (fn-pfp-default-policy values) core (cons physical limits)))
                  :heap))
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn-pfd-init-decide fn-pfd-launch-reserve posp natp zp max pfd-at-is-nth nth (:e zp))
                                      (theory 'minimal-theory))
           :use ((:instance fn-heap-init-decide-fits-the-budget-and-the-machine (limits (fn-pfd-init-limits physical limits budget-mb)))
                 (:instance pfd-init-limits-budget)
                 (:instance pfd-init-res-above-one (p (fn-bs-profile-resolve (fn-heap-init-decision-request (fn-heap-init-decide request core nursery physical (fn-pfd-init-limits physical limits budget-mb) budget-mb sizing-word)) nil)))
                 (:instance fn-heap-init-budget-is-under-the-machine (explicit (fn-heap-init-explicit-budget budget-mb)))
                 (:instance pfd-init-limits-machine)
                 (:instance fn-heap-reserve-full-store-accepts-on-a-larger-machine
                            (p (fn-bs-profile-resolve (fn-heap-init-decision-request (fn-heap-init-decide request core nursery physical (fn-pfd-init-limits physical limits budget-mb) budget-mb sizing-word)) nil)) (k (fn-heap-reserve-init-connections))
                            (obs1 (cons physical (fn-pfd-init-limits physical limits budget-mb))) (obs2 (cons physical limits)))
                 (:instance fn-heap-init-accepted-store-always-reopens
                            (p (fn-bs-profile-resolve (fn-heap-init-decision-request (fn-heap-init-decide request core nursery physical (fn-pfd-init-limits physical limits budget-mb) budget-mb sizing-word)) nil)) (obs (cons physical limits))
                            (k (fn-heap-reserve-init-connections)) (k2 k))
                 (:instance pfd-run-base-within-init (p (fn-bs-profile-resolve (fn-heap-init-decision-request (fn-heap-init-decide request core nursery physical (fn-pfd-init-limits physical limits budget-mb) budget-mb sizing-word)) nil)) (obs (cons physical limits)))
                 (:instance fn-pfd-default-launches-where-its-extra-fits
                            (base (fn-heap-reserve-operation-decide :run (fn-bs-profile-resolve (fn-heap-init-decision-request (fn-heap-init-decide request core nursery physical (fn-pfd-init-limits physical limits budget-mb) budget-mb sizing-word)) nil) core nursery (cons physical limits) k observed)) (observations (cons physical limits)))))))
