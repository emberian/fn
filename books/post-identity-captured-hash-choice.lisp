; UNHOOKED stage 0 (2026-10-01): depends on the reverted acceptance-binding field (planning/design-store-representation-2026-10-01.md section 5, D43): the captured-identity chain over the held binding gate is parked (review 2026-10-01 F01: KEEP-PARKED); not in the Makefile check roots or any image world.
; Proof-only retained incoming-agent comparison and exact tombstone hash choice.
(in-package "ACL2")
(include-book "post-identity-captured")
(defun fn-pic-retained-agent (c incoming)
 (take (- (fn-pic-at 2 (fn-pic-get agent c)) (fn-pic-at 1 (fn-pic-get agent c)))
       (nthcdr (fn-pic-at 1 (fn-pic-get agent c)) incoming)))
(defun fn-pic-retained-source-choicep (c incoming held)
 (and (fn-rcl-tomb-sourcep held) (fn-pic-get incoming-desc c)
      (equal (fn-pic-retained-agent c incoming) (fn-rcl-tomb-agent held))))
(defun fn-pic-choice-contextp (c incoming held)
 (let ((a (fn-pic-get agent c)))
  (and (true-listp incoming) (true-listp held)
       (equal (fn-pic-get incoming-n c) (len incoming))
       (equal (fn-pic-get held-n c) (len held)) (<= *fn-rcl-tombstone-fixed* (len held))
       (natp (fn-pic-at 1 a)) (natp (fn-pic-at 2 a))
       (<= (fn-pic-at 1 a) (fn-pic-at 2 a)) (<= (fn-pic-at 2 a) (len incoming))
       (or (not (fn-pic-get incoming-desc c))
           (fn-pic-spanp (fn-pic-get incoming-desc c) (len incoming))))))
(defun fn-pic-choice-productp (c incoming held)
 (let* ((left (fn-pic-retained-agent c incoming)) (right (fn-rcl-tomb-agent held))
        (phase (fn-pic-get phase c)) (pos (fn-pic-get pos c)))
  (and (fn-pic-choice-contextp c incoming held)
       (member-eq phase '(:tomb-agent-held :tomb-agent-incoming))
       (fn-rcl-tomb-sourcep held) (fn-pic-get incoming-desc c)
       (equal (len left) (len right)) (natp pos) (<= pos (len left))
       (equal (take pos left) (take pos right))
       (implies (equal phase :tomb-agent-incoming)
        (and (< pos (len left)) (equal (fn-pic-get cached c) (nth pos right)))))))
(defun fn-pic-choice-outcomep (c incoming held)
 (or (fn-pic-choice-productp c incoming held)
     (and (equal (fn-pic-get phase c) :digest-begin)
          (equal (fn-pic-get digest-base c) (if (fn-pic-retained-source-choicep c incoming held) 41 9))
          (equal (fn-pic-get digest-desc c)
                 (if (fn-pic-retained-source-choicep c incoming held)
                     (fn-pic-get incoming-desc c) '(0 0 0))))))
(defun fn-pic-choice-observationp (c observation incoming held)
 (let ((d (fn-pic-demand c)))
  (and (fn-pic-observation-okp c d observation)
       (or (equal d :control)
           (equal (fn-pic-observed-byte d observation)
            (case (fn-pic-get phase c)
             (:tomb-flag (nth 8 held))
             (:tomb-agent-held (nth (fn-pic-get pos c) (fn-rcl-tomb-agent held)))
             (:tomb-agent-incoming (nth (fn-pic-get pos c) (fn-pic-retained-agent c incoming)))))))))
(local (defthm fn-pic-ch-at-is-nth
 (implies (natp i) (equal (fn-pic-at i x) (nth i x)))
 :hints (("Goal" :induct (fn-pic-at i x) :in-theory (enable fn-pic-at nth)))))
(local (defthm fn-pic-ch-drop-is-tail
 (implies (and (natp n) (true-listp x)) (equal (fn-rcl-drop n x) (nthcdr n x)))
 :hints (("Goal" :induct (fn-rcl-drop n x) :in-theory (enable fn-rcl-drop nthcdr)))))
(local (defthm fn-pic-ch-len-take
 (implies (natp n) (equal (len (take n x)) n))))
(local (defthm fn-pic-ch-len-tail
 (implies (natp n) (equal (len (nthcdr n x)) (nfix (- (len x) n))))
 :hints (("Goal" :induct (nthcdr n x) :in-theory (enable nthcdr len nfix)))))
(local (defthm fn-pic-ch-nth-of-tail
 (implies (and (natp i) (natp j)) (equal (nth i (nthcdr j x)) (nth (+ i j) x)))
 :hints (("Goal" :induct (nthcdr j x) :in-theory (enable nthcdr nth)))))
(local (defthm fn-pic-ch-consp-of-take
 (implies (posp n) (consp (take n x))) :hints (("Goal" :expand ((take n x))))))
(local (defthm fn-pic-ch-car-of-take
 (implies (posp n) (equal (car (take n x)) (car x))) :hints (("Goal" :expand ((take n x))))))
(local (defthm fn-pic-ch-cdr-of-take
 (implies (posp n) (equal (cdr (take n x)) (take (1- n) (cdr x)))) :hints (("Goal" :expand ((take n x))))))
(local (defun fn-pic-ch-nth-take-induct (i n x)
 (declare (xargs :measure (nfix i) :guard (and (natp i) (natp n))))
 (if (or (zp i) (zp n)) x
  (fn-pic-ch-nth-take-induct (1- i) (1- n) (if (consp x) (cdr x) nil)))))
(local (defthm fn-pic-ch-nth-of-take
 (implies (and (natp i) (natp n) (< i n)) (equal (nth i (take n x)) (nth i x)))
 :hints (("Goal" :induct (fn-pic-ch-nth-take-induct i n x) :in-theory (enable nth take)))))
(local (defthm fn-pic-ch-take-at-length
 (implies (true-listp x) (equal (take (len x) x) x))
 :hints (("Goal" :induct (len x) :in-theory (enable take len)))))
(local (defthm fn-pic-ch-take-next
 (implies (natp n) (equal (take (+ 1 n) x) (append (take n x) (list (nth n x)))))
 :hints (("Goal" :induct (take n x) :in-theory (enable take nth binary-append)))))
(local (defthm fn-pic-ch-equal-prefix-advance
 (implies (and (natp n) (equal (take n x) (take n y)) (equal (nth n x) (nth n y)))
   (equal (take (+ 1 n) x) (take (+ 1 n) y)))
 :hints (("Goal" :in-theory (disable take nth)))))
(local (defthm fn-pic-ch-completed-prefix-is-equality
 (implies (and (true-listp x) (true-listp y) (equal n (len x)) (equal n (len y))
               (equal (take n x) (take n y))) (equal x y))
 :rule-classes nil
 :hints (("Goal" :use ((:instance fn-pic-ch-take-at-length) (:instance fn-pic-ch-take-at-length (x y)))
 :in-theory (disable fn-pic-ch-take-at-length take)))))
(local (defthm fn-pic-ch-different-cell-implies-different
 (implies (not (equal (nth n x) (nth n y))) (not (equal x y))) :rule-classes nil))
(local (defthm fn-pic-ch-agent-length
 (implies (and (natp (fn-pic-at 1 (fn-pic-get agent c)))
               (natp (fn-pic-at 2 (fn-pic-get agent c)))
               (<= (fn-pic-at 1 (fn-pic-get agent c)) (fn-pic-at 2 (fn-pic-get agent c))))
  (equal (len (fn-pic-retained-agent c incoming))
    (- (fn-pic-at 2 (fn-pic-get agent c)) (fn-pic-at 1 (fn-pic-get agent c)))))
 :hints (("Goal" :in-theory (e/d (fn-pic-choice-contextp fn-pic-retained-agent)
   (fn-pic-at fn-pic-spanp take nth nthcdr))))))
(local (defthm fn-pic-ch-tomb-agent-length
 (implies (and (true-listp held) (<= 145 (len held)))
  (equal (len (fn-rcl-tomb-agent held)) (- (len held) 145)))
 :hints (("Goal" :in-theory (e/d (fn-rcl-tomb-agent) (fn-rcl-drop nthcdr))))))
(local (defthm fn-pic-ch-retained-agent-of-other-update
 (implies (and (natp i) (not (equal i 10)))
  (equal (fn-pic-retained-agent (update-nth i value c) incoming)
         (fn-pic-retained-agent c incoming)))
 :hints (("Goal" :in-theory (e/d (fn-pic-retained-agent)
   (fn-pic-at take nth nthcdr update-nth))))))
(local (defthm fn-pic-ch-tomb-agent-is-proper
 (implies (true-listp held) (true-listp (fn-rcl-tomb-agent held)))
 :hints (("Goal" :in-theory (e/d (fn-rcl-tomb-agent) (fn-rcl-drop nthcdr))))))
(defthm fn-pic-feed-funded-preserves-exact-tombstone-hash-choice
 (implies (and (fn-pic-choice-productp c incoming held)
               (fn-pic-choice-observationp c observation incoming held))
  (fn-pic-choice-outcomep (mv-nth 1 (fn-pic-feed-funded c observation fuel)) incoming held))
 :rule-classes nil
 :hints (("Goal" :use
 ((:instance fn-pic-ch-completed-prefix-is-equality
   (x (fn-pic-retained-agent c incoming)) (y (fn-rcl-tomb-agent held)) (n (fn-pic-get pos c)))
  (:instance fn-pic-ch-different-cell-implies-different
   (x (fn-pic-retained-agent c incoming)) (y (fn-rcl-tomb-agent held)) (n (fn-pic-get pos c)))
  (:instance fn-pic-ch-equal-prefix-advance
   (x (fn-pic-retained-agent c incoming)) (y (fn-rcl-tomb-agent held)) (n (fn-pic-get pos c))))
 :in-theory (e/d (fn-pic-choice-productp fn-pic-choice-outcomep fn-pic-choice-contextp
                 fn-pic-choice-observationp fn-pic-retained-source-choicep
                 fn-pic-feed-funded fn-pic-feed fn-pic-demand fn-pic-hash-start)
  (fn-pic-at fn-pic-observation-okp fn-pic-observed-byte fn-pic-spanp fn-rcl-drop
   fn-pic-retained-agent fn-rcl-tomb-agent fn-rcl-tomb-sourcep
   fn-pic-ch-equal-prefix-advance fn-pic-ch-take-next take nth nthcdr update-nth)))))
(local (defthm fn-pic-ch-agent-byte-is-source-byte
 (implies (and (fn-pic-choice-contextp c incoming held) (natp pos)
               (< pos (len (fn-pic-retained-agent c incoming))))
  (equal (nth pos (fn-pic-retained-agent c incoming))
         (nth (+ (fn-pic-at 1 (fn-pic-get agent c)) pos) incoming)))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d (fn-pic-choice-contextp fn-pic-retained-agent)
   (fn-pic-at fn-pic-spanp nth take nthcdr))))))
(local (defthm fn-pic-ch-nth-is-octet
 (implies (and (fn-cbor-octet-listp x) (natp i) (< i (len x))) (unsigned-byte-p 8 (nth i x)))
 :hints (("Goal" :induct (nth i x)
  :in-theory (enable nth fn-cbor-octet-listp fn-cbor-octetp unsigned-byte-p)))))
(local (defthm fn-pic-ch-incoming-observation-is-exact
 (implies (and (fn-pic-choice-productp c fn-octets held) (fn-cbor-octet-listp fn-octets)
               (equal (fn-pic-get phase c) :tomb-agent-incoming))
  (fn-pic-choice-observationp c
   (list :incoming-byte (fn-pic-get incoming-token c)
    (+ (fn-pic-at 1 (fn-pic-get agent c)) (fn-pic-get pos c))
    (fn-octets-get (+ (fn-pic-at 1 (fn-pic-get agent c)) (fn-pic-get pos c)) fn-octets)) fn-octets held))
 :hints (("Goal" :use
  ((:instance fn-pic-ch-agent-byte-is-source-byte (incoming fn-octets) (pos (fn-pic-get pos c)))
   (:instance fn-pic-ch-nth-is-octet (x fn-octets)
    (i (+ (fn-pic-at 1 (fn-pic-get agent c)) (fn-pic-get pos c)))))
 :in-theory (e/d (fn-pic-choice-productp fn-pic-choice-contextp fn-pic-choice-observationp
      fn-pic-demand fn-pic-observation-okp fn-pic-observed-byte fn-octets-get)
  (fn-pic-at fn-pic-retained-agent fn-rcl-tomb-agent fn-rcl-tomb-sourcep fn-pic-spanp
   fn-pic-ch-nth-is-octet nth take nthcdr unsigned-byte-p))))))
(local (defthm fn-pic-ch-control-observation-is-exact
 (implies (and (fn-pic-choice-productp c incoming held)
               (equal (fn-pic-get phase c) :tomb-agent-held)
               (<= (len (fn-pic-retained-agent c incoming)) (fn-pic-get pos c)))
  (fn-pic-choice-observationp c :control incoming held))
 :hints (("Goal" :in-theory (e/d (fn-pic-choice-productp fn-pic-choice-contextp
      fn-pic-choice-observationp fn-pic-demand fn-pic-observation-okp)
  (fn-pic-at fn-pic-retained-agent fn-rcl-tomb-agent fn-rcl-tomb-sourcep fn-pic-spanp nth take nthcdr))))))
(local (defthm fn-pic-ch-product-outcome-unfolds
 (implies (fn-pic-choice-productp c incoming held) (fn-pic-choice-outcomep c incoming held))
 :rule-classes nil
 :hints (("Goal" :in-theory (e/d (fn-pic-choice-outcomep) (fn-pic-choice-productp))))))
(defthm fn-pic-next-preserves-exact-tombstone-hash-choice
 (implies (and (fn-pic-choice-productp c fn-octets held) (fn-cbor-octet-listp fn-octets))
  (fn-pic-choice-outcomep (mv-nth 1 (fn-pic-next c fuel fn-octets)) fn-octets held))
 :rule-classes nil
 :hints (("Goal" :use
 ((:instance fn-pic-feed-funded-preserves-exact-tombstone-hash-choice (incoming fn-octets) (observation :control))
  (:instance fn-pic-feed-funded-preserves-exact-tombstone-hash-choice (incoming fn-octets) (fuel (- fuel 1))
   (observation (list :incoming-byte (fn-pic-get incoming-token c)
    (+ (fn-pic-at 1 (fn-pic-get agent c)) (fn-pic-get pos c))
    (fn-octets-get (+ (fn-pic-at 1 (fn-pic-get agent c)) (fn-pic-get pos c)) fn-octets))))
  fn-pic-ch-incoming-observation-is-exact
  (:instance fn-pic-ch-control-observation-is-exact (incoming fn-octets))
  (:instance fn-pic-ch-product-outcome-unfolds (incoming fn-octets)))
 :in-theory (e/d (fn-pic-next fn-pic-demand fn-pic-choice-productp fn-pic-choice-contextp)
  (fn-pic-at fn-pic-feed-funded fn-pic-choice-outcomep fn-pic-choice-observationp fn-pic-observation-okp
   fn-pic-retained-agent fn-rcl-tomb-agent fn-rcl-tomb-sourcep fn-pic-spanp fn-octets-get
   fn-pic-ch-incoming-observation-is-exact fn-pic-ch-control-observation-is-exact
   fn-cbor-octet-listp nth take nthcdr update-nth)))))
(local (defthm fn-pic-ch-tail-is-consp-within-source
 (implies (and (natp n) (< n (len x))) (consp (nthcdr n x)))
 :hints (("Goal" :induct (nthcdr n x) :in-theory (enable nthcdr len)))))
(local (defthm fn-pic-ch-car-of-tail
 (implies (natp n) (equal (car (nthcdr n x)) (nth n x)))
 :hints (("Goal" :induct (nthcdr n x) :in-theory (enable nthcdr nth)))))
(local (defthm fn-pic-ch-source-flag-is-scalar
 (implies (and (true-listp held) (<= 145 (len held)))
  (equal (fn-rcl-tomb-sourcep held) (equal (nth 8 held) 1)))
 :hints (("Goal" :in-theory (e/d (fn-rcl-tomb-sourcep nth)
  (fn-rcl-drop nthcdr))))))
(local (defthm fn-pic-ch-different-length-implies-different
 (implies (not (equal (len x) (len y))) (not (equal x y))) :rule-classes nil))
(local (defthm fn-pic-ch-length-congruence
 (implies (equal x y) (equal (len x) (len y))) :rule-classes nil))
(local (defthm fn-pic-ch-equal-agents-have-equal-lengths
 (implies (and (fn-pic-choice-contextp c incoming held)
               (equal (fn-pic-retained-agent c incoming) (fn-rcl-tomb-agent held)))
  (equal (- (fn-pic-at 2 (fn-pic-get agent c)) (fn-pic-at 1 (fn-pic-get agent c)))
         (- (len held) 145)))
 :rule-classes nil
 :hints (("Goal" :use
  ((:instance fn-pic-ch-length-congruence
    (x (fn-pic-retained-agent c incoming)) (y (fn-rcl-tomb-agent held)))
   (:instance fn-pic-ch-agent-length)
   (:instance fn-pic-ch-tomb-agent-length))
 :in-theory (e/d (fn-pic-choice-contextp)
  (fn-pic-at fn-pic-retained-agent fn-rcl-tomb-agent fn-pic-spanp len
   fn-pic-ch-agent-length fn-pic-ch-tomb-agent-length))))))
(local (defthm fn-pic-ch-take-zero
 (equal (take 0 x) nil) :hints (("Goal" :in-theory (enable take)))))
(defthm fn-pic-feed-funded-establishes-exact-tombstone-hash-choice
 (implies (and (fn-pic-choice-contextp c incoming held)
               (equal (fn-pic-get phase c) :tomb-flag)
               (fn-pic-choice-observationp c observation incoming held))
  (let ((next (mv-nth 1 (fn-pic-feed-funded c observation fuel))))
   (implies (member-eq (fn-pic-get phase next) '(:tomb-agent-held :digest-begin))
    (fn-pic-choice-outcomep next incoming held))))
 :rule-classes nil
 :hints (("Goal" :use
  (fn-pic-ch-equal-agents-have-equal-lengths)
 :in-theory (e/d (fn-pic-choice-contextp fn-pic-choice-productp fn-pic-choice-outcomep
    fn-pic-choice-observationp fn-pic-retained-source-choicep
    fn-pic-feed-funded fn-pic-feed fn-pic-demand fn-pic-hash-start)
  (fn-pic-at fn-pic-observation-okp fn-pic-observed-byte fn-pic-retained-agent fn-rcl-tomb-agent
   fn-rcl-tomb-sourcep fn-pic-spanp fn-rcl-drop fn-pic-ch-take-next take nth nthcdr update-nth)))))
