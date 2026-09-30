; View-delta substrate (W9, the bounded pilot ratified 2026-09-30; PRF-1052).
;
; A maintained view V of a fact list F answers a query Q without walking F:
; decode(V) = Q(F), kept across each delta.  The vocabulary here is the
; smallest that carries the two first consumers (books/retention-obligation-
; view.lisp): a CONTRIBUTION is (KEY . WEIGHT), what one fact contributes to
; a keyed aggregate (the consumer's map: a retention obligation contributes
; (subject . charge)); the ORACLE `fn-vd-oracle-at' answers the aggregate
; (COUNT . SUM) at a key by walking every contribution -- the reconstruction
; the theorems compare against, never the served path; the VIEW is an alist
; from key to (COUNT . SUM) with each key once (`fn-vd-viewp'), read at a key
; by `fn-vd-get' and advanced by `fn-vd-bump' (a fact arrives) and
; `fn-vd-unbump' (a fact is retracted; the key's entry goes when its count
; reaches zero, so the view holds an entry per key with an active fact and
; nothing for the keys that had one).
;
; Each operator ships its delta lemma: reading the advanced view at ANY key
; answers the oracle over the advanced facts, given the view answered the
; oracle before (`fn-vd-get-of-bump-is-the-oracle', `fn-vd-get-of-unbump-is-
; the-oracle'); `fn-vd-build' is the initialization from the whole fact list
; (`fn-vd-build-corresponds').  `fn-vd-correspondp' is the pointwise
; correspondence at every key (a defun-sk, never executed); the three
; theorems over it (build, bump, unbump) are what a consumer instantiates.
;
; Not here: join, a general dataflow, or any action driven by a retraction
; (warranty-quality-proof-engineering.md section 7: a retracted row never
; performs an irreversible action; the consumers read counts).
(in-package "ACL2")
(local (include-book "arithmetic/top" :dir :system))

; -----------------------------------------------------------------------------
; 1. The view: an alist from key to (COUNT . SUM), each key once.

(defconst *fn-vd-zero* (cons 0 0))

(defun fn-vd-pairp (r)
  (declare (xargs :guard t))
  (and (consp r) (natp (car r)) (natp (cdr r))))

(defun fn-vd-boundp (k v)
  (declare (xargs :guard t))
  (if (consp v)
      (or (and (consp (car v)) (equal (car (car v)) k))
          (fn-vd-boundp k (cdr v)))
    nil))

(defun fn-vd-viewp (v)
  (declare (xargs :guard t))
  (if (consp v)
      (and (consp (car v))
           (fn-vd-pairp (cdr (car v)))
           (not (fn-vd-boundp (car (car v)) (cdr v)))
           (fn-vd-viewp (cdr v)))
    (null v)))

(defun fn-vd-get (k v)
  "The view's aggregate at K: (COUNT . SUM), zero when K has no entry."
  (declare (xargs :guard t))
  (if (consp v)
      (if (and (consp (car v)) (equal (car (car v)) k))
          (cdr (car v))
        (fn-vd-get k (cdr v)))
    *fn-vd-zero*))

(defun fn-vd-put (k r v)
  (declare (xargs :guard t))
  (if (consp v)
      (if (and (consp (car v)) (equal (car (car v)) k))
          (cons (cons k r) (cdr v))
        (cons (car v) (fn-vd-put k r (cdr v))))
    (list (cons k r))))

(defun fn-vd-drop (k v)
  (declare (xargs :guard t))
  (if (consp v)
      (if (and (consp (car v)) (equal (car (car v)) k))
          (cdr v)
        (cons (car v) (fn-vd-drop k (cdr v))))
    nil))

; -----------------------------------------------------------------------------
; 2. The oracle: the aggregate at K reconstructed from every contribution.

(defun fn-vd-contribsp (cs)
  (declare (xargs :guard t))
  (if (consp cs)
      (and (consp (car cs)) (fn-vd-contribsp (cdr cs)))
    (null cs)))

(defun fn-vd-oracle-at (k cs)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp cs)
      (let ((r (fn-vd-oracle-at k (cdr cs))))
        (if (and (consp (car cs)) (equal (car (car cs)) k))
            (cons (+ 1 (car r)) (+ (nfix (cdr (car cs))) (cdr r)))
          r))
    *fn-vd-zero*))

(defthm fn-vd-oracle-at-is-a-pair
  (fn-vd-pairp (fn-vd-oracle-at k cs)))

(verify-guards fn-vd-oracle-at
  :hints (("Goal" :use ((:instance fn-vd-oracle-at-is-a-pair (cs (cdr cs))))
           :in-theory (e/d (fn-vd-pairp) (fn-vd-oracle-at-is-a-pair)))))

; -----------------------------------------------------------------------------
; 3. The operators.

(defun fn-vd-bump (k w v)
  "The fact contributing (K . W) arrives."
  (declare (xargs :guard t))
  (let ((r (fn-vd-get k v)))
    (fn-vd-put k (cons (+ 1 (nfix (if (consp r) (car r) nil))) (+ (nfix w) (nfix (if (consp r) (cdr r) nil)))) v)))

(defun fn-vd-unbump (k w v)
  "The fact contributing (K . W) is retracted."
  (declare (xargs :guard t))
  (let* ((r (fn-vd-get k v))
         (c (nfix (if (consp r) (car r) nil))))
    (if (<= c 1)
        (fn-vd-drop k v)
      (fn-vd-put k (cons (- c 1) (nfix (- (nfix (if (consp r) (cdr r) nil)) (nfix w)))) v))))

(defun fn-vd-build (cs)
  "The view initialized from the whole contribution list."
  (declare (xargs :guard t))
  (if (consp cs)
      (if (consp (car cs))
          (fn-vd-bump (car (car cs)) (cdr (car cs)) (fn-vd-build (cdr cs)))
        (fn-vd-build (cdr cs)))
    nil))

; -----------------------------------------------------------------------------
; 4. Per-operator delta lemmas, pointwise at a key.

(defthm fn-vd-get-of-put
  (equal (fn-vd-get k (fn-vd-put k2 r v))
         (if (equal k k2) r (fn-vd-get k v))))

(defthm fn-vd-get-when-unbound
  (implies (not (fn-vd-boundp k v))
           (equal (fn-vd-get k v) *fn-vd-zero*)))

(defthm fn-vd-boundp-of-drop
  (implies (fn-vd-viewp v)
           (equal (fn-vd-boundp k (fn-vd-drop k2 v))
                  (and (not (equal k k2)) (fn-vd-boundp k v)))))

(defthm fn-vd-get-of-drop
  (implies (fn-vd-viewp v)
           (equal (fn-vd-get k (fn-vd-drop k2 v))
                  (if (equal k k2) *fn-vd-zero* (fn-vd-get k v)))))

(defthm fn-vd-boundp-of-put
  (equal (fn-vd-boundp k (fn-vd-put k2 r v))
         (or (equal k k2) (fn-vd-boundp k v))))

(defthm fn-vd-viewp-of-put
  (implies (and (fn-vd-viewp v) (fn-vd-pairp r))
           (fn-vd-viewp (fn-vd-put k r v))))

(defthm fn-vd-viewp-of-drop
  (implies (fn-vd-viewp v)
           (fn-vd-viewp (fn-vd-drop k v))))

(defthm fn-vd-get-is-a-pair-when-viewp
  (implies (fn-vd-viewp v)
           (fn-vd-pairp (fn-vd-get k v))))

(defthm fn-vd-viewp-of-bump
  (implies (fn-vd-viewp v)
           (fn-vd-viewp (fn-vd-bump k w v))))

(defthm fn-vd-viewp-of-unbump
  (implies (fn-vd-viewp v)
           (fn-vd-viewp (fn-vd-unbump k w v))))

(defthm fn-vd-viewp-of-build
  (fn-vd-viewp (fn-vd-build cs)))

(defthm fn-vd-oracle-count-natp
  (natp (car (fn-vd-oracle-at k cs)))
  :rule-classes :type-prescription
  :hints (("Goal" :use fn-vd-oracle-at-is-a-pair
           :in-theory (e/d (fn-vd-pairp) (fn-vd-oracle-at-is-a-pair)))))
(defthm fn-vd-oracle-sum-natp
  (natp (cdr (fn-vd-oracle-at k cs)))
  :rule-classes :type-prescription
  :hints (("Goal" :use fn-vd-oracle-at-is-a-pair
           :in-theory (e/d (fn-vd-pairp) (fn-vd-oracle-at-is-a-pair)))))
(defthm fn-vd-oracle-consp
  (consp (fn-vd-oracle-at k cs))
  :rule-classes :type-prescription
  :hints (("Goal" :use fn-vd-oracle-at-is-a-pair
           :in-theory (e/d (fn-vd-pairp) (fn-vd-oracle-at-is-a-pair)))))

; The insert rule: the view bumped by C answers the oracle over (cons C cs)
; wherever it answered the oracle over cs.
(defthm fn-vd-get-of-bump-is-the-oracle
  (implies (and (consp c)
                (equal (fn-vd-get k v) (fn-vd-oracle-at k cs)))
           (equal (fn-vd-get k (fn-vd-bump (car c) (cdr c) v))
                  (fn-vd-oracle-at k (cons c cs))))
  :hints (("Goal" :expand ((fn-vd-oracle-at k (cons c cs)))
           :in-theory (e/d (fn-vd-bump) (fn-vd-get fn-vd-put fn-vd-oracle-at)))))

; The retraction rule needs what the oracle knows about a member: its key's
; count is at least one, its sum at least the weight, and a count of one is
; that member alone.
(defthm fn-vd-oracle-at-of-remove1
  (implies (and (consp c) (member-equal c cs))
           (equal (fn-vd-oracle-at k (remove1-equal c cs))
                  (if (equal (car c) k)
                      (cons (- (car (fn-vd-oracle-at k cs)) 1)
                            (- (cdr (fn-vd-oracle-at k cs)) (nfix (cdr c))))
                    (fn-vd-oracle-at k cs)))))

(defthm fn-vd-oracle-at-member-bounds
  (implies (and (consp c) (member-equal c cs) (equal (car c) k))
           (and (<= 1 (car (fn-vd-oracle-at k cs)))
                (<= (nfix (cdr c)) (cdr (fn-vd-oracle-at k cs)))))
  :rule-classes (:rewrite :linear))

(defthm fn-vd-oracle-zero-count-zero-sum
  (implies (equal (car (fn-vd-oracle-at k cs)) 0)
           (equal (cdr (fn-vd-oracle-at k cs)) 0)))

(defthm fn-vd-oracle-at-count-one-is-the-member
  (implies (and (consp c) (member-equal c cs) (equal (car c) k)
                (equal (car (fn-vd-oracle-at k cs)) 1))
           (equal (cdr (fn-vd-oracle-at k cs)) (nfix (cdr c)))))

(defthm fn-vd-get-of-unbump-is-the-oracle
  (implies (and (fn-vd-viewp v)
                (consp c) (member-equal c cs)
                (equal (fn-vd-get k v) (fn-vd-oracle-at k cs))
                (equal (fn-vd-get (car c) v) (fn-vd-oracle-at (car c) cs)))
           (equal (fn-vd-get k (fn-vd-unbump (car c) (cdr c) v))
                  (fn-vd-oracle-at k (remove1-equal c cs))))
  :hints (("Goal" :in-theory (disable fn-vd-oracle-at-of-remove1)
           :use ((:instance fn-vd-oracle-at-of-remove1)
                 (:instance fn-vd-oracle-at-member-bounds (k (car c)))
                 (:instance fn-vd-oracle-at-count-one-is-the-member (k (car c)))))))

; -----------------------------------------------------------------------------
; 5. Correspondence at every key, and the three theorems a consumer uses.

(defun-sk fn-vd-correspondp (v cs)
  (forall (k) (equal (fn-vd-get k v) (fn-vd-oracle-at k cs))))

(in-theory (disable fn-vd-correspondp fn-vd-correspondp-necc
                    fn-vd-bump fn-vd-unbump fn-vd-get fn-vd-put fn-vd-drop fn-vd-oracle-at))

(defthm fn-vd-correspondp-of-nil
  (fn-vd-correspondp nil nil)
  :hints (("Goal" :in-theory (enable fn-vd-correspondp fn-vd-get fn-vd-oracle-at))))

(defthm fn-vd-correspondp-of-bump
  (implies (and (consp c) (fn-vd-correspondp v cs))
           (fn-vd-correspondp (fn-vd-bump (car c) (cdr c) v) (cons c cs)))
  :hints (("Goal"
           :expand ((fn-vd-correspondp (fn-vd-bump (car c) (cdr c) v) (cons c cs)))
           :use ((:instance fn-vd-correspondp-necc
                            (k (fn-vd-correspondp-witness
                                (fn-vd-bump (car c) (cdr c) v) (cons c cs))))))))

(defthm fn-vd-correspondp-of-unbump
  (implies (and (fn-vd-viewp v) (consp c) (member-equal c cs)
                (fn-vd-correspondp v cs))
           (fn-vd-correspondp (fn-vd-unbump (car c) (cdr c) v) (remove1-equal c cs)))
  :hints (("Goal"
           :expand ((fn-vd-correspondp (fn-vd-unbump (car c) (cdr c) v)
                                       (remove1-equal c cs)))
           :use ((:instance fn-vd-correspondp-necc
                            (k (fn-vd-correspondp-witness
                                (fn-vd-unbump (car c) (cdr c) v)
                                (remove1-equal c cs))))
                 (:instance fn-vd-correspondp-necc (k (car c)))))))

; Initialization: the view built from the whole list corresponds to it.
(defthm fn-vd-build-corresponds
  (implies (fn-vd-contribsp cs)
           (fn-vd-correspondp (fn-vd-build cs) cs))
  :hints (("Goal" :induct (fn-vd-build cs))
          ("Subgoal *1/1" :in-theory (disable fn-vd-correspondp-of-bump)
           :use ((:instance fn-vd-correspondp-of-bump
                    (c (car cs)) (v (fn-vd-build (cdr cs))) (cs (cdr cs)))))))

(in-theory (disable fn-vd-get fn-vd-put fn-vd-drop fn-vd-bump fn-vd-unbump
                    fn-vd-build fn-vd-oracle-at fn-vd-viewp fn-vd-boundp
                    fn-vd-pairp fn-vd-contribsp))
