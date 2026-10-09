; fn: the runtime contract's invariant, part one: what initialization
; establishes and what each operation a step is made of preserves (the slot,
; pool and use-table components, the requests an instance makes).
;
; Part of the runtime contract (books/runtime-contract.lisp states T1 and T2;
; books/runtime-contract-invariant.lisp proves them from this book).  Split
; so each book certifies under the per-book time limit.

(in-package "ACL2")
(include-book "runtime-contract-keystones")

; These proofs are written against the base book's theory; the keystone
; book's later rules (structure and frame lemmas for T7-T15) are kept out.
(local (in-theory (disable fn-rtc-accept-branch-keeps-foreign fn-rtc-accept-branch-no-slot-keeps-buffers
                           fn-rtc-accept-branch-not-done-keeps-buffers fn-rtc-close-branch-keeps-foreign
                           fn-rtc-deliver-keeps-foreign fn-rtc-end-use-keeps-workspaces fn-rtc-end-use-structure
                           fn-rtc-free-slot-found fn-rtc-invp-slots-len fn-rtc-key-equal-parts
                           fn-rtc-len-slots-of-retire-drained fn-rtc-rearm-arms-when-free
                           fn-rtc-req-acquire-keeps-foreign fn-rtc-req-release-keeps-foreign
                           fn-rtc-req-submit-keeps-foreign fn-rtc-req-write-keeps-foreign
                           fn-rtc-request-keeps-foreign fn-rtc-requests-keeps-foreign
                           fn-rtc-retire-drained-retires fn-rtc-slot-of-rearm fn-rtc-use-okp-slot-range
                           fn-rtc-req-acquire-keeps-uses fn-rtc-req-cancel-keeps-uses fn-rtc-req-close-keeps-uses
                           fn-rtc-req-release-keeps-uses fn-rtc-req-submit-keeps-uses fn-rtc-req-write-keeps-uses)))

(defthm fn-rtc-free-slots-length
  (equal (len (fn-rtc-free-slots n)) (nfix n)))

(defthm fn-rtc-free-pool-length
  (equal (len (fn-rtc-free-pool n)) (nfix n)))

(defthm fn-rtc-free-slots-okp
  (implies (and (natp i) (< 0 i))
           (fn-rtc-slots-okp i (fn-rtc-free-slots n))))

(defun fn-rtc-init-induct (n i)
  (declare (xargs :guard (and (natp n) (natp i))))
  (if (zp n) i (fn-rtc-init-induct (- n 1) (+ 1 i))))

(defthm fn-rtc-free-pool-okp
  (fn-rtc-pool-okp h (fn-rtc-free-pool n) s)
  :hints (("Goal" :induct (fn-rtc-init-induct n h))))

(defthm fn-rtc-free-slots-draining-okp
  (fn-rtc-draining-okp i (fn-rtc-free-slots n) uses)
  :hints (("Goal" :induct (fn-rtc-init-induct n i))))

(defthm fn-rtc-free-slots-first-free
  (implies (and (natp i) (< 0 i) (natp n) (< 0 n))
           (equal (fn-rtc-free-slot i (fn-rtc-free-slots n)) i)))

(defthm fn-rtc-nil-mstates-okp
  (implies (fn-rtc-mstates-okp tail)
           (fn-rtc-mstates-okp (make-list-ac n nil tail)))
  :hints (("Goal" :induct (make-list-ac n nil tail))))

(defthm fn-rtc-make-list-true-listp
  (equal (true-listp (make-list-ac n x tail)) (true-listp tail)))

(defthm fn-rtc-make-list-length
  (equal (len (make-list-ac n x tail)) (+ (nfix n) (len tail))))

; Admission may be temporarily absent between ending an accept and rearming.
(defun fn-rtc-core-invp (s)
  (declare (xargs :guard t))
  (let ((cfg (fn-rtc-config s)))
    (and (true-listp s) (equal (len s) 6)
         (natp (fn-rtc-get 5 s))
         (fn-rtc-configp cfg)
         (equal (len (fn-rtc-slots s)) (fn-rtc-nslots cfg))
         (fn-rtc-slots-okp 0 (fn-rtc-slots s))
         (fn-rtc-statics-okp 1 (fn-rtc-nstatic cfg) (fn-rtc-slots s))
         (equal (len (fn-rtc-pool s)) (fn-rtc-nbufs cfg))
         (fn-rtc-pool-okp 0 (fn-rtc-pool s) s)
         (fn-rtc-uses-okp (fn-rtc-uses s) s)
         (true-listp (fn-rtc-mstates s))
         (equal (len (fn-rtc-mstates s)) (fn-rtc-nslots cfg))
         (fn-rtc-mstates-okp (fn-rtc-mstates s))
         (fn-rtc-draining-okp 0 (fn-rtc-slots s) (fn-rtc-uses s)))))

(defthm fn-rtc-invp-is-core-and-admission
  (equal (fn-rtc-invp s)
         (and (fn-rtc-core-invp s)
              (iff (fn-rtc-free-slot 0 (fn-rtc-slots s))
                   (fn-rtc-kind-out-p :accept 0 0 (fn-rtc-uses s)))))
  :hints (("Goal" :in-theory
           (disable fn-rtc-slots-okp fn-rtc-pool-okp fn-rtc-uses-okp
                    fn-rtc-mstates-okp fn-rtc-draining-okp fn-rtc-free-slot
                    fn-rtc-kind-out-p))))

(defthm fn-rtc-next-op-of-with
  (and (equal (fn-rtc-next-op (fn-rtc-with-buffer h b s)) (fn-rtc-next-op s))
       (equal (fn-rtc-next-op (fn-rtc-with-slot id slot s)) (fn-rtc-next-op s))
       (equal (fn-rtc-next-op (fn-rtc-with-uses uses s)) (fn-rtc-next-op s))
       (equal (fn-rtc-next-op (fn-rtc-with-mstate id m s)) (fn-rtc-next-op s)))
  :hints (("Goal" :in-theory
           (enable fn-rtc-with-buffer fn-rtc-with-slot fn-rtc-with-uses fn-rtc-with-mstate))))

(defthm fn-rtc-pool-okp-of-with-buffer
  (equal (fn-rtc-pool-okp i pool (fn-rtc-with-buffer h b s))
         (fn-rtc-pool-okp i pool s))
  :hints (("Goal" :induct (fn-rtc-pool-okp i pool s)
           :in-theory (union-theories (theory 'minimal-theory)
                        '(fn-rtc-pool-okp fn-rtc-with-accessors fn-rtc-slot-of-with)))))

(defthm fn-rtc-pool-okp-of-with-mstate
  (equal (fn-rtc-pool-okp i pool (fn-rtc-with-mstate id m s))
         (fn-rtc-pool-okp i pool s))
  :hints (("Goal" :induct (fn-rtc-pool-okp i pool s)
           :in-theory (union-theories (theory 'minimal-theory)
                        '(fn-rtc-pool-okp fn-rtc-with-accessors fn-rtc-slot-of-with)))))

(defthm fn-rtc-use-okp-of-with-mstate
  (equal (fn-rtc-use-okp u (fn-rtc-with-mstate id m s))
         (fn-rtc-use-okp u s))
  :hints (("Goal" :in-theory
           (union-theories (theory 'minimal-theory)
            '(fn-rtc-use-okp fn-rtc-current-p fn-rtc-with-accessors
              fn-rtc-slot-of-with fn-rtc-buffer-of-with fn-rtc-next-op-of-with)))))

(defthm fn-rtc-uses-okp-of-with-mstate
  (equal (fn-rtc-uses-okp uses (fn-rtc-with-mstate id m s))
         (fn-rtc-uses-okp uses s))
  :hints (("Goal" :in-theory (disable fn-rtc-use-okp))))

(defthm fn-rtc-mstates-okp-of-set
  (implies (and (fn-rtc-mstates-okp ms)
                (<= (fn-rtc-size m) (fn-rtc-m-max-state)))
           (fn-rtc-mstates-okp (fn-rtc-set id m ms)))
  :hints (("Goal" :induct (fn-rtc-set id m ms)
           :in-theory (disable fn-rtc-size))))

(defthm fn-rtc-make-record
  (and (true-listp (fn-rtc-make c sl p u ms n))
       (equal (len (fn-rtc-make c sl p u ms n)) 6)
       (equal (fn-rtc-get 5 (fn-rtc-make c sl p u ms n)) n))
  :hints (("Goal" :in-theory (enable fn-rtc-make))))

(defthm fn-rtc-with-mstate-record
  (and (true-listp (fn-rtc-with-mstate id m s))
       (equal (len (fn-rtc-with-mstate id m s)) 6)
       (equal (fn-rtc-get 5 (fn-rtc-with-mstate id m s)) (fn-rtc-next-op s)))
  :hints (("Goal" :in-theory (enable fn-rtc-with-mstate))))

(defthm fn-rtc-core-invp-of-with-mstate
  (implies (and (fn-rtc-core-invp s)
                (<= (fn-rtc-size m) (fn-rtc-m-max-state)))
           (fn-rtc-core-invp (fn-rtc-with-mstate id m s)))
  :hints (("Goal" :in-theory
           (disable fn-rtc-configp fn-rtc-slots-okp fn-rtc-pool-okp
                    fn-rtc-uses-okp fn-rtc-mstates-okp fn-rtc-draining-okp
                    fn-rtc-size fn-rtc-get))))

; Pointwise form of the recursive pool invariant.
(defun fn-rtc-buffer-okp (h b s)
  (declare (xargs :guard t))
  (let ((o (fn-rtc-b-owner b)))
    (and (fn-rtc-bufferp b (fn-rtc-cap (fn-rtc-config s)))
         (case (fn-rtc-get 0 o)
           (:workspace
            (let ((slot (fn-rtc-slot (fn-rtc-get 1 o) s)))
              (and (<= 1 (nfix (fn-rtc-get 1 o)))
                   (equal (fn-rtc-s-inc slot) (fn-rtc-get 2 o))
                   (member-eq (fn-rtc-s-status slot) '(:live :closing)))))
           (:leased
            (and (<= 1 (nfix (fn-rtc-get 1 o)))
                 (< (nfix (fn-rtc-get 1 o)) (fn-rtc-nslots (fn-rtc-config s)))
                 (fn-rtc-holds-p h (fn-rtc-b-gen b) (fn-rtc-uses s))))
           (:handed
                (and (<= 1 (nfix (fn-rtc-get 1 o)))
                     (< (nfix (fn-rtc-get 1 o)) (fn-rtc-nslots (fn-rtc-config s)))
                     (<= 1 (nfix (fn-rtc-get 3 o)))
                     (< (nfix (fn-rtc-get 3 o)) (fn-rtc-nslots (fn-rtc-config s)))
                     (not (equal (fn-rtc-get 3 o) (fn-rtc-get 1 o)))
                     (implies (< (fn-rtc-nstatic (fn-rtc-config s)) (nfix (fn-rtc-get 1 o)))
                              (<= (nfix (fn-rtc-get 3 o)) (fn-rtc-nstatic (fn-rtc-config s))))
                     (fn-rtc-holds-p h (fn-rtc-b-gen b) (fn-rtc-uses s))))
           (otherwise t)))))

(defthm fn-rtc-pool-okp-unfolds
  (equal (fn-rtc-pool-okp i pool s)
         (if (consp pool)
             (and (fn-rtc-buffer-okp i (car pool) s)
                  (fn-rtc-pool-okp (+ 1 i) (cdr pool) s))
           (null pool)))
  :hints (("Goal" :in-theory
           (union-theories (theory 'minimal-theory)
            '(fn-rtc-pool-okp fn-rtc-buffer-okp))))
  :rule-classes :definition)

(in-theory (disable fn-rtc-pool-okp fn-rtc-buffer-okp))

(defun fn-rtc-index-induct (k i xs)
  (declare (xargs :guard (and (natp k) (natp i))))
  (if (and (consp xs) (not (zp k)))
      (fn-rtc-index-induct (- k 1) (+ 1 i) (cdr xs))
    i))

(defthm fn-rtc-pool-okp-get
  (implies (and (natp i) (natp k) (< k (len pool))
                (fn-rtc-pool-okp i pool s))
           (fn-rtc-buffer-okp (+ i k) (fn-rtc-get k pool) s))
  :hints (("Goal" :induct (fn-rtc-index-induct k i pool)
           :in-theory (disable fn-rtc-buffer-okp))))

(defthm fn-rtc-pool-okp-set
  (implies (and (natp i) (natp k)
                (fn-rtc-pool-okp i pool s)
                (fn-rtc-buffer-okp (+ i k) b s))
           (fn-rtc-pool-okp i (fn-rtc-set k b pool) s))
  :hints (("Goal" :induct (fn-rtc-index-induct k i pool)
           :in-theory (disable fn-rtc-buffer-okp)
           :expand ((:with fn-rtc-pool-okp-unfolds (fn-rtc-pool-okp i pool s))
                    (:with fn-rtc-pool-okp-unfolds
                     (fn-rtc-pool-okp i (cons b (cdr pool)) s))))))

(defthm fn-rtc-use-okp-of-unleased-update
  (implies (and (natp h) (fn-rtc-use-okp u s) (not (fn-rtc-leasedp h s)))
           (fn-rtc-use-okp u (fn-rtc-with-buffer h b s)))
  :hints (("Goal" :in-theory
           (union-theories (theory 'minimal-theory)
            '(fn-rtc-use-okp fn-rtc-leasedp fn-rtc-current-p
              (:executable-counterpart member-equal)
              fn-rtc-with-accessors fn-rtc-slot-of-with fn-rtc-buffer-of-with
              fn-rtc-next-op-of-with (:type-prescription fn-rtc-h-buf) nfix natp)))))

(defthm fn-rtc-uses-okp-of-unleased-update
  (implies (and (natp h) (fn-rtc-uses-okp uses s) (not (fn-rtc-leasedp h s)))
           (fn-rtc-uses-okp uses (fn-rtc-with-buffer h b s)))
  :hints (("Goal" :induct (fn-rtc-uses-okp uses s)
           :in-theory (union-theories (theory 'minimal-theory)
                        '(fn-rtc-uses-okp fn-rtc-use-okp-of-unleased-update)))))

(defthm fn-rtc-with-buffer-record
  (and (true-listp (fn-rtc-with-buffer h b s))
       (equal (len (fn-rtc-with-buffer h b s)) 6)
       (equal (fn-rtc-get 5 (fn-rtc-with-buffer h b s)) (fn-rtc-next-op s)))
  :hints (("Goal" :in-theory (enable fn-rtc-with-buffer))))

(defthm fn-rtc-core-invp-of-unleased-update
  (implies (and (fn-rtc-core-invp s) (natp h)
                (not (fn-rtc-leasedp h s)) (fn-rtc-buffer-okp h b s))
           (fn-rtc-core-invp (fn-rtc-with-buffer h b s)))
  :hints (("Goal" :in-theory
           (disable fn-rtc-configp fn-rtc-slots-okp fn-rtc-pool-okp-unfolds
                    fn-rtc-uses-okp fn-rtc-mstates-okp fn-rtc-draining-okp
                    fn-rtc-get fn-rtc-leasedp))))

(defun fn-rtc-instance-active-p (id inc s)
  (declare (xargs :guard t))
  (and (posp id) (natp inc) (< id (fn-rtc-nslots (fn-rtc-config s)))
       (equal (fn-rtc-s-inc (fn-rtc-slot id s)) inc)
       (member-eq (fn-rtc-s-status (fn-rtc-slot id s)) '(:live :closing))))

(defthm fn-rtc-core-invp-buffer
  (implies (and (fn-rtc-core-invp s) (natp h)
                (< h (fn-rtc-nbufs (fn-rtc-config s))))
           (fn-rtc-buffer-okp h (fn-rtc-buffer h s) s))
  :hints (("Goal" :use ((:instance fn-rtc-pool-okp-get
                                    (i 0) (k h) (pool (fn-rtc-pool s))))
           :in-theory (disable fn-rtc-pool-okp-unfolds fn-rtc-uses-okp
                               fn-rtc-slots-okp fn-rtc-mstates-okp
                               fn-rtc-draining-okp fn-rtc-configp fn-rtc-get))))

(defthm fn-rtc-acquire-preserves-core-invp
  (implies (and (fn-rtc-core-invp s) (fn-rtc-instance-active-p id inc s))
           (fn-rtc-core-invp (mv-nth 0 (fn-rtc-req-acquire r id inc s))))
  :hints (("Goal" :in-theory
           (e/d (fn-rtc-req-acquire fn-rtc-buffer-okp)
                (fn-rtc-core-invp fn-rtc-s-inc fn-rtc-s-status fn-rtc-b-gen)))))

(defthm fn-rtc-release-preserves-core-invp
  (implies (fn-rtc-core-invp s)
           (fn-rtc-core-invp (mv-nth 0 (fn-rtc-req-release r id inc s))))
  :hints (("Goal" :in-theory
           (e/d (fn-rtc-req-release fn-rtc-buffer-okp)
                (fn-rtc-core-invp fn-rtc-s-inc fn-rtc-s-status fn-rtc-b-gen))
           :use ((:instance fn-rtc-core-invp-buffer (h (fn-rtc-get 1 r)))))))

(defthm fn-rtc-octets-append
  (implies (and (fn-cbor-octet-listp a) (fn-cbor-octet-listp b))
           (fn-cbor-octet-listp (append a b))))

(defthm fn-rtc-octets-take
  (implies (and (fn-cbor-octet-listp a) (natp n) (<= n (len a)))
           (fn-cbor-octet-listp (take n a))))

(defthm fn-rtc-octets-nthcdr
  (implies (fn-cbor-octet-listp a)
           (fn-cbor-octet-listp (nthcdr n a))))

(defthm fn-rtc-true-list-fix-identity
  (implies (true-listp a) (equal (true-list-fix a) a)))

(defthm fn-rtc-len-take
  (equal (len (take n a)) (nfix n)))

(defthm fn-rtc-len-nthcdr
  (equal (len (nthcdr n a)) (nfix (- (len a) (nfix n))))
  :hints (("Goal" :induct (nthcdr n a))))

(defthm fn-rtc-len-append
  (equal (len (append a b)) (+ (len a) (len b))))

(defthm fn-rtc-splice-octets
  (implies (and (fn-cbor-octet-listp bytes) (fn-cbor-octet-listp data)
                (natp off) (<= off (len bytes)))
           (fn-cbor-octet-listp (fn-rtc-splice bytes off data)))
  :hints (("Goal" :in-theory (disable fn-cbor-octet-listp take nthcdr true-list-fix))))

(defthm fn-rtc-splice-length
  (implies (and (true-listp bytes) (true-listp data)
                (natp off) (<= off (len bytes)))
           (equal (len (fn-rtc-splice bytes off data))
                  (max (len bytes) (+ off (len data)))))
  :hints (("Goal" :in-theory (disable take nthcdr true-list-fix))))

(defthm fn-rtc-buffer-okp-change-bytes
  (implies (and (fn-rtc-buffer-okp h b s) (fn-cbor-octet-listp bytes)
                (<= (len bytes) (fn-rtc-cap (fn-rtc-config s))))
           (fn-rtc-buffer-okp h (list (fn-rtc-b-gen b) (fn-rtc-b-owner b) bytes) s))
  :hints (("Goal" :in-theory
           (e/d (fn-rtc-buffer-okp)
                (fn-rtc-holds-p fn-rtc-s-inc fn-rtc-s-status fn-cbor-octet-listp)))))

(defthm fn-rtc-buffer-okp-bytes
  (implies (fn-rtc-buffer-okp h b s)
           (and (fn-cbor-octet-listp (fn-rtc-b-bytes b))
                (<= (len (fn-rtc-b-bytes b)) (fn-rtc-cap (fn-rtc-config s)))))
  :hints (("Goal" :in-theory
           (e/d (fn-rtc-buffer-okp)
                (fn-cbor-octet-listp fn-rtc-holds-p fn-rtc-s-inc fn-rtc-s-status))))
  :rule-classes :forward-chaining)

(defthm fn-rtc-workspace-not-leased
  (implies (equal (fn-rtc-b-owner (fn-rtc-buffer h s)) (list :workspace id inc))
           (not (fn-rtc-leasedp h s)))
  :hints (("Goal" :in-theory (disable fn-rtc-b-owner))))

(defthm fn-rtc-write-preserves-core-invp
  (implies (fn-rtc-core-invp s)
           (fn-rtc-core-invp (mv-nth 0 (fn-rtc-req-write r id inc s))))
  :hints (("Goal" :in-theory
           (e/d (fn-rtc-req-write)
                (fn-rtc-core-invp fn-rtc-s-inc fn-rtc-s-status fn-rtc-b-gen
                 fn-rtc-b-owner fn-rtc-b-bytes fn-rtc-get fn-rtc-cap
                 fn-rtc-nbufs fn-rtc-leasedp fn-rtc-splice fn-cbor-octet-listp
                 fn-rtc-core-invp-buffer fn-rtc-core-invp-of-unleased-update
                 fn-rtc-buffer-okp-change-bytes))
           :use ((:instance fn-rtc-core-invp-buffer (h (fn-rtc-get 1 r)))
                 (:instance fn-rtc-core-invp-of-unleased-update
                  (h (fn-rtc-get 1 r))
                  (b (list (fn-rtc-get 2 r) (list :workspace id inc)
                           (fn-rtc-splice (fn-rtc-b-bytes (fn-rtc-buffer (fn-rtc-get 1 r) s))
                                          (fn-rtc-get 3 r) (fn-rtc-get 4 r)))))
                 (:instance fn-rtc-buffer-okp-change-bytes
                  (h (fn-rtc-get 1 r)) (b (fn-rtc-buffer (fn-rtc-get 1 r) s))
                  (bytes (fn-rtc-splice (fn-rtc-b-bytes (fn-rtc-buffer (fn-rtc-get 1 r) s))
                                        (fn-rtc-get 3 r) (fn-rtc-get 4 r))))))))

(defthm fn-rtc-slots-okp-get
  (implies (and (natp i) (natp k) (< k (len slots))
                (fn-rtc-slots-okp i slots))
           (and (fn-rtc-slotp (fn-rtc-get k slots))
                (if (equal (+ i k) 0)
                    (equal (fn-rtc-get k slots) *fn-rtc-listener*)
                  (iff (null (fn-rtc-s-res (fn-rtc-get k slots)))
                       (equal (fn-rtc-s-status (fn-rtc-get k slots)) :free)))))
  :hints (("Goal" :induct (fn-rtc-index-induct k i slots)
           :in-theory (disable fn-rtc-slotp fn-rtc-s-status fn-rtc-s-res))))

(defthm fn-rtc-slots-okp-set
  (implies (and (natp i) (natp k) (fn-rtc-slots-okp i slots)
                (fn-rtc-slotp slot)
                (if (equal (+ i k) 0)
                    (equal slot *fn-rtc-listener*)
                  (iff (null (fn-rtc-s-res slot))
                       (equal (fn-rtc-s-status slot) :free))))
           (fn-rtc-slots-okp i (fn-rtc-set k slot slots)))
  :hints (("Goal" :induct (fn-rtc-index-induct k i slots)
           :in-theory (disable fn-rtc-slotp fn-rtc-s-status fn-rtc-s-res))))

(defthm fn-rtc-slot-accessors
  (and (equal (fn-rtc-s-inc (list inc status res)) (nfix inc))
       (equal (fn-rtc-s-status (list inc status res)) status)
       (equal (fn-rtc-s-res (list inc status res)) res)))

(defthm fn-rtc-buffer-accessors
  (and (equal (fn-rtc-b-gen (list gen owner bytes)) (nfix gen))
       (equal (fn-rtc-b-owner (list gen owner bytes)) owner)
       (equal (fn-rtc-b-bytes (list gen owner bytes)) bytes)))

(defthm fn-rtc-pool-okp-of-closing-slot
  (implies (and (natp id) (fn-rtc-live-p id inc s) (fn-rtc-pool-okp i pool s))
           (fn-rtc-pool-okp i pool
             (fn-rtc-with-slot id (list inc :closing res) s)))
  :hints (("Goal" :induct (fn-rtc-pool-okp i pool s)
           :in-theory
           (e/d (fn-rtc-pool-okp fn-rtc-buffer-okp)
                (fn-rtc-pool-okp-unfolds fn-rtc-bufferp fn-rtc-holds-p
                 fn-rtc-s-inc fn-rtc-s-status fn-rtc-b-owner fn-rtc-b-gen)))))

(defthm fn-rtc-use-okp-of-closing-slot
  (implies (and (natp id) (fn-rtc-live-p id inc s) (fn-rtc-use-okp u s))
           (fn-rtc-use-okp u (fn-rtc-with-slot id (list inc :closing res) s)))
  :hints (("Goal" :in-theory
           (union-theories (theory 'minimal-theory)
            '(fn-rtc-use-okp fn-rtc-current-p fn-rtc-live-p fn-rtc-slot-accessors
              fn-rtc-with-accessors fn-rtc-slot-of-with fn-rtc-buffer-of-with
              fn-rtc-next-op-of-with (:type-prescription fn-rtc-s-inc)
              nfix natp (:executable-counterpart member-equal))))))

(defthm fn-rtc-uses-okp-of-closing-slot
  (implies (and (natp id) (fn-rtc-live-p id inc s) (fn-rtc-uses-okp uses s))
           (fn-rtc-uses-okp uses (fn-rtc-with-slot id (list inc :closing res) s)))
  :hints (("Goal" :induct (fn-rtc-uses-okp uses s)
           :in-theory (union-theories (theory 'minimal-theory)
                        '(fn-rtc-uses-okp fn-rtc-use-okp-of-closing-slot)))))

(defthm fn-rtc-draining-okp-set-nondraining
  (implies (and (fn-rtc-draining-okp i slots uses) (natp k) (natp i)
                (not (equal (fn-rtc-s-status slot) :draining)))
           (fn-rtc-draining-okp i (fn-rtc-set k slot slots) uses))
  :hints (("Goal" :induct (fn-rtc-index-induct k i slots)
           :in-theory (disable fn-rtc-uses-of-slot-p fn-rtc-s-inc fn-rtc-s-status))))

(defthm fn-rtc-with-slot-record
  (and (true-listp (fn-rtc-with-slot id slot s))
       (equal (len (fn-rtc-with-slot id slot s)) 6)
       (equal (fn-rtc-get 5 (fn-rtc-with-slot id slot s)) (fn-rtc-next-op s)))
  :hints (("Goal" :in-theory (enable fn-rtc-with-slot))))

(defthm fn-rtc-core-invp-slot
  (implies (and (fn-rtc-core-invp s) (natp id)
                (< id (fn-rtc-nslots (fn-rtc-config s))))
           (and (fn-rtc-slotp (fn-rtc-slot id s))
                (if (equal id 0)
                    (equal (fn-rtc-slot id s) *fn-rtc-listener*)
                  (iff (null (fn-rtc-s-res (fn-rtc-slot id s)))
                       (equal (fn-rtc-s-status (fn-rtc-slot id s)) :free)))))
  :hints (("Goal" :use ((:instance fn-rtc-slots-okp-get
                                    (i 0) (k id) (slots (fn-rtc-slots s))))
           :in-theory (disable fn-rtc-pool-okp-unfolds fn-rtc-uses-okp
                               fn-rtc-slots-okp fn-rtc-mstates-okp fn-rtc-slotp
                               fn-rtc-s-res fn-rtc-s-status
                               fn-rtc-draining-okp fn-rtc-configp fn-rtc-get))))

(defthm fn-rtc-statics-okp-of-set-after
  (implies (and (natp j) (natp n) (natp k) (<= (+ j n) k))
           (equal (fn-rtc-statics-okp j n (fn-rtc-set k x slots))
                  (fn-rtc-statics-okp j n slots)))
  :hints (("Goal" :induct (fn-rtc-statics-okp j n slots)
           :in-theory (disable fn-rtc-get fn-rtc-set))))

(defthm fn-rtc-core-invp-of-closing-dynamic-slot
  (implies (and (fn-rtc-core-invp s) (fn-rtc-instance-active-p id inc s)
                (fn-rtc-live-p id inc s)
                (< (fn-rtc-nstatic (fn-rtc-config s)) id))
           (fn-rtc-core-invp
            (fn-rtc-with-slot id (list inc :closing (fn-rtc-s-res (fn-rtc-slot id s))) s)))
  :hints (("Goal" :use fn-rtc-core-invp-slot
           :in-theory (disable fn-rtc-configp fn-rtc-slots-okp fn-rtc-pool-okp-unfolds
                               fn-rtc-uses-okp fn-rtc-mstates-okp fn-rtc-draining-okp
                               fn-rtc-core-invp-slot))))

(defthm fn-rtc-holds-p-cons
  (implies (fn-rtc-holds-p h g uses) (fn-rtc-holds-p h g (cons u uses)))
  :hints (("Goal" :expand ((fn-rtc-holds-p h g (cons u uses))) :in-theory
           (union-theories (theory 'minimal-theory) '(fn-rtc-holds-p car-cons cdr-cons)))))

(defthm fn-rtc-pool-okp-of-issue
  (implies (fn-rtc-pool-okp i pool s)
           (fn-rtc-pool-okp i pool (fn-rtc-issue u s)))
  :hints (("Goal" :induct (fn-rtc-pool-okp i pool s)
           :in-theory (union-theories (theory 'minimal-theory)
                        '(fn-rtc-pool-okp fn-rtc-issue-frame fn-rtc-holds-p-cons)))))

(defthm fn-rtc-uses-of-slot-cons
  (implies (fn-rtc-uses-of-slot-p id inc uses)
           (fn-rtc-uses-of-slot-p id inc (cons u uses)))
  :hints (("Goal" :expand ((fn-rtc-uses-of-slot-p id inc (cons u uses))) :in-theory
           (union-theories (theory 'minimal-theory) '(fn-rtc-uses-of-slot-p car-cons cdr-cons)))))

(defthm fn-rtc-draining-okp-cons
  (implies (fn-rtc-draining-okp i slots uses)
           (fn-rtc-draining-okp i slots (cons u uses)))
  :hints (("Goal" :induct (fn-rtc-draining-okp i slots uses)
           :in-theory (union-theories (theory 'minimal-theory)
                        '(fn-rtc-draining-okp fn-rtc-uses-of-slot-cons)))))

(defthm fn-rtc-holders-cons-unbuffered
  (implies (not (fn-rtc-handlep (fn-rtc-u-hd u)))
           (equal (fn-rtc-holders h g (cons u uses)) (fn-rtc-holders h g uses)))
  :hints (("Goal" :expand ((fn-rtc-holders h g (cons u uses))) :in-theory
           (union-theories (theory 'minimal-theory)
            '(fn-rtc-holders (:type-prescription fn-rtc-holders) car-cons cdr-cons
              unicity-of-0 fix)))))

(defthm fn-rtc-use-okp-of-unbuffered-issue
  (implies (and (fn-rtc-use-okp u s) (not (fn-rtc-handlep (fn-rtc-u-hd new))))
           (fn-rtc-use-okp u (fn-rtc-issue new s)))
  :hints (("Goal" :in-theory
           (union-theories (theory 'minimal-theory)
            '(fn-rtc-use-okp fn-rtc-current-p fn-rtc-issue-frame
              fn-rtc-holders-cons-unbuffered (:type-prescription fn-rtc-next-op))))))

(defthm fn-rtc-uses-okp-of-unbuffered-issue
  (implies (and (fn-rtc-uses-okp uses s) (not (fn-rtc-handlep (fn-rtc-u-hd new))))
           (fn-rtc-uses-okp uses (fn-rtc-issue new s)))
  :hints (("Goal" :induct (fn-rtc-uses-okp uses s)
           :in-theory (union-theories (theory 'minimal-theory)
                        '(fn-rtc-uses-okp fn-rtc-use-okp-of-unbuffered-issue)))))

(defthm fn-rtc-issue-record
  (and (true-listp (fn-rtc-issue u s))
       (equal (len (fn-rtc-issue u s)) 6)
       (equal (fn-rtc-get 5 (fn-rtc-issue u s)) (+ 1 (fn-rtc-next-op s))))
  :hints (("Goal" :in-theory (enable fn-rtc-issue))))

(defthm fn-rtc-core-invp-of-unbuffered-issue
  (implies (and (fn-rtc-core-invp s)
                (not (fn-rtc-handlep (fn-rtc-u-hd u)))
                (fn-rtc-use-okp u (fn-rtc-issue u s))
                (not (fn-rtc-kind-out-p (fn-rtc-get 0 u) (fn-rtc-get 1 u)
                                        (fn-rtc-get 2 u) (fn-rtc-uses s)))
                (not (fn-rtc-op-used-p (fn-rtc-get 3 u) (fn-rtc-uses s))))
           (fn-rtc-core-invp (fn-rtc-issue u s)))
  :hints (("Goal" :in-theory
           (disable fn-rtc-configp fn-rtc-slots-okp fn-rtc-pool-okp-unfolds
                    fn-rtc-uses-okp fn-rtc-use-okp fn-rtc-mstates-okp
                    fn-rtc-draining-okp fn-rtc-get fn-rtc-kind-out-p
                    fn-rtc-op-used-p fn-rtc-u-hd fn-rtc-handlep)
           :expand ((fn-rtc-uses-okp (cons u (fn-rtc-uses s)) (fn-rtc-issue u s))))))

(defthm fn-rtc-op-not-used-above-next
  (implies (and (fn-rtc-uses-okp uses s) (natp op) (<= (fn-rtc-next-op s) op))
           (not (fn-rtc-op-used-p op uses)))
  :hints (("Goal" :induct (fn-rtc-uses-okp uses s)
           :in-theory (disable fn-rtc-usep fn-rtc-handlep fn-rtc-holders
                               fn-rtc-current-p fn-rtc-get fn-rtc-u-hd
                               fn-rtc-b-gen fn-rtc-b-owner fn-rtc-b-bytes
                               fn-rtc-h-buf fn-rtc-h-gen fn-rtc-h-off fn-rtc-h-len))))

(defthm fn-rtc-core-invp-uses
  (implies (fn-rtc-core-invp s) (fn-rtc-uses-okp (fn-rtc-uses s) s))
  :hints (("Goal" :in-theory
           (disable fn-rtc-configp fn-rtc-slots-okp fn-rtc-pool-okp-unfolds
                    fn-rtc-uses-okp fn-rtc-mstates-okp fn-rtc-draining-okp)))
  :rule-classes :forward-chaining)

(defthm fn-rtc-live-slot-has-no-close
  (implies (and (natp id) (fn-rtc-live-p id inc s) (fn-rtc-uses-okp uses s))
           (not (fn-rtc-kind-out-p :close id inc uses)))
  :hints (("Goal" :induct (fn-rtc-uses-okp uses s)
           :in-theory (union-theories (theory 'minimal-theory)
                        '(fn-rtc-use-okp fn-rtc-uses-okp fn-rtc-kind-out-p
                          fn-rtc-live-p nfix natp)))))

(defthm fn-rtc-fresh-unbuffered-use-okp
  (implies (and (member-eq kind '(:fsync :close :accept :timer))
                (natp id) (natp inc) (< id (fn-rtc-nslots (fn-rtc-config s)))
                (fn-rtc-current-p id inc s)
                (iff (eq kind :accept) (equal id 0))
                (implies (eq kind :close)
                         (eq (fn-rtc-s-status (fn-rtc-slot id s)) :closing)))
           (fn-rtc-use-okp (list kind id inc (fn-rtc-next-op s) nil)
             (fn-rtc-issue (list kind id inc (fn-rtc-next-op s) nil) s)))
  :hints (("Goal" :in-theory (disable fn-rtc-get-of-non-natp))))

(defthm fn-rtc-core-invp-of-fresh-unbuffered-issue
  (implies (and (fn-rtc-core-invp s)
                (equal op (fn-rtc-next-op s))
                (member-eq kind '(:fsync :close :accept :timer))
                (natp id) (natp inc) (< id (fn-rtc-nslots (fn-rtc-config s)))
                (fn-rtc-current-p id inc s)
                (iff (eq kind :accept) (equal id 0))
                (implies (eq kind :close)
                         (eq (fn-rtc-s-status (fn-rtc-slot id s)) :closing))
                (not (fn-rtc-kind-out-p kind id inc (fn-rtc-uses s))))
           (fn-rtc-core-invp
            (fn-rtc-issue (list kind id inc op nil) s)))
  :hints (("Goal" :in-theory
           (disable fn-rtc-core-invp fn-rtc-use-okp fn-rtc-uses-okp fn-rtc-kind-out-p
                    fn-rtc-current-p fn-rtc-nslots fn-rtc-s-status))))

(defthm fn-rtc-core-invp-shape
  (implies (fn-rtc-core-invp s)
           (and (fn-rtc-configp (fn-rtc-config s))
                (equal (len (fn-rtc-slots s)) (fn-rtc-nslots (fn-rtc-config s)))
                (equal (len (fn-rtc-pool s)) (fn-rtc-nbufs (fn-rtc-config s)))
                (equal (len (fn-rtc-mstates s)) (fn-rtc-nslots (fn-rtc-config s)))))
  :hints (("Goal" :in-theory
           (disable fn-rtc-configp fn-rtc-slots-okp fn-rtc-pool-okp-unfolds
                    fn-rtc-uses-okp fn-rtc-mstates-okp fn-rtc-draining-okp)))
  :rule-classes :forward-chaining)

(defthm fn-rtc-close-preserves-core-invp
  (implies (and (fn-rtc-core-invp s) (fn-rtc-instance-active-p id inc s))
           (fn-rtc-core-invp (mv-nth 0 (fn-rtc-req-close r id inc s))))
  :hints (("Goal" :in-theory
           (disable mv-nth fn-rtc-use-bound fn-rtc-nbufs fn-rtc-nstatic fn-rtc-live-p
                    fn-rtc-core-invp fn-rtc-uses-okp fn-rtc-use-okp fn-rtc-kind-out-p
                    fn-rtc-s-status fn-rtc-s-inc fn-rtc-s-res fn-rtc-nslots)
           :use ((:instance fn-rtc-live-slot-has-no-close (uses (fn-rtc-uses s)))))))

; A new holder must not join an existing input lease.
(defun fn-rtc-compatible-use-p (new u)
  (declare (xargs :guard t))
  (or (not (or (member-eq (fn-rtc-get 0 u) *fn-rtc-in-kinds*)
               (equal (fn-rtc-get 0 u) :hand)))
      (not (fn-rtc-handlep (fn-rtc-u-hd new)))
      (not (equal (fn-rtc-h-buf (fn-rtc-u-hd new)) (fn-rtc-h-buf (fn-rtc-u-hd u))))
      (not (equal (fn-rtc-h-gen (fn-rtc-u-hd new)) (fn-rtc-h-gen (fn-rtc-u-hd u))))))

(defun fn-rtc-compatible-usesp (new uses)
  (declare (xargs :guard t))
  (if (consp uses)
      (and (fn-rtc-compatible-use-p new (car uses))
           (fn-rtc-compatible-usesp new (cdr uses)))
    t))

(defthm fn-rtc-holders-cons
  (equal (fn-rtc-holders h g (cons u uses))
         (+ (if (and (fn-rtc-handlep (fn-rtc-u-hd u))
                     (equal (fn-rtc-h-buf (fn-rtc-u-hd u)) h)
                     (equal (fn-rtc-h-gen (fn-rtc-u-hd u)) g)) 1 0)
            (fn-rtc-holders h g uses)))
  :hints (("Goal" :expand ((fn-rtc-holders h g (cons u uses)))
           :in-theory (union-theories (theory 'minimal-theory)
                        '(car-cons cdr-cons)))))

(defthm fn-rtc-use-okp-of-compatible-issue
  (implies (and (fn-rtc-use-okp u s) (fn-rtc-compatible-use-p new u))
           (fn-rtc-use-okp u (fn-rtc-issue new s)))
  :hints (("Goal" :in-theory
           (union-theories (theory 'minimal-theory)
            '(fn-rtc-use-okp fn-rtc-current-p fn-rtc-issue-frame fn-rtc-compatible-use-p
              fn-rtc-holders-cons (:type-prescription fn-rtc-next-op)
              (:type-prescription fn-rtc-holders) unicity-of-0 fix)))))

(defthm fn-rtc-uses-okp-of-compatible-issue
  (implies (and (fn-rtc-uses-okp uses s) (fn-rtc-compatible-usesp new uses))
           (fn-rtc-uses-okp uses (fn-rtc-issue new s)))
  :hints (("Goal" :induct (fn-rtc-uses-okp uses s)
           :in-theory (union-theories (theory 'minimal-theory)
                        '(fn-rtc-uses-okp fn-rtc-compatible-usesp
                          fn-rtc-use-okp-of-compatible-issue)))))

(defthm fn-rtc-compatible-use-from-shareable-pool
  (implies (and (fn-rtc-use-okp u s)
                (or (not (fn-rtc-handlep (fn-rtc-u-hd new)))
                    (not (fn-rtc-leasedp (fn-rtc-h-buf (fn-rtc-u-hd new)) s))
                    (and (equal (fn-rtc-get 0 (fn-rtc-b-owner
                                   (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd new)) s))) :leased)
                         (equal (fn-rtc-get 3 (fn-rtc-b-owner
                                   (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd new)) s))) :out))))
           (fn-rtc-compatible-use-p new u))
  :hints (("Goal" :in-theory
           (union-theories (theory 'minimal-theory)
            '(fn-rtc-use-okp fn-rtc-usep fn-rtc-u-hd
              fn-rtc-compatible-use-p fn-rtc-leasedp (:executable-counterpart member-equal))))))

(defthm fn-rtc-compatible-uses-from-shareable-pool
  (implies (and (fn-rtc-uses-okp uses s)
                (or (not (fn-rtc-handlep (fn-rtc-u-hd new)))
                    (not (fn-rtc-leasedp (fn-rtc-h-buf (fn-rtc-u-hd new)) s))
                    (and (equal (fn-rtc-get 0 (fn-rtc-b-owner
                                   (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd new)) s))) :leased)
                         (equal (fn-rtc-get 3 (fn-rtc-b-owner
                                   (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd new)) s))) :out))))
           (fn-rtc-compatible-usesp new uses))
  :hints (("Goal" :induct (fn-rtc-uses-okp uses s)
           :in-theory (union-theories (theory 'minimal-theory)
                        '(fn-rtc-uses-okp fn-rtc-compatible-usesp
                          fn-rtc-compatible-use-from-shareable-pool)))))

(defthm fn-rtc-core-invp-of-compatible-issue
  (implies (and (fn-rtc-core-invp s)
                (fn-rtc-compatible-usesp u (fn-rtc-uses s))
                (fn-rtc-use-okp u (fn-rtc-issue u s))
                (not (fn-rtc-kind-out-p (fn-rtc-get 0 u) (fn-rtc-get 1 u)
                                        (fn-rtc-get 2 u) (fn-rtc-uses s)))
                (not (fn-rtc-op-used-p (fn-rtc-get 3 u) (fn-rtc-uses s))))
           (fn-rtc-core-invp (fn-rtc-issue u s)))
  :hints (("Goal" :in-theory
           (disable fn-rtc-configp fn-rtc-slots-okp fn-rtc-pool-okp-unfolds
                    fn-rtc-uses-okp fn-rtc-use-okp fn-rtc-mstates-okp
                    fn-rtc-draining-okp fn-rtc-get fn-rtc-kind-out-p
                    fn-rtc-op-used-p fn-rtc-compatible-usesp)
           :expand ((fn-rtc-uses-okp (cons u (fn-rtc-uses s)) (fn-rtc-issue u s))))))

(defthm fn-rtc-core-invp-of-new-lease-issue
  (implies (and (fn-rtc-core-invp s) (natp h) (not (fn-rtc-leasedp h s))
                (fn-rtc-compatible-usesp u (fn-rtc-uses s))
                (fn-rtc-buffer-okp h b (fn-rtc-issue u (fn-rtc-with-buffer h b s)))
                (fn-rtc-use-okp u (fn-rtc-issue u (fn-rtc-with-buffer h b s)))
                (not (fn-rtc-kind-out-p (fn-rtc-get 0 u) (fn-rtc-get 1 u)
                                        (fn-rtc-get 2 u) (fn-rtc-uses s)))
                (not (fn-rtc-op-used-p (fn-rtc-get 3 u) (fn-rtc-uses s))))
           (fn-rtc-core-invp (fn-rtc-issue u (fn-rtc-with-buffer h b s))))
  :hints (("Goal" :in-theory
           (disable fn-rtc-configp fn-rtc-slots-okp fn-rtc-pool-okp-unfolds
                    fn-rtc-uses-okp fn-rtc-use-okp fn-rtc-mstates-okp
                    fn-rtc-draining-okp fn-rtc-get fn-rtc-kind-out-p fn-rtc-leasedp
                    fn-rtc-op-used-p fn-rtc-compatible-usesp)
           :expand ((fn-rtc-uses-okp (cons u (fn-rtc-uses s))
                      (fn-rtc-issue u (fn-rtc-with-buffer h b s)))))))

(defthm fn-rtc-holders-of-unleased-buffer
  (implies (and (fn-rtc-uses-okp uses s) (not (fn-rtc-leasedp h s)))
           (equal (fn-rtc-holders h g uses) 0))
  :hints (("Goal" :induct (fn-rtc-uses-okp uses s)
           :in-theory (union-theories (theory 'minimal-theory)
                        '((:executable-counterpart member-equal) fn-rtc-uses-okp fn-rtc-use-okp fn-rtc-leasedp
                          fn-rtc-holders unicity-of-0 fix
                          (:type-prescription fn-rtc-holders))))))

; Proof notation for the successful buffered-submit arm, not a new runtime entry.
(defun fn-rtc-buffered-submit-state (kind hd id inc s)
  (declare (xargs :guard t))
  (let* ((h (fn-rtc-h-buf hd)) (b (fn-rtc-buffer h s))
         (dir (if (member-eq kind *fn-rtc-in-kinds*) :in :out))
         (s1 (if (equal (fn-rtc-b-owner b) (list :workspace id inc))
                 (fn-rtc-with-buffer
                  h (list (fn-rtc-b-gen b) (list :leased id inc dir) (fn-rtc-b-bytes b)) s)
               s)))
    (fn-rtc-issue (list kind id inc (fn-rtc-next-op s1) hd) s1)))

(defthm fn-rtc-buffered-submit-new-use-okp
  (implies (and (fn-rtc-core-invp s) (fn-rtc-instance-active-p id inc s)
                (fn-rtc-live-p id inc s)
                (member-eq kind '(:recv :send :pread :pwrite :bp-send))
                (fn-rtc-submit-okp kind hd id inc s))
           (fn-rtc-use-okp (list kind id inc (fn-rtc-next-op s) hd)
                          (fn-rtc-buffered-submit-state kind hd id inc s)))
  :hints (("Goal" :in-theory
           (disable fn-rtc-core-invp fn-rtc-handlep fn-rtc-holders fn-rtc-uses-okp
                    fn-rtc-s-inc fn-rtc-s-status fn-rtc-b-owner fn-rtc-b-gen fn-rtc-b-bytes
                    fn-rtc-h-buf fn-rtc-h-gen fn-rtc-h-off fn-rtc-h-len
                    fn-rtc-nbufs fn-rtc-nslots fn-rtc-cap fn-rtc-configp)
           :use ((:instance fn-rtc-holders-of-unleased-buffer
                  (h (fn-rtc-h-buf hd)) (g (fn-rtc-h-gen hd)) (uses (fn-rtc-uses s)))))))

(defthm fn-rtc-core-invp-buffer-bytes
  (implies (and (fn-rtc-core-invp s) (natp h)
                (< h (fn-rtc-nbufs (fn-rtc-config s))))
           (and (fn-cbor-octet-listp (fn-rtc-b-bytes (fn-rtc-buffer h s)))
                (<= (len (fn-rtc-b-bytes (fn-rtc-buffer h s)))
                    (fn-rtc-cap (fn-rtc-config s)))))
  :hints (("Goal" :use ((:instance fn-rtc-core-invp-buffer)
                        (:instance fn-rtc-buffer-okp-bytes (b (fn-rtc-buffer h s))))
           :in-theory (theory 'minimal-theory))))

(defthm fn-rtc-buffered-submit-preserves-core-invp
  (implies (and (fn-rtc-core-invp s) (fn-rtc-instance-active-p id inc s)
                (fn-rtc-live-p id inc s)
                (member-eq kind '(:recv :send :pread :pwrite :bp-send))
                (fn-rtc-submit-okp kind hd id inc s)
                (not (fn-rtc-kind-out-p kind id inc (fn-rtc-uses s))))
           (fn-rtc-core-invp (fn-rtc-buffered-submit-state kind hd id inc s)))
  :hints (("Goal" :in-theory
           (e/d (fn-rtc-buffer-okp)
                (fn-rtc-core-invp fn-rtc-handlep fn-rtc-uses-okp fn-rtc-use-okp
                 fn-rtc-s-inc fn-rtc-s-status fn-rtc-b-owner fn-rtc-b-gen fn-rtc-b-bytes
                 fn-rtc-h-buf fn-rtc-h-gen fn-rtc-h-off fn-rtc-h-len fn-cbor-octet-listp
                 fn-rtc-nbufs fn-rtc-nslots fn-rtc-cap fn-rtc-configp fn-rtc-kind-out-p
                 fn-rtc-compatible-usesp fn-rtc-op-used-p
                 fn-rtc-buffered-submit-new-use-okp))
           :use (fn-rtc-buffered-submit-new-use-okp
                 (:instance fn-rtc-compatible-uses-from-shareable-pool
                   (uses (fn-rtc-uses s)) (new (list kind id inc (fn-rtc-next-op s) hd)))
                 (:instance fn-rtc-core-invp-buffer-bytes (h (fn-rtc-h-buf hd)))))))

(defthm fn-rtc-core-invp-of-distinct-compatible-issue
  (implies (and (fn-rtc-core-invp s)
                (fn-rtc-compatible-usesp u (fn-rtc-uses s))
                (fn-rtc-use-okp u (fn-rtc-issue u s))
                (or (equal (fn-rtc-get 0 u) :hand)
                    (not (fn-rtc-kind-out-p (fn-rtc-get 0 u) (fn-rtc-get 1 u)
                                            (fn-rtc-get 2 u) (fn-rtc-uses s))))
                (not (fn-rtc-op-used-p (fn-rtc-get 3 u) (fn-rtc-uses s))))
           (fn-rtc-core-invp (fn-rtc-issue u s)))
  :hints (("Goal" :in-theory
           (disable fn-rtc-configp fn-rtc-slots-okp fn-rtc-pool-okp-unfolds
                    fn-rtc-uses-okp fn-rtc-use-okp fn-rtc-mstates-okp
                    fn-rtc-draining-okp fn-rtc-get fn-rtc-kind-out-p
                    fn-rtc-op-used-p fn-rtc-compatible-usesp)
           :expand ((fn-rtc-uses-okp (cons u (fn-rtc-uses s)) (fn-rtc-issue u s))))))

(defthm fn-rtc-core-invp-of-exclusive-buffer-issue
  (implies (and (fn-rtc-core-invp s) (natp h) (not (fn-rtc-leasedp h s))
                (fn-rtc-compatible-usesp u (fn-rtc-uses s))
                (fn-rtc-buffer-okp h b (fn-rtc-issue u (fn-rtc-with-buffer h b s)))
                (fn-rtc-use-okp u (fn-rtc-issue u (fn-rtc-with-buffer h b s)))
                (or (equal (fn-rtc-get 0 u) :hand)
                    (not (fn-rtc-kind-out-p (fn-rtc-get 0 u) (fn-rtc-get 1 u)
                                            (fn-rtc-get 2 u) (fn-rtc-uses s))))
                (not (fn-rtc-op-used-p (fn-rtc-get 3 u) (fn-rtc-uses s))))
           (fn-rtc-core-invp (fn-rtc-issue u (fn-rtc-with-buffer h b s))))
  :hints (("Goal" :in-theory
           (disable fn-rtc-configp fn-rtc-slots-okp fn-rtc-pool-okp-unfolds
                    fn-rtc-uses-okp fn-rtc-use-okp fn-rtc-mstates-okp
                    fn-rtc-draining-okp fn-rtc-get fn-rtc-kind-out-p fn-rtc-leasedp
                    fn-rtc-op-used-p fn-rtc-compatible-usesp)
           :expand ((fn-rtc-uses-okp (cons u (fn-rtc-uses s))
                      (fn-rtc-issue u (fn-rtc-with-buffer h b s)))))))

(defun fn-rtc-hand-submit-state (hd extra id inc s)
  (declare (xargs :guard t))
  (let* ((h (fn-rtc-h-buf hd)) (b (fn-rtc-buffer h s))
         (s1 (fn-rtc-with-buffer h
               (list (fn-rtc-b-gen b)
                     (list :handed id inc (fn-rtc-get 0 extra) (fn-rtc-get 1 extra))
                     (fn-rtc-b-bytes b)) s)))
    (fn-rtc-issue (list :hand id inc (fn-rtc-next-op s1) hd) s1)))

(defthm fn-rtc-hand-submit-new-use-okp
  (implies (and (fn-rtc-core-invp s) (fn-rtc-instance-active-p id inc s)
                (fn-rtc-live-p id inc s) (fn-rtc-submit-okp :hand hd id inc s))
           (fn-rtc-use-okp (list :hand id inc (fn-rtc-next-op s) hd)
                          (fn-rtc-hand-submit-state hd extra id inc s)))
  :hints (("Goal" :in-theory
           (disable fn-rtc-core-invp fn-rtc-handlep fn-rtc-holders fn-rtc-uses-okp
                    fn-rtc-s-inc fn-rtc-s-status fn-rtc-b-owner fn-rtc-b-gen fn-rtc-b-bytes
                    fn-rtc-h-buf fn-rtc-h-gen fn-rtc-h-off fn-rtc-h-len
                    fn-rtc-nbufs fn-rtc-nslots fn-rtc-cap fn-rtc-configp)
           :use ((:instance fn-rtc-holders-of-unleased-buffer
                  (h (fn-rtc-h-buf hd)) (g (fn-rtc-h-gen hd)) (uses (fn-rtc-uses s)))))))

(defthm fn-rtc-hand-submit-preserves-core-invp
  (implies (and (fn-rtc-core-invp s) (fn-rtc-instance-active-p id inc s)
                (fn-rtc-live-p id inc s) (fn-rtc-submit-okp :hand hd id inc s)
                (fn-rtc-hand-target-okp extra id s))
           (fn-rtc-core-invp (fn-rtc-hand-submit-state hd extra id inc s)))
  :hints (("Goal" :in-theory
           (e/d (fn-rtc-buffer-okp)
                (fn-rtc-core-invp fn-rtc-handlep fn-rtc-uses-okp fn-rtc-use-okp
                 fn-rtc-s-inc fn-rtc-s-status fn-rtc-b-owner fn-rtc-b-gen fn-rtc-b-bytes
                 fn-rtc-h-buf fn-rtc-h-gen fn-rtc-h-off fn-rtc-h-len fn-cbor-octet-listp
                 fn-rtc-nbufs fn-rtc-nslots fn-rtc-nstatic fn-rtc-cap fn-rtc-configp
                 fn-rtc-kind-out-p fn-rtc-compatible-usesp fn-rtc-op-used-p
                 fn-rtc-hand-submit-new-use-okp))
           :use (fn-rtc-hand-submit-new-use-okp
                 (:instance fn-rtc-compatible-uses-from-shareable-pool
                   (uses (fn-rtc-uses s)) (new (list :hand id inc (fn-rtc-next-op s) hd)))
                 (:instance fn-rtc-core-invp-buffer-bytes (h (fn-rtc-h-buf hd)))))))

(defthm fn-rtc-hand-submit-okp-owner
  (implies (fn-rtc-submit-okp :hand hd id inc s)
           (equal (fn-rtc-b-owner (fn-rtc-buffer (fn-rtc-h-buf hd) s))
                  (list :workspace id inc)))
  :hints (("Goal" :in-theory (e/d (fn-rtc-submit-okp)
                                  (fn-rtc-b-owner fn-rtc-buffer fn-rtc-h-buf fn-rtc-handlep)))))

(defthm fn-rtc-submit-preserves-core-invp
  (implies (and (fn-rtc-core-invp s) (fn-rtc-instance-active-p id inc s))
           (fn-rtc-core-invp (mv-nth 0 (fn-rtc-req-submit r id inc s))))
  :hints (("Goal" :in-theory
           (disable fn-rtc-core-invp fn-rtc-submit-okp
                    fn-rtc-kind-out-p fn-rtc-use-okp fn-rtc-uses-okp
                    fn-rtc-b-owner fn-rtc-b-gen fn-rtc-b-bytes fn-rtc-s-res
                    fn-rtc-nslots fn-rtc-nbufs fn-rtc-configp fn-rtc-s-inc fn-rtc-s-status
                    fn-rtc-h-buf fn-rtc-hand-target-okp fn-rtc-nstatic fn-rtc-use-bound mv-nth
                    fn-rtc-buffered-submit-preserves-core-invp fn-rtc-hand-submit-preserves-core-invp)
           :use ((:instance fn-rtc-hand-submit-preserves-core-invp
                  (hd (fn-rtc-get 2 r)) (extra (fn-rtc-get 3 r)))
                 (:instance fn-rtc-buffered-submit-preserves-core-invp
                  (kind (fn-rtc-get 1 r)) (hd (fn-rtc-get 2 r)))))))

(defthm fn-rtc-request-preserves-core-invp
  (implies (and (fn-rtc-core-invp s) (fn-rtc-instance-active-p id inc s))
           (fn-rtc-core-invp (mv-nth 0 (fn-rtc-request r id inc s))))
  :hints (("Goal" :in-theory
           (e/d (fn-rtc-request)
                (mv-nth fn-rtc-core-invp fn-rtc-instance-active-p fn-rtc-req-acquire
                 fn-rtc-req-write fn-rtc-req-release fn-rtc-req-close fn-rtc-req-submit
                 fn-rtc-req-cancel)))))

(defthm fn-rtc-request-preserves-active
  (implies (fn-rtc-instance-active-p id inc s)
           (fn-rtc-instance-active-p id inc (mv-nth 0 (fn-rtc-request r id inc s))))
  :hints (("Goal" :in-theory
           (e/d (fn-rtc-request)
                (fn-rtc-submit-okp fn-rtc-kind-out-p fn-rtc-extrap fn-rtc-splice
                 fn-rtc-b-owner fn-rtc-b-gen fn-rtc-b-bytes fn-rtc-s-inc fn-rtc-s-status
                 fn-rtc-s-res fn-rtc-nslots fn-rtc-nbufs fn-rtc-cap fn-cbor-octet-listp)))))

(defthm fn-rtc-requests-preserve-core-invp
  (implies (and (fn-rtc-core-invp s) (fn-rtc-instance-active-p id inc s))
           (and (fn-rtc-core-invp (mv-nth 0 (fn-rtc-requests reqs id inc s)))
                (fn-rtc-instance-active-p id inc (mv-nth 0 (fn-rtc-requests reqs id inc s)))))
  :hints (("Goal" :induct (fn-rtc-requests reqs id inc s)
           :in-theory (e/d (fn-rtc-requests)
                           (mv-nth fn-rtc-request fn-rtc-core-invp fn-rtc-instance-active-p)))))

(defthm fn-rtc-active-of-with-mstate
  (equal (fn-rtc-instance-active-p id inc (fn-rtc-with-mstate j m s))
         (fn-rtc-instance-active-p id inc s))
  :hints (("Goal" :in-theory (disable fn-rtc-s-inc fn-rtc-s-status fn-rtc-nslots))))

(defthm fn-rtc-deliver-preserves-core-invp
  (implies (and (fn-rtc-core-invp s) (fn-rtc-instance-active-p id inc s))
           (fn-rtc-core-invp (mv-nth 0 (fn-rtc-deliver s id inc ev q))))
  :hints (("Goal" :in-theory
           (e/d (fn-rtc-deliver)
                (mv-nth fn-rtc-core-invp fn-rtc-instance-active-p fn-rtc-requests
                 fn-rtc-mstate fn-rtc-view fn-rtc-size)))))

(defthm fn-rtc-free-slot-of-set-nonfree
  (implies (and (natp i) (natp k)
                (not (equal (fn-rtc-s-status (fn-rtc-get k slots)) :free))
                (not (equal (fn-rtc-s-status slot) :free)))
           (equal (fn-rtc-free-slot i (fn-rtc-set k slot slots))
                  (fn-rtc-free-slot i slots)))
  :hints (("Goal" :induct (fn-rtc-index-induct k i slots)
           :in-theory (disable fn-rtc-s-status))))

(defthm fn-rtc-request-preserves-free-slot
  (implies (and (natp id) (fn-rtc-core-invp s))
           (equal (fn-rtc-free-slot 0 (fn-rtc-slots (mv-nth 0 (fn-rtc-request r id inc s))))
                  (fn-rtc-free-slot 0 (fn-rtc-slots s))))
  :hints (("Goal" :in-theory
           (e/d (fn-rtc-request)
                (fn-rtc-core-invp fn-rtc-free-slot fn-rtc-submit-okp fn-rtc-kind-out-p
                 fn-rtc-extrap fn-rtc-splice fn-rtc-b-owner fn-rtc-b-gen fn-rtc-b-bytes
                 fn-rtc-s-inc fn-rtc-s-status fn-rtc-s-res fn-rtc-nslots fn-rtc-nbufs
                 fn-rtc-cap fn-cbor-octet-listp))
           :use ((:instance fn-rtc-free-slot-of-set-nonfree
                  (i 0) (k id) (slots (fn-rtc-slots s))
                  (slot (list inc :closing (fn-rtc-s-res (fn-rtc-slot id s)))))))))

(defthm fn-rtc-kind-out-cons
  (equal (fn-rtc-kind-out-p kind id inc (cons u uses))
         (or (and (equal (fn-rtc-get 0 u) kind) (equal (fn-rtc-get 1 u) id)
                  (equal (fn-rtc-get 2 u) inc))
             (fn-rtc-kind-out-p kind id inc uses)))
  :hints (("Goal" :expand ((fn-rtc-kind-out-p kind id inc (cons u uses)))
           :in-theory (union-theories (theory 'minimal-theory) '(car-cons cdr-cons)))))

(defthm fn-rtc-request-preserves-accept
  (equal (fn-rtc-kind-out-p :accept 0 0 (fn-rtc-uses (mv-nth 0 (fn-rtc-request r id inc s))))
         (fn-rtc-kind-out-p :accept 0 0 (fn-rtc-uses s)))
  :hints (("Goal" :in-theory
           (e/d (fn-rtc-request)
                (fn-rtc-kind-out-p fn-rtc-submit-okp fn-rtc-extrap fn-rtc-splice
                 fn-rtc-b-owner fn-rtc-b-gen fn-rtc-b-bytes fn-rtc-s-inc fn-rtc-s-status
                 fn-rtc-s-res fn-rtc-nslots fn-rtc-nbufs fn-rtc-cap fn-cbor-octet-listp)))))

(defthm fn-rtc-active-id-natural
  (implies (fn-rtc-instance-active-p id inc s) (natp id))
  :rule-classes :forward-chaining)

(defthm fn-rtc-requests-preserve-admission-fields
  (implies (and (fn-rtc-core-invp s) (fn-rtc-instance-active-p id inc s))
           (and (equal (fn-rtc-free-slot 0 (fn-rtc-slots (mv-nth 0 (fn-rtc-requests reqs id inc s))))
                       (fn-rtc-free-slot 0 (fn-rtc-slots s)))
                (equal (fn-rtc-kind-out-p :accept 0 0 (fn-rtc-uses (mv-nth 0 (fn-rtc-requests reqs id inc s))))
                       (fn-rtc-kind-out-p :accept 0 0 (fn-rtc-uses s)))))
  :hints (("Goal" :induct (fn-rtc-requests reqs id inc s)
           :in-theory (e/d (fn-rtc-requests)
                           (mv-nth fn-rtc-request fn-rtc-core-invp fn-rtc-instance-active-p fn-rtc-free-slot
                            fn-rtc-kind-out-p fn-rtc-s-inc fn-rtc-s-status fn-rtc-nslots)))))

(defthm fn-rtc-deliver-preserves-admission-fields
  (implies (and (fn-rtc-core-invp s) (fn-rtc-instance-active-p id inc s))
           (and (equal (fn-rtc-free-slot 0 (fn-rtc-slots (mv-nth 0 (fn-rtc-deliver s id inc ev q))))
                       (fn-rtc-free-slot 0 (fn-rtc-slots s)))
                (equal (fn-rtc-kind-out-p :accept 0 0 (fn-rtc-uses (mv-nth 0 (fn-rtc-deliver s id inc ev q))))
                       (fn-rtc-kind-out-p :accept 0 0 (fn-rtc-uses s)))))
  :hints (("Goal" :in-theory
           (e/d (fn-rtc-deliver)
                (mv-nth fn-rtc-core-invp fn-rtc-instance-active-p fn-rtc-requests
                 fn-rtc-free-slot fn-rtc-kind-out-p fn-rtc-mstate fn-rtc-view fn-rtc-size)))))

(defthm fn-rtc-core-invp-listener
  (implies (fn-rtc-core-invp s) (equal (fn-rtc-slot 0 s) *fn-rtc-listener*))
  :hints (("Goal" :use (fn-rtc-core-invp-shape (:instance fn-rtc-core-invp-slot (id 0)))
           :in-theory (disable fn-rtc-core-invp fn-rtc-core-invp-slot fn-rtc-slotp
                               fn-rtc-s-res fn-rtc-s-status))))

(defthm fn-rtc-rearm-preserves-core-invp
  (implies (fn-rtc-core-invp s) (fn-rtc-core-invp (mv-nth 0 (fn-rtc-rearm s))))
  :hints (("Goal" :use (fn-rtc-core-invp-shape fn-rtc-core-invp-listener)
           :in-theory
           (e/d (fn-rtc-rearm)
                (fn-rtc-core-invp fn-rtc-kind-out-p fn-rtc-free-slot)))))

; Removal cannot create a use or increase the number of holders.
(defthm fn-rtc-remove-use-member-subset
  (implies (member-equal u (fn-rtc-remove-use key uses)) (member-equal u uses))
  :hints (("Goal" :induct (fn-rtc-remove-use key uses) :in-theory (disable fn-rtc-key))))

(defthm fn-rtc-remove-use-kind-subset
  (implies (not (fn-rtc-kind-out-p kind id inc uses))
           (not (fn-rtc-kind-out-p kind id inc (fn-rtc-remove-use key uses))))
  :hints (("Goal" :induct (fn-rtc-remove-use key uses)
           :in-theory (disable fn-rtc-key fn-rtc-get))))

(defthm fn-rtc-remove-use-op-subset
  (implies (not (fn-rtc-op-used-p op uses))
           (not (fn-rtc-op-used-p op (fn-rtc-remove-use key uses))))
  :hints (("Goal" :induct (fn-rtc-remove-use key uses)
           :in-theory (disable fn-rtc-key fn-rtc-get))))

(defthm fn-rtc-uses-okp-remove
  (implies (fn-rtc-uses-okp uses s)
           (fn-rtc-uses-okp (fn-rtc-remove-use key uses) s))
  :hints (("Goal" :induct (fn-rtc-remove-use key uses)
           :in-theory (disable fn-rtc-key fn-rtc-use-okp fn-rtc-kind-out-p
                               fn-rtc-op-used-p fn-rtc-get))))

(defthm fn-rtc-holders-remove-bound
  (<= (fn-rtc-holders h g (fn-rtc-remove-use key uses)) (fn-rtc-holders h g uses))
  :hints (("Goal" :induct (fn-rtc-remove-use key uses)
           :in-theory (disable fn-rtc-key fn-rtc-handlep fn-rtc-u-hd fn-rtc-h-buf fn-rtc-h-gen)))
  :rule-classes (:rewrite :linear))

(defthm fn-rtc-member-holder-positive
  (implies (and (member-equal u uses) (fn-rtc-handlep (fn-rtc-u-hd u)))
           (< 0 (fn-rtc-holders (fn-rtc-h-buf (fn-rtc-u-hd u))
                                 (fn-rtc-h-gen (fn-rtc-u-hd u)) uses)))
  :hints (("Goal" :induct (member-equal u uses)
           :in-theory (disable fn-rtc-handlep fn-rtc-u-hd fn-rtc-h-buf fn-rtc-h-gen)))
  :rule-classes (:rewrite :linear))

(defthm fn-rtc-use-okp-after-removal
  (implies (and (fn-rtc-use-okp u s)
                (member-equal u (fn-rtc-remove-use key (fn-rtc-uses s))))
           (fn-rtc-use-okp u (fn-rtc-with-uses (fn-rtc-remove-use key (fn-rtc-uses s)) s)))
  :hints (("Goal" :in-theory
           (e/d (fn-rtc-use-okp fn-rtc-current-p)
                (fn-rtc-usep fn-rtc-handlep fn-rtc-holders fn-rtc-remove-use fn-rtc-uses
                 fn-rtc-get fn-rtc-u-hd fn-rtc-b-gen fn-rtc-b-owner fn-rtc-b-bytes
                 fn-rtc-h-buf fn-rtc-h-gen fn-rtc-h-off fn-rtc-h-len
                 fn-rtc-s-inc fn-rtc-s-status fn-rtc-nbufs fn-rtc-nslots fn-rtc-cap))
           :use ((:instance fn-rtc-holders-remove-bound
                  (h (fn-rtc-h-buf (fn-rtc-u-hd u))) (g (fn-rtc-h-gen (fn-rtc-u-hd u)))
                  (uses (fn-rtc-uses s)))
                 (:instance fn-rtc-member-holder-positive
                  (uses (fn-rtc-remove-use key (fn-rtc-uses s))))))))

(defthm fn-rtc-uses-okp-after-removal-subset
  (implies (and (fn-rtc-uses-okp uses s)
                (subsetp-equal uses (fn-rtc-remove-use key (fn-rtc-uses s))))
           (fn-rtc-uses-okp uses (fn-rtc-with-uses (fn-rtc-remove-use key (fn-rtc-uses s)) s)))
  :hints (("Goal" :induct (fn-rtc-uses-okp uses s)
           :in-theory (disable fn-rtc-use-okp fn-rtc-remove-use fn-rtc-key
                               fn-rtc-kind-out-p fn-rtc-op-used-p fn-rtc-get))))

(defthm fn-rtc-subset-cons
  (implies (subsetp-equal xs ys) (subsetp-equal xs (cons y ys))))

(defthm fn-rtc-subset-reflexive
  (subsetp-equal xs xs))

(defthm fn-rtc-uses-okp-after-removal
  (implies (fn-rtc-uses-okp (fn-rtc-uses s) s)
           (fn-rtc-uses-okp (fn-rtc-remove-use key (fn-rtc-uses s))
             (fn-rtc-with-uses (fn-rtc-remove-use key (fn-rtc-uses s)) s)))
  :hints (("Goal" :in-theory (disable fn-rtc-uses-okp fn-rtc-remove-use subsetp-equal))))

(defthm fn-rtc-holds-iff-positive-holders
  (iff (fn-rtc-holds-p h g uses) (< 0 (fn-rtc-holders h g uses)))
  :hints (("Goal" :induct (fn-rtc-holds-p h g uses)
           :in-theory (disable fn-rtc-handlep fn-rtc-u-hd fn-rtc-h-buf fn-rtc-h-gen))))

(defthm fn-rtc-use-okp-of-unheld-update
  (implies (and (natp h) (fn-rtc-use-okp u s) (member-equal u (fn-rtc-uses s))
                (equal (fn-rtc-holders h (fn-rtc-b-gen (fn-rtc-buffer h s)) (fn-rtc-uses s)) 0))
           (fn-rtc-use-okp u (fn-rtc-with-buffer h b s)))
  :hints (("Goal" :in-theory
           (union-theories (theory 'minimal-theory)
            '(fn-rtc-use-okp fn-rtc-current-p fn-rtc-with-accessors fn-rtc-slot-of-with
              fn-rtc-buffer-of-with fn-rtc-next-op-of-with (:type-prescription fn-rtc-h-buf)
              nfix natp))
           :use ((:instance fn-rtc-member-holder-positive (uses (fn-rtc-uses s)))))))

(defthm fn-rtc-uses-okp-of-unheld-update-subset
  (implies (and (natp h) (fn-rtc-uses-okp uses s) (subsetp-equal uses (fn-rtc-uses s))
                (equal (fn-rtc-holders h (fn-rtc-b-gen (fn-rtc-buffer h s)) (fn-rtc-uses s)) 0))
           (fn-rtc-uses-okp uses (fn-rtc-with-buffer h b s)))
  :hints (("Goal" :induct (fn-rtc-uses-okp uses s)
           :in-theory (disable fn-rtc-use-okp fn-rtc-holders fn-rtc-kind-out-p
                               fn-rtc-op-used-p fn-rtc-get fn-rtc-b-gen))))

(defthm fn-rtc-uses-okp-of-unheld-update
  (implies (and (natp h) (fn-rtc-uses-okp (fn-rtc-uses s) s)
                (equal (fn-rtc-holders h (fn-rtc-b-gen (fn-rtc-buffer h s)) (fn-rtc-uses s)) 0))
           (fn-rtc-uses-okp (fn-rtc-uses s) (fn-rtc-with-buffer h b s)))
  :hints (("Goal" :in-theory (disable fn-rtc-uses-okp fn-rtc-holders fn-rtc-b-gen subsetp-equal))))

(defthm fn-rtc-holds-remove-other
  (implies (or (not (fn-rtc-handlep (fn-rtc-u-hd (fn-rtc-find-use key uses))))
               (not (equal h (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use key uses)))))
               (not (equal g (fn-rtc-h-gen (fn-rtc-u-hd (fn-rtc-find-use key uses))))))
           (equal (fn-rtc-holds-p h g (fn-rtc-remove-use key uses))
                  (fn-rtc-holds-p h g uses)))
  :hints (("Goal" :induct (fn-rtc-remove-use key uses)
           :in-theory (disable fn-rtc-key fn-rtc-handlep fn-rtc-u-hd fn-rtc-h-buf fn-rtc-h-gen
                               fn-rtc-holds-iff-positive-holders))))

(defthm fn-rtc-buffer-okp-after-removal-other
  (implies (and (fn-rtc-buffer-okp h b s)
                (or (not (fn-rtc-handlep (fn-rtc-u-hd (fn-rtc-find-use key (fn-rtc-uses s)))))
                    (not (equal h (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use key (fn-rtc-uses s))))))
                    (fn-rtc-holds-p (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use key (fn-rtc-uses s))))
                                    (fn-rtc-h-gen (fn-rtc-u-hd (fn-rtc-find-use key (fn-rtc-uses s))))
                                    (fn-rtc-remove-use key (fn-rtc-uses s)))))
           (fn-rtc-buffer-okp h b (fn-rtc-with-uses (fn-rtc-remove-use key (fn-rtc-uses s)) s)))
  :hints (("Goal" :in-theory
           (e/d (fn-rtc-buffer-okp)
                (fn-rtc-bufferp fn-rtc-handlep fn-rtc-u-hd fn-rtc-h-buf fn-rtc-h-gen
                 fn-rtc-holds-p fn-rtc-holds-iff-positive-holders fn-rtc-remove-use fn-rtc-find-use
                 fn-rtc-b-owner fn-rtc-b-gen fn-rtc-s-inc fn-rtc-s-status fn-rtc-get
                 fn-rtc-cap fn-rtc-nslots))
           :cases ((equal (fn-rtc-b-gen b)
                          (fn-rtc-h-gen (fn-rtc-u-hd (fn-rtc-find-use key (fn-rtc-uses s)))))))))

(defun fn-rtc-pool-induct (i pool)
  (declare (xargs :guard (natp i) :measure (len pool)))
  (if (consp pool) (fn-rtc-pool-induct (+ 1 i) (cdr pool)) i))

(defthm fn-rtc-pool-okp-after-covered-removal
  (implies (and (fn-rtc-pool-okp i pool s)
                (or (not (fn-rtc-handlep (fn-rtc-u-hd (fn-rtc-find-use key (fn-rtc-uses s)))))
                    (fn-rtc-holds-p (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use key (fn-rtc-uses s))))
                                    (fn-rtc-h-gen (fn-rtc-u-hd (fn-rtc-find-use key (fn-rtc-uses s))))
                                    (fn-rtc-remove-use key (fn-rtc-uses s)))))
           (fn-rtc-pool-okp i pool (fn-rtc-with-uses (fn-rtc-remove-use key (fn-rtc-uses s)) s)))
  :hints (("Goal" :induct (fn-rtc-pool-induct i pool)
           :in-theory (union-theories (theory 'minimal-theory)
                        '(fn-rtc-pool-okp-unfolds (:induction fn-rtc-pool-induct)
                          fn-rtc-buffer-okp-after-removal-other)))))

(defthm fn-rtc-pool-okp-after-removal-later
  (implies (and (natp i) (fn-rtc-pool-okp i pool s)
                (< (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use key (fn-rtc-uses s)))) i))
           (fn-rtc-pool-okp i pool (fn-rtc-with-uses (fn-rtc-remove-use key (fn-rtc-uses s)) s)))
  :hints (("Goal" :induct (fn-rtc-pool-induct i pool)
           :in-theory (e/d ((:induction fn-rtc-pool-induct))
                           (fn-rtc-h-buf fn-rtc-u-hd fn-rtc-find-use fn-rtc-remove-use
                            fn-rtc-holds-p fn-rtc-handlep fn-rtc-holds-iff-positive-holders)))))

(defthm fn-rtc-pool-okp-replace-after-removal
  (implies (and (natp i) (natp k) (fn-rtc-pool-okp i pool s)
                (equal (+ i k) (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use key (fn-rtc-uses s)))))
                (fn-rtc-buffer-okp (+ i k) b
                  (fn-rtc-with-uses (fn-rtc-remove-use key (fn-rtc-uses s)) s)))
           (fn-rtc-pool-okp i (fn-rtc-set k b pool)
             (fn-rtc-with-uses (fn-rtc-remove-use key (fn-rtc-uses s)) s)))
  :hints (("Goal" :induct (fn-rtc-index-induct k i pool)
           :in-theory (disable fn-rtc-h-buf fn-rtc-u-hd fn-rtc-find-use fn-rtc-remove-use
                               fn-rtc-holds-p fn-rtc-handlep fn-rtc-holds-iff-positive-holders)
           :expand ((:with fn-rtc-pool-okp-unfolds (fn-rtc-pool-okp i pool s))
                    (:with fn-rtc-pool-okp-unfolds
                     (fn-rtc-pool-okp i (cons b (cdr pool))
                       (fn-rtc-with-uses (fn-rtc-remove-use key (fn-rtc-uses s)) s)))))))

(defthm fn-rtc-octets-n-properties
  (implies (fn-rtc-octets-n-p data n)
           (and (fn-cbor-octet-listp data) (equal (len data) (nfix n))))
  :hints (("Goal" :induct (fn-rtc-octets-n-p data n))))

(defthm fn-rtc-delivered-in-data
  (implies (and (member-eq (fn-rtc-get 0 u) *fn-rtc-in-kinds*)
                (member-eq (fn-rtc-get 0 (fn-rtc-delivered-outcome u e)) '(:done :short)))
           (and (fn-cbor-octet-listp (fn-rtc-e-data e))
                (<= (len (fn-rtc-e-data e)) (fn-rtc-h-len (fn-rtc-u-hd u)))))
  :hints (("Goal" :in-theory (disable fn-rtc-octets-n-p fn-cbor-octet-listp fn-rtc-h-len fn-rtc-u-hd)
           :use ((:instance fn-rtc-octets-n-properties
                  (data (fn-rtc-e-data e)) (n (fn-rtc-get 1 (fn-rtc-e-outcome e))))))))

(defthm fn-rtc-lease-return-of-with-uses
  (equal (fn-rtc-lease-return u e b (fn-rtc-with-uses uses s))
         (fn-rtc-lease-return u e b s))
  :hints (("Goal" :in-theory
           (union-theories (theory 'minimal-theory)
            '(fn-rtc-lease-return fn-rtc-current-p fn-rtc-handed-to-live-p
              fn-rtc-live-p fn-rtc-slot-of-with)))))

(defthm fn-rtc-core-invp-found-use
  (implies (and (fn-rtc-core-invp s) (fn-rtc-find-use key (fn-rtc-uses s)))
           (fn-rtc-use-okp (fn-rtc-find-use key (fn-rtc-uses s)) s))
  :hints (("Goal" :use (fn-rtc-core-invp-uses
                        (:instance fn-rtc-find-use-is-member (k key) (uses (fn-rtc-uses s)))
                        (:instance fn-rtc-uses-okp-member (uses (fn-rtc-uses s))
                         (u (fn-rtc-find-use key (fn-rtc-uses s)))))
           :in-theory (theory 'minimal-theory))))
