; fn: the runtime contract's invariant: T1 (initialization establishes
; `fn-rtc-invp') and T2 (every step preserves it, for every event and
; quantum), from the per-operation preservation lemmas of
; books/runtime-contract-invariant-ops.lisp and the end-of-use, accept and
; close branches below.

(in-package "ACL2")
(include-book "runtime-contract-invariant-ops")

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

; Ending a use: the returned lease, the end-lease state.

(local (defthm fn-rtc-use-okp-in-local-range
  (implies (and (fn-rtc-use-okp u s) (fn-rtc-handlep (fn-rtc-u-hd u))
                (member-eq (fn-rtc-get 0 u) *fn-rtc-in-kinds*))
           (and (<= (fn-rtc-h-off (fn-rtc-u-hd u))
                    (len (fn-rtc-b-bytes (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd u)) s))))
                (<= (+ (fn-rtc-h-off (fn-rtc-u-hd u)) (fn-rtc-h-len (fn-rtc-u-hd u)))
                    (fn-rtc-buf-cap (fn-rtc-h-buf (fn-rtc-u-hd u)) (fn-rtc-config s)))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-rtc-use-okp (:executable-counterpart member-equal)))))
  :rule-classes nil))

(defthm fn-rtc-use-okp-in-range
  (implies (and (fn-rtc-use-okp u s) (fn-rtc-handlep (fn-rtc-u-hd u))
                (member-eq (fn-rtc-get 0 u) *fn-rtc-in-kinds*))
           (and (<= (fn-rtc-h-off (fn-rtc-u-hd u))
                    (len (fn-rtc-b-bytes (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd u)) s))))
                (<= (+ (fn-rtc-h-off (fn-rtc-u-hd u)) (fn-rtc-h-len (fn-rtc-u-hd u)))
                    (fn-rtc-cap (fn-rtc-config s)))))
  :hints (("Goal" :use (fn-rtc-use-okp-in-local-range
                         (:instance fn-rtc-buf-cap-at-most-cap (h (fn-rtc-h-buf (fn-rtc-u-hd u))) (cfg (fn-rtc-config s))))
           :in-theory (union-theories (theory 'minimal-theory) '(fn-rtc-use-okp (:executable-counterpart member-equal)))))
  :rule-classes nil)
(local (defthm fn-rtc-lease-return-local-bytes-okp
  (implies (and (fn-rtc-buffer-okp (fn-rtc-h-buf (fn-rtc-u-hd u))
                                  (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd u)) s) s)
                (fn-rtc-use-okp u s) (fn-rtc-handlep (fn-rtc-u-hd u)))
           (let ((bytes (fn-rtc-get 2 (fn-rtc-lease-return
                                       u e (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd u)) s) s))))
             (and (fn-cbor-octet-listp bytes)
                  (<= (len bytes) (fn-rtc-buf-cap (fn-rtc-h-buf (fn-rtc-u-hd u)) (fn-rtc-config s))))))
  :hints (("Goal" :in-theory
           (e/d (fn-rtc-lease-return)
                (fn-rtc-buffer-okp fn-rtc-handlep fn-rtc-usep fn-rtc-holders fn-rtc-holds-p
                 fn-rtc-splice fn-cbor-octet-listp fn-rtc-delivered-outcome
                 fn-rtc-u-hd fn-rtc-h-buf fn-rtc-h-gen fn-rtc-h-off fn-rtc-h-len
                 fn-rtc-s-inc fn-rtc-s-status fn-rtc-nslots fn-rtc-cap fn-rtc-buf-cap fn-rtc-current-p
                 fn-rtc-invp-listener fn-rtc-core-invp-listener fn-rtc-invp-is-core-and-admission
                 fn-rtc-core-invp fn-rtc-uses-okp fn-rtc-pool-okp-unfolds fn-rtc-use-okp
                 fn-rtc-get-out-of-range fn-rtc-buffer-out-of-range))
           :use (fn-rtc-delivered-in-data fn-rtc-use-okp-in-local-range
                 fn-rtc-use-okp-lease
                 (:instance fn-rtc-buffer-okp-local-bytes (h (fn-rtc-h-buf (fn-rtc-u-hd u)))
                            (b (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd u)) s))))))))


(defthm fn-rtc-lease-return-bytes-okp
  (implies (and (fn-rtc-buffer-okp (fn-rtc-h-buf (fn-rtc-u-hd u))
                                  (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd u)) s) s)
                (fn-rtc-use-okp u s) (fn-rtc-handlep (fn-rtc-u-hd u)))
           (let ((bytes (fn-rtc-get 2 (fn-rtc-lease-return
                                       u e (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd u)) s) s))))
             (and (fn-cbor-octet-listp bytes)
                  (<= (len bytes) (fn-rtc-cap (fn-rtc-config s))))))
  :hints (("Goal" :in-theory
           (e/d (fn-rtc-lease-return)
                (fn-rtc-buffer-okp fn-rtc-handlep fn-rtc-usep fn-rtc-holders fn-rtc-holds-p
                 fn-rtc-splice fn-cbor-octet-listp fn-rtc-delivered-outcome
                 fn-rtc-u-hd fn-rtc-h-buf fn-rtc-h-gen fn-rtc-h-off fn-rtc-h-len
                 fn-rtc-s-inc fn-rtc-s-status fn-rtc-nslots fn-rtc-cap fn-rtc-current-p
                 fn-rtc-invp-listener fn-rtc-core-invp-listener fn-rtc-invp-is-core-and-admission
                 fn-rtc-core-invp fn-rtc-uses-okp fn-rtc-pool-okp-unfolds fn-rtc-use-okp
                 fn-rtc-get-out-of-range fn-rtc-buffer-out-of-range))
           :use (fn-rtc-delivered-in-data fn-rtc-use-okp-in-range
                 fn-rtc-use-okp-lease
                 (:instance fn-rtc-buffer-okp-bytes (h (fn-rtc-h-buf (fn-rtc-u-hd u)))
                            (b (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd u)) s)))))))

(defthm fn-rtc-lease-return-buffer-okp
  (implies (and (fn-rtc-buffer-okp (fn-rtc-h-buf (fn-rtc-u-hd u))
                                  (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd u)) s) s)
                (fn-rtc-use-okp u s) (fn-rtc-handlep (fn-rtc-u-hd u)))
           (fn-rtc-buffer-okp (fn-rtc-h-buf (fn-rtc-u-hd u))
             (fn-rtc-lease-return u e (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd u)) s) s)
             (fn-rtc-with-uses uses s)))
  :hints (("Goal" :in-theory
           (e/d (fn-rtc-buffer-okp fn-rtc-lease-return fn-rtc-leasedp)
                (fn-rtc-use-okp fn-rtc-use-okp-lease fn-rtc-lease-return-local-bytes-okp
                 fn-rtc-handlep fn-rtc-usep fn-rtc-holders fn-rtc-holds-p
                 fn-rtc-splice fn-cbor-octet-listp fn-rtc-delivered-outcome
                 fn-rtc-u-hd fn-rtc-h-buf fn-rtc-h-gen fn-rtc-h-off fn-rtc-h-len
                 fn-rtc-s-inc fn-rtc-s-status fn-rtc-nslots fn-rtc-cap fn-rtc-buf-cap
                 fn-rtc-invp-listener fn-rtc-core-invp-listener fn-rtc-invp-is-core-and-admission
                 fn-rtc-core-invp fn-rtc-uses-okp fn-rtc-pool-okp-unfolds
                 fn-rtc-get-out-of-range fn-rtc-buffer-out-of-range
                 fn-rtc-splice-length fn-rtc-splice-octets))
           :use (fn-rtc-use-okp-lease fn-rtc-lease-return-local-bytes-okp))))

(defthm fn-rtc-core-invp-pool
  (implies (fn-rtc-core-invp s) (fn-rtc-pool-okp 0 (fn-rtc-pool s) s))
  :hints (("Goal" :in-theory
           (disable fn-rtc-configp fn-rtc-slots-okp fn-rtc-pool-okp-unfolds
                    fn-rtc-uses-okp fn-rtc-mstates-okp fn-rtc-draining-okp))))

(defthm fn-rtc-uses-okp-end-lease-after-removal
  (implies (and (fn-rtc-core-invp s) (fn-rtc-find-use key (fn-rtc-uses s)))
           (let* ((u (fn-rtc-find-use key (fn-rtc-uses s)))
                  (s1 (fn-rtc-with-uses (fn-rtc-remove-use key (fn-rtc-uses s)) s))
                  (s2 (fn-rtc-end-lease u e s1)))
             (fn-rtc-uses-okp (fn-rtc-uses s2) s2)))
  :hints (("Goal" :in-theory
           (e/d (fn-rtc-end-lease)
                (fn-rtc-core-invp fn-rtc-use-okp fn-rtc-uses-okp fn-rtc-find-use
                 fn-rtc-remove-use fn-rtc-u-hd fn-rtc-handlep fn-rtc-holders
                 fn-rtc-h-buf fn-rtc-h-gen fn-rtc-b-gen fn-rtc-lease-return
                 fn-rtc-use-okp-lease))
           :use (fn-rtc-core-invp-uses fn-rtc-core-invp-found-use
                 (:instance fn-rtc-use-okp-lease (u (fn-rtc-find-use key (fn-rtc-uses s))))))))

(defthm fn-rtc-use-okp-buffer-index
  (implies (and (fn-rtc-use-okp u s) (fn-rtc-handlep (fn-rtc-u-hd u)))
           (< (fn-rtc-h-buf (fn-rtc-u-hd u)) (fn-rtc-nbufs (fn-rtc-config s))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-rtc-use-okp (:executable-counterpart member-equal))))))

(defthm fn-rtc-pool-okp-end-lease-after-removal
  (implies (and (fn-rtc-core-invp s) (fn-rtc-find-use key (fn-rtc-uses s)))
           (let* ((u (fn-rtc-find-use key (fn-rtc-uses s)))
                  (s1 (fn-rtc-with-uses (fn-rtc-remove-use key (fn-rtc-uses s)) s))
                  (s2 (fn-rtc-end-lease u e s1)))
             (fn-rtc-pool-okp 0 (fn-rtc-pool s2) s2)))
  :hints (("Goal" :in-theory
           (e/d (fn-rtc-end-lease)
                (fn-rtc-core-invp fn-rtc-use-okp fn-rtc-uses-okp fn-rtc-find-use
                 fn-rtc-remove-use fn-rtc-u-hd fn-rtc-handlep fn-rtc-holders fn-rtc-holds-p
                 fn-rtc-holds-iff-positive-holders fn-rtc-pool-okp-unfolds
                 fn-rtc-h-buf fn-rtc-h-gen fn-rtc-b-gen fn-rtc-lease-return))
           :use (fn-rtc-core-invp-pool fn-rtc-core-invp-found-use
                 (:instance fn-rtc-use-okp-buffer-index (u (fn-rtc-find-use key (fn-rtc-uses s))))
                 (:instance fn-rtc-core-invp-buffer
                  (h (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use key (fn-rtc-uses s))))))
                 (:instance fn-rtc-use-okp-lease (u (fn-rtc-find-use key (fn-rtc-uses s))))
                 (:instance fn-rtc-pool-okp-replace-after-removal
                  (i 0) (pool (fn-rtc-pool s))
                  (k (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use key (fn-rtc-uses s)))))
                  (b (fn-rtc-lease-return (fn-rtc-find-use key (fn-rtc-uses s)) e
                       (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use key (fn-rtc-uses s)))) s) s)))))))

(defthm fn-rtc-static-slots-length
  (equal (len (fn-rtc-static-slots n)) (nfix n)))

(defthm fn-rtc-static-mstates-length
  (equal (len (fn-rtc-static-mstates j n)) (nfix n)))

(defthm fn-rtc-mstates-okp-append
  (equal (fn-rtc-mstates-okp (append a b))
         (and (fn-rtc-mstates-okp a) (fn-rtc-mstates-okp b))))

(defthm fn-rtc-static-mstates-okp
  (fn-rtc-mstates-okp (fn-rtc-static-mstates j n)))

(defthm fn-rtc-static-slots-okp
  (implies (and (posp i) (fn-rtc-slots-okp (+ i (nfix n)) tail))
           (fn-rtc-slots-okp i (append (fn-rtc-static-slots n) tail)))
  :hints (("Goal" :induct (fn-rtc-init-induct n i))))

(defthm fn-rtc-static-slots-draining-okp
  (implies (natp i)
           (equal (fn-rtc-draining-okp i (append (fn-rtc-static-slots n) tail) uses)
                  (fn-rtc-draining-okp (+ i (nfix n)) tail uses)))
  :hints (("Goal" :induct (fn-rtc-init-induct n i))))

(defthm fn-rtc-static-slots-first-free
  (implies (natp i)
           (equal (fn-rtc-free-slot i (append (fn-rtc-static-slots n) tail))
                  (fn-rtc-free-slot (+ i (nfix n)) tail)))
  :hints (("Goal" :induct (fn-rtc-init-induct n i))))

(local (defun fn-rtc-static-index-induct (j n)
  (declare (xargs :guard (and (natp j) (natp n))))
  (if (or (zp j) (zp n)) nil (fn-rtc-static-index-induct (- j 1) (- n 1)))))

(defthm fn-rtc-static-slots-get
  (implies (and (natp j) (< j (nfix n)))
           (equal (fn-rtc-get j (append (fn-rtc-static-slots n) tail))
                  *fn-rtc-static-slot*))
  :hints (("Goal" :induct (fn-rtc-static-index-induct j n))))

(defthm fn-rtc-initial-statics-okp
  (implies (and (posp j) (natp n) (natp count) (<= (+ j n) (+ 1 count)))
           (fn-rtc-statics-okp j n (cons head (append (fn-rtc-static-slots count) tail))))
  :hints (("Goal" :induct (fn-rtc-statics-okp j n (cons head (append (fn-rtc-static-slots count) tail)))
           :in-theory (disable fn-rtc-static-slots))))

(defthm fn-rtc-static-mstates-true-listp
  (true-listp (fn-rtc-static-mstates j n)))

(defthm fn-rtc-true-listp-append
  (equal (true-listp (append a b)) (true-listp b)))

; T1.
(defthm fn-rtc-init-establishes-invp
  (implies (fn-rtc-configp cfg)
           (fn-rtc-invp (mv-nth 0 (fn-rtc-init cfg))))
  :hints (("Goal" :in-theory
           (enable fn-rtc-rearm fn-rtc-issue fn-rtc-make fn-rtc-config
                   fn-rtc-slots fn-rtc-pool fn-rtc-uses fn-rtc-mstates
                   fn-rtc-next-op fn-rtc-slot))))

; Between removal and retirement, the last use of a draining slot is absent.
(defun fn-rtc-resource-invp (s)
  (declare (xargs :guard t))
  (let ((cfg (fn-rtc-config s)))
    (and (true-listp s) (equal (len s) 6) (natp (fn-rtc-get 5 s))
         (fn-rtc-configp cfg)
         (equal (len (fn-rtc-slots s)) (fn-rtc-nslots cfg))
         (fn-rtc-slots-okp 0 (fn-rtc-slots s))
         (fn-rtc-statics-okp 1 (fn-rtc-nstatic cfg) (fn-rtc-slots s))
         (equal (len (fn-rtc-pool s)) (fn-rtc-nbufs cfg))
         (fn-rtc-pool-okp 0 (fn-rtc-pool s) s)
         (fn-rtc-uses-okp (fn-rtc-uses s) s)
         (true-listp (fn-rtc-mstates s))
         (equal (len (fn-rtc-mstates s)) (fn-rtc-nslots cfg))
         (fn-rtc-mstates-okp (fn-rtc-mstates s)))))

(defthm fn-rtc-core-is-resource-and-draining
  (equal (fn-rtc-core-invp s)
         (and (fn-rtc-resource-invp s)
              (fn-rtc-draining-okp 0 (fn-rtc-slots s) (fn-rtc-uses s))))
  :hints (("Goal" :in-theory
           (disable fn-rtc-configp fn-rtc-slots-okp fn-rtc-pool-okp-unfolds
                    fn-rtc-uses-okp fn-rtc-mstates-okp fn-rtc-draining-okp)))
  :rule-classes nil)

(defthm fn-rtc-with-uses-record
  (and (true-listp (fn-rtc-with-uses uses s))
       (equal (len (fn-rtc-with-uses uses s)) 6)
       (equal (fn-rtc-get 5 (fn-rtc-with-uses uses s)) (fn-rtc-next-op s)))
  :hints (("Goal" :in-theory (enable fn-rtc-with-uses))))

(defthm fn-rtc-end-lease-shape
  (and (equal (fn-rtc-mstates (fn-rtc-end-lease u e s)) (fn-rtc-mstates s))
       (equal (fn-rtc-next-op (fn-rtc-end-lease u e s)) (fn-rtc-next-op s))
       (equal (len (fn-rtc-pool (fn-rtc-end-lease u e s))) (len (fn-rtc-pool s)))
       (implies (true-listp s) (true-listp (fn-rtc-end-lease u e s)))
       (implies (equal (len s) 6) (equal (len (fn-rtc-end-lease u e s)) 6))
       (implies (natp (fn-rtc-get 5 s)) (natp (fn-rtc-get 5 (fn-rtc-end-lease u e s)))))
  :hints (("Goal" :in-theory
           (e/d (fn-rtc-end-lease)
                (fn-rtc-lease-return fn-rtc-handlep fn-rtc-holds-p fn-rtc-u-hd
                 fn-rtc-h-buf fn-rtc-h-gen fn-rtc-get)))))

(defthm fn-rtc-resource-invp-end-lease-after-removal
  (implies (and (fn-rtc-core-invp s) (fn-rtc-find-use key (fn-rtc-uses s)))
           (fn-rtc-resource-invp
            (fn-rtc-end-lease (fn-rtc-find-use key (fn-rtc-uses s)) e
              (fn-rtc-with-uses (fn-rtc-remove-use key (fn-rtc-uses s)) s))))
  :hints (("Goal" :in-theory
           (disable fn-rtc-configp fn-rtc-slots-okp fn-rtc-pool-okp-unfolds
                    fn-rtc-uses-okp fn-rtc-mstates-okp fn-rtc-draining-okp
                    fn-rtc-find-use fn-rtc-remove-use fn-rtc-get)
           :use (fn-rtc-pool-okp-end-lease-after-removal
                 fn-rtc-uses-okp-end-lease-after-removal))))

(defthm fn-rtc-uses-of-slot-member
  (implies (member-equal u uses)
           (fn-rtc-uses-of-slot-p (fn-rtc-get 1 u) (fn-rtc-get 2 u) uses))
  :hints (("Goal" :induct (member-equal u uses) :in-theory (disable fn-rtc-get))))

(defthm fn-rtc-use-okp-of-unused-slot-update
  (implies (and (natp id) (fn-rtc-use-okp u s) (member-equal u (fn-rtc-uses s))
                (not (fn-rtc-uses-of-slot-p id (fn-rtc-s-inc (fn-rtc-slot id s)) (fn-rtc-uses s))))
           (fn-rtc-use-okp u (fn-rtc-with-slot id slot s)))
  :hints (("Goal" :in-theory
           (union-theories (theory 'minimal-theory)
            '(fn-rtc-use-okp fn-rtc-usep fn-rtc-current-p fn-rtc-with-accessors
              fn-rtc-slot-of-with fn-rtc-buffer-of-with fn-rtc-next-op-of-with nfix natp))
           :use ((:instance fn-rtc-uses-of-slot-member (uses (fn-rtc-uses s)))))))

(defthm fn-rtc-uses-okp-of-unused-slot-update-subset
  (implies (and (natp id) (fn-rtc-uses-okp uses s) (subsetp-equal uses (fn-rtc-uses s))
                (not (fn-rtc-uses-of-slot-p id (fn-rtc-s-inc (fn-rtc-slot id s)) (fn-rtc-uses s))))
           (fn-rtc-uses-okp uses (fn-rtc-with-slot id slot s)))
  :hints (("Goal" :induct (fn-rtc-uses-okp uses s)
           :in-theory (disable fn-rtc-use-okp fn-rtc-uses-of-slot-p fn-rtc-s-inc
                               fn-rtc-kind-out-p fn-rtc-op-used-p fn-rtc-get))))

(defthm fn-rtc-uses-okp-of-unused-slot-update
  (implies (and (natp id) (fn-rtc-uses-okp (fn-rtc-uses s) s)
                (not (fn-rtc-uses-of-slot-p id (fn-rtc-s-inc (fn-rtc-slot id s)) (fn-rtc-uses s))))
           (fn-rtc-uses-okp (fn-rtc-uses s) (fn-rtc-with-slot id slot s)))
  :hints (("Goal" :in-theory (disable fn-rtc-uses-okp fn-rtc-uses-of-slot-p fn-rtc-s-inc subsetp-equal))))

(defthm fn-rtc-pool-okp-of-retired-slot
  (implies (and (natp id) (equal (fn-rtc-s-status (fn-rtc-slot id s)) :draining)
                (fn-rtc-pool-okp i pool s))
           (fn-rtc-pool-okp i pool (fn-rtc-with-slot id (list inc :free nil) s)))
  :hints (("Goal" :induct (fn-rtc-pool-induct i pool)
           :in-theory
           (e/d (fn-rtc-buffer-okp)
                (fn-rtc-bufferp fn-rtc-holds-p fn-rtc-holds-iff-positive-holders
                 fn-rtc-s-inc fn-rtc-s-status fn-rtc-b-owner fn-rtc-b-gen)))))

(defthm fn-rtc-resource-invp-listener
  (implies (fn-rtc-resource-invp s) (equal (fn-rtc-slot 0 s) *fn-rtc-listener*))
  :hints (("Goal" :in-theory
           (e/d (fn-rtc-slot)
                (fn-rtc-uses-okp fn-rtc-pool-okp-unfolds fn-rtc-mstates-okp fn-rtc-slots-is-slot))
           :expand ((fn-rtc-slots-okp 0 (fn-rtc-slots s))))))

(defthm fn-rtc-free-slotp
  (implies (natp inc) (fn-rtc-slotp (list inc :free nil))))

(defthm fn-rtc-statics-okp-get
  (implies (and (fn-rtc-statics-okp j n slots) (natp j) (natp k)
                (<= j k) (< k (+ j (nfix n))))
           (equal (fn-rtc-get k slots) *fn-rtc-static-slot*))
  :hints (("Goal" :induct (fn-rtc-statics-okp j n slots) :in-theory (disable fn-rtc-get))))

(defthm fn-rtc-statics-okp-set-nonlive
  (implies (and (fn-rtc-statics-okp j n slots) (natp j) (natp n) (natp k) (<= j k)
                (not (equal (fn-rtc-s-status (fn-rtc-get k slots)) :live)))
           (fn-rtc-statics-okp j n (fn-rtc-set k x slots)))
  :hints (("Goal" :in-theory (disable fn-rtc-statics-okp fn-rtc-get fn-rtc-set fn-rtc-s-status)
           :use fn-rtc-statics-okp-get)))

(defthm fn-rtc-retire-preserves-resource-invp
  (implies (and (fn-rtc-resource-invp s) (natp id))
           (fn-rtc-resource-invp (fn-rtc-retire-drained id s)))
  :hints (("Goal" :cases ((equal id 0)) :in-theory
           (e/d (fn-rtc-retire-drained)
                (fn-rtc-configp fn-rtc-slots-okp fn-rtc-pool-okp-unfolds
                 fn-rtc-uses-okp fn-rtc-mstates-okp fn-rtc-uses-of-slot-p
                 fn-rtc-s-inc fn-rtc-s-status fn-rtc-get fn-rtc-slotp fn-rtc-nslots fn-rtc-nbufs
                 fn-rtc-resource-invp-listener))
           :use fn-rtc-resource-invp-listener)))

(defun fn-rtc-draining-okp-except (id i slots uses)
  (declare (xargs :guard (and (natp id) (natp i)) :measure (len slots)))
  (if (consp slots)
      (and (implies (and (not (equal id i))
                         (eq (fn-rtc-s-status (car slots)) :draining))
                    (fn-rtc-uses-of-slot-p i (fn-rtc-s-inc (car slots)) uses))
           (fn-rtc-draining-okp-except id (+ 1 i) (cdr slots) uses))
    t))

(defthm fn-rtc-uses-of-slot-remove-other
  (implies (not (equal id (fn-rtc-get 1 (fn-rtc-find-use key uses))))
           (equal (fn-rtc-uses-of-slot-p id inc (fn-rtc-remove-use key uses))
                  (fn-rtc-uses-of-slot-p id inc uses)))
  :hints (("Goal" :induct (fn-rtc-remove-use key uses)
           :in-theory (disable fn-rtc-key fn-rtc-get))))

(defthm fn-rtc-draining-okp-removal-except
  (implies (fn-rtc-draining-okp i slots uses)
           (fn-rtc-draining-okp-except (fn-rtc-get 1 (fn-rtc-find-use key uses)) i slots
                                       (fn-rtc-remove-use key uses)))
  :hints (("Goal" :induct (fn-rtc-pool-induct i slots)
           :in-theory (disable fn-rtc-find-use fn-rtc-remove-use fn-rtc-uses-of-slot-p
                               fn-rtc-get fn-rtc-s-inc fn-rtc-s-status))))

(defthm fn-rtc-draining-except-below
  (implies (and (fn-rtc-draining-okp-except id i slots uses) (natp i) (< id i))
           (fn-rtc-draining-okp i slots uses))
  :hints (("Goal" :induct (fn-rtc-pool-induct i slots)
           :in-theory (disable fn-rtc-uses-of-slot-p fn-rtc-s-inc fn-rtc-s-status))))

(defthm fn-rtc-draining-except-fill
  (implies (and (natp i) (natp k)
                (fn-rtc-draining-okp-except (+ i k) i slots uses)
                (implies (equal (fn-rtc-s-status (fn-rtc-get k slots)) :draining)
                         (fn-rtc-uses-of-slot-p (+ i k) (fn-rtc-s-inc (fn-rtc-get k slots)) uses)))
           (fn-rtc-draining-okp i slots uses))
  :hints (("Goal" :induct (fn-rtc-index-induct k i slots)
           :in-theory (disable fn-rtc-uses-of-slot-p fn-rtc-s-inc fn-rtc-s-status)
           :expand ((fn-rtc-draining-okp-except (+ i k) i slots uses)
                    (fn-rtc-draining-okp i slots uses)))))

(defthm fn-rtc-draining-except-replace
  (implies (and (natp i) (natp k)
                (fn-rtc-draining-okp-except (+ i k) i slots uses)
                (implies (equal (fn-rtc-s-status slot) :draining)
                         (fn-rtc-uses-of-slot-p (+ i k) (fn-rtc-s-inc slot) uses)))
           (fn-rtc-draining-okp i (fn-rtc-set k slot slots) uses))
  :hints (("Goal" :induct (fn-rtc-index-induct k i slots)
           :in-theory (disable fn-rtc-uses-of-slot-p fn-rtc-s-inc fn-rtc-s-status)
           :expand ((fn-rtc-draining-okp-except (+ i k) i slots uses)
                    (fn-rtc-draining-okp i (cons slot (cdr slots)) uses)))))

(defthm fn-rtc-retire-establishes-draining
  (implies (and (natp id) (fn-rtc-draining-okp-except id 0 (fn-rtc-slots s) (fn-rtc-uses s)))
           (fn-rtc-draining-okp 0 (fn-rtc-slots (fn-rtc-retire-drained id s)) (fn-rtc-uses s)))
  :hints (("Goal" :in-theory
           (e/d (fn-rtc-retire-drained)
                (fn-rtc-draining-okp fn-rtc-draining-okp-except fn-rtc-uses-of-slot-p
                 fn-rtc-s-inc fn-rtc-s-status))
           :use ((:instance fn-rtc-draining-except-fill
                  (i 0) (k id) (slots (fn-rtc-slots s)) (uses (fn-rtc-uses s)))))))

(defthm fn-rtc-oldest-wait-cons-other
  (implies (not (equal (fn-rtc-get 0 u) :wait))
           (equal (fn-rtc-oldest-wait (cons u uses))
                  (fn-rtc-oldest-wait uses)))
  :hints (("Goal" :expand ((fn-rtc-oldest-wait (cons u uses)))
           :in-theory (disable fn-rtc-oldest-wait fn-rtc-get))))

(defthm fn-rtc-rearm-establishes-admission
  (implies (and (fn-rtc-core-invp s)
                (implies (fn-rtc-kind-out-p :accept 0 0 (fn-rtc-uses s))
                         (fn-rtc-free-slot 0 (fn-rtc-slots s)))
                (implies (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses s))
                         (and (fn-rtc-free-pool-buf 0 (fn-rtc-pool s) (fn-rtc-config s))
                              (fn-rtc-oldest-wait (fn-rtc-uses s)))))
           (fn-rtc-invp (mv-nth 0 (fn-rtc-rearm s))))
  :hints (("Goal" :use (fn-rtc-core-invp-shape fn-rtc-core-invp-listener)
           :in-theory
           (e/d (fn-rtc-rearm)
                (fn-rtc-core-invp fn-rtc-kind-out-p fn-rtc-free-slot
                 fn-rtc-free-pool-buf fn-rtc-oldest-wait)))))

(defthm fn-rtc-matching-use-fields
  (implies (and (fn-rtc-completionp e) (fn-rtc-find-use (fn-rtc-key e) uses))
           (let ((u (fn-rtc-find-use (fn-rtc-key e) uses)))
             (and (equal (fn-rtc-get 0 u) (fn-rtc-e-kind e))
                  (equal (fn-rtc-get 1 u) (fn-rtc-e-id e))
                  (equal (fn-rtc-get 2 u) (fn-rtc-e-inc e))
                  (equal (fn-rtc-get 3 u) (fn-rtc-e-op e)))))
  :hints (("Goal" :use ((:instance fn-rtc-key-of-find-use (k (fn-rtc-key e))))
           :in-theory (disable fn-rtc-find-use fn-rtc-outcomep fn-rtc-key-of-find-use))))

(defthm fn-rtc-end-use-preserves-core-invp
  (implies (fn-rtc-core-invp s) (fn-rtc-core-invp (fn-rtc-end-use s e)))
  :hints (("Goal" :in-theory
           (e/d (fn-rtc-end-use)
                (fn-rtc-core-invp fn-rtc-resource-invp fn-rtc-find-use fn-rtc-remove-use
                 fn-rtc-key fn-rtc-completionp fn-rtc-e-id fn-rtc-e-inc fn-rtc-get
                 fn-rtc-draining-okp fn-rtc-draining-okp-except))
           :use (fn-rtc-core-is-resource-and-draining
                 (:instance fn-rtc-matching-use-fields (uses (fn-rtc-uses s)))
                 (:instance fn-rtc-draining-okp-removal-except
                  (i 0) (slots (fn-rtc-slots s)) (uses (fn-rtc-uses s)) (key (fn-rtc-key e)))
                 (:instance fn-rtc-retire-establishes-draining
                  (id (fn-rtc-e-id e))
                  (s (fn-rtc-end-lease (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)) e
                       (fn-rtc-with-uses (fn-rtc-remove-use (fn-rtc-key e) (fn-rtc-uses s)) s))))
                 (:instance fn-rtc-core-is-resource-and-draining
                  (s (fn-rtc-retire-drained (fn-rtc-e-id e)
                       (fn-rtc-end-lease (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)) e
                         (fn-rtc-with-uses (fn-rtc-remove-use (fn-rtc-key e) (fn-rtc-uses s)) s)))))))))

(defthm fn-rtc-end-use-config
  (equal (fn-rtc-config (fn-rtc-end-use s e)) (fn-rtc-config s))
  :hints (("Goal" :in-theory (enable fn-rtc-end-use))))

(defthm fn-rtc-acting-instance-active
  (implies (and (not (fn-rtc-hand-delivers-p s e)) (and (fn-rtc-core-invp s) (fn-rtc-acts-on-p s e)
                (not (member-eq (fn-rtc-e-kind e) '(:accept :grant)))))
           (fn-rtc-instance-active-p (fn-rtc-e-id e) (fn-rtc-e-inc e) s))
  :hints (("Goal" :in-theory
           (disable fn-rtc-core-invp fn-rtc-find-use fn-rtc-key fn-rtc-outcomep
                    fn-rtc-core-invp-found-use fn-rtc-matching-use-fields
                    fn-rtc-uses-okp-member
                    fn-rtc-get fn-rtc-e-id fn-rtc-e-inc fn-rtc-e-op fn-rtc-e-kind fn-rtc-completionp
                    fn-rtc-handlep fn-rtc-holders fn-rtc-b-owner fn-rtc-b-gen fn-rtc-b-bytes
                    fn-rtc-h-buf fn-rtc-h-gen fn-rtc-h-off fn-rtc-h-len
                    fn-rtc-s-inc fn-rtc-s-status fn-rtc-nslots fn-rtc-cap)
           :use ((:instance fn-rtc-core-invp-found-use (key (fn-rtc-key e)))
                 (:instance fn-rtc-matching-use-fields (uses (fn-rtc-uses s)))))))

(defthm fn-rtc-acting-instance-active-after-end-use
  (implies (and (not (fn-rtc-hand-delivers-p s e)) (and (fn-rtc-core-invp s) (fn-rtc-acts-on-p s e)
                (not (member-eq (fn-rtc-e-kind e) '(:accept :grant)))))
           (fn-rtc-instance-active-p (fn-rtc-e-id e) (fn-rtc-e-inc e) (fn-rtc-end-use s e)))
  :hints (("Goal" :in-theory
           (union-theories (theory 'minimal-theory)
             '(fn-rtc-instance-active-p fn-rtc-slot fn-rtc-end-use-config
               (:executable-counterpart member-equal)))
           :use (fn-rtc-acting-instance-active fn-rtc-slots-of-end-use-at-live-slot))))

(defthm fn-rtc-use-okp-of-free-slot-update
  (implies (and (natp id) (fn-rtc-use-okp u s)
                (equal (fn-rtc-s-status (fn-rtc-slot id s)) :free))
           (fn-rtc-use-okp u (fn-rtc-with-slot id slot s)))
  :hints (("Goal" :in-theory
           (union-theories (theory 'minimal-theory)
            '(fn-rtc-use-okp fn-rtc-current-p fn-rtc-with-accessors fn-rtc-slot-of-with
              fn-rtc-buffer-of-with fn-rtc-next-op-of-with nfix natp)))))

(defthm fn-rtc-uses-okp-of-free-slot-update
  (implies (and (natp id) (fn-rtc-uses-okp uses s)
                (equal (fn-rtc-s-status (fn-rtc-slot id s)) :free))
           (fn-rtc-uses-okp uses (fn-rtc-with-slot id slot s)))
  :hints (("Goal" :induct (fn-rtc-uses-okp uses s)
           :in-theory (union-theories (theory 'minimal-theory)
                        '(fn-rtc-uses-okp fn-rtc-use-okp-of-free-slot-update)))))

(defthm fn-rtc-pool-okp-of-free-slot-update
  (implies (and (natp id) (equal (fn-rtc-s-status (fn-rtc-slot id s)) :free)
                (fn-rtc-pool-okp i pool s))
           (fn-rtc-pool-okp i pool (fn-rtc-with-slot id slot s)))
  :hints (("Goal" :induct (fn-rtc-pool-induct i pool)
           :in-theory
           (e/d (fn-rtc-buffer-okp)
                (fn-rtc-bufferp fn-rtc-holds-p fn-rtc-holds-iff-positive-holders
                 fn-rtc-s-inc fn-rtc-s-status fn-rtc-b-owner fn-rtc-b-gen)))))

(defthm fn-rtc-core-invp-activate-slot
  (implies (and (fn-rtc-core-invp s) (posp id) (natp inc) (natp r) (< r (expt 2 64))
                (equal (fn-rtc-s-status (fn-rtc-slot id s)) :free))
           (fn-rtc-core-invp (fn-rtc-with-slot id (list inc :live r) s)))
  :hints (("Goal" :in-theory
           (disable fn-rtc-configp fn-rtc-slots-okp fn-rtc-pool-okp-unfolds fn-rtc-uses-okp
                    fn-rtc-mstates-okp fn-rtc-draining-okp fn-rtc-s-inc fn-rtc-s-status))))

(defthm fn-rtc-free-slot-result
  (implies (and (natp i) (fn-rtc-free-slot i slots))
           (let ((j (fn-rtc-free-slot i slots)))
             (and (posp j) (<= i j) (< j (+ i (len slots)))
                  (equal (fn-rtc-s-status (fn-rtc-get (- j i) slots)) :free))))
  :hints (("Goal" :induct (fn-rtc-free-slot i slots)
           :in-theory (disable fn-rtc-s-status)
           :expand ((:free (k) (fn-rtc-get k slots))))))

(defthm fn-rtc-active-of-activated-slot
  (implies (and (posp id) (natp inc) (< id (len (fn-rtc-slots s)))
                (< id (fn-rtc-nslots (fn-rtc-config s))))
           (fn-rtc-instance-active-p id inc (fn-rtc-with-slot id (list inc :live r) s)))
  :hints (("Goal" :in-theory (disable fn-rtc-s-inc fn-rtc-s-status fn-rtc-nslots))))

(defun fn-rtc-grant-admission-safe-p (s)
  (declare (xargs :guard t))
  (implies (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses s))
           (and (fn-rtc-free-pool-buf 0 (fn-rtc-pool s) (fn-rtc-config s))
                (fn-rtc-oldest-wait (fn-rtc-uses s)))))
(local (defthm fn-rtc-oldest-wait-cons-present
  (implies (fn-rtc-oldest-wait uses) (fn-rtc-oldest-wait (cons u uses)))
  :hints (("Goal" :expand ((fn-rtc-oldest-wait (cons u uses)))
           :in-theory (disable fn-rtc-oldest-wait fn-rtc-get)))))
(defthm fn-rtc-free-pool-buf-pool-index
  (implies (and (natp i) (fn-rtc-free-pool-buf i pool cfg))
           (fn-rtc-pool-buf-p (fn-rtc-free-pool-buf i pool cfg) cfg))
  :hints (("Goal" :induct (fn-rtc-free-pool-buf i pool cfg)
           :in-theory (disable fn-rtc-pool-buf-p fn-rtc-b-owner))))
(local (defthm fn-rtc-free-pool-buf-exists
  (implies (and (natp i) (natp k) (fn-rtc-pool-buf-p (+ i k) cfg)
                (equal (fn-rtc-b-owner (fn-rtc-get k pool)) '(:free)))
           (fn-rtc-free-pool-buf i pool cfg))
  :rule-classes nil
  :hints (("Goal" :induct (fn-rtc-index-induct k i pool)
           :in-theory (disable fn-rtc-pool-buf-p fn-rtc-b-owner)))))
(local (defthm fn-rtc-request-keeps-free-pool-buffer
  (implies (and (posp id) (natp h) (fn-rtc-pool-buf-p h (fn-rtc-config s))
                (equal (fn-rtc-b-owner (fn-rtc-buffer h s)) '(:free)))
           (equal (fn-rtc-buffer h (mv-nth 0 (fn-rtc-request r id inc s)))
                  (fn-rtc-buffer h s)))
  :hints (("Goal" :in-theory
           (e/d (fn-rtc-request)
                (fn-rtc-b-owner fn-rtc-b-gen fn-rtc-b-bytes fn-rtc-h-buf fn-rtc-h-gen
                 fn-rtc-h-off fn-rtc-h-len fn-rtc-splice fn-rtc-buf-cap fn-rtc-cap
                 fn-rtc-kind-out-p fn-rtc-hand-target-okp fn-rtc-live-p fn-rtc-extrap
                 fn-rtc-nslots fn-rtc-nstatic fn-rtc-nbufs fn-rtc-s-inc fn-rtc-s-status
                 fn-rtc-use-bound fn-cbor-octet-listp))))))
(local (defthm fn-rtc-request-keeps-free-pool
  (implies (and (posp id) (fn-rtc-free-pool-buf 0 (fn-rtc-pool s) (fn-rtc-config s)))
           (fn-rtc-free-pool-buf 0 (fn-rtc-pool (mv-nth 0 (fn-rtc-request r id inc s)))
                                  (fn-rtc-config s)))
  :hints (("Goal" :in-theory
           (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
             '(fn-rtc-buffer natp nfix unicity-of-0 fix commutativity-of-+ fn-rtc-free-pool-buf-type
               (:executable-counterpart natp) (:executable-counterpart unary--)))
           :use ((:instance fn-rtc-request-keeps-free-pool-buffer
                   (h (fn-rtc-free-pool-buf 0 (fn-rtc-pool s) (fn-rtc-config s))))
                 (:instance fn-rtc-free-pool-buf-is-free (i 0) (pool (fn-rtc-pool s)) (cfg (fn-rtc-config s)))
                 (:instance fn-rtc-free-pool-buf-pool-index (i 0) (pool (fn-rtc-pool s)) (cfg (fn-rtc-config s)))
                 (:instance fn-rtc-free-pool-buf-exists (i 0)
                   (k (fn-rtc-free-pool-buf 0 (fn-rtc-pool s) (fn-rtc-config s)))
                   (pool (fn-rtc-pool (mv-nth 0 (fn-rtc-request r id inc s)))) (cfg (fn-rtc-config s))))))))
(local (defthm fn-rtc-request-keeps-wait
  (implies (fn-rtc-oldest-wait (fn-rtc-uses s))
           (fn-rtc-oldest-wait (fn-rtc-uses (mv-nth 0 (fn-rtc-request r id inc s)))))
  :hints (("Goal" :in-theory
           (e/d (fn-rtc-request)
                (fn-rtc-home fn-rtc-hand-target-okp fn-rtc-current-p fn-rtc-live-p fn-rtc-pool-buf-p fn-rtc-use-bound
                 fn-rtc-oldest-wait fn-rtc-kind-out-p fn-rtc-submit-okp fn-rtc-extrap
                 fn-rtc-splice fn-rtc-buf-cap fn-rtc-b-owner fn-rtc-b-gen fn-rtc-b-bytes
                 fn-rtc-s-inc fn-rtc-s-status fn-rtc-s-res fn-rtc-nslots fn-rtc-nbufs
                 fn-rtc-cap fn-cbor-octet-listp))))))
(local (defthm fn-rtc-request-keeps-grant
  (equal (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses (mv-nth 0 (fn-rtc-request r id inc s))))
         (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses s)))
  :hints (("Goal" :in-theory
           (e/d (fn-rtc-request)
                (fn-rtc-home fn-rtc-hand-target-okp fn-rtc-current-p fn-rtc-live-p fn-rtc-pool-buf-p fn-rtc-use-bound
                 fn-rtc-kind-out-p fn-rtc-submit-okp fn-rtc-extrap fn-rtc-splice fn-rtc-buf-cap
                 fn-rtc-b-owner fn-rtc-b-gen fn-rtc-b-bytes fn-rtc-s-inc fn-rtc-s-status
                 fn-rtc-s-res fn-rtc-nslots fn-rtc-nbufs fn-rtc-cap fn-cbor-octet-listp))))))
(defthm fn-rtc-request-config-frame
  (equal (fn-rtc-config (mv-nth 0 (fn-rtc-request r id inc s))) (fn-rtc-config s))
  :hints (("Goal" :in-theory
    (e/d (fn-rtc-request)
      (fn-rtc-home fn-rtc-hand-target-okp fn-rtc-current-p fn-rtc-live-p fn-rtc-pool-buf-p fn-rtc-use-bound
       fn-rtc-kind-out-p fn-rtc-submit-okp fn-rtc-extrap fn-rtc-splice fn-rtc-buf-cap
       fn-rtc-b-owner fn-rtc-b-gen fn-rtc-b-bytes fn-rtc-s-inc fn-rtc-s-status
       fn-rtc-s-res fn-rtc-nslots fn-rtc-nbufs fn-rtc-cap fn-cbor-octet-listp)))))
(local (defthm fn-rtc-request-preserves-grant-admission
  (implies (and (posp id) (fn-rtc-grant-admission-safe-p s))
           (fn-rtc-grant-admission-safe-p (mv-nth 0 (fn-rtc-request r id inc s))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-grant-admission-safe-p)
    (mv-nth fn-rtc-request fn-rtc-kind-out-p fn-rtc-free-pool-buf fn-rtc-oldest-wait))))))
(local (defthm fn-rtc-requests-preserve-grant-admission
  (implies (and (posp id) (fn-rtc-grant-admission-safe-p s))
           (fn-rtc-grant-admission-safe-p (mv-nth 0 (fn-rtc-requests reqs id inc s))))
  :hints (("Goal" :induct (fn-rtc-requests reqs id inc s)
           :in-theory (e/d (fn-rtc-requests)
              (mv-nth fn-rtc-request fn-rtc-grant-admission-safe-p))))))
(local (defthm fn-rtc-grant-admission-of-with-mstate
  (equal (fn-rtc-grant-admission-safe-p (fn-rtc-with-mstate j m s))
         (fn-rtc-grant-admission-safe-p s))
  :hints (("Goal" :in-theory (e/d (fn-rtc-grant-admission-safe-p)
              (fn-rtc-kind-out-p fn-rtc-free-pool-buf fn-rtc-oldest-wait))))))
(local (defthm fn-rtc-grant-admission-of-with-slot
  (equal (fn-rtc-grant-admission-safe-p (fn-rtc-with-slot j slot s))
         (fn-rtc-grant-admission-safe-p s))
  :hints (("Goal" :in-theory (e/d (fn-rtc-grant-admission-safe-p)
              (fn-rtc-kind-out-p fn-rtc-free-pool-buf fn-rtc-oldest-wait))))))
(local (defthm fn-rtc-deliver-preserves-grant-admission
  (implies (and (posp id) (fn-rtc-grant-admission-safe-p s))
           (fn-rtc-grant-admission-safe-p (mv-nth 0 (fn-rtc-deliver s id inc ev q))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-deliver)
             (mv-nth fn-rtc-requests fn-rtc-grant-admission-safe-p fn-rtc-mstate fn-rtc-view))))))

(local (defthm fn-rtc-rearm-invp-when-admission-safe
  (implies (and (fn-rtc-core-invp s) (fn-rtc-grant-admission-safe-p s)
                (implies (fn-rtc-kind-out-p :accept 0 0 (fn-rtc-uses s))
                         (fn-rtc-free-slot 0 (fn-rtc-slots s))))
           (fn-rtc-invp (mv-nth 0 (fn-rtc-rearm s))))
  :hints (("Goal" :use fn-rtc-rearm-establishes-admission
           :in-theory (union-theories (theory 'minimal-theory) '(fn-rtc-grant-admission-safe-p))))))

(defthm fn-rtc-accept-branch-establishes-invp
  (implies (and (fn-rtc-core-invp s1) (fn-rtc-grant-admission-safe-p s1)
                (not (fn-rtc-kind-out-p :accept 0 0 (fn-rtc-uses s1))))
           (fn-rtc-invp (mv-nth 0 (fn-rtc-accept-branch s1 out q))))
  :hints (("Goal" :in-theory
           (e/d (fn-rtc-accept-branch)
                (fn-rtc-grant-admission-safe-p mv-nth fn-rtc-core-invp fn-rtc-resource-invp fn-rtc-invp
                 fn-rtc-invp-is-core-and-admission
                 fn-rtc-free-slot fn-rtc-kind-out-p fn-rtc-deliver fn-rtc-rearm
                 fn-rtc-instance-active-p fn-rtc-s-inc fn-rtc-s-status fn-rtc-nslots
                 fn-rtc-configp fn-rtc-core-invp-shape fn-rtc-free-slot-result))
           :use ((:instance fn-rtc-core-invp-shape (s s1))
                 (:instance fn-rtc-free-slot-result (i 0) (slots (fn-rtc-slots s1)))))))

; The close branch before rearming, factored only for its preservation proof.
(defun fn-rtc-close-state (s id inc)
  (declare (xargs :guard t))
  (let* ((s2 (fn-rtc-make (fn-rtc-config s) (fn-rtc-slots s)
                          (fn-rtc-release-all (fn-rtc-pool s) id inc)
                          (fn-rtc-uses s) (fn-rtc-mstates s) (fn-rtc-next-op s)))
         (status (if (fn-rtc-uses-of-slot-p id inc (fn-rtc-uses s2)) :draining :free)))
    (fn-rtc-with-mstate id (fn-rtc-m-init)
      (fn-rtc-with-slot id (list inc status (if (eq status :free) nil
                                               (fn-rtc-s-res (fn-rtc-slot id s2)))) s2))))

(defthm fn-rtc-close-state-accessors
  (and (equal (fn-rtc-config (fn-rtc-close-state s id inc)) (fn-rtc-config s))
       (equal (fn-rtc-uses (fn-rtc-close-state s id inc)) (fn-rtc-uses s))
       (equal (fn-rtc-next-op (fn-rtc-close-state s id inc)) (fn-rtc-next-op s))
       (equal (fn-rtc-pool (fn-rtc-close-state s id inc)) (fn-rtc-release-all (fn-rtc-pool s) id inc))
       (equal (fn-rtc-mstates (fn-rtc-close-state s id inc))
              (fn-rtc-set id (fn-rtc-m-init) (fn-rtc-mstates s)))
       (equal (fn-rtc-slots (fn-rtc-close-state s id inc))
              (fn-rtc-set id (list inc
                               (if (fn-rtc-uses-of-slot-p id inc (fn-rtc-uses s)) :draining :free)
                               (if (fn-rtc-uses-of-slot-p id inc (fn-rtc-uses s))
                                   (fn-rtc-s-res (fn-rtc-slot id s)) nil))
                          (fn-rtc-slots s)))
       (true-listp (fn-rtc-close-state s id inc))
       (equal (len (fn-rtc-close-state s id inc)) 6)
       (equal (fn-rtc-get 5 (fn-rtc-close-state s id inc)) (fn-rtc-next-op s)))
  :hints (("Goal" :in-theory (disable fn-rtc-uses-of-slot-p fn-rtc-release-all fn-rtc-s-res))))

(defthm fn-rtc-close-state-slot
  (equal (fn-rtc-slot j (fn-rtc-close-state s id inc))
         (if (and (equal (nfix j) (nfix id)) (< (nfix id) (len (fn-rtc-slots s))))
             (list inc (if (fn-rtc-uses-of-slot-p id inc (fn-rtc-uses s)) :draining :free)
                   (if (fn-rtc-uses-of-slot-p id inc (fn-rtc-uses s))
                       (fn-rtc-s-res (fn-rtc-slot id s)) nil))
           (fn-rtc-slot j s)))
  :hints (("Goal" :in-theory
           (union-theories (theory 'minimal-theory)
            '(fn-rtc-close-state fn-rtc-make-accessors fn-rtc-buffer-of-make
              fn-rtc-with-accessors fn-rtc-slot-of-with fn-rtc-slots-is-slot
              car-cons cdr-cons)))))

(defthm fn-rtc-close-state-keeps-used-buffer
  (implies (and (fn-rtc-core-invp s) (fn-rtc-use-okp u s) (fn-rtc-handlep (fn-rtc-u-hd u)))
           (equal (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd u)) (fn-rtc-close-state s id inc))
                  (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd u)) s)))
  :hints (("Goal" :in-theory
           (disable fn-rtc-core-invp fn-rtc-use-okp fn-rtc-handlep fn-rtc-u-hd fn-rtc-h-buf
                    fn-rtc-uses-of-slot-p fn-rtc-release-all fn-rtc-s-res fn-rtc-b-owner
                    fn-rtc-use-okp-lease fn-rtc-use-okp-buffer-index)
           :use (fn-rtc-core-invp-shape fn-rtc-use-okp-lease fn-rtc-use-okp-buffer-index))))

(in-theory (disable fn-rtc-close-state))

(defthm fn-rtc-kind-out-of-member
  (implies (member-equal u uses)
           (fn-rtc-kind-out-p (fn-rtc-get 0 u) (fn-rtc-get 1 u) (fn-rtc-get 2 u) uses))
  :hints (("Goal" :induct (member-equal u uses) :in-theory (disable fn-rtc-get))))

(defthm fn-rtc-use-okp-close-state
  (implies (and (fn-rtc-core-invp s) (fn-rtc-use-okp u s) (member-equal u (fn-rtc-uses s))
                (natp id) (equal (fn-rtc-s-inc (fn-rtc-slot id s)) inc)
                (not (fn-rtc-kind-out-p :close id inc (fn-rtc-uses s))))
           (fn-rtc-use-okp u (fn-rtc-close-state s id inc)))
  :hints (("Goal" :in-theory
           (disable fn-rtc-core-invp fn-rtc-handlep fn-rtc-holders
                    fn-rtc-uses-of-slot-p fn-rtc-kind-out-p fn-rtc-get fn-rtc-u-hd
                    fn-rtc-b-owner fn-rtc-b-gen fn-rtc-b-bytes fn-rtc-h-buf fn-rtc-h-gen
                    fn-rtc-h-off fn-rtc-h-len fn-rtc-s-inc fn-rtc-s-status fn-rtc-s-res
                    fn-rtc-nslots fn-rtc-nbufs fn-rtc-cap fn-rtc-uses-okp-member
                    fn-rtc-uses-of-slot-member fn-rtc-kind-out-of-member)
           :use ((:instance fn-rtc-uses-of-slot-member (uses (fn-rtc-uses s)))
                 (:instance fn-rtc-kind-out-of-member (uses (fn-rtc-uses s)))))))

(defthm fn-rtc-uses-okp-close-state-subset
  (implies (and (fn-rtc-core-invp s) (fn-rtc-uses-okp uses s) (subsetp-equal uses (fn-rtc-uses s))
                (natp id) (equal (fn-rtc-s-inc (fn-rtc-slot id s)) inc)
                (not (fn-rtc-kind-out-p :close id inc (fn-rtc-uses s))))
           (fn-rtc-uses-okp uses (fn-rtc-close-state s id inc)))
  :hints (("Goal" :induct (fn-rtc-uses-okp uses s)
           :in-theory (disable fn-rtc-core-invp fn-rtc-use-okp fn-rtc-kind-out-p fn-rtc-op-used-p
                               fn-rtc-get fn-rtc-s-inc))))

(defthm fn-rtc-uses-okp-close-state
  (implies (and (fn-rtc-core-invp s) (natp id) (equal (fn-rtc-s-inc (fn-rtc-slot id s)) inc)
                (not (fn-rtc-kind-out-p :close id inc (fn-rtc-uses s))))
           (fn-rtc-uses-okp (fn-rtc-uses s) (fn-rtc-close-state s id inc)))
  :hints (("Goal" :use fn-rtc-core-invp-uses
           :in-theory (disable fn-rtc-core-invp fn-rtc-uses-okp fn-rtc-kind-out-p fn-rtc-s-inc subsetp-equal))))

(defthm fn-rtc-workspace-owner-reconstruct
  (implies (and (fn-rtc-ownerp o) (equal (fn-rtc-get 0 o) :workspace))
           (equal (list :workspace (fn-rtc-get 1 o) (fn-rtc-get 2 o)) o))
  :hints (("Goal" :expand
           ((len o) (len (cdr o)) (len (cddr o)) (len (cdddr o))
            (true-listp o) (true-listp (cdr o)) (true-listp (cddr o)) (true-listp (cdddr o))
            (fn-rtc-get 1 o) (fn-rtc-get 2 o) (fn-rtc-get 1 (cdr o))))))

(defthm fn-rtc-pool-okp-close-state
  (implies (and (natp id) (equal (fn-rtc-s-inc (fn-rtc-slot id s)) inc)
                (fn-rtc-pool-okp i pool s))
           (fn-rtc-pool-okp i (fn-rtc-release-all pool id inc) (fn-rtc-close-state s id inc)))
  :hints (("Goal" :induct (fn-rtc-pool-induct i pool)
           :in-theory (e/d (fn-rtc-buffer-okp)
                           (fn-rtc-buf-cap fn-rtc-holds-p fn-rtc-holds-iff-positive-holders
                            fn-rtc-s-inc fn-rtc-s-status fn-rtc-uses-of-slot-p
                            fn-cbor-octet-listp fn-rtc-ownerp)))))

(defthm fn-rtc-slotp-resource
  (implies (fn-rtc-slotp slot)
           (or (null (fn-rtc-s-res slot))
               (and (natp (fn-rtc-s-res slot)) (< (fn-rtc-s-res slot) (expt 2 64))))))

(defthm fn-rtc-core-active-resource
  (implies (and (fn-rtc-core-invp s) (fn-rtc-instance-active-p id inc s))
           (and (natp (fn-rtc-s-res (fn-rtc-slot id s)))
                (< (fn-rtc-s-res (fn-rtc-slot id s)) (expt 2 64))))
  :hints (("Goal" :in-theory
           (disable fn-rtc-core-invp fn-rtc-core-invp-slot fn-rtc-slotp fn-rtc-slotp-resource
                    fn-rtc-s-res fn-rtc-s-inc fn-rtc-s-status fn-rtc-nslots)
           :use (fn-rtc-core-invp-slot (:instance fn-rtc-slotp-resource (slot (fn-rtc-slot id s)))))))

(defthm fn-rtc-draining-okp-set
  (implies (and (natp i) (natp k) (fn-rtc-draining-okp i slots uses)
                (implies (equal (fn-rtc-s-status slot) :draining)
                         (fn-rtc-uses-of-slot-p (+ i k) (fn-rtc-s-inc slot) uses)))
           (fn-rtc-draining-okp i (fn-rtc-set k slot slots) uses))
  :hints (("Goal" :induct (fn-rtc-index-induct k i slots)
           :in-theory (disable fn-rtc-uses-of-slot-p fn-rtc-s-inc fn-rtc-s-status)
           :expand ((fn-rtc-draining-okp i slots uses)
                    (fn-rtc-draining-okp i (cons slot (cdr slots)) uses)))))

(defthm fn-rtc-core-invp-close-state
  (implies (and (fn-rtc-core-invp s) (fn-rtc-instance-active-p id inc s)
                (equal (fn-rtc-s-status (fn-rtc-slot id s)) :closing)
                (not (fn-rtc-kind-out-p :close id inc (fn-rtc-uses s))))
           (fn-rtc-core-invp (fn-rtc-close-state s id inc)))
  :hints (("Goal" :in-theory
           (disable fn-rtc-configp fn-rtc-slots-okp fn-rtc-pool-okp-unfolds fn-rtc-uses-okp
                    fn-rtc-mstates-okp fn-rtc-draining-okp fn-rtc-kind-out-p fn-rtc-uses-of-slot-p
                    fn-rtc-s-inc fn-rtc-s-status fn-rtc-s-res fn-rtc-nslots fn-rtc-nbufs
                    fn-rtc-release-all fn-rtc-uses-okp-close-state fn-rtc-core-active-resource)
           :use (fn-rtc-core-active-resource fn-rtc-uses-okp-close-state))))

(defthm fn-rtc-free-slot-of-set-free
  (implies (and (natp i) (natp k) (fn-rtc-free-slot i slots)
                (equal (fn-rtc-s-status slot) :free))
           (fn-rtc-free-slot i (fn-rtc-set k slot slots)))
  :hints (("Goal" :induct (fn-rtc-index-induct k i slots)
           :in-theory (disable fn-rtc-s-status))))

(defthm fn-rtc-close-state-keeps-free-slot
  (implies (and (natp id) (fn-rtc-free-slot 0 (fn-rtc-slots s))
                (equal (fn-rtc-s-status (fn-rtc-slot id s)) :closing))
           (fn-rtc-free-slot 0 (fn-rtc-slots (fn-rtc-close-state s id inc))))
  :hints (("Goal" :in-theory
           (disable fn-rtc-free-slot fn-rtc-uses-of-slot-p fn-rtc-s-inc fn-rtc-s-status fn-rtc-s-res))))

(local (defthm fn-rtc-free-pool-buf-of-release-all
  (implies (and (natp i) (fn-rtc-free-pool-buf i pool cfg))
           (fn-rtc-free-pool-buf i (fn-rtc-release-all pool id inc) cfg))
  :hints (("Goal" :induct (fn-rtc-free-pool-buf i pool cfg)
           :in-theory (disable fn-rtc-pool-buf-p fn-rtc-b-owner fn-rtc-b-gen fn-rtc-b-bytes)))))
(local (defthm fn-rtc-close-state-preserves-grant-admission
  (implies (fn-rtc-grant-admission-safe-p s)
           (fn-rtc-grant-admission-safe-p (fn-rtc-close-state s id inc)))
  :hints (("Goal" :in-theory (e/d (fn-rtc-grant-admission-safe-p)
              (fn-rtc-close-state fn-rtc-release-all fn-rtc-free-pool-buf fn-rtc-oldest-wait fn-rtc-kind-out-p))))))
(local (defthm fn-rtc-invp-grant-admission-safe
  (implies (fn-rtc-invp s) (fn-rtc-grant-admission-safe-p s))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
              '(fn-rtc-grant-admission-safe-p)) :use fn-rtc-invp-grant-admission))))

(defthm fn-rtc-close-branch-preserves-invp
  (implies (and (fn-rtc-invp s1) (fn-rtc-instance-active-p id inc s1)
                (equal (fn-rtc-s-status (fn-rtc-slot id s1)) :closing)
                (not (fn-rtc-kind-out-p :close id inc (fn-rtc-uses s1))))
           (fn-rtc-invp (mv-nth 0 (fn-rtc-close-branch s1 id inc))))
  :hints (("Goal" :in-theory
           (e/d (fn-rtc-close-branch fn-rtc-close-state)
                (mv-nth fn-rtc-invp fn-rtc-invp-is-core-and-admission fn-rtc-core-invp
                 fn-rtc-instance-active-p fn-rtc-rearm fn-rtc-kind-out-p fn-rtc-free-slot
                 fn-rtc-uses-of-slot-p fn-rtc-s-inc fn-rtc-s-status fn-rtc-s-res
                 fn-rtc-core-invp-close-state fn-rtc-close-state-keeps-free-slot))
           :use ((:instance fn-rtc-invp-is-core-and-admission (s s1))
                 (:instance fn-rtc-core-invp-close-state (s s1))
                 (:instance fn-rtc-close-state-keeps-free-slot (s s1))
                 (:instance fn-rtc-rearm-establishes-admission (s (fn-rtc-close-state s1 id inc)))))))

(local (defthm fn-rtc-close-branch-establishes-invp
  (implies (and (fn-rtc-core-invp s1) (fn-rtc-grant-admission-safe-p s1)
                (implies (fn-rtc-kind-out-p :accept 0 0 (fn-rtc-uses s1))
                         (fn-rtc-free-slot 0 (fn-rtc-slots s1))) (fn-rtc-instance-active-p id inc s1)
                (equal (fn-rtc-s-status (fn-rtc-slot id s1)) :closing)
                (not (fn-rtc-kind-out-p :close id inc (fn-rtc-uses s1))))
           (fn-rtc-invp (mv-nth 0 (fn-rtc-close-branch s1 id inc))))
  :hints (("Goal" :in-theory
           (e/d (fn-rtc-close-branch fn-rtc-close-state)
                (mv-nth fn-rtc-invp fn-rtc-invp-is-core-and-admission fn-rtc-core-invp
                 fn-rtc-instance-active-p fn-rtc-rearm fn-rtc-kind-out-p fn-rtc-free-slot
                 fn-rtc-uses-of-slot-p fn-rtc-s-inc fn-rtc-s-status fn-rtc-s-res
                 fn-rtc-core-invp-close-state fn-rtc-close-state-keeps-free-slot))
           :use ((:instance fn-rtc-close-state-preserves-grant-admission (s s1))
                 (:instance fn-rtc-core-invp-close-state (s s1))
                 (:instance fn-rtc-close-state-keeps-free-slot (s s1))
                 (:instance fn-rtc-rearm-invp-when-admission-safe (s (fn-rtc-close-state s1 id inc))))))))

(defthm fn-rtc-kind-out-of-found-use
  (implies (fn-rtc-find-use key uses)
           (let ((u (fn-rtc-find-use key uses)))
             (fn-rtc-kind-out-p (fn-rtc-get 0 u) (fn-rtc-get 1 u) (fn-rtc-get 2 u) uses)))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use ((:instance fn-rtc-find-use-is-member (k key))
                 (:instance fn-rtc-kind-out-of-member (u (fn-rtc-find-use key uses)))))))

(defthm fn-rtc-kind-out-remove-matching
  (implies (and (not (member-eq (fn-rtc-get 0 (fn-rtc-find-use key uses)) '(:hand :pool))) (and (fn-rtc-uses-okp uses s) (fn-rtc-find-use key uses)))
           (let ((u (fn-rtc-find-use key uses)))
             (not (fn-rtc-kind-out-p (fn-rtc-get 0 u) (fn-rtc-get 1 u) (fn-rtc-get 2 u)
                                     (fn-rtc-remove-use key uses)))))
  :hints (("Goal" :induct (fn-rtc-remove-use key uses)
           :in-theory (disable fn-rtc-use-okp fn-rtc-key fn-rtc-get fn-rtc-kind-out-p fn-rtc-op-used-p))))

(defthm fn-rtc-kind-out-remove-other-kind
  (implies (not (equal kind (fn-rtc-get 0 key)))
           (equal (fn-rtc-kind-out-p kind id inc (fn-rtc-remove-use key uses))
                  (fn-rtc-kind-out-p kind id inc uses)))
  :hints (("Goal" :induct (fn-rtc-remove-use key uses))))

(defthm fn-rtc-key-kind
  (equal (fn-rtc-get 0 (fn-rtc-key e)) (fn-rtc-e-kind e)))

(defthm fn-rtc-end-use-removes-event-kind
  (implies (and (not (member-eq (fn-rtc-e-kind e) '(:hand :pool))) (and (fn-rtc-core-invp s) (fn-rtc-completionp e)
                (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s))))
           (not (fn-rtc-kind-out-p (fn-rtc-e-kind e) (fn-rtc-e-id e) (fn-rtc-e-inc e)
                                   (fn-rtc-uses (fn-rtc-end-use s e)))))
  :hints (("Goal" :in-theory
           (disable fn-rtc-core-invp fn-rtc-completionp fn-rtc-find-use fn-rtc-key
                    fn-rtc-remove-use fn-rtc-kind-out-p fn-rtc-uses-okp fn-rtc-get
                    fn-rtc-e-kind fn-rtc-e-id fn-rtc-e-inc fn-rtc-e-op
                    fn-rtc-matching-use-fields fn-rtc-kind-out-remove-matching)
           :use (fn-rtc-core-invp-uses
                 (:instance fn-rtc-matching-use-fields (uses (fn-rtc-uses s)))
                 (:instance fn-rtc-kind-out-remove-matching (key (fn-rtc-key e)) (uses (fn-rtc-uses s)))))))

(defthm fn-rtc-end-use-keeps-accept-on-other-kind
  (implies (not (equal (fn-rtc-e-kind e) :accept))
           (equal (fn-rtc-kind-out-p :accept 0 0 (fn-rtc-uses (fn-rtc-end-use s e)))
                  (fn-rtc-kind-out-p :accept 0 0 (fn-rtc-uses s))))
  :hints (("Goal" :in-theory
           (disable fn-rtc-completionp fn-rtc-find-use fn-rtc-key fn-rtc-remove-use
                    fn-rtc-kind-out-p fn-rtc-e-kind))))

(defthm fn-rtc-slots-of-end-use-when-acting
  (implies (and (not (fn-rtc-hand-delivers-p s e)) (fn-rtc-acts-on-p s e))
           (equal (fn-rtc-slots (fn-rtc-end-use s e)) (fn-rtc-slots s)))
  :hints (("Goal" :in-theory
           (disable fn-rtc-completionp fn-rtc-find-use fn-rtc-key fn-rtc-e-id fn-rtc-e-inc fn-rtc-e-kind
                    fn-rtc-s-inc fn-rtc-s-status))))

(defthm fn-rtc-slot-of-end-use-when-acting
  (implies (and (not (fn-rtc-hand-delivers-p s e)) (fn-rtc-acts-on-p s e))
           (equal (fn-rtc-slot j (fn-rtc-end-use s e)) (fn-rtc-slot j s)))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
 '(fn-rtc-slot fn-rtc-slots-of-end-use-when-acting)))))

(defthm fn-rtc-end-use-keeps-free-buffer
  (implies (and (fn-rtc-core-invp s) (natp h)
                (equal (fn-rtc-b-owner (fn-rtc-buffer h s)) '(:free)))
           (equal (fn-rtc-buffer h (fn-rtc-end-use s e)) (fn-rtc-buffer h s)))
  :hints (("Goal" :in-theory
           (e/d (fn-rtc-end-use fn-rtc-end-lease fn-rtc-leasedp)
                (fn-rtc-core-invp fn-rtc-use-okp fn-rtc-completionp fn-rtc-find-use fn-rtc-remove-use
                 fn-rtc-holds-p fn-rtc-handlep fn-rtc-key fn-rtc-h-buf fn-rtc-h-gen fn-rtc-u-hd
                 fn-rtc-b-owner fn-rtc-b-gen fn-rtc-lease-return fn-rtc-use-okp-lease))
           :use ((:instance fn-rtc-core-invp-found-use (key (fn-rtc-key e)))
                 (:instance fn-rtc-use-okp-lease (u (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s))))))))
(local (defthm fn-rtc-end-use-keeps-free-pool
  (implies (and (fn-rtc-core-invp s) (fn-rtc-free-pool-buf 0 (fn-rtc-pool s) (fn-rtc-config s)))
           (fn-rtc-free-pool-buf 0 (fn-rtc-pool (fn-rtc-end-use s e)) (fn-rtc-config s)))
  :hints (("Goal" :in-theory
           (union-theories (theory 'minimal-theory)
             '(fn-rtc-buffer natp nfix unicity-of-0 fix commutativity-of-+ fn-rtc-free-pool-buf-type
               (:executable-counterpart natp) (:executable-counterpart unary--)))
           :use ((:instance fn-rtc-end-use-keeps-free-buffer
                   (h (fn-rtc-free-pool-buf 0 (fn-rtc-pool s) (fn-rtc-config s))))
                 (:instance fn-rtc-free-pool-buf-is-free (i 0) (pool (fn-rtc-pool s)) (cfg (fn-rtc-config s)))
                 (:instance fn-rtc-free-pool-buf-pool-index (i 0) (pool (fn-rtc-pool s)) (cfg (fn-rtc-config s)))
                 (:instance fn-rtc-free-pool-buf-exists (i 0)
                   (k (fn-rtc-free-pool-buf 0 (fn-rtc-pool s) (fn-rtc-config s)))
                   (pool (fn-rtc-pool (fn-rtc-end-use s e))) (cfg (fn-rtc-config s))))))))
(local (defthm fn-rtc-oldest-wait-remove-other
  (implies (not (equal (fn-rtc-get 0 key) :wait))
           (equal (fn-rtc-oldest-wait (fn-rtc-remove-use key uses)) (fn-rtc-oldest-wait uses)))
  :hints (("Goal" :induct (fn-rtc-remove-use key uses)
           :in-theory (disable fn-rtc-get fn-rtc-key)
           :expand ((:free (u tail) (fn-rtc-oldest-wait (cons u tail)))))
          ("Subgoal *1/1" :in-theory (enable fn-rtc-key)))))
(local (defthm fn-rtc-end-use-keeps-wait
  (equal (fn-rtc-oldest-wait (fn-rtc-uses (fn-rtc-end-use s e)))
         (fn-rtc-oldest-wait (fn-rtc-uses s)))
  :hints (("Goal" :in-theory (disable fn-rtc-find-use fn-rtc-key fn-rtc-oldest-wait fn-rtc-remove-use
                                     fn-rtc-outcomep fn-rtc-retire-drained fn-rtc-end-lease)))))
(local (defthm fn-rtc-end-use-grant-subset
  (implies (not (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses s)))
           (not (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses (fn-rtc-end-use s e)))))
  :hints (("Goal" :in-theory
           (disable fn-rtc-kind-out-p fn-rtc-find-use fn-rtc-key fn-rtc-completionp fn-rtc-remove-use)))))
(local (defthm fn-rtc-end-use-preserves-grant-admission
  (implies (and (fn-rtc-core-invp s) (fn-rtc-grant-admission-safe-p s))
           (fn-rtc-grant-admission-safe-p (fn-rtc-end-use s e)))
  :hints (("Goal" :in-theory (e/d (fn-rtc-grant-admission-safe-p)
    (fn-rtc-core-invp fn-rtc-end-use fn-rtc-kind-out-p fn-rtc-free-pool-buf fn-rtc-oldest-wait))))))

(local (defthm fn-rtc-ordinary-end-use-rearm-preserves-invp
  (implies (and (not (fn-rtc-hand-delivers-p s e)) (fn-rtc-invp s) (fn-rtc-acts-on-p s e)
                (not (equal (fn-rtc-e-kind e) :accept)))
           (fn-rtc-invp (mv-nth 0 (fn-rtc-rearm (fn-rtc-end-use s e)))))
  :hints (("Goal" :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
    '(fn-rtc-invp-is-core-and-admission fn-rtc-slots-of-end-use-when-acting
      fn-rtc-end-use-keeps-accept-on-other-kind fn-rtc-end-use-preserves-core-invp
      fn-rtc-end-use-preserves-grant-admission fn-rtc-rearm-invp-when-admission-safe))
    :use fn-rtc-invp-grant-admission-safe))))

(local (defthm fn-rtc-deliver-rearm-establishes-invp
  (implies (and (fn-rtc-core-invp s) (fn-rtc-instance-active-p id inc s)
                (fn-rtc-grant-admission-safe-p s)
                (implies (fn-rtc-kind-out-p :accept 0 0 (fn-rtc-uses s))
                         (fn-rtc-free-slot 0 (fn-rtc-slots s))))
           (fn-rtc-invp (mv-nth 0 (fn-rtc-rearm (mv-nth 0 (fn-rtc-deliver s id inc ev q))))))
  :hints (("Goal" :in-theory
    (e/d (fn-rtc-instance-active-p)
      (mv-nth fn-rtc-invp fn-rtc-core-invp fn-rtc-free-slot fn-rtc-kind-out-p
       fn-rtc-grant-admission-safe-p fn-rtc-deliver fn-rtc-rearm fn-rtc-nslots fn-rtc-s-inc fn-rtc-s-status))))))

(local (defthm fn-rtc-deliver-rearm-preserves-invp
  (implies (and (fn-rtc-invp s) (fn-rtc-instance-active-p id inc s))
           (fn-rtc-invp (mv-nth 0 (fn-rtc-rearm (mv-nth 0 (fn-rtc-deliver s id inc ev q))))))
  :hints (("Goal" :in-theory
    (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
      '(fn-rtc-invp-is-core-and-admission fn-rtc-deliver-rearm-establishes-invp))
    :use fn-rtc-invp-grant-admission-safe))))

(defthm fn-rtc-accept-event-listener
  (implies (and (fn-rtc-invp s) (fn-rtc-acts-on-p s e) (equal (fn-rtc-e-kind e) :accept))
           (and (equal (fn-rtc-e-id e) 0) (equal (fn-rtc-e-inc e) 0)))
  :hints (("Goal" :in-theory
           (disable fn-rtc-invp fn-rtc-invp-is-core-and-admission fn-rtc-completionp
                    fn-rtc-find-use fn-rtc-key fn-rtc-e-kind fn-rtc-e-id fn-rtc-e-inc
                    fn-rtc-acts-on-accept-id fn-rtc-invp-listener)
           :use (fn-rtc-acts-on-accept-id fn-rtc-invp-listener))))

(defthm fn-rtc-end-use-keeps-free-slot
  (implies (fn-rtc-free-slot 0 (fn-rtc-slots s))
           (fn-rtc-free-slot 0 (fn-rtc-slots (fn-rtc-end-use s e))))
  :hints (("Goal" :in-theory
           (e/d (fn-rtc-end-use fn-rtc-retire-drained)
                (fn-rtc-free-slot fn-rtc-completionp fn-rtc-find-use fn-rtc-key
                 fn-rtc-uses-of-slot-p fn-rtc-e-id fn-rtc-s-inc fn-rtc-s-status)))))

(defthm fn-rtc-end-use-accept-subset
  (implies (not (fn-rtc-kind-out-p :accept 0 0 (fn-rtc-uses s)))
           (not (fn-rtc-kind-out-p :accept 0 0 (fn-rtc-uses (fn-rtc-end-use s e)))))
  :hints (("Goal" :in-theory
           (disable fn-rtc-kind-out-p fn-rtc-find-use fn-rtc-key fn-rtc-completionp fn-rtc-remove-use))))

(defthm fn-rtc-end-use-rearm-preserves-invp
  (implies (fn-rtc-invp s)
           (fn-rtc-invp (mv-nth 0 (fn-rtc-rearm (fn-rtc-end-use s e)))))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use (fn-rtc-invp-is-core-and-admission fn-rtc-end-use-keeps-free-slot
                 fn-rtc-end-use-accept-subset fn-rtc-end-use-preserves-core-invp
                 fn-rtc-invp-grant-admission-safe fn-rtc-end-use-preserves-grant-admission
                 (:instance fn-rtc-rearm-invp-when-admission-safe (s (fn-rtc-end-use s e)))))))

(defthm fn-rtc-live-slot-of-end-use
  (implies (and (natp j) (equal (fn-rtc-s-status (fn-rtc-slot j s)) :live))
           (equal (fn-rtc-slot j (fn-rtc-end-use s e)) (fn-rtc-slot j s)))
  :hints (("Goal" :in-theory
           (e/d (fn-rtc-end-use fn-rtc-retire-drained)
                (fn-rtc-completionp fn-rtc-find-use fn-rtc-remove-use fn-rtc-key fn-rtc-e-id
                 fn-rtc-s-inc fn-rtc-s-status fn-rtc-end-lease fn-rtc-uses-of-slot-p)))))

(defthm fn-rtc-hand-target-active
  (implies (and (fn-rtc-core-invp s) (fn-rtc-hand-delivers-p s e))
           (let* ((u (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))
                  (o (fn-rtc-b-owner (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd u)) s))))
             (fn-rtc-instance-active-p (nfix (fn-rtc-get 3 o)) (fn-rtc-get 4 o)
                                        (fn-rtc-end-use s e))))
  :hints (("Goal" :in-theory
           (e/d (fn-rtc-hand-delivers-p fn-rtc-handed-to-live-p fn-rtc-live-p
                 fn-rtc-instance-active-p fn-rtc-buffer-okp)
                (fn-rtc-core-invp fn-rtc-use-okp fn-rtc-use-okp-buffer-index fn-rtc-core-invp-found-use
                 fn-rtc-core-invp-buffer fn-rtc-bufferp fn-rtc-ownerp fn-rtc-end-use
                 fn-rtc-delivered-outcome fn-rtc-u-hd fn-rtc-h-buf fn-rtc-handlep
                 fn-rtc-b-owner fn-rtc-b-gen fn-rtc-b-bytes fn-rtc-s-inc fn-rtc-s-status
                 fn-rtc-get fn-rtc-nslots fn-rtc-nbufs fn-rtc-nstatic fn-rtc-cap
                 fn-rtc-find-use fn-rtc-completionp fn-rtc-key fn-rtc-e-kind))
           :use ((:instance fn-rtc-core-invp-found-use (key (fn-rtc-key e)))
                 (:instance fn-rtc-use-okp-buffer-index (u (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s))))
                 (:instance fn-rtc-core-invp-buffer
                   (h (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s))))))))))

(defthm fn-rtc-deliver-rearm-after-end-use
  (implies (and (fn-rtc-invp s) (fn-rtc-instance-active-p id inc (fn-rtc-end-use s e)))
           (fn-rtc-invp (mv-nth 0 (fn-rtc-rearm
                                  (mv-nth 0 (fn-rtc-deliver (fn-rtc-end-use s e) id inc ev q))))))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use (fn-rtc-invp-is-core-and-admission fn-rtc-end-use-preserves-core-invp
                 fn-rtc-invp-grant-admission-safe fn-rtc-end-use-preserves-grant-admission
                 fn-rtc-end-use-keeps-free-slot fn-rtc-end-use-accept-subset
                 (:instance fn-rtc-deliver-rearm-establishes-invp (s (fn-rtc-end-use s e)))))))

(defthm fn-rtc-oldest-wait-member
  (implies (fn-rtc-oldest-wait uses) (member-equal (fn-rtc-oldest-wait uses) uses))
  :hints (("Goal" :induct (fn-rtc-oldest-wait uses) :in-theory (disable fn-rtc-get))))
(local (defthm fn-rtc-key-of-replace-use-old
  (implies (equal (fn-rtc-get 0 key) :wait)
           (equal (fn-rtc-get 0 (fn-rtc-find-use key uses)) (if (fn-rtc-find-use key uses) :wait nil)))
  :hints (("Goal" :induct (fn-rtc-find-use key uses)))))
(local (defthm fn-rtc-use-wait-unbuffered
  (implies (and (fn-rtc-usep u) (equal (fn-rtc-get 0 u) :wait))
           (not (fn-rtc-handlep (fn-rtc-u-hd u))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-usep fn-rtc-u-hd) (fn-rtc-get))))))
(local (defthm fn-rtc-replace-use-kind-subset
  (implies (and (not (equal kind (fn-rtc-get 0 v))) (not (fn-rtc-kind-out-p kind id inc uses)))
           (not (fn-rtc-kind-out-p kind id inc (fn-rtc-replace-use key v uses))))
  :hints (("Goal" :induct (fn-rtc-replace-use key v uses)
           :in-theory (disable fn-rtc-get fn-rtc-key)))))
(local (defthm fn-rtc-replace-use-op-subset
  (implies (and (not (equal op (fn-rtc-get 3 v))) (not (fn-rtc-op-used-p op uses)))
           (not (fn-rtc-op-used-p op (fn-rtc-replace-use key v uses))))
  :hints (("Goal" :induct (fn-rtc-replace-use key v uses)
           :in-theory (disable fn-rtc-get fn-rtc-key)))))
(local (defthm fn-rtc-replace-wait-op-unused
  (implies (and (fn-rtc-uses-okp uses s)
                (equal (fn-rtc-get 3 key) (fn-rtc-get 3 v))
                (not (fn-rtc-op-used-p op uses)))
           (not (fn-rtc-op-used-p op (fn-rtc-replace-use key v uses))))
  :hints (("Goal" :induct (fn-rtc-replace-use key v uses)
           :in-theory (disable fn-rtc-use-okp fn-rtc-get fn-rtc-kind-out-p)))))
(local (defthm fn-rtc-uses-okp-replace-wait
  (implies (and (fn-rtc-uses-okp uses s) (equal (fn-rtc-get 0 v) :pool)
                (equal (fn-rtc-get 3 v) (fn-rtc-get 3 key)) (fn-rtc-use-okp v s))
           (fn-rtc-uses-okp (fn-rtc-replace-use key v uses) s))
  :hints (("Goal" :induct (fn-rtc-replace-use key v uses)
           :in-theory (disable fn-rtc-use-okp fn-rtc-get fn-rtc-kind-out-p fn-rtc-op-used-p)))))
(local (defthm fn-rtc-holders-replace-wait
  (implies (and (fn-rtc-uses-okp uses s) (equal (fn-rtc-get 0 key) :wait))
           (equal (fn-rtc-holders h g (fn-rtc-replace-use key v uses))
                  (+ (fn-rtc-holders h g uses)
                     (if (and (fn-rtc-find-use key uses) (fn-rtc-handlep (fn-rtc-u-hd v))
                              (equal h (fn-rtc-h-buf (fn-rtc-u-hd v)))
                              (equal g (fn-rtc-h-gen (fn-rtc-u-hd v)))) 1 0))))
  :hints (("Goal" :induct (fn-rtc-replace-use key v uses)
           :in-theory (disable fn-rtc-usep fn-rtc-use-okp fn-rtc-key fn-rtc-get fn-rtc-u-hd
                               fn-rtc-handlep fn-rtc-h-buf fn-rtc-h-gen fn-rtc-kind-out-p fn-rtc-op-used-p)
           :expand ((:free (u us) (fn-rtc-holders h g (cons u us)))))
          ("Subgoal *1/1" :in-theory (enable fn-rtc-use-okp fn-rtc-key)))))


(defun fn-rtc-pool-grant-use (w h s)
  (declare (xargs :guard t))
  (list :pool (nfix (fn-rtc-get 1 w)) (fn-rtc-get 2 w) (fn-rtc-get 3 w)
        (list h (+ 1 (fn-rtc-b-gen (fn-rtc-buffer h s))) 0 0)))

(defun fn-rtc-pool-grant-state (w h s)
  (declare (xargs :guard t))
  (fn-rtc-with-buffer h
    (list (+ 1 (fn-rtc-b-gen (fn-rtc-buffer h s)))
          (list :leased (nfix (fn-rtc-get 1 w)) (fn-rtc-get 2 w) :in) nil)
    (fn-rtc-with-uses (fn-rtc-replace-use (fn-rtc-key w) (fn-rtc-pool-grant-use w h s)
                                        (fn-rtc-uses s)) s)))

(defthm fn-rtc-pool-grant-use-fields
  (and (equal (fn-rtc-get 0 (fn-rtc-pool-grant-use w h s)) :pool)
       (equal (fn-rtc-get 1 (fn-rtc-pool-grant-use w h s)) (nfix (fn-rtc-get 1 w)))
       (equal (fn-rtc-get 2 (fn-rtc-pool-grant-use w h s)) (fn-rtc-get 2 w))
       (equal (fn-rtc-get 3 (fn-rtc-pool-grant-use w h s)) (fn-rtc-get 3 w))
       (fn-rtc-handlep (fn-rtc-u-hd (fn-rtc-pool-grant-use w (nfix h) s)))
       (equal (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-pool-grant-use w h s))) (nfix h))
       (equal (fn-rtc-h-gen (fn-rtc-u-hd (fn-rtc-pool-grant-use w h s))) (+ 1 (fn-rtc-b-gen (fn-rtc-buffer h s))))
       (equal (fn-rtc-h-off (fn-rtc-u-hd (fn-rtc-pool-grant-use w h s))) 0)
       (equal (fn-rtc-h-len (fn-rtc-u-hd (fn-rtc-pool-grant-use w h s))) 0))
  :hints (("Goal" :in-theory (disable fn-rtc-b-gen fn-rtc-buffer))))
(defthm fn-rtc-pool-grant-state-frame
  (and (equal (fn-rtc-config (fn-rtc-pool-grant-state w h s)) (fn-rtc-config s))
       (equal (fn-rtc-slot j (fn-rtc-pool-grant-state w h s)) (fn-rtc-slot j s))
       (equal (fn-rtc-slots (fn-rtc-pool-grant-state w h s)) (fn-rtc-slots s))
       (equal (fn-rtc-mstates (fn-rtc-pool-grant-state w h s)) (fn-rtc-mstates s))
       (equal (fn-rtc-next-op (fn-rtc-pool-grant-state w h s)) (fn-rtc-next-op s))
       (equal (fn-rtc-uses (fn-rtc-pool-grant-state w h s))
              (fn-rtc-replace-use (fn-rtc-key w) (fn-rtc-pool-grant-use w h s) (fn-rtc-uses s))))
  :hints (("Goal" :in-theory (disable fn-rtc-pool-grant-use fn-rtc-b-gen fn-rtc-key fn-rtc-replace-use))))
(local (defthm fn-rtc-pool-grant-state-other-buffer
  (implies (not (equal (nfix k) (nfix h)))
           (equal (fn-rtc-buffer k (fn-rtc-pool-grant-state w h s)) (fn-rtc-buffer k s)))
  :hints (("Goal" :in-theory (disable fn-rtc-pool-grant-use fn-rtc-b-gen fn-rtc-key fn-rtc-replace-use)))))
(local (defthm fn-rtc-use-okp-avoids-free-buffer
  (implies (and (fn-rtc-use-okp u s) (fn-rtc-handlep (fn-rtc-u-hd u))
                (equal (fn-rtc-b-owner (fn-rtc-buffer h s)) '(:free)))
           (not (equal (fn-rtc-h-buf (fn-rtc-u-hd u)) h)))
  :hints (("Goal" :use fn-rtc-use-okp-lease
           :in-theory (e/d (fn-rtc-leasedp)
             (fn-rtc-use-okp-lease fn-rtc-use-okp fn-rtc-u-hd fn-rtc-handlep fn-rtc-h-buf fn-rtc-b-owner fn-rtc-h-gen fn-rtc-b-gen))))))


(local (defthm fn-rtc-pool-grant-use-handle
  (equal (fn-rtc-get 4 (fn-rtc-pool-grant-use w h s))
         (list h (+ 1 (fn-rtc-b-gen (fn-rtc-buffer h s))) 0 0))
  :hints (("Goal" :in-theory (disable fn-rtc-b-gen fn-rtc-buffer)))))
(local (defthm fn-rtc-pool-grant-use-valid
  (implies (and (natp h) (fn-rtc-usep w)) (fn-rtc-usep (fn-rtc-pool-grant-use w h s)))
  :hints (("Goal" :in-theory (e/d (fn-rtc-usep) (fn-rtc-b-gen fn-rtc-buffer fn-rtc-get))))))
(local (defthm fn-rtc-pool-grant-use-list-shape
  (and (true-listp (fn-rtc-pool-grant-use w h s))
       (equal (len (fn-rtc-pool-grant-use w h s)) 5))))
(local (defthm fn-rtc-pool-grant-use-handlep
  (implies (natp h) (fn-rtc-handlep (fn-rtc-u-hd (fn-rtc-pool-grant-use w h s))))
  :hints (("Goal" :in-theory (disable fn-rtc-b-gen fn-rtc-buffer)))))


(local (defthm fn-rtc-use-okp-through-pool-grant
  (implies (and (natp h) (fn-rtc-use-okp u s) (fn-rtc-uses-okp (fn-rtc-uses s) s)
                (equal (fn-rtc-get 0 w) :wait)
                (equal (fn-rtc-b-owner (fn-rtc-buffer h s)) '(:free)))
           (fn-rtc-use-okp u (fn-rtc-pool-grant-state w h s)))
  :hints (("Goal" :in-theory
           (union-theories (theory 'minimal-theory)
             '(fn-rtc-use-okp fn-rtc-current-p fn-rtc-pool-grant-state-frame
               fn-rtc-pool-grant-state-other-buffer fn-rtc-pool-grant-use-fields
               fn-rtc-holders-replace-wait fn-rtc-key-kind fn-rtc-e-kind
               natp nfix unicity-of-0 fix (:type-prescription fn-rtc-h-buf)
               (:executable-counterpart member-equal) (:executable-counterpart fn-rtc-get)))
           :use (fn-rtc-use-okp-avoids-free-buffer
                 (:instance fn-rtc-holders-replace-wait (key (fn-rtc-key w))
                   (uses (fn-rtc-uses s)) (h (fn-rtc-h-buf (fn-rtc-u-hd u)))
                   (g (fn-rtc-h-gen (fn-rtc-u-hd u))) (v (fn-rtc-pool-grant-use w h s))))))))

(local (defthm fn-rtc-uses-okp-through-pool-grant
  (implies (and (natp h) (fn-rtc-uses-okp uses s) (fn-rtc-uses-okp (fn-rtc-uses s) s)
                (equal (fn-rtc-get 0 w) :wait)
                (equal (fn-rtc-b-owner (fn-rtc-buffer h s)) '(:free)))
           (fn-rtc-uses-okp uses (fn-rtc-pool-grant-state w h s)))
  :hints (("Goal" :induct (fn-rtc-uses-okp uses s)
           :in-theory (e/d (fn-rtc-uses-okp)
             (fn-rtc-use-okp fn-rtc-pool-grant-state fn-rtc-get fn-rtc-kind-out-p fn-rtc-op-used-p
              fn-rtc-b-owner fn-rtc-buffer))))))

(local (defthm fn-rtc-pool-grant-new-use-okp
  (implies (and (fn-rtc-core-invp s) (fn-rtc-use-okp w s) (member-equal w (fn-rtc-uses s))
                (equal (fn-rtc-get 0 w) :wait) (natp h) (< h (fn-rtc-nbufs (fn-rtc-config s)))
                (fn-rtc-pool-buf-p h (fn-rtc-config s))
                (equal (fn-rtc-b-owner (fn-rtc-buffer h s)) '(:free)))
           (fn-rtc-use-okp (fn-rtc-pool-grant-use w h s) (fn-rtc-pool-grant-state w h s)))
  :hints (("Goal" :in-theory
           (e/d (fn-rtc-pool-grant-state fn-rtc-use-okp fn-rtc-current-p)
              (fn-rtc-pool-grant-use fn-rtc-uses-okp-member fn-rtc-core-invp fn-rtc-uses-okp fn-rtc-get
               fn-rtc-b-owner fn-rtc-b-gen fn-rtc-b-bytes fn-rtc-s-inc fn-rtc-s-status
               fn-rtc-nslots fn-rtc-nbufs fn-rtc-buf-cap fn-rtc-pool-buf-p
               fn-rtc-holders fn-rtc-key fn-rtc-replace-use fn-rtc-find-use))
           :use ((:instance fn-rtc-holders-of-unleased-buffer
                   (g (+ 1 (fn-rtc-b-gen (fn-rtc-buffer h s)))) (uses (fn-rtc-uses s)))
                 (:instance fn-rtc-holders-replace-wait (key (fn-rtc-key w))
                   (uses (fn-rtc-uses s)) (g (+ 1 (fn-rtc-b-gen (fn-rtc-buffer h s))))
                   (v (fn-rtc-pool-grant-use w h s))))))))

(local (defthm fn-rtc-pool-grant-uses-okp
  (implies (and (fn-rtc-core-invp s) (fn-rtc-use-okp w s) (member-equal w (fn-rtc-uses s))
                (equal (fn-rtc-get 0 w) :wait) (natp h) (< h (fn-rtc-nbufs (fn-rtc-config s)))
                (fn-rtc-pool-buf-p h (fn-rtc-config s))
                (equal (fn-rtc-b-owner (fn-rtc-buffer h s)) '(:free)))
           (fn-rtc-uses-okp (fn-rtc-uses (fn-rtc-pool-grant-state w h s))
                            (fn-rtc-pool-grant-state w h s)))
  :hints (("Goal" :in-theory
           (e/d (fn-rtc-key) (fn-rtc-core-invp fn-rtc-use-okp fn-rtc-uses-okp
             fn-rtc-pool-grant-use fn-rtc-pool-grant-state fn-rtc-get fn-rtc-b-owner
             fn-rtc-pool-buf-p fn-rtc-uses-okp-member))))))
(local (defthm fn-rtc-buffer-okp-through-pool-grant
  (implies (and (fn-rtc-uses-okp (fn-rtc-uses s) s) (fn-rtc-buffer-okp k b s)
                (equal (fn-rtc-get 0 w) :wait))
           (fn-rtc-buffer-okp k b (fn-rtc-pool-grant-state w h s)))
  :hints (("Goal" :in-theory
           (e/d (fn-rtc-buffer-okp fn-rtc-grant-admission-safe-p)
             (fn-rtc-pool-grant-use fn-rtc-pool-grant-state fn-rtc-bufferp fn-rtc-buf-cap
              fn-rtc-b-owner fn-rtc-b-gen fn-rtc-holders fn-rtc-find-use fn-rtc-key fn-rtc-get
              fn-rtc-u-hd fn-rtc-handlep fn-rtc-s-inc fn-rtc-s-status fn-rtc-nslots fn-rtc-nstatic
              fn-rtc-uses-okp fn-rtc-h-buf fn-rtc-h-gen))
           :use ((:instance fn-rtc-holders-replace-wait (key (fn-rtc-key w))
                    (uses (fn-rtc-uses s)) (h k) (g (fn-rtc-b-gen b))
                    (v (fn-rtc-pool-grant-use w h s))))))))
(local (defthm fn-rtc-old-pool-okp-through-grant
  (implies (and (fn-rtc-uses-okp (fn-rtc-uses s) s) (fn-rtc-pool-okp k pool s)
                (equal (fn-rtc-get 0 w) :wait))
           (fn-rtc-pool-okp k pool (fn-rtc-pool-grant-state w h s)))
  :hints (("Goal" :induct (fn-rtc-pool-induct k pool)
           :in-theory (union-theories (theory 'minimal-theory)
             '(fn-rtc-pool-okp-unfolds (:induction fn-rtc-pool-induct)
               fn-rtc-buffer-okp-through-pool-grant))))))
(local (defthm fn-rtc-pool-grant-holders
  (implies (and (fn-rtc-core-invp s) (member-equal w (fn-rtc-uses s))
                (equal (fn-rtc-get 0 w) :wait) (natp h)
                (equal (fn-rtc-b-owner (fn-rtc-buffer h s)) '(:free)))
           (equal (fn-rtc-holders h (+ 1 (fn-rtc-b-gen (fn-rtc-buffer h s)))
                                  (fn-rtc-uses (fn-rtc-pool-grant-state w h s))) 1))
  :hints (("Goal" :in-theory
           (e/d (fn-rtc-leasedp)
             (fn-rtc-core-invp fn-rtc-pool-grant-use fn-rtc-pool-grant-state fn-rtc-get
              fn-rtc-b-gen fn-rtc-b-owner fn-rtc-holders fn-rtc-uses-okp fn-rtc-find-use
              fn-rtc-key fn-rtc-u-hd fn-rtc-handlep fn-rtc-h-buf fn-rtc-h-gen))
           :use (fn-rtc-pool-grant-use-fields
                 (:instance fn-rtc-holders-of-unleased-buffer (uses (fn-rtc-uses s))
                            (g (+ 1 (fn-rtc-b-gen (fn-rtc-buffer h s)))))
                 (:instance fn-rtc-holders-replace-wait (key (fn-rtc-key w))
                    (uses (fn-rtc-uses s)) (g (+ 1 (fn-rtc-b-gen (fn-rtc-buffer h s))))
                    (v (fn-rtc-pool-grant-use w h s))))))))
(local (defthm fn-rtc-pool-grant-new-buffer-okp
  (implies (and (fn-rtc-core-invp s) (fn-rtc-use-okp w s) (member-equal w (fn-rtc-uses s))
                (equal (fn-rtc-get 0 w) :wait) (natp h)
                (equal (fn-rtc-b-owner (fn-rtc-buffer h s)) '(:free)))
           (fn-rtc-buffer-okp h
             (list (+ 1 (fn-rtc-b-gen (fn-rtc-buffer h s)))
                   (list :leased (nfix (fn-rtc-get 1 w)) (fn-rtc-get 2 w) :in) nil)
             (fn-rtc-pool-grant-state w h s)))
  :hints (("Goal" :in-theory
           (e/d (fn-rtc-buffer-okp fn-rtc-use-okp)
             (fn-rtc-core-invp fn-rtc-pool-grant-state fn-rtc-pool-grant-use fn-rtc-uses-okp-member
              fn-rtc-get fn-rtc-buf-cap fn-rtc-holders fn-rtc-b-gen fn-rtc-b-owner fn-rtc-b-bytes
              fn-rtc-uses-okp fn-rtc-find-use fn-rtc-key fn-rtc-h-buf fn-rtc-h-gen))
           :use fn-rtc-pool-grant-holders))))


(local (defthm fn-rtc-pool-grant-state-record
  (and (true-listp (fn-rtc-pool-grant-state w h s))
       (equal (len (fn-rtc-pool-grant-state w h s)) 6)
       (equal (fn-rtc-get 5 (fn-rtc-pool-grant-state w h s)) (fn-rtc-next-op s)))))

(local (defthm fn-rtc-pool-grant-state-pool
  (equal (fn-rtc-pool (fn-rtc-pool-grant-state w h s))
         (fn-rtc-set h (list (+ 1 (fn-rtc-b-gen (fn-rtc-buffer h s)))
                             (list :leased (nfix (fn-rtc-get 1 w)) (fn-rtc-get 2 w) :in) nil)
                      (fn-rtc-pool s)))
  :hints (("Goal" :in-theory (disable fn-rtc-pool-grant-use fn-rtc-replace-use fn-rtc-b-gen fn-rtc-key)))))

(local (defthm fn-rtc-pool-grant-pool-okp
  (implies (and (fn-rtc-core-invp s) (fn-rtc-use-okp w s) (member-equal w (fn-rtc-uses s))
                (equal (fn-rtc-get 0 w) :wait) (natp h)
                (equal (fn-rtc-b-owner (fn-rtc-buffer h s)) '(:free)))
           (fn-rtc-pool-okp 0 (fn-rtc-pool (fn-rtc-pool-grant-state w h s))
                             (fn-rtc-pool-grant-state w h s)))
  :hints (("Goal" :in-theory
             (disable fn-rtc-core-invp fn-rtc-use-okp fn-rtc-uses-okp fn-rtc-uses-okp-member
              fn-rtc-pool-grant-state fn-rtc-pool-grant-use fn-rtc-get fn-rtc-b-gen fn-rtc-b-owner
              fn-rtc-pool-okp-unfolds fn-rtc-buffer-okp fn-rtc-set)
           :use (fn-rtc-core-invp-pool fn-rtc-core-invp-uses fn-rtc-pool-grant-new-buffer-okp
                 (:instance fn-rtc-old-pool-okp-through-grant (k 0) (pool (fn-rtc-pool s)))
                 (:instance fn-rtc-pool-okp-set (i 0) (k h) (pool (fn-rtc-pool s))
                   (s (fn-rtc-pool-grant-state w h s))
                   (b (list (+ 1 (fn-rtc-b-gen (fn-rtc-buffer h s)))
                            (list :leased (nfix (fn-rtc-get 1 w)) (fn-rtc-get 2 w) :in) nil))))))))

(local (defthm fn-rtc-uses-of-slot-replace-same-instance
  (implies (and (equal (fn-rtc-get 1 v) (fn-rtc-get 1 key))
                (equal (fn-rtc-get 2 v) (fn-rtc-get 2 key)))
           (equal (fn-rtc-uses-of-slot-p id inc (fn-rtc-replace-use key v uses))
                  (fn-rtc-uses-of-slot-p id inc uses)))
  :hints (("Goal" :induct (fn-rtc-replace-use key v uses)))))

(local (defthm fn-rtc-draining-okp-replace-same-instance
  (implies (and (equal (fn-rtc-get 1 v) (fn-rtc-get 1 key))
                (equal (fn-rtc-get 2 v) (fn-rtc-get 2 key)))
           (equal (fn-rtc-draining-okp i slots (fn-rtc-replace-use key v uses))
                  (fn-rtc-draining-okp i slots uses)))
  :hints (("Goal" :induct (fn-rtc-draining-okp i slots uses)
           :in-theory (disable fn-rtc-replace-use fn-rtc-get fn-rtc-uses-of-slot-p fn-rtc-s-inc fn-rtc-s-status)))))

(defthm fn-rtc-use-okp-natural-fields
  (implies (fn-rtc-use-okp w s)
           (and (natp (fn-rtc-get 1 w)) (natp (fn-rtc-get 2 w)) (natp (fn-rtc-get 3 w))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-rtc-use-okp fn-rtc-usep)))))

(local (defthm fn-rtc-pool-grant-state-pool-length
  (equal (len (fn-rtc-pool (fn-rtc-pool-grant-state w h s))) (len (fn-rtc-pool s)))
  :hints (("Goal" :in-theory (disable fn-rtc-pool-grant-state fn-rtc-b-gen fn-rtc-b-owner fn-rtc-get)))))


(local (defthm fn-rtc-pool-grant-preserves-core-invp
  (implies (and (fn-rtc-core-invp s) (fn-rtc-use-okp w s) (member-equal w (fn-rtc-uses s))
                (equal (fn-rtc-get 0 w) :wait) (natp h) (< h (fn-rtc-nbufs (fn-rtc-config s)))
                (fn-rtc-pool-buf-p h (fn-rtc-config s))
                (equal (fn-rtc-b-owner (fn-rtc-buffer h s)) '(:free)))
           (fn-rtc-core-invp (fn-rtc-pool-grant-state w h s)))
  :hints (("Goal" :in-theory
           (union-theories (theory 'minimal-theory)
             '(fn-rtc-core-invp fn-rtc-pool-grant-state-frame fn-rtc-pool-grant-state-record
               fn-rtc-pool-grant-state-pool-length fn-rtc-pool-grant-use-fields
               fn-rtc-draining-okp-replace-same-instance fn-rtc-key fn-rtc-get-of-cons
               natp nfix unicity-of-0 fix (:type-prescription fn-rtc-next-op)
               (:executable-counterpart zp) (:executable-counterpart natp)
               (:executable-counterpart unary--) (:executable-counterpart binary-+)))
           :use (fn-rtc-use-okp-natural-fields fn-rtc-pool-grant-pool-okp fn-rtc-pool-grant-uses-okp)))))

(defthm fn-rtc-free-pool-buf-upper-bound
  (implies (and (natp i) (fn-rtc-free-pool-buf i pool cfg))
           (< (fn-rtc-free-pool-buf i pool cfg) (+ i (len pool))))
  :hints (("Goal" :induct (fn-rtc-free-pool-buf i pool cfg)
           :in-theory (disable fn-rtc-pool-buf-p fn-rtc-b-owner)))
  :rule-classes :linear)
(defthm fn-rtc-grant-one-is-pool-grant-state
  (equal (mv-nth 0 (fn-rtc-grant-one s))
         (let ((h (fn-rtc-free-pool-buf 0 (fn-rtc-pool s) (fn-rtc-config s)))
               (w (fn-rtc-oldest-wait (fn-rtc-uses s))))
           (if (and h w) (fn-rtc-pool-grant-state w h s) s)))
  :hints (("Goal" :in-theory
           (disable fn-rtc-free-pool-buf fn-rtc-oldest-wait fn-rtc-b-gen fn-rtc-get fn-rtc-key fn-rtc-replace-use))))
(defthm fn-rtc-grant-one-preserves-core-invp
  (implies (fn-rtc-core-invp s) (fn-rtc-core-invp (mv-nth 0 (fn-rtc-grant-one s))))
  :hints (("Goal" :in-theory
           (disable mv-nth fn-rtc-core-invp fn-rtc-use-okp fn-rtc-uses-okp fn-rtc-uses-okp-member
              fn-rtc-grant-one fn-rtc-pool-grant-state fn-rtc-pool-grant-use fn-rtc-b-owner fn-rtc-buffer
              fn-rtc-free-pool-buf fn-rtc-oldest-wait fn-rtc-pool-buf-p fn-rtc-get)
           :use (fn-rtc-core-invp-shape
                 (:instance fn-rtc-pool-grant-preserves-core-invp
                   (w (fn-rtc-oldest-wait (fn-rtc-uses s)))
                   (h (fn-rtc-free-pool-buf 0 (fn-rtc-pool s) (fn-rtc-config s))))
                 (:instance fn-rtc-free-pool-buf-pool-index (i 0) (pool (fn-rtc-pool s)) (cfg (fn-rtc-config s)))
                 (:instance fn-rtc-free-pool-buf-upper-bound (i 0) (pool (fn-rtc-pool s)) (cfg (fn-rtc-config s)))
                 (:instance fn-rtc-free-pool-buf-is-free (i 0) (pool (fn-rtc-pool s)) (cfg (fn-rtc-config s)))
                 (:instance fn-rtc-uses-okp-member (u (fn-rtc-oldest-wait (fn-rtc-uses s))) (uses (fn-rtc-uses s)))))))
(local (defthm fn-rtc-grant-preserves-core-invp
  (implies (fn-rtc-core-invp s) (fn-rtc-core-invp (mv-nth 0 (fn-rtc-grant n s))))
  :hints (("Goal" :induct (fn-rtc-grant n s)
           :in-theory (e/d (fn-rtc-grant) (mv-nth fn-rtc-core-invp fn-rtc-grant-one fn-rtc-grant-one-is-pool-grant-state))))))
(local (defthm fn-rtc-kind-out-replace-other
  (implies (and (not (equal kind (fn-rtc-get 0 key))) (not (equal kind (fn-rtc-get 0 v))))
           (equal (fn-rtc-kind-out-p kind id inc (fn-rtc-replace-use key v uses))
                  (fn-rtc-kind-out-p kind id inc uses)))
  :hints (("Goal" :induct (fn-rtc-replace-use key v uses)))))
(local (defthm fn-rtc-grant-one-admission-fields
  (and (equal (fn-rtc-kind-out-p :accept 0 0 (fn-rtc-uses (mv-nth 0 (fn-rtc-grant-one s))))
              (fn-rtc-kind-out-p :accept 0 0 (fn-rtc-uses s)))
       (equal (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses (mv-nth 0 (fn-rtc-grant-one s))))
              (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses s))))
  :hints (("Goal" :in-theory
           (disable mv-nth fn-rtc-grant-one fn-rtc-pool-grant-state fn-rtc-pool-grant-use
                    fn-rtc-free-pool-buf fn-rtc-oldest-wait fn-rtc-kind-out-p fn-rtc-replace-use)))))
(local (defthm fn-rtc-grant-admission-fields
  (and (equal (fn-rtc-kind-out-p :accept 0 0 (fn-rtc-uses (mv-nth 0 (fn-rtc-grant n s))))
              (fn-rtc-kind-out-p :accept 0 0 (fn-rtc-uses s)))
       (equal (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses (mv-nth 0 (fn-rtc-grant n s))))
              (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses s))))
  :hints (("Goal" :induct (fn-rtc-grant n s)
           :in-theory (e/d (fn-rtc-grant)
              (mv-nth fn-rtc-grant-one fn-rtc-kind-out-p fn-rtc-grant-one-is-pool-grant-state))))))
(local (defthm fn-rtc-grant-rearm-establishes-invp
  (implies (and (fn-rtc-core-invp s) (not (fn-rtc-kind-out-p :grant 0 0 (fn-rtc-uses s)))
                (implies (fn-rtc-kind-out-p :accept 0 0 (fn-rtc-uses s))
                         (fn-rtc-free-slot 0 (fn-rtc-slots s))))
           (fn-rtc-invp (mv-nth 0 (fn-rtc-rearm (mv-nth 0 (fn-rtc-grant n s))))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-grant-admission-safe-p)
             (mv-nth fn-rtc-core-invp fn-rtc-invp fn-rtc-invp-is-core-and-admission
              fn-rtc-grant fn-rtc-rearm fn-rtc-free-slot fn-rtc-free-pool-buf fn-rtc-oldest-wait fn-rtc-kind-out-p))
           :use ((:instance fn-rtc-rearm-invp-when-admission-safe (s (mv-nth 0 (fn-rtc-grant n s)))))))))


(local (defthm fn-rtc-use-okp-grant-is-listener
  (implies (and (fn-rtc-use-okp u s) (equal (fn-rtc-get 0 u) :grant))
           (and (equal (fn-rtc-get 1 u) 0)
                (equal (fn-rtc-get 2 u) (fn-rtc-s-inc (fn-rtc-slot 0 s)))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-use-okp fn-rtc-usep fn-rtc-current-p)
              (fn-rtc-get fn-rtc-s-inc fn-rtc-s-status fn-rtc-nslots fn-rtc-slot fn-rtc-next-op))))))
(defthm fn-rtc-grant-event-listener
  (implies (and (fn-rtc-invp s) (fn-rtc-acts-on-p s e) (equal (fn-rtc-e-kind e) :grant))
           (and (equal (fn-rtc-e-id e) 0) (equal (fn-rtc-e-inc e) 0)))
  :hints (("Goal" :in-theory
           (union-theories (theory 'minimal-theory)
             '(fn-rtc-acts-on-p fn-rtc-hand-delivers-kind fn-rtc-invp-listener
               (:executable-counterpart fn-rtc-s-inc)))
           :use (fn-rtc-invp-is-core-and-admission
                 (:instance fn-rtc-core-invp-found-use (key (fn-rtc-key e)))
                 (:instance fn-rtc-matching-use-fields (uses (fn-rtc-uses s)))
                 (:instance fn-rtc-use-okp-grant-is-listener
                   (u (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s))))))))


(defthm fn-rtc-step-preserves-invp
  (implies (fn-rtc-invp s)
           (fn-rtc-invp (mv-nth 0 (fn-rtc-step s e q))))
  :hints (("Goal" :in-theory
 (union-theories (theory 'minimal-theory)
 '(fn-rtc-step-is-step-state fn-rtc-step-state fn-rtc-acts-on-p
   fn-rtc-accept-branch-establishes-invp fn-rtc-close-branch-establishes-invp
   fn-rtc-deliver-rearm-preserves-invp fn-rtc-deliver-rearm-after-end-use
   fn-rtc-end-use-rearm-preserves-invp
   fn-rtc-end-use-preserves-core-invp fn-rtc-end-use-keeps-free-slot fn-rtc-end-use-accept-subset
   fn-rtc-invp-grant-admission-safe fn-rtc-end-use-preserves-grant-admission
   fn-rtc-acting-instance-active-after-end-use fn-rtc-hand-target-active
   fn-rtc-slot-of-end-use-when-acting fn-rtc-end-use-removes-event-kind
   fn-rtc-grant-rearm-establishes-invp fn-rtc-grant-event-listener fn-rtc-accept-event-listener fn-rtc-hand-delivers-kind
   member-equal (:executable-counterpart member-equal) (:executable-counterpart equal)))
 :use (fn-rtc-invp-is-core-and-admission
       fn-rtc-end-use-preserves-core-invp fn-rtc-end-use-keeps-free-slot fn-rtc-end-use-accept-subset
   fn-rtc-invp-grant-admission-safe fn-rtc-end-use-preserves-grant-admission
       fn-rtc-acting-instance-active-after-end-use fn-rtc-hand-target-active
       fn-rtc-grant-rearm-establishes-invp fn-rtc-grant-event-listener fn-rtc-accept-event-listener fn-rtc-end-use-removes-event-kind
       (:instance fn-rtc-slot-of-end-use-when-acting (j (fn-rtc-e-id e)))))))
