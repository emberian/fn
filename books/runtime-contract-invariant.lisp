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

(defthm fn-rtc-use-okp-in-range
  (implies (and (fn-rtc-use-okp u s) (fn-rtc-handlep (fn-rtc-u-hd u))
                (member-eq (fn-rtc-get 0 u) *fn-rtc-in-kinds*))
           (and (<= (fn-rtc-h-off (fn-rtc-u-hd u))
                    (len (fn-rtc-b-bytes (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd u)) s))))
                (<= (+ (fn-rtc-h-off (fn-rtc-u-hd u)) (fn-rtc-h-len (fn-rtc-u-hd u)))
                    (fn-rtc-cap (fn-rtc-config s)))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-rtc-use-okp))))
  :rule-classes nil)
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
           (e/d (fn-rtc-buffer-okp fn-rtc-lease-return)
                (fn-rtc-lease-return-bytes-okp
                 fn-rtc-handlep fn-rtc-usep fn-rtc-holders fn-rtc-holds-p
                 fn-rtc-splice fn-cbor-octet-listp fn-rtc-delivered-outcome
                 fn-rtc-u-hd fn-rtc-h-buf fn-rtc-h-gen fn-rtc-h-off fn-rtc-h-len
                 fn-rtc-s-inc fn-rtc-s-status fn-rtc-nslots fn-rtc-cap
                 fn-rtc-invp-listener fn-rtc-core-invp-listener fn-rtc-invp-is-core-and-admission
                 fn-rtc-core-invp fn-rtc-uses-okp fn-rtc-pool-okp-unfolds
                 fn-rtc-get-out-of-range fn-rtc-buffer-out-of-range
                 fn-rtc-splice-length fn-rtc-splice-octets))
           :use (fn-rtc-lease-return-bytes-okp))))

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
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-rtc-use-okp)))))

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

(defthm fn-rtc-rearm-establishes-admission
  (implies (and (fn-rtc-core-invp s)
                (implies (fn-rtc-kind-out-p :accept 0 0 (fn-rtc-uses s))
                         (fn-rtc-free-slot 0 (fn-rtc-slots s))))
           (fn-rtc-invp (mv-nth 0 (fn-rtc-rearm s))))
  :hints (("Goal" :use (fn-rtc-core-invp-shape fn-rtc-core-invp-listener)
           :in-theory
           (e/d (fn-rtc-rearm)
                (fn-rtc-core-invp fn-rtc-kind-out-p fn-rtc-free-slot)))))

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
  (implies (and (fn-rtc-core-invp s) (fn-rtc-acts-on-p s e)
                (not (equal (fn-rtc-e-kind e) :accept)))
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
  (implies (and (fn-rtc-core-invp s) (fn-rtc-acts-on-p s e)
                (not (equal (fn-rtc-e-kind e) :accept)))
           (fn-rtc-instance-active-p (fn-rtc-e-id e) (fn-rtc-e-inc e) (fn-rtc-end-use s e)))
  :hints (("Goal" :in-theory
           (e/d (fn-rtc-slot)
                (fn-rtc-core-invp fn-rtc-find-use fn-rtc-key fn-rtc-completionp
                 fn-rtc-e-id fn-rtc-e-inc fn-rtc-e-kind fn-rtc-get fn-rtc-slots-is-slot
                 fn-rtc-s-inc fn-rtc-s-status fn-rtc-nslots fn-rtc-acting-instance-active
                 fn-rtc-slots-of-end-use-at-live-slot))
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

(defthm fn-rtc-accept-branch-establishes-invp
  (implies (and (fn-rtc-core-invp s1)
                (not (fn-rtc-kind-out-p :accept 0 0 (fn-rtc-uses s1))))
           (fn-rtc-invp (mv-nth 0 (fn-rtc-accept-branch s1 out q))))
  :hints (("Goal" :in-theory
           (e/d (fn-rtc-accept-branch)
                (mv-nth fn-rtc-core-invp fn-rtc-resource-invp fn-rtc-invp
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
                           (fn-rtc-holds-p fn-rtc-holds-iff-positive-holders
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

(defthm fn-rtc-kind-out-of-found-use
  (implies (fn-rtc-find-use key uses)
           (let ((u (fn-rtc-find-use key uses)))
             (fn-rtc-kind-out-p (fn-rtc-get 0 u) (fn-rtc-get 1 u) (fn-rtc-get 2 u) uses)))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use ((:instance fn-rtc-find-use-is-member (k key))
                 (:instance fn-rtc-kind-out-of-member (u (fn-rtc-find-use key uses)))))))

(defthm fn-rtc-kind-out-remove-matching
  (implies (and (fn-rtc-uses-okp uses s) (fn-rtc-find-use key uses))
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
  (implies (and (fn-rtc-core-invp s) (fn-rtc-completionp e)
                (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))
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
  (implies (fn-rtc-acts-on-p s e)
           (equal (fn-rtc-slots (fn-rtc-end-use s e)) (fn-rtc-slots s)))
  :hints (("Goal" :in-theory
           (disable fn-rtc-completionp fn-rtc-find-use fn-rtc-key fn-rtc-e-id fn-rtc-e-inc fn-rtc-e-kind
                    fn-rtc-s-inc fn-rtc-s-status))))

(defthm fn-rtc-slot-of-end-use-when-acting
  (implies (fn-rtc-acts-on-p s e)
           (equal (fn-rtc-slot j (fn-rtc-end-use s e)) (fn-rtc-slot j s)))
  :hints (("Goal" :in-theory (e/d (fn-rtc-slot) (fn-rtc-acts-on-p fn-rtc-slots-is-slot)))))

(defthm fn-rtc-ordinary-end-use-preserves-invp
  (implies (and (fn-rtc-invp s) (fn-rtc-acts-on-p s e)
                (not (equal (fn-rtc-e-kind e) :accept)))
           (fn-rtc-invp (fn-rtc-end-use s e)))
  :hints (("Goal" :in-theory
           (disable fn-rtc-invp fn-rtc-core-invp fn-rtc-acts-on-p fn-rtc-e-kind
                    fn-rtc-free-slot fn-rtc-kind-out-p fn-rtc-uses-of-end-use))))

(defthm fn-rtc-deliver-preserves-invp
  (implies (and (fn-rtc-invp s) (fn-rtc-instance-active-p id inc s))
           (fn-rtc-invp (mv-nth 0 (fn-rtc-deliver s id inc ev q))))
  :hints (("Goal" :in-theory
           (disable mv-nth fn-rtc-invp fn-rtc-core-invp fn-rtc-instance-active-p
                    fn-rtc-free-slot fn-rtc-kind-out-p))))

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
                 (:instance fn-rtc-rearm-establishes-admission (s (fn-rtc-end-use s e)))))))

(defthm fn-rtc-step-preserves-invp
  (implies (fn-rtc-invp s)
           (fn-rtc-invp (mv-nth 0 (fn-rtc-step s e q))))
  :hints (("Goal" :in-theory
           (union-theories (theory 'minimal-theory)
            '(fn-rtc-step-is-step-state fn-rtc-step-state fn-rtc-acts-on-p))
           :use (fn-rtc-invp-is-core-and-admission
                 fn-rtc-end-use-preserves-core-invp fn-rtc-end-use-rearm-preserves-invp
                 fn-rtc-ordinary-end-use-preserves-invp fn-rtc-acting-instance-active-after-end-use
                 fn-rtc-accept-event-listener fn-rtc-end-use-removes-event-kind
                 (:instance fn-rtc-slot-of-end-use-when-acting (j (fn-rtc-e-id e)))
                 (:instance fn-rtc-accept-branch-establishes-invp
                  (s1 (fn-rtc-end-use s e))
                  (out (fn-rtc-delivered-outcome (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)) e)))
                 (:instance fn-rtc-close-branch-preserves-invp
                  (s1 (fn-rtc-end-use s e)) (id (fn-rtc-e-id e)) (inc (fn-rtc-e-inc e)))
                 (:instance fn-rtc-deliver-preserves-invp
                  (s (fn-rtc-end-use s e)) (id (fn-rtc-e-id e)) (inc (fn-rtc-e-inc e))
                  (ev (list (fn-rtc-e-kind e)
                            (fn-rtc-delivered-outcome (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)) e))))))))
