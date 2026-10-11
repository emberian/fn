; fn: the host's landing of input into a leased buffer (runtime contract,
; RUNTIME-MODEL section 1; the executable pool of books/runtime-contract-pool).
;
; The executable layer's :in completion carries no data: the worker has
; already written the octets into the buffer's cells, by `fn-rtc-st-splice'
; at the handle's offset, while the buffer is :in-leased.  This book proves
; that this landing is sound for the contract:
;
;   fn-rtc-splice-keeps-invp           any splice keeps the invariant;
;   fn-rtc-landing-is-hidden           a splice into an :in-leased buffer
;                                      changes nothing but that buffer's
;                                      octets, so the pools agree off the
;                                      :in leases and every instance's
;                                      view is unchanged (T14);
;   fn-rtc-landed-is-what-the-host-landed
;                                      after the host splices DATA at an :in
;                                      use's handle, the completion the
;                                      contract sees (`fn-rtc-landed') carries
;                                      exactly DATA;
;   fn-rtc-x-step-after-landing        so the executable step on the landed
;                                      state is the contract's step on the
;                                      completion carrying DATA;
;   fn-rtc-landing-then-step-is-the-contract-step
;                                      and it is the contract's step on the
;                                      state BEFORE the landing: the host's
;                                      landing plus the executable step is
;                                      exactly the delivery of DATA.
;
; With A-HOST-LANDS (books/assumptions-runtime.lisp: DATA is the operation's
; own octets) the last is `fn-rtc-host-landing-is-the-contract-step'.

(in-package "ACL2")
(include-book "runtime-contract-exec-is")
(include-book "assumptions-runtime")
(include-book "runtime-contract-invariant")
(include-book "runtime-contract-isolation")

; The completion E with DATA as its data.
(defun fn-rtc-with-data (e data)
  (declare (xargs :guard t))
  (list (fn-rtc-get 0 e) (fn-rtc-get 1 e) (fn-rtc-get 2 e) (fn-rtc-get 3 e)
        (fn-rtc-get 4 e) data))

; -----------------------------------------------------------------------------
; Proofs.  The keystones are the non-local events; the invariant's frame
; lemmas for a buffer whose octets grow are local.

(local (defthm fn-rtc-in-use-on-has-holder
  (implies (and (fn-rtc-uses-okp uses s) (fn-rtc-in-use-on-p h uses))
           (< 0 (fn-rtc-holders h (fn-rtc-b-gen (fn-rtc-buffer h s)) uses)))
  :hints (("Goal" :induct (fn-rtc-uses-okp uses s)
           :in-theory (union-theories (theory 'minimal-theory)
            '(fn-rtc-uses-okp fn-rtc-in-use-on-p fn-rtc-holders fn-rtc-use-okp
              (:type-prescription fn-rtc-holders) (:executable-counterpart member-equal)))))))

(local (defthm fn-rtc-in-use-and-other-holder
  (implies (and (fn-rtc-uses-okp uses s) (fn-rtc-in-use-on-p h uses)
                (member-equal u uses)
                (not (member-eq (fn-rtc-get 0 u) *fn-rtc-in-kinds*))
                (fn-rtc-handlep (fn-rtc-u-hd u))
                (equal (fn-rtc-h-buf (fn-rtc-u-hd u)) h)
                (equal (fn-rtc-h-gen (fn-rtc-u-hd u)) (fn-rtc-b-gen (fn-rtc-buffer h s))))
           (< 1 (fn-rtc-holders h (fn-rtc-b-gen (fn-rtc-buffer h s)) uses)))
  :hints (("Goal" :induct (fn-rtc-uses-okp uses s)
           :in-theory (union-theories (theory 'minimal-theory)
            '(fn-rtc-uses-okp fn-rtc-in-use-on-p fn-rtc-holders fn-rtc-use-okp-lease member-equal
              fn-rtc-in-use-on-has-holder fn-rtc-member-holder-positive
              (:type-prescription fn-rtc-holders) (:executable-counterpart member-equal))))
          ("Subgoal *1/1" :use ((:instance fn-rtc-in-use-on-has-holder (uses (cdr uses)))
                                  (:instance fn-rtc-member-holder-positive (uses (cdr uses))))))))

(local (defthm fn-rtc-splice-target-excludes-pinned-use
  (implies (and (fn-rtc-use-okp u s) (member-equal u (fn-rtc-uses s))
                (fn-rtc-uses-okp (fn-rtc-uses s) s)
                (fn-rtc-splice-target-p h (fn-rtc-b-owner (fn-rtc-buffer h s)) (fn-rtc-uses s))
                (fn-rtc-handlep (fn-rtc-u-hd u))
                (equal (fn-rtc-h-buf (fn-rtc-u-hd u)) h))
           (not (member-eq (fn-rtc-get 0 u) '(:hand :pool))))
  :hints (("Goal" :use ((:instance fn-rtc-in-use-and-other-holder (uses (fn-rtc-uses s))))
           :in-theory (union-theories (theory 'minimal-theory)
            '(fn-rtc-use-okp fn-rtc-splice-target-p member-equal))))))

(local (defthm fn-rtc-use-okp-of-grown-buffer
  (implies (and (fn-rtc-use-okp u s) (natp h)
                (member-equal u (fn-rtc-uses s))
                (fn-rtc-uses-okp (fn-rtc-uses s) s)
                (fn-rtc-splice-target-p h (fn-rtc-b-owner (fn-rtc-buffer h s)) (fn-rtc-uses s))
                (equal (fn-rtc-b-gen b) (fn-rtc-b-gen (fn-rtc-buffer h s)))
                (equal (fn-rtc-b-owner b) (fn-rtc-b-owner (fn-rtc-buffer h s)))
                (<= (len (fn-rtc-b-bytes (fn-rtc-buffer h s))) (len (fn-rtc-b-bytes b))))
           (fn-rtc-use-okp u (fn-rtc-with-buffer h b s)))
  :hints (("Goal" :use fn-rtc-splice-target-excludes-pinned-use
           :in-theory
           (union-theories (theory 'minimal-theory)
            '(fn-rtc-use-okp fn-rtc-current-p fn-rtc-with-accessors fn-rtc-slot-of-with
              fn-rtc-buffer-of-with fn-rtc-next-op-of-with (:type-prescription fn-rtc-h-buf)
              member-equal nfix natp))))))

(local (defthm fn-rtc-uses-okp-of-grown-buffer
  (implies (and (fn-rtc-uses-okp uses s) (natp h)
                (subsetp-equal uses (fn-rtc-uses s))
                (fn-rtc-uses-okp (fn-rtc-uses s) s)
                (fn-rtc-splice-target-p h (fn-rtc-b-owner (fn-rtc-buffer h s)) (fn-rtc-uses s))
                (equal (fn-rtc-b-gen b) (fn-rtc-b-gen (fn-rtc-buffer h s)))
                (equal (fn-rtc-b-owner b) (fn-rtc-b-owner (fn-rtc-buffer h s)))
                (<= (len (fn-rtc-b-bytes (fn-rtc-buffer h s))) (len (fn-rtc-b-bytes b))))
           (fn-rtc-uses-okp uses (fn-rtc-with-buffer h b s)))
  :hints (("Goal" :induct (fn-rtc-uses-okp uses s)
           :in-theory (union-theories (theory 'minimal-theory)
                        '(fn-rtc-uses-okp fn-rtc-use-okp-of-grown-buffer subsetp-equal))))))

(local (defthm fn-rtc-core-invp-of-grown-buffer
  (implies (and (fn-rtc-core-invp s) (natp h) (< h (fn-rtc-nbufs (fn-rtc-config s)))
                (fn-rtc-splice-target-p h (fn-rtc-b-owner (fn-rtc-buffer h s)) (fn-rtc-uses s))
                (equal (fn-rtc-b-gen b) (fn-rtc-b-gen (fn-rtc-buffer h s)))
                (equal (fn-rtc-b-owner b) (fn-rtc-b-owner (fn-rtc-buffer h s)))
                (<= (len (fn-rtc-b-bytes (fn-rtc-buffer h s))) (len (fn-rtc-b-bytes b)))
                (fn-rtc-buffer-okp h b s))
           (fn-rtc-core-invp (fn-rtc-with-buffer h b s)))
  :hints (("Goal" :in-theory
           (disable fn-rtc-buf-cap fn-rtc-nbufs fn-rtc-nslots fn-rtc-nstatic fn-rtc-configp fn-rtc-slots-okp fn-rtc-pool-okp-unfolds
                    fn-rtc-uses-okp fn-rtc-mstates-okp fn-rtc-draining-okp
                    fn-rtc-get fn-rtc-leasedp fn-rtc-buffer-okp fn-rtc-splice-target-p)))))

(local (defthm fn-rtc-core-invp-bytes
  (implies (and (fn-rtc-core-invp s) (natp h) (< h (fn-rtc-nbufs (fn-rtc-config s))))
           (and (fn-cbor-octet-listp (fn-rtc-b-bytes (fn-rtc-buffer h s)))
                (true-listp (fn-rtc-b-bytes (fn-rtc-buffer h s)))
                (<= (len (fn-rtc-b-bytes (fn-rtc-buffer h s))) (fn-rtc-buf-cap h (fn-rtc-config s)))))
  :hints (("Goal" :use (fn-rtc-core-invp-buffer
                        (:instance fn-rtc-buffer-okp-local-bytes (b (fn-rtc-buffer h s))))
           :in-theory (union-theories (theory 'minimal-theory)
                        '(fn-cbor-octet-listp-implies-true-listp))))))

(local (defthm fn-rtc-octet-listp-true-listp
  (implies (fn-cbor-octet-listp x) (true-listp x))
  :rule-classes :forward-chaining))

(local (defthm fn-rtc-core-invp-buffer-fields
  (implies (and (fn-rtc-core-invp s) (natp h) (< h (fn-rtc-nbufs (fn-rtc-config s))))
           (and (equal (fn-rtc-get 0 (fn-rtc-buffer h s)) (fn-rtc-b-gen (fn-rtc-buffer h s)))
                (equal (fn-rtc-get 1 (fn-rtc-buffer h s)) (fn-rtc-b-owner (fn-rtc-buffer h s)))))
  :hints (("Goal" :use fn-rtc-core-invp-buffer
           :in-theory (e/d (fn-rtc-buffer-okp fn-rtc-bufferp fn-rtc-b-gen fn-rtc-b-owner)
                           (fn-rtc-core-invp fn-rtc-core-invp-buffer fn-rtc-ownerp fn-cbor-octet-listp
                            fn-rtc-holds-p fn-rtc-slot))))))

(local (defthm fn-rtc-st-splice-under-core-invp
  (implies (fn-rtc-core-invp st)
           (equal (fn-rtc-st-splice h off data st)
                  (if (fn-rtc-splice-okp h off data st)
                      (fn-rtc-with-buffer h (list (fn-rtc-b-gen (fn-rtc-buffer h st))
                                                  (fn-rtc-b-owner (fn-rtc-buffer h st))
                                                  (fn-rtc-splice (fn-rtc-b-bytes (fn-rtc-buffer h st)) off data))
                                          st)
                    st)))
  :hints (("Goal" :in-theory (e/d (fn-rtc-st-splice fn-rtc-st$a-splice fn-rtc-splice-okp)
                                  (fn-rtc-core-invp fn-rtc-splice fn-rtc-get fn-rtc-b-gen fn-rtc-b-owner fn-rtc-b-bytes
                                   fn-rtc-with-buffer fn-rtc-buffer))))))

(local (defun fn-rtc-splice-frame-ind (k i pool)
  (if (or (zp k) (atom pool)) (list k i pool)
    (fn-rtc-splice-frame-ind (- k 1) (+ 1 (nfix i)) (cdr pool)))))
(local (defthm fn-rtc-free-pool-buf-of-same-owner
  (implies (and (natp k) (< k (len pool))
                (equal (fn-rtc-b-owner b) (fn-rtc-b-owner (fn-rtc-get k pool))))
           (equal (fn-rtc-free-pool-buf i (fn-rtc-set k b pool) cfg)
                  (fn-rtc-free-pool-buf i pool cfg)))
  :hints (("Goal" :induct (fn-rtc-splice-frame-ind k i pool)
           :expand ((:free (x xs) (fn-rtc-free-pool-buf i (cons x xs) cfg)))
           :in-theory (union-theories (theory 'minimal-theory)
             '(car-cons cdr-cons fn-rtc-splice-frame-ind fn-rtc-free-pool-buf fn-rtc-set fn-rtc-get natp nfix zp len
               (:type-prescription len)))))))

(local (defthm fn-rtc-splice-keeps-core-invp
  (implies (fn-rtc-core-invp st)
           (fn-rtc-core-invp (fn-rtc-st-splice h off data st)))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
       '(fn-rtc-st-splice-under-core-invp fn-rtc-splice-okp fn-rtc-buffer-accessors
         fn-cbor-octet-listp-implies-true-listp max nfix natp (:type-prescription len) (:type-prescription fn-rtc-b-gen)))
     :use ((:instance fn-rtc-core-invp-of-grown-buffer (s st)
             (b (list (fn-rtc-b-gen (fn-rtc-buffer h st)) (fn-rtc-b-owner (fn-rtc-buffer h st))
                      (fn-rtc-splice (fn-rtc-b-bytes (fn-rtc-buffer h st)) off data))))
           (:instance fn-rtc-core-invp-bytes (s st))
           (:instance fn-rtc-core-invp-buffer (s st))
           (:instance fn-rtc-splice-length (bytes (fn-rtc-b-bytes (fn-rtc-buffer h st))))
           (:instance fn-rtc-splice-octets (bytes (fn-rtc-b-bytes (fn-rtc-buffer h st))))
           (:instance fn-rtc-buffer-okp-change-bytes (s st) (b (fn-rtc-buffer h st))
             (bytes (fn-rtc-splice (fn-rtc-b-bytes (fn-rtc-buffer h st)) off data))))))))

(local (defthm fn-rtc-splice-keeps-free-pool-buf
  (implies (fn-rtc-core-invp st)
           (equal (fn-rtc-free-pool-buf 0 (fn-rtc-pool (fn-rtc-st-splice h off data st)) (fn-rtc-config st))
                  (fn-rtc-free-pool-buf 0 (fn-rtc-pool st) (fn-rtc-config st))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
       '(fn-rtc-st-splice-under-core-invp fn-rtc-splice-okp fn-rtc-buffer-accessors
         fn-rtc-with-accessors fn-rtc-buffer nfix natp))
     :use ((:instance fn-rtc-core-invp-shape (s st))
           (:instance fn-rtc-free-pool-buf-of-same-owner
             (i 0) (k h) (pool (fn-rtc-pool st)) (cfg (fn-rtc-config st))
             (b (list (fn-rtc-b-gen (fn-rtc-buffer h st)) (fn-rtc-b-owner (fn-rtc-buffer h st))
                      (fn-rtc-splice (fn-rtc-b-bytes (fn-rtc-buffer h st)) off data)))))))))

(local (defthm fn-rtc-uses-of-st-splice
  (equal (fn-rtc-uses (fn-rtc-st-splice h off data st)) (fn-rtc-uses st))
  :hints (("Goal" :in-theory (e/d (fn-rtc-st-splice fn-rtc-st$a-splice) (fn-rtc-splice-okp fn-rtc-splice))))))

(local (defthm fn-rtc-st-splice-tables
  (and (equal (fn-rtc-config (fn-rtc-st-splice h off data st)) (fn-rtc-config st))
       (equal (fn-rtc-slots (fn-rtc-st-splice h off data st)) (fn-rtc-slots st))
       (equal (fn-rtc-mstates (fn-rtc-st-splice h off data st)) (fn-rtc-mstates st))
       (equal (fn-rtc-next-op (fn-rtc-st-splice h off data st)) (fn-rtc-next-op st)))
  :hints (("Goal" :in-theory (e/d (fn-rtc-st-splice fn-rtc-st$a-splice) (fn-rtc-splice-okp fn-rtc-splice
                                                                          fn-rtc-st-splice-under-core-invp))))))

(defthm fn-rtc-splice-keeps-invp
  (implies (fn-rtc-invp st)
           (fn-rtc-invp (fn-rtc-st-splice h off data st)))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
    '(fn-rtc-invp-is-core-and-admission fn-rtc-splice-keeps-core-invp
      fn-rtc-splice-keeps-free-pool-buf fn-rtc-st-splice-tables fn-rtc-uses-of-st-splice)))))

(local (defthm fn-rtc-pools-agree-of-set-in-leased
  (implies (and (natp h)
                (eq (fn-rtc-get 0 (fn-rtc-b-owner (fn-rtc-get h pool))) :leased)
                (eq (fn-rtc-get 3 (fn-rtc-b-owner (fn-rtc-get h pool))) :in)
                (equal (fn-rtc-get 0 b) (fn-rtc-get 0 (fn-rtc-get h pool)))
                (equal (fn-rtc-get 1 b) (fn-rtc-get 1 (fn-rtc-get h pool))))
           (fn-rtc-pools-agree-off-in-leases-p pool (fn-rtc-set h b pool)))
  :hints (("Goal" :induct (fn-rtc-set h b pool)
           :in-theory (enable fn-rtc-b-gen fn-rtc-b-owner)))))

(local (defthm fn-rtc-pools-agree-refl
  (fn-rtc-pools-agree-off-in-leases-p pool pool)))

(local (defthm fn-rtc-pools-agree-of-with-in-leased
  (implies (and (natp h) (fn-rtc-in-leased-p h st)
                (equal (fn-rtc-get 0 b) (fn-rtc-get 0 (fn-rtc-buffer h st)))
                (equal (fn-rtc-get 1 b) (fn-rtc-get 1 (fn-rtc-buffer h st))))
           (fn-rtc-pools-agree-off-in-leases-p (fn-rtc-pool st) (fn-rtc-pool (fn-rtc-with-buffer h b st))))
  :hints (("Goal" :in-theory (e/d (fn-rtc-in-leased-p fn-rtc-b-owner)
                                  (fn-rtc-pools-agree-off-in-leases-p fn-rtc-get))
           :use ((:instance fn-rtc-pools-agree-of-set-in-leased (pool (fn-rtc-pool st))))))))

(defthm fn-rtc-landing-is-hidden
  (implies (fn-rtc-in-leased-p h st)
           (let ((st2 (fn-rtc-st-splice h off data st)))
             (and (equal (fn-rtc-config st2) (fn-rtc-config st))
                  (equal (fn-rtc-slots st2) (fn-rtc-slots st))
                  (equal (fn-rtc-uses st2) (fn-rtc-uses st))
                  (equal (fn-rtc-mstates st2) (fn-rtc-mstates st))
                  (equal (fn-rtc-next-op st2) (fn-rtc-next-op st))
                  (fn-rtc-pools-agree-off-in-leases-p (fn-rtc-pool st) (fn-rtc-pool st2)))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
              '(fn-rtc-st-splice fn-rtc-st$a-splice fn-rtc-splice-okp fn-rtc-in-leased-p fn-rtc-b-owner fn-rtc-b-bytes
                fn-rtc-next-op-of-with fn-rtc-with-accessors fn-rtc-buffer fn-rtc-pools-agree-refl fn-rtc-get-of-cons
                natp nfix zp))
           :use ((:instance fn-rtc-pools-agree-of-set-in-leased (pool (fn-rtc-pool st))
                  (b (list (fn-rtc-get 0 (fn-rtc-buffer h st)) (fn-rtc-get 1 (fn-rtc-buffer h st))
                           (fn-rtc-splice (fn-rtc-get 2 (fn-rtc-buffer h st)) off data))))))))

(defthm fn-rtc-landing-keeps-every-view
  (implies (fn-rtc-in-leased-p h st)
           (equal (fn-rtc-view id inc (fn-rtc-st-splice h off data st))
                  (fn-rtc-view id inc st)))
  :hints (("Goal" :use (fn-rtc-landing-is-hidden
                        (:instance fn-rtc-view-hides-in-leased-bytes
                          (s1 st) (s2 (fn-rtc-st-splice h off data st))))
           :in-theory (theory 'minimal-theory))))

(local (defthm fn-rtc-use-okp-in-facts
  (implies (and (fn-rtc-use-okp u s) (member-eq (fn-rtc-get 0 u) *fn-rtc-in-kinds*))
           (and (fn-rtc-handlep (fn-rtc-u-hd u))
                (<= (fn-rtc-h-off (fn-rtc-u-hd u)) (len (fn-rtc-bytes (fn-rtc-h-buf (fn-rtc-u-hd u)) s)))
                (<= (+ (fn-rtc-h-off (fn-rtc-u-hd u)) (fn-rtc-h-len (fn-rtc-u-hd u)))
                    (fn-rtc-buf-cap (fn-rtc-h-buf (fn-rtc-u-hd u)) (fn-rtc-config s)))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
             '(fn-rtc-use-okp fn-rtc-usep fn-rtc-u-hd fn-rtc-bytes member-equal))))))

(local (defthm fn-rtc-core-invp-pool-len
  (implies (fn-rtc-core-invp s) (equal (len (fn-rtc-pool s)) (fn-rtc-nbufs (fn-rtc-config s))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-rtc-core-invp))))))

(local (defthm fn-rtc-bytes-of-st-splice
  (implies (and (fn-rtc-core-invp st) (fn-rtc-splice-okp h off data st))
           (equal (fn-rtc-bytes h (fn-rtc-st-splice h off data st))
                  (fn-rtc-splice (fn-rtc-bytes h st) off data)))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                                             '(fn-rtc-bytes fn-rtc-core-invp-pool-len fn-rtc-st-splice-under-core-invp fn-rtc-buffer-of-with
                                               fn-rtc-buffer-accessors fn-rtc-splice-okp fn-rtc-with-accessors
                                               natp nfix (:executable-counterpart tau-system) (:type-prescription len)))))))

(local (defthm fn-rtc-l-nthcdr-of-append-len
  (implies (equal n (len a)) (equal (nthcdr n (append a b)) b))))

(local (defthm fn-rtc-l-take-of-append-len
  (implies (and (equal n (len a)) (true-listp a)) (equal (take n (append a b)) a))))

(local (defthm fn-rtc-l-len-take-min
  (implies (and (natp k) (<= k (len x))) (equal (len (take k x)) k))))

(local (defthm fn-rtc-take-nthcdr-of-splice
  (implies (and (true-listp bytes) (true-listp data) (natp off) (<= off (len bytes)))
           (equal (take (len data) (nthcdr off (fn-rtc-splice bytes off data))) data))
  :hints (("Goal" :in-theory (e/d (fn-rtc-splice) (take nthcdr))
           :use ((:instance fn-rtc-l-nthcdr-of-append-len (n off) (a (take off bytes))
                  (b (append data (nthcdr (+ off (len data)) bytes)))))))))

(local (defthm fn-rtc-core-invp-bytes-true-listp
  (implies (and (fn-rtc-core-invp s) (natp h) (< h (fn-rtc-nbufs (fn-rtc-config s))))
           (true-listp (fn-rtc-bytes h s)))
  :hints (("Goal" :in-theory (e/d (fn-rtc-bytes) (fn-rtc-core-invp fn-rtc-core-invp-bytes fn-cbor-octet-listp))
           :use fn-rtc-core-invp-bytes))))

(local (defthm fn-rtc-landed-octets-of-st-splice
  (implies (and (fn-rtc-core-invp st) (natp h) (< h (fn-rtc-nbufs (fn-rtc-config st)))
                (fn-rtc-splice-target-p h (fn-rtc-b-owner (fn-rtc-buffer h st)) (fn-rtc-uses st))
                (natp off) (<= off (len (fn-rtc-bytes h st)))
                (fn-cbor-octet-listp data)
                (<= (+ off (len data)) (fn-rtc-buf-cap h (fn-rtc-config st))))
           (equal (take (len data) (nthcdr off (fn-rtc-bytes h (fn-rtc-st-splice h off data st))))
                  data))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                   '(fn-rtc-splice-okp fn-rtc-bytes fn-cbor-octet-listp-implies-true-listp))
           :use ((:instance fn-rtc-core-invp-bytes-true-listp (s st))
                 (:instance fn-rtc-bytes-of-st-splice)
                 (:instance fn-rtc-take-nthcdr-of-splice (bytes (fn-rtc-bytes h st))))
           :do-not-induct t))))

(local (defthm fn-rtc-in-use-on-of-member
  (implies (and (member-equal u uses)
                (member-eq (fn-rtc-get 0 u) *fn-rtc-in-kinds*)
                (fn-rtc-handlep (fn-rtc-u-hd u)))
           (fn-rtc-in-use-on-p (fn-rtc-h-buf (fn-rtc-u-hd u)) uses))
  :hints (("Goal" :induct (member-equal u uses)
           :in-theory (union-theories (theory 'minimal-theory)
               '(fn-rtc-in-use-on-p member-equal car-cons cdr-cons))))))

(defthm fn-rtc-landed-is-what-the-host-landed
  (implies (and (fn-rtc-invp st)
                (fn-rtc-completionp e)
                (equal u (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses st)))
                u
                (member-eq (fn-rtc-get 0 u) *fn-rtc-in-kinds*)
                (member-eq (fn-rtc-get 0 (fn-rtc-e-outcome e)) '(:done :short))
                (equal (fn-rtc-get 1 (fn-rtc-e-outcome e)) (len data))
                (<= (len data) (fn-rtc-h-len (fn-rtc-u-hd u)))
                (fn-cbor-octet-listp data))
           (equal (fn-rtc-landed e (fn-rtc-st-splice (fn-rtc-h-buf (fn-rtc-u-hd u))
                                                     (fn-rtc-h-off (fn-rtc-u-hd u))
                                                     data st))
                  (fn-rtc-with-data e data)))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
               '(fn-rtc-landed fn-rtc-with-data fn-rtc-invp-is-core-and-admission
                 fn-rtc-e-outcome fn-rtc-splice-target-p fn-rtc-uses-of-st-splice
                 fn-rtc-bytes nfix natp member-equal fn-rtc-get-of-cons
                 (:type-prescription len) (:type-prescription fn-rtc-h-buf)
                 (:type-prescription fn-rtc-h-off) (:type-prescription fn-rtc-h-len)))
           :use ((:instance fn-rtc-find-use-is-member (k (fn-rtc-key e)) (uses (fn-rtc-uses st)))
                 (:instance fn-rtc-in-use-on-of-member (uses (fn-rtc-uses st)))
                 (:instance fn-rtc-core-invp-found-use (s st) (key (fn-rtc-key e)))
                 (:instance fn-rtc-use-okp-buffer-index (s st))
                 (:instance fn-rtc-use-okp-in-facts (s st))
                 (:instance fn-rtc-landed-octets-of-st-splice
                            (h (fn-rtc-h-buf (fn-rtc-u-hd u))) (off (fn-rtc-h-off (fn-rtc-u-hd u))))))))

(local (defthm fn-rtc-pool-okp-implies-pool-shapep
  (implies (and (natp i) (fn-rtc-pool-okp i pool s))
           (fn-rtc-pool-shapep i pool (fn-rtc-config s)))
  :hints (("Goal" :induct (fn-rtc-pool-okp i pool s)
           :expand ((fn-rtc-pool-okp i pool s) (fn-rtc-pool-shapep i pool (fn-rtc-config s)))
           :in-theory (union-theories (theory 'minimal-theory)
              '(fn-rtc-buffer-okp fn-rtc-bufferp fn-rtc-pool-okp fn-rtc-pool-shapep
                fn-rtc-b-gen fn-rtc-b-owner fn-rtc-b-bytes fn-rtc-get nfix natp zp
                car-cons cdr-cons fn-cbor-octet-listp-implies-true-listp))))))

(local (defthm fn-rtc-slots-okp-true-listp
  (implies (fn-rtc-slots-okp i slots) (true-listp slots))
  :hints (("Goal" :in-theory (disable fn-rtc-slotp)))))

(defthm fn-rtc-invp-implies-st-p
  (implies (fn-rtc-invp s) (fn-rtc-st-p s))
  :hints (("Goal" :in-theory (e/d (fn-rtc-st-p-is-shapep fn-rtc-shapep)
                                  (fn-rtc-pool-okp fn-rtc-uses-okp fn-rtc-slots-okp fn-rtc-mstates-okp
                                   fn-rtc-draining-okp fn-rtc-free-slot fn-rtc-kind-out-p fn-rtc-pool-shapep
                                   fn-rtc-invp-is-core-and-admission fn-rtc-pool-okp-implies-pool-shapep))
           :use ((:instance fn-rtc-pool-okp-implies-pool-shapep (i 0) (pool (fn-rtc-pool s)))))))

(defthm fn-rtc-x-step-after-landing
  (implies (and (fn-rtc-invp st)
                (fn-rtc-completionp e)
                (equal u (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses st)))
                u
                (member-eq (fn-rtc-get 0 u) *fn-rtc-in-kinds*)
                (member-eq (fn-rtc-get 0 (fn-rtc-e-outcome e)) '(:done :short))
                (equal (fn-rtc-get 1 (fn-rtc-e-outcome e)) (len data))
                (<= (len data) (fn-rtc-h-len (fn-rtc-u-hd u)))
                (fn-cbor-octet-listp data))
           (let ((st2 (fn-rtc-st-splice (fn-rtc-h-buf (fn-rtc-u-hd u))
                                        (fn-rtc-h-off (fn-rtc-u-hd u))
                                        data st)))
             (equal (fn-rtc-x-step* e q st2)
                    (fn-rtc-step* st2 (fn-rtc-with-data e data) q))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                                             '(fn-rtc-x-step*-is fn-rtc-splice-keeps-invp fn-rtc-invp-implies-st-p
                                               fn-rtc-landed-is-what-the-host-landed)))))

(local (defthm fn-rtc-completion-count-natp
  (implies (and (fn-rtc-completionp e)
                (member-eq (fn-rtc-get 0 (fn-rtc-e-outcome e)) '(:done :short)))
           (natp (fn-rtc-get 1 (fn-rtc-e-outcome e))))
  :hints (("Goal" :in-theory (enable fn-rtc-completionp fn-rtc-outcomep fn-rtc-e-outcome)))))

(local (defthm fn-rtc-use-okp-in-holders
  (implies (and (fn-rtc-use-okp u s) (member-eq (fn-rtc-get 0 u) *fn-rtc-in-kinds*))
           (equal (fn-rtc-holders (fn-rtc-h-buf (fn-rtc-u-hd u)) (fn-rtc-h-gen (fn-rtc-u-hd u)) (fn-rtc-uses s))
                  1))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
             '(fn-rtc-use-okp fn-rtc-usep fn-rtc-u-hd fn-rtc-bytes member-equal))))))

(defthm fn-rtc-splice-idempotent
  (implies (and (true-listp bytes) (true-listp data) (natp off) (<= off (len bytes)))
           (equal (fn-rtc-splice (fn-rtc-splice bytes off data) off data)
                  (fn-rtc-splice bytes off data)))
  :hints (("Goal" :in-theory (enable fn-rtc-splice))))

(local (defthm fn-rtc-holders-of-remove-found
  (implies (and (equal u (fn-rtc-find-use key uses)) u)
           (equal (fn-rtc-holders h g (fn-rtc-remove-use key uses))
                  (- (fn-rtc-holders h g uses)
                     (if (and (fn-rtc-handlep (fn-rtc-u-hd u))
                              (equal (fn-rtc-h-buf (fn-rtc-u-hd u)) h)
                              (equal (fn-rtc-h-gen (fn-rtc-u-hd u)) g))
                         1 0))))
  :hints (("Goal" :induct (fn-rtc-remove-use key uses)
           :in-theory (disable fn-rtc-key fn-rtc-handlep fn-rtc-h-buf fn-rtc-h-gen)))))

; The :in use E completes holds its buffer alone, so its removal ends the lease.
(local (defthm fn-rtc-in-lease-ends-on-its-completion
  (implies (and (fn-rtc-invp st)
                (equal u (fn-rtc-find-use key (fn-rtc-uses st))) u
                (member-eq (fn-rtc-get 0 u) *fn-rtc-in-kinds*))
           (not (fn-rtc-holds-p (fn-rtc-h-buf (fn-rtc-u-hd u)) (fn-rtc-h-gen (fn-rtc-u-hd u))
                                (fn-rtc-remove-use key (fn-rtc-uses st)))))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
              '(fn-rtc-invp-is-core-and-admission fn-rtc-holds-iff-positive-holders
                fn-rtc-holders-of-remove-found))
           :use ((:instance fn-rtc-core-invp-found-use (s st))
                 (:instance fn-rtc-use-okp-in-facts (s st))
                 (:instance fn-rtc-use-okp-in-holders (s st)))))))

(local (defthm fn-rtc-with-buffer-twice
  (equal (fn-rtc-with-buffer h b2 (fn-rtc-with-uses uses (fn-rtc-with-buffer h b1 s)))
         (fn-rtc-with-buffer h b2 (fn-rtc-with-uses uses s)))
  :hints (("Goal" :in-theory (enable fn-rtc-with-buffer fn-rtc-with-uses)))))

(local (defthm fn-rtc-lease-return-of-landed-bytes
  (implies (and (true-listp bytes) (true-listp (fn-rtc-e-data e)) (natp (fn-rtc-h-off (fn-rtc-u-hd u)))
                (<= (fn-rtc-h-off (fn-rtc-u-hd u)) (len bytes))
                (member-eq (fn-rtc-get 0 u) *fn-rtc-in-kinds*)
                (member-eq (fn-rtc-get 0 (fn-rtc-delivered-outcome u e)) '(:done :short)))
           (equal (fn-rtc-lease-return u e (list g o (fn-rtc-splice bytes (fn-rtc-h-off (fn-rtc-u-hd u))
                                                                   (fn-rtc-e-data e)))
                                       s)
                  (fn-rtc-lease-return u e (list g o bytes) s)))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                                             '(fn-rtc-lease-return fn-rtc-splice-idempotent fn-rtc-buffer-accessors))))))

(local (defthm fn-rtc-octets-n-p-of-len
  (implies (fn-cbor-octet-listp data) (fn-rtc-octets-n-p data (len data)))))

(local (defthm fn-rtc-with-data-fields
  (and (equal (fn-rtc-key (fn-rtc-with-data e data)) (fn-rtc-key e))
       (equal (fn-rtc-e-data (fn-rtc-with-data e data)) data)
       (equal (fn-rtc-e-outcome (fn-rtc-with-data e data)) (fn-rtc-e-outcome e))
       (equal (fn-rtc-e-id (fn-rtc-with-data e data)) (fn-rtc-e-id e))
       (equal (fn-rtc-e-inc (fn-rtc-with-data e data)) (fn-rtc-e-inc e))
       (equal (fn-rtc-e-kind (fn-rtc-with-data e data)) (fn-rtc-e-kind e))
       (implies (fn-rtc-completionp e) (fn-rtc-completionp (fn-rtc-with-data e data))))
  :hints (("Goal" :in-theory (enable fn-rtc-with-data fn-rtc-key fn-rtc-completionp)))))

(local (defthm fn-rtc-delivered-outcome-of-with-data
  (implies (and (member-eq (fn-rtc-get 0 u) *fn-rtc-in-kinds*)
                (member-eq (fn-rtc-get 0 (fn-rtc-e-outcome e)) '(:done :short))
                (equal (fn-rtc-get 1 (fn-rtc-e-outcome e)) (len data))
                (<= (len data) (fn-rtc-h-len (fn-rtc-u-hd u)))
                (fn-cbor-octet-listp data))
           (equal (fn-rtc-delivered-outcome u (fn-rtc-with-data e data)) (fn-rtc-e-outcome e)))
  :hints (("Goal" :in-theory (e/d (fn-rtc-delivered-outcome) (fn-rtc-octets-n-p fn-cbor-octet-listp fn-rtc-with-data))))))

(local (defthm fn-rtc-buffer-is-its-fields
  (implies (and (fn-rtc-core-invp st) (natp h) (< h (fn-rtc-nbufs (fn-rtc-config st))))
           (equal (list (fn-rtc-b-gen (fn-rtc-buffer h st)) (fn-rtc-b-owner (fn-rtc-buffer h st))
                        (fn-rtc-b-bytes (fn-rtc-buffer h st)))
                  (fn-rtc-buffer h st)))
  :hints (("Goal" :use (fn-rtc-core-invp-buffer-fields
                        (:instance fn-rtc-core-invp-buffer (s st)))
           :in-theory (e/d (fn-rtc-buffer-okp fn-rtc-bufferp fn-rtc-b-bytes fn-rtc-b-gen fn-rtc-b-owner)
                           (fn-rtc-buf-cap fn-rtc-holds-iff-positive-holders fn-rtc-core-invp fn-rtc-core-invp-buffer-fields fn-rtc-core-invp-buffer
                            fn-rtc-ownerp fn-cbor-octet-listp fn-rtc-holds-p fn-rtc-slot fn-rtc-buffer))
           :expand ((len (fn-rtc-buffer h st)) (len (cdr (fn-rtc-buffer h st)))
                    (len (cddr (fn-rtc-buffer h st))) (len (cdddr (fn-rtc-buffer h st))))))))

(local (defthm fn-rtc-lease-return-reads-slots-only
  (equal (fn-rtc-lease-return u e b (fn-rtc-with-uses r (fn-rtc-with-buffer h b2 s)))
         (fn-rtc-lease-return u e b (fn-rtc-with-uses r s)))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                                             '(fn-rtc-lease-return fn-rtc-current-p fn-rtc-slot-of-with fn-rtc-handed-to-live-p fn-rtc-live-p))))))

; End-use after a buffer's octets changed, when the completing use's lease on
; that buffer ends: the lease return's octets decide.
(local (defthm fn-rtc-end-use-of-rebytes
  (implies (and (fn-rtc-completionp e)
                (equal u (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s))) u
                (fn-rtc-handlep (fn-rtc-u-hd u))
                (equal h (fn-rtc-h-buf (fn-rtc-u-hd u)))
                (not (fn-rtc-holds-p h (fn-rtc-h-gen (fn-rtc-u-hd u))
                                     (fn-rtc-remove-use (fn-rtc-key e) (fn-rtc-uses s))))
                (natp h) (< h (len (fn-rtc-pool s)))
                (equal (fn-rtc-lease-return u e b2 (fn-rtc-with-uses (fn-rtc-remove-use (fn-rtc-key e) (fn-rtc-uses s)) s))
                       (fn-rtc-lease-return u e (fn-rtc-buffer h s)
                                            (fn-rtc-with-uses (fn-rtc-remove-use (fn-rtc-key e) (fn-rtc-uses s)) s))))
           (equal (fn-rtc-end-use (fn-rtc-with-buffer h b2 s) e)
                  (fn-rtc-end-use s e)))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
             '(fn-rtc-end-use fn-rtc-end-lease fn-rtc-lease-return-reads-slots-only
               fn-rtc-with-accessors fn-rtc-buffer-of-with fn-rtc-with-buffer-twice
               nfix natp))))))

(local (defthm fn-rtc-end-use-of-landing
  (implies (and (fn-rtc-invp st)
                (fn-rtc-completionp e)
                (equal u (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses st)))
                u
                (member-eq (fn-rtc-get 0 u) *fn-rtc-in-kinds*)
                (member-eq (fn-rtc-get 0 (fn-rtc-e-outcome e)) '(:done :short))
                (equal (fn-rtc-get 1 (fn-rtc-e-outcome e)) (len data))
                (<= (len data) (fn-rtc-h-len (fn-rtc-u-hd u)))
                (fn-cbor-octet-listp data))
           (equal (fn-rtc-end-use (fn-rtc-st-splice (fn-rtc-h-buf (fn-rtc-u-hd u))
                                                    (fn-rtc-h-off (fn-rtc-u-hd u)) data st)
                                  (fn-rtc-with-data e data))
                  (fn-rtc-end-use st (fn-rtc-with-data e data))))
  :hints (("Goal"
           :use ((:instance fn-rtc-core-invp-found-use (s st) (key (fn-rtc-key e)))
                 (:instance fn-rtc-use-okp-buffer-index (s st))
                 (:instance fn-rtc-use-okp-in-facts (s st))
                 (:instance fn-rtc-in-lease-ends-on-its-completion (key (fn-rtc-key e)))
                 (:instance fn-rtc-core-invp-bytes (s st) (h (fn-rtc-h-buf (fn-rtc-u-hd u))))
                 (:instance fn-rtc-core-invp-pool-len (s st))
                 (:instance fn-rtc-buffer-is-its-fields (h (fn-rtc-h-buf (fn-rtc-u-hd u))))
                 (:instance fn-rtc-st-splice-under-core-invp (h (fn-rtc-h-buf (fn-rtc-u-hd u)))
                            (off (fn-rtc-h-off (fn-rtc-u-hd u))))
                 (:instance fn-rtc-lease-return-of-landed-bytes (e (fn-rtc-with-data e data))
                            (bytes (fn-rtc-b-bytes (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd u)) st)))
                            (g (fn-rtc-b-gen (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd u)) st)))
                            (o (fn-rtc-b-owner (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd u)) st)))
                            (s (fn-rtc-with-uses (fn-rtc-remove-use (fn-rtc-key e) (fn-rtc-uses st)) st)))
                 (:instance fn-rtc-end-use-of-rebytes (s st) (e (fn-rtc-with-data e data))
                            (h (fn-rtc-h-buf (fn-rtc-u-hd u)))
                            (b2 (list (fn-rtc-b-gen (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd u)) st))
                                      (fn-rtc-b-owner (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd u)) st))
                                      (fn-rtc-splice (fn-rtc-b-bytes (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd u)) st))
                                                     (fn-rtc-h-off (fn-rtc-u-hd u)) data)))))
           :in-theory (union-theories (theory 'minimal-theory)
                                      '(fn-rtc-invp-is-core-and-admission fn-rtc-with-data-fields
                                        fn-rtc-delivered-outcome-of-with-data fn-rtc-splice-okp fn-rtc-bytes
                                        fn-rtc-octet-listp-true-listp natp (:type-prescription len)
                                        (:type-prescription fn-rtc-h-off) (:type-prescription fn-rtc-h-buf)
                                        (:type-prescription fn-rtc-h-len) (:executable-counterpart tau-system)))))))

(local (defthm fn-rtc-slot-of-st-splice
  (equal (fn-rtc-slot id (fn-rtc-st-splice h off data st)) (fn-rtc-slot id st))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-rtc-slot fn-rtc-st-splice-tables))))))

(local (defthm fn-rtc-owner-of-st-splice
  (equal (fn-rtc-b-owner (fn-rtc-buffer k (fn-rtc-st-splice h off data st)))
         (fn-rtc-b-owner (fn-rtc-buffer k st)))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
               '(fn-rtc-st-splice fn-rtc-st$a-splice fn-rtc-buffer-of-with fn-rtc-buffer-of-non-natp fn-rtc-splice-okp
                 fn-rtc-b-owner fn-rtc-get-of-cons nfix natp zp))))))

(local (defthm fn-rtc-acts-on-p-of-st-splice
  (equal (fn-rtc-acts-on-p (fn-rtc-st-splice h off data st) e) (fn-rtc-acts-on-p st e))
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory)
                                             '(fn-rtc-acts-on-p fn-rtc-hand-delivers-p fn-rtc-handed-to-live-p fn-rtc-live-p
                                               fn-rtc-owner-of-st-splice fn-rtc-slot-of-st-splice fn-rtc-uses-of-st-splice))))))

(local (defthm fn-rtc-step*-of-landing
  (implies (and (fn-rtc-invp st)
                (fn-rtc-completionp e)
                (equal u (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses st)))
                u
                (member-eq (fn-rtc-get 0 u) *fn-rtc-in-kinds*)
                (member-eq (fn-rtc-get 0 (fn-rtc-e-outcome e)) '(:done :short))
                (equal (fn-rtc-get 1 (fn-rtc-e-outcome e)) (len data))
                (<= (len data) (fn-rtc-h-len (fn-rtc-u-hd u)))
                (fn-cbor-octet-listp data))
           (equal (fn-rtc-step* (fn-rtc-st-splice (fn-rtc-h-buf (fn-rtc-u-hd u))
                                                  (fn-rtc-h-off (fn-rtc-u-hd u))
                                                  data st)
                                (fn-rtc-with-data e data) q)
                  (fn-rtc-step* st (fn-rtc-with-data e data) q)))
  :hints (("Goal" :use ((:instance fn-rtc-kind-of-find-use (k (fn-rtc-key e)) (uses (fn-rtc-uses st)))
                               (:instance fn-rtc-key-of-find-use (k (fn-rtc-key e)) (uses (fn-rtc-uses st))))
           :expand ((:free (s) (fn-rtc-step* s (fn-rtc-with-data e data) q)))
           :in-theory (union-theories (theory 'minimal-theory)
                                      '(fn-rtc-end-use-of-landing fn-rtc-acts-on-p-of-st-splice
                                        fn-rtc-with-data-fields fn-rtc-hand-delivers-p fn-rtc-key fn-rtc-e-kind
                                        member-equal car-cons cdr-cons
                                        fn-rtc-uses-of-st-splice fn-rtc-st-splice-tables))))))

; L5. The pre-landing refinement: the executable step after the host lands
; DATA at the :in use's handle is the contract's step, on the state BEFORE the
; landing, of the completion carrying DATA -- whether or not the completion
; acts on a live instance (the lease returns the landed octets either way).
(defthm fn-rtc-landing-then-step-is-the-contract-step
  (implies (and (fn-rtc-invp st)
                (fn-rtc-completionp e)
                (equal u (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses st)))
                u
                (member-eq (fn-rtc-get 0 u) *fn-rtc-in-kinds*)
                (member-eq (fn-rtc-get 0 (fn-rtc-e-outcome e)) '(:done :short))
                (equal (fn-rtc-get 1 (fn-rtc-e-outcome e)) (len data))
                (<= (len data) (fn-rtc-h-len (fn-rtc-u-hd u)))
                (fn-cbor-octet-listp data))
           (equal (fn-rtc-x-step* e q (fn-rtc-st-splice (fn-rtc-h-buf (fn-rtc-u-hd u))
                                                        (fn-rtc-h-off (fn-rtc-u-hd u))
                                                        data st))
                  (fn-rtc-step* st (fn-rtc-with-data e data) q)))
  :hints (("Goal" :use (fn-rtc-x-step-after-landing fn-rtc-step*-of-landing)
           :in-theory (theory 'minimal-theory))))

; With A-HOST-LANDS: the octets the host lands are the operation's.
(defthm fn-rtc-host-landing-is-the-contract-step
  (implies (and (fn-rtc-invp st)
                (fn-rtc-completionp e)
                (equal u (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses st)))
                u
                (member-eq (fn-rtc-get 0 u) *fn-rtc-in-kinds*)
                (member-eq (fn-rtc-get 0 (fn-rtc-e-outcome e)) '(:done :short))
                (<= (fn-rtc-get 1 (fn-rtc-e-outcome e)) (fn-rtc-h-len (fn-rtc-u-hd u))))
           (let ((data (fn-assume-host-input (fn-rtc-e-op e) (fn-rtc-get 1 (fn-rtc-e-outcome e)))))
             (equal (fn-rtc-x-step* e q (fn-rtc-st-splice (fn-rtc-h-buf (fn-rtc-u-hd u))
                                                          (fn-rtc-h-off (fn-rtc-u-hd u))
                                                          data st))
                    (fn-rtc-step* st (fn-rtc-with-data e data) q))))
  :hints (("Goal" :use ((:instance fn-rtc-landing-then-step-is-the-contract-step
                                   (data (fn-assume-host-input (fn-rtc-e-op e) (fn-rtc-get 1 (fn-rtc-e-outcome e)))))
                        fn-rtc-completion-count-natp
                        (:instance fn-assume-host-input-is-n-octets (op (fn-rtc-e-op e)) (n (fn-rtc-get 1 (fn-rtc-e-outcome e)))))
           :in-theory (union-theories (theory 'minimal-theory) '(nfix natp)))))
