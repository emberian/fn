; Runtime contract v2: ownership transfer and instance isolation.
(in-package "ACL2")
(include-book "runtime-contract-invariant")
(include-book "runtime-contract-budget")

(defun fn-rtc-of-slot-p (o j)
  (declare (xargs :guard t))
  (case (fn-rtc-get 0 o)
    ((:workspace :leased) (equal (fn-rtc-get 1 o) j))
    (:handed (or (equal (fn-rtc-get 1 o) j) (equal (fn-rtc-get 3 o) j)))
    (otherwise nil)))

(defun fn-rtc-held-by-p (o j)
  (declare (xargs :guard t))
  (and (member-eq (fn-rtc-get 0 o) '(:workspace :leased :handed))
       (equal (fn-rtc-get 1 o) j)))

(defun fn-rtc-pools-agree-for-p (j p1 p2)
  (declare (xargs :guard t))
  (if (consp p1)
      (and (consp p2)
           (let ((b1 (car p1)) (b2 (car p2)))
             (if (fn-rtc-of-slot-p (fn-rtc-b-owner b1) j)
                 (equal b1 b2)
               (and (equal (fn-rtc-b-gen b1) (fn-rtc-b-gen b2))
                    (equal (fn-rtc-b-owner b1) (fn-rtc-b-owner b2)))))
           (fn-rtc-pools-agree-for-p j (cdr p1) (cdr p2)))
    (atom p2)))

(defun fn-rtc-same-but-foreign-octets-p (j s1 s2)
  (declare (xargs :guard t))
  (and (equal (fn-rtc-config s1) (fn-rtc-config s2))
       (equal (fn-rtc-slots s1) (fn-rtc-slots s2))
       (equal (fn-rtc-uses s1) (fn-rtc-uses s2))
       (equal (fn-rtc-mstates s1) (fn-rtc-mstates s2))
       (equal (fn-rtc-next-op s1) (fn-rtc-next-op s2))
       (fn-rtc-pools-agree-for-p j (fn-rtc-pool s1) (fn-rtc-pool s2))))

(defun fn-rtc-local-buffers (j cfg h pool)
  (declare (xargs :guard (natp h)))
  (if (consp pool)
      (cons (let ((o (fn-rtc-b-owner (car pool))))
              (if (or (fn-rtc-of-slot-p o j)
                      (and (equal o '(:free)) (equal (fn-rtc-home h cfg) j)))
                  (car pool)
                :other))
            (fn-rtc-local-buffers j cfg (+ 1 h) (cdr pool)))
    nil))

(defun fn-rtc-uses-of (j uses)
  (declare (xargs :guard t))
  (if (consp uses)
      (if (equal (fn-rtc-get 1 (car uses)) j)
          (cons (car uses) (fn-rtc-uses-of j (cdr uses)))
        (fn-rtc-uses-of j (cdr uses)))
    nil))

(defun fn-rtc-ranked (xs i)
  (declare (xargs :guard (natp i)))
  (if (consp xs)
      (cons (list (fn-rtc-get 0 (car xs)) (fn-rtc-get 1 (car xs)) (fn-rtc-get 2 (car xs)) i
                  (fn-rtc-get 4 (car xs)))
            (fn-rtc-ranked (cdr xs) (+ 1 i)))
    nil))

(defun fn-rtc-key-rank (key xs i)
  (declare (xargs :guard (natp i)))
  (if (consp xs)
      (if (equal (fn-rtc-key (car xs)) key) i (fn-rtc-key-rank key (cdr xs) (+ 1 i)))
    nil))

(defun fn-rtc-corresponding-event (j e s s2)
  (declare (xargs :guard t))
  (let ((r (fn-rtc-key-rank (fn-rtc-key e) (fn-rtc-uses-of j (fn-rtc-uses s)) 0)))
    (if (natp r)
        (fn-rtc-set 3 (fn-rtc-get 3 (nth r (fn-rtc-uses-of j (fn-rtc-uses s2)))) e)
      (fn-rtc-set 3 (fn-rtc-next-op s2) e))))

(defun fn-rtc-local-ranked (j s)
  (declare (xargs :guard t))
  (list (fn-rtc-config s) (fn-rtc-slot j s) (fn-rtc-mstate j s)
        (fn-rtc-ranked (fn-rtc-uses-of j (fn-rtc-uses s)) 0)
        (fn-rtc-local-buffers j (fn-rtc-config s) 0 (fn-rtc-pool s))))

(defun fn-rtc-others-or-incoming-p (x j)
  (declare (xargs :guard t))
  (or (equal x :other)
      (and (equal (fn-rtc-get 0 (fn-rtc-b-owner x)) :handed)
           (equal (fn-rtc-get 3 (fn-rtc-b-owner x)) j)
           (not (equal (fn-rtc-get 1 (fn-rtc-b-owner x)) j)))))

(defun fn-rtc-local-returns-p (j cfg h l1 l2 pool2)
  (declare (xargs :guard (and (natp h) (true-listp pool2)) :measure (len l1)))
  (if (consp l1)
      (and (consp l2)
           (or (equal (car l1) (car l2))
               ;; a buffer of J's home that another held, or had in flight
               ;; to J, comes back :free
               (and (fn-rtc-others-or-incoming-p (car l1) j)
                    (equal (fn-rtc-home h cfg) j)
                    (equal (fn-rtc-b-owner (car l2)) '(:free))
                    (equal (car l2) (car pool2)))
               ;; another instance puts a buffer in flight to J, or takes
               ;; one in flight to J back (and may hand it again)
               (and (fn-rtc-others-or-incoming-p (car l1) j)
                    (fn-rtc-others-or-incoming-p (car l2) j)))
           (fn-rtc-local-returns-p j cfg (+ 1 h) (cdr l1) (cdr l2) (cdr pool2)))
    (atom l2)))

; Contract v2 keystones, statements only (Builder A, landing 2, 2026-10-09).
; Vocabulary: build/vertical-runs/landing2/v2-statements.lsp (fn-rtc-of-slot-p,
; fn-rtc-held-by-p, fn-rtc-pools-agree-for-p, fn-rtc-same-but-foreign-octets-p,
; fn-rtc-local, fn-rtc-local-ranked, fn-rtc-ranked, fn-rtc-corresponding-event,
; fn-rtc-uses-of, fn-rtc-others-or-incoming-p, fn-rtc-local-returns-p);
; definitions: books/runtime-contract.lisp at 8171ee145.  T1-T15 keep their
; v1 text (T14 restated over the view); their meaning moves with the
; definitions (target includes a delivered hand's target; acts-on includes a
; delivering hand).  T7 is renamed fn-rtc-machine-changes-only-when-delivered-to:
; a machine changes on its own completion or on a hand delivered to it.  T16a
; is a one-step frame; with T2 it holds along every run.

(local
 (defthm fn-rtc-view-pool-hides-in-leases
   (implies (fn-rtc-pools-agree-off-in-leases-p p1 p2)
            (equal (fn-rtc-view-pool id inc cfg h p1)
                   (fn-rtc-view-pool id inc cfg h p2)))
   :hints (("Goal" :induct (list (fn-rtc-view-pool id inc cfg h p1)
                                 (fn-rtc-pools-agree-off-in-leases-p p1 p2))
            :in-theory (e/d (fn-rtc-view-pool fn-rtc-view-own-p fn-rtc-view-mine-p)
                             (fn-rtc-b-owner fn-rtc-b-gen fn-rtc-home))))))

; T14' the view hides octets a worker may be writing
(defthm fn-rtc-view-hides-in-leased-bytes
  (implies (and (equal (fn-rtc-config s1) (fn-rtc-config s2))
                (fn-rtc-pools-agree-off-in-leases-p (fn-rtc-pool s1) (fn-rtc-pool s2)))
           (equal (fn-rtc-view id inc s1) (fn-rtc-view id inc s2)))
  :hints (("Goal" :in-theory (enable fn-rtc-view))))

(local
 (defthm fn-rtc-get-of-cons
   (equal (fn-rtc-get n (cons a d))
          (if (zp n) a (fn-rtc-get (- n 1) d)))))

(local
 (defthm fn-rtc-request-foreign-workspace-frame
   (let ((b (fn-rtc-buffer h s))
         (b2 (fn-rtc-buffer h (mv-nth 0 (fn-rtc-request r id inc s)))))
     (implies (or (and (equal (fn-rtc-get 0 (fn-rtc-b-owner b)) :workspace)
                       (not (equal (fn-rtc-b-owner b) (list :workspace id inc))))
                  (and (equal (fn-rtc-get 0 (fn-rtc-b-owner b2)) :workspace)
                       (not (equal (fn-rtc-b-owner b2) (list :workspace id inc)))))
              (equal b2 b)))
   :hints (("Goal" :use ((:instance fn-rtc-hand-submit-okp-owner (hd (fn-rtc-get 2 r))))
            :in-theory
            (e/d (fn-rtc-request fn-rtc-req-acquire fn-rtc-req-write fn-rtc-req-release
                  fn-rtc-req-close fn-rtc-req-cancel fn-rtc-req-submit)
                 (fn-rtc-get fn-rtc-home fn-rtc-nslots fn-rtc-nbufs fn-rtc-cap fn-rtc-use-bound fn-rtc-next-op fn-rtc-extrap fn-rtc-s-res fn-rtc-s-inc fn-rtc-hand-submit-okp-owner fn-rtc-submit-okp fn-rtc-live-p fn-rtc-current-p fn-rtc-kind-out-p
                  fn-rtc-buffered-kind-p fn-rtc-hand-target-okp fn-rtc-kind-op
                  fn-rtc-b-owner fn-rtc-b-gen fn-rtc-b-bytes fn-rtc-h-buf fn-rtc-h-gen
                  fn-rtc-h-off fn-rtc-h-len fn-rtc-splice fn-cbor-octet-listp))))))

(local
 (defthm fn-rtc-requests-foreign-workspace-frame
   (let ((b (fn-rtc-buffer h s))
         (b2 (fn-rtc-buffer h (mv-nth 0 (fn-rtc-requests reqs id inc s)))))
     (implies (or (and (equal (fn-rtc-get 0 (fn-rtc-b-owner b)) :workspace)
                       (not (equal (fn-rtc-b-owner b) (list :workspace id inc))))
                  (and (equal (fn-rtc-get 0 (fn-rtc-b-owner b2)) :workspace)
                       (not (equal (fn-rtc-b-owner b2) (list :workspace id inc)))))
              (equal b2 b)))
   :hints (("Goal" :induct (fn-rtc-requests reqs id inc s)
            :in-theory (e/d (fn-rtc-requests)
                             (mv-nth fn-rtc-request fn-rtc-b-owner fn-rtc-get))))))

(local
 (defthm fn-rtc-requests-workspace-owner
   (let ((o (fn-rtc-b-owner (fn-rtc-buffer h s)))
         (o2 (fn-rtc-b-owner (fn-rtc-buffer h (mv-nth 0 (fn-rtc-requests reqs id inc s))))))
     (implies (and (equal (fn-rtc-get 0 o) :workspace) (equal (fn-rtc-get 0 o2) :workspace))
              (equal o2 o)))
   :hints (("Goal" :in-theory (theory 'minimal-theory)
            :use fn-rtc-requests-foreign-workspace-frame))))

(local
 (defthm fn-rtc-deliver-workspace-owner
   (let ((o (fn-rtc-b-owner (fn-rtc-buffer h s)))
         (o2 (fn-rtc-b-owner (fn-rtc-buffer h (mv-nth 0 (fn-rtc-deliver s id inc ev q))))))
     (implies (and (equal (fn-rtc-get 0 o) :workspace) (equal (fn-rtc-get 0 o2) :workspace))
              (equal o2 o)))
   :hints (("Goal" :in-theory
            (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
             '(fn-rtc-deliver fn-rtc-buffer-of-with fn-rtc-requests-workspace-owner))))))

(local
 (defthm fn-rtc-close-workspace-owner
   (let ((o (fn-rtc-b-owner (fn-rtc-buffer h s)))
         (o2 (fn-rtc-b-owner (fn-rtc-buffer h (mv-nth 0 (fn-rtc-close-branch s id inc))))))
     (implies (equal (fn-rtc-get 0 o2) :workspace) (equal o2 o)))
   :hints (("Goal" :in-theory
            (e/d (fn-rtc-close-branch)
                 (mv-nth fn-rtc-rearm fn-rtc-release-all fn-rtc-uses-of-slot-p fn-rtc-b-owner
                  fn-rtc-b-gen fn-rtc-b-bytes fn-rtc-s-inc fn-rtc-s-res fn-rtc-s-status))))))

(local
 (defthm fn-rtc-accept-workspace-owner
   (let ((o (fn-rtc-b-owner (fn-rtc-buffer h s)))
         (o2 (fn-rtc-b-owner (fn-rtc-buffer h (mv-nth 0 (fn-rtc-accept-branch s out q))))))
     (implies (and (equal (fn-rtc-get 0 o) :workspace) (equal (fn-rtc-get 0 o2) :workspace))
              (equal o2 o)))
   :hints (("Goal" :in-theory
            (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
             '(fn-rtc-accept-branch fn-rtc-rearm-frame fn-rtc-buffer-of-with
               fn-rtc-deliver-workspace-owner))))))

; T16a a workspace passes between instances only by a hand
(defthm fn-rtc-workspaces-move-only-by-hand
  (let ((o (fn-rtc-b-owner (fn-rtc-buffer h s)))
        (o2 (fn-rtc-b-owner (fn-rtc-buffer h (mv-nth 0 (fn-rtc-step s e q))))))
    (implies (and (fn-rtc-invp s) (equal (fn-rtc-get 0 o) :workspace) (equal (fn-rtc-get 0 o2) :workspace))
             (equal o2 o)))
  :hints (("Goal" :in-theory
           (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
            '(fn-rtc-step-is-step-state fn-rtc-step-state fn-rtc-end-use-keeps-workspaces
              fn-rtc-rearm-frame fn-rtc-deliver-workspace-owner fn-rtc-accept-workspace-owner
              fn-rtc-close-workspace-owner)))))

(local
 (defun fn-rtc-owner-at-p (o id inc)
   (declare (xargs :guard t))
   (or (equal o '(:free))
       (and (member-eq (fn-rtc-get 0 o) '(:workspace :leased :handed))
            (equal (fn-rtc-get 1 o) id) (equal (fn-rtc-get 2 o) inc)))))

(local
 (defthm fn-rtc-request-preserves-owner-at
   (implies (fn-rtc-owner-at-p (fn-rtc-b-owner (fn-rtc-buffer h s)) id inc)
            (fn-rtc-owner-at-p
             (fn-rtc-b-owner (fn-rtc-buffer h (mv-nth 0 (fn-rtc-request r id inc s)))) id inc))
   :hints (("Goal" :in-theory
 (union-theories (theory 'minimal-theory)
 '(fn-rtc-request fn-rtc-req-acquire fn-rtc-req-write fn-rtc-req-release
   fn-rtc-req-close fn-rtc-req-cancel fn-rtc-req-submit fn-rtc-owner-at-p
   fn-rtc-buffer-of-with fn-rtc-buffer-accessors fn-rtc-issue-frame
   fn-rtc-get-of-cons fn-rtc-get-of-non-natp fn-rtc-buffer-of-non-natp
   car-cons cdr-cons nfix natp zp-open
   (:type-prescription fn-rtc-h-buf)
   (:executable-counterpart member-equal) (:executable-counterpart fn-rtc-get)
   (:executable-counterpart equal) (:executable-counterpart zp)
   (:executable-counterpart binary-+) (:executable-counterpart unary--)))
 :use ((:instance fn-rtc-hand-submit-okp-owner (hd (fn-rtc-get 2 r))))))))

(local
 (defthm fn-rtc-requests-preserve-owner-at
   (implies (fn-rtc-owner-at-p (fn-rtc-b-owner (fn-rtc-buffer h s)) id inc)
            (fn-rtc-owner-at-p
             (fn-rtc-b-owner (fn-rtc-buffer h (mv-nth 0 (fn-rtc-requests reqs id inc s)))) id inc))
   :hints (("Goal" :induct (fn-rtc-requests reqs id inc s)
            :in-theory (e/d (fn-rtc-requests)
                             (mv-nth fn-rtc-request fn-rtc-owner-at-p fn-rtc-b-owner fn-rtc-get))))))

(local
 (defthm fn-rtc-deliver-preserves-owner-at
   (implies (fn-rtc-owner-at-p (fn-rtc-b-owner (fn-rtc-buffer h s)) id inc)
            (fn-rtc-owner-at-p
             (fn-rtc-b-owner (fn-rtc-buffer h (mv-nth 0 (fn-rtc-deliver s id inc ev q)))) id inc))
   :hints (("Goal" :in-theory
            (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
             '(fn-rtc-deliver fn-rtc-buffer-of-with fn-rtc-requests-preserve-owner-at))))))

(local
 (defthm fn-rtc-step-keeps-unreturned-handed
   (implies (and (equal (fn-rtc-get 0 (fn-rtc-b-owner (fn-rtc-buffer h s))) :handed)
                 (equal (fn-rtc-buffer h (fn-rtc-end-use s e)) (fn-rtc-buffer h s)))
            (equal (fn-rtc-buffer h (mv-nth 0 (fn-rtc-step s e q))) (fn-rtc-buffer h s)))
   :hints (("Goal" :in-theory
            (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
             '(fn-rtc-step-is-step-state fn-rtc-step-state fn-rtc-leasedp
               fn-rtc-rearm-frame fn-rtc-deliver-frame fn-rtc-accept-branch-frame fn-rtc-close-branch-frame
               (:executable-counterpart member-equal)))))))

(local
 (defthm fn-rtc-end-use-change-names-buffer
   (implies (not (equal (fn-rtc-buffer h (fn-rtc-end-use s e)) (fn-rtc-buffer h s)))
            (let ((u (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s))))
              (and (fn-rtc-completionp e) u (fn-rtc-handlep (fn-rtc-u-hd u))
                   (equal (fn-rtc-h-buf (fn-rtc-u-hd u)) (nfix h)))))
   :hints (("Goal" :in-theory
            (e/d (fn-rtc-end-use fn-rtc-end-lease)
                 (fn-rtc-completionp fn-rtc-find-use fn-rtc-remove-use fn-rtc-key fn-rtc-e-id
                  fn-rtc-u-hd fn-rtc-handlep fn-rtc-h-buf fn-rtc-h-gen fn-rtc-holds-p fn-rtc-lease-return))))))

(local
 (defthm fn-rtc-use-of-handed-buffer
   (implies (and (fn-rtc-use-okp u s) (fn-rtc-handlep (fn-rtc-u-hd u))
                 (equal (fn-rtc-get 0 (fn-rtc-b-owner (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd u)) s))) :handed))
            (let ((o (fn-rtc-b-owner (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd u)) s))))
              (and (equal (fn-rtc-get 0 u) :hand)
                   (equal (fn-rtc-get 1 o) (fn-rtc-get 1 u))
                   (equal (fn-rtc-get 2 o) (fn-rtc-get 2 u)))))
   :hints (("Goal" :in-theory
            (union-theories (theory 'minimal-theory)
             '(fn-rtc-use-okp fn-rtc-usep nfix natp (:executable-counterpart member-equal)))))))

(local
 (defthm fn-rtc-buffer-of-nfix
   (equal (fn-rtc-buffer (nfix h) s) (fn-rtc-buffer h s))
   :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(nfix natp fn-rtc-buffer-of-non-natp))))))

(local
 (defthm fn-rtc-changed-hand-use
   (implies (and (fn-rtc-invp s)
                 (equal (fn-rtc-get 0 (fn-rtc-b-owner (fn-rtc-buffer h s))) :handed)
                 (not (equal (fn-rtc-b-owner (fn-rtc-buffer h (mv-nth 0 (fn-rtc-step s e q))))
                             (fn-rtc-b-owner (fn-rtc-buffer h s)))))
            (let ((u (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))
                  (o (fn-rtc-b-owner (fn-rtc-buffer h s))))
              (and (fn-rtc-completionp e) u (fn-rtc-handlep (fn-rtc-u-hd u))
                   (equal (fn-rtc-h-buf (fn-rtc-u-hd u)) (nfix h))
                   (equal (fn-rtc-e-kind e) :hand)
                   (equal (fn-rtc-e-id e) (fn-rtc-get 1 o))
                   (equal (fn-rtc-e-inc e) (fn-rtc-get 2 o)))))
   :hints (("Goal" :in-theory
            (union-theories (theory 'minimal-theory)
             '(fn-rtc-buffer-of-nfix))
            :use (fn-rtc-step-keeps-unreturned-handed fn-rtc-end-use-change-names-buffer
                  fn-rtc-invp-uses-okp
                  (:instance fn-rtc-find-use-is-member (k (fn-rtc-key e)) (uses (fn-rtc-uses s)))
                  (:instance fn-rtc-uses-okp-member (uses (fn-rtc-uses s))
                    (u (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s))))
                  (:instance fn-rtc-matching-use-fields (uses (fn-rtc-uses s)))
                  (:instance fn-rtc-use-of-handed-buffer
                    (u (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))))))))

(local
 (defthm fn-rtc-end-use-returned-buffer
   (implies (not (equal (fn-rtc-buffer h (fn-rtc-end-use s e)) (fn-rtc-buffer h s)))
            (equal (fn-rtc-buffer h (fn-rtc-end-use s e))
                   (fn-rtc-lease-return (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s))
                                        e (fn-rtc-buffer h s) s)))
   :hints (("Goal" :in-theory
            (e/d (fn-rtc-end-use fn-rtc-end-lease)
                 (fn-rtc-completionp fn-rtc-find-use fn-rtc-remove-use fn-rtc-key fn-rtc-e-id
                  fn-rtc-u-hd fn-rtc-handlep fn-rtc-h-buf fn-rtc-h-gen fn-rtc-holds-p fn-rtc-lease-return))))))

(local
 (defthm fn-rtc-found-use-buffer-ownerp
   (let ((u (fn-rtc-find-use key (fn-rtc-uses s))))
     (implies (and (fn-rtc-invp s) u (fn-rtc-handlep (fn-rtc-u-hd u)))
              (fn-rtc-ownerp (fn-rtc-b-owner (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd u)) s)))))
   :hints (("Goal" :in-theory
            (e/d (fn-rtc-buffer-okp fn-rtc-bufferp fn-rtc-b-owner)
                 (fn-rtc-core-invp-buffer fn-rtc-core-invp-found-use fn-rtc-use-okp-buffer-index
                  fn-rtc-invp-is-core-and-admission fn-rtc-invp fn-rtc-core-invp fn-rtc-ownerp fn-rtc-use-okp fn-rtc-find-use
                  fn-rtc-get fn-rtc-buffer fn-rtc-handlep fn-rtc-u-hd fn-rtc-h-buf))
            :use (fn-rtc-invp-is-core-and-admission
                  (:instance fn-rtc-core-invp-found-use)
                  (:instance fn-rtc-use-okp-buffer-index (u (fn-rtc-find-use key (fn-rtc-uses s))))
                  (:instance fn-rtc-core-invp-buffer
                    (h (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use key (fn-rtc-uses s)))))))))))

(local
 (defthm fn-rtc-changed-hand-ownerp
   (implies (and (fn-rtc-invp s)
                 (equal (fn-rtc-get 0 (fn-rtc-b-owner (fn-rtc-buffer h s))) :handed)
                 (not (equal (fn-rtc-b-owner (fn-rtc-buffer h (mv-nth 0 (fn-rtc-step s e q))))
                             (fn-rtc-b-owner (fn-rtc-buffer h s)))))
            (fn-rtc-ownerp (fn-rtc-b-owner (fn-rtc-buffer h s))))
   :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-rtc-buffer-of-nfix))
            :use (fn-rtc-changed-hand-use
                  (:instance fn-rtc-found-use-buffer-ownerp (key (fn-rtc-key e))))))))

(local
 (defthm fn-rtc-owner-equality-fields
   (implies (equal o (list* tag id inc tail))
            (and (equal (fn-rtc-get 0 o) tag)
                 (equal (fn-rtc-get 1 o) id)
                 (equal (fn-rtc-get 2 o) inc)))
   :rule-classes :forward-chaining))

(local
 (defthm fn-rtc-buffer-equality-owner
   (implies (equal b (list g o bytes)) (equal (fn-rtc-b-owner b) o))
   :rule-classes :forward-chaining))

(local
 (defthm fn-rtc-end-use-returned-owner
   (implies (not (equal (fn-rtc-buffer h (fn-rtc-end-use s e)) (fn-rtc-buffer h s)))
            (equal (fn-rtc-b-owner (fn-rtc-buffer h (fn-rtc-end-use s e)))
                   (fn-rtc-b-owner (fn-rtc-lease-return (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s))
                                                        e (fn-rtc-buffer h s) s))))
   :hints (("Goal" :in-theory (theory 'minimal-theory) :use fn-rtc-end-use-returned-buffer))))

(local
 (defthm fn-rtc-deliver-owner-fields
   (let ((o2 (fn-rtc-b-owner (fn-rtc-buffer h (mv-nth 0 (fn-rtc-deliver s id inc ev q))))))
     (implies (and (fn-rtc-owner-at-p (fn-rtc-b-owner (fn-rtc-buffer h s)) id inc)
                   (not (equal o2 '(:free))))
              (and (fn-rtc-of-slot-p o2 id) (equal (fn-rtc-get 2 o2) inc))))
   :hints (("Goal" :in-theory
            (union-theories (theory 'minimal-theory)
             '(fn-rtc-owner-at-p fn-rtc-of-slot-p member-equal car-cons cdr-cons
               (:executable-counterpart equal)))
            :use fn-rtc-deliver-preserves-owner-at))))

(local
 (defthm fn-rtc-of-workspace
   (equal (fn-rtc-of-slot-p (list :workspace id inc) j) (equal id j))))

; T16b a handed buffer moves only on its own hand's completion: to the named
; target live at the named incarnation (the step's target), back to the
; sender's incarnation, or to :free
(defthm fn-rtc-handed-buffer-lands-only-at-its-target
  (let ((o (fn-rtc-b-owner (fn-rtc-buffer h s)))
        (o2 (fn-rtc-b-owner (fn-rtc-buffer h (mv-nth 0 (fn-rtc-step s e q))))))
    (implies (and (fn-rtc-invp s) (equal (fn-rtc-get 0 o) :handed) (not (equal o2 o)))
             (and (fn-rtc-completionp e) (equal (fn-rtc-e-kind e) :hand)
                  (equal (fn-rtc-e-id e) (fn-rtc-get 1 o)) (equal (fn-rtc-e-inc e) (fn-rtc-get 2 o))
                  (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s))
                  (equal (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))) (nfix h))
                  (or (equal o2 '(:free))
                      (if (fn-rtc-hand-delivers-p s e)
                          (and (equal (fn-rtc-target s e) (fn-rtc-get 3 o))
                               (fn-rtc-live-p (fn-rtc-get 3 o) (fn-rtc-get 4 o) s)
                               (fn-rtc-of-slot-p o2 (fn-rtc-get 3 o))
                               (equal (fn-rtc-get 2 o2) (fn-rtc-get 4 o)))
                        (and (fn-rtc-of-slot-p o2 (fn-rtc-get 1 o))
                             (equal (fn-rtc-get 2 o2) (fn-rtc-get 2 o))))))))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
            '(fn-rtc-owner-equality-fields fn-rtc-buffer-equality-owner fn-rtc-buffer-of-non-natp fn-rtc-acts-on-p
              fn-rtc-step-is-step-state fn-rtc-step-state fn-rtc-rearm-frame
              fn-rtc-deliver-owner-fields fn-rtc-owner-at-p fn-rtc-of-workspace
              fn-rtc-hand-delivers-p fn-rtc-target fn-rtc-hand-to fn-rtc-handed-to-live-p
              fn-rtc-lease-return fn-rtc-buffer-accessors fn-rtc-buffer-of-nfix
              fn-rtc-ownerp nfix natp fn-rtc-get-of-cons car-cons cdr-cons
              (:executable-counterpart zp) (:executable-counterpart binary-+) (:executable-counterpart unary--)
              (:executable-counterpart member-equal) (:executable-counterpart equal)))
           :use (fn-rtc-changed-hand-use fn-rtc-changed-hand-ownerp
                 fn-rtc-step-keeps-unreturned-handed fn-rtc-end-use-returned-owner))))

(local
 (defthm fn-rtc-pools-agree-for-get
   (implies (fn-rtc-pools-agree-for-p j p1 p2)
            (let ((b1 (fn-rtc-get h p1)) (b2 (fn-rtc-get h p2)))
              (and (equal (fn-rtc-b-gen b1) (fn-rtc-b-gen b2))
                   (equal (fn-rtc-b-owner b1) (fn-rtc-b-owner b2))
                   (implies (fn-rtc-of-slot-p (fn-rtc-b-owner b1) j) (equal b1 b2)))))
   :hints (("Goal" :induct (list (fn-rtc-get h p1) (fn-rtc-pools-agree-for-p j p1 p2))
            :in-theory (disable fn-rtc-b-gen fn-rtc-b-owner fn-rtc-of-slot-p)))))

(local
 (defthm fn-rtc-pools-agree-for-set
   (implies (fn-rtc-pools-agree-for-p j p1 p2)
            (fn-rtc-pools-agree-for-p j (fn-rtc-set h b p1) (fn-rtc-set h b p2)))
   :hints (("Goal" :induct (list (fn-rtc-set h b p1) (fn-rtc-pools-agree-for-p j p1 p2))
            :in-theory (disable fn-rtc-b-gen fn-rtc-b-owner fn-rtc-of-slot-p)))))

(local
 (defthm fn-rtc-pools-agree-for-view
   (implies (fn-rtc-pools-agree-for-p j p1 p2)
            (equal (fn-rtc-view-pool j inc cfg h p1) (fn-rtc-view-pool j inc cfg h p2)))
   :hints (("Goal" :induct (list (fn-rtc-view-pool j inc cfg h p1)
                                 (fn-rtc-pools-agree-for-p j p1 p2))
            :in-theory (e/d (fn-rtc-view-pool fn-rtc-view-mine-p fn-rtc-view-own-p fn-rtc-of-slot-p)
                             (fn-rtc-b-gen fn-rtc-b-owner fn-rtc-b-bytes fn-rtc-home))))))

(local
 (defthm fn-rtc-foreign-octets-views-equal
   (implies (fn-rtc-same-but-foreign-octets-p j s1 s2)
            (equal (fn-rtc-view j inc s1) (fn-rtc-view j inc s2)))
   :hints (("Goal" :in-theory (e/d (fn-rtc-view)
                                  (fn-rtc-pools-agree-for-p fn-rtc-view-pool))))))

(local
 (defthm fn-rtc-foreign-octets-buffer-fields
   (implies (fn-rtc-same-but-foreign-octets-p j s1 s2)
            (and (equal (fn-rtc-b-gen (fn-rtc-buffer h s1)) (fn-rtc-b-gen (fn-rtc-buffer h s2)))
                 (equal (fn-rtc-b-owner (fn-rtc-buffer h s1)) (fn-rtc-b-owner (fn-rtc-buffer h s2)))
                 (implies (fn-rtc-of-slot-p (fn-rtc-b-owner (fn-rtc-buffer h s1)) j)
                          (equal (fn-rtc-buffer h s1) (fn-rtc-buffer h s2)))))
   :hints (("Goal" :in-theory
 (union-theories (theory 'minimal-theory) '(fn-rtc-buffer fn-rtc-same-but-foreign-octets-p))
 :use ((:instance fn-rtc-pools-agree-for-get (p1 (fn-rtc-pool s1)) (p2 (fn-rtc-pool s2))))))))

(local
 (defthm fn-rtc-foreign-octets-control-fields
   (implies (fn-rtc-same-but-foreign-octets-p j s1 s2)
            (and (equal (fn-rtc-slot id s1) (fn-rtc-slot id s2))
                 (equal (fn-rtc-live-p id inc s1) (fn-rtc-live-p id inc s2))
                 (equal (fn-rtc-current-p id inc s1) (fn-rtc-current-p id inc s2))
                 (equal (fn-rtc-hand-target-okp extra id s1) (fn-rtc-hand-target-okp extra id s2))))
   :hints (("Goal" :in-theory
            (union-theories (theory 'minimal-theory)
             '(fn-rtc-same-but-foreign-octets-p fn-rtc-slot fn-rtc-live-p
               fn-rtc-current-p fn-rtc-hand-target-okp))))))


(local
 (defthm fn-rtc-foreign-octets-owned-buffer
   (implies (and (fn-rtc-same-but-foreign-octets-p j s1 s2)
                 (or (equal (fn-rtc-b-owner (fn-rtc-buffer h s1)) (list :workspace j inc))
                     (equal (fn-rtc-b-owner (fn-rtc-buffer h s1)) (list :leased j inc :out))))
            (equal (fn-rtc-buffer h s1) (fn-rtc-buffer h s2)))
   :hints (("Goal" :in-theory
            (e/d (fn-rtc-of-slot-p)
                 (fn-rtc-same-but-foreign-octets-p fn-rtc-buffer fn-rtc-b-owner
                  fn-rtc-b-gen fn-rtc-foreign-octets-buffer-fields))
            :use fn-rtc-foreign-octets-buffer-fields))))

(local
 (defthm fn-rtc-foreign-octets-submit-okp
   (implies (fn-rtc-same-but-foreign-octets-p j s1 s2)
            (equal (fn-rtc-submit-okp kind hd j inc s1) (fn-rtc-submit-okp kind hd j inc s2)))
   :hints (("Goal" :in-theory
            (union-theories (theory 'minimal-theory)
             '(fn-rtc-owner-equality-fields fn-rtc-same-but-foreign-octets-p fn-rtc-submit-okp fn-rtc-of-slot-p
               fn-rtc-get fn-rtc-get-of-cons nfix natp zp-open car-cons cdr-cons
               (:executable-counterpart binary-+) (:executable-counterpart unary--) (:executable-counterpart fn-rtc-get)
               (:executable-counterpart member-equal) (:executable-counterpart zp)
               (:executable-counterpart equal)))
            :use ((:instance fn-rtc-foreign-octets-buffer-fields (h (fn-rtc-h-buf hd))))))))

(local
 (defthm fn-rtc-request-foreign-octets
   (implies (fn-rtc-same-but-foreign-octets-p j s1 s2)
            (and (equal (mv-nth 1 (fn-rtc-request r j inc s1)) (mv-nth 1 (fn-rtc-request r j inc s2)))
                 (fn-rtc-same-but-foreign-octets-p j
                   (mv-nth 0 (fn-rtc-request r j inc s1))
                   (mv-nth 0 (fn-rtc-request r j inc s2)))))
   :hints (("Goal" :in-theory
            (union-theories (theory 'minimal-theory)
             '(fn-rtc-request fn-rtc-req-acquire fn-rtc-req-write fn-rtc-req-release
               fn-rtc-req-close fn-rtc-req-cancel fn-rtc-req-submit fn-rtc-issue
               fn-rtc-same-but-foreign-octets-p fn-rtc-of-slot-p
               fn-rtc-with-accessors fn-rtc-next-op-of-with fn-rtc-make-accessors fn-rtc-owner-equality-fields
               fn-rtc-pools-agree-for-set fn-rtc-get-of-cons fn-rtc-get-of-non-natp
               fn-rtc-buffer-of-non-natp fn-rtc-buffer-accessors
               nfix natp zp-open car-cons cdr-cons
               (:type-prescription fn-rtc-next-op)
               (:executable-counterpart member-equal) (:executable-counterpart equal)
               (:executable-counterpart zp) (:executable-counterpart binary-+)
               (:executable-counterpart unary--)))
            :use ((:instance fn-rtc-foreign-octets-control-fields (id j) (extra (fn-rtc-get 3 r)))
                  (:instance fn-rtc-foreign-octets-submit-okp (kind (fn-rtc-get 1 r)) (hd (fn-rtc-get 2 r)))
                  (:instance fn-rtc-foreign-octets-buffer-fields (h (fn-rtc-get 1 r)))
                  (:instance fn-rtc-foreign-octets-buffer-fields (h (fn-rtc-h-buf (fn-rtc-get 2 r)))))))))

(local
 (defun-nx fn-rtc-requests-pair-induct (reqs id inc s1 s2)
   (declare (xargs :measure (len reqs)))
   (if (consp reqs)
       (fn-rtc-requests-pair-induct (cdr reqs) id inc
          (mv-nth 0 (fn-rtc-request (car reqs) id inc s1))
          (mv-nth 0 (fn-rtc-request (car reqs) id inc s2)))
     (list s1 s2))))

(local
 (defthm fn-rtc-requests-foreign-octets
   (implies (fn-rtc-same-but-foreign-octets-p j s1 s2)
            (and (equal (mv-nth 1 (fn-rtc-requests reqs j inc s1)) (mv-nth 1 (fn-rtc-requests reqs j inc s2)))
                 (fn-rtc-same-but-foreign-octets-p j
                   (mv-nth 0 (fn-rtc-requests reqs j inc s1))
                   (mv-nth 0 (fn-rtc-requests reqs j inc s2)))))
   :hints (("Goal" :induct (fn-rtc-requests-pair-induct reqs j inc s1 s2)
            :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
                         '(fn-rtc-requests fn-rtc-requests-pair-induct fn-rtc-request-foreign-octets))))))

(local
 (defthm fn-rtc-foreign-octets-with-mstate
   (implies (fn-rtc-same-but-foreign-octets-p j s1 s2)
            (fn-rtc-same-but-foreign-octets-p j (fn-rtc-with-mstate id m s1) (fn-rtc-with-mstate id m s2)))
   :hints (("Goal" :in-theory
            (union-theories (theory 'minimal-theory)
             '(fn-rtc-same-but-foreign-octets-p fn-rtc-with-accessors fn-rtc-next-op-of-with))))))

(local
 (defthm fn-rtc-foreign-octets-mstate
   (implies (fn-rtc-same-but-foreign-octets-p j s1 s2)
            (equal (fn-rtc-mstate id s1) (fn-rtc-mstate id s2)))
   :hints (("Goal" :in-theory
            (union-theories (theory 'minimal-theory) '(fn-rtc-mstate fn-rtc-same-but-foreign-octets-p))))))

(local
 (defthm fn-rtc-deliver-foreign-octets
   (implies (fn-rtc-same-but-foreign-octets-p j s1 s2)
            (and (equal (mv-nth 1 (fn-rtc-deliver s1 j inc ev q)) (mv-nth 1 (fn-rtc-deliver s2 j inc ev q)))
                 (fn-rtc-same-but-foreign-octets-p j
                   (mv-nth 0 (fn-rtc-deliver s1 j inc ev q))
                   (mv-nth 0 (fn-rtc-deliver s2 j inc ev q)))))
   :hints (("Goal" :in-theory
            (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
             '(fn-rtc-deliver fn-rtc-foreign-octets-with-mstate))
            :use ((:instance fn-rtc-requests-foreign-octets
                    (reqs (mv-nth 1 (fn-rtc-m-step (fn-rtc-mstate j s1) ev (fn-rtc-view j inc s1) (nfix q))))
                    (s1 (fn-rtc-with-mstate j (mv-nth 0 (fn-rtc-m-step (fn-rtc-mstate j s1) ev (fn-rtc-view j inc s1) (nfix q))) s1))
                    (s2 (fn-rtc-with-mstate j (mv-nth 0 (fn-rtc-m-step (fn-rtc-mstate j s1) ev (fn-rtc-view j inc s1) (nfix q))) s2)))
                  (:instance fn-rtc-foreign-octets-mstate (id j))
                  fn-rtc-foreign-octets-views-equal
                  (:instance fn-rtc-foreign-octets-control-fields (id j)))))))

(local
 (defthm fn-rtc-pools-agree-for-set-pair
   (implies (and (fn-rtc-pools-agree-for-p j p1 p2)
                 (fn-rtc-pools-agree-for-p j (list b1) (list b2)))
            (fn-rtc-pools-agree-for-p j (fn-rtc-set h b1 p1) (fn-rtc-set h b2 p2)))
   :hints (("Goal" :induct (list (fn-rtc-set h b1 p1) (fn-rtc-pools-agree-for-p j p1 p2))
            :in-theory (disable fn-rtc-b-gen fn-rtc-b-owner fn-rtc-of-slot-p)))))

(local
 (defthm fn-rtc-foreign-octets-lease-return
   (implies (and (fn-rtc-same-but-foreign-octets-p j s1 s2)
                 (fn-rtc-pools-agree-for-p j (list b1) (list b2))
                 (fn-rtc-ownerp (fn-rtc-b-owner b1))
                 (member-eq (fn-rtc-get 0 (fn-rtc-b-owner b1)) '(:leased :handed)))
            (fn-rtc-pools-agree-for-p j (list (fn-rtc-lease-return u e b1 s1))
                                          (list (fn-rtc-lease-return u e b2 s2))))
   :hints (("Goal" :in-theory
            (union-theories (theory 'minimal-theory)
             '(fn-rtc-pools-agree-for-p fn-rtc-of-slot-p fn-rtc-lease-return fn-rtc-handed-to-live-p
               fn-rtc-ownerp fn-rtc-buffer-accessors fn-rtc-get-of-cons fn-rtc-owner-equality-fields
               fn-rtc-same-but-foreign-octets-p fn-rtc-current-p fn-rtc-live-p fn-rtc-slot
               nfix natp member-equal car-cons cdr-cons
               (:executable-counterpart equal) (:executable-counterpart zp)
               (:executable-counterpart unary--) (:executable-counterpart binary-+)))))))

(local
 (defthm fn-rtc-foreign-octets-buffer-pair
   (implies (fn-rtc-same-but-foreign-octets-p j s1 s2)
            (fn-rtc-pools-agree-for-p j (list (fn-rtc-buffer h s1)) (list (fn-rtc-buffer h s2))))
   :hints (("Goal" :in-theory
            (union-theories (theory 'minimal-theory)
             '(fn-rtc-pools-agree-for-p car-cons cdr-cons))
            :use fn-rtc-foreign-octets-buffer-fields))))

(local
 (defthm fn-rtc-found-use-is-leased
   (let ((u (fn-rtc-find-use key (fn-rtc-uses s))))
     (implies (and (fn-rtc-invp s) u (fn-rtc-handlep (fn-rtc-u-hd u)))
              (fn-rtc-leasedp (fn-rtc-h-buf (fn-rtc-u-hd u)) s)))
   :hints (("Goal" :in-theory (theory 'minimal-theory)
            :use (fn-rtc-invp-is-core-and-admission
                  (:instance fn-rtc-core-invp-found-use)
                  (:instance fn-rtc-use-okp-lease (u (fn-rtc-find-use key (fn-rtc-uses s)))))))))

(local
 (defthm fn-rtc-end-use-foreign-octets
   (implies (and (fn-rtc-invp s1) (fn-rtc-same-but-foreign-octets-p j s1 s2))
            (fn-rtc-same-but-foreign-octets-p j (fn-rtc-end-use s1 e) (fn-rtc-end-use s2 e)))
   :hints (("Goal" :in-theory
            (union-theories (theory 'minimal-theory)
             '(fn-rtc-end-use fn-rtc-end-lease fn-rtc-retire-drained fn-rtc-slot
               fn-rtc-same-but-foreign-octets-p fn-rtc-with-accessors fn-rtc-next-op-of-with
               fn-rtc-buffer-of-with fn-rtc-leasedp fn-rtc-lease-return-of-with-uses
               fn-rtc-pools-agree-for-set-pair))
            :use ((:instance fn-rtc-found-use-buffer-ownerp (s s1) (key (fn-rtc-key e)))
                  (:instance fn-rtc-found-use-is-leased (s s1) (key (fn-rtc-key e)))
                  (:instance fn-rtc-foreign-octets-buffer-pair (h (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s1))))))
                  (:instance fn-rtc-foreign-octets-lease-return
                    (u (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s1)))
                    (b1 (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s1)))) s1))
                    (b2 (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s1)))) s2))))))))

(local
 (defthm fn-rtc-rearm-foreign-octets
   (implies (fn-rtc-same-but-foreign-octets-p j s1 s2)
            (and (equal (mv-nth 1 (fn-rtc-rearm s1)) (mv-nth 1 (fn-rtc-rearm s2)))
                 (fn-rtc-same-but-foreign-octets-p j (mv-nth 0 (fn-rtc-rearm s1)) (mv-nth 0 (fn-rtc-rearm s2)))))
   :hints (("Goal" :in-theory
            (union-theories (theory 'minimal-theory)
             '(fn-rtc-rearm fn-rtc-issue fn-rtc-same-but-foreign-octets-p fn-rtc-make-accessors))))))

(local
 (defthm fn-rtc-release-all-foreign-octets
   (implies (fn-rtc-pools-agree-for-p j p1 p2)
            (fn-rtc-pools-agree-for-p j (fn-rtc-release-all p1 id inc) (fn-rtc-release-all p2 id inc)))
   :hints (("Goal" :induct (fn-rtc-pools-agree-for-p j p1 p2)
            :in-theory (e/d (fn-rtc-release-all fn-rtc-pools-agree-for-p fn-rtc-of-slot-p)
                             (fn-rtc-b-gen fn-rtc-b-owner fn-rtc-b-bytes))))))

(local
 (defthm fn-rtc-close-branch-foreign-octets
   (implies (fn-rtc-same-but-foreign-octets-p j s1 s2)
            (and (equal (mv-nth 1 (fn-rtc-close-branch s1 id inc)) (mv-nth 1 (fn-rtc-close-branch s2 id inc)))
                 (fn-rtc-same-but-foreign-octets-p j (mv-nth 0 (fn-rtc-close-branch s1 id inc))
                                                      (mv-nth 0 (fn-rtc-close-branch s2 id inc)))))
   :hints (("Goal" :in-theory
            (union-theories (theory 'minimal-theory)
             '(fn-rtc-close-branch fn-rtc-rearm fn-rtc-issue fn-rtc-slot
               fn-rtc-same-but-foreign-octets-p fn-rtc-with-accessors fn-rtc-next-op-of-with
               fn-rtc-make-accessors fn-rtc-release-all-foreign-octets))))))

(local
 (defthm fn-rtc-foreign-octets-step-control
   (implies (fn-rtc-same-but-foreign-octets-p j s1 s2)
            (and (equal (fn-rtc-hand-delivers-p s1 e) (fn-rtc-hand-delivers-p s2 e))
                 (equal (fn-rtc-acts-on-p s1 e) (fn-rtc-acts-on-p s2 e))
                 (equal (fn-rtc-target s1 e) (fn-rtc-target s2 e))))
   :hints (("Goal" :in-theory
            (union-theories (theory 'minimal-theory)
             '(fn-rtc-hand-delivers-p fn-rtc-acts-on-p fn-rtc-target fn-rtc-hand-to fn-rtc-handed-to-live-p
               fn-rtc-live-p fn-rtc-slot fn-rtc-same-but-foreign-octets-p))
            :use ((:instance fn-rtc-foreign-octets-buffer-fields
                    (h (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s1)))))))))))

(local
 (defthm fn-rtc-foreign-octets-accept-prepared
   (implies (fn-rtc-same-but-foreign-octets-p j s1 s2)
            (and (equal (fn-rtc-accept-go-p s1 out) (fn-rtc-accept-go-p s2 out))
                 (equal (fn-rtc-accept-slot s1) (fn-rtc-accept-slot s2))
                 (equal (fn-rtc-accept-inc s1) (fn-rtc-accept-inc s2))
                 (fn-rtc-same-but-foreign-octets-p j (fn-rtc-accept-prepared s1 out) (fn-rtc-accept-prepared s2 out))))
   :hints (("Goal" :in-theory
            (union-theories (theory 'minimal-theory)
             '(fn-rtc-accept-go-p fn-rtc-accept-slot fn-rtc-accept-inc fn-rtc-accept-prepared
               fn-rtc-slot fn-rtc-same-but-foreign-octets-p fn-rtc-with-accessors fn-rtc-next-op-of-with))))))

(local
 (defthm fn-rtc-accept-branch-foreign-octets
   (implies (and (fn-rtc-same-but-foreign-octets-p j s1 s2)
                 (equal j (nfix (fn-rtc-free-slot 0 (fn-rtc-slots s1)))))
            (and (equal (mv-nth 1 (fn-rtc-accept-branch s1 out q)) (mv-nth 1 (fn-rtc-accept-branch s2 out q)))
                 (fn-rtc-same-but-foreign-octets-p j (mv-nth 0 (fn-rtc-accept-branch s1 out q))
                                                      (mv-nth 0 (fn-rtc-accept-branch s2 out q)))))
   :hints (("Goal" :in-theory
            (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
             '(fn-rtc-accept-branch-parts fn-rtc-accept-slot fn-rtc-accept-go-p natp nfix))
            :use (fn-rtc-foreign-octets-accept-prepared fn-rtc-rearm-foreign-octets
                  (:instance fn-rtc-free-slot-natp (i 0) (slots (fn-rtc-slots s1)))
                  (:instance fn-rtc-deliver-foreign-octets
                    (s1 (fn-rtc-accept-prepared s1 out)) (s2 (fn-rtc-accept-prepared s2 out))
                    (inc (fn-rtc-accept-inc s1)) (ev (fn-rtc-ev :accept out j (fn-rtc-accept-inc s1) nil)))
                  (:instance fn-rtc-rearm-foreign-octets
                    (s1 (mv-nth 0 (fn-rtc-deliver (fn-rtc-accept-prepared s1 out) j (fn-rtc-accept-inc s1)
                                (fn-rtc-ev :accept out j (fn-rtc-accept-inc s1) nil) q)))
                    (s2 (mv-nth 0 (fn-rtc-deliver (fn-rtc-accept-prepared s2 out) j (fn-rtc-accept-inc s1)
                                (fn-rtc-ev :accept out j (fn-rtc-accept-inc s1) nil) q)))))))))

(local
 (defthm fn-rtc-foreign-octets-hand-buffer
   (implies (and (fn-rtc-invp s1) (fn-rtc-same-but-foreign-octets-p j s1 s2)
                 (equal j (fn-rtc-target s1 e)) (equal (fn-rtc-e-kind e) :hand)
                 (fn-rtc-completionp e) (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s1)))
            (let ((h (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s1))))))
              (equal (fn-rtc-buffer h s1) (fn-rtc-buffer h s2))))
   :hints (("Goal" :in-theory
            (union-theories (theory 'minimal-theory)
             '(fn-rtc-target fn-rtc-hand-to fn-rtc-of-slot-p fn-rtc-use-okp fn-rtc-usep fn-rtc-u-hd
               fn-rtc-ownerp natp nfix (:executable-counterpart member-equal) (:executable-counterpart equal)))
            :use ((:instance fn-rtc-invp-is-core-and-admission (s s1))
                  (:instance fn-rtc-core-invp-found-use (s s1) (key (fn-rtc-key e)))
                  (:instance fn-rtc-matching-use-fields (uses (fn-rtc-uses s1)))
                  (:instance fn-rtc-found-use-buffer-ownerp (s s1) (key (fn-rtc-key e)))
                  (:instance fn-rtc-foreign-octets-buffer-fields
                    (h (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s1)))))))))))

(local
 (defthm fn-rtc-foreign-octets-plain-fields
   (implies (fn-rtc-same-but-foreign-octets-p j s1 s2)
            (and (equal (fn-rtc-config s1) (fn-rtc-config s2))
                 (equal (fn-rtc-slots s1) (fn-rtc-slots s2))
                 (equal (fn-rtc-uses s1) (fn-rtc-uses s2))
                 (equal (fn-rtc-mstates s1) (fn-rtc-mstates s2))
                 (equal (fn-rtc-next-op s1) (fn-rtc-next-op s2))))
   :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-rtc-same-but-foreign-octets-p))))))

(local
 (defthm fn-rtc-acting-matches-use
   (implies (fn-rtc-acts-on-p s e)
            (and (fn-rtc-completionp e) (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s))))
   :hints (("Goal" :in-theory
            (union-theories (theory 'minimal-theory) '(fn-rtc-acts-on-p fn-rtc-hand-delivers-p))))))

(local
 (defthm fn-rtc-accept-not-done-foreign-octets
   (implies (and (fn-rtc-same-but-foreign-octets-p j s1 s2) (not (equal (fn-rtc-get 0 out) :done)))
            (and (equal (mv-nth 1 (fn-rtc-accept-branch s1 out q)) (mv-nth 1 (fn-rtc-accept-branch s2 out q)))
                 (fn-rtc-same-but-foreign-octets-p j (mv-nth 0 (fn-rtc-accept-branch s1 out q))
                                                      (mv-nth 0 (fn-rtc-accept-branch s2 out q)))))
   :hints (("Goal" :in-theory
            (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth)) '(fn-rtc-accept-branch))
            :use fn-rtc-rearm-foreign-octets))))

(local
 (defthm fn-rtc-step-foreign-octets-inactive
   (implies (and (fn-rtc-invp s1) (fn-rtc-same-but-foreign-octets-p j s1 s2) (equal j (fn-rtc-target s1 e)) (not (fn-rtc-acts-on-p s1 e)))
            (and (equal (mv-nth 1 (fn-rtc-step s1 e q)) (mv-nth 1 (fn-rtc-step s2 e q)))
                 (fn-rtc-same-but-foreign-octets-p j (mv-nth 0 (fn-rtc-step s1 e q))
                                                      (mv-nth 0 (fn-rtc-step s2 e q)))))
   :hints (("Goal" :in-theory
            (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
             '(fn-rtc-step-is-step-state fn-rtc-step-state fn-rtc-step-actions-is fn-rtc-step-actions fn-rtc-step*
               fn-rtc-target fn-rtc-hand-to fn-rtc-slots-of-end-use-when-acting
               (:executable-counterpart member-equal) (:executable-counterpart equal)))
            :use (fn-rtc-foreign-octets-plain-fields
                  fn-rtc-foreign-octets-step-control
                  fn-rtc-end-use-foreign-octets
                  (:instance fn-rtc-rearm-foreign-octets (s1 (fn-rtc-end-use s1 e)) (s2 (fn-rtc-end-use s2 e))))))))

(local
 (defthm fn-rtc-step-foreign-octets-hand
   (implies (and (fn-rtc-invp s1) (fn-rtc-same-but-foreign-octets-p j s1 s2) (equal j (fn-rtc-target s1 e)) (fn-rtc-acts-on-p s1 e) (fn-rtc-hand-delivers-p s1 e))
            (and (equal (mv-nth 1 (fn-rtc-step s1 e q)) (mv-nth 1 (fn-rtc-step s2 e q)))
                 (fn-rtc-same-but-foreign-octets-p j (mv-nth 0 (fn-rtc-step s1 e q))
                                                      (mv-nth 0 (fn-rtc-step s2 e q)))))
   :hints (("Goal" :in-theory
            (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
             '(fn-rtc-step-is-step-state fn-rtc-step-state fn-rtc-step-actions-is fn-rtc-step-actions fn-rtc-step*
               fn-rtc-target fn-rtc-hand-to fn-rtc-slots-of-end-use-when-acting
               (:executable-counterpart member-equal) (:executable-counterpart equal)))
            :use (fn-rtc-foreign-octets-plain-fields
                  fn-rtc-foreign-octets-step-control
                  fn-rtc-end-use-foreign-octets
                  fn-rtc-foreign-octets-hand-buffer
                  (:instance fn-rtc-acting-matches-use (s s1))
                  (:instance fn-rtc-hand-delivers-kind (s s1))
                  (:instance fn-rtc-deliver-foreign-octets (s1 (fn-rtc-end-use s1 e)) (s2 (fn-rtc-end-use s2 e)) (inc (fn-rtc-get 4 (fn-rtc-b-owner (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s1)))) s1)))) (ev (fn-rtc-ev :handed (fn-rtc-delivered-outcome (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s1)) e) j (fn-rtc-get 4 (fn-rtc-b-owner (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s1)))) s1))) (list (fn-rtc-e-id e) (fn-rtc-e-inc e) (list (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s1)))) (+ 1 (fn-rtc-b-gen (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s1)))) s1))) 0 (len (fn-rtc-b-bytes (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s1)))) s1))))))))
                  (:instance fn-rtc-rearm-foreign-octets (s1 (mv-nth 0 (fn-rtc-deliver (fn-rtc-end-use s1 e) j (fn-rtc-get 4 (fn-rtc-b-owner (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s1)))) s1))) (fn-rtc-ev :handed (fn-rtc-delivered-outcome (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s1)) e) j (fn-rtc-get 4 (fn-rtc-b-owner (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s1)))) s1))) (list (fn-rtc-e-id e) (fn-rtc-e-inc e) (list (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s1)))) (+ 1 (fn-rtc-b-gen (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s1)))) s1))) 0 (len (fn-rtc-b-bytes (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s1)))) s1)))))) q))) (s2 (mv-nth 0 (fn-rtc-deliver (fn-rtc-end-use s2 e) j (fn-rtc-get 4 (fn-rtc-b-owner (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s1)))) s1))) (fn-rtc-ev :handed (fn-rtc-delivered-outcome (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s1)) e) j (fn-rtc-get 4 (fn-rtc-b-owner (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s1)))) s1))) (list (fn-rtc-e-id e) (fn-rtc-e-inc e) (list (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s1)))) (+ 1 (fn-rtc-b-gen (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s1)))) s1))) 0 (len (fn-rtc-b-bytes (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s1)))) s1)))))) q)))))))))

(local
 (defthm fn-rtc-step-foreign-octets-accept
   (implies (and (fn-rtc-invp s1) (fn-rtc-same-but-foreign-octets-p j s1 s2) (equal j (fn-rtc-target s1 e)) (fn-rtc-acts-on-p s1 e) (not (fn-rtc-hand-delivers-p s1 e)) (equal (fn-rtc-e-kind e) :accept))
            (and (equal (mv-nth 1 (fn-rtc-step s1 e q)) (mv-nth 1 (fn-rtc-step s2 e q)))
                 (fn-rtc-same-but-foreign-octets-p j (mv-nth 0 (fn-rtc-step s1 e q))
                                                      (mv-nth 0 (fn-rtc-step s2 e q)))))
   :hints (("Goal" :in-theory
            (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
             '(fn-rtc-step-is-step-state fn-rtc-step-state fn-rtc-step-actions-is fn-rtc-step-actions fn-rtc-step*
               fn-rtc-target fn-rtc-hand-to fn-rtc-slots-of-end-use-when-acting
               (:executable-counterpart member-equal) (:executable-counterpart equal)))
            :use (fn-rtc-foreign-octets-plain-fields
                  fn-rtc-foreign-octets-step-control
                  fn-rtc-end-use-foreign-octets
                  (:instance fn-rtc-delivered-outcome-done (u (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s1))))
                  (:instance fn-rtc-accept-branch-foreign-octets (s1 (fn-rtc-end-use s1 e)) (s2 (fn-rtc-end-use s2 e)) (out (fn-rtc-delivered-outcome (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s1)) e)))
                  (:instance fn-rtc-accept-not-done-foreign-octets (s1 (fn-rtc-end-use s1 e)) (s2 (fn-rtc-end-use s2 e)) (out (fn-rtc-delivered-outcome (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s1)) e))))))))

(local
 (defthm fn-rtc-step-foreign-octets-close
   (implies (and (fn-rtc-invp s1) (fn-rtc-same-but-foreign-octets-p j s1 s2) (equal j (fn-rtc-target s1 e)) (fn-rtc-acts-on-p s1 e) (not (fn-rtc-hand-delivers-p s1 e)) (equal (fn-rtc-e-kind e) :close))
            (and (equal (mv-nth 1 (fn-rtc-step s1 e q)) (mv-nth 1 (fn-rtc-step s2 e q)))
                 (fn-rtc-same-but-foreign-octets-p j (mv-nth 0 (fn-rtc-step s1 e q))
                                                      (mv-nth 0 (fn-rtc-step s2 e q)))))
   :hints (("Goal" :in-theory
            (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
             '(fn-rtc-step-is-step-state fn-rtc-step-state fn-rtc-step-actions-is fn-rtc-step-actions fn-rtc-step*
               fn-rtc-target fn-rtc-hand-to fn-rtc-slots-of-end-use-when-acting
               (:executable-counterpart member-equal) (:executable-counterpart equal)))
            :use (fn-rtc-foreign-octets-plain-fields
                  fn-rtc-foreign-octets-step-control
                  fn-rtc-end-use-foreign-octets
                  (:instance fn-rtc-close-branch-foreign-octets (s1 (fn-rtc-end-use s1 e)) (s2 (fn-rtc-end-use s2 e)) (id (fn-rtc-e-id e)) (inc (fn-rtc-e-inc e))))))))

(local
 (defthm fn-rtc-step-foreign-octets-deliver
   (implies (and (fn-rtc-invp s1) (fn-rtc-same-but-foreign-octets-p j s1 s2) (equal j (fn-rtc-target s1 e)) (fn-rtc-acts-on-p s1 e) (not (fn-rtc-hand-delivers-p s1 e)) (not (equal (fn-rtc-e-kind e) :accept)) (not (equal (fn-rtc-e-kind e) :close)))
            (and (equal (mv-nth 1 (fn-rtc-step s1 e q)) (mv-nth 1 (fn-rtc-step s2 e q)))
                 (fn-rtc-same-but-foreign-octets-p j (mv-nth 0 (fn-rtc-step s1 e q))
                                                      (mv-nth 0 (fn-rtc-step s2 e q)))))
   :hints (("Goal" :in-theory
            (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
             '(fn-rtc-step-is-step-state fn-rtc-step-state fn-rtc-step-actions-is fn-rtc-step-actions fn-rtc-step*
               fn-rtc-target fn-rtc-hand-to fn-rtc-slots-of-end-use-when-acting
               (:executable-counterpart member-equal) (:executable-counterpart equal)))
            :use (fn-rtc-foreign-octets-plain-fields
                  fn-rtc-foreign-octets-step-control
                  fn-rtc-end-use-foreign-octets
                  fn-rtc-foreign-octets-hand-buffer
                  (:instance fn-rtc-acting-matches-use (s s1))
                  (:instance fn-rtc-deliver-foreign-octets (s1 (fn-rtc-end-use s1 e)) (s2 (fn-rtc-end-use s2 e)) (inc (fn-rtc-e-inc e)) (ev (fn-rtc-ev (fn-rtc-e-kind e) (if (equal (fn-rtc-get 0 (fn-rtc-delivered-outcome (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s1)) e)) :done) '(:failed :gone) (fn-rtc-delivered-outcome (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s1)) e)) j (fn-rtc-e-inc e) (list (list (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s1)))) (+ 1 (fn-rtc-b-gen (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s1)))) s1))) 0 (len (fn-rtc-b-bytes (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s1)))) s1))))))))
                  (:instance fn-rtc-deliver-foreign-octets (s1 (fn-rtc-end-use s1 e)) (s2 (fn-rtc-end-use s2 e)) (inc (fn-rtc-e-inc e)) (ev (fn-rtc-ev (fn-rtc-e-kind e) (fn-rtc-delivered-outcome (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s1)) e) j (fn-rtc-e-inc e) nil))))))))

(local
 (defthm fn-rtc-step-foreign-octets
   (implies (and (fn-rtc-invp s1) (fn-rtc-same-but-foreign-octets-p j s1 s2) (equal j (fn-rtc-target s1 e)))
            (and (equal (mv-nth 1 (fn-rtc-step s1 e q)) (mv-nth 1 (fn-rtc-step s2 e q)))
                 (fn-rtc-same-but-foreign-octets-p j (mv-nth 0 (fn-rtc-step s1 e q))
                                                      (mv-nth 0 (fn-rtc-step s2 e q)))))
   :hints (("Goal" :in-theory (theory 'minimal-theory)
            :use (fn-rtc-step-foreign-octets-inactive fn-rtc-step-foreign-octets-hand fn-rtc-step-foreign-octets-accept fn-rtc-step-foreign-octets-close fn-rtc-step-foreign-octets-deliver)))))

; T17a isolation of octets
(defthm fn-rtc-instances-see-no-foreign-octets
  (implies (and (fn-rtc-invp s) (fn-rtc-same-but-foreign-octets-p (fn-rtc-target s e) s s2))
           (and (equal (mv-nth 1 (fn-rtc-step s e q)) (mv-nth 1 (fn-rtc-step s2 e q)))
                (fn-rtc-same-but-foreign-octets-p (fn-rtc-target s e)
                                                  (mv-nth 0 (fn-rtc-step s e q))
                                                  (mv-nth 0 (fn-rtc-step s2 e q)))))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use ((:instance fn-rtc-step-foreign-octets (s1 s) (j (fn-rtc-target s e)))))))

(local
 (defun fn-rtc-visible-buffer (j cfg h b)
   (let ((o (fn-rtc-b-owner b)))
     (if (or (fn-rtc-of-slot-p o j) (and (equal o '(:free)) (equal (fn-rtc-home h cfg) j))) b :other))))

(local
 (defun fn-rtc-ranked-equal-p (xs ys)
   (if (consp xs)
       (and (consp ys)
            (equal (fn-rtc-get 0 (car xs)) (fn-rtc-get 0 (car ys)))
            (equal (fn-rtc-get 1 (car xs)) (fn-rtc-get 1 (car ys)))
            (equal (fn-rtc-get 2 (car xs)) (fn-rtc-get 2 (car ys)))
            (equal (fn-rtc-get 4 (car xs)) (fn-rtc-get 4 (car ys)))
            (fn-rtc-ranked-equal-p (cdr xs) (cdr ys)))
     (atom ys))))

(local
 (defthm fn-rtc-ranked-equal-is-ranked
   (equal (equal (fn-rtc-ranked xs i) (fn-rtc-ranked ys i)) (fn-rtc-ranked-equal-p xs ys))
   :hints (("Goal" :induct (list (fn-rtc-ranked xs i) (fn-rtc-ranked ys i))
            :in-theory (e/d (fn-rtc-ranked fn-rtc-ranked-equal-p) (fn-rtc-get))))))

(local
 (defthm fn-rtc-local-ranked-equal-parts
   (equal (equal (fn-rtc-local-ranked j s1) (fn-rtc-local-ranked j s2))
          (and (equal (fn-rtc-config s1) (fn-rtc-config s2))
               (equal (fn-rtc-slot j s1) (fn-rtc-slot j s2))
               (equal (fn-rtc-mstate j s1) (fn-rtc-mstate j s2))
               (fn-rtc-ranked-equal-p (fn-rtc-uses-of j (fn-rtc-uses s1)) (fn-rtc-uses-of j (fn-rtc-uses s2)))
               (equal (fn-rtc-local-buffers j (fn-rtc-config s1) 0 (fn-rtc-pool s1))
                      (fn-rtc-local-buffers j (fn-rtc-config s2) 0 (fn-rtc-pool s2)))))
   :hints (("Goal" :in-theory
            (e/d (fn-rtc-local-ranked) (fn-rtc-ranked fn-rtc-ranked-equal-p fn-rtc-uses-of fn-rtc-local-buffers))))))

(local
 (defthm fn-rtc-ranked-equal-kind-out
   (implies (fn-rtc-ranked-equal-p xs ys)
            (equal (fn-rtc-kind-out-p kind id inc xs) (fn-rtc-kind-out-p kind id inc ys)))
   :hints (("Goal" :induct (fn-rtc-ranked-equal-p xs ys)
            :in-theory (e/d (fn-rtc-ranked-equal-p fn-rtc-kind-out-p) (fn-rtc-get))))))

(local
 (defthm fn-rtc-kind-out-of-uses-of
   (equal (fn-rtc-kind-out-p kind j inc (fn-rtc-uses-of j uses)) (fn-rtc-kind-out-p kind j inc uses))
   :hints (("Goal" :in-theory (disable fn-rtc-get)))))

(local
 (defthm fn-rtc-local-buffers-consp
   (equal (consp (fn-rtc-local-buffers j cfg h pool)) (consp pool))
   :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-rtc-local-buffers))))))

(local
 (defthm fn-rtc-local-buffers-nonnil
   (iff (fn-rtc-local-buffers j cfg h pool) (consp pool))
   :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-rtc-local-buffers))))))

(local
 (defthm fn-rtc-visible-buffer-nonother
   (implies (not (equal (fn-rtc-visible-buffer j cfg h b) :other))
            (equal (fn-rtc-visible-buffer j cfg h b) b))
   :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-rtc-visible-buffer))))))

(local
 (defun fn-rtc-pool-index-pair-induct (k h p1 p2)
   (declare (xargs :measure (len p1)))
   (if (and (consp p1) (not (zp k)))
       (fn-rtc-pool-index-pair-induct (- k 1) (+ h 1) (cdr p1) (cdr p2))
     (list h p1 p2))))

(local
 (defthm fn-rtc-local-buffers-get
   (implies (and (natp h) (equal (fn-rtc-local-buffers j cfg h p1) (fn-rtc-local-buffers j cfg h p2)))
            (equal (fn-rtc-visible-buffer j cfg (+ h (nfix k)) (fn-rtc-get k p1))
                   (fn-rtc-visible-buffer j cfg (+ h (nfix k)) (fn-rtc-get k p2))))
   :hints (("Goal" :induct (fn-rtc-pool-index-pair-induct k h p1 p2)
            :in-theory (e/d (fn-rtc-local-buffers fn-rtc-visible-buffer fn-rtc-get)
                             (fn-rtc-of-slot-p fn-rtc-b-owner fn-rtc-home))))))

(local
 (defthm fn-rtc-local-buffers-set
   (implies (equal (fn-rtc-local-buffers j cfg h p1) (fn-rtc-local-buffers j cfg h p2))
            (equal (fn-rtc-local-buffers j cfg h (fn-rtc-set k b p1))
                   (fn-rtc-local-buffers j cfg h (fn-rtc-set k b p2))))
   :hints (("Goal" :induct (fn-rtc-pool-index-pair-induct k h p1 p2)
            :in-theory (e/d (fn-rtc-local-buffers fn-rtc-set)
                             (fn-rtc-of-slot-p fn-rtc-b-owner fn-rtc-home))))))

(local
 (defthm fn-rtc-visible-buffer-unhides
   (implies (or (fn-rtc-of-slot-p (fn-rtc-b-owner b) j)
                (and (equal (fn-rtc-b-owner b) '(:free)) (equal (fn-rtc-home h cfg) j)))
            (and (equal (fn-rtc-visible-buffer j cfg h b) b) (not (equal b :other))))
   :hints (("Goal" :in-theory (e/d (fn-rtc-visible-buffer fn-rtc-of-slot-p) (fn-rtc-b-owner fn-rtc-home))))))

(local
 (defthm fn-rtc-visible-buffer-equal-unhides
   (implies (and (equal (fn-rtc-visible-buffer j cfg h b1) (fn-rtc-visible-buffer j cfg h b2))
                 (not (equal (fn-rtc-visible-buffer j cfg h b1) :other)))
            (equal b1 b2))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (fn-rtc-visible-buffer) (fn-rtc-of-slot-p fn-rtc-b-owner fn-rtc-home))))))

(local
 (defthm fn-rtc-local-view-pool
   (equal (fn-rtc-view-pool j inc cfg h (fn-rtc-local-buffers j cfg h pool))
          (fn-rtc-view-pool j inc cfg h pool))
   :hints (("Goal" :induct (fn-rtc-local-buffers j cfg h pool)
            :in-theory (e/d (fn-rtc-view-pool fn-rtc-view-own-p fn-rtc-view-mine-p fn-rtc-local-buffers fn-rtc-of-slot-p)
                             (fn-rtc-b-owner fn-rtc-b-gen fn-rtc-b-bytes fn-rtc-home))))))

(local
 (defthm fn-rtc-local-ranked-visible
   (implies (and (natp h) (equal (fn-rtc-local-ranked j s1) (fn-rtc-local-ranked j s2)))
            (equal (fn-rtc-visible-buffer j (fn-rtc-config s1) h (fn-rtc-buffer h s1))
                   (fn-rtc-visible-buffer j (fn-rtc-config s2) h (fn-rtc-buffer h s2))))
   :hints (("Goal" :in-theory
            (e/d (fn-rtc-buffer) (fn-rtc-pool-is-buffers fn-rtc-local-ranked fn-rtc-ranked fn-rtc-ranked-equal-p
                                 fn-rtc-local-buffers fn-rtc-visible-buffer fn-rtc-get))
            :use ((:instance fn-rtc-local-buffers-get (h 0) (k h) (cfg (fn-rtc-config s1))
                    (p1 (fn-rtc-pool s1)) (p2 (fn-rtc-pool s2))))))))

(local
 (defthm fn-rtc-local-ranked-control
   (implies (equal (fn-rtc-local-ranked j s1) (fn-rtc-local-ranked j s2))
            (and (equal (fn-rtc-live-p j inc s1) (fn-rtc-live-p j inc s2))
                 (equal (fn-rtc-current-p j inc s1) (fn-rtc-current-p j inc s2))
                 (equal (fn-rtc-hand-target-okp extra j s1) (fn-rtc-hand-target-okp extra j s2))
                 (equal (fn-rtc-kind-out-p kind j inc (fn-rtc-uses s1))
                        (fn-rtc-kind-out-p kind j inc (fn-rtc-uses s2)))))
   :hints (("Goal" :in-theory
            (union-theories (theory 'minimal-theory)
             '(fn-rtc-local-ranked-equal-parts fn-rtc-live-p fn-rtc-current-p fn-rtc-hand-target-okp
               fn-rtc-kind-out-of-uses-of))
            :use ((:instance fn-rtc-ranked-equal-kind-out (id j)
                    (xs (fn-rtc-uses-of j (fn-rtc-uses s1))) (ys (fn-rtc-uses-of j (fn-rtc-uses s2)))))))))

(local
 (defthm fn-rtc-local-ranked-view
   (implies (equal (fn-rtc-local-ranked j s1) (fn-rtc-local-ranked j s2))
            (equal (fn-rtc-view j inc s1) (fn-rtc-view j inc s2)))
   :hints (("Goal" :in-theory
            (union-theories (theory 'minimal-theory) '(fn-rtc-view fn-rtc-local-ranked-equal-parts))
            :use ((:instance fn-rtc-local-view-pool (h 0) (cfg (fn-rtc-config s1)) (pool (fn-rtc-pool s1)))
                  (:instance fn-rtc-local-view-pool (h 0) (cfg (fn-rtc-config s2)) (pool (fn-rtc-pool s2))))))))

(local
 (defthm fn-rtc-local-ranked-submit-okp
   (implies (equal (fn-rtc-local-ranked j s1) (fn-rtc-local-ranked j s2))
            (equal (fn-rtc-submit-okp kind hd j inc s1) (fn-rtc-submit-okp kind hd j inc s2)))
   :hints (("Goal" :in-theory
            (union-theories (theory 'minimal-theory)
             '(fn-rtc-submit-okp fn-rtc-local-ranked-equal-parts fn-rtc-visible-buffer fn-rtc-of-slot-p
               fn-rtc-owner-equality-fields fn-rtc-get-of-cons car-cons cdr-cons natp nfix
               (:type-prescription fn-rtc-h-buf)
               (:executable-counterpart equal) (:executable-counterpart member-equal)
               (:executable-counterpart fn-rtc-b-owner) (:executable-counterpart fn-rtc-get)
               (:executable-counterpart zp) (:executable-counterpart unary--) (:executable-counterpart binary-+)))
            :use ((:instance fn-rtc-local-ranked-visible (h (fn-rtc-h-buf hd))))))))

(local
 (defthm fn-rtc-live-index-in-slots
   (implies (fn-rtc-live-p j inc s) (< (nfix j) (len (fn-rtc-slots s))))
   :rule-classes :linear
   :hints (("Goal" :in-theory (e/d (fn-rtc-live-p fn-rtc-slot) (fn-rtc-slots-is-slot fn-rtc-get))
            :use ((:instance fn-rtc-get-out-of-range (i j) (l (fn-rtc-slots s))))))))

(local
 (defthm fn-rtc-request-local-ranked-buffer
   (implies (and (member-eq (fn-rtc-get 0 r) '(:acquire :write :release)) (natp j) (equal (fn-rtc-local-ranked j s1) (fn-rtc-local-ranked j s2)))
            (and (equal (fn-rtc-local-ranked j (mv-nth 0 (fn-rtc-request r j inc s1)))
                        (fn-rtc-local-ranked j (mv-nth 0 (fn-rtc-request r j inc s2))))
                 (fn-rtc-ranked-equal-p (mv-nth 1 (fn-rtc-request r j inc s1))
                                        (mv-nth 1 (fn-rtc-request r j inc s2)))))
   :hints (("Goal" :in-theory
            (union-theories (theory 'minimal-theory)
             '(fn-rtc-request fn-rtc-req-acquire fn-rtc-req-write fn-rtc-req-release fn-rtc-req-close fn-rtc-req-cancel fn-rtc-req-submit
               fn-rtc-local-ranked-equal-parts fn-rtc-ranked-equal-p fn-rtc-uses-of
               fn-rtc-visible-buffer fn-rtc-of-slot-p fn-rtc-owner-equality-fields
               fn-rtc-with-accessors fn-rtc-slot-of-with fn-rtc-mstate-of-with fn-rtc-issue-frame fn-rtc-next-op-of-with
               fn-rtc-live-index-in-slots fn-rtc-slot-accessors fn-rtc-buffer-accessors fn-rtc-get-of-cons
               fn-rtc-buffer-of-non-natp fn-rtc-get-of-non-natp nfix natp car-cons cdr-cons
               (:type-prescription fn-rtc-h-buf)
               (:executable-counterpart fn-rtc-b-owner) (:executable-counterpart fn-rtc-get)
               (:executable-counterpart member-equal) (:executable-counterpart equal)
               (:executable-counterpart zp) (:executable-counterpart binary-+) (:executable-counterpart unary--)))
            :use ((:instance fn-rtc-local-buffers-set (cfg (fn-rtc-config s1)) (h 0) (p1 (fn-rtc-pool s1)) (p2 (fn-rtc-pool s2)) (k (fn-rtc-get 1 r)) (b (cond ((equal (fn-rtc-get 0 r) :acquire) (list (+ 1 (fn-rtc-b-gen (fn-rtc-buffer (fn-rtc-get 1 r) s1))) (list :workspace j inc) nil)) ((equal (fn-rtc-get 0 r) :write) (list (fn-rtc-get 2 r) (list :workspace j inc) (fn-rtc-splice (fn-rtc-b-bytes (fn-rtc-buffer (fn-rtc-get 1 r) s1)) (fn-rtc-get 3 r) (fn-rtc-get 4 r)))) (t (list (fn-rtc-get 2 r) '(:free) (fn-rtc-b-bytes (fn-rtc-buffer (fn-rtc-get 1 r) s1)))))))
                  (:instance fn-rtc-local-ranked-visible (h (fn-rtc-get 1 r))))))))

(local
 (defthm fn-rtc-request-local-ranked-control
   (implies (and (member-eq (fn-rtc-get 0 r) '(:close :cancel)) (natp j) (equal (fn-rtc-local-ranked j s1) (fn-rtc-local-ranked j s2)))
            (and (equal (fn-rtc-local-ranked j (mv-nth 0 (fn-rtc-request r j inc s1)))
                        (fn-rtc-local-ranked j (mv-nth 0 (fn-rtc-request r j inc s2))))
                 (fn-rtc-ranked-equal-p (mv-nth 1 (fn-rtc-request r j inc s1))
                                        (mv-nth 1 (fn-rtc-request r j inc s2)))))
   :hints (("Goal" :in-theory
            (union-theories (theory 'minimal-theory)
             '(fn-rtc-request fn-rtc-req-acquire fn-rtc-req-write fn-rtc-req-release fn-rtc-req-close fn-rtc-req-cancel fn-rtc-req-submit
               fn-rtc-local-ranked-equal-parts fn-rtc-ranked-equal-p fn-rtc-uses-of
               fn-rtc-visible-buffer fn-rtc-of-slot-p fn-rtc-owner-equality-fields
               fn-rtc-with-accessors fn-rtc-slot-of-with fn-rtc-mstate-of-with fn-rtc-issue-frame fn-rtc-next-op-of-with
               fn-rtc-live-index-in-slots fn-rtc-slot-accessors fn-rtc-buffer-accessors fn-rtc-get-of-cons
               fn-rtc-buffer-of-non-natp fn-rtc-get-of-non-natp nfix natp car-cons cdr-cons
               (:type-prescription fn-rtc-h-buf)
               (:executable-counterpart fn-rtc-b-owner) (:executable-counterpart fn-rtc-get)
               (:executable-counterpart member-equal) (:executable-counterpart equal)
               (:executable-counterpart zp) (:executable-counterpart binary-+) (:executable-counterpart unary--)))
            :use ((:instance fn-rtc-live-index-in-slots (s s1))
                  (:instance fn-rtc-live-index-in-slots (s s2))
                  (:instance fn-rtc-local-ranked-control (kind (fn-rtc-get 1 r)) (extra (fn-rtc-get 3 r))))))))

(local
 (defthm fn-rtc-request-local-ranked-submit
   (implies (and (equal (fn-rtc-get 0 r) :submit) (natp j) (equal (fn-rtc-local-ranked j s1) (fn-rtc-local-ranked j s2)))
            (and (equal (fn-rtc-local-ranked j (mv-nth 0 (fn-rtc-request r j inc s1)))
                        (fn-rtc-local-ranked j (mv-nth 0 (fn-rtc-request r j inc s2))))
                 (fn-rtc-ranked-equal-p (mv-nth 1 (fn-rtc-request r j inc s1))
                                        (mv-nth 1 (fn-rtc-request r j inc s2)))))
   :hints (("Goal" :in-theory
            (union-theories (theory 'minimal-theory)
             '(fn-rtc-request fn-rtc-req-acquire fn-rtc-req-write fn-rtc-req-release fn-rtc-req-close fn-rtc-req-cancel fn-rtc-req-submit
               fn-rtc-local-ranked-equal-parts fn-rtc-ranked-equal-p fn-rtc-uses-of
               fn-rtc-visible-buffer fn-rtc-of-slot-p fn-rtc-owner-equality-fields
               fn-rtc-with-accessors fn-rtc-slot-of-with fn-rtc-mstate-of-with fn-rtc-issue-frame fn-rtc-next-op-of-with
               fn-rtc-live-index-in-slots fn-rtc-slot-accessors fn-rtc-buffer-accessors fn-rtc-get-of-cons
               fn-rtc-buffer-of-non-natp fn-rtc-get-of-non-natp nfix natp car-cons cdr-cons
               (:type-prescription fn-rtc-h-buf)
               (:executable-counterpart fn-rtc-b-owner) (:executable-counterpart fn-rtc-get)
               (:executable-counterpart member-equal) (:executable-counterpart equal)
               (:executable-counterpart zp) (:executable-counterpart binary-+) (:executable-counterpart unary--)))
            :use ((:instance fn-rtc-local-buffers-set (cfg (fn-rtc-config s1)) (h 0) (p1 (fn-rtc-pool s1)) (p2 (fn-rtc-pool s2)) (k (fn-rtc-h-buf (fn-rtc-get 2 r))) (b (list (fn-rtc-b-gen (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-get 2 r)) s1)) (if (equal (fn-rtc-get 1 r) :hand) (list :handed j inc (fn-rtc-get 0 (fn-rtc-get 3 r)) (fn-rtc-get 1 (fn-rtc-get 3 r))) (list :leased j inc (if (member-eq (fn-rtc-get 1 r) *fn-rtc-in-kinds*) :in :out))) (fn-rtc-b-bytes (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-get 2 r)) s1)))))
                  (:instance fn-rtc-local-ranked-control (kind (fn-rtc-get 1 r)) (extra (fn-rtc-get 3 r)))
                  (:instance fn-rtc-local-ranked-submit-okp (kind (fn-rtc-get 1 r)) (hd (fn-rtc-get 2 r)))
                  (:instance fn-rtc-local-ranked-visible (h (fn-rtc-h-buf (fn-rtc-get 2 r)))))))))

(local
 (defthm fn-rtc-request-local-ranked-other
   (implies (and (not (member-eq (fn-rtc-get 0 r) '(:acquire :write :release :close :cancel :submit))) (natp j) (equal (fn-rtc-local-ranked j s1) (fn-rtc-local-ranked j s2)))
            (and (equal (fn-rtc-local-ranked j (mv-nth 0 (fn-rtc-request r j inc s1)))
                        (fn-rtc-local-ranked j (mv-nth 0 (fn-rtc-request r j inc s2))))
                 (fn-rtc-ranked-equal-p (mv-nth 1 (fn-rtc-request r j inc s1))
                                        (mv-nth 1 (fn-rtc-request r j inc s2)))))
   :hints (("Goal" :in-theory
            (union-theories (theory 'minimal-theory)
             '(fn-rtc-request fn-rtc-req-acquire fn-rtc-req-write fn-rtc-req-release fn-rtc-req-close fn-rtc-req-cancel fn-rtc-req-submit
               fn-rtc-local-ranked-equal-parts fn-rtc-ranked-equal-p fn-rtc-uses-of
               fn-rtc-visible-buffer fn-rtc-of-slot-p fn-rtc-owner-equality-fields
               fn-rtc-with-accessors fn-rtc-slot-of-with fn-rtc-mstate-of-with fn-rtc-issue-frame fn-rtc-next-op-of-with
               fn-rtc-live-index-in-slots fn-rtc-slot-accessors fn-rtc-buffer-accessors fn-rtc-get-of-cons
               fn-rtc-buffer-of-non-natp fn-rtc-get-of-non-natp nfix natp car-cons cdr-cons
               (:type-prescription fn-rtc-h-buf)
               (:executable-counterpart fn-rtc-b-owner) (:executable-counterpart fn-rtc-get)
               (:executable-counterpart member-equal) (:executable-counterpart equal)
               (:executable-counterpart zp) (:executable-counterpart binary-+) (:executable-counterpart unary--)))
))))

(local
 (defthm fn-rtc-request-local-ranked
   (implies (and (natp j) (equal (fn-rtc-local-ranked j s1) (fn-rtc-local-ranked j s2)))
            (and (equal (fn-rtc-local-ranked j (mv-nth 0 (fn-rtc-request r j inc s1)))
                        (fn-rtc-local-ranked j (mv-nth 0 (fn-rtc-request r j inc s2))))
                 (fn-rtc-ranked-equal-p (mv-nth 1 (fn-rtc-request r j inc s1))
                                        (mv-nth 1 (fn-rtc-request r j inc s2)))))
   :hints (("Goal" :in-theory
            (union-theories (theory 'minimal-theory) '(member-equal car-cons cdr-cons (:executable-counterpart equal)))
            :use (fn-rtc-request-local-ranked-buffer fn-rtc-request-local-ranked-control fn-rtc-request-local-ranked-submit fn-rtc-request-local-ranked-other)))))

(local
 (defthm fn-rtc-ranked-equal-append
   (implies (and (fn-rtc-ranked-equal-p xs ys) (fn-rtc-ranked-equal-p zs ws))
            (fn-rtc-ranked-equal-p (append xs zs) (append ys ws)))
   :hints (("Goal" :induct (fn-rtc-ranked-equal-p xs ys)
            :in-theory (union-theories (theory 'minimal-theory) '(fn-rtc-ranked-equal-p binary-append car-cons cdr-cons))))))

(local
 (defthm fn-rtc-requests-local-ranked
   (implies (and (natp j) (equal (fn-rtc-local-ranked j s1) (fn-rtc-local-ranked j s2)))
            (and (equal (fn-rtc-local-ranked j (mv-nth 0 (fn-rtc-requests reqs j inc s1)))
                        (fn-rtc-local-ranked j (mv-nth 0 (fn-rtc-requests reqs j inc s2))))
                 (fn-rtc-ranked-equal-p (mv-nth 1 (fn-rtc-requests reqs j inc s1))
                                        (mv-nth 1 (fn-rtc-requests reqs j inc s2)))))
   :hints (("Goal" :induct (fn-rtc-requests-pair-induct reqs j inc s1 s2)
            :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
             '(fn-rtc-requests-pair-induct fn-rtc-requests fn-rtc-ranked-equal-append (:executable-counterpart fn-rtc-ranked-equal-p))))
           ("Subgoal *1/1" :use ((:instance fn-rtc-request-local-ranked (r (car reqs)))))
           ("Subgoal *1/2" :use ((:instance fn-rtc-request-local-ranked (r (car reqs))))))))

(local
 (defthm fn-rtc-local-ranked-with-mstate
   (implies (and (equal (fn-rtc-local-ranked j s1) (fn-rtc-local-ranked j s2))
                 (equal (len (fn-rtc-mstates s1)) (len (fn-rtc-mstates s2))))
            (equal (fn-rtc-local-ranked j (fn-rtc-with-mstate j m s1))
                   (fn-rtc-local-ranked j (fn-rtc-with-mstate j m s2))))
   :hints (("Goal" :in-theory
            (union-theories (theory 'minimal-theory)
             '(fn-rtc-local-ranked-equal-parts fn-rtc-with-accessors fn-rtc-slot-of-with fn-rtc-mstate-of-with))))))

(local
 (defthm fn-rtc-deliver-local-ranked
   (implies (and (natp j) (equal (fn-rtc-local-ranked j s1) (fn-rtc-local-ranked j s2))
                 (equal (len (fn-rtc-mstates s1)) (len (fn-rtc-mstates s2))))
            (and (equal (fn-rtc-local-ranked j (mv-nth 0 (fn-rtc-deliver s1 j inc ev q)))
                        (fn-rtc-local-ranked j (mv-nth 0 (fn-rtc-deliver s2 j inc ev q))))
                 (fn-rtc-ranked-equal-p (mv-nth 1 (fn-rtc-deliver s1 j inc ev q))
                                        (mv-nth 1 (fn-rtc-deliver s2 j inc ev q)))))
   :hints (("Goal" :in-theory
            (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth)) '(fn-rtc-deliver))
            :use (fn-rtc-local-ranked-view
                  fn-rtc-local-ranked-equal-parts
                  (:instance fn-rtc-local-ranked-with-mstate (m (mv-nth 0 (fn-rtc-m-step (fn-rtc-mstate j s1) ev (fn-rtc-view j inc s1) (nfix q)))))
                  (:instance fn-rtc-requests-local-ranked
                    (reqs (mv-nth 1 (fn-rtc-m-step (fn-rtc-mstate j s1) ev (fn-rtc-view j inc s1) (nfix q))))
                    (s1 (fn-rtc-with-mstate j (mv-nth 0 (fn-rtc-m-step (fn-rtc-mstate j s1) ev (fn-rtc-view j inc s1) (nfix q))) s1))
                    (s2 (fn-rtc-with-mstate j (mv-nth 0 (fn-rtc-m-step (fn-rtc-mstate j s1) ev (fn-rtc-view j inc s1) (nfix q))) s2))))))))

(local
 (defthm fn-rtc-request-config-is-constant
   (equal (fn-rtc-config (mv-nth 0 (fn-rtc-request r id inc s))) (fn-rtc-config s))
   :hints (("Goal" :in-theory
            (e/d (fn-rtc-request fn-rtc-req-acquire fn-rtc-req-write fn-rtc-req-release
                  fn-rtc-req-close fn-rtc-req-cancel fn-rtc-req-submit)
                 (fn-rtc-submit-okp fn-rtc-live-p fn-rtc-current-p fn-rtc-kind-out-p
                  fn-rtc-buffered-kind-p fn-rtc-hand-target-okp fn-rtc-kind-op
                  fn-rtc-b-owner fn-rtc-b-gen fn-rtc-b-bytes fn-rtc-h-buf fn-rtc-h-gen
                  fn-rtc-h-off fn-rtc-h-len fn-rtc-splice fn-cbor-octet-listp))))))

(local
 (defthm fn-rtc-requests-config-is-constant
   (equal (fn-rtc-config (mv-nth 0 (fn-rtc-requests reqs id inc s))) (fn-rtc-config s))
   :hints (("Goal" :induct (fn-rtc-requests reqs id inc s)
            :in-theory (e/d (fn-rtc-requests) (mv-nth fn-rtc-request))))))

(local
 (defun fn-rtc-buffer-transfer-frame-p (j cfg h b1 b2)
   (let ((x1 (fn-rtc-visible-buffer j cfg h b1)) (x2 (fn-rtc-visible-buffer j cfg h b2)))
     (or (equal x1 x2)
         (and (fn-rtc-others-or-incoming-p x1 j) (equal (fn-rtc-home h cfg) j)
              (equal (fn-rtc-b-owner x2) '(:free)) (equal x2 b2))
         (and (fn-rtc-others-or-incoming-p x1 j) (fn-rtc-others-or-incoming-p x2 j))))))

(local
 (defun fn-rtc-pool-transfer-frame-p (j cfg h p1 p2)
   (declare (xargs :measure (len p1)))
   (if (consp p1)
       (and (consp p2) (fn-rtc-buffer-transfer-frame-p j cfg h (car p1) (car p2))
            (fn-rtc-pool-transfer-frame-p j cfg (+ 1 h) (cdr p1) (cdr p2)))
     (atom p2))))

(local
 (defthm fn-rtc-pool-transfer-frame-is-local-returns
   (equal (fn-rtc-pool-transfer-frame-p j cfg h p1 p2)
          (fn-rtc-local-returns-p j cfg h (fn-rtc-local-buffers j cfg h p1)
                                          (fn-rtc-local-buffers j cfg h p2) p2))
   :hints (("Goal" :induct (fn-rtc-pool-transfer-frame-p j cfg h p1 p2)
            :in-theory (e/d (fn-rtc-pool-transfer-frame-p fn-rtc-buffer-transfer-frame-p fn-rtc-visible-buffer
                            fn-rtc-local-buffers fn-rtc-local-returns-p)
                           (fn-rtc-of-slot-p fn-rtc-others-or-incoming-p fn-rtc-home fn-rtc-b-owner))))))

(local
 (defthm fn-rtc-buffer-transfer-frame-refl (fn-rtc-buffer-transfer-frame-p j cfg h b b)))

(local
 (defthm fn-rtc-pool-transfer-frame-refl (fn-rtc-pool-transfer-frame-p j cfg h p p)
   :hints (("Goal" :in-theory (disable fn-rtc-pool-transfer-frame-is-local-returns fn-rtc-buffer-transfer-frame-p)))))

(local
 (defthm fn-rtc-buffer-transfer-frame-trans
   (implies (and (fn-rtc-buffer-transfer-frame-p j cfg h b1 b2) (fn-rtc-buffer-transfer-frame-p j cfg h b2 b3))
            (fn-rtc-buffer-transfer-frame-p j cfg h b1 b3))
   :hints (("Goal" :in-theory
            (e/d (fn-rtc-buffer-transfer-frame-p fn-rtc-others-or-incoming-p)
                 (fn-rtc-visible-buffer fn-rtc-b-owner fn-rtc-of-slot-p fn-rtc-home))))))

(local
 (defthm fn-rtc-pool-transfer-frame-trans
   (implies (and (fn-rtc-pool-transfer-frame-p j cfg h p1 p2) (fn-rtc-pool-transfer-frame-p j cfg h p2 p3))
            (fn-rtc-pool-transfer-frame-p j cfg h p1 p3))
   :hints (("Goal" :induct (list (fn-rtc-pool-transfer-frame-p j cfg h p1 p2)
                                 (fn-rtc-pool-transfer-frame-p j cfg h p2 p3))
            :in-theory (e/d (fn-rtc-pool-transfer-frame-p)
                             (fn-rtc-pool-transfer-frame-is-local-returns fn-rtc-buffer-transfer-frame-p))))))

(local
 (defthm fn-rtc-pool-transfer-frame-set
   (implies (and (natp h) (natp k)
                 (fn-rtc-buffer-transfer-frame-p j cfg (+ h k) (fn-rtc-get k pool) b))
            (fn-rtc-pool-transfer-frame-p j cfg h pool (fn-rtc-set k b pool)))
   :hints (("Goal" :induct (fn-rtc-pool-index-pair-induct k h pool pool)
            :in-theory (e/d (fn-rtc-pool-transfer-frame-p fn-rtc-get fn-rtc-set)
                             (fn-rtc-pool-transfer-frame-is-local-returns fn-rtc-buffer-transfer-frame-p
                              fn-rtc-pool-transfer-frame-trans))))))

(local
 (defthm fn-rtc-pool-transfer-frame-update
   (implies (and (natp k) (fn-rtc-buffer-transfer-frame-p j cfg k (fn-rtc-get k pool) b))
            (fn-rtc-pool-transfer-frame-p j cfg 0 pool (fn-rtc-set k b pool)))
   :hints (("Goal" :in-theory
            (disable fn-rtc-pool-transfer-frame-p fn-rtc-pool-transfer-frame-is-local-returns
                     fn-rtc-buffer-transfer-frame-p fn-rtc-get fn-rtc-set fn-rtc-pool-transfer-frame-set)
            :use ((:instance fn-rtc-pool-transfer-frame-set (h 0)))))))

(local
 (defthm fn-rtc-foreign-workspace-update-frame
   (implies (and (not (equal id j)) (equal (fn-rtc-b-owner b) (list :workspace id inc)))
            (fn-rtc-buffer-transfer-frame-p j cfg h b (list g (list :workspace id inc) bytes)))
   :hints (("Goal" :in-theory
            (e/d (fn-rtc-buffer-transfer-frame-p fn-rtc-visible-buffer fn-rtc-of-slot-p fn-rtc-others-or-incoming-p)
                 (fn-rtc-b-owner fn-rtc-b-gen fn-rtc-b-bytes fn-rtc-home))))))

(local
 (defthm fn-rtc-request-pool-transfer-frame-buffer
   (implies (and (member-eq (fn-rtc-get 0 r) '(:acquire :write :release)) (natp id) (not (equal id j)))
            (fn-rtc-pool-transfer-frame-p j (fn-rtc-config s) 0 (fn-rtc-pool s)
                                          (fn-rtc-pool (mv-nth 0 (fn-rtc-request r id inc s)))))
   :hints (("Goal" :in-theory
            (union-theories (theory 'minimal-theory)
             '(fn-rtc-request fn-rtc-req-acquire fn-rtc-req-write fn-rtc-req-release fn-rtc-req-close fn-rtc-req-cancel fn-rtc-req-submit
               fn-rtc-foreign-workspace-update-frame fn-rtc-with-accessors fn-rtc-issue-frame fn-rtc-pool-transfer-frame-update fn-rtc-pool-transfer-frame-refl
               fn-rtc-buffer-transfer-frame-p fn-rtc-visible-buffer fn-rtc-others-or-incoming-p fn-rtc-of-slot-p
               fn-rtc-pool-is-buffers fn-rtc-buffer-accessors fn-rtc-owner-equality-fields fn-rtc-get-of-cons
               fn-rtc-buffer-of-non-natp fn-rtc-get-of-non-natp nfix natp zp-open car-cons cdr-cons
               (:type-prescription fn-rtc-h-buf)
               (:executable-counterpart fn-rtc-get) (:executable-counterpart fn-rtc-b-owner)
               (:executable-counterpart equal) (:executable-counterpart member-equal)
               (:executable-counterpart zp) (:executable-counterpart unary--) (:executable-counterpart binary-+)))
            :use ((:instance fn-rtc-pool-transfer-frame-update (cfg (fn-rtc-config s)) (pool (fn-rtc-pool s))
                    (k (fn-rtc-get 1 r)) (b (list (fn-rtc-get 2 r) (list :workspace id inc)
                         (fn-rtc-splice (fn-rtc-b-bytes (fn-rtc-buffer (fn-rtc-get 1 r) s)) (fn-rtc-get 3 r) (fn-rtc-get 4 r)))))
                  (:instance fn-rtc-pool-transfer-frame-update (cfg (fn-rtc-config s)) (pool (fn-rtc-pool s)) (k (fn-rtc-get 1 r)) (b (list (fn-rtc-get 2 r) '(:free) (fn-rtc-b-bytes (fn-rtc-buffer (fn-rtc-get 1 r) s)))))
                  (:instance fn-rtc-pool-transfer-frame-update (cfg (fn-rtc-config s)) (pool (fn-rtc-pool s)) (k (fn-rtc-get 1 r)) (b (list (+ 1 (fn-rtc-b-gen (fn-rtc-buffer (fn-rtc-get 1 r) s))) (list :workspace id inc) nil))))))))

(local
 (defthm fn-rtc-request-pool-transfer-frame-control
   (implies (and (member-eq (fn-rtc-get 0 r) '(:close :cancel)) (natp id) (not (equal id j)))
            (fn-rtc-pool-transfer-frame-p j (fn-rtc-config s) 0 (fn-rtc-pool s)
                                          (fn-rtc-pool (mv-nth 0 (fn-rtc-request r id inc s)))))
   :hints (("Goal" :in-theory
            (union-theories (theory 'minimal-theory)
             '(fn-rtc-request fn-rtc-req-acquire fn-rtc-req-write fn-rtc-req-release fn-rtc-req-close fn-rtc-req-cancel fn-rtc-req-submit
               fn-rtc-foreign-workspace-update-frame fn-rtc-with-accessors fn-rtc-issue-frame fn-rtc-pool-transfer-frame-update fn-rtc-pool-transfer-frame-refl
               fn-rtc-buffer-transfer-frame-p fn-rtc-visible-buffer fn-rtc-others-or-incoming-p fn-rtc-of-slot-p
               fn-rtc-pool-is-buffers fn-rtc-buffer-accessors fn-rtc-owner-equality-fields fn-rtc-get-of-cons
               fn-rtc-buffer-of-non-natp fn-rtc-get-of-non-natp nfix natp zp-open car-cons cdr-cons
               (:type-prescription fn-rtc-h-buf)
               (:executable-counterpart fn-rtc-get) (:executable-counterpart fn-rtc-b-owner)
               (:executable-counterpart equal) (:executable-counterpart member-equal)
               (:executable-counterpart zp) (:executable-counterpart unary--) (:executable-counterpart binary-+)))
))))

(local
 (defthm fn-rtc-request-pool-transfer-frame-submit
   (implies (and (equal (fn-rtc-get 0 r) :submit) (natp id) (not (equal id j)))
            (fn-rtc-pool-transfer-frame-p j (fn-rtc-config s) 0 (fn-rtc-pool s)
                                          (fn-rtc-pool (mv-nth 0 (fn-rtc-request r id inc s)))))
   :hints (("Goal" :in-theory
            (union-theories (theory 'minimal-theory)
             '(fn-rtc-request fn-rtc-req-acquire fn-rtc-req-write fn-rtc-req-release fn-rtc-req-close fn-rtc-req-cancel fn-rtc-req-submit
               fn-rtc-foreign-workspace-update-frame fn-rtc-with-accessors fn-rtc-issue-frame fn-rtc-pool-transfer-frame-update fn-rtc-pool-transfer-frame-refl
               fn-rtc-buffer-transfer-frame-p fn-rtc-visible-buffer fn-rtc-others-or-incoming-p fn-rtc-of-slot-p
               fn-rtc-pool-is-buffers fn-rtc-buffer-accessors fn-rtc-owner-equality-fields fn-rtc-get-of-cons
               fn-rtc-buffer-of-non-natp fn-rtc-get-of-non-natp nfix natp zp-open car-cons cdr-cons
               (:type-prescription fn-rtc-h-buf)
               (:executable-counterpart fn-rtc-get) (:executable-counterpart fn-rtc-b-owner)
               (:executable-counterpart equal) (:executable-counterpart member-equal)
               (:executable-counterpart zp) (:executable-counterpart unary--) (:executable-counterpart binary-+)))
            :use ((:instance fn-rtc-pool-transfer-frame-update (cfg (fn-rtc-config s)) (pool (fn-rtc-pool s)) (k (fn-rtc-h-buf (fn-rtc-get 2 r))) (b (list (fn-rtc-b-gen (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-get 2 r)) s)) (if (equal (fn-rtc-get 1 r) :hand) (list :handed id inc (fn-rtc-get 0 (fn-rtc-get 3 r)) (fn-rtc-get 1 (fn-rtc-get 3 r))) (list :leased id inc (if (member-eq (fn-rtc-get 1 r) *fn-rtc-in-kinds*) :in :out))) (fn-rtc-b-bytes (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-get 2 r)) s)))))
                  (:instance fn-rtc-hand-submit-okp-owner (hd (fn-rtc-get 2 r))))))))

(local
 (defthm fn-rtc-request-pool-transfer-frame-other
   (implies (and (not (member-eq (fn-rtc-get 0 r) '(:acquire :write :release :close :cancel :submit))) (natp id) (not (equal id j)))
            (fn-rtc-pool-transfer-frame-p j (fn-rtc-config s) 0 (fn-rtc-pool s)
                                          (fn-rtc-pool (mv-nth 0 (fn-rtc-request r id inc s)))))
   :hints (("Goal" :in-theory
            (union-theories (theory 'minimal-theory)
             '(fn-rtc-request fn-rtc-req-acquire fn-rtc-req-write fn-rtc-req-release fn-rtc-req-close fn-rtc-req-cancel fn-rtc-req-submit
               fn-rtc-foreign-workspace-update-frame fn-rtc-with-accessors fn-rtc-issue-frame fn-rtc-pool-transfer-frame-update fn-rtc-pool-transfer-frame-refl
               fn-rtc-buffer-transfer-frame-p fn-rtc-visible-buffer fn-rtc-others-or-incoming-p fn-rtc-of-slot-p
               fn-rtc-pool-is-buffers fn-rtc-buffer-accessors fn-rtc-owner-equality-fields fn-rtc-get-of-cons
               fn-rtc-buffer-of-non-natp fn-rtc-get-of-non-natp nfix natp zp-open car-cons cdr-cons
               (:type-prescription fn-rtc-h-buf)
               (:executable-counterpart fn-rtc-get) (:executable-counterpart fn-rtc-b-owner)
               (:executable-counterpart equal) (:executable-counterpart member-equal)
               (:executable-counterpart zp) (:executable-counterpart unary--) (:executable-counterpart binary-+)))
))))

(local
 (defthm fn-rtc-request-pool-transfer-frame
   (implies (and (natp id) (not (equal id j)))
            (fn-rtc-pool-transfer-frame-p j (fn-rtc-config s) 0 (fn-rtc-pool s)
                                          (fn-rtc-pool (mv-nth 0 (fn-rtc-request r id inc s)))))
   :hints (("Goal" :in-theory
            (union-theories (theory 'minimal-theory) '(member-equal car-cons cdr-cons (:executable-counterpart equal)))
            :use (fn-rtc-request-pool-transfer-frame-buffer fn-rtc-request-pool-transfer-frame-control fn-rtc-request-pool-transfer-frame-submit fn-rtc-request-pool-transfer-frame-other)))))

(local
 (defthm fn-rtc-request-chain-pool-frame
   (implies (and (natp id) (not (equal id j)) (fn-rtc-pool-transfer-frame-p j (fn-rtc-config s) 0 p (fn-rtc-pool s)))
            (fn-rtc-pool-transfer-frame-p j (fn-rtc-config s) 0 p
                                          (fn-rtc-pool (mv-nth 0 (fn-rtc-request r id inc s)))))
   :hints (("Goal" :in-theory (theory 'minimal-theory)
            :use (fn-rtc-request-pool-transfer-frame
                  (:instance fn-rtc-pool-transfer-frame-trans (cfg (fn-rtc-config s)) (h 0)
                    (p1 p) (p2 (fn-rtc-pool s)) (p3 (fn-rtc-pool (mv-nth 0 (fn-rtc-request r id inc s))))))))))

(local
 (defthm fn-rtc-requests-chain-pool-frame
   (implies (and (natp id) (not (equal id j)) (fn-rtc-pool-transfer-frame-p j (fn-rtc-config s) 0 p (fn-rtc-pool s)))
            (fn-rtc-pool-transfer-frame-p j (fn-rtc-config s) 0 p
                                          (fn-rtc-pool (mv-nth 0 (fn-rtc-requests reqs id inc s)))))
   :hints (("Goal" :induct (fn-rtc-requests reqs id inc s)
            :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
             '(fn-rtc-requests fn-rtc-request-chain-pool-frame fn-rtc-request-config-is-constant))))))

(local
 (defthm fn-rtc-deliver-pool-transfer-frame
   (implies (and (natp id) (not (equal id j)))
            (fn-rtc-pool-transfer-frame-p j (fn-rtc-config s) 0 (fn-rtc-pool s)
                                          (fn-rtc-pool (mv-nth 0 (fn-rtc-deliver s id inc ev q)))))
   :hints (("Goal" :in-theory
            (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
             '(fn-rtc-deliver fn-rtc-with-accessors fn-rtc-pool-transfer-frame-refl))
            :use ((:instance fn-rtc-requests-chain-pool-frame (p (fn-rtc-pool s))
                    (s (fn-rtc-with-mstate id (mv-nth 0 (fn-rtc-m-step (fn-rtc-mstate id s) ev (fn-rtc-view id inc s) (nfix q))) s))
                    (reqs (mv-nth 1 (fn-rtc-m-step (fn-rtc-mstate id s) ev (fn-rtc-view id inc s) (nfix q))))))))))

(local
 (defthm fn-rtc-pool-of-rearm
   (equal (fn-rtc-pool (mv-nth 0 (fn-rtc-rearm s))) (fn-rtc-pool s))
   :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-rtc-rearm fn-rtc-issue-frame))))))

(local
 (defthm fn-rtc-request-foreign-fields
   (implies (and (natp j) (natp id) (not (equal id j)))
            (and (equal (fn-rtc-slot j (mv-nth 0 (fn-rtc-request r id inc s))) (fn-rtc-slot j s))
                 (equal (fn-rtc-uses-of j (fn-rtc-uses (mv-nth 0 (fn-rtc-request r id inc s))))
                        (fn-rtc-uses-of j (fn-rtc-uses s)))))
   :hints (("Goal" :in-theory
            (union-theories (theory 'minimal-theory)
             '(fn-rtc-request fn-rtc-req-acquire fn-rtc-req-write fn-rtc-req-release fn-rtc-req-close fn-rtc-req-cancel fn-rtc-req-submit
               fn-rtc-slot-of-with fn-rtc-with-accessors fn-rtc-issue-frame fn-rtc-uses-of fn-rtc-get-of-cons
               nfix natp car-cons cdr-cons (:executable-counterpart member-equal) (:executable-counterpart equal)
               (:executable-counterpart zp) (:executable-counterpart unary--) (:executable-counterpart binary-+)))))))

(local
 (defthm fn-rtc-foreign-lease-return-frame
   (implies (and (fn-rtc-ownerp (fn-rtc-b-owner b))
                 (member-eq (fn-rtc-get 0 (fn-rtc-b-owner b)) '(:leased :handed))
                 (not (equal (fn-rtc-get 1 (fn-rtc-b-owner b)) j))
                 (not (and (fn-rtc-handed-to-live-p (fn-rtc-b-owner b) (fn-rtc-delivered-outcome u e) s)
                           (equal (nfix (fn-rtc-get 3 (fn-rtc-b-owner b))) j))))
            (fn-rtc-buffer-transfer-frame-p j (fn-rtc-config s) h b (fn-rtc-lease-return u e b s)))
   :hints (("Goal" :in-theory
            (e/d (fn-rtc-buffer-transfer-frame-p fn-rtc-visible-buffer fn-rtc-others-or-incoming-p fn-rtc-of-slot-p
                  fn-rtc-lease-return fn-rtc-ownerp)
                 (fn-rtc-b-owner fn-rtc-b-gen fn-rtc-b-bytes fn-rtc-home fn-rtc-handed-to-live-p fn-rtc-delivered-outcome
                  fn-rtc-live-p fn-rtc-current-p fn-rtc-slot fn-rtc-u-hd fn-rtc-h-off fn-rtc-splice fn-rtc-e-data))))))

(local
 (defthm fn-rtc-matched-use-owner-source
   (let* ((u (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))
          (o (fn-rtc-b-owner (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd u)) s))))
     (implies (and (fn-rtc-invp s) (fn-rtc-completionp e) u (fn-rtc-handlep (fn-rtc-u-hd u)))
              (and (equal (fn-rtc-get 1 o) (fn-rtc-e-id e)) (equal (fn-rtc-get 2 o) (fn-rtc-e-inc e)))))
   :hints (("Goal" :in-theory
            (union-theories (theory 'minimal-theory)
             '(fn-rtc-use-okp fn-rtc-usep natp nfix (:type-prescription fn-rtc-e-id)))
            :use (fn-rtc-invp-is-core-and-admission
                  (:instance fn-rtc-core-invp-found-use (key (fn-rtc-key e)))
                  (:instance fn-rtc-matching-use-fields (uses (fn-rtc-uses s))))))))

(local
 (defthm fn-rtc-end-use-pool-transfer-frame
   (implies (and (fn-rtc-invp s) (not (equal (fn-rtc-e-id e) j)) (not (equal (fn-rtc-target s e) j)))
            (fn-rtc-pool-transfer-frame-p j (fn-rtc-config s) 0 (fn-rtc-pool s) (fn-rtc-pool (fn-rtc-end-use s e))))
   :hints (("Goal" :in-theory
            (union-theories (theory 'minimal-theory)
             '(fn-rtc-end-use fn-rtc-end-lease fn-rtc-retire-drained fn-rtc-with-accessors fn-rtc-lease-return-of-with-uses
               fn-rtc-handed-to-live-p fn-rtc-use-okp fn-rtc-buffer-of-with fn-rtc-target fn-rtc-hand-to fn-rtc-hand-delivers-p fn-rtc-leasedp
               fn-rtc-pool-transfer-frame-refl fn-rtc-pool-is-buffers natp (:type-prescription fn-rtc-h-buf)))
            :use (fn-rtc-invp-is-core-and-admission
                  (:instance fn-rtc-core-invp-found-use (key (fn-rtc-key e)))
                  (:instance fn-rtc-matching-use-fields (uses (fn-rtc-uses s)))
                  fn-rtc-matched-use-owner-source fn-rtc-hand-delivers-kind
                  (:instance fn-rtc-found-use-buffer-ownerp (key (fn-rtc-key e)))
                  (:instance fn-rtc-found-use-is-leased (key (fn-rtc-key e)))
                  (:instance fn-rtc-foreign-lease-return-frame
                    (u (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))
                    (h (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))))
                    (b (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))) s)))
                  (:instance fn-rtc-pool-transfer-frame-update (cfg (fn-rtc-config s)) (pool (fn-rtc-pool s))
                    (k (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))))
                    (b (fn-rtc-lease-return (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)) e
                         (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))) s) s))))))))

(local
 (defthm fn-rtc-key-equality-id
   (implies (equal (fn-rtc-key u) key) (equal (fn-rtc-get 1 u) (fn-rtc-get 1 key)))
   :rule-classes :forward-chaining))

(local
 (defthm fn-rtc-uses-of-remove-other
   (implies (not (equal (fn-rtc-get 1 key) j))
            (equal (fn-rtc-uses-of j (fn-rtc-remove-use key uses)) (fn-rtc-uses-of j uses)))
   :hints (("Goal" :induct (fn-rtc-remove-use key uses)
            :in-theory (e/d (fn-rtc-remove-use fn-rtc-uses-of fn-rtc-key) (fn-rtc-get))))))

(local
 (defthm fn-rtc-end-use-foreign-fields
   (implies (and (natp j) (not (equal (fn-rtc-e-id e) j)))
            (and (equal (fn-rtc-slot j (fn-rtc-end-use s e)) (fn-rtc-slot j s))
                 (equal (fn-rtc-uses-of j (fn-rtc-uses (fn-rtc-end-use s e))) (fn-rtc-uses-of j (fn-rtc-uses s)))))
   :hints (("Goal" :in-theory
            (union-theories (theory 'minimal-theory)
             '(fn-rtc-end-use fn-rtc-retire-drained fn-rtc-end-lease-frame fn-rtc-retire-drained-frame
               fn-rtc-slot-of-with fn-rtc-with-accessors fn-rtc-uses-of-remove-other
               fn-rtc-completionp fn-rtc-e-id fn-rtc-key fn-rtc-get-of-cons nfix natp car-cons cdr-cons
               (:type-prescription fn-rtc-e-id) (:executable-counterpart equal)
               (:executable-counterpart zp) (:executable-counterpart binary-+) (:executable-counterpart unary--)))))))

(local
 (defthm fn-rtc-requests-foreign-fields
   (implies (and (natp j) (natp id) (not (equal id j)))
            (and (equal (fn-rtc-slot j (mv-nth 0 (fn-rtc-requests reqs id inc s))) (fn-rtc-slot j s))
                 (equal (fn-rtc-uses-of j (fn-rtc-uses (mv-nth 0 (fn-rtc-requests reqs id inc s)))) (fn-rtc-uses-of j (fn-rtc-uses s)))))
   :hints (("Goal" :induct (fn-rtc-requests reqs id inc s)
            :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
                         '(fn-rtc-requests fn-rtc-request-foreign-fields))))))

(local
 (defthm fn-rtc-deliver-foreign-fields
   (implies (and (natp j) (natp id) (not (equal id j)))
            (and (equal (fn-rtc-slot j (mv-nth 0 (fn-rtc-deliver s id inc ev q))) (fn-rtc-slot j s))
                 (equal (fn-rtc-uses-of j (fn-rtc-uses (mv-nth 0 (fn-rtc-deliver s id inc ev q)))) (fn-rtc-uses-of j (fn-rtc-uses s)))))
   :hints (("Goal" :in-theory
            (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
                         '(fn-rtc-deliver fn-rtc-requests-foreign-fields fn-rtc-with-accessors fn-rtc-slot-of-with))))))

(local
 (defthm fn-rtc-rearm-foreign-fields
   (implies (not (equal j 0))
            (and (equal (fn-rtc-slot j (mv-nth 0 (fn-rtc-rearm s))) (fn-rtc-slot j s))
                 (equal (fn-rtc-uses-of j (fn-rtc-uses (mv-nth 0 (fn-rtc-rearm s)))) (fn-rtc-uses-of j (fn-rtc-uses s)))))
   :hints (("Goal" :in-theory
            (union-theories (theory 'minimal-theory)
             '(fn-rtc-rearm fn-rtc-issue-frame fn-rtc-uses-of fn-rtc-get-of-cons car-cons cdr-cons
               (:executable-counterpart equal) (:executable-counterpart zp)
               (:executable-counterpart binary-+) (:executable-counterpart unary--)))))))

(local
 (defthm fn-rtc-other-step-other-id
   (implies (and (fn-rtc-invp s) (natp j) (<= 1 j)
                 (not (equal (fn-rtc-target s e) j))
                 (not (and (fn-rtc-hand-delivers-p s e) (equal (fn-rtc-e-id e) j))))
            (not (equal (fn-rtc-e-id e) j)))
   :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-rtc-target natp))
            :use fn-rtc-acts-on-accept-id))))

(local
 (defthm fn-rtc-release-all-pool-transfer-frame
   (implies (not (equal id j))
            (fn-rtc-pool-transfer-frame-p j cfg h pool (fn-rtc-release-all pool id inc)))
   :hints (("Goal" :induct (fn-rtc-local-buffers j cfg h pool)
            :in-theory
            (union-theories (theory 'minimal-theory)
             '((:induction fn-rtc-local-buffers) fn-rtc-pool-transfer-frame-p fn-rtc-release-all fn-rtc-buffer-transfer-frame-p
               fn-rtc-visible-buffer fn-rtc-of-slot-p fn-rtc-others-or-incoming-p
               fn-rtc-buffer-accessors fn-rtc-owner-equality-fields fn-rtc-get-of-cons car-cons cdr-cons
               (:executable-counterpart fn-rtc-b-owner) (:executable-counterpart fn-rtc-get)
               (:executable-counterpart member-equal) (:executable-counterpart equal)
               (:executable-counterpart zp) (:executable-counterpart binary-+) (:executable-counterpart unary--)))))))

(local
 (defthm fn-rtc-close-branch-foreign-frame
   (implies (and (natp j) (natp id) (not (equal j 0)) (not (equal id j)))
            (and (equal (fn-rtc-slot j (mv-nth 0 (fn-rtc-close-branch s id inc))) (fn-rtc-slot j s))
                 (equal (fn-rtc-uses-of j (fn-rtc-uses (mv-nth 0 (fn-rtc-close-branch s id inc)))) (fn-rtc-uses-of j (fn-rtc-uses s)))
                 (fn-rtc-pool-transfer-frame-p j (fn-rtc-config s) 0 (fn-rtc-pool s)
                                               (fn-rtc-pool (mv-nth 0 (fn-rtc-close-branch s id inc))))))
   :hints (("Goal" :in-theory
            (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
             '(fn-rtc-close-branch fn-rtc-pool-of-rearm fn-rtc-rearm-foreign-fields
               fn-rtc-with-accessors fn-rtc-slot-of-with fn-rtc-make-accessors fn-rtc-buffer-of-make
               fn-rtc-release-all-pool-transfer-frame fn-rtc-slots-is-slot natp nfix))))))

(local
 (defthm fn-rtc-accept-branch-foreign-frame
   (implies (and (natp j) (not (equal j 0))
                 (not (equal j (nfix (fn-rtc-free-slot 0 (fn-rtc-slots s))))))
            (and (equal (fn-rtc-slot j (mv-nth 0 (fn-rtc-accept-branch s out q))) (fn-rtc-slot j s))
                 (equal (fn-rtc-uses-of j (fn-rtc-uses (mv-nth 0 (fn-rtc-accept-branch s out q)))) (fn-rtc-uses-of j (fn-rtc-uses s)))
                 (fn-rtc-pool-transfer-frame-p j (fn-rtc-config s) 0 (fn-rtc-pool s)
                                               (fn-rtc-pool (mv-nth 0 (fn-rtc-accept-branch s out q))))))
   :hints (("Goal" :in-theory
            (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
             '(fn-rtc-accept-prepared fn-rtc-accept-slot fn-rtc-accept-inc fn-rtc-accept-branch fn-rtc-pool-of-rearm fn-rtc-rearm-foreign-fields
               fn-rtc-with-accessors fn-rtc-slot-of-with fn-rtc-deliver-foreign-fields
               fn-rtc-deliver-pool-transfer-frame fn-rtc-pool-transfer-frame-refl natp nfix))
            :use ((:instance fn-rtc-deliver-pool-transfer-frame (s (fn-rtc-accept-prepared s out))
                    (id (fn-rtc-accept-slot s)) (inc (fn-rtc-accept-inc s))
                    (ev (fn-rtc-ev :accept out (fn-rtc-accept-slot s) (fn-rtc-accept-inc s) nil)))
                  (:instance fn-rtc-free-slot-natp (i 0) (slots (fn-rtc-slots s))))))))

(local
 (defthm fn-rtc-accept-not-done-foreign-frame
   (implies (and (not (equal j 0)) (not (equal (fn-rtc-get 0 out) :done)))
            (and (equal (fn-rtc-slot j (mv-nth 0 (fn-rtc-accept-branch s out q))) (fn-rtc-slot j s))
                 (equal (fn-rtc-uses-of j (fn-rtc-uses (mv-nth 0 (fn-rtc-accept-branch s out q)))) (fn-rtc-uses-of j (fn-rtc-uses s)))
                 (fn-rtc-pool-transfer-frame-p j (fn-rtc-config s) 0 (fn-rtc-pool s)
                                               (fn-rtc-pool (mv-nth 0 (fn-rtc-accept-branch s out q))))))
   :hints (("Goal" :in-theory
            (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
             '(fn-rtc-accept-branch fn-rtc-pool-of-rearm fn-rtc-rearm-foreign-fields fn-rtc-pool-transfer-frame-refl))))))

(local
 (defthm fn-rtc-deliver-chain-pool-frame
   (implies (and (natp id) (not (equal id j)) (fn-rtc-pool-transfer-frame-p j (fn-rtc-config s) 0 p (fn-rtc-pool s)))
            (fn-rtc-pool-transfer-frame-p j (fn-rtc-config s) 0 p
                                          (fn-rtc-pool (mv-nth 0 (fn-rtc-deliver s id inc ev q)))))
   :hints (("Goal" :in-theory (theory 'minimal-theory)
            :use (fn-rtc-deliver-pool-transfer-frame
                  (:instance fn-rtc-pool-transfer-frame-trans (cfg (fn-rtc-config s)) (h 0)
                    (p1 p) (p2 (fn-rtc-pool s)) (p3 (fn-rtc-pool (mv-nth 0 (fn-rtc-deliver s id inc ev q))))))))))

(local
 (defthm fn-rtc-close-chain-pool-frame
   (implies (and (natp j) (not (equal j 0)) (natp id) (not (equal id j))
                 (fn-rtc-pool-transfer-frame-p j (fn-rtc-config s) 0 p (fn-rtc-pool s)))
            (fn-rtc-pool-transfer-frame-p j (fn-rtc-config s) 0 p
                                          (fn-rtc-pool (mv-nth 0 (fn-rtc-close-branch s id inc)))))
   :hints (("Goal" :in-theory (theory 'minimal-theory)
            :use (fn-rtc-close-branch-foreign-frame
                  (:instance fn-rtc-pool-transfer-frame-trans (cfg (fn-rtc-config s)) (h 0)
                    (p1 p) (p2 (fn-rtc-pool s)) (p3 (fn-rtc-pool (mv-nth 0 (fn-rtc-close-branch s id inc))))))))))

(local
 (defthm fn-rtc-accept-chain-pool-frame
   (implies (and (natp j) (not (equal j 0))
                 (or (not (equal j (nfix (fn-rtc-free-slot 0 (fn-rtc-slots s))))) (not (equal (fn-rtc-get 0 out) :done)))
                 (fn-rtc-pool-transfer-frame-p j (fn-rtc-config s) 0 p (fn-rtc-pool s)))
            (fn-rtc-pool-transfer-frame-p j (fn-rtc-config s) 0 p
                                          (fn-rtc-pool (mv-nth 0 (fn-rtc-accept-branch s out q)))))
   :hints (("Goal" :in-theory (theory 'minimal-theory)
            :use (fn-rtc-accept-branch-foreign-frame fn-rtc-accept-not-done-foreign-frame
                  (:instance fn-rtc-pool-transfer-frame-trans (cfg (fn-rtc-config s)) (h 0)
                    (p1 p) (p2 (fn-rtc-pool s)) (p3 (fn-rtc-pool (mv-nth 0 (fn-rtc-accept-branch s out q))))))))))

(local
 (defthm fn-rtc-other-step-frame
   (implies (and (fn-rtc-invp s) (natp j) (<= 1 j)
                 (not (equal (fn-rtc-target s e) j))
                 (not (and (fn-rtc-hand-delivers-p s e) (equal (fn-rtc-e-id e) j))))
            (let ((s2 (mv-nth 0 (fn-rtc-step s e q))))
              (and (equal (fn-rtc-slot j s2) (fn-rtc-slot j s))
                   (equal (fn-rtc-uses-of j (fn-rtc-uses s2)) (fn-rtc-uses-of j (fn-rtc-uses s)))
                   (fn-rtc-pool-transfer-frame-p j (fn-rtc-config s) 0 (fn-rtc-pool s) (fn-rtc-pool s2)))))
   :hints (("Goal" :in-theory
            (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
             '(fn-rtc-step-is-step-state fn-rtc-step-state fn-rtc-target fn-rtc-hand-to
               fn-rtc-slots-of-end-use-when-acting fn-rtc-config-of-end-use fn-rtc-pool-of-rearm
               fn-rtc-rearm-foreign-fields fn-rtc-deliver-foreign-fields fn-rtc-close-branch-foreign-frame
               fn-rtc-accept-branch-foreign-frame fn-rtc-accept-not-done-foreign-frame
               natp nfix (:type-prescription fn-rtc-e-id) (:type-prescription nfix)
               (:executable-counterpart equal)))
            :use ((:instance fn-rtc-accept-branch-foreign-frame (s (fn-rtc-end-use s e)) (out (fn-rtc-delivered-outcome (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)) e)))
                  (:instance fn-rtc-accept-not-done-foreign-frame (s (fn-rtc-end-use s e)) (out (fn-rtc-delivered-outcome (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)) e)))
                  fn-rtc-other-step-other-id
                  fn-rtc-end-use-pool-transfer-frame
                  fn-rtc-end-use-foreign-fields
                  fn-rtc-hand-delivers-kind
                  (:instance fn-rtc-delivered-outcome-done (u (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s))))
                  (:instance fn-rtc-deliver-chain-pool-frame (s (fn-rtc-end-use s e)) (p (fn-rtc-pool s)) (id (nfix (fn-rtc-get 3 (fn-rtc-b-owner (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))) s))))) (inc (fn-rtc-get 4 (fn-rtc-b-owner (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))) s)))) (ev (fn-rtc-ev :handed (fn-rtc-delivered-outcome (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)) e) (nfix (fn-rtc-get 3 (fn-rtc-b-owner (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))) s)))) (fn-rtc-get 4 (fn-rtc-b-owner (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))) s))) (list (fn-rtc-e-id e) (fn-rtc-e-inc e) (list (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))) (+ 1 (fn-rtc-b-gen (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))) s))) 0 (len (fn-rtc-b-bytes (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))) s))))))))
                  (:instance fn-rtc-deliver-chain-pool-frame (s (fn-rtc-end-use s e)) (p (fn-rtc-pool s)) (id (fn-rtc-e-id e)) (inc (fn-rtc-e-inc e)) (ev (fn-rtc-ev (fn-rtc-e-kind e) (if (equal (fn-rtc-get 0 (fn-rtc-delivered-outcome (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)) e)) :done) '(:failed :gone) (fn-rtc-delivered-outcome (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)) e)) (fn-rtc-e-id e) (fn-rtc-e-inc e) (list (list (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))) (+ 1 (fn-rtc-b-gen (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))) s))) 0 (len (fn-rtc-b-bytes (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))) s))))))))
                  (:instance fn-rtc-deliver-chain-pool-frame (s (fn-rtc-end-use s e)) (p (fn-rtc-pool s)) (id (fn-rtc-e-id e)) (inc (fn-rtc-e-inc e)) (ev (fn-rtc-ev (fn-rtc-e-kind e) (fn-rtc-delivered-outcome (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)) e) (fn-rtc-e-id e) (fn-rtc-e-inc e) nil)))
                  (:instance fn-rtc-close-chain-pool-frame (s (fn-rtc-end-use s e)) (p (fn-rtc-pool s)) (id (fn-rtc-e-id e)) (inc (fn-rtc-e-inc e)))
                  (:instance fn-rtc-accept-chain-pool-frame (s (fn-rtc-end-use s e)) (p (fn-rtc-pool s)) (out (fn-rtc-delivered-outcome (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)) e))))))))

; T17c others' steps touch J's local part only by explicit transfer
(defthm fn-rtc-others-touch-an-instance-only-by-transfer
  (implies (and (fn-rtc-invp s) (natp j) (<= 1 j)
                (not (equal (fn-rtc-target s e) j))
                (not (and (fn-rtc-hand-delivers-p s e) (equal (fn-rtc-e-id e) j))))
           (let ((s2 (mv-nth 0 (fn-rtc-step s e q))))
             (and (equal (fn-rtc-slot j s2) (fn-rtc-slot j s))
                  (equal (fn-rtc-mstate j s2) (fn-rtc-mstate j s))
                  (equal (fn-rtc-uses-of j (fn-rtc-uses s2)) (fn-rtc-uses-of j (fn-rtc-uses s)))
                  (fn-rtc-local-returns-p j (fn-rtc-config s) 0
                                          (fn-rtc-local-buffers j (fn-rtc-config s) 0 (fn-rtc-pool s))
                                          (fn-rtc-local-buffers j (fn-rtc-config s) 0 (fn-rtc-pool s2))
                                          (fn-rtc-pool s2)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(natp nfix))
           :use (fn-rtc-other-step-frame fn-rtc-machine-changes-only-when-delivered-to
                 (:instance fn-rtc-pool-transfer-frame-is-local-returns (cfg (fn-rtc-config s)) (h 0)
                   (p1 (fn-rtc-pool s)) (p2 (fn-rtc-pool (mv-nth 0 (fn-rtc-step s e q)))))))))

(local
 (defthm fn-rtc-local-ranked-rearm
   (implies (not (equal j 0))
            (equal (fn-rtc-local-ranked j (mv-nth 0 (fn-rtc-rearm s))) (fn-rtc-local-ranked j s)))
   :hints (("Goal" :in-theory
            (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
             '(fn-rtc-local-ranked fn-rtc-rearm-frame fn-rtc-pool-of-rearm fn-rtc-rearm-foreign-fields))))))

(local
 (defthm fn-rtc-uses-of-rearm-actions
   (implies (not (equal j 0)) (equal (fn-rtc-uses-of j (mv-nth 1 (fn-rtc-rearm s))) nil))
   :hints (("Goal" :in-theory
            (union-theories (theory 'minimal-theory)
             '(fn-rtc-rearm fn-rtc-uses-of fn-rtc-get-of-cons car-cons cdr-cons
               (:executable-counterpart equal) (:executable-counterpart zp)
               (:executable-counterpart unary--) (:executable-counterpart binary-+)))))))

(local
 (defthm fn-rtc-find-use-of-uses-of
   (implies (equal (fn-rtc-get 1 key) j)
            (equal (fn-rtc-find-use key (fn-rtc-uses-of j uses)) (fn-rtc-find-use key uses)))
   :hints (("Goal" :induct (fn-rtc-find-use key uses)
            :in-theory (e/d (fn-rtc-find-use fn-rtc-uses-of fn-rtc-key) (fn-rtc-get))))))

(local
 (defthm fn-rtc-key-rank-type
   (implies (natp i) (or (natp (fn-rtc-key-rank key xs i)) (not (fn-rtc-key-rank key xs i))))
   :rule-classes nil
   :hints (("Goal" :in-theory (disable fn-rtc-key)))))

(local
 (defthm fn-rtc-key-rank-found
   (implies (and (natp i) (not (member-equal nil xs)))
            (iff (natp (fn-rtc-key-rank key xs i)) (fn-rtc-find-use key xs)))
   :hints (("Goal" :induct (fn-rtc-key-rank key xs i)
            :in-theory (disable fn-rtc-key)))))

(local
 (defthm fn-rtc-key-rank-nth
   (implies (and (natp i) (fn-rtc-find-use key xs))
            (equal (nth (- (fn-rtc-key-rank key xs i) i) xs) (fn-rtc-find-use key xs)))
   :hints (("Goal" :induct (fn-rtc-key-rank key xs i)
            :in-theory (disable fn-rtc-key)))))

(local
 (defthm fn-rtc-ranked-equal-length
   (implies (fn-rtc-ranked-equal-p xs ys) (equal (len xs) (len ys)))
   :hints (("Goal" :induct (fn-rtc-ranked-equal-p xs ys) :in-theory (disable fn-rtc-get)))))

(local
 (defthm fn-rtc-ranked-equal-nth
   (implies (fn-rtc-ranked-equal-p xs ys)
            (and (equal (fn-rtc-get 0 (nth k xs)) (fn-rtc-get 0 (nth k ys)))
                 (equal (fn-rtc-get 1 (nth k xs)) (fn-rtc-get 1 (nth k ys)))
                 (equal (fn-rtc-get 2 (nth k xs)) (fn-rtc-get 2 (nth k ys)))
                 (equal (fn-rtc-get 4 (nth k xs)) (fn-rtc-get 4 (nth k ys)))))
   :hints (("Goal" :induct (list (nth k xs) (nth k ys)) :in-theory (disable fn-rtc-get)))))

(local
 (defthm fn-rtc-key-rank-bound
   (implies (and (natp i) (natp (fn-rtc-key-rank key xs i)))
            (and (<= i (fn-rtc-key-rank key xs i)) (< (fn-rtc-key-rank key xs i) (+ i (len xs)))))
   :rule-classes :linear
   :hints (("Goal" :induct (fn-rtc-key-rank key xs i) :in-theory (disable fn-rtc-key)))))

(local
 (defthm fn-rtc-uses-of-op-subset
   (implies (not (fn-rtc-op-used-p op uses)) (not (fn-rtc-op-used-p op (fn-rtc-uses-of j uses))))
   :hints (("Goal" :in-theory (disable fn-rtc-get)))))

(local
 (defthm fn-rtc-uses-of-kind-subset
   (implies (not (fn-rtc-kind-out-p kind id inc uses))
            (not (fn-rtc-kind-out-p kind id inc (fn-rtc-uses-of j uses))))
   :hints (("Goal" :in-theory (disable fn-rtc-get)))))

(local
 (defthm fn-rtc-uses-of-okp
   (implies (fn-rtc-uses-okp uses s) (fn-rtc-uses-okp (fn-rtc-uses-of j uses) s))
   :hints (("Goal" :induct (fn-rtc-uses-of j uses)
            :in-theory (disable fn-rtc-use-okp fn-rtc-get fn-rtc-kind-out-p fn-rtc-op-used-p)))))

(local
 (defthm fn-rtc-uses-okp-no-nil
   (implies (fn-rtc-uses-okp uses s) (not (member-equal nil uses)))
   :hints (("Goal" :in-theory (disable fn-rtc-uses-okp fn-rtc-uses-okp-member)
            :use ((:instance fn-rtc-uses-okp-member (u nil)))))))

(local
 (defthm fn-rtc-op-used-at-nth
   (implies (and (natp k) (< k (len xs))) (fn-rtc-op-used-p (fn-rtc-get 3 (nth k xs)) xs))
   :hints (("Goal" :induct (nth k xs) :in-theory (disable fn-rtc-get)))))

(local
 (defthm fn-rtc-find-use-of-nth
   (implies (and (fn-rtc-uses-okp xs s) (natp k) (< k (len xs)))
            (equal (fn-rtc-find-use (fn-rtc-key (nth k xs)) xs) (nth k xs)))
   :hints (("Goal" :induct (nth k xs)
            :in-theory (union-theories (theory 'minimal-theory)
             '(fn-rtc-key fn-rtc-uses-okp fn-rtc-find-use fn-rtc-remove-use fn-rtc-op-used-at-nth nth len natp zp-open car-cons cdr-cons cons-equal
               (:type-prescription len) (:executable-counterpart equal) (:executable-counterpart zp)
               (:executable-counterpart binary-+) (:executable-counterpart unary--))))
           ("Subgoal *1/3" :use ((:instance fn-rtc-op-used-at-nth (k (- k 1)) (xs (cdr xs))))))))

(local
 (defun fn-rtc-drop-at (k xs)
   (if (consp xs) (if (zp k) (cdr xs) (cons (car xs) (fn-rtc-drop-at (- k 1) (cdr xs)))) nil)))

(local
 (defthm fn-rtc-remove-use-of-nth
   (implies (and (fn-rtc-uses-okp xs s) (natp k) (< k (len xs)))
            (equal (fn-rtc-remove-use (fn-rtc-key (nth k xs)) xs) (fn-rtc-drop-at k xs)))
   :hints (("Goal" :induct (nth k xs)
            :in-theory (union-theories (theory 'minimal-theory)
             '(fn-rtc-key fn-rtc-uses-okp fn-rtc-find-use fn-rtc-remove-use fn-rtc-drop-at fn-rtc-op-used-at-nth nth len natp zp-open car-cons cdr-cons cons-equal
               (:type-prescription len) (:executable-counterpart equal) (:executable-counterpart zp)
               (:executable-counterpart binary-+) (:executable-counterpart unary--))))
           ("Subgoal *1/3" :use ((:instance fn-rtc-op-used-at-nth (k (- k 1)) (xs (cdr xs))))))))

(local
 (defthm fn-rtc-ranked-equal-drop-at
   (implies (fn-rtc-ranked-equal-p xs ys) (fn-rtc-ranked-equal-p (fn-rtc-drop-at k xs) (fn-rtc-drop-at k ys)))
   :hints (("Goal" :induct (list (fn-rtc-drop-at k xs) (fn-rtc-drop-at k ys)) :in-theory (disable fn-rtc-get)))))

(local
 (defthm fn-rtc-uses-of-remove-own
   (implies (equal (fn-rtc-get 1 key) j)
            (equal (fn-rtc-uses-of j (fn-rtc-remove-use key uses))
                   (fn-rtc-remove-use key (fn-rtc-uses-of j uses))))
   :hints (("Goal" :induct (fn-rtc-remove-use key uses)
            :in-theory (e/d (fn-rtc-remove-use fn-rtc-uses-of fn-rtc-key) (fn-rtc-get))))))

(local
 (defthm fn-rtc-use-holding-is-owner
   (implies (and (fn-rtc-use-okp u s) (fn-rtc-handlep (fn-rtc-u-hd u))
                 (equal (fn-rtc-h-buf (fn-rtc-u-hd u)) h))
            (equal (fn-rtc-get 1 u) (fn-rtc-get 1 (fn-rtc-b-owner (fn-rtc-buffer h s)))))
   :hints (("Goal" :in-theory
            (union-theories (theory 'minimal-theory) '(fn-rtc-use-okp fn-rtc-usep natp nfix))))))

(local
 (defthm fn-rtc-holds-of-uses-of
   (implies (and (fn-rtc-uses-okp uses s) (equal (fn-rtc-get 1 (fn-rtc-b-owner (fn-rtc-buffer h s))) j))
            (equal (fn-rtc-holds-p h g (fn-rtc-uses-of j uses)) (fn-rtc-holds-p h g uses)))
   :hints (("Goal" :induct (fn-rtc-uses-of j uses)
            :in-theory (e/d (fn-rtc-uses-of fn-rtc-holds-p fn-rtc-uses-okp)
                             (fn-rtc-get fn-rtc-u-hd fn-rtc-h-buf fn-rtc-h-gen fn-rtc-handlep fn-rtc-use-okp
                              fn-rtc-kind-out-p fn-rtc-op-used-p fn-rtc-use-holding-is-owner)))
           ("Subgoal *1/1" :use ((:instance fn-rtc-use-holding-is-owner (u (car uses)))))
           ("Subgoal *1/2" :use ((:instance fn-rtc-use-holding-is-owner (u (car uses))))))))

(local
 (defthm fn-rtc-ranked-equal-holds
   (implies (fn-rtc-ranked-equal-p xs ys) (equal (fn-rtc-holds-p h g xs) (fn-rtc-holds-p h g ys)))
   :hints (("Goal" :induct (fn-rtc-ranked-equal-p xs ys)
            :in-theory (e/d (fn-rtc-holds-p fn-rtc-u-hd fn-rtc-ranked-equal-p)
                             (fn-rtc-get fn-rtc-h-buf fn-rtc-h-gen fn-rtc-handlep))))))

(local
 (defthm fn-rtc-uses-of-slot-of-uses-of
   (equal (fn-rtc-uses-of-slot-p j inc (fn-rtc-uses-of j uses)) (fn-rtc-uses-of-slot-p j inc uses))
   :hints (("Goal" :in-theory (disable fn-rtc-get)))))

(local
 (defthm fn-rtc-ranked-equal-uses-of-slot
   (implies (fn-rtc-ranked-equal-p xs ys)
            (equal (fn-rtc-uses-of-slot-p id inc xs) (fn-rtc-uses-of-slot-p id inc ys)))
   :hints (("Goal" :induct (fn-rtc-ranked-equal-p xs ys)
            :in-theory (e/d (fn-rtc-uses-of-slot-p fn-rtc-ranked-equal-p) (fn-rtc-get))))))

(local
 (defthm fn-rtc-get-nonnil-in-range
   (implies (fn-rtc-get k xs) (< (nfix k) (len xs)))
   :rule-classes :linear
   :hints (("Goal" :induct (fn-rtc-get k xs) :in-theory (enable fn-rtc-get)))))

(local
 (defthm fn-rtc-set-preserves-true-listp
   (implies (< (nfix k) (len xs)) (equal (true-listp (fn-rtc-set k v xs)) (true-listp xs)))
   :hints (("Goal" :induct (fn-rtc-set k v xs) :in-theory (enable fn-rtc-set)))))

(local
 (defthm fn-rtc-uses-okp-nth
   (implies (and (fn-rtc-uses-okp xs s) (natp k) (< k (len xs)))
            (fn-rtc-use-okp (nth k xs) s))
   :hints (("Goal" :induct (nth k xs) :in-theory (disable fn-rtc-use-okp fn-rtc-get)))))

(local
 (defthm fn-rtc-uses-okp-next-unused
   (implies (fn-rtc-uses-okp xs s) (not (fn-rtc-op-used-p (fn-rtc-next-op s) xs)))
   :hints (("Goal" :induct (fn-rtc-uses-okp xs s)
            :in-theory (union-theories (theory 'minimal-theory)
             '(fn-rtc-uses-okp fn-rtc-op-used-p fn-rtc-use-okp fn-rtc-usep natp nfix car-cons cdr-cons))))))

(local
 (defthm fn-rtc-key-find-fields
   (implies (fn-rtc-find-use (fn-rtc-key e) xs)
            (and (equal (fn-rtc-get 0 (fn-rtc-find-use (fn-rtc-key e) xs)) (fn-rtc-get 0 e))
                 (equal (fn-rtc-get 1 (fn-rtc-find-use (fn-rtc-key e) xs)) (fn-rtc-get 1 e))
                 (equal (fn-rtc-get 2 (fn-rtc-find-use (fn-rtc-key e) xs)) (fn-rtc-get 2 e))
                 (equal (fn-rtc-get 3 (fn-rtc-find-use (fn-rtc-key e) xs)) (fn-rtc-get 3 e))))
   :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-rtc-key cons-equal))
            :use ((:instance fn-rtc-key-of-find-use (k (fn-rtc-key e)) (uses xs)))))))

(local (defthm fn-rtc-plus-zero (implies (acl2-numberp x) (equal (+ x 0) x))))

(local (defthm fn-rtc-use-okp-nonnil (not (fn-rtc-use-okp nil s))
 :hints (("Goal" :in-theory (enable fn-rtc-use-okp fn-rtc-usep)))))

(local
 (defthm fn-rtc-rank-rekey-matched
   (implies (and (fn-rtc-uses-okp xs s) (fn-rtc-uses-okp ys s2)
                 (fn-rtc-ranked-equal-p xs ys) (fn-rtc-find-use (fn-rtc-key e) xs))
            (let* ((r (fn-rtc-key-rank (fn-rtc-key e) xs 0))
                   (e2 (fn-rtc-set 3 (fn-rtc-get 3 (nth r ys)) e)))
              (and (equal (fn-rtc-key e2) (fn-rtc-key (nth r ys)))
                   (equal (fn-rtc-find-use (fn-rtc-key e2) ys) (nth r ys))
                   (fn-rtc-find-use (fn-rtc-key e2) ys)
                   (equal (fn-rtc-completionp e2) (fn-rtc-completionp e)))))
   :hints (("Goal" :in-theory
            (union-theories (theory 'minimal-theory)
             '(fn-rtc-use-okp-nonnil fn-rtc-plus-zero fn-rtc-key fn-rtc-get-of-set fn-rtc-len-of-set fn-rtc-set-preserves-true-listp
               fn-rtc-completionp 
               fn-rtc-uses-okp-nth fn-rtc-ranked-equal-length fn-rtc-get-nonnil-in-range
               fn-rtc-key-rank-bound natp nfix cons-equal (:type-prescription len)
               (:executable-counterpart fn-rtc-get) (:executable-counterpart equal) (:executable-counterpart nfix)
               (:executable-counterpart binary-+) (:executable-counterpart unary--)))
            :use ((:instance fn-rtc-find-use-of-nth (xs ys) (s s2) (k (fn-rtc-key-rank (fn-rtc-key e) xs 0)))
                  (:instance fn-rtc-uses-okp-nth (xs ys) (s s2) (k (fn-rtc-key-rank (fn-rtc-key e) xs 0)))
                  (:instance fn-rtc-use-okp-op-natp (u (nth (fn-rtc-key-rank (fn-rtc-key e) xs 0) ys)) (s s2))
                  (:instance fn-rtc-use-okp-op-natp (u (fn-rtc-find-use (fn-rtc-key e) xs)))
                  fn-rtc-key-find-fields
                  (:instance fn-rtc-key-rank-found (key (fn-rtc-key e)) (i 0))
                  (:instance fn-rtc-key-rank-nth (key (fn-rtc-key e)) (i 0))
                  (:instance fn-rtc-uses-okp-no-nil (uses xs))
                  (:instance fn-rtc-uses-okp-member (uses xs) (u (fn-rtc-find-use (fn-rtc-key e) xs)))
                  (:instance fn-rtc-find-use-is-member (k (fn-rtc-key e)) (uses xs))
                  (:instance fn-rtc-ranked-equal-nth (k (fn-rtc-key-rank (fn-rtc-key e) xs 0))))))))

(local
 (defthm fn-rtc-find-use-op-natp
   (implies (and (fn-rtc-uses-okp xs s) (fn-rtc-find-use (fn-rtc-key e) xs))
            (natp (fn-rtc-get 3 e)))
   :hints (("Goal" :in-theory (theory 'minimal-theory)
            :use (fn-rtc-key-find-fields
                  (:instance fn-rtc-use-okp-op-natp (u (fn-rtc-find-use (fn-rtc-key e) xs)))
                  (:instance fn-rtc-uses-okp-member (uses xs) (u (fn-rtc-find-use (fn-rtc-key e) xs)))
                  (:instance fn-rtc-find-use-is-member (k (fn-rtc-key e)) (uses xs)))))))

(local
 (defthm fn-rtc-fresh-event-unmatched
   (implies (fn-rtc-uses-okp xs s)
            (not (fn-rtc-find-use (fn-rtc-key (fn-rtc-set 3 (fn-rtc-next-op s) e)) xs)))
   :hints (("Goal" :in-theory
            (union-theories (theory 'minimal-theory)
             '(fn-rtc-get-of-set fn-rtc-get-nonnil-in-range natp nfix (:executable-counterpart equal) (:executable-counterpart nfix)))
            :use (fn-rtc-uses-okp-next-unused
                  (:instance fn-rtc-find-use-implies-op-used (x (fn-rtc-set 3 (fn-rtc-next-op s) e)) (l xs))
                  (:instance fn-rtc-find-use-op-natp (e (fn-rtc-set 3 (fn-rtc-next-op s) e))))))))

(local
 (defthm fn-rtc-rank-rekey-fields-and-removal
   (implies (and (fn-rtc-uses-okp xs s) (fn-rtc-uses-okp ys s2)
                 (fn-rtc-ranked-equal-p xs ys) (fn-rtc-find-use (fn-rtc-key e) xs))
            (let* ((r (fn-rtc-key-rank (fn-rtc-key e) xs 0))
                   (e2 (fn-rtc-set 3 (fn-rtc-get 3 (nth r ys)) e))
                   (u1 (fn-rtc-find-use (fn-rtc-key e) xs))
                   (u2 (fn-rtc-find-use (fn-rtc-key e2) ys)))
              (and (equal (fn-rtc-get 0 u1) (fn-rtc-get 0 u2))
                   (equal (fn-rtc-get 1 u1) (fn-rtc-get 1 u2))
                   (equal (fn-rtc-get 2 u1) (fn-rtc-get 2 u2))
                   (equal (fn-rtc-get 4 u1) (fn-rtc-get 4 u2))
                   (fn-rtc-ranked-equal-p (fn-rtc-remove-use (fn-rtc-key e) xs)
                                          (fn-rtc-remove-use (fn-rtc-key e2) ys)))))
   :hints (("Goal" :in-theory
            (union-theories (theory 'minimal-theory)
             '(fn-rtc-plus-zero fn-rtc-ranked-equal-drop-at natp fn-rtc-key-rank-bound fn-rtc-ranked-equal-length
               (:type-prescription len) (:executable-counterpart natp) (:executable-counterpart unary--)))
            :use (fn-rtc-rank-rekey-matched
                  (:instance fn-rtc-key-rank-found (key (fn-rtc-key e)) (i 0))
                  (:instance fn-rtc-uses-okp-no-nil (uses xs))
                  (:instance fn-rtc-key-rank-nth (key (fn-rtc-key e)) (i 0))
                  (:instance fn-rtc-key-of-find-use (k (fn-rtc-key e)) (uses xs))
                  (:instance fn-rtc-remove-use-of-nth (k (fn-rtc-key-rank (fn-rtc-key e) xs 0)))
                  (:instance fn-rtc-remove-use-of-nth (k (fn-rtc-key-rank (fn-rtc-key e) xs 0)) (xs ys) (s s2))
                  (:instance fn-rtc-ranked-equal-nth (k (fn-rtc-key-rank (fn-rtc-key e) xs 0))))))))

(local
 (defthm fn-rtc-remove-unmatched
   (implies (and (not (member-equal nil xs)) (not (fn-rtc-find-use key xs)) (true-listp xs))
            (equal (fn-rtc-remove-use key xs) xs))
   :hints (("Goal" :induct (fn-rtc-find-use key xs) :in-theory (disable fn-rtc-key)))))

(local
 (defthm fn-rtc-uses-of-true-listp
   (true-listp (fn-rtc-uses-of j xs))))

(local
 (defthm fn-rtc-corresponding-fields
   (let ((e2 (fn-rtc-corresponding-event j e s s2)))
     (and (equal (fn-rtc-e-id e2) (fn-rtc-e-id e))
          (equal (fn-rtc-e-inc e2) (fn-rtc-e-inc e))
          (equal (fn-rtc-e-kind e2) (fn-rtc-e-kind e))
          (equal (fn-rtc-e-outcome e2) (fn-rtc-e-outcome e))
          (equal (fn-rtc-e-data e2) (fn-rtc-e-data e))
          (equal (fn-rtc-get 1 e2) (fn-rtc-get 1 e))))
   :hints (("Goal" :in-theory
            (union-theories (theory 'minimal-theory)
             '(fn-rtc-corresponding-event fn-rtc-e-id fn-rtc-e-inc fn-rtc-e-kind fn-rtc-e-outcome fn-rtc-e-data
               fn-rtc-get-of-set (:executable-counterpart equal) (:executable-counterpart nfix)))))))

(local
 (defthm fn-rtc-corresponding-matching
   (implies (and (fn-rtc-invp s) (fn-rtc-invp s2) (natp j) (< 0 j)
                 (equal (fn-rtc-e-id e) j) (equal (fn-rtc-local-ranked j s) (fn-rtc-local-ranked j s2)))
            (let* ((e2 (fn-rtc-corresponding-event j e s s2))
                   (u1 (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))
                   (u2 (fn-rtc-find-use (fn-rtc-key e2) (fn-rtc-uses s2))))
              (and (iff u1 u2)
                   (implies u1 (equal (fn-rtc-completionp e2) (fn-rtc-completionp e)))
                   (equal (fn-rtc-get 0 u1) (fn-rtc-get 0 u2))
                   (equal (fn-rtc-get 1 u1) (fn-rtc-get 1 u2))
                   (equal (fn-rtc-get 2 u1) (fn-rtc-get 2 u2))
                   (equal (fn-rtc-get 4 u1) (fn-rtc-get 4 u2))
                   (fn-rtc-ranked-equal-p (fn-rtc-uses-of j (fn-rtc-remove-use (fn-rtc-key e) (fn-rtc-uses s)))
                                          (fn-rtc-uses-of j (fn-rtc-remove-use (fn-rtc-key e2) (fn-rtc-uses s2)))))))
   :hints (("Goal" :in-theory
            (union-theories (theory 'minimal-theory)
             '(fn-rtc-corresponding-event fn-rtc-e-id fn-rtc-key fn-rtc-get-of-cons fn-rtc-get-of-set
               fn-rtc-find-use-of-uses-of fn-rtc-uses-of-remove-own fn-rtc-remove-unmatched
               fn-rtc-uses-of-okp fn-rtc-invp-uses-okp fn-rtc-uses-okp-no-nil fn-rtc-uses-of-true-listp
               fn-rtc-local-ranked-equal-parts fn-rtc-key-rank-found fn-rtc-fresh-event-unmatched
               nfix natp cons-equal (:executable-counterpart fn-rtc-get) (:executable-counterpart equal)
               (:executable-counterpart nfix) (:executable-counterpart binary-+) (:executable-counterpart unary--)
               (:executable-counterpart zp)))
            :use (fn-rtc-invp-uses-okp (:instance fn-rtc-invp-uses-okp (s s2))
                  (:instance fn-rtc-uses-of-okp (uses (fn-rtc-uses s)))
                  (:instance fn-rtc-uses-of-okp (uses (fn-rtc-uses s2)) (s s2))
                  (:instance fn-rtc-uses-okp-no-nil (uses (fn-rtc-uses-of j (fn-rtc-uses s))))
                  (:instance fn-rtc-uses-okp-no-nil (uses (fn-rtc-uses-of j (fn-rtc-uses s2))) (s s2))
                  (:instance fn-rtc-find-use-of-uses-of (key (fn-rtc-key e)) (uses (fn-rtc-uses s)))
                  (:instance fn-rtc-find-use-of-uses-of (key (fn-rtc-key (fn-rtc-corresponding-event j e s s2))) (uses (fn-rtc-uses s2)))
                  (:instance fn-rtc-uses-of-remove-own (key (fn-rtc-key e)) (uses (fn-rtc-uses s)))
                  (:instance fn-rtc-uses-of-remove-own (key (fn-rtc-key (fn-rtc-corresponding-event j e s s2))) (uses (fn-rtc-uses s2)))
                  (:instance fn-rtc-fresh-event-unmatched (s s2) (xs (fn-rtc-uses s2)))
                  (:instance fn-rtc-key-rank-found (key (fn-rtc-key e)) (xs (fn-rtc-uses-of j (fn-rtc-uses s))) (i 0))
                  (:instance fn-rtc-rank-rekey-matched (xs (fn-rtc-uses-of j (fn-rtc-uses s))) (ys (fn-rtc-uses-of j (fn-rtc-uses s2))))
                  (:instance fn-rtc-rank-rekey-fields-and-removal (xs (fn-rtc-uses-of j (fn-rtc-uses s))) (ys (fn-rtc-uses-of j (fn-rtc-uses s2))))) ))))

(local
 (defthm fn-rtc-invp-static-slot
   (implies (and (fn-rtc-invp s) (natp k) (<= 1 k) (<= k (fn-rtc-nstatic (fn-rtc-config s))))
            (equal (fn-rtc-slot k s) '(1 :live 0)))
   :hints (("Goal" :in-theory
            (union-theories (theory 'minimal-theory) '(fn-rtc-invp fn-rtc-slot nfix natp (:type-prescription fn-rtc-nstatic)))
            :use ((:instance fn-rtc-statics-okp-get (j 1) (n (fn-rtc-nstatic (fn-rtc-config s))) (slots (fn-rtc-slots s))))))))

(local
 (defthm fn-rtc-local-ranked-owned-buffer
   (implies (and (natp h) (equal (fn-rtc-local-ranked j s1) (fn-rtc-local-ranked j s2))
                 (fn-rtc-of-slot-p (fn-rtc-b-owner (fn-rtc-buffer h s1)) j))
            (equal (fn-rtc-buffer h s1) (fn-rtc-buffer h s2)))
   :hints (("Goal" :in-theory
            (union-theories (theory 'minimal-theory) '(fn-rtc-local-ranked-equal-parts))
            :use (fn-rtc-local-ranked-visible
                  (:instance fn-rtc-visible-buffer-unhides (cfg (fn-rtc-config s1)) (b (fn-rtc-buffer h s1)))
                  (:instance fn-rtc-visible-buffer-equal-unhides (cfg (fn-rtc-config s1)) (b1 (fn-rtc-buffer h s1)) (b2 (fn-rtc-buffer h s2))))))))

(local
 (defthm fn-rtc-use-own-buffer
   (implies (and (fn-rtc-use-okp u s) (equal (fn-rtc-get 1 u) j) (fn-rtc-handlep (fn-rtc-u-hd u)))
            (fn-rtc-of-slot-p (fn-rtc-b-owner (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd u)) s)) j))
   :hints (("Goal" :in-theory
            (union-theories (theory 'minimal-theory) '(fn-rtc-use-okp fn-rtc-usep fn-rtc-of-slot-p natp nfix member-equal
               (:executable-counterpart equal)))))))

(local
 (defthm fn-rtc-ranked-outcome
   (implies (and (equal (fn-rtc-get 0 u1) (fn-rtc-get 0 u2))
                 (equal (fn-rtc-get 4 u1) (fn-rtc-get 4 u2))
                 (equal (fn-rtc-e-outcome e1) (fn-rtc-e-outcome e2))
                 (equal (fn-rtc-e-data e1) (fn-rtc-e-data e2)))
            (equal (fn-rtc-delivered-outcome u1 e1) (fn-rtc-delivered-outcome u2 e2)))
   :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-rtc-delivered-outcome fn-rtc-u-hd))))))

(local
 (defthm fn-rtc-local-handed-to-live
   (implies (and (fn-rtc-invp s1) (fn-rtc-invp s2) (fn-rtc-buffer-okp h b s1)
                 (equal (fn-rtc-config s1) (fn-rtc-config s2))
                 (equal (fn-rtc-get 1 (fn-rtc-b-owner b)) j) (natp j)
                 (< (fn-rtc-nstatic (fn-rtc-config s1)) j))
            (equal (fn-rtc-handed-to-live-p (fn-rtc-b-owner b) out s1)
                   (fn-rtc-handed-to-live-p (fn-rtc-b-owner b) out s2)))
   :hints (("Goal" :in-theory
            (union-theories (theory 'minimal-theory)
             '(fn-rtc-buffer-okp fn-rtc-handed-to-live-p fn-rtc-live-p fn-rtc-current-p fn-rtc-invp-static-slot natp nfix
               (:type-prescription nfix) (:executable-counterpart equal)))
            :use ((:instance fn-rtc-invp-static-slot (s s1) (k (nfix (fn-rtc-get 3 (fn-rtc-b-owner b)))))
                  (:instance fn-rtc-invp-static-slot (s s2) (k (nfix (fn-rtc-get 3 (fn-rtc-b-owner b))))))))))

(local
 (defthm fn-rtc-corresponding-buffer
   (implies (and (fn-rtc-invp s) (fn-rtc-invp s2) (natp j) (< 0 j)
                 (equal (fn-rtc-e-id e) j) (equal (fn-rtc-local-ranked j s) (fn-rtc-local-ranked j s2))
                 (fn-rtc-completionp e) (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s))
                 (fn-rtc-handlep (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))))
            (equal (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))) s)
                   (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))) s2)))
   :hints (("Goal" :in-theory
            (union-theories (theory 'minimal-theory) '(natp (:type-prescription fn-rtc-h-buf)))
            :use (fn-rtc-invp-is-core-and-admission
                  (:instance fn-rtc-core-invp-found-use (key (fn-rtc-key e)))
                  (:instance fn-rtc-matching-use-fields (uses (fn-rtc-uses s)))
                  (:instance fn-rtc-use-own-buffer (u (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s))))
                  (:instance fn-rtc-local-ranked-owned-buffer (s1 s) (h (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))))))))))

(local
 (defthm fn-rtc-corresponding-outcome
   (implies (and (fn-rtc-invp s) (fn-rtc-invp s2) (natp j) (< 0 j)
                 (equal (fn-rtc-e-id e) j) (equal (fn-rtc-local-ranked j s) (fn-rtc-local-ranked j s2)))
            (equal (fn-rtc-delivered-outcome (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)) e)
                   (fn-rtc-delivered-outcome (fn-rtc-find-use (fn-rtc-key (fn-rtc-corresponding-event j e s s2)) (fn-rtc-uses s2))
                                              (fn-rtc-corresponding-event j e s s2))))
   :hints (("Goal" :in-theory (theory 'minimal-theory)
            :use (fn-rtc-corresponding-matching fn-rtc-corresponding-fields
                  (:instance fn-rtc-ranked-outcome
                    (u1 (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))
                    (u2 (fn-rtc-find-use (fn-rtc-key (fn-rtc-corresponding-event j e s s2)) (fn-rtc-uses s2)))
                    (e1 e) (e2 (fn-rtc-corresponding-event j e s s2))))))))

(local
 (defthm fn-rtc-matched-buffer-okp
   (implies (and (fn-rtc-invp s) (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s))
                 (fn-rtc-handlep (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))))
            (fn-rtc-buffer-okp (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s))))
                               (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))) s) s))
   :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(natp (:type-prescription fn-rtc-h-buf)))
            :use (fn-rtc-invp-is-core-and-admission
                  (:instance fn-rtc-core-invp-found-use (key (fn-rtc-key e)))
                  (:instance fn-rtc-use-okp-buffer-index (u (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s))))
                  (:instance fn-rtc-core-invp-buffer (h (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))))))))))

(local
 (defthm fn-rtc-corresponding-hand
   (implies (and (fn-rtc-invp s) (fn-rtc-invp s2) (natp j) (< 0 j)
                 (< (fn-rtc-nstatic (fn-rtc-config s)) j)
                 (equal (fn-rtc-e-id e) j) (equal (fn-rtc-local-ranked j s) (fn-rtc-local-ranked j s2)))
            (equal (fn-rtc-hand-delivers-p s e)
                   (fn-rtc-hand-delivers-p s2 (fn-rtc-corresponding-event j e s s2))))
   :hints (("Goal" :in-theory
            (union-theories (theory 'minimal-theory) '(fn-rtc-hand-delivers-p fn-rtc-u-hd fn-rtc-local-ranked-equal-parts))
            :use (fn-rtc-corresponding-matching fn-rtc-corresponding-fields fn-rtc-corresponding-buffer
                  fn-rtc-corresponding-outcome fn-rtc-matched-buffer-okp fn-rtc-matched-use-owner-source
                  (:instance fn-rtc-local-handed-to-live (s1 s)
                    (h (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))))
                    (b (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))) s))
                    (out (fn-rtc-delivered-outcome (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)) e))))))))

(local
 (defthm fn-rtc-own-target-not-hand-delivery
   (implies (and (fn-rtc-invp s) (equal (fn-rtc-target s e) (fn-rtc-e-id e)))
            (not (fn-rtc-hand-delivers-p s e)))
   :hints (("Goal" :in-theory
            (union-theories (theory 'minimal-theory)
             '(fn-rtc-target fn-rtc-hand-to fn-rtc-hand-delivers-p fn-rtc-handed-to-live-p fn-rtc-buffer-okp
               fn-rtc-bufferp fn-rtc-ownerp natp nfix (:type-prescription fn-rtc-e-id)))
            :use (fn-rtc-matched-buffer-okp fn-rtc-matched-use-owner-source)))))

(local
 (defthm fn-rtc-corresponding-acts
   (implies (and (fn-rtc-invp s) (fn-rtc-invp s2) (natp j) (< 0 j)
                 (< (fn-rtc-nstatic (fn-rtc-config s)) j)
                 (equal (fn-rtc-e-id e) j) (equal (fn-rtc-local-ranked j s) (fn-rtc-local-ranked j s2)))
            (equal (fn-rtc-acts-on-p s e)
                   (fn-rtc-acts-on-p s2 (fn-rtc-corresponding-event j e s s2))))
   :hints (("Goal" :in-theory
            (union-theories (theory 'minimal-theory) '(fn-rtc-acts-on-p fn-rtc-local-ranked-equal-parts))
            :use (fn-rtc-corresponding-matching fn-rtc-corresponding-fields fn-rtc-corresponding-hand)))))

(local
 (defthm fn-rtc-local-ranked-with-uses
   (implies (and (equal (fn-rtc-local-ranked j s1) (fn-rtc-local-ranked j s2))
                 (fn-rtc-ranked-equal-p (fn-rtc-uses-of j xs) (fn-rtc-uses-of j ys)))
            (equal (fn-rtc-local-ranked j (fn-rtc-with-uses xs s1)) (fn-rtc-local-ranked j (fn-rtc-with-uses ys s2))))
   :hints (("Goal" :in-theory
            (union-theories (theory 'minimal-theory)
             '(fn-rtc-local-ranked fn-rtc-with-accessors fn-rtc-slot-of-with fn-rtc-mstate-of-with fn-rtc-ranked-equal-is-ranked cons-equal))))))

(local
 (defthm fn-rtc-local-ranked-with-buffer
   (implies (and (equal (fn-rtc-local-ranked j s1) (fn-rtc-local-ranked j s2)) (natp h))
            (equal (fn-rtc-local-ranked j (fn-rtc-with-buffer h b s1)) (fn-rtc-local-ranked j (fn-rtc-with-buffer h b s2))))
   :hints (("Goal" :in-theory
            (union-theories (theory 'minimal-theory)
             '(fn-rtc-local-ranked fn-rtc-with-accessors fn-rtc-slot-of-with fn-rtc-mstate-of-with cons-equal
               (:executable-counterpart natp)))
            :use ((:instance fn-rtc-local-buffers-set (h 0) (k h) (cfg (fn-rtc-config s1)) (p1 (fn-rtc-pool s1)) (p2 (fn-rtc-pool s2))))))))

(local
 (defthm fn-rtc-local-ranked-with-slot
   (implies (and (equal (fn-rtc-local-ranked j s1) (fn-rtc-local-ranked j s2))
                 (equal (len (fn-rtc-slots s1)) (len (fn-rtc-slots s2))))
            (equal (fn-rtc-local-ranked j (fn-rtc-with-slot j slot s1)) (fn-rtc-local-ranked j (fn-rtc-with-slot j slot s2))))
   :hints (("Goal" :in-theory
            (union-theories (theory 'minimal-theory)
             '(fn-rtc-local-ranked fn-rtc-with-accessors fn-rtc-slot-of-with fn-rtc-mstate-of-with cons-equal))))))

(local
 (defthm fn-rtc-local-ranked-slot-uses
   (implies (equal (fn-rtc-local-ranked j s1) (fn-rtc-local-ranked j s2))
            (equal (fn-rtc-uses-of-slot-p j inc (fn-rtc-uses s1)) (fn-rtc-uses-of-slot-p j inc (fn-rtc-uses s2))))
   :hints (("Goal" :in-theory
            (union-theories (theory 'minimal-theory) '(fn-rtc-local-ranked-equal-parts fn-rtc-uses-of-slot-of-uses-of))
            :use ((:instance fn-rtc-ranked-equal-uses-of-slot (id j) (xs (fn-rtc-uses-of j (fn-rtc-uses s1))) (ys (fn-rtc-uses-of j (fn-rtc-uses s2)))))))))

(local
 (defthm fn-rtc-local-ranked-retire
   (implies (and (equal (fn-rtc-local-ranked j s1) (fn-rtc-local-ranked j s2))
                 (equal (len (fn-rtc-slots s1)) (len (fn-rtc-slots s2))))
            (equal (fn-rtc-local-ranked j (fn-rtc-retire-drained j s1)) (fn-rtc-local-ranked j (fn-rtc-retire-drained j s2))))
   :hints (("Goal" :in-theory
            (union-theories (theory 'minimal-theory)
             '(fn-rtc-retire-drained fn-rtc-local-ranked-equal-parts))
            :use ((:instance fn-rtc-local-ranked-with-slot (slot (list (fn-rtc-s-inc (fn-rtc-slot j s1)) :free nil)))
                  (:instance fn-rtc-local-ranked-slot-uses (inc (fn-rtc-s-inc (fn-rtc-slot j s1)))))))))

(local
 (defthm fn-rtc-corresponding-holds-after-removal
   (let* ((e2 (fn-rtc-corresponding-event j e s s2))
          (u (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))
          (hd (fn-rtc-u-hd u)) (h (fn-rtc-h-buf hd)) (g (fn-rtc-h-gen hd)))
     (implies (and (fn-rtc-invp s) (fn-rtc-invp s2) (natp j) (< 0 j)
                   (equal (fn-rtc-e-id e) j) (equal (fn-rtc-local-ranked j s) (fn-rtc-local-ranked j s2))
                   (fn-rtc-completionp e) u (fn-rtc-handlep hd))
              (equal (fn-rtc-holds-p h g (fn-rtc-remove-use (fn-rtc-key e) (fn-rtc-uses s)))
                     (fn-rtc-holds-p h g (fn-rtc-remove-use (fn-rtc-key e2) (fn-rtc-uses s2))))))
   :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-rtc-u-hd))
            :use (fn-rtc-invp-uses-okp (:instance fn-rtc-invp-uses-okp (s s2))
                  fn-rtc-corresponding-matching fn-rtc-corresponding-fields fn-rtc-matched-use-owner-source
                  (:instance fn-rtc-matched-use-owner-source (s s2) (e (fn-rtc-corresponding-event j e s s2)))
                  (:instance fn-rtc-uses-okp-remove (uses (fn-rtc-uses s)) (key (fn-rtc-key e)))
                  (:instance fn-rtc-uses-okp-remove (uses (fn-rtc-uses s2)) (s s2) (key (fn-rtc-key (fn-rtc-corresponding-event j e s s2))))
                  (:instance fn-rtc-holds-of-uses-of (uses (fn-rtc-remove-use (fn-rtc-key e) (fn-rtc-uses s)))
                    (h (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))))
                    (g (fn-rtc-h-gen (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s))))))
                  (:instance fn-rtc-holds-of-uses-of (uses (fn-rtc-remove-use (fn-rtc-key (fn-rtc-corresponding-event j e s s2)) (fn-rtc-uses s2))) (s s2)
                    (h (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))))
                    (g (fn-rtc-h-gen (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s))))))
                  (:instance fn-rtc-ranked-equal-holds
                    (xs (fn-rtc-uses-of j (fn-rtc-remove-use (fn-rtc-key e) (fn-rtc-uses s))))
                    (ys (fn-rtc-uses-of j (fn-rtc-remove-use (fn-rtc-key (fn-rtc-corresponding-event j e s s2)) (fn-rtc-uses s2))))
                    (h (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))))
                    (g (fn-rtc-h-gen (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))))))))))

(local
 (defthm fn-rtc-local-lease-return
   (implies (and (equal (fn-rtc-slot j s1) (fn-rtc-slot j s2)) (natp j)
                 (equal (fn-rtc-get 1 (fn-rtc-b-owner b)) j)
                 (equal (fn-rtc-get 4 u1) (fn-rtc-get 4 u2))
                 (equal (fn-rtc-get 0 u1) (fn-rtc-get 0 u2))
                 (equal (fn-rtc-delivered-outcome u1 e1) (fn-rtc-delivered-outcome u2 e2))
                 (equal (fn-rtc-e-data e1) (fn-rtc-e-data e2))
                 (equal (fn-rtc-handed-to-live-p (fn-rtc-b-owner b) (fn-rtc-delivered-outcome u1 e1) s1)
                        (fn-rtc-handed-to-live-p (fn-rtc-b-owner b) (fn-rtc-delivered-outcome u1 e1) s2)))
            (equal (fn-rtc-lease-return u1 e1 b s1) (fn-rtc-lease-return u2 e2 b s2)))
   :hints (("Goal" :in-theory
            (union-theories (theory 'minimal-theory) '(fn-rtc-lease-return fn-rtc-u-hd fn-rtc-current-p natp nfix))))))

(local
 (defthm fn-rtc-local-ranked-end-lease
   (implies (and (equal (fn-rtc-local-ranked j s1) (fn-rtc-local-ranked j s2))
                 (equal (fn-rtc-u-hd u1) (fn-rtc-u-hd u2))
                 (implies (fn-rtc-handlep (fn-rtc-u-hd u1))
                          (and (equal (fn-rtc-holds-p (fn-rtc-h-buf (fn-rtc-u-hd u1)) (fn-rtc-h-gen (fn-rtc-u-hd u1)) (fn-rtc-uses s1))
                                      (fn-rtc-holds-p (fn-rtc-h-buf (fn-rtc-u-hd u1)) (fn-rtc-h-gen (fn-rtc-u-hd u1)) (fn-rtc-uses s2)))
                               (equal (fn-rtc-lease-return u1 e1 (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd u1)) s1) s1)
                                      (fn-rtc-lease-return u2 e2 (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd u1)) s2) s2)))))
            (equal (fn-rtc-local-ranked j (fn-rtc-end-lease u1 e1 s1)) (fn-rtc-local-ranked j (fn-rtc-end-lease u2 e2 s2))))
   :hints (("Goal" :in-theory
            (union-theories (theory 'minimal-theory) '(fn-rtc-end-lease natp (:type-prescription fn-rtc-h-buf)))
            :use ((:instance fn-rtc-local-ranked-with-buffer
                    (h (fn-rtc-h-buf (fn-rtc-u-hd u1)))
                    (b (fn-rtc-lease-return u1 e1 (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd u1)) s1) s1))))))))

(local
 (defthm fn-rtc-end-lease-slot-length
   (equal (len (fn-rtc-slots (fn-rtc-end-lease u e s))) (len (fn-rtc-slots s)))
   :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-rtc-end-lease fn-rtc-with-accessors))))))

(local
 (defthm fn-rtc-corresponding-lease-return
   (implies (and (and (fn-rtc-invp s) (fn-rtc-invp s2) (natp j) (< 0 j)
                 (< (fn-rtc-nstatic (fn-rtc-config s)) j)
                 (equal (fn-rtc-e-id e) j) (equal (fn-rtc-local-ranked j s) (fn-rtc-local-ranked j s2))) (fn-rtc-completionp e) (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)) (fn-rtc-handlep (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))))
            (equal (fn-rtc-lease-return (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)) e (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))) s) s)
                   (fn-rtc-lease-return (fn-rtc-find-use (fn-rtc-key (fn-rtc-corresponding-event j e s s2)) (fn-rtc-uses s2)) (fn-rtc-corresponding-event j e s s2) (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))) s2) s2)))
   :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn-rtc-local-ranked-equal-parts))
            :use (fn-rtc-corresponding-matching fn-rtc-corresponding-fields fn-rtc-corresponding-buffer
                  fn-rtc-corresponding-outcome fn-rtc-matched-buffer-okp fn-rtc-matched-use-owner-source
                  (:instance fn-rtc-local-handed-to-live (s1 s) (h (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s))))) (b (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))) s)) (out (fn-rtc-delivered-outcome (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)) e)))
                  (:instance fn-rtc-local-lease-return (s1 s) (u1 (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s))) (u2 (fn-rtc-find-use (fn-rtc-key (fn-rtc-corresponding-event j e s s2)) (fn-rtc-uses s2))) (e1 e) (e2 (fn-rtc-corresponding-event j e s s2)) (b (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))) s))))))))

(local
 (defthm fn-rtc-corresponding-end-use
   (implies (and (fn-rtc-invp s) (fn-rtc-invp s2) (natp j) (< 0 j)
                 (< (fn-rtc-nstatic (fn-rtc-config s)) j)
                 (equal (fn-rtc-e-id e) j) (equal (fn-rtc-local-ranked j s) (fn-rtc-local-ranked j s2)))
            (equal (fn-rtc-local-ranked j (fn-rtc-end-use s e)) (fn-rtc-local-ranked j (fn-rtc-end-use s2 (fn-rtc-corresponding-event j e s s2)))))
   :hints (("Goal" :in-theory
            (union-theories (theory 'minimal-theory)
             '(fn-rtc-end-use fn-rtc-u-hd fn-rtc-with-accessors fn-rtc-buffer-of-with fn-rtc-lease-return-of-with-uses
               fn-rtc-end-lease-slot-length fn-rtc-local-ranked-equal-parts))
            :use (fn-rtc-corresponding-matching fn-rtc-corresponding-fields fn-rtc-corresponding-holds-after-removal
                  fn-rtc-corresponding-lease-return
                  fn-rtc-invp-is-core-and-admission (:instance fn-rtc-invp-is-core-and-admission (s s2))
                  fn-rtc-core-invp-shape (:instance fn-rtc-core-invp-shape (s s2))
                  (:instance fn-rtc-local-ranked-with-uses (s1 s)
                    (xs (fn-rtc-remove-use (fn-rtc-key e) (fn-rtc-uses s))) (ys (fn-rtc-remove-use (fn-rtc-key (fn-rtc-corresponding-event j e s s2)) (fn-rtc-uses s2))))
                  (:instance fn-rtc-local-ranked-end-lease (s1 (fn-rtc-with-uses (fn-rtc-remove-use (fn-rtc-key e) (fn-rtc-uses s)) s)) (s2 (fn-rtc-with-uses (fn-rtc-remove-use (fn-rtc-key (fn-rtc-corresponding-event j e s s2)) (fn-rtc-uses s2)) s2)) (u1 (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s))) (u2 (fn-rtc-find-use (fn-rtc-key (fn-rtc-corresponding-event j e s s2)) (fn-rtc-uses s2))) (e1 e) (e2 (fn-rtc-corresponding-event j e s s2)))
                  (:instance fn-rtc-local-ranked-retire (s1 (fn-rtc-end-lease (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)) e (fn-rtc-with-uses (fn-rtc-remove-use (fn-rtc-key e) (fn-rtc-uses s)) s))) (s2 (fn-rtc-end-lease (fn-rtc-find-use (fn-rtc-key (fn-rtc-corresponding-event j e s s2)) (fn-rtc-uses s2)) (fn-rtc-corresponding-event j e s s2) (fn-rtc-with-uses (fn-rtc-remove-use (fn-rtc-key (fn-rtc-corresponding-event j e s s2)) (fn-rtc-uses s2)) s2)))))))))

(local
 (defthm fn-rtc-local-buffers-release-all
   (implies (equal (fn-rtc-local-buffers j cfg h p1) (fn-rtc-local-buffers j cfg h p2))
            (equal (fn-rtc-local-buffers j cfg h (fn-rtc-release-all p1 j inc))
                   (fn-rtc-local-buffers j cfg h (fn-rtc-release-all p2 j inc))))
   :hints (("Goal" :induct (list (fn-rtc-local-buffers j cfg h p1) (fn-rtc-local-buffers j cfg h p2))
            :in-theory (e/d (fn-rtc-local-buffers fn-rtc-release-all fn-rtc-of-slot-p)
                             (fn-rtc-b-owner fn-rtc-b-gen fn-rtc-b-bytes fn-rtc-home fn-rtc-get fn-rtc-local-buffers-set))
            :expand ((fn-rtc-local-buffers j cfg h p1) (fn-rtc-local-buffers j cfg h p2))))))

(local
 (defthm fn-rtc-close-prepared-local-ranked
   (implies (and (equal (fn-rtc-local-ranked j s1) (fn-rtc-local-ranked j s2))
                 (equal (len (fn-rtc-slots s1)) (len (fn-rtc-slots s2)))
                 (equal (len (fn-rtc-mstates s1)) (len (fn-rtc-mstates s2))))
            (equal (fn-rtc-local-ranked j (fn-rtc-close-prepared s1 j inc))
                   (fn-rtc-local-ranked j (fn-rtc-close-prepared s2 j inc))))
   :hints (("Goal" :in-theory
            (union-theories (theory 'minimal-theory)
             '(fn-rtc-close-prepared fn-rtc-local-ranked fn-rtc-make-accessors fn-rtc-with-accessors
               fn-rtc-slot-of-with fn-rtc-mstate-of-with fn-rtc-slot fn-rtc-mstate
               fn-rtc-get-of-set fn-rtc-ranked-equal-is-ranked cons-equal))
            :use (fn-rtc-local-ranked-slot-uses
                  (:instance fn-rtc-local-buffers-release-all (cfg (fn-rtc-config s1)) (h 0) (p1 (fn-rtc-pool s1)) (p2 (fn-rtc-pool s2))))))))

(local
 (defthm fn-rtc-close-local-ranked
   (implies (and (not (equal j 0)) (equal (fn-rtc-local-ranked j s1) (fn-rtc-local-ranked j s2))
                 (equal (len (fn-rtc-slots s1)) (len (fn-rtc-slots s2)))
                 (equal (len (fn-rtc-mstates s1)) (len (fn-rtc-mstates s2))))
            (and (equal (fn-rtc-local-ranked j (mv-nth 0 (fn-rtc-close-branch s1 j inc)))
                        (fn-rtc-local-ranked j (mv-nth 0 (fn-rtc-close-branch s2 j inc))))
                 (equal (fn-rtc-uses-of j (mv-nth 1 (fn-rtc-close-branch s1 j inc))) nil)
                 (equal (fn-rtc-uses-of j (mv-nth 1 (fn-rtc-close-branch s2 j inc))) nil)))
   :hints (("Goal" :in-theory
            (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
             '(fn-rtc-close-branch-is-rearm fn-rtc-local-ranked-rearm fn-rtc-uses-of-rearm-actions))
            :use fn-rtc-close-prepared-local-ranked))))

(local
 (defthm fn-rtc-ranked-equal-uses-of
   (implies (fn-rtc-ranked-equal-p xs ys)
            (fn-rtc-ranked-equal-p (fn-rtc-uses-of j xs) (fn-rtc-uses-of j ys)))
   :hints (("Goal" :induct (fn-rtc-ranked-equal-p xs ys) :in-theory (disable fn-rtc-get)))))

(local
 (defthm fn-rtc-end-use-column-lengths
   (and (equal (len (fn-rtc-slots (fn-rtc-end-use s e))) (len (fn-rtc-slots s)))
        (equal (fn-rtc-mstates (fn-rtc-end-use s e)) (fn-rtc-mstates s)))
   :hints (("Goal" :in-theory
            (union-theories (theory 'minimal-theory)
             '(fn-rtc-end-use fn-rtc-end-lease fn-rtc-retire-drained fn-rtc-with-accessors fn-rtc-len-of-set))))))

(local
 (defthm fn-rtc-local-ranked-shape
   (implies (and (fn-rtc-invp s) (fn-rtc-invp s2)
                 (equal (fn-rtc-local-ranked j s) (fn-rtc-local-ranked j s2)))
            (and (equal (len (fn-rtc-slots s)) (len (fn-rtc-slots s2)))
                 (equal (len (fn-rtc-mstates s)) (len (fn-rtc-mstates s2)))))
   :hints (("Goal" :in-theory
            (union-theories (theory 'minimal-theory) '(fn-rtc-local-ranked-equal-parts))
            :use (fn-rtc-invp-is-core-and-admission (:instance fn-rtc-invp-is-core-and-admission (s s2))
                  fn-rtc-core-invp-shape (:instance fn-rtc-core-invp-shape (s s2)))))))

(local
 (defthm fn-rtc-corresponding-step-inactive
   (implies (and (and (fn-rtc-invp s) (fn-rtc-invp s2) (natp j) (< 0 j)
                  (< (fn-rtc-nstatic (fn-rtc-config s)) j)
                  (equal (fn-rtc-local-ranked j s) (fn-rtc-local-ranked j s2))
                  (equal (fn-rtc-e-id e) j) (equal (fn-rtc-target s e) j)
                  (not (equal (fn-rtc-e-kind e) :accept))) (not (fn-rtc-acts-on-p s e))) (and (equal (fn-rtc-local-ranked j (mv-nth 0 (fn-rtc-step s e q)))
                        (fn-rtc-local-ranked j (mv-nth 0 (fn-rtc-step s2 (fn-rtc-corresponding-event j e s s2) q))))
                 (equal (fn-rtc-ranked (fn-rtc-uses-of j (mv-nth 1 (fn-rtc-step s e q))) 0)
                        (fn-rtc-ranked (fn-rtc-uses-of j (mv-nth 1 (fn-rtc-step s2 (fn-rtc-corresponding-event j e s s2) q))) 0))))
   :hints (("Goal" :in-theory
            (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
             '(fn-rtc-step-is-step-state fn-rtc-step-state fn-rtc-step-actions-is fn-rtc-step-actions fn-rtc-step*
               fn-rtc-local-ranked-rearm fn-rtc-uses-of-rearm-actions fn-rtc-end-use-column-lengths
               fn-rtc-ranked-equal-is-ranked fn-rtc-ranked-equal-uses-of fn-rtc-u-hd
               (:executable-counterpart fn-rtc-ranked-equal-p) (:executable-counterpart fn-rtc-ranked) (:executable-counterpart equal)
               (:executable-counterpart member-equal) natp))
            :use (fn-rtc-corresponding-acts fn-rtc-corresponding-hand fn-rtc-own-target-not-hand-delivery
                  fn-rtc-corresponding-end-use fn-rtc-corresponding-fields fn-rtc-corresponding-matching
                  fn-rtc-corresponding-outcome fn-rtc-corresponding-buffer fn-rtc-local-ranked-shape
                  fn-rtc-acting-matches-use )))))

(local
 (defthm fn-rtc-corresponding-step-close
   (implies (and (and (fn-rtc-invp s) (fn-rtc-invp s2) (natp j) (< 0 j)
                  (< (fn-rtc-nstatic (fn-rtc-config s)) j)
                  (equal (fn-rtc-local-ranked j s) (fn-rtc-local-ranked j s2))
                  (equal (fn-rtc-e-id e) j) (equal (fn-rtc-target s e) j)
                  (not (equal (fn-rtc-e-kind e) :accept))) (and (fn-rtc-acts-on-p s e) (equal (fn-rtc-e-kind e) :close))) (and (equal (fn-rtc-local-ranked j (mv-nth 0 (fn-rtc-step s e q)))
                        (fn-rtc-local-ranked j (mv-nth 0 (fn-rtc-step s2 (fn-rtc-corresponding-event j e s s2) q))))
                 (equal (fn-rtc-ranked (fn-rtc-uses-of j (mv-nth 1 (fn-rtc-step s e q))) 0)
                        (fn-rtc-ranked (fn-rtc-uses-of j (mv-nth 1 (fn-rtc-step s2 (fn-rtc-corresponding-event j e s s2) q))) 0))))
   :hints (("Goal" :in-theory
            (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
             '(fn-rtc-step-is-step-state fn-rtc-step-state fn-rtc-step-actions-is fn-rtc-step-actions fn-rtc-step*
               fn-rtc-local-ranked-rearm fn-rtc-uses-of-rearm-actions fn-rtc-end-use-column-lengths
               fn-rtc-ranked-equal-is-ranked fn-rtc-ranked-equal-uses-of fn-rtc-u-hd
               (:executable-counterpart fn-rtc-ranked-equal-p) (:executable-counterpart fn-rtc-ranked) (:executable-counterpart equal)
               (:executable-counterpart member-equal) natp))
            :use (fn-rtc-corresponding-acts fn-rtc-corresponding-hand fn-rtc-own-target-not-hand-delivery
                  fn-rtc-corresponding-end-use fn-rtc-corresponding-fields fn-rtc-corresponding-matching
                  fn-rtc-corresponding-outcome fn-rtc-corresponding-buffer fn-rtc-local-ranked-shape
                  fn-rtc-acting-matches-use (:instance fn-rtc-close-local-ranked (s1 (fn-rtc-end-use s e)) (s2 (fn-rtc-end-use s2 (fn-rtc-corresponding-event j e s s2))) (inc (fn-rtc-e-inc e))))))))

(local
 (defthm fn-rtc-matched-hand-handle
   (implies (and (fn-rtc-invp s) (fn-rtc-completionp e) (equal (fn-rtc-e-kind e) :hand)
                 (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))
            (fn-rtc-handlep (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))))
   :hints (("Goal" :in-theory
            (union-theories (theory 'minimal-theory) '(fn-rtc-use-okp fn-rtc-usep fn-rtc-u-hd (:executable-counterpart member-equal)))
            :use (fn-rtc-invp-is-core-and-admission
                  (:instance fn-rtc-core-invp-found-use (key (fn-rtc-key e)))
                  (:instance fn-rtc-matching-use-fields (uses (fn-rtc-uses s))))))))

(local
 (defthm fn-rtc-corresponding-step-deliver
   (implies (and (and (fn-rtc-invp s) (fn-rtc-invp s2) (natp j) (< 0 j)
                  (< (fn-rtc-nstatic (fn-rtc-config s)) j)
                  (equal (fn-rtc-local-ranked j s) (fn-rtc-local-ranked j s2))
                  (equal (fn-rtc-e-id e) j) (equal (fn-rtc-target s e) j)
                  (not (equal (fn-rtc-e-kind e) :accept))) (and (fn-rtc-acts-on-p s e) (not (equal (fn-rtc-e-kind e) :close)))) (and (equal (fn-rtc-local-ranked j (mv-nth 0 (fn-rtc-step s e q)))
                        (fn-rtc-local-ranked j (mv-nth 0 (fn-rtc-step s2 (fn-rtc-corresponding-event j e s s2) q))))
                 (equal (fn-rtc-ranked (fn-rtc-uses-of j (mv-nth 1 (fn-rtc-step s e q))) 0)
                        (fn-rtc-ranked (fn-rtc-uses-of j (mv-nth 1 (fn-rtc-step s2 (fn-rtc-corresponding-event j e s s2) q))) 0))))
   :hints (("Goal" :in-theory
            (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
             '(fn-rtc-step-is-step-state fn-rtc-step-state fn-rtc-step-actions-is fn-rtc-step-actions fn-rtc-step*
               fn-rtc-local-ranked-rearm fn-rtc-uses-of-rearm-actions fn-rtc-end-use-column-lengths
               fn-rtc-ranked-equal-is-ranked fn-rtc-ranked-equal-uses-of fn-rtc-u-hd
               (:executable-counterpart fn-rtc-ranked-equal-p) (:executable-counterpart fn-rtc-ranked) (:executable-counterpart equal)
               (:executable-counterpart member-equal) natp))
            :use (fn-rtc-matched-hand-handle fn-rtc-corresponding-acts fn-rtc-corresponding-hand fn-rtc-own-target-not-hand-delivery
                  fn-rtc-corresponding-end-use fn-rtc-corresponding-fields fn-rtc-corresponding-matching
                  fn-rtc-corresponding-outcome fn-rtc-corresponding-buffer fn-rtc-local-ranked-shape
                  fn-rtc-acting-matches-use (:instance fn-rtc-deliver-local-ranked (s1 (fn-rtc-end-use s e)) (s2 (fn-rtc-end-use s2 (fn-rtc-corresponding-event j e s s2))) (inc (fn-rtc-e-inc e)) (ev (fn-rtc-ev (fn-rtc-e-kind e) (fn-rtc-delivered-outcome (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)) e) j (fn-rtc-e-inc e) nil)))
                  (:instance fn-rtc-deliver-local-ranked (s1 (fn-rtc-end-use s e)) (s2 (fn-rtc-end-use s2 (fn-rtc-corresponding-event j e s s2))) (inc (fn-rtc-e-inc e)) (ev (fn-rtc-ev (fn-rtc-e-kind e) (if (equal (fn-rtc-get 0 (fn-rtc-delivered-outcome (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)) e)) :done) '(:failed :gone) (fn-rtc-delivered-outcome (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)) e)) j (fn-rtc-e-inc e) (list (list (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))) (+ 1 (fn-rtc-b-gen (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))) s))) 0 (len (fn-rtc-b-bytes (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-u-hd (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))) s)))))))))))))

; T17b isolation of occupancy: a connection's own step acts on its local part
; alone, operations by rank, events corresponding; the conclusion restores the
; premise, so it composes over traces
(defthm fn-rtc-connections-see-no-foreign-occupancy
  (let ((e2 (fn-rtc-corresponding-event j e s s2)))
    (implies (and (fn-rtc-invp s) (fn-rtc-invp s2) (natp j)
                  (< (fn-rtc-nstatic (fn-rtc-config s)) j)
                  (equal (fn-rtc-local-ranked j s) (fn-rtc-local-ranked j s2))
                  (equal (fn-rtc-e-id e) j) (equal (fn-rtc-target s e) j)
                  (not (equal (fn-rtc-e-kind e) :accept)))
             (and (equal (fn-rtc-local-ranked j (mv-nth 0 (fn-rtc-step s e q)))
                         (fn-rtc-local-ranked j (mv-nth 0 (fn-rtc-step s2 e2 q))))
                  (equal (fn-rtc-ranked (fn-rtc-uses-of j (mv-nth 1 (fn-rtc-step s e q))) 0)
                         (fn-rtc-ranked (fn-rtc-uses-of j (mv-nth 1 (fn-rtc-step s2 e2 q))) 0)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(natp (:type-prescription fn-rtc-nstatic)))
           :use (fn-rtc-corresponding-step-inactive fn-rtc-corresponding-step-close fn-rtc-corresponding-step-deliver))))

(local
 (defun fn-rtc-action-held-p (a id s)
   (and (equal (fn-rtc-get 1 a) id)
        (let ((hd (fn-rtc-get 0 (fn-rtc-get 4 a))))
          (implies (fn-rtc-handlep hd)
                   (and (fn-rtc-leasedp (fn-rtc-h-buf hd) s)
                        (fn-rtc-held-by-p (fn-rtc-b-owner (fn-rtc-buffer (fn-rtc-h-buf hd) s)) id)))))))

(local
 (defun fn-rtc-actions-held-p (acts id s)
   (if (consp acts)
       (and (fn-rtc-action-held-p (car acts) id s) (fn-rtc-actions-held-p (cdr acts) id s))
     t)))

(local
 (defthm fn-rtc-request-actions-held
   (implies (and (equal (len (fn-rtc-pool s)) (fn-rtc-nbufs (fn-rtc-config s)))
                 (not (fn-rtc-handlep (fn-rtc-s-res (fn-rtc-slot id s)))))
            (fn-rtc-actions-held-p (mv-nth 1 (fn-rtc-request r id inc s)) id
                                  (mv-nth 0 (fn-rtc-request r id inc s))))
   :hints (("Goal" :in-theory
            (union-theories (theory 'minimal-theory)
             '(fn-rtc-request fn-rtc-req-acquire fn-rtc-req-write fn-rtc-req-release
               fn-rtc-req-close fn-rtc-req-cancel fn-rtc-req-submit fn-rtc-submit-okp
               fn-rtc-actions-held-p fn-rtc-action-held-p fn-rtc-held-by-p fn-rtc-leasedp
               fn-rtc-buffer-of-with fn-rtc-issue-frame fn-rtc-buffer-accessors fn-rtc-get-of-cons
               fn-rtc-owner-equality-fields fn-rtc-buffer-of-non-natp fn-rtc-next-op-of-with
               nfix natp car-cons cdr-cons member-equal
               (:type-prescription fn-rtc-h-buf)
               (:executable-counterpart fn-rtc-handlep) (:executable-counterpart equal)
               (:executable-counterpart zp) (:executable-counterpart binary-+)
               (:executable-counterpart unary--)))))))

(local
 (defthm fn-rtc-actions-held-append
   (equal (fn-rtc-actions-held-p (append a b) id s)
          (and (fn-rtc-actions-held-p a id s) (fn-rtc-actions-held-p b id s)))))

(local
 (defthm fn-rtc-action-held-through-requests
   (implies (fn-rtc-action-held-p a id s)
            (fn-rtc-action-held-p a id (mv-nth 0 (fn-rtc-requests reqs k inc s))))
   :hints (("Goal" :in-theory
            (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
             '(fn-rtc-action-held-p fn-rtc-leasedp fn-rtc-requests-keeps-leased))))))

(local
 (defthm fn-rtc-actions-held-through-requests
   (implies (fn-rtc-actions-held-p acts id s)
            (fn-rtc-actions-held-p acts id (mv-nth 0 (fn-rtc-requests reqs k inc s))))
   :hints (("Goal" :induct (fn-rtc-actions-held-p acts id s)
            :in-theory (union-theories (theory 'minimal-theory)
                         '(fn-rtc-actions-held-p fn-rtc-action-held-through-requests))))))

(local
 (defthm fn-rtc-request-preserves-action-context
   (implies (and (equal (len (fn-rtc-pool s)) (fn-rtc-nbufs (fn-rtc-config s)))
                 (not (fn-rtc-handlep (fn-rtc-s-res (fn-rtc-slot id s)))))
            (let ((s2 (mv-nth 0 (fn-rtc-request r id inc s))))
              (and (equal (len (fn-rtc-pool s2)) (fn-rtc-nbufs (fn-rtc-config s2)))
                   (not (fn-rtc-handlep (fn-rtc-s-res (fn-rtc-slot id s2)))))))
   :hints (("Goal" :in-theory
            (union-theories (theory 'minimal-theory)
             '(fn-rtc-request fn-rtc-req-acquire fn-rtc-req-write fn-rtc-req-release
               fn-rtc-req-close fn-rtc-req-cancel fn-rtc-req-submit fn-rtc-issue-frame
               fn-rtc-with-accessors fn-rtc-slot-of-with fn-rtc-len-of-set fn-rtc-s-res fn-rtc-get-of-cons
               car-cons cdr-cons (:executable-counterpart equal) (:executable-counterpart zp)
               (:executable-counterpart unary--) (:executable-counterpart binary-+)
               (:executable-counterpart member-equal)))))))

(local
 (defthm fn-rtc-requests-actions-held
   (implies (and (equal (len (fn-rtc-pool s)) (fn-rtc-nbufs (fn-rtc-config s)))
                 (not (fn-rtc-handlep (fn-rtc-s-res (fn-rtc-slot id s)))))
            (fn-rtc-actions-held-p (mv-nth 1 (fn-rtc-requests reqs id inc s)) id
                                  (mv-nth 0 (fn-rtc-requests reqs id inc s))))
   :hints (("Goal" :induct (fn-rtc-requests reqs id inc s)
            :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
             '(fn-rtc-requests fn-rtc-actions-held-append fn-rtc-request-actions-held
               fn-rtc-actions-held-through-requests fn-rtc-request-preserves-action-context))
            :expand ((fn-rtc-actions-held-p nil id s))))))

(local
 (defthm fn-rtc-deliver-actions-held
   (implies (and (equal (len (fn-rtc-pool s)) (fn-rtc-nbufs (fn-rtc-config s)))
                 (not (fn-rtc-handlep (fn-rtc-s-res (fn-rtc-slot id s)))))
            (fn-rtc-actions-held-p (mv-nth 1 (fn-rtc-deliver s id inc ev q)) id
                                  (mv-nth 0 (fn-rtc-deliver s id inc ev q))))
   :hints (("Goal" :in-theory
            (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
             '(fn-rtc-deliver fn-rtc-requests-actions-held fn-rtc-with-accessors fn-rtc-slot-of-with))))))

(local
 (defthm fn-rtc-slots-resource-not-handle
   (implies (and (natp i) (fn-rtc-slots-okp i slots))
            (not (fn-rtc-handlep (fn-rtc-s-res (fn-rtc-get k slots)))))
   :hints (("Goal" :induct (fn-rtc-ind-free i k slots)
            :in-theory (enable fn-rtc-slots-okp fn-rtc-slotp fn-rtc-s-res fn-rtc-handlep)))))

(local
 (defthm fn-rtc-core-action-context
   (implies (fn-rtc-core-invp s)
            (and (equal (len (fn-rtc-pool s)) (fn-rtc-nbufs (fn-rtc-config s)))
                 (not (fn-rtc-handlep (fn-rtc-s-res (fn-rtc-slot id s))))))
   :hints (("Goal" :in-theory
            (union-theories (theory 'minimal-theory)
             '(fn-rtc-core-invp fn-rtc-slot natp (:executable-counterpart <)))
            :use (fn-rtc-core-invp-shape
                  (:instance fn-rtc-slots-resource-not-handle (i 0) (k id) (slots (fn-rtc-slots s))))))))

(local
 (defthm fn-rtc-action-held-through-rearm
   (implies (fn-rtc-action-held-p a id s)
            (fn-rtc-action-held-p a id (mv-nth 0 (fn-rtc-rearm s))))
   :hints (("Goal" :in-theory
            (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
             '(fn-rtc-action-held-p fn-rtc-leasedp fn-rtc-rearm-frame))))))

(local
 (defthm fn-rtc-actions-held-through-rearm
   (implies (fn-rtc-actions-held-p acts id s)
            (fn-rtc-actions-held-p acts id (mv-nth 0 (fn-rtc-rearm s))))
   :hints (("Goal" :induct (fn-rtc-actions-held-p acts id s)
            :in-theory (union-theories (theory 'minimal-theory)
                         '(fn-rtc-actions-held-p fn-rtc-action-held-through-rearm))))))

(local
 (defthm fn-rtc-actions-held-member
   (implies (and (fn-rtc-actions-held-p acts id s) (member-equal a acts))
            (fn-rtc-action-held-p a id s))
   :hints (("Goal" :in-theory (disable fn-rtc-action-held-p)))))

(local
 (defun fn-rtc-actions-owned-p (acts id s)
   (if (consp acts)
       (and (let* ((a (car acts)) (hd (fn-rtc-get 0 (fn-rtc-get 4 a))))
              (and (or (equal (fn-rtc-get 1 a) id) (equal (fn-rtc-get 0 a) :accept))
                   (implies (fn-rtc-handlep hd)
                            (fn-rtc-held-by-p (fn-rtc-b-owner (fn-rtc-buffer (fn-rtc-h-buf hd) s))
                                              (fn-rtc-get 1 a)))))
            (fn-rtc-actions-owned-p (cdr acts) id s))
     t)))

(local
 (defthm fn-rtc-actions-held-are-owned
   (implies (fn-rtc-actions-held-p acts id s) (fn-rtc-actions-owned-p acts id s))
   :hints (("Goal" :induct (fn-rtc-actions-held-p acts id s)
            :in-theory (union-theories (theory 'minimal-theory) '(fn-rtc-actions-held-p fn-rtc-action-held-p fn-rtc-actions-owned-p))))))

(local
 (defthm fn-rtc-actions-owned-append
   (equal (fn-rtc-actions-owned-p (append a b) id s)
          (and (fn-rtc-actions-owned-p a id s) (fn-rtc-actions-owned-p b id s)))
   :hints (("Goal" :induct (append a b)
            :in-theory (union-theories (theory 'minimal-theory) '(fn-rtc-actions-owned-p binary-append car-cons cdr-cons))))))

(local
 (defthm fn-rtc-actions-owned-through-rearm
   (implies (fn-rtc-actions-owned-p acts id s)
            (fn-rtc-actions-owned-p acts id (mv-nth 0 (fn-rtc-rearm s))))
   :hints (("Goal" :induct (fn-rtc-actions-owned-p acts id s)
            :in-theory (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
                         '(fn-rtc-actions-owned-p fn-rtc-rearm-frame))))))

(local
 (defthm fn-rtc-rearm-actions-owned
   (fn-rtc-actions-owned-p (mv-nth 1 (fn-rtc-rearm s)) id (mv-nth 0 (fn-rtc-rearm s)))
   :hints (("Goal" :in-theory
            (union-theories (theory 'minimal-theory)
             '(fn-rtc-rearm fn-rtc-actions-owned-p fn-rtc-get-of-cons car-cons cdr-cons
               (:executable-counterpart equal) (:executable-counterpart fn-rtc-handlep)
               (:executable-counterpart zp) (:executable-counterpart binary-+) (:executable-counterpart unary--)))))))

(local
 (defthm fn-rtc-deliver-actions-owned
   (implies (and (equal (len (fn-rtc-pool s)) (fn-rtc-nbufs (fn-rtc-config s)))
                 (not (fn-rtc-handlep (fn-rtc-s-res (fn-rtc-slot id s)))))
            (fn-rtc-actions-owned-p (mv-nth 1 (fn-rtc-deliver s id inc ev q)) id
                                   (mv-nth 0 (fn-rtc-deliver s id inc ev q))))
   :hints (("Goal" :in-theory (theory 'minimal-theory)
            :use (fn-rtc-deliver-actions-held
                  (:instance fn-rtc-actions-held-are-owned
                    (acts (mv-nth 1 (fn-rtc-deliver s id inc ev q)))
                    (s (mv-nth 0 (fn-rtc-deliver s id inc ev q)))))))))

(local
 (defthm fn-rtc-accept-actions-owned
   (implies (equal (len (fn-rtc-pool s)) (fn-rtc-nbufs (fn-rtc-config s)))
            (fn-rtc-actions-owned-p (mv-nth 1 (fn-rtc-accept-branch s out q))
                                   (nfix (fn-rtc-free-slot 0 (fn-rtc-slots s)))
                                   (mv-nth 0 (fn-rtc-accept-branch s out q))))
   :hints (("Goal" :in-theory
            (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
             '(fn-rtc-free-slot-in-range fn-rtc-accept-branch fn-rtc-actions-owned-append fn-rtc-actions-owned-through-rearm
               fn-rtc-deliver-actions-owned fn-rtc-rearm-actions-owned
               fn-rtc-with-accessors fn-rtc-slot-of-with fn-rtc-slot-accessors
               nfix natp fn-rtc-handlep true-listp len (:type-prescription fn-rtc-s-inc)
               (:executable-counterpart fn-rtc-get) (:executable-counterpart equal)))
            :use ((:instance fn-rtc-free-slot-natp (i 0) (slots (fn-rtc-slots s))))))))


(local
 (defthm fn-rtc-accept-not-done-actions-owned
   (implies (not (equal (fn-rtc-get 0 out) :done))
            (fn-rtc-actions-owned-p (mv-nth 1 (fn-rtc-accept-branch s out q)) id
                                   (mv-nth 0 (fn-rtc-accept-branch s out q))))
   :hints (("Goal" :in-theory
            (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
             '(fn-rtc-accept-branch fn-rtc-rearm-actions-owned))))))

(local
 (defthm fn-rtc-close-actions-owned
   (fn-rtc-actions-owned-p (mv-nth 1 (fn-rtc-close-branch s id inc)) j
                          (mv-nth 0 (fn-rtc-close-branch s id inc)))
   :hints (("Goal" :in-theory
            (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
             '(fn-rtc-close-branch-is-rearm fn-rtc-rearm-actions-owned))))))

(local
 (defthm fn-rtc-accept-actions-owned-at
   (implies (and (equal (len (fn-rtc-pool s)) (fn-rtc-nbufs (fn-rtc-config s)))
                 (equal id (nfix (fn-rtc-free-slot 0 (fn-rtc-slots s)))))
            (fn-rtc-actions-owned-p (mv-nth 1 (fn-rtc-accept-branch s out q)) id
                                   (mv-nth 0 (fn-rtc-accept-branch s out q))))
   :hints (("Goal" :in-theory (theory 'minimal-theory) :use fn-rtc-accept-actions-owned))))

(local
 (defthm fn-rtc-step-actions-owned
   (implies (fn-rtc-invp s)
            (fn-rtc-actions-owned-p (mv-nth 1 (fn-rtc-step s e q)) (fn-rtc-target s e)
                                   (mv-nth 0 (fn-rtc-step s e q))))
   :hints (("Goal" :in-theory
            (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
             '(fn-rtc-step-actions-is fn-rtc-step-actions fn-rtc-step* fn-rtc-step-is-step-state fn-rtc-step-state
               fn-rtc-target fn-rtc-hand-to fn-rtc-slots-of-end-use-when-acting
               (:executable-counterpart member-equal) (:executable-counterpart equal)
               fn-rtc-actions-owned-append fn-rtc-actions-owned-through-rearm
               fn-rtc-rearm-actions-owned fn-rtc-deliver-actions-owned fn-rtc-accept-actions-owned-at
               fn-rtc-accept-not-done-actions-owned fn-rtc-close-actions-owned
               fn-rtc-core-action-context fn-rtc-end-use-preserves-core-invp fn-rtc-delivered-outcome-done))
            :use (fn-rtc-invp-is-core-and-admission fn-rtc-hand-delivers-kind
                  (:instance fn-rtc-delivered-outcome-done (u (fn-rtc-find-use (fn-rtc-key e) (fn-rtc-uses s)))))))))

(local
 (defthm fn-rtc-actions-owned-member
   (implies (and (fn-rtc-actions-owned-p acts id s) (member-equal a acts))
            (and (or (equal (fn-rtc-get 1 a) id) (equal (fn-rtc-get 0 a) :accept))
                 (implies (fn-rtc-handlep (fn-rtc-get 0 (fn-rtc-get 4 a)))
                          (fn-rtc-held-by-p (fn-rtc-b-owner (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-get 0 (fn-rtc-get 4 a))) s))
                                           (fn-rtc-get 1 a)))))
   :hints (("Goal" :induct (fn-rtc-actions-owned-p acts id s)
            :in-theory (union-theories (theory 'minimal-theory) '(fn-rtc-actions-owned-p member-equal))))))

; T18 every action a step emits is its target's (or the listener's :accept)
; and names only buffers of its own instance
(defthm fn-rtc-actions-name-only-their-instances-buffers
  (implies (and (fn-rtc-invp s) (member-equal a (mv-nth 1 (fn-rtc-step s e q))))
           (and (or (equal (fn-rtc-get 1 a) (fn-rtc-target s e)) (equal (fn-rtc-get 0 a) :accept))
                (implies (fn-rtc-handlep (fn-rtc-get 0 (fn-rtc-get 4 a)))
                         (fn-rtc-held-by-p
                          (fn-rtc-b-owner (fn-rtc-buffer (fn-rtc-h-buf (fn-rtc-get 0 (fn-rtc-get 4 a)))
                                                         (mv-nth 0 (fn-rtc-step s e q))))
                          (fn-rtc-get 1 a)))))
  :hints (("Goal" :in-theory (theory 'minimal-theory)
           :use (fn-rtc-step-actions-owned
                 (:instance fn-rtc-actions-owned-member (acts (mv-nth 1 (fn-rtc-step s e q)))
                   (id (fn-rtc-target s e)) (s (mv-nth 0 (fn-rtc-step s e q))))))))

(local
 (defthm fn-rtc-step-config-is-constant
   (equal (fn-rtc-config (mv-nth 0 (fn-rtc-step s e q))) (fn-rtc-config s))
   :hints (("Goal" :in-theory
 (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
 '(fn-rtc-step-is-step-state fn-rtc-step-state fn-rtc-deliver fn-rtc-accept-branch
   fn-rtc-close-branch fn-rtc-end-use-config fn-rtc-rearm-frame
   fn-rtc-make-accessors fn-rtc-with-accessors fn-rtc-requests-config-is-constant
   car-cons cdr-cons))))))

; T19 static instances stay live at incarnation 1
(defthm fn-rtc-static-instances-stay-live
  (implies (and (fn-rtc-invp s) (posp j) (<= j (fn-rtc-nstatic (fn-rtc-config s))))
           (equal (fn-rtc-slot j (mv-nth 0 (fn-rtc-step s e q))) *fn-rtc-static-slot*))
  :hints (("Goal" :in-theory
 (union-theories (set-difference-theories (theory 'minimal-theory) '(mv-nth))
 '(fn-rtc-invp fn-rtc-slot fn-rtc-step-config-is-constant natp posp nfix
   (:type-prescription fn-rtc-nstatic)))
 :use (fn-rtc-step-preserves-invp
       (:instance fn-rtc-statics-okp-get (j 1) (n (fn-rtc-nstatic (fn-rtc-config s)))
         (k j) (slots (fn-rtc-slots (mv-nth 0 (fn-rtc-step s e q)))))))))
