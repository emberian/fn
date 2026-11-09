; The rows an owner kind K holds in the operation table and the pool, as one
; observation, and what each write of another owner keeps of it. The dispatch's
; held frame (machines.lisp fn2-dh-chain-*, assembly-dispatch) is this
; observation at the commit kind, kept by every run of a kind that holds no
; batch membership.
(in-package "ACL2")
(include-book "arm-children")
(deflabel fn2-dh-start)

;; ---------------------------------------------------------------------------
;; HELD ROWS. An operation row K owns that is not free; a pool row K owns that
;; is neither free nor handed (a handed row is its target's to accept,
;; fn2-pool-accept-own). Free rows are excluded because the reserves take the
;; free head after checking only its phase or state.
(defun-nx fn2-dh-op-held (k s ops)
  (and (equal (nth s (nth *fn2-ops-owner-kind$ai* ops)) k)
       (not (equal (nth s (nth *fn2-ops-phase$ai* ops)) *fn2-op-phase-free*))))
(defun-nx fn2-dh-pool-held (k r pool)
  (and (equal (nth r (nth *fn2-pool-owner-kind$ai* pool)) k)
       (not (equal (nth r (nth *fn2-pool-state$ai* pool)) *fn2-pool-state-free*))
       (not (equal (nth r (nth *fn2-pool-state$ai* pool)) *fn2-pool-state-handed*))))

;; A row's values at the column indices COLS.
(defun-nx fn2-dh-row (cols s x)
  (if (atom cols) nil (cons (nth s (nth (car cols) x)) (fn2-dh-row (cdr cols) s x))))
(defun fn2-dh-range (i n)
  (declare (xargs :verify-guards nil :measure (nfix (- n i))))
  (if (or (not (natp i)) (not (natp n)) (>= i n)) nil (cons i (fn2-dh-range (+ 1 i) n))))
;; Every operation column but the free-chain link (meaningful only on a free
;; row); every pool column but the free-chain link and the extent (base, cap:
;; observed for every row, below).
(make-event
 (let* ((ops (strip-cars (fn2-view-layout 'fn2-ops (w state))))
        (pool (strip-cars (fn2-view-layout 'fn2-pool (w state)))))
   (value `(progn
             (defconst *fn2-dh-op-cols*
               ',(remove (position-eq 'next-free ops) (fn2-dh-range 0 (len ops))))
             (defconst *fn2-dh-pool-cols*
               ',(set-difference-equal (fn2-dh-range 0 (len pool))
                                       (list (position-eq 'next-free pool) (position-eq 'base pool)
                                             (position-eq 'cap pool))))))))
(assert-event (and (equal *fn2-ops-rows* (+ 1 (car (last *fn2-dh-op-cols*))))
                   (member-equal *fn2-ops-owner-kind$ai* *fn2-dh-op-cols*)
                   (member-equal *fn2-ops-phase$ai* *fn2-dh-op-cols*)
                   (member-equal *fn2-pool-owner-kind$ai* *fn2-dh-pool-cols*)
                   (member-equal *fn2-pool-state$ai* *fn2-dh-pool-cols*)
                   (not (member-equal *fn2-pool-base$ai* *fn2-dh-pool-cols*))
                   (not (member-equal *fn2-pool-cap$ai* *fn2-dh-pool-cols*))
                   (< (car (last *fn2-dh-pool-cols*)) *fn2-pool-rows*)
                   (< *fn2-pool-rows* *fn2-pool-datai*)))

;; ---------------------------------------------------------------------------
;; THE OBSERVATION. Operations: the row count and every held row's columns.
;; Pool: the row count, every row's extent, every held row's columns, and --
;; when the extents are ordered and disjoint, a fact of the extents alone --
;; the data length and every held row's octets over its whole extent.
(defun-nx fn2-dh-op-rows (k n ops)
  (if (zp n) nil
    (cons (and (fn2-dh-op-held k (1- n) ops) (fn2-dh-row *fn2-dh-op-cols* (1- n) ops))
          (fn2-dh-op-rows k (1- n) ops))))
(defun-nx fn2-dh-ops-obs (k ops)
  (cons (nth *fn2-ops-rows* ops) (fn2-dh-op-rows k (nfix (nth *fn2-ops-rows* ops)) ops)))

(defun-nx fn2-dh-extents (n pool)
  (if (zp n) nil
    (cons (cons (nth (1- n) (nth *fn2-pool-base$ai* pool)) (nth (1- n) (nth *fn2-pool-cap$ai* pool)))
          (fn2-dh-extents (1- n) pool))))
(defun-nx fn2-dh-ordered (n pool)
  ; row i's extent ends at or before row i+1's begins
  (if (zp n) t
    (and (natp (nth (1- n) (nth *fn2-pool-base$ai* pool)))
         (natp (nth (1- n) (nth *fn2-pool-cap$ai* pool)))
         (or (zp (1- n))
             (<= (+ (nth (- n 2) (nth *fn2-pool-base$ai* pool)) (nth (- n 2) (nth *fn2-pool-cap$ai* pool)))
                 (nth (1- n) (nth *fn2-pool-base$ai* pool))))
         (fn2-dh-ordered (1- n) pool))))
(defun-nx fn2-dh-pool-rows (k n pool)
  (if (zp n) nil
    (cons (and (fn2-dh-pool-held k (1- n) pool) (fn2-dh-row *fn2-dh-pool-cols* (1- n) pool))
          (fn2-dh-pool-rows k (1- n) pool))))
(defun-nx fn2-dh-octets (k n pool)
  (if (zp n) nil
    (cons (and (fn2-dh-pool-held k (1- n) pool)
               (fn2-pool-logical-octets (nth (1- n) (nth *fn2-pool-cap$ai* pool))
                                        (nth (1- n) (nth *fn2-pool-base$ai* pool)) pool))
          (fn2-dh-octets k (1- n) pool))))
(defun-nx fn2-dh-pool-obs (k pool)
  (let ((n (nfix (nth *fn2-pool-rows* pool))))
    (list (nth *fn2-pool-rows* pool) (fn2-dh-extents n pool) (fn2-dh-pool-rows k n pool)
          (and (natp (nth *fn2-pool-rows* pool)) (fn2-dh-ordered n pool)
               (cons (len (nth *fn2-pool-datai* pool)) (fn2-dh-octets k n pool))))))

