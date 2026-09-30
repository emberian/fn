; fn: the positional schedule for a private protected-extent window.
; PRF-1109 / SCN-1018. Library component, not yet a served implementation.
; The descriptor covers ELEN bytes, not one record. Neither BEGIN nor TICK
; traverses those bytes. A requested window is one scheduling quantum;
; subsequent windows continue the same payload without a stored-data cap.
(in-package "ACL2")
(include-book "packed-octets")

; State = (phase file eoff elen woff wn expected pos ticket incarnation lease poff plen offset).
; WOFF is absolute within the protected prefix, not a file offset.
(defun fn-ewp-state (phase file eoff elen woff wn expected pos ticket incarnation lease poff plen offset)
  (declare (xargs :guard t))
  (list phase file eoff elen woff wn expected pos ticket incarnation lease poff plen offset))

(defun fn-ewp-begin (file eoff elen poff plen offset ticket incarnation lease expected)
  (declare (xargs :guard (and (natp file) (natp eoff) (natp elen)
                              (natp poff) (natp plen) (natp offset)
                              (natp expected))))
  (if (and (<= eoff poff) (<= (+ poff plen) (+ eoff elen))
           (<= offset plen))
      (fn-ewp-state (if (zp elen) :trailer :scan)
                    file eoff elen (+ (- poff eoff) offset)
                    (min 16384 (- plen offset)) expected 0 ticket incarnation lease poff plen offset)
    (fn-ewp-state :bounds file eoff elen 0 0 expected 0 ticket incarnation lease poff plen offset)))

(defun fn-ewp-demand (s)
  (declare (xargs :guard (true-listp s)))
  (case (nth 0 s)
    (:scan (min 64 (nfix (- (nfix (nth 3 s)) (nfix (nth 7 s))))))
    (:trailer 32)
    (otherwise 0)))

(defun fn-ewp-effect (s)
  (declare (xargs :guard (true-listp s)))
  (if (zp (fn-ewp-demand s)) nil
    (list (nth 8 s) (nth 9 s) (nth 10 s) (nth 1 s)
          (+ (nfix (nth 2 s))
             (if (eq (nth 0 s) :trailer) (nfix (nth 3 s)) (nfix (nth 7 s))))
          (fn-ewp-demand s) (nth 0 s))))

(defun fn-ewp-with-phase-pos (phase pos s)
  (declare (xargs :guard (true-listp s)))
  (fn-ewp-state phase (nth 1 s) (nth 2 s) (nth 3 s) (nth 4 s) (nth 5 s)
                (nth 6 s) pos (nth 8 s) (nth 9 s) (nth 10 s)
                (nth 11 s) (nth 12 s) (nth 13 s)))

; A completion is consumed only for the exact outstanding effect, including
; physical incarnation and lease. The caller feeds/copies its bytes BEFORE
; applying this completion. A read failure never publishes a partial window.
(defun fn-ewp-complete-read (effect got verdict s)
  (declare (xargs :guard (and (natp got) (true-listp s))))
  (cond ((or (not (fn-ewp-effect s)) (not (equal effect (fn-ewp-effect s))))
         (mv :stale s))
        ((or (not (eq verdict :ok)) (not (equal got (fn-ewp-demand s))))
         (mv :read (fn-ewp-with-phase-pos :read (nth 7 s) s)))
        ((eq (nth 0 s) :trailer)
         (mv :digest (fn-ewp-with-phase-pos :digest (nth 7 s) s)))
        (t (let ((pos (+ (nfix (nth 7 s)) (fn-ewp-demand s))))
             (mv :continue
                 (fn-ewp-with-phase-pos
                   (if (equal pos (nth 3 s)) :trailer :scan) pos s))))))

; Position in the private output buffer for a byte in the issued scan.
; NIL means hash it but do not retain it. The host must never calculate a
; competing overlap or file offset; it executes these core decisions.
(defun fn-ewp-window-index (i s)
  (declare (xargs :guard (and (natp i) (true-listp s))))
  (let ((p (+ (nfix (nth 7 s)) i))
        (a (nfix (nth 4 s)))
        (n (nfix (nth 5 s))))
    (and (eq (nth 0 s) :scan) (< i (fn-ewp-demand s))
         (<= a p) (< p (+ a n)) (- p a))))

; Inspect exactly N cells. Even a malformed external tail cannot turn a
; trailer check into a whole-input traversal.
(defun fn-ewp-octets-n-p (n xs)
  (declare (xargs :guard (natp n) :measure (nfix n)))
  (if (zp n) (null xs)
    (and (consp xs) (fn-bch-octetp (car xs))
         (fn-ewp-octets-n-p (1- n) (cdr xs)))))

(defthm fn-ewp-octets-n-p-is-exact
  (equal (fn-ewp-octets-n-p n xs)
         (and (fn-bch-octetsp xs) (equal (len xs) (nfix n)))))

; A private decoder consumes only the payload intersection of an issued
; prefix block. The two values are offsets within the bounded input buffer.
(defun fn-ewp-payload-span (poff plen s)
  (declare (xargs :guard (and (natp poff) (natp plen) (true-listp s))))
  (let* ((start (+ (nfix (nth 2 s)) (nfix (nth 7 s))))
         (a (max start poff))
         (b (min (+ start (fn-ewp-demand s)) (+ poff plen))))
    (if (and (eq (nth 0 s) :scan) (< a b))
        (list (- a start) (- b a))
      (list 0 0))))

; DIGEST is the final value of the concrete incremental digest over exactly
; the consumed protected prefix. That bridge is deliberately a separate,
; still-open integration obligation: callers cannot assert it by a flag.
(defun fn-ewp-finish (read digest s)
  (declare (xargs :guard (true-listp s)))
  (if (not (and (eq (nth 0 s) :digest)
                (equal (nth 7 s) (nth 3 s)))) (mv :stale s)
    (let ((verdict
           (cond ((not (and (fn-ewp-octets-n-p 32 read)
                            (equal (fn-bch-pack read) (nth 6 s)))) :commitment)
                 ((not (equal digest read)) :digest)
                 (t :verified))))
      (mv verdict (fn-ewp-with-phase-pos verdict (nth 7 s) s)))))

(defun fn-ewp-publication (s)
  (declare (xargs :guard (true-listp s)))
  (and (eq (nth 0 s) :verified)
       (list (nth 8 s) (nth 9 s) (nth 10 s) (nth 1 s)
             (+ (nfix (nth 2 s)) (nfix (nth 4 s))) (nth 5 s))))

(defthm fn-ewp-demand-bounded
  (and (natp (fn-ewp-demand s)) (<= (fn-ewp-demand s) 64))
  :rule-classes nil)

(defthm fn-ewp-window-index-in-range
  (implies (and (natp i) (fn-ewp-window-index i s))
           (and (natp (fn-ewp-window-index i s))
                (< (fn-ewp-window-index i s) (nfix (nth 5 s)))))
  :rule-classes nil)

(defthm fn-ewp-stale-completion-preserves-state
  (implies (not (equal effect (fn-ewp-effect s)))
           (equal (mv-nth 1 (fn-ewp-complete-read effect got verdict s)) s)))

(defthm fn-ewp-read-completion-cannot-publish
  (implies (not (fn-ewp-publication s))
           (not (fn-ewp-publication
                  (mv-nth 1 (fn-ewp-complete-read effect got verdict s))))))

(defthm fn-ewp-finish-publication-requires-integrity
  (implies (and (not (fn-ewp-publication s))
                (fn-ewp-publication (mv-nth 1 (fn-ewp-finish read digest s))))
           (and (equal (nth 0 s) :digest)
                (equal (nth 7 s) (nth 3 s))
                (fn-bch-octetsp read) (equal (len read) 32)
                (equal (fn-bch-pack read) (nth 6 s)) (equal digest read)))
  :rule-classes nil)

(defthm fn-ewp-finish-preserves-window-and-ownership
  (implies (fn-ewp-publication (mv-nth 1 (fn-ewp-finish read digest s)))
           (equal (fn-ewp-publication (mv-nth 1 (fn-ewp-finish read digest s)))
                  (list (nth 8 s) (nth 9 s) (nth 10 s) (nth 1 s)
                        (+ (nfix (nth 2 s)) (nfix (nth 4 s))) (nth 5 s)))))

(in-theory (disable fn-ewp-begin fn-ewp-demand fn-ewp-effect
                    fn-ewp-complete-read fn-ewp-window-index fn-ewp-finish
                    fn-ewp-publication))

(defthm fn-ewp-begin-window-is-bounded
  (implies (and (natp file) (natp eoff) (natp elen) (natp poff)
                (natp plen) (natp offset) (natp expected))
           (let ((s (fn-ewp-begin file eoff elen poff plen offset ticket incarnation lease expected)))
             (and (natp (nth 5 s)) (<= (nth 5 s) 16384)
                  (implies (not (equal (nth 0 s) :bounds))
                           (and (<= (nth 4 s) elen)
                                (<= (+ (nth 4 s) (nth 5 s)) elen))))))
  :hints (("Goal" :in-theory (enable fn-ewp-begin)))
  :rule-classes nil)

(defthm fn-ewp-scan-completion-advances-without-skipping
  (implies (and (equal (nth 0 s) :scan)
                (natp (nth 3 s)) (natp (nth 7 s))
                (< (nth 7 s) (nth 3 s)))
           (let* ((effect (fn-ewp-effect s))
                  (demand (fn-ewp-demand s))
                  (next (mv-nth 1 (fn-ewp-complete-read effect demand :ok s))))
             (and (equal (nth 7 next) (+ (nth 7 s) demand))
                  (< (nth 7 s) (nth 7 next))
                  (<= (nth 7 next) (nth 3 s))
                  (equal (nth 4 effect) (+ (nfix (nth 2 s)) (nth 7 s))) )))
  :hints (("Goal" :in-theory (enable fn-ewp-complete-read fn-ewp-effect fn-ewp-demand)))
  :rule-classes nil)

(defthm fn-ewp-payload-span-bounded
  (implies (and (natp poff) (natp plen))
           (let ((r (fn-ewp-payload-span poff plen s)))
             (and (natp (car r)) (natp (cadr r))
                  (<= (+ (car r) (cadr r)) (fn-ewp-demand s)))))
  :hints (("Goal" :in-theory (enable fn-ewp-demand)))
  :rule-classes nil)

(defun fn-ewp-window-span (s)
  (declare (xargs :guard (true-listp s)))
  (let* ((pos (nfix (nth 7 s))) (woff (nfix (nth 4 s)))
         (a (max pos woff))
         (b (min (+ pos (fn-ewp-demand s)) (+ woff (nfix (nth 5 s))))))
    (if (and (eq (nth 0 s) :scan) (< a b))
        (list (- a pos) (- b a) (- a woff))
      (list 0 0 0))))

(defthm fn-ewp-window-span-bounds
  (let ((r (fn-ewp-window-span s)))
    (and (natp (car r)) (natp (cadr r)) (natp (caddr r))
         (<= (+ (car r) (cadr r)) (fn-ewp-demand s))
         (<= (+ (caddr r) (cadr r)) (nfix (nth 5 s)))))
  :hints (("Goal" :in-theory (e/d (fn-ewp-window-span) (nth nfix fn-ewp-demand))
           :use fn-ewp-demand-bounded))
  :rule-classes nil)
