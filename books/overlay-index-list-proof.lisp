; The active overlay's index window as a list of arena offsets, for any
; schema: starting an overlay gives the empty list; fn2-ov-place inserts its
; offset at the given position (take, the offset, nthcdr) and fn2-ov-reput
; replaces the one there, each leaving every overlay whose window lies apart
; with the entries it had.
(in-package "ACL2")
(include-book "overlay")

; The offsets at index rows BASE .. BASE+N-1, in order.
(defun fn2-ov-index-list (n base fn2-overlay-index)
  (declare (xargs :stobjs fn2-overlay-index :verify-guards nil))
  (if (zp n) nil
    (cons (fn2-overlay-index-off base fn2-overlay-index)
          (fn2-ov-index-list (- n 1) (+ 1 (nfix base)) fn2-overlay-index))))

; Overlay O's entries: the arena offsets of its index window, in key order.
(defun fn2-ov-offsets (o fn2-overlays fn2-overlay-index)
  (declare (xargs :stobjs (fn2-overlays fn2-overlay-index) :verify-guards nil))
  (fn2-ov-index-list (fn2-overlays-count o fn2-overlays) (fn2-overlays-ibase o fn2-overlays) fn2-overlay-index))

(local
 (defthm fn2-overlay-index-off-of-set-off
   (implies (and (natp i) (natp j))
            (equal (fn2-overlay-index-off i (fn2-overlay-index-set-off j v ix))
                   (if (equal i j) v (fn2-overlay-index-off i ix))))))

(local (in-theory (disable fn2-overlay-index-off fn2-overlay-index-set-off)))

(defthm fn2-ov-index-list-len
  (equal (len (fn2-ov-index-list n base ix)) (nfix n)))

(defthm true-listp-of-fn2-ov-index-list
  (true-listp (fn2-ov-index-list n base ix))
  :rule-classes :type-prescription)

(defthm fn2-ov-index-list-split
  (implies (and (natp a) (natp b) (natp base))
           (equal (fn2-ov-index-list (+ a b) base ix)
                  (append (fn2-ov-index-list a base ix) (fn2-ov-index-list b (+ base a) ix))))
  :rule-classes nil
  :hints (("Goal" :induct (fn2-ov-index-list a base ix))))

(defthm fn2-ov-index-list-take
  (implies (and (natp p) (natp n) (natp base) (<= p n))
           (equal (take p (fn2-ov-index-list n base ix)) (fn2-ov-index-list p base ix)))
  :hints (("Goal" :use ((:instance fn2-ov-index-list-split (a p) (b (- n p)))))))

(local
 (defthm fn2-ov-nthcdr-of-append-at-len
   (implies (equal (len a) p) (equal (nthcdr p (append a b)) b))))

(defthm fn2-ov-index-list-nthcdr
  (implies (and (natp p) (natp n) (natp base) (<= p n))
           (equal (nthcdr p (fn2-ov-index-list n base ix)) (fn2-ov-index-list (- n p) (+ base p) ix)))
  :hints (("Goal" :do-not-induct t :in-theory (disable fn2-ov-index-list fn2-ov-nthcdr-of-append-at-len)
           :use ((:instance fn2-ov-index-list-split (a p) (b (- n p)))
                 (:instance fn2-ov-nthcdr-of-append-at-len (a (fn2-ov-index-list p base ix))
                            (b (fn2-ov-index-list (- n p) (+ base p) ix)))))))

(local
 (defun fn2-ov-index-walk (p n base)
   (if (zp p) (list n base) (fn2-ov-index-walk (- p 1) (- n 1) (+ 1 base)))))

(defthm fn2-ov-index-list-nth
  (implies (and (natp p) (natp base) (< p (nfix n)))
           (equal (nth p (fn2-ov-index-list n base ix)) (fn2-overlay-index-off (+ base p) ix)))
  :hints (("Goal" :induct (fn2-ov-index-walk p n base) :in-theory (enable nth) :expand ((fn2-ov-index-list n base ix)))))

; One row written: outside the window nothing moves; inside, that position.
(defthm fn2-ov-index-list-of-set-off
  (implies (and (natp base) (natp r))
           (equal (fn2-ov-index-list n base (fn2-overlay-index-set-off r v ix))
                  (if (and (<= base r) (< r (+ base (nfix n))))
                      (update-nth (- r base) v (fn2-ov-index-list n base ix))
                    (fn2-ov-index-list n base ix))))
  :hints (("Goal" :induct (fn2-ov-index-list n base ix) :in-theory (enable update-nth))))

; Opening the gap: what fn2-ov-insert-at leaves in each row.
(defthm fn2-ov-insert-at-row
  (implies (and (natp at) (natp n) (natp r)
                (< (+ at n) (fn2-overlay-index-rows ix)) (unsigned-byte-p 32 off))
           (equal (fn2-overlay-index-off r (mv-nth 1 (fn2-ov-insert-at n at off ix)))
                  (cond ((or (< r at) (< (+ at n) r)) (fn2-overlay-index-off r ix))
                        ((equal r at) off)
                        (t (fn2-overlay-index-off (- r 1) ix)))))
  :hints (("Goal" :induct (fn2-ov-insert-at n at off ix) :in-theory (enable fn2-ov-insert-at))))

(defthm fn2-ov-insert-at-ok
  (implies (and (natp at) (natp n) (< (+ at n) (fn2-overlay-index-rows ix)) (unsigned-byte-p 32 off))
           (equal (car (fn2-ov-insert-at n at off ix)) :ok))
  :hints (("Goal" :induct (fn2-ov-insert-at n at off ix) :in-theory (enable fn2-ov-insert-at))))
(defthm fn2-ov-index-list-of-insert-at-outside
  (implies (and (natp at) (natp n) (natp base)
                (< (+ at n) (fn2-overlay-index-rows ix)) (unsigned-byte-p 32 off)
                (or (<= (+ base (nfix m)) at) (< (+ at n) base)))
           (equal (fn2-ov-index-list m base (mv-nth 1 (fn2-ov-insert-at n at off ix)))
                  (fn2-ov-index-list m base ix)))
  :hints (("Goal" :induct (fn2-ov-index-list m base ix))))

(local
 (defthm fn2-ov-index-list-of-insert-at-shifted
   (implies (and (natp at) (natp n) (natp b) (<= at b) (<= (+ b (nfix m)) (+ at n))
                 (< (+ at n) (fn2-overlay-index-rows ix)) (unsigned-byte-p 32 off))
            (equal (fn2-ov-index-list m (+ 1 b) (mv-nth 1 (fn2-ov-insert-at n at off ix)))
                   (fn2-ov-index-list m b ix)))
   :hints (("Goal" :induct (fn2-ov-index-walk m m b)))))

(defthm fn2-ov-index-list-of-insert-at
  (implies (and (natp at) (natp n) (< (+ at n) (fn2-overlay-index-rows ix)) (unsigned-byte-p 32 off))
           (equal (fn2-ov-index-list (+ 1 n) at (mv-nth 1 (fn2-ov-insert-at n at off ix)))
                  (cons off (fn2-ov-index-list n at ix))))
  :hints (("Goal" :expand ((fn2-ov-index-list (+ 1 n) at (mv-nth 1 (fn2-ov-insert-at n at off ix)))))))

(defthm fn2-ov-index-list-insert-window-parts
    (implies (and (natp b) (natp pos) (natp c) (<= pos c)
                  (< (+ b c) (fn2-overlay-index-rows ix)) (unsigned-byte-p 32 off))
             (equal (fn2-ov-index-list (+ 1 c) b (mv-nth 1 (fn2-ov-insert-at (- c pos) (+ b pos) off ix)))
                    (append (fn2-ov-index-list pos b ix) (cons off (fn2-ov-index-list (- c pos) (+ b pos) ix)))))
  :hints (("Goal" :do-not-induct t :in-theory (disable fn2-ov-index-list)
           :use ((:instance fn2-ov-index-list-split (a pos) (b (+ 1 c (- pos))) (base b)
                            (ix (mv-nth 1 (fn2-ov-insert-at (- c pos) (+ b pos) off ix))))))))

; The overlay's list insertion: fn2-ov-place succeeds exactly when the
; position is within the count and the window has room, and then the
; offsets become the old ones with OFF inserted at POS.
(defthm fn2-ov-place-ok
  (implies (fn2-overlaysp ov)
           (equal (equal (car (fn2-ov-place o pos off end ov ix)) :ok)
                  (and (fn2-ov-okp o ov ix) (natp pos) (<= pos (fn2-overlays-count o ov))
                       (< (fn2-overlays-count o ov) (fn2-overlays-icap o ov))
                       (unsigned-byte-p 32 off) (unsigned-byte-p 32 end))))
  :hints (("Goal" :in-theory (enable fn2-ov-place fn2-ov-okp))))

; Reading an overlay field back after a write of one field of one row.
(defun fn2-ov-frame-events-1 (f setters)
  (declare (xargs :verify-guards nil))
  (if (atom setters) nil
    (let* ((g (car setters)) (get (fn2-columns-sym 'fn2-overlays (concatenate 'string "-" (symbol-name f))))
           (set (fn2-columns-sym 'fn2-overlays (concatenate 'string "-SET-" (symbol-name g)))))
      (cons `(defthm ,(fn2-columns-sym get (concatenate 'string "-OF-SET-" (symbol-name g)))
               (implies (and (natp o) (natp p))
                        (equal (,get p (,set o v ov))
                               ,(if (eq f g) `(if (equal p o) v (,get p ov)) `(,get p ov))))
               :hints (("Goal" :in-theory (enable ,get))))
            (fn2-ov-frame-events-1 f (cdr setters))))))

(defun fn2-ov-frame-events (fields setters)
  (declare (xargs :verify-guards nil))
  (if (atom fields) nil
    (append (fn2-ov-frame-events-1 (car fields) setters) (fn2-ov-frame-events (cdr fields) setters))))

(make-event
 (cons 'progn
       (fn2-ov-frame-events '(phase schema slot gen fill cap count ibase icap okind oslot ogen cov batch seq)
                            '(count fill))))

(local (in-theory (disable fn2-overlays-phase fn2-overlays-schema fn2-overlays-slot fn2-overlays-gen fn2-overlays-fill
                    fn2-overlays-cap fn2-overlays-count fn2-overlays-ibase fn2-overlays-icap fn2-overlays-okind
                    fn2-overlays-oslot fn2-overlays-ogen fn2-overlays-cov fn2-overlays-batch fn2-overlays-seq
                    fn2-overlays-rows fn2-overlay-index-rows fn2-overlays-set-count fn2-overlays-set-fill)))

(defthm fn2-ov-place-tables
  (let ((r (fn2-ov-place o pos off end ov ix)))
    (implies (equal (car r) :ok)
             (and (equal (mv-nth 1 r) (fn2-overlays-set-fill o end (fn2-overlays-set-count o (+ 1 (fn2-overlays-count o ov)) ov)))
                  (equal (mv-nth 2 r) (mv-nth 1 (fn2-ov-insert-at (- (fn2-overlays-count o ov) pos)
                                                                   (+ (fn2-overlays-ibase o ov) pos) off ix))))))
  :hints (("Goal" :in-theory (enable fn2-ov-place))))

(in-theory (disable fn2-ov-offsets))

(defthm fn2-ov-place-offsets
  (let ((xs (fn2-ov-offsets o ov ix)) (r (fn2-ov-place o pos off end ov ix)))
    (implies (and (fn2-overlaysp ov) (equal (car r) :ok))
             (equal (fn2-ov-offsets o (mv-nth 1 r) (mv-nth 2 r))
                    (append (take pos xs) (cons off (nthcdr pos xs))))))
  :hints (("Goal" :in-theory (e/d (fn2-ov-okp fn2-ov-offsets) (fn2-ov-index-list fn2-ov-place-ok fn2-ov-index-list-insert-window-parts))
           :use (fn2-ov-place-ok
                 (:instance fn2-ov-index-list-insert-window-parts
                            (b (fn2-overlays-ibase o ov)) (c (fn2-overlays-count o ov)))))))

(make-event
 (cons 'progn
       (fn2-ov-frame-events '(count ibase)
                            '(phase schema slot gen cap ibase icap okind oslot ogen cov batch seq))))

(local (in-theory (disable fn2-overlays-set-phase fn2-overlays-set-schema fn2-overlays-set-slot fn2-overlays-set-gen
                    fn2-overlays-set-cap fn2-overlays-set-ibase fn2-overlays-set-icap fn2-overlays-set-okind
                    fn2-overlays-set-oslot fn2-overlays-set-ogen fn2-overlays-set-cov fn2-overlays-set-batch
                    fn2-overlays-set-seq)))

(defthm fn2-ov-reput-ok
  (implies (fn2-overlaysp ov)
           (equal (equal (car (fn2-ov-reput o pos off end ov ix)) :ok)
                  (and (fn2-ov-okp o ov ix) (natp pos) (< pos (fn2-overlays-count o ov))
                       (unsigned-byte-p 32 off) (unsigned-byte-p 32 end))))
  :hints (("Goal" :in-theory (enable fn2-ov-reput fn2-ov-okp))))

(defthm fn2-ov-reput-tables
  (let ((r (fn2-ov-reput o pos off end ov ix)))
    (implies (equal (car r) :ok)
             (and (equal (mv-nth 1 r) (fn2-overlays-set-fill o end ov))
                  (equal (mv-nth 2 r) (fn2-overlay-index-set-off (+ (fn2-overlays-ibase o ov) pos) off ix)))))
  :hints (("Goal" :in-theory (enable fn2-ov-reput))))

(defthm fn2-ov-reput-offsets
  (let ((xs (fn2-ov-offsets o ov ix)) (r (fn2-ov-reput o pos off end ov ix)))
    (implies (and (fn2-overlaysp ov) (equal (car r) :ok))
             (equal (fn2-ov-offsets o (mv-nth 1 r) (mv-nth 2 r)) (update-nth pos off xs))))
  :hints (("Goal" :in-theory (e/d (fn2-ov-okp fn2-ov-offsets) (fn2-ov-index-list fn2-ov-reput-ok))
           :use fn2-ov-reput-ok)))

; Another overlay whose window lies outside O's keeps its entries.
(defun-nx fn2-ov-apart-p (o p ov)
  (and (natp p) (not (equal p o))
       (or (<= (+ (fn2-overlays-ibase p ov) (fn2-overlays-count p ov)) (fn2-overlays-ibase o ov))
           (<= (+ (fn2-overlays-ibase o ov) (fn2-overlays-icap o ov)) (fn2-overlays-ibase p ov)))))

(defthm fn2-ov-place-keeps-apart
  (let ((r (fn2-ov-place o pos off end ov ix)))
    (implies (and (fn2-overlaysp ov) (equal (car r) :ok) (fn2-ov-apart-p o p ov) (< p (fn2-overlays-rows ov)))
             (equal (fn2-ov-offsets p (mv-nth 1 r) (mv-nth 2 r)) (fn2-ov-offsets p ov ix))))
  :hints (("Goal" :in-theory (e/d (fn2-ov-okp fn2-ov-offsets fn2-ov-apart-p) (fn2-ov-index-list fn2-ov-place-ok))
           :use fn2-ov-place-ok)))

(defthm fn2-ov-reput-keeps-apart
  (let ((r (fn2-ov-reput o pos off end ov ix)))
    (implies (and (fn2-overlaysp ov) (equal (car r) :ok) (fn2-ov-apart-p o p ov) (< p (fn2-overlays-rows ov)))
             (equal (fn2-ov-offsets p (mv-nth 1 r) (mv-nth 2 r)) (fn2-ov-offsets p ov ix))))
  :hints (("Goal" :in-theory (e/d (fn2-ov-okp fn2-ov-offsets fn2-ov-apart-p) (fn2-ov-index-list fn2-ov-reput-ok))
           :use fn2-ov-reput-ok)))

; Starting an overlay: an empty entry list over its window.
(defthm fn2-ov-start-tables
  (let ((r (fn2-ov-start o schema slot gen ibase icap okind oslot ogen cov fn2-overlays ix pool)))
    (implies (equal (car r) :ok)
             (equal (mv-nth 1 r)
                    (fn2-overlays-put o (phase *fn2-overlay-phase-active*) (schema schema) (slot slot) (gen gen)
                      (fill 0) (cap (fn2-pool-slot-cap slot pool)) (count 0) (ibase ibase) (icap icap)
                      (okind okind) (oslot oslot) (ogen ogen) (cov cov) (batch 0) (seq 0)))))
  :hints (("Goal" :in-theory (enable fn2-ov-start))))

(defthm fn2-ov-start-empty
  (let ((r (fn2-ov-start o schema slot gen ibase icap okind oslot ogen cov ov ix pool)))
    (implies (equal (car r) :ok)
             (and (equal (fn2-ov-offsets o (mv-nth 1 r) ix) nil)
                  (equal (fn2-overlays-count o (mv-nth 1 r)) 0)
                  (equal (fn2-overlays-phase o (mv-nth 1 r)) *fn2-overlay-phase-active*)
                  (equal (fn2-overlays-schema o (mv-nth 1 r)) schema)
                  (equal (fn2-overlays-ibase o (mv-nth 1 r)) ibase)
                  (equal (fn2-overlays-icap o (mv-nth 1 r)) icap))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn2-ov-offsets fn2-overlays-phase fn2-overlays-count fn2-overlays-schema
                            fn2-overlays-ibase fn2-overlays-icap)
                           (fn2-ov-start)))))

(defthm fn2-ov-start-ok-row
  (implies (equal (car (fn2-ov-start o schema slot gen ibase icap okind oslot ogen cov ov ix pool)) :ok)
           (and (natp o) (< o (fn2-overlays-rows ov))))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable fn2-ov-start))))
(defthm fn2-ov-start-keeps-others
  (let ((r (fn2-ov-start o schema slot gen ibase icap okind oslot ogen cov ov ix pool)))
    (implies (and (equal (car r) :ok) (natp p) (not (equal p o)))
             (equal (fn2-ov-offsets p (mv-nth 1 r) ix) (fn2-ov-offsets p ov ix))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn2-ov-offsets fn2-overlays-count fn2-overlays-ibase) (fn2-ov-start fn2-ov-index-list)))))

(defthm fn2-ov-start-okp
  (let ((r (fn2-ov-start o schema slot gen ibase icap okind oslot ogen cov ov ix pool)))
    (implies (and (equal (car r) :ok) (fn2-overlays-wfp ov) (fn2-overlay-index-wfp ix))
             (fn2-ov-okp o (mv-nth 1 r) ix)))
  :hints (("Goal" :do-not-induct t :use fn2-ov-start-empty
           :in-theory (e/d (fn2-ov-start fn2-ov-okp fn2-overlays-rows fn2-overlays-count fn2-overlays-ibase
                            fn2-overlays-icap fn2-overlay-index-rows)
                           (fn2-ov-start-tables fn2-ov-start-empty)))))
