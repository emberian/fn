; The overlay's bounded binary search and insert, for any schema whose
; comparison of a stored entry with the query agrees with the key order
; (fn2-ovg-reads, a schema's obligation): over sorted rows the search finds
; the query's lower bound and tells a duplicate key from a new one, and
; fn2-ov-insert changes the overlay's offsets as fn2-ov-insert-spec changes
; the sorted entries, which for a new key is the sorted insertion.
(in-package "ACL2")
(include-book "runs-served")
(include-book "overlay-index-list-proof")
(include-book "overlay-order-spec-proof")

; A sorted list's head comes before every later entry.
(local
 (defthm fn2-ovg-sorted-head-before
   (implies (and (fn2-run-sorted-spec key rows) (natp j) (< 0 j) (< j (len rows)))
            (equal (fn2-run-key-order-spec key (car rows) (nth j rows)) :lt))
   :hints (("Goal" :induct (nth j rows) :in-theory (e/d (nth) (fn2-run-key-order-spec fn2-run-key-order-spec-flips))
            :expand ((fn2-run-sorted-spec key rows)))
           (and stable-under-simplificationp
                '(:use ((:instance fn2-run-key-order-spec-transitive
                                   (a (car rows)) (b (cadr rows)) (c (nth (+ -1 j) (cdr rows))))))))))

(local
 (defun fn2-ovg-bound-walk (rows j i)
   (if (or (zp j) (atom rows)) i (fn2-ovg-bound-walk (cdr rows) (1- j) (1+ i)))))

(defthm fn2-ovg-bound-index-in-range
  (let ((index (cadr (fn2-run-lower-bound-spec key rows query i))))
    (implies (natp i) (and (natp index) (<= i index) (<= index (+ i (len rows))))))
  :rule-classes nil
  :hints (("Goal" :induct (fn2-run-lower-bound-spec key rows query i)
           :in-theory (disable fn2-run-key-order-spec fn2-run-key-order-spec-flips))))

; Of a sorted list, the entries before the lower bound are exactly those
; ordered before the query.
(defthm fn2-ovg-row-before-lower-bound
  (let ((bound (cadr (fn2-run-lower-bound-spec key rows query i))))
    (implies (and (natp i) (natp j) (< j (len rows)) (fn2-run-sorted-spec key rows))
             (equal (eq (fn2-run-key-order-spec key (nth j rows) query) :lt)
                    (< (+ i j) bound))))
  :rule-classes nil
  :hints (("Goal" :induct (fn2-ovg-bound-walk rows j i)
           :expand ((fn2-run-lower-bound-spec key rows query i))
           :in-theory (e/d (nth) (fn2-run-key-order-spec fn2-run-key-order-spec-flips)))
          (and stable-under-simplificationp
               '(:use ((:instance fn2-ovg-bound-index-in-range (i (1+ i)) (rows (cdr rows)))
                       (:instance fn2-ovg-sorted-head-before)
                       (:instance fn2-run-key-order-spec-transitive (a (car rows)) (b (nth j rows)) (c query))
                       (:instance fn2-run-key-order-spec-cases (a (car rows)) (b query)))))))

; Each halving step spends at least one bit of the interval.
(local
 (defun fn2-ovg-halves (i j)
   (if (or (zp i) (zp j)) (list i j) (fn2-ovg-halves (floor i 2) (floor j 2)))))
(defthm fn2-ovg-integer-length-monotonic
  (implies (and (natp i) (natp j) (<= i j)) (<= (integer-length i) (integer-length j)))
  :rule-classes nil
  :hints (("Goal" :induct (fn2-ovg-halves i j) :in-theory (enable integer-length))))
(local
 (defthm fn2-ovg-integer-length-of-half
   (implies (natp n) (equal (integer-length (floor n 2)) (if (zp n) 0 (1- (integer-length n)))))
   :rule-classes nil
   :hints (("Goal" :expand ((integer-length n))))))

(local
 (defthm fn2-ovg-half-interval
   (let* ((j (floor (+ lo hi) 2)) (low (if less (1+ j) lo)) (high (if less hi j)))
     (implies (and (natp lo) (natp hi) (< lo hi))
              (and (natp j) (<= lo j) (< j hi) (natp low) (natp high) (<= low high)
                   (<= (- high low) (floor (- hi lo) 2)))))
   :rule-classes nil
   :hints (("Goal" :cases ((< (floor (+ lo hi) 2) (/ (+ lo hi) 2)))))))

(local
 (defthm fn2-ovg-half-bits
   (let* ((j (floor (+ lo hi) 2)) (low (if less (1+ j) lo)) (high (if less hi j)))
     (implies (and (natp lo) (natp hi) (< lo hi))
              (and (natp j) (<= lo j) (< j hi) (natp low) (natp high) (<= low high)
                   (<= (+ 1 (integer-length (- high low))) (integer-length (- hi lo))))))
   :rule-classes nil
   :hints (("Goal" :use (fn2-ovg-half-interval
                         (:instance fn2-ovg-integer-length-monotonic
                           (i (- (if less hi (floor (+ lo hi) 2)) (if less (1+ (floor (+ lo hi) 2)) lo)))
                           (j (floor (- hi lo) 2)))
                         (:instance fn2-ovg-integer-length-of-half (n (- hi lo))))
            :in-theory (disable integer-length floor)))))

; What a schema supplies: an invariant READS over the reader's fields under
; which comparing the entry at any stored position POS with the query gives
; the key order of row POS of ROWS against QUERY, and is kept by the
; comparison; and the overlay holds exactly ROWS.
(encapsulate
  (((fn2-ovg-reads * * * * * * * * * * * * *) => *))
  (local (defun fn2-ovg-reads (o eb qbase qk qs qg ov ix f pool key rows query)
           (declare (ignore o eb qbase qk qs qg ov ix f pool key rows query)) nil))
  (defthm fn2-ovg-reads-bounds
    (implies (fn2-ovg-reads o eb qbase qk qs qg ov ix f pool key rows query)
             (and (natp o) (< o (fn2-overlays-rows ov)) (natp eb) (natp qbase)
                  (<= (+ eb *fn2-run-entry-rows*) (fn2-fields-rows f))
                  (<= (+ qbase *fn2-run-entry-rows*) (fn2-fields-rows f))
                  (equal (fn2-overlays-count o ov) (len rows))))
    :rule-classes nil)
  (defthm fn2-ovg-reads-order
    (implies (and (fn2-ovg-reads o eb qbase qk qs qg ov ix f pool key rows query)
                  (natp pos) (< pos (len rows)))
             (let ((r (fn2-ov-order o pos eb qbase qk qs qg ov ix f pool)))
               (and (equal (car r) :ok)
                    (equal (mv-nth 1 r) (fn2-run-key-order-spec key (nth pos rows) query))
                    (fn2-ovg-reads o eb qbase qk qs qg ov ix (mv-nth 2 r) pool key rows query))))))

(local
 (defthm fn2-ovg-order-past-last
   (implies (and (fn2-ovg-reads o eb qbase qk qs qg ov ix f pool key rows query)
                 (natp pos) (<= (len rows) pos))
            (equal (fn2-ov-order o pos eb qbase qk qs qg ov ix f pool) (list :ok :end f)))
   :hints (("Goal" :use fn2-ovg-reads-bounds
            :in-theory (e/d (fn2-ov-order) (fn2-ov-entry fn2-run-layout-compare))))))

(local
 (defthmd fn2-ovg-search-finds-cut
   (let* ((search (fn2-ov-search steps lo hi o eb qbase qk qs qg ov ix f pool)) (rf (mv-nth 2 search)))
     (implies (and (natp steps) (natp lo) (natp hi) (<= lo cut) (<= cut hi) (<= hi (len rows))
                   (<= (integer-length (- hi lo)) steps)
                   (fn2-run-sorted-spec key rows)
                   (equal cut (cadr (fn2-run-lower-bound-spec key rows query 0)))
                   (fn2-ovg-reads o eb qbase qk qs qg ov ix f pool key rows query))
              (and (equal (car search) :ok) (equal (mv-nth 1 search) cut)
                   (fn2-ovg-reads o eb qbase qk qs qg ov ix rf pool key rows query))))
   :hints (("Goal" :induct (fn2-ov-search steps lo hi o eb qbase qk qs qg ov ix f pool)
            :do-not '(preprocess)
            :expand ((fn2-ov-search steps lo hi o eb qbase qk qs qg ov ix f pool))
            :in-theory (e/d ((:induction fn2-ov-search) mv-nth)
                            ((:definition fn2-ov-search) fn2-ov-order fn2-run-key-order-spec fn2-run-lower-bound-spec
                             fn2-run-sorted-spec floor integer-length len nth fn2-run-key-order-spec-flips
                             fn2-layoutp-list fn2-layoutp true-listp)))
           (and (equal (access clause-id id :pool-lst) '(1))
                (equal (len (access clause-id id :case-lst)) 1)
                (equal (access clause-id id :primes) 0)
                '(:use ((:instance fn2-ovg-half-bits (less (< (floor (+ lo hi) 2) cut)))
                        (:instance fn2-ovg-reads-order (pos (floor (+ lo hi) 2)))
                        (:instance fn2-ovg-row-before-lower-bound (j (floor (+ lo hi) 2)) (i 0))))))))

; The search finds the lower bound of the query among the stored rows, and
; how the row there compares with the query.
(defthmd fn2-ovg-locate-lower-bound
  (let* ((i (cadr (fn2-run-lower-bound-spec key rows query 0)))
         (locate (fn2-ov-locate o eb qbase qk qs qg ov ix f pool)))
    (implies (and (<= (integer-length (len rows)) *fn2-ov-search-steps*)
                  (fn2-run-sorted-spec key rows)
                  (fn2-ovg-reads o eb qbase qk qs qg ov ix f pool key rows query))
             (and (equal (car locate) :ok) (equal (mv-nth 1 locate) i)
                  (equal (mv-nth 2 locate)
                         (if (< i (len rows)) (fn2-run-key-order-spec key (nth i rows) query) :end))
                  (fn2-ovg-reads o eb qbase qk qs qg ov ix (mv-nth 3 locate) pool key rows query))))
  :hints (("Goal" :do-not '(preprocess)
           :use (fn2-ovg-reads-bounds
                 (:instance fn2-ovg-bound-index-in-range (i 0))
                 (:instance fn2-ovg-search-finds-cut (steps *fn2-ov-search-steps*) (lo 0) (hi (len rows))
                            (cut (cadr (fn2-run-lower-bound-spec key rows query 0))))
                 (:instance fn2-ovg-reads-order (pos (cadr (fn2-run-lower-bound-spec key rows query 0)))
                            (f (mv-nth 2 (fn2-ov-search *fn2-ov-search-steps* 0 (len rows) o eb qbase qk qs qg ov ix f pool))))
                 (:instance fn2-ovg-order-past-last (pos (cadr (fn2-run-lower-bound-spec key rows query 0)))
                            (f (mv-nth 2 (fn2-ov-search *fn2-ov-search-steps* 0 (len rows) o eb qbase qk qs qg ov ix f pool)))))
           :in-theory (e/d (fn2-ov-locate mv-nth)
                           (fn2-ov-search fn2-ov-order fn2-run-key-order-spec fn2-run-lower-bound-spec fn2-ovg-order-past-last
                            fn2-ov-insert-place-is-lower-bound fn2-ovg-reads-order
                            fn2-run-sorted-spec fn2-overlays-count fn2-overlays-rows integer-length len nth)))))

; The lower bound holds an equal key exactly when the query's key is present.
(defthm fn2-ovg-lower-bound-found
  (let* ((lb (fn2-run-lower-bound-spec key rows query i)) (b (- (cadr lb) i)))
    (implies (natp i)
             (equal (equal (car lb) :found)
                    (and (< b (len rows)) (equal (fn2-run-key-order-spec key (nth b rows) query) :eq)))))
  :hints (("Goal" :induct (fn2-run-lower-bound-spec key rows query i)
           :in-theory (e/d (nth) (fn2-run-key-order-spec fn2-run-key-order-spec-flips fn2-ov-insert-place-is-lower-bound)))
          (and stable-under-simplificationp
               '(:use ((:instance fn2-ovg-bound-index-in-range (i (+ 1 i)) (rows (cdr rows))))))))

(local
 (defthm fn2-ovg-before-sorted-absent
   (implies (and (fn2-run-sorted-spec key rows) (consp rows)
                 (equal (fn2-run-key-order-spec key query (car rows)) :lt))
            (fn2-ov-key-absent-spec key query rows))
   :hints (("Goal" :induct (fn2-ov-key-absent-spec key query rows)
            :in-theory (disable fn2-run-key-order-spec fn2-run-key-order-spec-flips))
           (and stable-under-simplificationp
                '(:use ((:instance fn2-run-key-order-spec-transitive (a query) (b (car rows)) (c (cadr rows)))))))))

(defthm fn2-ovg-lower-bound-found-is-present
  (implies (fn2-run-sorted-spec key rows)
           (equal (equal (car (fn2-run-lower-bound-spec key rows query i)) :found)
                  (not (fn2-ov-key-absent-spec key query rows))))
  :hints (("Goal" :induct (fn2-run-lower-bound-spec key rows query i)
           :in-theory (disable fn2-run-key-order-spec fn2-ov-insert-place-is-lower-bound))
          (and stable-under-simplificationp
               '(:use ((:instance fn2-run-key-order-spec-exchange (a (car rows)) (b query))
                       (:instance fn2-run-key-order-spec-cases (a (car rows)) (b query)))))))

; So the search tells a duplicate key from a new one.
(defthm fn2-ovg-locate-detects-duplicate
  (let ((locate (fn2-ov-locate o eb qbase qk qs qg ov ix f pool)))
    (implies (and (<= (integer-length (len rows)) *fn2-ov-search-steps*)
                  (fn2-run-sorted-spec key rows)
                  (fn2-ovg-reads o eb qbase qk qs qg ov ix f pool key rows query))
             (equal (equal (mv-nth 2 locate) :eq) (not (fn2-ov-key-absent-spec key query rows)))))
  :hints (("Goal" :do-not-induct t
           :use (fn2-ovg-locate-lower-bound (:instance fn2-ovg-lower-bound-found (i 0)))
           :in-theory (disable fn2-ovg-lower-bound-found fn2-ov-locate fn2-ov-insert-place-is-lower-bound
                               fn2-run-key-order-spec fn2-run-lower-bound-spec))))

; Inserting one entry into a sorted list, by the schema's merge rule: at
; its lower bound when its key is new; in place of the equal-keyed entry
; under :latest; refused :duplicate otherwise.
(defun fn2-ov-list-put (i repl v xs)
  (declare (xargs :verify-guards nil))
  (if repl (update-nth i v xs) (append (take i xs) (cons v (nthcdr i xs)))))

(defun fn2-ov-insert-spec (key merge e sorted)
  (declare (xargs :verify-guards nil))
  (let* ((lb (fn2-run-lower-bound-spec key sorted e 0)) (i (cadr lb)) (found (eq (car lb) :found)))
    (cond ((and found (not (eq merge :latest))) (list :duplicate sorted))
          (t (list :ok (fn2-ov-list-put i found e sorted))))))

; For a new key this is the sorted insertion.
(defthm fn2-ov-insert-spec-new-key
  (implies (and (true-listp sorted) (fn2-run-sorted-spec key sorted) (fn2-ov-key-absent-spec key e sorted))
           (equal (fn2-ov-insert-spec key merge e sorted) (list :ok (fn2-ov-sort-insert-spec key e sorted))))
  :hints (("Goal" :in-theory (e/d (fn2-ov-sort-insert-at-place) (fn2-run-lower-bound-spec fn2-ov-sort-insert-spec)))))

; Writing an entry: encoded at the arena's fill, its offset put at POS.
(defthm fn2-ovg-write-puts-offset
  (let* ((at (fn2-overlays-fill o ov)) (sid (fn2-overlays-schema o ov))
         (enc (fn2-run-layout-encode sid 0 ebase (fn2-overlays-slot o ov) (fn2-overlays-gen o ov) at
                                     (fn2-overlays-okind o ov) (fn2-overlays-oslot o ov) (fn2-overlays-ogen o ov) f pool))
         (res (fn2-ov-write o pos ebase repl ov ix f pool)))
    (implies (and (fn2-overlaysp ov) (fn2-ov-okp o ov ix) (natp ebase)
                  (<= (+ ebase *fn2-run-entry-rows*) (fn2-fields-rows f))
                  (<= (+ at (fn2-run-layout-size sid 0 ebase f)) (fn2-overlays-cap o ov))
                  (equal (car enc) :ok) (unsigned-byte-p 32 (mv-nth 1 enc))
                  (natp pos)
                  (if repl (< pos (fn2-overlays-count o ov))
                    (and (<= pos (fn2-overlays-count o ov)) (< (fn2-overlays-count o ov) (fn2-overlays-icap o ov)))))
             (and (equal (car res) :ok)
                  (equal (fn2-ov-offsets o (mv-nth 1 res) (mv-nth 2 res))
                         (fn2-ov-list-put pos repl at (fn2-ov-offsets o ov ix)))
                  (equal (mv-nth 3 res) (mv-nth 2 enc)))))
  :hints (("Goal" :do-not-induct t :do-not '(generalize fertilize eliminate-destructors)
           :use ((:instance fn2-ov-place-ok (off (fn2-overlays-fill o ov))
                            (end (mv-nth 1 (fn2-run-layout-encode (fn2-overlays-schema o ov) 0 ebase (fn2-overlays-slot o ov) (fn2-overlays-gen o ov) (fn2-overlays-fill o ov)
                                     (fn2-overlays-okind o ov) (fn2-overlays-oslot o ov) (fn2-overlays-ogen o ov) f pool))))
                 (:instance fn2-ov-reput-ok (off (fn2-overlays-fill o ov))
                            (end (mv-nth 1 (fn2-run-layout-encode (fn2-overlays-schema o ov) 0 ebase (fn2-overlays-slot o ov) (fn2-overlays-gen o ov) (fn2-overlays-fill o ov)
                                     (fn2-overlays-okind o ov) (fn2-overlays-oslot o ov) (fn2-overlays-ogen o ov) f pool)))))
           :in-theory (e/d (fn2-ov-write mv-nth) (fn2-ov-place-ok fn2-ov-reput-ok fn2-ov-place fn2-ov-reput fn2-run-layout-encode
                                                fn2-run-layout-size fn2-ov-offsets
                                                fn2-ov-place-tables fn2-ov-reput-tables fn2-overlays-fill fn2-overlays-schema
                                                fn2-overlays-slot fn2-overlays-gen fn2-overlays-okind fn2-overlays-oslot
                                                fn2-overlays-ogen fn2-overlays-count fn2-overlays-icap fn2-overlays-cap
                                                fn2-overlays-ibase fn2-overlays-rows fn2-fields-rows
                                                fn2-layoutp-list fn2-layoutp fn2-layoutp-cdr true-listp member-equal fn2-run-layout-merge)))))

; The real insert does what fn2-ov-insert-spec says to the overlay's
; offsets: the new entry's offset (the arena's fill) goes to the lower bound
; of its key, in place of an equal key under :latest; a duplicate is refused
; with nothing changed. The schema supplies the comparison (fn2-ovg-reads)
; and an encoding that fits.
(defthm fn2-ovg-insert-refines-spec
  (let* ((qk (fn2-overlays-okind o ov)) (qs (fn2-overlays-oslot o ov)) (qg (fn2-overlays-ogen o ov))
         (sid (fn2-overlays-schema o ov)) (at (fn2-overlays-fill o ov))
         (f2 (mv-nth 3 (fn2-ov-locate o eb ebase qk qs qg ov ix f pool)))
         (enc (fn2-run-layout-encode sid 0 ebase (fn2-overlays-slot o ov) (fn2-overlays-gen o ov) at qk qs qg f2 pool))
         (lb (fn2-run-lower-bound-spec key rows e 0))
         (spec (fn2-ov-insert-spec key (fn2-run-layout-merge sid) e rows))
         (res (fn2-ov-insert o ebase eb ov ix f pool)))
    (implies (and (fn2-overlaysp ov) (fn2-ov-okp o ov ix)
                  (member (fn2-overlays-phase o ov) (list *fn2-overlay-phase-active* *fn2-overlay-phase-private*))
                  (<= (integer-length (len rows)) *fn2-ov-search-steps*)
                  (fn2-run-sorted-spec key rows)
                  (fn2-ovg-reads o eb ebase qk qs qg ov ix f pool key rows e)
                  (implies (equal (car spec) :ok)
                           (and (or (equal (car lb) :found) (< (len rows) (fn2-overlays-icap o ov)))
                                (<= (+ at (fn2-run-layout-size sid 0 ebase f2)) (fn2-overlays-cap o ov))
                                (equal (car enc) :ok) (unsigned-byte-p 32 (mv-nth 1 enc)))))
             (and (equal (car res) (car spec))
                  (equal (fn2-ov-offsets o (mv-nth 1 res) (mv-nth 2 res))
                         (if (equal (car spec) :ok)
                             (fn2-ov-list-put (cadr lb) (equal (car lb) :found) at (fn2-ov-offsets o ov ix))
                           (fn2-ov-offsets o ov ix)))
                  (equal (mv-nth 4 res) (if (equal (car spec) :ok) (mv-nth 2 enc) pool)))))
  :hints (("Goal" :do-not-induct t :do-not '(generalize fertilize eliminate-destructors)
           :use ((:instance fn2-ovg-locate-lower-bound (query e) (qbase ebase)
                            (qk (fn2-overlays-okind o ov)) (qs (fn2-overlays-oslot o ov)) (qg (fn2-overlays-ogen o ov)))
                 (:instance fn2-ovg-lower-bound-found (query e) (i 0))
                 (:instance fn2-ovg-bound-index-in-range (query e) (i 0))
                 (:instance fn2-ovg-reads-bounds (qbase ebase) (query e)
                            (qk (fn2-overlays-okind o ov)) (qs (fn2-overlays-oslot o ov)) (qg (fn2-overlays-ogen o ov))
                            (f (mv-nth 3 (fn2-ov-locate o eb ebase (fn2-overlays-okind o ov) (fn2-overlays-oslot o ov)
                                                        (fn2-overlays-ogen o ov) ov ix f pool))))
                 (:instance fn2-ovg-write-puts-offset
                            (pos (cadr (fn2-run-lower-bound-spec key rows e 0)))
                            (repl (equal (car (fn2-run-lower-bound-spec key rows e 0)) :found))
                            (f (mv-nth 3 (fn2-ov-locate o eb ebase (fn2-overlays-okind o ov) (fn2-overlays-oslot o ov)
                                                        (fn2-overlays-ogen o ov) ov ix f pool)))))
           :in-theory (e/d (fn2-ov-insert mv-nth)
                           (fn2-ov-locate fn2-ov-write fn2-ovg-write-puts-offset fn2-ovg-lower-bound-found fn2-ov-insert-spec-new-key fn2-layoutp-list fn2-layoutp true-listp member-equal
                            fn2-ov-insert-place-is-lower-bound fn2-ovg-lower-bound-found-is-present
                            fn2-run-lower-bound-spec fn2-run-key-order-spec fn2-run-sorted-spec fn2-ov-okp fn2-ov-offsets
                            fn2-run-layout-encode fn2-run-layout-size fn2-ov-list-put
                            fn2-overlays-fill fn2-overlays-schema fn2-overlays-slot fn2-overlays-gen fn2-overlays-okind
                            fn2-overlays-oslot fn2-overlays-ogen fn2-overlays-count fn2-overlays-icap fn2-overlays-cap
                            fn2-overlays-ibase fn2-overlays-rows fn2-overlays-phase fn2-fields-rows integer-length len nth
                            fn2-layoutp-cdr fn2-run-layout-merge (:type-prescription fn2-run-lower-bound-spec) (:type-prescription fn2-run-key-order-spec))))))
