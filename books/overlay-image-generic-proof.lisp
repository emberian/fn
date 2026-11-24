; The overlay adapter's image is the sorted specification, for any schema
; that meets these obligations over its own predicate STORED (overlay 0
; holds ROWS, readable, with the entry fixture free from OFF): the
; adapter's start stores no rows; a stored overlay is active, of the
; schema, counts its rows, and they are sorted; loading an entry into the
; fixture makes the comparison agree with the key order (fn2-ovg-reads);
; encoding a new entry fits, and placing its offset at its lower bound
; stores the sorted insertion; reading the stored rows back returns them.
; A schema takes fn2-ovg-overlay-sorted by functional instantiation, with
; fn2-ovg-schema-ok true and its own STORED, proving each obligation.
(in-package "ACL2")
(include-book "overlay-search-generic-proof")

(encapsulate
  (((fn2-ovg-sid) => *) ((fn2-ovg-layout) => *) ((fn2-ovg-key) => *) ((fn2-ovg-schema-ok) => *)
   ((fn2-ovg-stored * * * * * * * *) => *))
  (local (defun fn2-ovg-sid () 0))
  (local (defun fn2-ovg-layout () nil))
  (local (defun fn2-ovg-key () nil))
  (local (defun fn2-ovg-schema-ok () nil))
  (local (defun fn2-ovg-stored (src sgen off ov ix f pool rows)
           (declare (ignore src sgen off ov ix f pool rows)) nil))

  (defthm fn2-ovg-start-stores-nothing
    (implies (fn2-ovg-schema-ok)
             (b* ((ov (fn2-overlays-init 1 ov)) (ix (fn2-overlay-index-init 256 ix))
                  (f (fn2-fields-init 512 f)) (pool (fn2-pool-init '((2 . 65536)) 1 100 pool))
                  ((mv & aslot agen pool) (fn2-pool-reserve 0 9 0 1 pool))
                  ((mv & src sgen pool) (fn2-pool-reserve 0 9 0 1 pool))
                  ((mv code ov pool) (fn2-ov-start 0 (fn2-ovg-sid) aslot agen 0 256 9 0 1 0 ov ix pool)))
               (and (equal code :ok) (fn2-ovg-stored src sgen 0 ov ix f pool nil))))
    :rule-classes nil)

  (defthm fn2-ovg-stored-shape
    (implies (and (fn2-ovg-schema-ok) (fn2-ovg-stored src sgen off ov ix f pool rows))
             (and (fn2-overlaysp ov) (fn2-overlay-indexp ix) (fn2-ov-okp 0 ov ix)
                  (equal (fn2-overlays-phase 0 ov) *fn2-overlay-phase-active*)
                  (equal (fn2-overlays-schema 0 ov) (fn2-ovg-sid))
                  (equal (fn2-overlays-count 0 ov) (len rows)) (<= 64 (fn2-overlays-icap 0 ov))
                  (true-listp rows) (fn2-run-sorted-spec (fn2-ovg-key) rows)))
    :rule-classes nil)

  (defthm fn2-ovg-load-reads
    (implies (and (fn2-ovg-schema-ok) (fn2-ovg-stored src sgen off ov ix f pool rows)
                  (fn2-run-values-layoutp (fn2-ovg-layout) e) (< (len rows) 64))
             (let ((ld (fn2-run-load-values (fn2-ovg-layout) e *fn2-run-adapter-entry* src sgen off 9 0 1 f pool)))
               (and (equal (car ld) :ok)
                    (fn2-ovg-reads 0 *fn2-run-adapter-reader* *fn2-run-adapter-entry*
                                   (fn2-overlays-okind 0 ov) (fn2-overlays-oslot 0 ov) (fn2-overlays-ogen 0 ov)
                                   ov ix (mv-nth 2 ld) (mv-nth 3 ld) (fn2-ovg-key) rows e))))
    :rule-classes nil)

  (defthm fn2-ovg-write-stores-insertion
    (implies (and (fn2-ovg-schema-ok) (fn2-ovg-stored src sgen off ov ix f pool rows)
                  (fn2-run-values-layoutp (fn2-ovg-layout) e) (< (len rows) 64)
                  (fn2-ov-key-absent-spec (fn2-ovg-key) e rows))
             (let* ((ld (fn2-run-load-values (fn2-ovg-layout) e *fn2-run-adapter-entry* src sgen off 9 0 1 f pool))
                    (qk (fn2-overlays-okind 0 ov)) (qs (fn2-overlays-oslot 0 ov)) (qg (fn2-overlays-ogen 0 ov))
                    (f2 (mv-nth 3 (fn2-ov-locate 0 *fn2-run-adapter-reader* *fn2-run-adapter-entry* qk qs qg
                                                 ov ix (mv-nth 2 ld) (mv-nth 3 ld))))
                    (at (fn2-overlays-fill 0 ov))
                    (enc (fn2-run-layout-encode (fn2-ovg-sid) 0 *fn2-run-adapter-entry* (fn2-overlays-slot 0 ov)
                                                (fn2-overlays-gen 0 ov) at qk qs qg f2 (mv-nth 3 ld)))
                    (i (cadr (fn2-run-lower-bound-spec (fn2-ovg-key) rows e 0))))
               (and (<= (+ at (fn2-run-layout-size (fn2-ovg-sid) 0 *fn2-run-adapter-entry* f2)) (fn2-overlays-cap 0 ov))
                    (equal (car enc) :ok) (unsigned-byte-p 32 (mv-nth 1 enc))
                    (implies (and (fn2-overlay-indexp ix2) (fn2-overlay-index-wfp ix2)
                                  (equal (fn2-overlay-index-rows ix2) (fn2-overlay-index-rows ix))
                                  (equal (fn2-ov-offsets 0 ov2 ix2)
                                         (fn2-ov-list-put i nil at (fn2-ov-offsets 0 ov ix)))
                                  (equal ov2 (fn2-overlays-set-fill 0 (mv-nth 1 enc)
                                                                    (fn2-overlays-set-count 0 (+ 1 (len rows)) ov))))
                             (fn2-ovg-stored src sgen (mv-nth 1 ld) ov2 ix2 f2 (mv-nth 2 enc)
                                             (fn2-ov-sort-insert-spec (fn2-ovg-key) e rows))))))
    :rule-classes nil)

  (defthm fn2-ovg-read-returns-rows
    (implies (and (fn2-ovg-schema-ok) (fn2-ovg-stored src sgen off ov ix f pool rows))
             (equal (car (fn2-ov-adapter-read (len rows) 0 (fn2-ovg-layout) ov ix f pool)) rows))
    :rule-classes nil))

; An adapter's 64 entries fit the search's step budget.
(defthm fn2-ovg-small-fits-search
  (implies (and (natp n) (< n 64)) (<= (integer-length n) *fn2-ov-search-steps*))
  :hints (("Goal" :use ((:instance fn2-ovg-integer-length-monotonic (i n) (j 63))))))

; A new key's insert: what it leaves in each table.
(defthm fn2-ovg-insert-new-tables
  (let* ((qk (fn2-overlays-okind o ov)) (qs (fn2-overlays-oslot o ov)) (qg (fn2-overlays-ogen o ov))
         (sid (fn2-overlays-schema o ov)) (at (fn2-overlays-fill o ov))
         (f2 (mv-nth 3 (fn2-ov-locate o eb ebase qk qs qg ov ix f pool)))
         (enc (fn2-run-layout-encode sid 0 ebase (fn2-overlays-slot o ov) (fn2-overlays-gen o ov) at qk qs qg f2 pool))
         (res (fn2-ov-insert o ebase eb ov ix f pool)))
    (implies (and (fn2-overlaysp ov) (fn2-overlay-indexp ix) (fn2-ov-okp o ov ix)
                  (member (fn2-overlays-phase o ov) (list *fn2-overlay-phase-active* *fn2-overlay-phase-private*))
                  (<= (integer-length (len rows)) *fn2-ov-search-steps*)
                  (fn2-run-sorted-spec key rows) (fn2-ov-key-absent-spec key e rows)
                  (fn2-ovg-reads o eb ebase qk qs qg ov ix f pool key rows e)
                  (< (len rows) (fn2-overlays-icap o ov))
                  (<= (+ at (fn2-run-layout-size sid 0 ebase f2)) (fn2-overlays-cap o ov))
                  (equal (car enc) :ok) (unsigned-byte-p 32 (mv-nth 1 enc)))
             (and (equal (mv-nth 1 res)
                         (fn2-overlays-set-fill o (mv-nth 1 enc) (fn2-overlays-set-count o (+ 1 (len rows)) ov)))
                  (fn2-overlay-indexp (mv-nth 2 res)) (fn2-overlay-index-wfp (mv-nth 2 res))
                  (equal (fn2-overlay-index-rows (mv-nth 2 res)) (fn2-overlay-index-rows ix))
                  (equal (mv-nth 3 res) f2))))
  :hints (("Goal" :do-not-induct t :do-not '(generalize fertilize eliminate-destructors)
           :use ((:instance fn2-ovg-locate-lower-bound (query e) (qbase ebase)
                            (qk (fn2-overlays-okind o ov)) (qs (fn2-overlays-oslot o ov)) (qg (fn2-overlays-ogen o ov)))
                 (:instance fn2-ovg-lower-bound-found-is-present (query e) (i 0))
                 (:instance fn2-ovg-lower-bound-found (query e) (i 0))
                 (:instance fn2-ovg-bound-index-in-range (query e) (i 0))
                 (:instance fn2-ovg-reads-bounds (qbase ebase) (query e)
                            (qk (fn2-overlays-okind o ov)) (qs (fn2-overlays-oslot o ov)) (qg (fn2-overlays-ogen o ov))
                            (f (mv-nth 3 (fn2-ov-locate o eb ebase (fn2-overlays-okind o ov) (fn2-overlays-oslot o ov)
                                                        (fn2-overlays-ogen o ov) ov ix f pool)))))
           :in-theory (e/d (fn2-ov-insert fn2-ov-write fn2-ov-place mv-nth)
                           (fn2-ov-locate fn2-ovg-lower-bound-found fn2-ov-insert-spec-new-key
                            fn2-layoutp-list fn2-layoutp true-listp member-equal
                            fn2-ov-insert-place-is-lower-bound fn2-ovg-lower-bound-found-is-present
                            fn2-run-lower-bound-spec fn2-run-key-order-spec fn2-run-sorted-spec fn2-ov-offsets
                            fn2-run-layout-encode fn2-run-layout-size fn2-ov-list-put fn2-ov-key-absent-spec
                            fn2-overlays-fill fn2-overlays-schema fn2-overlays-slot fn2-overlays-gen fn2-overlays-okind
                            fn2-overlays-oslot fn2-overlays-ogen fn2-overlays-count fn2-overlays-icap fn2-overlays-cap
                            fn2-overlays-ibase fn2-overlays-rows fn2-overlays-phase fn2-fields-rows integer-length len nth
                            fn2-layoutp-cdr fn2-run-layout-merge (:type-prescription fn2-run-lower-bound-spec)
                            (:type-prescription fn2-run-key-order-spec))))))

(defun-sk fn2-ovg-stored-some (src sgen ov ix f pool rows)
  (exists off (fn2-ovg-stored src sgen off ov ix f pool rows)))

; Every entry's key is absent from ROWS.
(defun fn2-ovg-all-absent (key entries rows)
  (declare (xargs :verify-guards nil))
  (or (atom entries)
      (and (fn2-ov-key-absent-spec key (car entries) rows) (fn2-ovg-all-absent key (cdr entries) rows))))

(local
 (defthm fn2-ovg-all-absent-after-insert
   (implies (and (fn2-ovg-all-absent key rest rows) (fn2-ov-key-absent-spec key e rest))
            (fn2-ovg-all-absent key rest (fn2-ov-sort-insert-spec key e rows)))
   :hints (("Goal" :induct (fn2-ovg-all-absent key rest rows)
            :in-theory (disable fn2-ov-sort-insert-spec fn2-run-key-order-spec fn2-run-key-order-spec-flips))
           (and stable-under-simplificationp
                '(:use ((:instance fn2-run-key-order-spec-exchange (a e) (b (car rest)))
                        (:instance fn2-run-key-order-spec-cases (a e) (b (car rest)))))))))

(local
 (defthm fn2-ovg-make-list-ac-cons
   (equal (make-list-ac n v (cons v acc)) (cons v (make-list-ac n v acc)))))

(local
 (defthm fn2-ovg-make-list-cons
   (equal (make-list (len (cons a x)) :initial-element v) (cons v (make-list (len x) :initial-element v)))
   :hints (("Goal" :in-theory (enable make-list-ac)))))

(local
 (defthm fn2-ovg-len-sort-insert-bound
   (implies (<= (+ (len rows) (len (cons e entries))) 64)
            (<= (+ (len (fn2-ov-sort-insert-spec key e rows)) (len entries)) 64))))

(local
 (defthm fn2-ovg-make-list-succ
   (implies (natp n) (equal (make-list-ac (+ 1 n) v nil) (cons v (make-list-ac n v nil))))))

; One adapter step, as one opaque value: (code off ov ix f pool).
(defun-nx fn2-ovg-step (e src sgen off ov ix f pool)
  (b* (((mv code off f pool)
        (fn2-run-load-values (fn2-ovg-layout) e *fn2-run-adapter-entry* src sgen off 9 0 1 f pool))
       ((mv code ov ix f pool)
        (if (eq code :ok) (fn2-ov-insert 0 *fn2-run-adapter-entry* *fn2-run-adapter-reader* ov ix f pool)
          (mv (list :load code) ov ix f pool))))
    (list code off ov ix f pool)))

(local
 (defthm fn2-ovg-adapter-load-by-step
   (implies (consp entries)
            (equal (fn2-ov-adapter-load sid (fn2-ovg-layout) entries src sgen off ov ix f pool)
                   (let* ((s (fn2-ovg-step (car entries) src sgen off ov ix f pool))
                          (r (fn2-ov-adapter-load sid (fn2-ovg-layout) (cdr entries) src sgen
                                                  (nth 1 s) (nth 2 s) (nth 3 s) (nth 4 s) (nth 5 s))))
                     (list (cons (nth 0 s) (mv-nth 0 r)) (mv-nth 1 r) (mv-nth 2 r) (mv-nth 3 r) (mv-nth 4 r)))))
   :hints (("Goal" :expand ((fn2-ov-adapter-load sid (fn2-ovg-layout) entries src sgen off ov ix f pool))
            :in-theory (e/d (fn2-ovg-step mv-nth) (fn2-ov-insert fn2-run-load-values))))))

; One adapter step: a new entry loads, inserts :ok, and the overlay then
; stores the sorted insertion.
(defthm fn2-ovg-step-stores
  (let ((s (fn2-ovg-step e src sgen off ov ix f pool)))
    (implies (and (fn2-ovg-schema-ok) (fn2-ovg-stored src sgen off ov ix f pool rows)
                  (fn2-run-values-layoutp (fn2-ovg-layout) e) (< (len rows) 64)
                  (fn2-ov-key-absent-spec (fn2-ovg-key) e rows))
             (and (equal (nth 0 s) :ok)
                  (fn2-ovg-stored src sgen (nth 1 s) (nth 2 s) (nth 3 s) (nth 4 s) (nth 5 s)
                                  (fn2-ov-sort-insert-spec (fn2-ovg-key) e rows)))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :use (fn2-ovg-stored-shape fn2-ovg-load-reads
                 (:instance fn2-ovg-write-stores-insertion
                            (ov2 (mv-nth 1 (fn2-ov-insert 0 *fn2-run-adapter-entry* *fn2-run-adapter-reader* ov ix
                                   (mv-nth 2 (fn2-run-load-values (fn2-ovg-layout) e *fn2-run-adapter-entry* src sgen off 9 0 1 f pool))
                                   (mv-nth 3 (fn2-run-load-values (fn2-ovg-layout) e *fn2-run-adapter-entry* src sgen off 9 0 1 f pool)))))
                            (ix2 (mv-nth 2 (fn2-ov-insert 0 *fn2-run-adapter-entry* *fn2-run-adapter-reader* ov ix
                                   (mv-nth 2 (fn2-run-load-values (fn2-ovg-layout) e *fn2-run-adapter-entry* src sgen off 9 0 1 f pool))
                                   (mv-nth 3 (fn2-run-load-values (fn2-ovg-layout) e *fn2-run-adapter-entry* src sgen off 9 0 1 f pool))))))
                 (:instance fn2-ovg-insert-refines-spec (o 0) (ebase *fn2-run-adapter-entry*) (eb *fn2-run-adapter-reader*)
                            (key (fn2-ovg-key))
                            (f (mv-nth 2 (fn2-run-load-values (fn2-ovg-layout) e *fn2-run-adapter-entry* src sgen off 9 0 1 f pool)))
                            (pool (mv-nth 3 (fn2-run-load-values (fn2-ovg-layout) e *fn2-run-adapter-entry* src sgen off 9 0 1 f pool))))
                 (:instance fn2-ovg-insert-new-tables (o 0) (ebase *fn2-run-adapter-entry*) (eb *fn2-run-adapter-reader*)
                            (key (fn2-ovg-key))
                            (f (mv-nth 2 (fn2-run-load-values (fn2-ovg-layout) e *fn2-run-adapter-entry* src sgen off 9 0 1 f pool)))
                            (pool (mv-nth 3 (fn2-run-load-values (fn2-ovg-layout) e *fn2-run-adapter-entry* src sgen off 9 0 1 f pool))))
                 (:instance fn2-ovg-lower-bound-found-is-present (key (fn2-ovg-key)) (query e) (i 0)))
           :in-theory (e/d (fn2-ovg-step fn2-ov-insert-spec fn2-ov-list-put mv-nth)
                           (fn2-ov-insert fn2-ov-locate fn2-run-load-values fn2-run-layout-encode fn2-run-layout-size
                            fn2-ovg-insert-refines-spec fn2-ovg-insert-new-tables fn2-ovg-lower-bound-found-is-present
                            fn2-ov-insert-spec-new-key fn2-ov-insert-place-is-lower-bound
                            fn2-run-lower-bound-spec fn2-run-key-order-spec fn2-run-sorted-spec fn2-ov-offsets
                            fn2-ov-key-absent-spec fn2-ov-okp fn2-layoutp-list fn2-layoutp true-listp member-equal
                            fn2-overlays-fill fn2-overlays-schema fn2-overlays-slot fn2-overlays-gen fn2-overlays-okind
                            fn2-overlays-oslot fn2-overlays-ogen fn2-overlays-count fn2-overlays-icap fn2-overlays-cap
                            fn2-overlays-phase fn2-run-layout-merge fn2-run-values-layoutp fn2-ov-sort-insert-spec
                            integer-length len)))))

(local (in-theory (disable fn2-ovg-step)))

(local
 (defun-nx fn2-ovg-load-walk (entries src sgen off ov ix f pool rows)
   (if (atom entries) (list src sgen off ov ix f pool rows)
     (let ((s (fn2-ovg-step (car entries) src sgen off ov ix f pool)))
       (fn2-ovg-load-walk (cdr entries) src sgen (nth 1 s) (nth 2 s) (nth 3 s) (nth 4 s) (nth 5 s)
                          (fn2-ov-sort-insert-spec (fn2-ovg-key) (car entries) rows))))))

(defthm fn2-ovg-adapter-load-base
  (implies (and (atom entries) (fn2-ovg-stored src sgen off ov ix f pool rows))
           (let ((r (fn2-ov-adapter-load sid layout entries src sgen off ov ix f pool)))
             (and (equal (car r) nil)
                  (fn2-ovg-stored-some src sgen (mv-nth 1 r) (mv-nth 2 r) (mv-nth 3 r) (mv-nth 4 r) rows))))
  :rule-classes nil
  :hints (("Goal" :expand ((fn2-ov-adapter-load sid layout entries src sgen off ov ix f pool))
           :use fn2-ovg-stored-some-suff
           :in-theory (e/d (mv-nth) (fn2-ovg-stored-some)))))

(defthm fn2-ovg-adapter-load-stores
  (implies (and (fn2-ovg-schema-ok) (fn2-ovg-stored src sgen off ov ix f pool rows)
                (fn2-run-entries-layoutp (fn2-ovg-layout) entries)
                (fn2-ov-distinct-spec (fn2-ovg-key) entries)
                (fn2-ovg-all-absent (fn2-ovg-key) entries rows)
                (<= (+ (len rows) (len entries)) 64))
           (let ((r (fn2-ov-adapter-load sid (fn2-ovg-layout) entries src sgen off ov ix f pool)))
             (and (equal (car r) (make-list (len entries) :initial-element :ok))
                  (fn2-ovg-stored-some src sgen (mv-nth 1 r) (mv-nth 2 r) (mv-nth 3 r) (mv-nth 4 r)
                                       (fn2-ov-insert-all-spec (fn2-ovg-key) entries rows)))))
  :rule-classes nil
  :hints (("Goal" :induct (fn2-ovg-load-walk entries src sgen off ov ix f pool rows)
           :do-not '(generalize fertilize eliminate-destructors)
           :in-theory (e/d (mv-nth) (fn2-ov-sort-insert-spec make-list-ac fn2-ovg-stored-some fn2-ov-adapter-load
                                     fn2-ovg-adapter-load-by-step
                                     fn2-ov-key-absent-spec fn2-run-values-layoutp)))
          ("Subgoal *1/2" :in-theory (e/d (mv-nth fn2-ovg-adapter-load-by-step) (fn2-ov-sort-insert-spec make-list-ac fn2-ovg-stored-some fn2-ov-adapter-load
                                     fn2-ov-key-absent-spec fn2-run-values-layoutp))
           :use ((:instance fn2-ovg-adapter-load-base (layout (fn2-ovg-layout))) (:instance fn2-ovg-step-stores (e (car entries)))))
          ("Subgoal *1/1" :in-theory (e/d (mv-nth fn2-ovg-adapter-load-by-step) (fn2-ov-sort-insert-spec make-list-ac fn2-ovg-stored-some fn2-ov-adapter-load
                                     fn2-ov-key-absent-spec fn2-run-values-layoutp))
           :use ((:instance fn2-ovg-adapter-load-base (layout (fn2-ovg-layout))) (:instance fn2-ovg-step-stores (e (car entries)))))))

(local
 (defthm fn2-ovg-all-absent-from-nothing
   (fn2-ovg-all-absent key entries nil)))

(local
 (defthm fn2-ovg-load-then-read
   (implies (and (fn2-ovg-schema-ok) (fn2-ovg-stored src sgen off ov ix f pool nil)
                 (fn2-ov-inputp (fn2-ovg-layout) (fn2-ovg-key) entries))
            (let* ((ld (fn2-ov-adapter-load sid (fn2-ovg-layout) entries src sgen off ov ix f pool))
                   (back (fn2-ov-adapter-read (fn2-overlays-count 0 (mv-nth 1 ld)) 0 (fn2-ovg-layout)
                                              (mv-nth 1 ld) (mv-nth 2 ld) (mv-nth 3 ld) (mv-nth 4 ld))))
              (equal (list (car ld) (car back)) (fn2-ov-image-spec (fn2-ovg-key) entries))))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn2-ovg-adapter-load-stores (rows nil))
                  (:instance fn2-ovg-stored-shape
                             (off (fn2-ovg-stored-some-witness src sgen
                                   (mv-nth 1 (fn2-ov-adapter-load sid (fn2-ovg-layout) entries src sgen off ov ix f pool))
                                   (mv-nth 2 (fn2-ov-adapter-load sid (fn2-ovg-layout) entries src sgen off ov ix f pool))
                                   (mv-nth 3 (fn2-ov-adapter-load sid (fn2-ovg-layout) entries src sgen off ov ix f pool))
                                   (mv-nth 4 (fn2-ov-adapter-load sid (fn2-ovg-layout) entries src sgen off ov ix f pool))
                                   (fn2-ov-sort-spec (fn2-ovg-key) entries)))
                             (ov (mv-nth 1 (fn2-ov-adapter-load sid (fn2-ovg-layout) entries src sgen off ov ix f pool)))
                             (ix (mv-nth 2 (fn2-ov-adapter-load sid (fn2-ovg-layout) entries src sgen off ov ix f pool)))
                             (f (mv-nth 3 (fn2-ov-adapter-load sid (fn2-ovg-layout) entries src sgen off ov ix f pool)))
                             (pool (mv-nth 4 (fn2-ov-adapter-load sid (fn2-ovg-layout) entries src sgen off ov ix f pool)))
                             (rows (fn2-ov-sort-spec (fn2-ovg-key) entries)))
                  (:instance fn2-ovg-read-returns-rows
                             (off (fn2-ovg-stored-some-witness src sgen
                                   (mv-nth 1 (fn2-ov-adapter-load sid (fn2-ovg-layout) entries src sgen off ov ix f pool))
                                   (mv-nth 2 (fn2-ov-adapter-load sid (fn2-ovg-layout) entries src sgen off ov ix f pool))
                                   (mv-nth 3 (fn2-ov-adapter-load sid (fn2-ovg-layout) entries src sgen off ov ix f pool))
                                   (mv-nth 4 (fn2-ov-adapter-load sid (fn2-ovg-layout) entries src sgen off ov ix f pool))
                                   (fn2-ov-sort-spec (fn2-ovg-key) entries)))
                             (ov (mv-nth 1 (fn2-ov-adapter-load sid (fn2-ovg-layout) entries src sgen off ov ix f pool)))
                             (ix (mv-nth 2 (fn2-ov-adapter-load sid (fn2-ovg-layout) entries src sgen off ov ix f pool)))
                             (f (mv-nth 3 (fn2-ov-adapter-load sid (fn2-ovg-layout) entries src sgen off ov ix f pool)))
                             (pool (mv-nth 4 (fn2-ov-adapter-load sid (fn2-ovg-layout) entries src sgen off ov ix f pool)))
                             (rows (fn2-ov-sort-spec (fn2-ovg-key) entries))))
            :in-theory (e/d (fn2-ov-inputp fn2-ov-image-spec fn2-ovg-stored-some)
                            (fn2-ov-adapter-load fn2-ov-adapter-read fn2-ov-sort-spec fn2-ov-distinct-spec
                             fn2-run-entries-layoutp fn2-layoutp make-list-ac))))))

(local
 (defthm fn2-ovg-adapter-run-sorted
   (implies (and (fn2-ovg-schema-ok) (fn2-ov-inputp (fn2-ovg-layout) (fn2-ovg-key) entries))
            (equal (car (fn2-ov-adapter-run (fn2-ovg-sid) (fn2-ovg-layout) entries ov ix f pool))
                   (fn2-ov-image-spec (fn2-ovg-key) entries)))
   :hints (("Goal" :do-not-induct t
            :use (fn2-ovg-start-stores-nothing
                  (:instance fn2-ovg-load-then-read (sid (fn2-ovg-sid)) (src (mv-nth 1 (fn2-pool-reserve 0 9 0 1 (mv-nth 3 (fn2-pool-reserve 0 9 0 1 (fn2-pool-init '((2 . 65536)) 1 100 pool)))))) (sgen (mv-nth 2 (fn2-pool-reserve 0 9 0 1 (mv-nth 3 (fn2-pool-reserve 0 9 0 1 (fn2-pool-init '((2 . 65536)) 1 100 pool)))))) (off 0)
                             (ov (mv-nth 1 (fn2-ov-start 0 (fn2-ovg-sid) (mv-nth 1 (fn2-pool-reserve 0 9 0 1 (fn2-pool-init '((2 . 65536)) 1 100 pool))) (mv-nth 2 (fn2-pool-reserve 0 9 0 1 (fn2-pool-init '((2 . 65536)) 1 100 pool))) 0 256 9 0 1 0 (fn2-overlays-init 1 ov) (fn2-overlay-index-init 256 ix) (mv-nth 3 (fn2-pool-reserve 0 9 0 1 (mv-nth 3 (fn2-pool-reserve 0 9 0 1 (fn2-pool-init '((2 . 65536)) 1 100 pool)))))))) (ix (fn2-overlay-index-init 256 ix)) (f (fn2-fields-init 512 f))
                             (pool (mv-nth 2 (fn2-ov-start 0 (fn2-ovg-sid) (mv-nth 1 (fn2-pool-reserve 0 9 0 1 (fn2-pool-init '((2 . 65536)) 1 100 pool))) (mv-nth 2 (fn2-pool-reserve 0 9 0 1 (fn2-pool-init '((2 . 65536)) 1 100 pool))) 0 256 9 0 1 0 (fn2-overlays-init 1 ov) (fn2-overlay-index-init 256 ix) (mv-nth 3 (fn2-pool-reserve 0 9 0 1 (mv-nth 3 (fn2-pool-reserve 0 9 0 1 (fn2-pool-init '((2 . 65536)) 1 100 pool))))))))))
            :in-theory (e/d (fn2-ov-adapter-run mv-nth)
                            (fn2-ov-adapter-load fn2-ov-adapter-read fn2-ov-start fn2-ov-image-spec fn2-ov-inputp
                             fn2-pool-reserve fn2-pool-init fn2-fields-init fn2-overlays-init fn2-overlay-index-init
                             fn2-ov-start-tables fn2-ov-start-empty fn2-ov-start-keeps-others fn2-ovg-load-then-read))))))

; The keystone's statement, for any schema meeting the obligations.
(defthm fn2-ovg-overlay-sorted
  (implies (and (fn2-ovg-schema-ok) (fn2-ov-inputp (fn2-ovg-layout) (fn2-ovg-key) entries))
           (equal (fn2-ov-image (fn2-ovg-sid) (fn2-ovg-layout) entries)
                  (fn2-ov-image-spec (fn2-ovg-key) entries)))
  :hints (("Goal" :in-theory (e/d (fn2-ov-image mv-nth)
                                  (fn2-ov-adapter-run fn2-ov-image-spec fn2-ov-inputp create-fn2-overlays
                                   create-fn2-overlay-index create-fn2-fields create-fn2-pool)))))
