; Logical contents of a growing page, including every physical restart word.
(in-package "ACL2")
(include-book "runs-overview-builder-proof")
(include-book "runs-restart-lookup-proof")

(local (defthm fn2-run-spliced-length (equal (len (append a b)) (+ (len a) (len b)))))
(local (defthm fn2-run-spliced-lists (equal (append (append a b) c) (append a (append b c)))))

(defthm fn2-run-spliced-entry-bytes
  (equal (fn2-run-entries-octets layout (append rows tail))
         (append (fn2-run-entries-octets layout rows) (fn2-run-entries-octets layout tail)))
  :hints (("Goal" :induct (len rows) :in-theory (disable fn2-layout-octets))))

(defthmd fn2-run-spliced-restart-offsets
  (implies (and (natp i) (natp off))
           (equal (fn2-run-restart-offsets-spec layout (append rows tail) i off)
                  (append (fn2-run-restart-offsets-spec layout rows i off)
                          (fn2-run-restart-offsets-spec layout tail (+ i (len rows))
                                 (+ off (len (fn2-run-entries-octets layout rows)))))))
  :hints (("Goal" :induct (fn2-run-restart-offsets-spec layout rows i off)
           :expand ((:free (xs) (fn2-run-restart-offsets-spec layout (cons (car rows) xs) i off)))
           :in-theory (disable fn2-layout-octets mod))))

(local
 (defthm fn2-run-saving-next-offset
   (implies (and (natp k) (natp base))
            (equal (fn2-run-saved-offsets (1+ k) base (fn2-run-restarts-set-offset (+ base k) v restarts))
                   (append (fn2-run-saved-offsets k base restarts) (list v))))
   :hints (("Goal" :induct (fn2-run-saved-offsets k base restarts)
            :expand ((:free (rs) (fn2-run-saved-offsets (1+ k) base rs))
                     (:free (rs) (fn2-run-saved-offsets 1 base rs)))
            :in-theory (e/d (fn2-run-restarts-set-offset fn2-run-restarts-offset
                             update-fn2-run-restarts-offset$ai nth-update-nth)
                        (nth update-nth))))))

(defthmd fn2-run-note-extends-restart-list
  (let* ((nr (fn2-run-writers-restarts w writers)) (first (* w *fn2-run-restart-capacity*))
         (restartp (equal (mod (fn2-run-writers-entries w writers) *fn2-run-restart-interval*) 0))
         (note (fn2-run-note-restart w writers restarts)))
    (implies (and (natp w) (natp nr) (< nr *fn2-run-restart-capacity*)
                  (< (+ first nr) (fn2-run-restarts-rows restarts)))
             (equal (fn2-run-saved-offsets (if restartp (1+ nr) nr) first (mv-nth 2 note))
                    (append (fn2-run-saved-offsets nr first restarts)
                            (if restartp (list (fn2-run-writers-cursor w writers)) nil)))))
  :hints (("Goal" :cases ((equal (mod (fn2-run-writers-entries w writers) *fn2-run-restart-interval*) 0))
           :in-theory (e/d (fn2-run-note-restart)
                     (fn2-run-saved-offsets fn2-run-restarts-set-offset fn2-run-writers-entries fn2-run-writers-restarts
                      fn2-run-writers-cursor fn2-run-writers-set-restarts fn2-run-restarts-rows mod)))))

(defthmd fn2-run-successful-build-keeps-noted-restarts
  (let* ((build (fn2-run-build-add b base builds writers restarts f pool))
         (w (fn2-run-builds-wbase b builds)))
    (implies (equal (car build) :ok)
             (equal (mv-nth 3 build) (mv-nth 2 (fn2-run-note-restart w writers restarts)))))
  :hints (("Goal" :do-not '(preprocess)
           :in-theory (e/d (fn2-run-build-add fn2-run-add fn2-run-add-write fn2-run-close-full)
                     (fn2-run-add-ready fn2-run-add-check fn2-run-note-restart fn2-run-add-commit fn2-run-close
                      fn2-run-layout-encode fn2-run-layout-decode fn2-run-builds-wbase fn2-run-builds-height
                      fn2-run-builds-schema fn2-run-builds-phase fn2-run-builds-entries fn2-run-builds-set-entries
                      fn2-run-builds-set-height fn2-run-writers-phase fn2-run-writers-level fn2-run-writers-fields
                      fn2-run-writers-slot fn2-run-writers-gen fn2-run-writers-cursor fn2-run-writers-okind
                      fn2-run-writers-oslot fn2-run-writers-ogen fn2-fields-rows unsigned-byte-p)))))

(defun-nx fn2-run-open-overview-contents-p (rows w idx nr off dst dg restarts pool)
  (let ((body (fn2-run-entries-octets *fn2-overview-entry* rows))
        (offsets (fn2-run-restart-offsets-spec *fn2-overview-entry* rows 0 *fn2-run-entries-base*)))
    (and (equal idx (len rows)) (equal nr (len offsets)) (equal off (+ *fn2-run-entries-base* (len body)))
         (equal (fn2-run-read-bytes (len body) dst dg *fn2-run-entries-base* 9 0 1 pool) body)
         (equal (fn2-run-saved-offsets nr (* w *fn2-run-restart-capacity*) restarts) offsets))))

(local
 (defthm fn2-run-one-more-entry
   (let ((body (fn2-run-entries-octets layout rows)) (offsets (fn2-run-restart-offsets-spec layout rows 0 off))
         (bytes (fn2-layout-octets layout row)) (joined (append rows (list row))))
     (implies (natp off)
              (and (equal (fn2-run-entries-octets layout joined) (append body bytes))
                   (equal (fn2-run-restart-offsets-spec layout joined 0 off)
                          (append offsets (if (equal (mod (len rows) *fn2-run-restart-interval*) 0)
                                              (list (+ off (len body))) nil))))))
   :hints (("Goal" :do-not-induct t :use ((:instance fn2-run-spliced-restart-offsets (i 0) (tail (list row)))
                              (:instance fn2-run-spliced-entry-bytes (tail (list row))))
            :expand ((fn2-run-entries-octets layout nil) (:free (i at) (fn2-run-restart-offsets-spec layout nil i at))
                     (fn2-run-entries-octets layout (list row))
                     (:free (i next) (fn2-run-restart-offsets-spec layout (list row) i next)))
            :in-theory (disable fn2-run-spliced-entry-bytes fn2-run-entries-octets fn2-run-restart-offsets-spec fn2-layout-octets binary-append mod)))))

(local
 (defthm fn2-run-join-written-entry
   (let* ((body (fn2-run-entries-octets *fn2-overview-entry* rows))
          (bytes (fn2-layout-octets *fn2-overview-entry* row))
          (first (* w *fn2-run-restart-capacity*)) (restartp (equal (mod idx *fn2-run-restart-interval*) 0))
          (newnr (if restartp (1+ nr) nr)))
     (implies (and (fn2-run-open-overview-contents-p rows w idx nr off dst dg restarts pool)
                   (equal (fn2-run-read-bytes (len body) dst dg *fn2-run-entries-base* 9 0 1 newpool)
                          (fn2-run-read-bytes (len body) dst dg *fn2-run-entries-base* 9 0 1 pool))
                   (equal (fn2-run-read-bytes (len bytes) dst dg off 9 0 1 newpool) bytes)
                   (equal (fn2-run-saved-offsets newnr first newrs)
                          (append (fn2-run-saved-offsets nr first restarts) (if restartp (list off) nil))))
              (fn2-run-open-overview-contents-p (append rows (list row)) w (1+ idx) newnr (+ off (len bytes))
                                                dst dg newrs newpool)))
   :rule-classes nil
   :hints (("Goal" :use ((:instance fn2-run-read-prefix (n (len (fn2-run-entries-octets *fn2-overview-entry* rows)))
                            (m (len (fn2-layout-octets *fn2-overview-entry* row))) (at *fn2-run-entries-base*)
                            (slot dst) (gen dg) (pk 9) (ps 0) (pg 1) (pool newpool)))
            :in-theory (e/d (fn2-run-open-overview-contents-p)
                      (fn2-run-read-bytes fn2-run-saved-offsets fn2-run-spliced-entry-bytes fn2-run-entries-octets
                       fn2-layout-octets fn2-run-restart-offsets-spec mod binary-append))))))

(local
 (defthm fn2-run-previous-body-ends-at-cursor
   (implies (fn2-run-open-overview-contents-p rows w idx nr off dst dg restarts pool)
            (equal (+ *fn2-run-entries-base* (len (fn2-run-entries-octets *fn2-overview-entry* rows))) off))
   :rule-classes nil
   :hints (("Goal" :in-theory (union-theories (theory 'minimal-theory) '(fn2-run-open-overview-contents-p))))))

(defthmd fn2-run-builder-extends-overview-page
  (fn2-run-checked-overview-append
   (implies (and (natp w) (< (+ (* w *fn2-run-restart-capacity*) nr) (fn2-run-restarts-rows restarts))
                 (fn2-run-open-overview-contents-p rows w idx nr off dst dg restarts pool)
                 (or (<= (+ (fn2-pool-base dst pool) off) source)
                     (<= (+ source n) (+ (fn2-pool-base dst pool) *fn2-run-entries-base*))))
            (and (equal (car build) :ok)
                 (equal (fn2-run-writers-restarts w after) (if restartp (1+ nr) nr))
                 (fn2-run-open-overview-contents-p (append rows (list row)) w
                    (fn2-run-writers-entries w after) (fn2-run-writers-restarts w after)
                    (fn2-run-writers-cursor w after) dst dg (mv-nth 3 build) (mv-nth 5 build)))))
  :hints (("Goal" :do-not '(preprocess)
           :use (fn2-run-builder-appends-overview-source-row
                 (:instance fn2-run-builder-append-keeps-prior-rows (start *fn2-run-entries-base*)
                            (count (len (fn2-run-entries-octets *fn2-overview-entry* rows))))
                 (:instance fn2-run-note-extends-restart-list (w (fn2-run-builds-wbase 0 builds)))
                 (:instance fn2-run-successful-build-keeps-noted-restarts (b 0) (base *fn2-run-run-entry*)
                            (f (mv-nth 2 (fn2-run-load-values *fn2-overview-entry* row *fn2-run-run-entry* src sg at 9 0 1 f pool)))
                            (pool (mv-nth 3 (fn2-run-load-values *fn2-overview-entry* row *fn2-run-run-entry* src sg at 9 0 1 f pool))))
                 (:instance fn2-run-previous-body-ends-at-cursor
                            (w (fn2-run-builds-wbase 0 builds))
                            (idx (fn2-run-writers-entries (fn2-run-builds-wbase 0 builds) writers))
                            (nr (fn2-run-writers-restarts (fn2-run-builds-wbase 0 builds) writers))
                            (off (fn2-run-writers-cursor (fn2-run-builds-wbase 0 builds) writers))
                            (dst (fn2-run-writers-slot (fn2-run-builds-wbase 0 builds) writers))
                            (dg (fn2-run-writers-gen (fn2-run-builds-wbase 0 builds) writers)))
                 (:instance fn2-run-join-written-entry
                            (w (fn2-run-builds-wbase 0 builds))
                            (idx (fn2-run-writers-entries (fn2-run-builds-wbase 0 builds) writers))
                            (nr (fn2-run-writers-restarts (fn2-run-builds-wbase 0 builds) writers))
                            (off (fn2-run-writers-cursor (fn2-run-builds-wbase 0 builds) writers))
                            (dst (fn2-run-writers-slot (fn2-run-builds-wbase 0 builds) writers))
                            (dg (fn2-run-writers-gen (fn2-run-builds-wbase 0 builds) writers))
                            (newrs (let ((load (fn2-run-load-values *fn2-overview-entry* row *fn2-run-run-entry* src sg at 9 0 1 f pool)))
                                     (mv-nth 3 (fn2-run-build-add 0 *fn2-run-run-entry* builds writers restarts
                                                                 (mv-nth 2 load) (mv-nth 3 load)))))
                            (newpool (let ((load (fn2-run-load-values *fn2-overview-entry* row *fn2-run-run-entry* src sg at 9 0 1 f pool)))
                                     (mv-nth 5 (fn2-run-build-add 0 *fn2-run-run-entry* builds writers restarts
                                                                 (mv-nth 2 load) (mv-nth 3 load)))))))
           :in-theory (union-theories (theory 'minimal-theory)
                       '(eq not (:e equal) (:e natp) (:type-prescription len) natp-compound-recognizer
                         commutativity-of-+ associativity-of-+)))))
