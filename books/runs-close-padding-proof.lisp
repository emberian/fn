; Padding extends the page to its full size without changing the entries or
; the restart directory written before it.
(in-package "ACL2")
(include-book "runs-page-copy-proof")

(local
 (defthm fn2-run-padding-load
   (implies (natp off)
            (equal (fn2-run-zero n slot gen off pk ps pg pool)
                   (fn2-run-load-bytes (fn2-layout-le n 0) slot gen off pk ps pg pool)))
   :hints (("Goal" :induct (fn2-run-zero n slot gen off pk ps pg pool)
            :expand ((fn2-layout-le n 0) (fn2-run-load-bytes (fn2-layout-le n 0) slot gen off pk ps pg pool))
            :in-theory (e/d (fn2-run-zero fn2-run-load-bytes fn2-layout-le)
                            (fn2-pool-write))))))

(local
 (defthm fn2-run-padding-bytes
   (and (equal (len (fn2-layout-le n 0)) (nfix n))
        (equal (true-list-fix (fn2-layout-le n 0)) (fn2-layout-le n 0))
        (fn-b3-octet-listp (fn2-layout-le n 0)))
   :hints (("Goal" :induct (fn2-layout-le n 0) :in-theory (enable fn2-layout-le)))))

(defthmd fn2-run-padding-keeps-page-prefix
  (let* ((write (fn2-run-zero n slot gen off pk ps pg pool)) (after (mv-nth 1 write)))
    (implies (and (natp n) (natp off) (<= (+ off n) cap)
                  (natp slot) (natp (fn2-pool-base slot pool))
                  (equal (fn2-layout-range-code slot gen off cap t pk ps pg pool) :ok)
                  (natp at) (natp size) (<= (+ at size) off))
             (and (equal (car write) :ok)
                  (equal (fn2-run-read-bytes size slot gen at pk ps pg after)
                         (fn2-run-read-bytes size slot gen at pk ps pg pool))
                  (equal (fn2-layout-range-code slot gen (+ off n) cap t pk ps pg after) :ok)
                  (equal (fn2-pool-base slot after) (fn2-pool-base slot pool)))))
  :hints (("Goal" :use ((:instance fn2-run-load-bytes-roundtrip (bytes (fn2-layout-le n 0)))
                        (:instance fn2-run-load-preserves-earlier-bytes (src slot) (dst slot)
                                   (sg gen) (dg gen) (bytes (fn2-layout-le n 0)) (n size)))
           :in-theory (e/d (fn2-run-load-preserves-base)
                         (fn2-run-zero fn2-run-load-bytes fn2-run-read-bytes
                          fn2-layout-range-code fn2-pool-base fn2-layout-le)))))

(defthm fn2-run-close-pads-stored-page
  (let* ((slot (fn2-run-writers-slot w writers)) (gen (fn2-run-writers-gen w writers))
         (pk (fn2-run-writers-okind w writers)) (ps (fn2-run-writers-oslot w writers))
         (pg (fn2-run-writers-ogen w writers))
         (cursor (fn2-run-writers-cursor w writers)) (pos (fn2-run-writers-pos w writers))
         (off (+ cursor pos)) (n (min 4096 (- *fn2-run-page-size* off)))
         (close (fn2-run-close-step w 4096 writers restarts f pool)) (after (mv-nth 3 close)))
    (implies (and (natp w) (equal (fn2-run-writers-phase w writers) *fn2-run-writer-phase-closing*)
                  (natp cursor) (natp pos) (<= (* 4 (fn2-run-writers-restarts w writers)) pos)
                  (<= off *fn2-run-page-size*) (natp slot) (natp (fn2-pool-base slot pool))
                  (equal (fn2-layout-range-code slot gen off *fn2-run-page-size* t pk ps pg pool) :ok)
                  (natp at) (natp size) (<= (+ at size) off))
             (and (equal (car close) (if (zp n) :ok :more))
                  (equal (mv-nth 1 close)
                         (if (zp n) (fn2-run-writers-set-phase w *fn2-run-writer-phase-heading* writers)
                           (fn2-run-writers-set-pos w (+ pos n) writers)))
                  (equal (mv-nth 2 close) f)
                  (equal (fn2-run-read-bytes size slot gen at pk ps pg after)
                         (fn2-run-read-bytes size slot gen at pk ps pg pool))
                  (equal (fn2-layout-range-code slot gen (+ off n) *fn2-run-page-size* t pk ps pg after) :ok)
                  (equal (fn2-pool-base slot after) (fn2-pool-base slot pool)))))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
           :use ((:instance fn2-run-padding-keeps-page-prefix
                       (n (min 4096 (- *fn2-run-page-size* (+ (fn2-run-writers-cursor w writers)
                                                              (fn2-run-writers-pos w writers)))))
                       (cap *fn2-run-page-size*) (slot (fn2-run-writers-slot w writers))
                       (gen (fn2-run-writers-gen w writers)) (pk (fn2-run-writers-okind w writers))
                       (ps (fn2-run-writers-oslot w writers)) (pg (fn2-run-writers-ogen w writers))
                       (off (+ (fn2-run-writers-cursor w writers) (fn2-run-writers-pos w writers)))))
           :in-theory (e/d (fn2-run-close-step)
                (fn2-run-read-bytes fn2-run-write-restarts fn2-run-load-bytes fn2-run-zero
                 fn2-run-writers-cursor fn2-run-writers-slot fn2-run-writers-gen fn2-run-writers-okind
                 fn2-run-writers-oslot fn2-run-writers-ogen fn2-run-writers-phase fn2-run-writers-fields
                 fn2-run-writers-restarts fn2-run-writers-pos fn2-run-writers-set-pos fn2-run-writers-set-phase
                 fn2-pool-base fn2-layout-range-code fn2-run-padding-load)))))
