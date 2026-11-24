; The adapter gives a closing writer 4096 bytes per step. A page with at most
; 1024 restarts therefore writes its entire directory in the first step.
(in-package "ACL2")
(include-book "runs-restart-lookup-proof")

(defthm fn2-run-close-writes-directory
  (let* ((cursor (fn2-run-writers-cursor w writers)) (k (fn2-run-writers-restarts w writers))
         (slot (fn2-run-writers-slot w writers)) (gen (fn2-run-writers-gen w writers))
         (pk (fn2-run-writers-okind w writers)) (ps (fn2-run-writers-oslot w writers))
         (pg (fn2-run-writers-ogen w writers)) (end (+ cursor (* 4 k)))
         (row (* *fn2-run-restart-capacity* w))
         (scratch (+ *fn2-run-scratch-fields* (fn2-run-writers-fields w writers)))
         (write (fn2-run-write-restarts k 0 w cursor scratch slot gen pk ps pg restarts f pool))
         (close (fn2-run-close-step w 4096 writers restarts f pool)))
    (implies (and (natp w) (equal (fn2-run-writers-phase w writers) *fn2-run-writer-phase-closing*)
                  (equal (fn2-run-writers-pos w writers) 0)
                  (posp k) (<= k 1024) (natp cursor) (natp scratch)
                  (<= (+ row k) (fn2-run-restarts-rows restarts))
                  (fn2-run-restartsp restarts) (fn2-run-restarts-wfp restarts)
                  (unsigned-byte-p 32 end) (natp (fn2-pool-base slot pool))
                  (equal (fn2-layout-range-code slot gen cursor end t pk ps pg pool) :ok))
             (and (equal (car close) :more)
                  (equal (mv-nth 1 close) (fn2-run-writers-set-pos w (* 4 k) writers))
                  (equal (mv-nth 2 close) (mv-nth 1 write))
                  (equal (mv-nth 3 close) (mv-nth 1 (fn2-run-load-bytes
                                  (fn2-run-directory-octets (fn2-run-saved-offsets k row restarts))
                                  slot gen cursor pk ps pg pool))))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance fn2-run-write-restarts-serializes-directory (j 0)
                    (k (fn2-run-writers-restarts w writers)) (slot (fn2-run-writers-slot w writers))
                    (gen (fn2-run-writers-gen w writers)) (cursor (fn2-run-writers-cursor w writers))
                    (scratch (+ *fn2-run-scratch-fields* (fn2-run-writers-fields w writers)))
                    (pk (fn2-run-writers-okind w writers)) (ps (fn2-run-writers-oslot w writers))
                    (pg (fn2-run-writers-ogen w writers))))
           :in-theory (e/d (fn2-run-close-step)
                    (fn2-run-write-restarts fn2-run-writers-slot fn2-run-writers-gen fn2-run-writers-pos
                     fn2-run-writers-cursor fn2-run-writers-restarts fn2-run-writers-okind fn2-run-writers-oslot
                     fn2-run-writers-ogen fn2-run-writers-fields fn2-run-writers-phase fn2-run-writers-set-pos
                     fn2-run-saved-offsets fn2-run-directory-octets fn2-run-load-bytes fn2-pool-base
                     fn2-run-restarts-rows fn2-run-restartsp fn2-run-restarts-wfp fn2-layout-range-code)))))

(defthm fn2-run-close-keeps-entry-bytes
  (let* ((cursor (fn2-run-writers-cursor w writers)) (k (fn2-run-writers-restarts w writers))
         (slot (fn2-run-writers-slot w writers)) (gen (fn2-run-writers-gen w writers))
         (pk (fn2-run-writers-okind w writers)) (ps (fn2-run-writers-oslot w writers))
         (pg (fn2-run-writers-ogen w writers)) (end (+ cursor (* 4 k)))
         (row (* *fn2-run-restart-capacity* w))
         (after (mv-nth 3 (fn2-run-close-step w 4096 writers restarts f pool))))
    (implies (and (natp w) (equal (fn2-run-writers-phase w writers) *fn2-run-writer-phase-closing*)
                  (equal (fn2-run-writers-pos w writers) 0)
                  (posp k) (<= k 1024) (natp cursor) (natp slot)
                  (natp (+ *fn2-run-scratch-fields* (fn2-run-writers-fields w writers)))
                  (<= (+ row k) (fn2-run-restarts-rows restarts))
                  (fn2-run-restartsp restarts) (fn2-run-restarts-wfp restarts)
                  (unsigned-byte-p 32 end) (natp (fn2-pool-base slot pool))
                  (equal (fn2-layout-range-code slot gen cursor end t pk ps pg pool) :ok)
                  (natp at) (natp n) (<= (+ at n) cursor))
             (equal (fn2-run-read-bytes n slot gen at pk ps pg after)
                    (fn2-run-read-bytes n slot gen at pk ps pg pool))))
  :rule-classes nil
  :hints (("Goal" :use (fn2-run-close-writes-directory
                        (:instance fn2-run-load-preserves-earlier-bytes
                    (src (fn2-run-writers-slot w writers)) (dst (fn2-run-writers-slot w writers))
                    (sg (fn2-run-writers-gen w writers)) (dg (fn2-run-writers-gen w writers))
                    (off (fn2-run-writers-cursor w writers)) (pk (fn2-run-writers-okind w writers))
                    (ps (fn2-run-writers-oslot w writers)) (pg (fn2-run-writers-ogen w writers))
                    (bytes (fn2-run-directory-octets (fn2-run-saved-offsets (fn2-run-writers-restarts w writers)
                                                     (* *fn2-run-restart-capacity* w) restarts)))))
           :in-theory (disable fn2-run-close-step fn2-run-read-bytes fn2-run-load-bytes fn2-run-directory-octets
                     fn2-run-saved-offsets fn2-run-writers-slot fn2-run-writers-gen fn2-run-writers-pos
                     fn2-run-writers-cursor fn2-run-writers-restarts fn2-run-writers-okind fn2-run-writers-oslot
                     fn2-run-writers-ogen fn2-run-writers-fields fn2-run-writers-phase fn2-run-writers-set-pos
                     fn2-run-write-restarts fn2-pool-base fn2-run-restarts-rows fn2-run-restartsp
                     fn2-run-restarts-wfp fn2-layout-range-code))))
