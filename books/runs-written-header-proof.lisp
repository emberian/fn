; The decoder's physical header predicate follows from writing typed fields.
(in-package "ACL2")
(include-book "runs-writer-header-bytes-proof")
(include-book "runs-header-values-proof")
(include-book "runs-header-overwrite-proof")

(defmacro fn2-run-header-room-p (layout vals off cap)
  `(and (fn2-run-header-values-valid-p ,layout ,vals) (natp ,off) (natp ,cap)
        (<= (+ ,off (fn2-layout-max-size ,layout)) ,cap) (<= ,cap *fn2-run-page-size*)
        (<= (fn2-layout-max-size ,layout) *fn2-codec-decode-fuel*)))

(local (defthm fn2-run-written-octets-proper
         (implies (fn-b3-octet-listp bytes) (equal (true-list-fix bytes) bytes))))

(defthmd fn2-run-filled-page-stores-typed-header
  (let* ((bytes (fn2-layout-octets layout vals))
         (write (fn2-run-load-bytes bytes slot gen off pk ps pg pool)) (after (mv-nth 1 write)))
    (implies (and (fn2-run-header-room-p layout vals off cap) (fn2-run-filled-page-p slot gen pk ps pg pool)
                  (unsigned-byte-p 32 slot) (unsigned-byte-p 60 gen) (fn2-poolp pool) (fn2-pool-wfp pool))
             (and (fn2-run-writable-header-p layout vals slot gen off cap pk ps pg pool)
                  (equal (car write) :ok) (fn2-run-filled-page-p slot gen pk ps pg after)
                  (fn2-poolp after) (fn2-pool-wfp after)
                  (fn2-run-stored-header-p layout vals slot gen off cap pk ps pg after))))
  :hints (("Goal" :do-not '(preprocess)
           :use (fn2-run-typed-header-has-canonical-encoding
                 (:instance fn2-run-filled-page-allows-subrange (start off) (end cap) (writep t))
                 (:instance fn2-run-load-bytes-roundtrip (bytes (fn2-layout-octets layout vals)))
                 (:instance fn2-run-overwrite-filled-page (bytes (fn2-layout-octets layout vals)) (i 0))
                 (:instance fn2-run-filled-page-allows-subrange (start off) (end cap) (writep nil)
                   (pool (mv-nth 1 (fn2-run-load-bytes (fn2-layout-octets layout vals) slot gen off pk ps pg pool)))))
           :in-theory (e/d (fn2-run-writable-header-p fn2-run-stored-header-p unsigned-byte-p)
                     (fn2-layout-max-size fn2-layout-octets fn2-run-header-values-valid-p fn2-run-header-scalars-p
                      fn2-run-values-layoutp fn-b3-octet-listp true-list-fix fn2-run-load-bytes fn2-run-read-bytes
                      fn2-pool-base fn2-poolp fn2-pool-wfp fn2-layout-range-code)))))

(defthmd fn2-run-later-write-preserves-stored-header
  (let* ((write (fn2-run-load-bytes bytes slot gen at pk ps pg pool)) (after (mv-nth 1 write)))
    (implies (and (fn2-run-stored-header-p layout vals slot gen off cap pk ps pg pool)
                  (fn2-run-filled-page-p slot gen pk ps pg pool) (<= cap at)
                  (natp at) (fn-b3-octet-listp bytes) (<= (+ at (len bytes)) *fn2-run-page-size*))
             (fn2-run-stored-header-p layout vals slot gen off cap pk ps pg after)))
  :hints (("Goal" :do-not '(preprocess)
           :use ((:instance fn2-run-overwrite-filled-page (off at) (i 0))
                 (:instance fn2-run-header-overwrite-retains-span (off at) (at off) (n (len (fn2-layout-octets layout vals))))
                 (:instance fn2-run-filled-page-allows-subrange (start off) (end cap) (writep nil)
                      (pool (mv-nth 1 (fn2-run-load-bytes bytes slot gen at pk ps pg pool)))))
           :in-theory (e/d (fn2-run-stored-header-p unsigned-byte-p)
                     (fn2-layout-max-size fn2-layout-octets fn2-run-header-values-valid-p fn2-run-header-scalars-p
                      fn2-run-values-layoutp fn-b3-octet-listp fn2-run-load-bytes fn2-run-read-bytes
                      fn2-pool-base fn2-poolp fn2-pool-wfp fn2-layout-range-code)))))
