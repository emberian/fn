; A reply cursor can widen by 20 octets at the V1 position boundary.
(in-package "ACL2")
(include-book "../books/fncu-pool")
(include-book "../books/xfnc-batch-codec")

(defun fn2-ppbp-seal (items next cursor-at cursor-len slot gen fn2-fields fn2-digests fn2-b3 fn2-pool)
  (declare (xargs :stobjs (fn2-fields fn2-digests fn2-b3 fn2-pool) :verify-guards nil))
  (b* ((chain-at (fn2-pool-fill-value slot fn2-pool))
       ((mv code fn2-pool) (fn2-fnct-put-be 0 0 32 slot gen 1 2 3 fn2-pool))
       ((unless (eq code :ok)) (mv code 0 fn2-fields fn2-digests fn2-b3 fn2-pool))
       ((mv header result-at header-len fn2-fields fn2-pool)
        (fn2-xfnc-put-batch-header 0 #x010203 #x040506 1 chain-at 1 1
                                   next next 0 1 cursor-at cursor-len slot gen 1 2 3
                                   fn2-fields fn2-pool))
       ((unless (and (eq header :ok) (equal header-len 158)))
        (mv :header 0 fn2-fields fn2-digests fn2-b3 fn2-pool))
       ((mv filled fn2-pool) (fn2-fnct-put-be 0 0 items slot gen 1 2 3 fn2-pool))
       ((unless (eq filled :ok)) (mv filled 0 fn2-fields fn2-digests fn2-b3 fn2-pool))
       ((mv sealed & count fn2-fields fn2-digests fn2-b3 fn2-pool)
        (fn2-fnct-put-k28 0 0 0 0 0 result-at (+ header-len items)
                         slot gen 1 2 3 fn2-fields fn2-digests fn2-b3 fn2-pool)))
    (mv sealed count fn2-fields fn2-digests fn2-b3 fn2-pool)))

(defun fn2-ppbp-check (fn2-fields fn2-digests fn2-b3 fn2-pool)
  (declare (xargs :stobjs (fn2-fields fn2-digests fn2-b3 fn2-pool) :verify-guards nil))
  (b* ((fn2-fields (fn2-fields-init 128 fn2-fields))
       (fn2-digests (fn2-digests-init *fn2-digest-stride* fn2-digests))
       (fn2-b3 (fn2-b3-table-init 1 fn2-b3))
       ;; Keep producer scratch and both sealed frames for extent comparison.
       (fn2-pool (fn2-pool-init '((1 . 4096)) 1 100 fn2-pool))
       ((mv reserved slot gen fn2-pool) (fn2-pool-reserve 0 1 2 3 fn2-pool))
       (old #xffffffff) (next (+ old 1))
       ((mv original v1-at v1-len fn2-fields fn2-pool)
        (fn2-cns-put-query-cursor 0 #x070809 #x0a0b #x010203 #x040506 #x0c0d
                                  1 1 1 old slot gen 1 2 3 fn2-fields fn2-pool))
       ((mv successor v2-at v2-len fn2-fields fn2-pool)
        (fn2-cns-put-query-cursor 0 #x070809 #x0a0b #x010203 #x040506 #x0c0d
                                  1 1 1 next slot gen 1 2 3 fn2-fields fn2-pool))
       ((mv read-v1 v1) (fn2-pool-read slot gen (+ v1-at 4) 1 2 3 fn2-pool))
       ((mv read-v2 v2) (fn2-pool-read slot gen (+ v2-at 4) 1 2 3 fn2-pool))
       (v1-budget (fn2-xfnc-batch-read-budget v1 v1-len 512))
       (v2-budget (fn2-xfnc-batch-read-budget v2 v2-len 512))
       ;; The old budget subtracted the request's V1 extent from RX capacity.
       ((mv large large-len fn2-fields fn2-digests fn2-b3 fn2-pool)
        (fn2-ppbp-seal 325 next v2-at v2-len slot gen fn2-fields fn2-digests fn2-b3 fn2-pool))
       ((mv fitted fitted-len fn2-fields fn2-digests fn2-b3 fn2-pool)
        (fn2-ppbp-seal v1-budget next v2-at v2-len slot gen fn2-fields fn2-digests fn2-b3 fn2-pool)))
    (mv (and (eq reserved :ok) (eq original :ok) (eq successor :ok)
             (eq read-v1 :ok) (eq read-v2 :ok)
             (equal v1 1) (equal v1-len 39)
             (equal v2 2) (equal v2-len 59)
             (equal v1-budget 305) (equal v2-budget 305)
             (eq large :ok) (equal large-len 532)
             (eq fitted :ok) (equal fitted-len 512))
        fn2-fields fn2-digests fn2-b3 fn2-pool)))

(defun fn2-ppbp-test ()
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn2-fields
    (mv-let (ok fn2-fields)
      (with-local-stobj fn2-digests
        (mv-let (ok fn2-fields fn2-digests)
          (with-local-stobj fn2-b3
            (mv-let (ok fn2-fields fn2-digests fn2-b3)
              (with-local-stobj fn2-pool
                (mv-let (ok fn2-fields fn2-digests fn2-b3 fn2-pool)
                  (fn2-ppbp-check fn2-fields fn2-digests fn2-b3 fn2-pool)
                  (mv ok fn2-fields fn2-digests fn2-b3)))
              (mv ok fn2-fields fn2-digests)))
          (mv ok fn2-fields)))
      ok)))

(assert-event (fn2-ppbp-test))
