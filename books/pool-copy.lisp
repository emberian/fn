; Exact shared owner-checked pool copy, independent of ordered read machines.
(in-package "ACL2")
(include-book "pool")
(include-book "std/util/bstar" :dir :system)
(fn2-book-layer :c)
; Nfix maps a malformed index to zero. Nonempty backing storage is therefore
; necessary when the checked upper bound alone licenses a logical write.
(local (defthm fn2-pool-update-nth-length-nonempty
 (implies (and (consp xs) (< i (len xs)))
          (equal (len (update-nth i value xs)) (len xs)))
 :hints (("Goal" :induct (update-nth i value xs) :in-theory (enable update-nth)))))
(local (defthm fn2-pool-data-update-length-nonempty
 (implies (and (posp (fn2-pool-data-length fn2-pool))
               (< i (fn2-pool-data-length fn2-pool)))
          (equal (fn2-pool-data-length (update-fn2-pool-datai i value fn2-pool))
                 (fn2-pool-data-length fn2-pool)))
 :hints (("Goal" :in-theory (enable update-fn2-pool-datai fn2-pool-data-length)))))
(local (defthm fn2-pool-data-length-of-set-fill
 (equal (fn2-pool-data-length (fn2-pool-set-fill slot value fn2-pool))
        (fn2-pool-data-length fn2-pool))
 :hints (("Goal" :in-theory (e/d (fn2-pool-data-length) (fn2-pool-set-fill nth))))))
(defthm fn2-pool-write-data-length-when-nonempty
 (implies (posp (fn2-pool-data-length fn2-pool))
  (equal (fn2-pool-data-length
          (mv-nth 1 (fn2-pool-write slot gen idx byte okind oslot ogen fn2-pool)))
         (fn2-pool-data-length fn2-pool)))
 :hints (("Goal" :in-theory (e/d (fn2-pool-write)
   (fn2-pool-workspace-code fn2-pool-data-length fn2-pool-set-fill)))))
(defthm fn2-pool-write-invalid-byte-unchanged
 (implies (not (unsigned-byte-p 8 byte))
  (equal (mv-nth 1 (fn2-pool-write slot gen idx byte okind oslot ogen fn2-pool)) fn2-pool))
 :hints (("Goal" :in-theory (e/d (fn2-pool-write) (fn2-pool-workspace-code)))))
(local (defthm fn2-pool-valid-data-byte-nonempty
 (implies (unsigned-byte-p 8 (fn2-pool-datai i fn2-pool))
          (posp (fn2-pool-data-length fn2-pool)))
 :hints (("Goal" :cases ((consp (nth *fn2-pool-datai* fn2-pool)))
   :in-theory (enable fn2-pool-datai fn2-pool-data-length unsigned-byte-p integer-range-p)))))
(defthm fn2-pool-read-valid-byte-data-nonempty
 (implies
  (and (equal (car (fn2-pool-read slot gen idx okind oslot ogen fn2-pool)) :ok)
       (unsigned-byte-p 8 (mv-nth 1 (fn2-pool-read slot gen idx okind oslot ogen fn2-pool))))
  (posp (fn2-pool-data-length fn2-pool)))
 :hints (("Goal" :in-theory (e/d (fn2-pool-read)
   (fn2-pool-readable-code fn2-pool-data-length fn2-pool-datai)))))
(local (defthm fn2-pool-read-write-data-length
 (implies (equal (car (fn2-pool-read sslot sgen soff sk ss sg fn2-pool)) :ok)
  (equal
   (fn2-pool-data-length
    (mv-nth 1 (fn2-pool-write dslot dgen doff
                (mv-nth 1 (fn2-pool-read sslot sgen soff sk ss sg fn2-pool))
                dk ds dg fn2-pool)))
   (fn2-pool-data-length fn2-pool)))
 :hints (("Goal"
   :cases ((unsigned-byte-p 8 (mv-nth 1 (fn2-pool-read sslot sgen soff sk ss sg fn2-pool))))
   :use ((:instance fn2-pool-read-valid-byte-data-nonempty
           (slot sslot) (gen sgen) (idx soff) (okind sk) (oslot ss) (ogen sg)))
   :in-theory (disable fn2-pool-read fn2-pool-write fn2-pool-data-length
                      fn2-pool-read-valid-byte-data-nonempty)))))

(defun fn2-rd-copy (n sslot sgen soff sk ss sg dslot dgen doff dk ds dg fn2-pool)
 (declare (xargs :stobjs fn2-pool :measure (nfix n) :guard (and (fn2-pool-wfp fn2-pool) (natp n) (natp soff) (natp doff))
  :guard-hints (("Goal" :in-theory (disable fn2-pool-read fn2-pool-write)))))
 (if (zp n) (mv :ok fn2-pool)
  (b* (((mv code byte) (fn2-pool-read sslot sgen soff sk ss sg fn2-pool))
       ((unless (eq code :ok)) (mv code fn2-pool))
       ((mv code fn2-pool) (fn2-pool-write dslot dgen doff byte dk ds dg fn2-pool))
       ((unless (eq code :ok)) (mv code fn2-pool)))
   (fn2-rd-copy (- n 1) sslot sgen (+ 1 soff) sk ss sg dslot dgen (+ 1 doff) dk ds dg fn2-pool))))
(fn2-pool-preserves fn2-rd-copy (n sslot sgen soff sk ss sg dslot dgen doff dk ds dg fn2-pool) :position 1
 :hints (("Goal" :in-theory (disable fn2-pool-read fn2-pool-write fn2-pool-rows))))
(in-theory (disable fn2-rd-copy))

; This actual loop either refuses the read, refuses an invalid byte unchanged,
; or writes into nonempty data. No typed-state/guard premise is borrowed.
(defthm fn2-rd-copy-data-length
 (equal (fn2-pool-data-length
          (mv-nth 1 (fn2-rd-copy n sslot sgen soff sk ss sg dslot dgen doff dk ds dg fn2-pool)))
        (fn2-pool-data-length fn2-pool))
 :hints (("Goal" :induct (fn2-rd-copy n sslot sgen soff sk ss sg dslot dgen doff dk ds dg fn2-pool)
   :in-theory (e/d (fn2-rd-copy) (fn2-pool-read fn2-pool-write fn2-pool-data-length)))))
