; Bulk span-zero and span-copy over the pool. Each export checks handles and
; bounds once, then runs a raw loop over the byte array and sets the fill
; once; any span the precheck refuses falls back to the bytewise model, so
; every refusal code and partial-write prefix is the model's own.
(in-package "ACL2")
(include-book "pool-copy")
(fn2-book-layer :c)

; ------------------------------------------------------------------------
; The bytewise zero model: one checked fn2-pool-write per byte.
(defun fn2-pool-zero-bytes (n slot gen off okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool :measure (nfix n)
                  :guard (and (fn2-pool-wfp fn2-pool) (natp n) (natp off))
                  :guard-hints (("Goal" :in-theory (disable fn2-pool-write)))))
  (if (zp n) (mv :ok fn2-pool)
    (b* (((mv code fn2-pool) (fn2-pool-write slot gen off 0 okind oslot ogen fn2-pool))
         ((unless (eq code :ok)) (mv code fn2-pool)))
      (fn2-pool-zero-bytes (- n 1) slot gen (+ 1 off) okind oslot ogen fn2-pool))))
(fn2-pool-preserves fn2-pool-zero-bytes (n slot gen off okind oslot ogen fn2-pool) :position 1
 :disable nil :hints (("Goal" :in-theory (disable fn2-pool-write fn2-pool-rows))))

; ------------------------------------------------------------------------
; Raw loops over absolute indices into the byte array: no handle, owner or
; fill check, only the array bound in the guard. A typed pool holds octets,
; so a byte the copy loop reads always passes fn2-pool-write's octet check.
(local (defthm fn2-pool-span-data-octet
  (implies (and (fn2-poolp fn2-pool) (natp i) (< i (len (nth *fn2-pool-datai* fn2-pool))))
           (unsigned-byte-p 8 (nth i (nth *fn2-pool-datai* fn2-pool))))
  :hints (("Goal" :use ((:instance fn2-pool-datai-natp) (:instance fn2-pool-datai-bound))))))
(defun fn2-pool-zero-raw (n didx fn2-pool)
  (declare (xargs :stobjs fn2-pool :measure (nfix n)
                  :guard (and (fn2-poolp fn2-pool) (natp n) (natp didx)
                              (<= (+ didx n) (fn2-pool-data-length fn2-pool)))))
  (if (zp n) fn2-pool
    (let ((fn2-pool (update-fn2-pool-datai didx 0 fn2-pool)))
      (fn2-pool-zero-raw (- n 1) (+ 1 didx) fn2-pool))))

(defun fn2-pool-copy-raw (n sidx didx fn2-pool)
  (declare (xargs :stobjs fn2-pool :measure (nfix n)
                  :guard (and (fn2-poolp fn2-pool) (natp n) (natp sidx) (natp didx)
                              (<= (+ sidx n) (fn2-pool-data-length fn2-pool))
                              (<= (+ didx n) (fn2-pool-data-length fn2-pool)))))
  (if (zp n) fn2-pool
    (let ((fn2-pool (update-fn2-pool-datai didx (fn2-pool-datai sidx fn2-pool) fn2-pool)))
      (fn2-pool-copy-raw (- n 1) (+ 1 sidx) (+ 1 didx) fn2-pool))))

; The loops write only the byte array: every other field is framed, and the
; shape survives an in-bounds span.
(defthm fn2-pool-zero-raw-frame
  (implies (not (equal k *fn2-pool-datai*))
           (equal (nth k (fn2-pool-zero-raw n didx fn2-pool)) (nth k fn2-pool))))
(defthm fn2-pool-copy-raw-frame
  (implies (not (equal k *fn2-pool-datai*))
           (equal (nth k (fn2-pool-copy-raw n sidx didx fn2-pool)) (nth k fn2-pool))))
(defthm fn2-pool-zero-raw-rows
  (equal (fn2-pool-rows (fn2-pool-zero-raw n didx fn2-pool)) (fn2-pool-rows fn2-pool))
  :hints (("Goal" :in-theory (disable fn2-pool-rows))))
(defthm fn2-pool-copy-raw-rows
  (equal (fn2-pool-rows (fn2-pool-copy-raw n sidx didx fn2-pool)) (fn2-pool-rows fn2-pool))
  :hints (("Goal" :in-theory (disable fn2-pool-rows))))
(defthm fn2-pool-zero-raw-shape
  (implies (and (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool) (natp didx)
                (<= (+ didx (nfix n)) (fn2-pool-data-length fn2-pool)))
           (and (fn2-poolp (fn2-pool-zero-raw n didx fn2-pool))
                (fn2-pool-wfp (fn2-pool-zero-raw n didx fn2-pool))
                (equal (fn2-pool-data-length (fn2-pool-zero-raw n didx fn2-pool))
                       (fn2-pool-data-length fn2-pool)))))
(defthm fn2-pool-copy-raw-shape
  (implies (and (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool) (natp sidx) (natp didx)
                (<= (+ sidx (nfix n)) (fn2-pool-data-length fn2-pool))
                (<= (+ didx (nfix n)) (fn2-pool-data-length fn2-pool)))
           (and (fn2-poolp (fn2-pool-copy-raw n sidx didx fn2-pool))
                (fn2-pool-wfp (fn2-pool-copy-raw n sidx didx fn2-pool))
                (equal (fn2-pool-data-length (fn2-pool-copy-raw n sidx didx fn2-pool))
                       (fn2-pool-data-length fn2-pool)))))

; Handle success names a live row (stated over the opened rows field, the form
; the bound rules on fill and cap are triggered by).
(local (defthm fn2-pool-span-workspace-ok-row
  (implies (equal (fn2-pool-workspace-code slot gen okind oslot ogen fn2-pool) :ok)
           (and (natp slot) (< slot (nth *fn2-pool-rows* fn2-pool))))
  :rule-classes :forward-chaining))
(local (defthm fn2-pool-span-readable-ok-row
  (implies (equal (fn2-pool-readable-code slot gen okind oslot ogen fn2-pool) :ok)
           (and (natp slot) (< slot (nth *fn2-pool-rows* fn2-pool))))
  :rule-classes :forward-chaining))

; ------------------------------------------------------------------------
; The span exports. One handle check and one bounds check, then the raw loop
; and a single fill update; a refused span runs the bytewise model.
(defun fn2-pool-zero-span (n slot gen off okind oslot ogen fn2-pool)
  (declare (xargs :stobjs fn2-pool
                  :guard (and (fn2-pool-wfp fn2-pool) (natp n) (natp off))))
  (if (zp n) (mv :ok fn2-pool)
    (let ((code (fn2-pool-workspace-code slot gen okind oslot ogen fn2-pool)))
      (cond ((not (eq code :ok)) (mv code fn2-pool))
            ((not (and (natp off) (<= off (fn2-pool-fill slot fn2-pool))
                       (<= (+ off n) (fn2-pool-cap slot fn2-pool))
                       (<= (+ (fn2-pool-base slot fn2-pool) off n) (fn2-pool-data-length fn2-pool))))
             (fn2-pool-zero-bytes n slot gen off okind oslot ogen fn2-pool))
            (t (let* ((new-fill (max (fn2-pool-fill slot fn2-pool) (+ off n)))
                      (fn2-pool (fn2-pool-zero-raw n (+ (fn2-pool-base slot fn2-pool) off) fn2-pool))
                      (fn2-pool (fn2-pool-set-fill slot new-fill fn2-pool)))
                 (mv :ok fn2-pool)))))))

(defun fn2-rd-copy-span (n sslot sgen soff sk ss sg dslot dgen doff dk ds dg fn2-pool)
  (declare (xargs :stobjs fn2-pool
                  :guard (and (fn2-pool-wfp fn2-pool) (natp n) (natp soff) (natp doff))))
  (cond ((zp n) (mv :ok fn2-pool))
        ((not (and (not (equal sslot dslot))
                   (eq (fn2-pool-readable-code sslot sgen sk ss sg fn2-pool) :ok)
                   (eq (fn2-pool-workspace-code dslot dgen dk ds dg fn2-pool) :ok)
                   (natp soff) (natp doff)
                   (<= (+ soff n) (fn2-pool-fill sslot fn2-pool))
                   (<= (+ (fn2-pool-base sslot fn2-pool) soff n) (fn2-pool-data-length fn2-pool))
                   (<= doff (fn2-pool-fill dslot fn2-pool))
                   (<= (+ doff n) (fn2-pool-cap dslot fn2-pool))
                   (<= (+ (fn2-pool-base dslot fn2-pool) doff n) (fn2-pool-data-length fn2-pool))))
         (fn2-rd-copy n sslot sgen soff sk ss sg dslot dgen doff dk ds dg fn2-pool))
        (t (let* ((new-fill (max (fn2-pool-fill dslot fn2-pool) (+ doff n)))
                  (fn2-pool (fn2-pool-copy-raw n (+ (fn2-pool-base sslot fn2-pool) soff)
                                               (+ (fn2-pool-base dslot fn2-pool) doff) fn2-pool))
                  (fn2-pool (fn2-pool-set-fill dslot new-fill fn2-pool)))
             (mv :ok fn2-pool)))))

; ------------------------------------------------------------------------
; Algebra of the two writes a span makes. The byte array and the fill column
; are different stobj fields, so a byte write commutes past a fill write, and
; the last of two fill writes to one row wins.
(local (defthm fn2-pool-span-update-nth-same
  (equal (update-nth i a (update-nth i b l)) (update-nth i a l))))
(local (defun fn2-pool-span-nth2-ind (i j l)
  (if (or (zp i) (zp j)) (list i j l)
    (fn2-pool-span-nth2-ind (- i 1) (- j 1) (cdr l)))))
(local (defthmd fn2-pool-span-update-nth-diff
  (implies (not (equal (nfix i) (nfix j)))
           (equal (update-nth i a (update-nth j b l))
                  (update-nth j b (update-nth i a l))))
  :hints (("Goal" :induct (fn2-pool-span-nth2-ind i j l)))))
(local (defthm fn2-pool-span-datai-of-set-fill
  (equal (update-fn2-pool-datai i x (fn2-pool-set-fill d v fn2-pool))
         (fn2-pool-set-fill d v (update-fn2-pool-datai i x fn2-pool)))
  :hints (("Goal" :in-theory (enable fn2-pool-set-fill update-fn2-pool-fill$ai
                                     update-fn2-pool-datai fn2-pool-span-update-nth-diff)))))
(local (defthm fn2-pool-span-set-fill-twice
  (equal (fn2-pool-set-fill d a (fn2-pool-set-fill d b fn2-pool))
         (fn2-pool-set-fill d a fn2-pool))
  :hints (("Goal" :in-theory (enable fn2-pool-set-fill update-fn2-pool-fill$ai)))))
(local (defthm fn2-pool-span-zero-raw-of-set-fill
  (equal (fn2-pool-zero-raw n didx (fn2-pool-set-fill d v fn2-pool))
         (fn2-pool-set-fill d v (fn2-pool-zero-raw n didx fn2-pool)))))
(local (defthm fn2-pool-span-copy-raw-of-set-fill
  (equal (fn2-pool-copy-raw n sidx didx (fn2-pool-set-fill d v fn2-pool))
         (fn2-pool-set-fill d v (fn2-pool-copy-raw n sidx didx fn2-pool)))))

; ------------------------------------------------------------------------
; One accepted byte. A checked read or write whose checks pass is the raw
; array access (and, for a write, the fill update); neither write moves a
; handle verdict, which reads no byte and no fill.
(local (defthm fn2-pool-span-read-ok
  (implies (and (equal (fn2-pool-readable-code slot gen okind oslot ogen fn2-pool) :ok)
                (natp idx) (< idx (fn2-pool-fill slot fn2-pool))
                (< (+ (fn2-pool-base slot fn2-pool) idx) (fn2-pool-data-length fn2-pool)))
           (equal (fn2-pool-read slot gen idx okind oslot ogen fn2-pool)
                  (mv :ok (fn2-pool-datai (+ (fn2-pool-base slot fn2-pool) idx) fn2-pool))))))
(local (defthm fn2-pool-span-write-ok
  (implies (and (equal (fn2-pool-workspace-code slot gen okind oslot ogen fn2-pool) :ok)
                (natp idx) (unsigned-byte-p 8 byte)
                (< idx (fn2-pool-cap slot fn2-pool)) (<= idx (fn2-pool-fill slot fn2-pool))
                (< (+ (fn2-pool-base slot fn2-pool) idx) (fn2-pool-data-length fn2-pool)))
           (equal (fn2-pool-write slot gen idx byte okind oslot ogen fn2-pool)
                  (mv :ok (fn2-pool-set-fill slot (max (fn2-pool-fill slot fn2-pool) (+ idx 1))
                                             (update-fn2-pool-datai (+ (fn2-pool-base slot fn2-pool) idx)
                                                                    byte fn2-pool)))))))
(local (defthm fn2-pool-span-workspace-code-of-update-datai
  (equal (fn2-pool-workspace-code slot gen okind oslot ogen (update-fn2-pool-datai i v fn2-pool))
         (fn2-pool-workspace-code slot gen okind oslot ogen fn2-pool))))
(local (defthm fn2-pool-span-workspace-code-of-set-fill
  (equal (fn2-pool-workspace-code slot gen okind oslot ogen (fn2-pool-set-fill d v fn2-pool))
         (fn2-pool-workspace-code slot gen okind oslot ogen fn2-pool))))
(local (defthm fn2-pool-span-readable-code-of-update-datai
  (equal (fn2-pool-readable-code slot gen okind oslot ogen (update-fn2-pool-datai i v fn2-pool))
         (fn2-pool-readable-code slot gen okind oslot ogen fn2-pool))))
(local (defthm fn2-pool-span-readable-code-of-set-fill
  (equal (fn2-pool-readable-code slot gen okind oslot ogen (fn2-pool-set-fill d v fn2-pool))
         (fn2-pool-readable-code slot gen okind oslot ogen fn2-pool))))
(local (defthm fn2-pool-zero-bytes-zp
  (implies (zp n)
           (equal (fn2-pool-zero-bytes n slot gen off okind oslot ogen fn2-pool)
                  (mv :ok fn2-pool)))))
(local (defthm fn2-rd-copy-zp
  (implies (zp n)
           (equal (fn2-rd-copy n sslot sgen soff sk ss sg dslot dgen doff dk ds dg fn2-pool)
                  (mv :ok fn2-pool)))
  :hints (("Goal" :in-theory (enable fn2-rd-copy)))))

; ------------------------------------------------------------------------
; A span the precheck accepts: the bytewise model succeeds at every byte, and
; its n writes and n fill updates are the raw loop and the last fill.
(local (defthm fn2-pool-zero-bytes-accepted
  (implies (and (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool) (not (zp n))
                (equal (fn2-pool-workspace-code slot gen okind oslot ogen fn2-pool) :ok)
                (natp off) (<= off (fn2-pool-fill slot fn2-pool))
                (<= (+ off n) (fn2-pool-cap slot fn2-pool))
                (<= (+ (fn2-pool-base slot fn2-pool) off n) (fn2-pool-data-length fn2-pool)))
           (equal (fn2-pool-zero-bytes n slot gen off okind oslot ogen fn2-pool)
                  (mv :ok (fn2-pool-set-fill slot (max (fn2-pool-fill slot fn2-pool) (+ off n))
                                             (fn2-pool-zero-raw n (+ (fn2-pool-base slot fn2-pool) off)
                                                                fn2-pool)))))
  :hints (("Goal" :induct (fn2-pool-zero-bytes n slot gen off okind oslot ogen fn2-pool)
           :in-theory (disable fn2-pool-write fn2-pool-workspace-code)
           :expand ((fn2-pool-zero-bytes n slot gen off okind oslot ogen fn2-pool)
                    (:free (didx) (fn2-pool-zero-raw n didx fn2-pool)))))))

(local (defthm fn2-rd-copy-accepted
  (implies (and (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool) (not (zp n))
                (not (equal sslot dslot))
                (equal (fn2-pool-readable-code sslot sgen sk ss sg fn2-pool) :ok)
                (equal (fn2-pool-workspace-code dslot dgen dk ds dg fn2-pool) :ok)
                (natp soff) (natp doff)
                (<= (+ soff n) (fn2-pool-fill sslot fn2-pool))
                (<= (+ (fn2-pool-base sslot fn2-pool) soff n) (fn2-pool-data-length fn2-pool))
                (<= doff (fn2-pool-fill dslot fn2-pool))
                (<= (+ doff n) (fn2-pool-cap dslot fn2-pool))
                (<= (+ (fn2-pool-base dslot fn2-pool) doff n) (fn2-pool-data-length fn2-pool)))
           (equal (fn2-rd-copy n sslot sgen soff sk ss sg dslot dgen doff dk ds dg fn2-pool)
                  (mv :ok (fn2-pool-set-fill dslot (max (fn2-pool-fill dslot fn2-pool) (+ doff n))
                                             (fn2-pool-copy-raw n (+ (fn2-pool-base sslot fn2-pool) soff)
                                                                (+ (fn2-pool-base dslot fn2-pool) doff)
                                                                fn2-pool)))))
  :hints (("Goal" :induct (fn2-rd-copy n sslot sgen soff sk ss sg dslot dgen doff dk ds dg fn2-pool)
           :in-theory (e/d ((:induction fn2-rd-copy))
                           (fn2-pool-read fn2-pool-write
                            fn2-pool-readable-code fn2-pool-workspace-code))
           :expand ((fn2-rd-copy n sslot sgen soff sk ss sg dslot dgen doff dk ds dg fn2-pool)
                    (:free (sidx didx) (fn2-pool-copy-raw n sidx didx fn2-pool)))))))

; ------------------------------------------------------------------------
; The exact equivalences: every result code, every byte, every fill.
(defthm fn2-pool-zero-span-is-zero-bytes
  (implies (and (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool))
           (equal (fn2-pool-zero-span n slot gen off okind oslot ogen fn2-pool)
                  (fn2-pool-zero-bytes n slot gen off okind oslot ogen fn2-pool))))

(defthm fn2-rd-copy-span-is-rd-copy
  (implies (and (fn2-poolp fn2-pool) (fn2-pool-wfp fn2-pool))
           (equal (fn2-rd-copy-span n sslot sgen soff sk ss sg dslot dgen doff dk ds dg fn2-pool)
                  (fn2-rd-copy n sslot sgen soff sk ss sg dslot dgen doff dk ds dg fn2-pool))))

(fn2-pool-preserves fn2-pool-zero-span (n slot gen off okind oslot ogen fn2-pool) :position 1
 :hints (("Goal" :in-theory (disable fn2-pool-rows fn2-pool-workspace-code))))
(fn2-pool-preserves fn2-rd-copy-span (n sslot sgen soff sk ss sg dslot dgen doff dk ds dg fn2-pool)
 :position 1
 :hints (("Goal" :in-theory (disable fn2-pool-rows fn2-pool-workspace-code fn2-pool-readable-code))))

(in-theory (disable fn2-pool-zero-bytes fn2-pool-zero-raw fn2-pool-copy-raw))

(assert-event
 (fn2-assert-compliant-p
  '(fn2-pool-zero-bytes fn2-pool-zero-raw fn2-pool-copy-raw fn2-pool-zero-span fn2-rd-copy-span)
  (w state)))
