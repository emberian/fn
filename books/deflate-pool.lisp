; fn: the served read's pooled payload decoder (lane compress-3, Q15's
; follow-on, PRF-949).  Prefix `fn-zpl-'.
;
; `fn-pzd-decode-bufs' (books/payload-deflate.lisp) makes every buffer it
; reads, so each payload rebuilds the 64 KiB window: a 32 KiB zero ring and
; the dictionary's last 32 KiB appended from its octet list (with its
; length, a walk of the list).  That rebuild cost more than the decode.
;
; This entry carries a POOL value with the buffers, (DICT H DIRTY): the
; window holds DICT's ready window (`fn-zpl-ready-window') everywhere
; except its first DIRTY cells, H is the preset's length.  A call over the
; same dictionary (an `equal' that is `eq' for the shared table entry) only
; zeroes those DIRTY cells and remakes the small table; any other call
; makes the buffers as `fn-zin-payload-ready' does.  The decoder writes
; only ring cells below min(TOUT, 32 KiB) and never the preset half
; (books/deflate-frame.lisp, KEYSTONE `fn-zfr-loop-ahead-frame'), so the
; answer carries a pool whose invariant (`fn-zpl-pool-okp') holds again.
;
; KEYSTONES: `fn-zpl-decode-bufs-is-decode' (the host entry answers
; `fn-pzd-decode''s status, and on :ok its output buffer holds the
; decoder's octets, and it returns a pool that satisfies the invariant) and
; `fn-zpl-decode-bufs-is-the-lz-value' (an :ok answer's octets are the
; value A-DURABLE-LZ names).  The host (host/native/deflate.lisp
; fnn-pzd-decode) starts each buffer set with the pool NIL, which
; satisfies the invariant, and passes back only what the entry returned.

(in-package "ACL2")
(include-book "payload-lz-record")
(include-book "deflate-frame")

; -----------------------------------------------------------------------------
; The invariant.

(defun-nx fn-zpl-ready-window (dict)
  (mv-nth 1 (fn-zin-payload-ready dict nil nil)))

(defun-nx fn-zpl-ready-h (dict)
  (car (fn-zin-payload-ready dict nil nil)))

(defun-nx fn-zpl-pool-okp (pool fn-zin-win)
  ; NIL (no window made yet), or (DICT H DIRTY) with the window DICT's ready
  ; window from cell DIRTY on.
  (or (atom pool)
      (let ((dict (car pool)) (h (cadr pool)) (k (caddr pool)))
        (and (fn-cbor-octet-listp dict)
             (equal h (fn-zpl-ready-h dict))
             (natp k) (<= k *fn-zin-window*)
             (fn-cbor-octet-listp fn-zin-win)
             (equal (len fn-zin-win) *fn-zin-win-octets*)
             (equal (nthcdr k fn-zin-win) (nthcdr k (fn-zpl-ready-window dict)))))))

; -----------------------------------------------------------------------------
; Making the buffers from a pool.

(defun fn-zpl-zero-below (i n fn-zin-win)
  ; Cells [I, N) := 0.
  (declare (xargs :stobjs fn-zin-win
                  :guard (and (natp i) (natp n) (<= n (fn-zin-win-len fn-zin-win)))
                  :measure (nfix (- (nfix n) (nfix i)))))
  (if (and (mbt (and (natp i) (natp n))) (< i n) (< i (fn-zin-win-len fn-zin-win)))
      (let ((fn-zin-win (fn-zin-win-put i 0 fn-zin-win)))
        (fn-zpl-zero-below (1+ i) n fn-zin-win))
    fn-zin-win))


(defun fn-zpl-zeros (n)
  (declare (xargs :guard (natp n)))
  (if (zp n) nil (cons 0 (fn-zpl-zeros (1- n)))))
(local (defthm fn-zpl-nthcdr-update-nth-below
  (implies (and (natp i) (natp n) (< i n))
           (equal (nthcdr n (update-nth i o x)) (nthcdr n x)))
  :hints (("Goal" :induct (list (nthcdr i x) (nthcdr n x)) :in-theory (enable update-nth nthcdr)))))
(local (defthm fn-zpl-take-update-nth-at
  (implies (and (natp i) (< i (len x)))
           (equal (take (1+ i) (update-nth i o x)) (append (take i x) (list o))))
  :hints (("Goal" :induct (update-nth i o x) :in-theory (enable update-nth)))))
(local (defthm fn-zpl-zeros-snoc
  (implies (natp k) (equal (append (list 0) (fn-zpl-zeros k)) (fn-zpl-zeros (1+ k))))))
(local (defthm fn-zpl-append-take-nthcdr
  (implies (and (natp i) (<= i (len x)) (true-listp x))
           (equal (append (take i x) (nthcdr i x)) x))
  :hints (("Goal" :induct (nthcdr i x) :in-theory (enable nthcdr)))))
(defthm fn-zpl-zero-below-is
  (implies (and (natp i) (natp n) (<= i n) (<= n (len win)) (true-listp win))
           (equal (fn-zpl-zero-below i n win)
                  (append (take i win) (fn-zpl-zeros (- n i)) (nthcdr n win))))
  :hints (("Goal" :induct (fn-zpl-zero-below i n win))
          ("Subgoal *1/1" :use ((:instance fn-zpl-zeros-snoc (k (- n (+ 1 i)))))
                          :in-theory (disable fn-zpl-zeros-snoc))))

(local (defthm fn-zpl-len-zeros (equal (len (fn-zpl-zeros n)) (nfix n))))
(local (defun fn-zpl-ind2 (i n) (if (or (zp n) (zp i)) (list i n) (fn-zpl-ind2 (1- i) (1- n)))))
(local (defthm fn-zpl-nth-zeros (implies (< (nfix i) (nfix n)) (equal (nth i (fn-zpl-zeros n)) 0))
  :hints (("Goal" :induct (fn-zpl-ind2 i n) :in-theory (enable nth)))))
(local (defthm fn-zpl-zeros-append-0
  (equal (append (fn-zpl-zeros n) (list 0)) (fn-zpl-zeros (+ 1 (nfix n))))))
(local (defun fn-zpl-ind3 (m n) (if (zp n) m (fn-zpl-ind3 (1+ m) (1- n)))))
(local (defthm fn-zpl-back-copy-zeros
  (implies (posp m)
           (equal (fn-oct-back-copy 1 n (fn-zpl-zeros m)) (fn-zpl-zeros (+ m (nfix n)))))
  :hints (("Goal" :induct (fn-zpl-ind3 m n)
           :expand ((fn-oct-back-copy 1 n (fn-zpl-zeros m)))
           :in-theory (disable fn-zpl-zeros (:e fn-zpl-zeros))))))
(local (defthm fn-zpl-take-append-zeros
  (implies (and (natp k) (<= k (nfix m)))
           (equal (take k (append (fn-zpl-zeros m) y)) (fn-zpl-zeros k)))
  :hints (("Goal" :induct (fn-zpl-ind2 k m) :in-theory (disable (:e fn-zpl-zeros))))))
(local (defthm fn-zpl-back-copy-one-zero
  (equal (fn-oct-back-copy 1 n '(0)) (fn-zpl-zeros (+ 1 (nfix n))))
  :hints (("Goal" :use ((:instance fn-zpl-back-copy-zeros (m 1)))
           :in-theory (disable fn-zpl-back-copy-zeros (:e fn-zpl-zeros) (:e fn-oct-back-copy))
           :expand ((fn-zpl-zeros 1))))))
(local (defthm fn-zpl-take-append-short
  (implies (and (natp k) (<= k (len xs)))
           (equal (take k (append xs ys)) (take k xs)))
  :hints (("Goal" :induct (fn-zpl-ind2 k xs) :in-theory (enable take)))))
(local (defthm fn-zpl-len-snoc (equal (len (fn-oct-snoc xs o)) (+ 1 (len xs)))))
(local (defthm fn-zpl-take-snoc
  (implies (and (natp k) (<= k (len xs)))
           (equal (take k (fn-oct-snoc xs o)) (take k xs)))
  :hints (("Goal" :induct (fn-zpl-ind2 k xs) :in-theory (enable take)))))
(local (defthm fn-zpl-take-back-copy
  (implies (and (natp k) (<= k (len xs)))
           (equal (take k (fn-oct-back-copy off n xs)) (take k xs)))
  :hints (("Goal" :induct (fn-oct-back-copy off n xs) :in-theory (disable fn-oct-snoc-is-append)))))
(local (defthm fn-zpl-take-zeros
  (implies (and (natp k) (<= k (nfix m)))
           (equal (take k (fn-zpl-zeros m)) (fn-zpl-zeros k)))
  :hints (("Goal" :induct (fn-zpl-ind2 k m) :in-theory (disable (:e fn-zpl-zeros))))))
(defthm fn-zpl-ready-window-low
  (implies (and (fn-cbor-octet-listp dict) (natp k) (<= k 32768))
           (equal (take k (fn-zpl-ready-window dict)) (fn-zpl-zeros k)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-zin-payload-ready fn-zpl-ready-window)
                           (fn-zpl-zeros (:e fn-zpl-zeros) (:e fn-oct-back-copy) (:e fn-oct-snoc)
                            (:e fn-octets$a-append-back) (:e fn-oct-cat)
                            (:e fn-zin-win-append-back) (:e fn-zin-tab-append-back))))))

(defun fn-zpl-tab-ready (fn-zin-tab)
  ; The table zero: what fn-zin-payload-ready makes of it.
  (declare (xargs :stobjs fn-zin-tab))
  (let* ((fn-zin-tab (fn-zin-tab-clear fn-zin-tab))
         (fn-zin-tab (fn-zin-tab-reserve *fn-zin-tab-octets* fn-zin-tab))
         (fn-zin-tab (fn-zin-tab-append-octet 0 fn-zin-tab)))
    (fn-zin-tab-append-back 1 (1- *fn-zin-tab-octets*) fn-zin-tab)))

(defun fn-zpl-reusep (pool dict fn-zin-win)
  (declare (xargs :stobjs fn-zin-win :guard t))
  (and (consp pool) (consp (cdr pool)) (consp (cddr pool))
       (equal (car pool) dict)
       (natp (cadr pool)) (<= (cadr pool) *fn-zin-window*)
       (natp (caddr pool)) (<= (caddr pool) *fn-zin-window*)
       (fn-zin-window-ready-p fn-zin-win)))

(defun fn-zpl-prepare (pool dict fn-zin-win fn-zin-tab)
  ; (mv H fn-zin-win fn-zin-tab), as fn-zin-payload-ready makes them.
  (declare (xargs :stobjs (fn-zin-win fn-zin-tab)
                  :guard (fn-cbor-octet-listp dict)))
  (if (fn-zpl-reusep pool dict fn-zin-win)
      (let* ((fn-zin-win (fn-zpl-zero-below 0 (caddr pool) fn-zin-win))
             (fn-zin-tab (fn-zpl-tab-ready fn-zin-tab)))
        (mv (cadr pool) fn-zin-win fn-zin-tab))
    (fn-zin-payload-ready dict fn-zin-win fn-zin-tab)))

; -----------------------------------------------------------------------------
(local (defthm fn-zpl-ready-window-shape
  (implies (fn-cbor-octet-listp dict)
           (and (fn-cbor-octet-listp (fn-zpl-ready-window dict))
                (true-listp (fn-zpl-ready-window dict))
                (equal (len (fn-zpl-ready-window dict)) *fn-zin-win-octets*)))
  :hints (("Goal" :use ((:instance fn-zin-payload-ready-shape (fn-zin-win nil) (fn-zin-tab nil)))
           :in-theory (e/d (fn-zpl-ready-window) (fn-zin-payload-ready-shape))))))
(local (defthm fn-zpl-rezero-is-ready
  (implies (and (fn-cbor-octet-listp dict) (natp k) (<= k 32768)
                (true-listp win) (equal (len win) *fn-zin-win-octets*)
                (equal (nthcdr k win) (nthcdr k (fn-zpl-ready-window dict))))
           (equal (fn-zpl-zero-below 0 k win) (fn-zpl-ready-window dict)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-zpl-append-take-nthcdr (i k) (x (fn-zpl-ready-window dict))))
           :in-theory (disable fn-zpl-append-take-nthcdr fn-zpl-ready-window fn-zpl-zeros)))))
(local (defthm fn-zpl-tab-ready-logic
  (equal (fn-zpl-tab-ready fn-zin-tab) (fn-oct-back-copy 1 3493 '(0)))
  :hints (("Goal" :in-theory (set-difference-theories (enable fn-zpl-tab-ready)
                                                      (executable-counterpart-theory :here))))))
(local (defthm fn-zpl-ready-tab-logic
  (equal (mv-nth 2 (fn-zin-payload-ready dict fn-zin-win fn-zin-tab)) (fn-oct-back-copy 1 3493 '(0)))
  :hints (("Goal" :in-theory (set-difference-theories (enable fn-zin-payload-ready)
                                                      (executable-counterpart-theory :here))))))

(defthm fn-zpl-prepare-is-ready
  (implies (and (fn-zpl-pool-okp pool fn-zin-win) (fn-cbor-octet-listp dict))
           (let ((p (fn-zpl-prepare pool dict fn-zin-win fn-zin-tab))
                 (r (fn-zin-payload-ready dict nil nil)))
             (and (equal (car p) (car r))
                  (equal (mv-nth 1 p) (mv-nth 1 r))
                  (equal (mv-nth 2 p) (mv-nth 2 r)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-zpl-ready-h fn-zpl-ready-window)
                           (fn-zpl-zero-below fn-zpl-tab-ready fn-zin-payload-ready
                            (:e fn-zin-payload-ready) (:e fn-oct-back-copy))))))

; The decoder over a pool: fn-zin-payload-bufs with fn-zpl-prepare, and the
; pool it leaves.  (mv STATUS POOL fn-zin-win fn-zin-tab fn-zin-out).

(defun fn-zpl-payload-bufs (pool b dict start end lim fn-octets fn-zin-win fn-zin-tab
                                 fn-zin-out)
  (declare (xargs :stobjs (fn-octets fn-zin-win fn-zin-tab fn-zin-out)
                  :guard (and (natp b) (fn-cbor-octet-listp dict) (natp start) (natp end)
                              (natp lim) (<= end (fn-octets-len fn-octets)))))
  (with-local-stobj fn-zin-st
    (mv-let (st pool fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
      (let* ((fn-zin-out (fn-zin-out-clear fn-zin-out))
             (fn-zin-st (fn-zin-reset fn-zin-st)))
        (mv-let (h fn-zin-win fn-zin-tab) (fn-zpl-prepare pool dict fn-zin-win fn-zin-tab)
          (let ((fn-zin-st (fn-zin-set 18 h fn-zin-st)))
            (if (and (fn-zin-window-ready-p fn-zin-win) (fn-zin-tab-okp fn-zin-tab))
                (mv-let (st b2 ip fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)
                  (fn-zin-loop-ahead b start end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab
                                     fn-zin-out)
                  (declare (ignore b2 ip))
                  (mv st (list dict h (fn-zfr-dirty (fn-zin-tout fn-zin-st)))
                      fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))
              (mv (list :refused :buffers) nil fn-zin-st fn-zin-win fn-zin-tab fn-zin-out)))))
      (mv st pool fn-zin-win fn-zin-tab fn-zin-out))))

; THE HOST ENTRY: fn-pzd-decode-bufs over a pool.
; (mv ANSWER POOL fn-zin-win fn-zin-tab fn-zin-out).

(defun fn-zpl-decode-bufs (pool dict end n fn-octets fn-zin-win fn-zin-tab fn-zin-out)
  (declare (xargs :stobjs (fn-octets fn-zin-win fn-zin-tab fn-zin-out)
                  :guard (and (fn-cbor-octet-listp dict) (natp end) (natp n)
                              (<= end (fn-octets-len fn-octets)))))
  (if (and (zp n) (zp end))
      (let ((fn-zin-out (fn-zin-out-clear fn-zin-out)))
        (mv (list :ok nil) pool fn-zin-win fn-zin-tab fn-zin-out))
    (mv-let (st pool fn-zin-win fn-zin-tab fn-zin-out)
      (fn-zpl-payload-bufs pool (fn-pzd-budget end n) dict 0 end (+ 1 (nfix n)) fn-octets
                           fn-zin-win fn-zin-tab fn-zin-out)
      (mv (if (and (fn-pzd-endedp st) (equal (fn-zin-out-len fn-zin-out) (nfix n)))
              (list :ok)
            (list :error (if (fn-pzd-endedp st) :length st)))
          pool fn-zin-win fn-zin-tab fn-zin-out))))

(defthm fn-zpl-payload-bufs-is-payload-bufs
  (implies (and (fn-zpl-pool-okp pool fn-zin-win) (fn-cbor-octet-listp dict))
           (let ((p (fn-zpl-payload-bufs pool b dict start end lim fn-octets fn-zin-win fn-zin-tab
                                         fn-zin-out))
                 (q (fn-zin-payload-bufs b dict start end lim fn-octets fn-zin-win fn-zin-tab
                                         fn-zin-out)))
             (and (equal (car p) (car q))
                  (equal (mv-nth 2 p) (mv-nth 1 q))
                  (equal (mv-nth 3 p) (mv-nth 2 q))
                  (equal (mv-nth 4 p) (mv-nth 3 q)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-zin-payload-bufs)
                           (fn-zin-loop-ahead fn-zin-payload-ready fn-zpl-prepare
                            fn-zin-payload-bufs-ignores-buffers fn-zpl-pool-okp)))))

(local (defthm fn-zpl-reset-loop-below
  (implies (and (natp i) (natp j) (< j i))
           (equal (fn-zin-fld j (fn-zin-reset-loop i fn-zin-st)) (fn-zin-fld j fn-zin-st)))
  :hints (("Goal" :induct (fn-zin-reset-loop i fn-zin-st)))))
(local (defthm fn-zpl-reset-loop-fields
  (implies (and (natp i) (natp j) (<= i j) (< j 18))
           (equal (fn-zin-fld j (fn-zin-reset-loop i fn-zin-st)) 0))
  :hints (("Goal" :induct (fn-zin-reset-loop i fn-zin-st)))))
(local (defthm fn-zpl-start-posp
  (fn-zfr-posp (fn-zin-fld 5 (fn-zin-set 18 h (fn-zin-reset fn-zin-st)))
               (fn-zin-fld 6 (fn-zin-set 18 h (fn-zin-reset fn-zin-st))))
  :hints (("Goal" :in-theory (enable fn-zin-reset)))))
(local (defthm fn-zpl-loop-ahead-pool-okp
  (implies (and (fn-zfr-posp (fn-zin-fld 5 fn-zin-st) (fn-zin-fld 6 fn-zin-st))
                (fn-cbor-octet-listp dict)
                (fn-cbor-octet-listp fn-zin-tab) (equal (len fn-zin-tab) *fn-zin-tab-octets*)
                (fn-cbor-octet-listp fn-zin-out))
           (let ((r (fn-zin-loop-ahead b ip end lim fn-zin-st fn-octets (fn-zpl-ready-window dict)
                                       fn-zin-tab fn-zin-out)))
             (fn-zpl-pool-okp (list dict (fn-zpl-ready-h dict) (fn-zfr-dirty (fn-zin-fld 6 (mv-nth 3 r))))
                              (mv-nth 4 r))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-zfr-loop-ahead-frame (fn-zin-win (fn-zpl-ready-window dict))))
           :in-theory (disable fn-zin-loop-ahead fn-zfr-loop-ahead-frame fn-zpl-ready-window
                               fn-zpl-ready-h)))))
(local (defthm fn-zpl-loop-ahead-pool-okp-2
  (implies (and (fn-zfr-posp (fn-zin-fld 5 fn-zin-st) (fn-zin-fld 6 fn-zin-st))
                (fn-cbor-octet-listp dict)
                (fn-cbor-octet-listp fn-zin-tab) (equal (len fn-zin-tab) *fn-zin-tab-octets*)
                (fn-cbor-octet-listp fn-zin-out))
           (let ((r (fn-zin-loop-ahead b ip end lim fn-zin-st fn-octets
                                       (mv-nth 1 (fn-zin-payload-ready dict nil nil))
                                       fn-zin-tab fn-zin-out)))
             (fn-zpl-pool-okp (list dict (car (fn-zin-payload-ready dict nil nil))
                                    (fn-zfr-dirty (fn-zin-fld 6 (mv-nth 3 r))))
                              (mv-nth 4 r))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-zpl-loop-ahead-pool-okp))
           :in-theory (e/d (fn-zpl-ready-window fn-zpl-ready-h)
                           (fn-zin-loop-ahead fn-zpl-loop-ahead-pool-okp fn-zpl-pool-okp
                            fn-zin-payload-ready fn-zfr-dirty))))))
(defthm fn-zpl-payload-bufs-pool-okp
  (implies (and (fn-zpl-pool-okp pool fn-zin-win) (fn-cbor-octet-listp dict))
           (let ((p (fn-zpl-payload-bufs pool b dict start end lim fn-octets fn-zin-win fn-zin-tab
                                         fn-zin-out)))
             (fn-zpl-pool-okp (mv-nth 1 p) (mv-nth 2 p))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-zin-payload-ready-shape (fn-zin-win nil) (fn-zin-tab nil)))
           :in-theory (e/d ()
                           (fn-zin-loop-ahead fn-zin-payload-ready fn-zpl-prepare
                            fn-zin-payload-ready-shape fn-zpl-ready-tab-logic fn-zfr-dirty
                            fn-zpl-pool-okp fn-zin-reset)))))

(local (defthm fn-zpl-decode-bufs-is-pzd
  (implies (and (fn-zpl-pool-okp pool fn-zin-win) (fn-cbor-octet-listp dict)
                (fn-cbor-octet-listp c))
           (let ((r (fn-zpl-decode-bufs pool dict (len c) n c fn-zin-win fn-zin-tab fn-zin-out))
                 (q (fn-pzd-decode-bufs dict (len c) n c fn-zin-win fn-zin-tab fn-zin-out)))
             (and (equal (car r) (car q))
                  (equal (mv-nth 4 r) (mv-nth 3 q)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-zpl-payload-bufs-is-payload-bufs (b (fn-pzd-budget (len c) n)) (start 0)
                            (end (len c)) (lim (+ 1 (nfix n))) (fn-octets c))
                 (:instance fn-zin-payload-bufs-is-payload-with
                            (b (fn-pzd-budget (len c) n)) (lim (+ 1 (nfix n))))
                 (:instance fn-zin-payload-with-octets
                            (b (fn-pzd-budget (len c) n)) (lim (+ 1 (nfix n)))))
           :in-theory (e/d (fn-pzd-answer)
                           (fn-zpl-payload-bufs fn-zin-payload-bufs fn-zin-payload-with
                            fn-zpl-payload-bufs-is-payload-bufs fn-zin-payload-bufs-is-payload-with
                            fn-zin-payload-with-octets fn-zpl-pool-okp))))))

(local (defthm fn-zpl-decode-bufs-pool-okp
  (implies (and (fn-zpl-pool-okp pool fn-zin-win) (fn-cbor-octet-listp dict))
           (let ((r (fn-zpl-decode-bufs pool dict end n fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
             (fn-zpl-pool-okp (mv-nth 1 r) (mv-nth 2 r))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-zpl-payload-bufs-pool-okp (b (fn-pzd-budget end n)) (start 0)
                            (lim (+ 1 (nfix n)))))
           :in-theory (e/d (fn-zpl-decode-bufs)
                           (fn-zpl-payload-bufs-pool-okp fn-zpl-payload-bufs fn-zpl-pool-okp))))))
(defthm fn-zpl-decode-bufs-is-decode
  (implies (and (fn-cbor-octet-listp c) (natp n) (fn-cbor-octet-listp dict)
                (fn-zpl-pool-okp pool fn-zin-win))
           (let ((r (fn-zpl-decode-bufs pool dict (len c) n c fn-zin-win fn-zin-tab fn-zin-out))
                 (d (fn-pzd-decode dict c n)))
             (and (equal (car (car r)) (car d))
                  (implies (equal (car d) :ok)
                           (equal (mv-nth 4 r) (cadr d)))
                  (fn-zpl-pool-okp (mv-nth 1 r) (mv-nth 2 r)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-zpl-decode-bufs-is-pzd)
                 (:instance fn-pzd-decode-bufs-is-decode))
           :in-theory (disable fn-zpl-decode-bufs-is-pzd fn-pzd-decode-bufs-is-decode
                               fn-zpl-decode-bufs fn-pzd-decode-bufs fn-pzd-decode fn-zpl-pool-okp))))

; KEYSTONE (the served read's boundary, over a pool): an :ok answer leaves
; in the output buffer exactly the value A-DURABLE-LZ names.
(defthm fn-zpl-decode-bufs-is-the-lz-value
  (implies (and (fn-cbor-octet-listp c) (fn-cbor-octet-listp dict) (natp n)
                (fn-zpl-pool-okp pool fn-zin-win)
                (equal (car (car (fn-zpl-decode-bufs pool dict (len c) n c fn-zin-win fn-zin-tab
                                                     fn-zin-out)))
                       :ok))
           (equal (mv-nth 4 (fn-zpl-decode-bufs pool dict (len c) n c fn-zin-win fn-zin-tab
                                                fn-zin-out))
                  (fn-lzr-lz-value dict c n)))
  :hints (("Goal" :use ((:instance fn-zpl-decode-bufs-is-pzd)
                        (:instance fn-lzr-decode-bufs-is-the-lz-value))
           :in-theory (disable fn-zpl-decode-bufs-is-pzd fn-lzr-decode-bufs-is-the-lz-value
                               fn-zpl-decode-bufs fn-pzd-decode-bufs fn-zpl-pool-okp
                               fn-zpl-decode-bufs-is-decode))))

; The preset's length a pool records (what a witness checks the invariant's
; H against).
(defthm fn-zpl-ready-h-is
  (implies (fn-cbor-octet-listp dict)
           (equal (fn-zpl-ready-h dict) (min (len dict) *fn-zin-window*)))
  :hints (("Goal" :do-not-induct t
           :in-theory (set-difference-theories (enable fn-zin-payload-ready fn-zpl-ready-h)
                                               (executable-counterpart-theory :here)))))

; The host's starting pool satisfies the invariant.
(defthm fn-zpl-pool-okp-of-nil
  (fn-zpl-pool-okp nil fn-zin-win))
