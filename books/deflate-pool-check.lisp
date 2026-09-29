; fn: the pooled read's invariant, executable (lane compress-4, PRF-949's
; teeth).  Prefix `fn-zpl-' (books/deflate-pool.lisp's).
;
; `fn-zpl-pool-okp' is a defun-nx: its ready window is what
; `fn-zin-payload-ready' makes of fresh stobjs, which no executable call can
; name, so nothing ever EVALUATED the invariant on a pool the host entry
; returned.  `fn-zpl-pool-check' is its executable twin over the window
; stobj, and `fn-zpl-pool-check-is-pool-okp' equates the two, so a witness
; (tests/acl2/deflate-pool-tests.lisp) that runs the check on the pool and
; window `fn-zpl-decode-bufs' answered is a check of the invariant itself.
; It rests on `fn-zpl-ready-window-is-list': the ready window is the 32 KiB
; zero ring, the preset (the dictionary's last 32 KiB) and zeros after it.
;
; A test and diagnosis tool: no served path calls the check (the host keeps
; the pool the entry returns and never revalidates it).

(in-package "ACL2")
(include-book "deflate-pool")

(defun fn-zpl-preset (dict)
  ; The dictionary's last 32 KiB (all of it when shorter).
  (declare (xargs :guard (true-listp dict)))
  (let ((n (len dict)))
    (if (< *fn-zin-window* n) (nthcdr (- n *fn-zin-window*) dict) dict)))

(defun fn-zpl-ready-window-list (dict)
  (declare (xargs :guard (true-listp dict)))
  (let ((h (min (len dict) *fn-zin-window*)))
    (append (fn-zpl-zeros *fn-zin-window*)
            (fn-zpl-preset dict)
            (fn-zpl-zeros (- *fn-zin-window* h)))))

(defun fn-zpl-pool-check (pool fn-zin-win)
  ; `fn-zpl-pool-okp', executable.
  (declare (xargs :stobjs fn-zin-win :guard t))
  (or (atom pool)
      (and (consp (cdr pool)) (consp (cddr pool))
           (let ((dict (car pool)) (h (cadr pool)) (k (caddr pool))
                 (win (fn-zin-win-list fn-zin-win)))
             (and (fn-cbor-octet-listp dict)
                  (equal h (min (len dict) *fn-zin-window*))
                  (natp k) (<= k *fn-zin-window*)
                  (fn-cbor-octet-listp win)
                  (equal (len win) *fn-zin-win-octets*)
                  (equal (nthcdr k win) (nthcdr k (fn-zpl-ready-window-list dict))))))))

; -----------------------------------------------------------------------------
; The ready window, as a list.

(local (defun fn-zpl-c-ind (m n) (if (zp n) m (fn-zpl-c-ind (1+ m) (1- n)))))

(local (defthm fn-zpl-c-true-listp-zeros (true-listp (fn-zpl-zeros n))))
(local (defthm fn-zpl-c-len-zeros (equal (len (fn-zpl-zeros n)) (nfix n))))

(local (defun fn-zpl-c-ind2 (i n) (if (or (zp n) (zp i)) (list i n) (fn-zpl-c-ind2 (1- i) (1- n)))))
(local (defthm fn-zpl-c-nth-zeros
  (implies (< (nfix i) (nfix n)) (equal (nth i (fn-zpl-zeros n)) 0))
  :hints (("Goal" :induct (fn-zpl-c-ind2 i n) :in-theory (enable nth)))))
(local (defthm fn-zpl-c-nth-append-right
  (implies (and (natp j) (true-listp ys))
           (equal (nth (+ (len ys) j) (append ys zs)) (nth j zs)))
  :hints (("Goal" :induct (len ys) :in-theory (enable nth)))))
(local (defthm fn-zpl-c-last-of-zeros
  (implies (and (true-listp ys) (posp m))
           (equal (nth (+ -1 m (len ys)) (append ys (fn-zpl-zeros m))) 0))
  :hints (("Goal" :use ((:instance fn-zpl-c-nth-append-right (j (+ -1 m)) (zs (fn-zpl-zeros m))))
           :in-theory (disable fn-zpl-c-nth-append-right)))))

(local (defthm fn-zpl-c-zeros-append-0
  (equal (append (fn-zpl-zeros m) (list 0)) (fn-zpl-zeros (+ 1 (nfix m))))))
(local (defthm fn-zpl-c-snoc-zero
  (equal (append (append ys (fn-zpl-zeros m)) (list 0))
         (append ys (fn-zpl-zeros (+ 1 (nfix m)))))
  :hints (("Goal" :do-not-induct t :in-theory (disable fn-zpl-zeros (:e fn-zpl-zeros))))))

(local (defthm fn-zpl-c-back-copy-zeros
  (implies (and (true-listp ys) (posp m))
           (equal (fn-oct-back-copy 1 n (append ys (fn-zpl-zeros m)))
                  (append ys (fn-zpl-zeros (+ m (nfix n))))))
  :hints (("Goal" :induct (fn-zpl-c-ind m n)
           :expand ((fn-oct-back-copy 1 n (append ys (fn-zpl-zeros m))))
           :in-theory (disable fn-zpl-zeros (:e fn-zpl-zeros))))))

(local (defthm fn-zpl-c-zeros-of-zp (implies (zp n) (equal (fn-zpl-zeros n) nil))))

(local (defthm fn-zpl-c-back-copy-one-zero
  (equal (fn-oct-back-copy 1 n '(0)) (fn-zpl-zeros (+ 1 (nfix n))))
  :hints (("Goal" :use ((:instance fn-zpl-c-back-copy-zeros (ys nil) (m 1)))
           :in-theory (disable fn-zpl-c-back-copy-zeros (:e fn-zpl-zeros) (:e fn-oct-back-copy))
           :expand ((fn-zpl-zeros 1))))))

(local (defthm fn-zpl-c-back-copy-after-zero
  (implies (true-listp b)
           (equal (fn-oct-back-copy 1 n (append a b '(0)))
                  (append a b (fn-zpl-zeros (+ 1 (nfix n))))))
  :hints (("Goal" :use ((:instance fn-zpl-c-back-copy-zeros (ys (append a b)) (m 1)))
           :in-theory (disable fn-zpl-c-back-copy-zeros (:e fn-zpl-zeros) (:e fn-oct-back-copy))
           :expand ((fn-zpl-zeros 1))))))

(defthm fn-zpl-ready-window-is-list
  (implies (fn-cbor-octet-listp dict)
           (equal (fn-zpl-ready-window dict) (fn-zpl-ready-window-list dict)))
  :hints (("Goal" :do-not-induct t
           :in-theory (set-difference-theories
                       (enable fn-zin-payload-ready fn-zpl-ready-window)
                       '(fn-zpl-zeros (:e fn-zpl-zeros) (:e fn-oct-back-copy)
                         (:e fn-oct-snoc) (:e fn-octets$a-append-back) (:e fn-oct-cat)
                         (:e fn-zin-win-append-back) (:e fn-zin-tab-append-back))))))

; -----------------------------------------------------------------------------
; KEYSTONE: the check is the invariant.

(defthm fn-zpl-pool-check-is-pool-okp
  (equal (fn-zpl-pool-check pool fn-zin-win)
         (fn-zpl-pool-okp pool fn-zin-win))
  :hints (("Goal" :in-theory (e/d (fn-zpl-pool-okp fn-zpl-ready-h-is)
                                  (fn-zpl-ready-window-list)))))
