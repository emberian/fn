; Source event counts for the actual selected buffer executives.
; All observer trace/MV cells are excluded from target allocation.
(in-package "ACL2")
(include-book "decoded-window-initial-buffer-trace")
(defun fn-pib-event-count (kind trace)
 (declare (xargs :guard t))
 (if (atom trace) 0
  (+ (if (and (consp (car trace)) (equal kind (caar trace))) 1 0) (fn-pib-event-count kind (cdr trace)))))
(defthm fn-pib-event-count-of-append
 (equal (fn-pib-event-count k (append a b))
        (+ (fn-pib-event-count k a) (fn-pib-event-count k b)))
 :hints (("Goal" :induct (append a b))))
(defthm fn-pib-clear-array-source-counts
 (let ((r (fn-pib-octets$c-clear c)))
  (and (equal (fn-pib-event-count :array-resize (cdr r)) 0)
       (equal (fn-pib-event-count :array-write (cdr r)) 0)
       (equal (fn-pib-event-count :fill-write (cdr r)) 1)))
 :hints (("Goal" :in-theory (enable fn-pib-octets$c-clear fn-pib-event-count))))
(defthm fn-pib-reserve-array-source-counts
 (let ((r (fn-pib-octets$c-reserve n c)))
  (and (equal (fn-pib-event-count :array-resize (cdr r))
              (if (<= n (fn-octets$c-buf-length c)) 0 1))
       (equal (fn-pib-event-count :array-write (cdr r)) 0)
       (equal (fn-pib-event-count :fill-write (cdr r)) 0)))
 :hints (("Goal" :in-theory (enable fn-pib-octets$c-reserve fn-pib-event-count))))
(defthm fn-pib-append-octet-array-source-counts
 (let ((r (fn-pib-octets$c-append-octet o c)))
  (and (equal (fn-pib-event-count :array-resize (cdr r))
              (if (< (fn-octets$c-fill c) (fn-octets$c-buf-length c)) 0 1))
       (equal (fn-pib-event-count :array-write (cdr r)) 1)
       (equal (fn-pib-event-count :fill-write (cdr r)) 1)))
 :hints (("Goal" :in-theory (enable fn-pib-octets$c-append-octet fn-pib-event-count))))
(defthm fn-pib-back-loop-array-source-counts
 (implies (and (natp src) (natp dst) (natp end) (< src dst))
  (let ((r (fn-pib-oct-back-loop src dst end c)))
   (and (equal (fn-pib-event-count :array-resize (cdr r)) 0)
        (equal (fn-pib-event-count :array-write (cdr r)) (nfix (- end dst)))
        (equal (fn-pib-event-count :fill-write (cdr r)) 0))))
 :hints (("Goal" :induct (fn-oct-back-loop src dst end c)
                 :in-theory (enable fn-pib-oct-back-loop fn-pib-event-count))))
(local (defthm fn-pib-append-octet-fill-unfolds
 (equal (fn-octets$c-fill (fn-octets$c-append-octet o c))
        (+ 1 (fn-octets$c-fill c)))
 :hints (("Goal" :in-theory (enable fn-octets$c-append-octet)))))
(defthm fn-pib-write-list-prefunded-array-source-counts
 (implies (and (natp (fn-octets$c-fill c))
               (<= (+ (fn-octets$c-fill c) (len xs)) (fn-octets$c-buf-length c)))
  (let ((r (fn-pib-oct-write-list xs c)))
   (and (equal (fn-pib-event-count :array-resize (cdr r)) 0)
        (equal (fn-pib-event-count :array-write (cdr r)) (len xs))
        (equal (fn-pib-event-count :fill-write (cdr r)) (len xs)))))
 :hints (("Goal" :induct (fn-oct-write-list xs c)
 :in-theory (e/d (fn-pib-oct-write-list fn-pib-event-count)
   (fn-octets$c-append-octet fn-pib-octets$c-append-octet fn-octets$c-fill fn-octets$c-buf-length)))))
(defthm fn-pib-append-back-prefunded-array-source-counts
 (implies (and (natp (fn-octets$c-fill c)) (natp off) (posp off)
               (<= off (fn-octets$c-fill c)) (natp n)
               (<= (+ (fn-octets$c-fill c) n) (fn-octets$c-buf-length c)))
  (let ((r (fn-pib-octets$c-append-back off n c)))
   (and (equal (fn-pib-event-count :array-resize (cdr r)) 0)
        (equal (fn-pib-event-count :array-write (cdr r)) n)
        (equal (fn-pib-event-count :fill-write (cdr r)) 1))))
 :hints (("Goal" :do-not '(preprocess)
 :use ((:instance fn-pib-back-loop-array-source-counts
        (src (- (fn-octets$c-fill c) off)) (dst (fn-octets$c-fill c))
        (end (+ (fn-octets$c-fill c) n)) (c c)))
 :in-theory (e/d (fn-pib-octets$c-append-back fn-pib-event-count)
    (fn-pib-oct-back-loop fn-octets$c-fill fn-octets$c-buf-length
     fn-pib-back-loop-array-source-counts fn-octets$c-bufi resize-fn-octets$c-buf update-fn-octets$c-fill)))))

(local (defthm fn-pibi-clear-capacity-and-fill
 (and (equal (fn-octets$c-buf-length (fn-octets$c-clear b)) (fn-octets$c-buf-length b))
      (equal (fn-octets$c-fill (fn-octets$c-clear b)) 0))
 :hints (("Goal" :in-theory (enable fn-octets$c-clear)))))
(local (defthm fn-pibi-reserve-capacity-and-fill
 (implies (natp n)
  (and (equal (fn-octets$c-buf-length (fn-octets$c-reserve n b))
              (max n (fn-octets$c-buf-length b)))
       (equal (fn-octets$c-fill (fn-octets$c-reserve n b)) (fn-octets$c-fill b))))
 :hints (("Goal" :in-theory (enable fn-octets$c-reserve)))))
(local (defthm fn-pibi-len-nthcdr
 (equal (len (nthcdr n xs)) (nfix (- (len xs) (nfix n))))
 :hints (("Goal" :induct (nthcdr n xs) :in-theory (enable nthcdr)))))

(local (defthm fn-pibi-append-octet-fill
 (equal (fn-octets$c-fill (fn-octets$c-append-octet o b))
        (+ 1 (fn-octets$c-fill b)))
 :hints (("Goal" :in-theory (enable fn-octets$c-append-octet)))))
(local (defthm fn-pibi-append-back-fill
 (equal (fn-octets$c-fill (fn-octets$c-append-back off n b))
        (+ n (fn-octets$c-fill b)))
 :hints (("Goal" :in-theory (e/d (fn-octets$c-append-back) (fn-oct-back-loop))))))
(local (defthm fn-pibi-write-list-fill
 (implies (acl2-numberp (fn-octets$c-fill b))
  (equal (fn-octets$c-fill (fn-oct-write-list xs b))
         (+ (len xs) (fn-octets$c-fill b))))
 :hints (("Goal" :induct (fn-oct-write-list xs b)
            :in-theory (e/d (fn-oct-write-list) (fn-octets$c-append-octet))))))

(local (defthm fn-pib-ready-prefix-capacity-and-fill
 (let ((b (fn-octets$c-append-back 1 32767
             (fn-octets$c-append-octet 0
               (fn-octets$c-reserve 65536 (fn-octets$c-clear c))))))
  (and (equal (fn-octets$c-fill b) 32768)
       (equal (fn-octets$c-buf-length b) (max 65536 (fn-octets$c-buf-length c)))))
 :hints (("Goal" :in-theory (disable fn-octets$c-clear fn-octets$c-reserve
   fn-octets$c-append-octet fn-octets$c-append-back fn-octets$c-fill fn-octets$c-buf-length)))))

(encapsulate ()
 (local (include-book "arithmetic-5/top" :dir :system))
 (defthm fn-pib-prefilled-dict-source-counts
 (let ((r (fn-pib-oct-write-list (if (< 32768 (len dict)) (nthcdr (- (len dict) 32768) dict) dict) (fn-octets$c-append-back 1 32767 (fn-octets$c-append-octet 0 (fn-octets$c-reserve 65536 (fn-octets$c-clear cwin)))))))
  (and (equal (fn-pib-event-count :array-resize (cdr r)) 0)
       (equal (fn-pib-event-count :array-write (cdr r)) (min (len dict) 32768))
       (equal (fn-pib-event-count :fill-write (cdr r)) (min (len dict) 32768))))
 :hints (("Goal" :do-not '(preprocess)
 :use ((:instance fn-pib-write-list-prefunded-array-source-counts (xs (if (< 32768 (len dict)) (nthcdr (- (len dict) 32768) dict) dict)) (c (fn-octets$c-append-back 1 32767 (fn-octets$c-append-octet 0 (fn-octets$c-reserve 65536 (fn-octets$c-clear cwin)))))))
 :in-theory (disable fn-pib-oct-write-list fn-pib-write-list-prefunded-array-source-counts
 fn-octets$c-clear fn-octets$c-reserve fn-octets$c-append-octet fn-octets$c-append-back
 fn-octets$c-fill fn-octets$c-buf-length nthcdr (:e fn-octets$c-append-back))))))

(encapsulate ()
 (local (include-book "arithmetic-5/top" :dir :system))
 (defthm fn-pib-prefilled-dict-capacity-and-fill
 (let ((b (fn-oct-write-list (if (< 32768 (len dict)) (nthcdr (- (len dict) 32768) dict) dict) (fn-octets$c-append-back 1 32767 (fn-octets$c-append-octet 0 (fn-octets$c-reserve 65536 (fn-octets$c-clear cwin)))))))
  (and (equal (fn-octets$c-fill b) (+ 32768 (min (len dict) 32768)))
       (equal (fn-octets$c-buf-length b) (max 65536 (fn-octets$c-buf-length cwin)))))
 :hints (("Goal" :do-not '(preprocess)
 :use ((:instance fn-piwc-write-list-keeps-funded-capacity (xs (if (< 32768 (len dict)) (nthcdr (- (len dict) 32768) dict) dict)) (fn-octets$c (fn-octets$c-append-back 1 32767 (fn-octets$c-append-octet 0 (fn-octets$c-reserve 65536 (fn-octets$c-clear cwin)))))))
 :in-theory (disable fn-piwc-write-list-keeps-funded-capacity fn-oct-write-list
 fn-octets$c-clear fn-octets$c-reserve fn-octets$c-append-octet fn-octets$c-append-back
 fn-octets$c-fill fn-octets$c-buf-length nthcdr (:e fn-octets$c-append-back))))))

(encapsulate ()
 (local (include-book "arithmetic-5/top" :dir :system))
 (defthm fn-pib-payload-ready-exact-array-source-roster
  (let* ((r (fn-pib-piwc-payload-ready dict cwin ctab)) (trace (cdr r))
         (h (min (len dict) 32768)))
   (and (equal (fn-pib-event-count :array-resize trace)
         (+ (if (<= 65536 (fn-octets$c-buf-length cwin)) 0 1)
            (if (<= 3494 (fn-octets$c-buf-length ctab)) 0 1)))
        (equal (fn-pib-event-count :array-write trace) 69030)
        (equal (fn-pib-event-count :fill-write trace)
               (+ 6 h (if (< h 32768) 2 0)))))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
   :use (fn-pib-prefilled-dict-source-counts fn-pib-prefilled-dict-capacity-and-fill)
   :in-theory (e/d (fn-pib-piwc-payload-ready fn-pib-event-count)
    (fn-pib-prefilled-dict-source-counts fn-pib-prefilled-dict-capacity-and-fill
     fn-pib-octets$c-clear fn-pib-octets$c-reserve fn-pib-octets$c-append-octet
     fn-pib-octets$c-append-back fn-pib-oct-write-list fn-pib-oct-back-loop
     fn-octets$c-clear fn-octets$c-reserve fn-octets$c-append-octet
     fn-octets$c-append-back fn-oct-write-list fn-oct-back-loop
     fn-octets$c-fill fn-octets$c-buf-length nthcdr (:e fn-octets$c-append-back)))))))
(defthm fn-pib-initialize-exact-array-source-roster
 (let* ((r (fn-pib-piwc-initialize dict zin cwin ctab cout)) (trace (cdr r))
        (h (min (len dict) 32768)))
  (and (equal (fn-pib-event-count :array-resize trace)
        (+ (if (<= 65536 (fn-octets$c-buf-length cwin)) 0 1)
           (if (<= 3494 (fn-octets$c-buf-length ctab)) 0 1)
           (if (<= 64 (fn-octets$c-buf-length cout)) 0 1)))
       (equal (fn-pib-event-count :array-write trace) 69030)
       (equal (fn-pib-event-count :fill-write trace) (+ 7 h (if (< h 32768) 2 0)))))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
 :use fn-pib-payload-ready-exact-array-source-roster
 :in-theory (e/d (fn-pib-piwc-initialize fn-pib-event-count)
    (fn-pib-piwc-payload-ready fn-piwc-payload-ready fn-octets$c-clear
     fn-octets$c-reserve fn-octets$c-buf-length fn-octets$c-fill
     fn-pib-octets$c-clear fn-pib-octets$c-reserve fn-zin-reset fn-zin-set)))))
(defthm fn-pib-ewz-begin-exact-array-source-roster
 (let* ((r (fn-pib-piwc-ewz-begin file eoff elen poff compressed decoded offset
                    ticket incarnation lease expected dict hash zin cwin ctab cout)) (trace (cdr r))
        (h (min (len dict) 32768)))
  (and (equal (fn-pib-event-count :array-resize trace)
        (+ (if (<= 65536 (fn-octets$c-buf-length cwin)) 0 1)
           (if (<= 3494 (fn-octets$c-buf-length ctab)) 0 1)
           (if (<= 64 (fn-octets$c-buf-length cout)) 0 1)))
       (equal (fn-pib-event-count :array-write trace) 69030)
       (equal (fn-pib-event-count :fill-write trace) (+ 7 h (if (< h 32768) 2 0)))))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
 :use fn-pib-initialize-exact-array-source-roster
 :in-theory (e/d (fn-pib-piwc-ewz-begin fn-pib-event-count)
    (fn-pib-piwc-initialize fn-piwc-initialize fn-ews-begin fn-ewz-state
     fn-pzd-budget fn-pzw-stored-admissiblep nfix natp nth fn-octets$c-clear
     fn-octets$c-reserve fn-octets$c-buf-length fn-octets$c-fill
     fn-pib-octets$c-clear fn-pib-octets$c-reserve fn-zin-reset fn-zin-set)))))
(defthm fn-pib-begin-exact-array-source-roster
 (let* ((r (fn-pib-piwc-begin token incarnation hash zin cwin ctab cout)) (trace (cdr r))
        (h (min (len (fn-pwz-dictionary token)) 32768)))
  (and (equal (fn-pib-event-count :array-resize trace)
        (+ (if (<= 65536 (fn-octets$c-buf-length cwin)) 0 1)
           (if (<= 3494 (fn-octets$c-buf-length ctab)) 0 1)
           (if (<= 64 (fn-octets$c-buf-length cout)) 0 1)))
       (equal (fn-pib-event-count :array-write trace) 69030)
       (equal (fn-pib-event-count :fill-write trace) (+ 7 h (if (< h 32768) 2 0)))))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
 :use ((:instance fn-pib-ewz-begin-exact-array-source-roster (dict (fn-pwz-dictionary token))
    (file (nfix (fn-pwz-nth 2 token))) (eoff (nfix (fn-pwz-nth 3 token)))
    (elen (nfix (fn-pwz-nth 4 token))) (poff (nfix (fn-pwz-nth 5 token)))
    (compressed (nfix (fn-pwz-nth 6 token))) (decoded (nfix (fn-pwz-nth 9 token)))
    (offset (nfix (fn-pwz-nth 7 token))) (ticket (fn-pwz-nth 1 token))
    (lease token) (expected (nfix (fn-pwz-nth 8 token)))))
 :in-theory (e/d (fn-pib-piwc-begin fn-pib-event-count)
    (fn-pib-piwc-ewz-begin fn-piwc-ewz-begin fn-pib-piwc-initialize fn-piwc-initialize fn-pwz-nth fn-pwz-dictionary
     fn-octets$c-buf-length fn-octets$c-fill fn-ews-begin fn-ewz-state
     fn-pzd-budget fn-pzw-stored-admissiblep nfix natp nth (:e fn-pwz-dictionary))))))
; Complete host-subject boundary: observer value is the actual selected
; executive composition, whose six outputs refine the actual host call.
(defthm fn-pib-actual-begin-array-source-boundary
 (implies (and (fn-octets$cp cwin) (fn-octets$cp ctab) (fn-octets$cp cout))
  (let* ((o (fn-pib-piwc-begin token incarnation hash zin cwin ctab cout))
         (rc (car o)) (trace (cdr o))
         (ra (fn-pwz-begin token incarnation hash zin awin atab aout))
         (h (min (len (fn-pwz-dictionary token)) 32768)))
   (and (equal (mv-nth 0 rc) (mv-nth 0 ra))
        (equal (mv-nth 1 rc) (mv-nth 1 ra))
        (equal (mv-nth 2 rc) (mv-nth 2 ra))
        (fn-octets$corr (mv-nth 3 rc) (mv-nth 3 ra))
        (fn-octets$corr (mv-nth 4 rc) (mv-nth 4 ra))
        (fn-octets$corr (mv-nth 5 rc) (mv-nth 5 ra))
        (equal (fn-pib-event-count :array-resize trace)
         (+ (if (<= 65536 (fn-octets$c-buf-length cwin)) 0 1)
            (if (<= 3494 (fn-octets$c-buf-length ctab)) 0 1)
            (if (<= 64 (fn-octets$c-buf-length cout)) 0 1)))
        (equal (fn-pib-event-count :array-write trace) 69030)
        (equal (fn-pib-event-count :fill-write trace) (+ 7 h (if (< h 32768) 2 0))))))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
 :use (fn-pib-begin-exact-array-source-roster
       (:instance fn-piwc-begin-refines-actual-begin-from-typed-arrays
         (pgs-digest-state hash) (fn-zin-st zin)))
 :in-theory (disable fn-pib-piwc-begin fn-piwc-begin fn-pwz-begin fn-pib-event-count
  fn-pwz-dictionary fn-octets$cp fn-octets$corr fn-octets$c-buf-length
  (:e fn-pib-piwc-begin) (:e fn-piwc-begin) (:e fn-pwz-begin) (:e fn-pwz-dictionary)))))
