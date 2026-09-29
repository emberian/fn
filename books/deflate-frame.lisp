; fn: the payload decoder's window frame (lane compress-3, PRF-to-be-assigned).
; Prefix `fn-zfr-'.
;
; From a state whose ring position is its output count (below 32 KiB) or
; within the ring (past it), the payload decoder (fn-zin-loop-ahead) writes
; only ring cells below min(TOUT, 32 KiB) and never the preset half: the
; window's cells from that bound on are what they were
; (KEYSTONE `fn-zfr-loop-ahead-frame').  So a pooled window need only
; re-zero the cells the last payload dirtied.

(in-package "ACL2")
(include-book "deflate-inflate")

(defun fn-zfr-dirty (tout)
  (declare (xargs :guard t))
  (min (nfix tout) *fn-zin-window*))

(defun fn-zfr-posp (w tout)
  (declare (xargs :guard t))
  (and (natp w) (< w *fn-zin-window*)
       (implies (< (nfix tout) *fn-zin-window*) (equal w (nfix tout)))))

(local
 (defun fn-zfr-ind (i k x)
   (if (or (zp i) (zp k)) x (fn-zfr-ind (1- i) (1- k) (cdr x)))))

(local
 (defthm fn-zfr-nthcdr-of-update
   (implies (and (natp i) (natp k) (< i k))
            (equal (nthcdr k (fn-oct-update i o x)) (nthcdr k x)))
   :hints (("Goal" :in-theory (enable fn-oct-update)
            :induct (fn-zfr-ind i k x)
            :expand ((fn-oct-update i o x) (fn-oct-update 0 o x)
                     (nthcdr k x) (:free (a b) (nthcdr k (cons a b))))))))

; One write at the ring's next cell W, TOUT octets produced so far: the
; cells from min(TOUT + 1, 32 KiB) on are untouched.
(local
 (defthm fn-zfr-write
   (implies (and (fn-zfr-posp w tout) (natp tout) (natp k) (<= (fn-zfr-dirty t2) k)
                 (integerp t2) (< tout t2))
            (equal (nthcdr k (fn-oct-update w o x)) (nthcdr k x)))
   :hints (("Goal" :do-not-induct t :in-theory (disable fn-oct-update fn-zfr-nthcdr-of-update)
            :use ((:instance fn-zfr-nthcdr-of-update (i w)))))))

(local
 (defthm fn-zfr-posp-step
   (implies (and (fn-zfr-posp w tout) (natp tout))
            (and (fn-zfr-posp (fn-zin-wrap (+ 1 w)) (+ 1 tout))
                 (equal (fn-zin-wrap w) w)))
   :hints (("Goal" :in-theory (enable fn-zin-wrap$inline)))))

(local
 (defthm fn-zfr-posp-bounds
   (implies (fn-zfr-posp w tout)
            (and (natp w) (< w *fn-zin-window*)))
   :rule-classes :forward-chaining))

(local
 (defthm fn-zfr-posp-step-if
   (implies (and (fn-zfr-posp w tout) (natp tout))
            (fn-zfr-posp (if (< (+ 1 w) *fn-zin-window*) (+ 1 w) 0) (+ 1 tout)))))

(local
 (defthm fn-zfr-posp-step-split
   (implies (and (fn-zfr-posp w tout) (natp tout))
            (and (implies (< (+ 1 w) *fn-zin-window*) (fn-zfr-posp (+ 1 w) (+ 1 tout)))
                 (implies (<= *fn-zin-window* (+ 1 w)) (fn-zfr-posp 0 (+ 1 tout)))))))

(local
 (defthm fn-zfr-dirty-monotone
   (implies (<= (nfix a) (nfix b))
            (<= (fn-zfr-dirty a) (fn-zfr-dirty b)))
   :rule-classes :linear))

(local
 (defthm fn-zfr-dirty-below
   (implies (and (<= (fn-zfr-dirty b) k) (natp a) (natp b) (<= a b))
            (<= (fn-zfr-dirty a) k))
   :hints (("Goal" :in-theory (enable fn-zfr-dirty)))))

(local (in-theory (disable fn-zfr-posp fn-zfr-dirty)))

(defthm fn-zfr-copy-frame
  (implies (and (fn-zfr-posp w tout) (natp tout))
           (let ((r (fn-zin-copy k w d tout h fn-zin-win fn-zin-out)))
             (and (fn-zfr-posp (car r) (+ tout (nfix k)))
                  (implies (and (natp kk) (<= (fn-zfr-dirty (+ tout (nfix k))) kk))
                           (equal (nthcdr kk (mv-nth 1 r)) (nthcdr kk fn-zin-win))))))
  :hints (("Goal" :induct (fn-zin-copy k w d tout h fn-zin-win fn-zin-out)
           :in-theory (enable fn-zin-copy))))

(defthm fn-zfr-copy-pos
  (implies (and (fn-zfr-posp w tout) (natp tout) (equal t2 (+ tout (nfix k))))
           (fn-zfr-posp (car (fn-zin-copy k w d tout h fn-zin-win fn-zin-out)) t2))
  :hints (("Goal" :use fn-zfr-copy-frame :in-theory (disable fn-zfr-copy-frame))))

(defthm fn-zfr-copy-frame-2
  (implies (and (fn-zfr-posp w tout) (natp tout) (natp kk) (<= (fn-zfr-dirty t2) kk)
                (equal t2 (+ tout (nfix k))))
           (equal (nthcdr kk (mv-nth 1 (fn-zin-copy k w d tout h fn-zin-win fn-zin-out)))
                  (nthcdr kk fn-zin-win)))
  :hints (("Goal" :use fn-zfr-copy-frame :in-theory (disable fn-zfr-copy-frame))))

(defthm fn-zfr-lit-loop-pos
  (implies (and (fn-zfr-posp w tout) (natp tout))
           (let ((r (fn-zin-lit-loop k bits nbits w tout limit fn-zin-tab fn-zin-win fn-zin-out)))
             (and (fn-zfr-posp (mv-nth 2 r) (mv-nth 3 r))
                  (natp (mv-nth 3 r))
                  (<= tout (mv-nth 3 r))
                  (implies (not (equal (mv-nth 4 r) fn-zin-win)) (< tout (mv-nth 3 r))))))
  :hints (("Goal" :induct (fn-zin-lit-loop k bits nbits w tout limit fn-zin-tab fn-zin-win fn-zin-out)
           :in-theory (enable fn-zin-lit-loop))))

(defthm fn-zfr-lit-loop-tout-linear
  (implies (and (fn-zfr-posp w tout) (natp tout))
           (<= tout (mv-nth 3 (fn-zin-lit-loop k bits nbits w tout limit fn-zin-tab fn-zin-win
                                               fn-zin-out))))
  :rule-classes :linear)

(defthm fn-zfr-lit-loop-tout-natp
  (implies (natp tout)
           (natp (mv-nth 3 (fn-zin-lit-loop k bits nbits w tout limit fn-zin-tab fn-zin-win
                                            fn-zin-out))))
  :hints (("Goal" :in-theory (enable fn-zin-lit-loop)))
  :rule-classes :type-prescription)

(defthm fn-zfr-lit-loop-w
  (implies (and (fn-zfr-posp w tout) (natp tout))
           (natp (mv-nth 2 (fn-zin-lit-loop k bits nbits w tout limit fn-zin-tab fn-zin-win
                                            fn-zin-out))))
  :hints (("Goal" :use fn-zfr-lit-loop-pos :in-theory (disable fn-zfr-lit-loop-pos)))
  :rule-classes :type-prescription)

(defthm fn-zfr-lit-loop-frame
  (implies (and (fn-zfr-posp w tout) (natp tout) (natp kk)
                (<= (fn-zfr-dirty (mv-nth 3 (fn-zin-lit-loop k bits nbits w tout limit fn-zin-tab
                                                             fn-zin-win fn-zin-out)))
                    kk))
           (equal (nthcdr kk (mv-nth 4 (fn-zin-lit-loop k bits nbits w tout limit fn-zin-tab
                                                        fn-zin-win fn-zin-out)))
                  (nthcdr kk fn-zin-win)))
  :hints (("Goal" :induct (fn-zin-lit-loop k bits nbits w tout limit fn-zin-tab fn-zin-win fn-zin-out)
           :in-theory (enable fn-zin-lit-loop))))

(defthm fn-zfr-f-copy-pos
  (implies (and (fn-zfr-posp w tout) (natp tout) (natp k)
                (integerp d) (<= 1 d) (<= d *fn-zin-window*) (natp h) (<= h *fn-zin-window*))
           (fn-zfr-posp (car (fn-zin-f-copy k w d tout h fn-zin-win fn-zin-out)) (+ tout k)))
  :hints (("Goal" :induct (fn-zin-f-copy k w d tout h fn-zin-win fn-zin-out)
           :in-theory (enable fn-zin-f-copy))))

(defthm fn-zfr-f-copy-frame
  (implies (and (fn-zfr-posp w tout) (natp tout) (natp k)
                (integerp d) (<= 1 d) (<= d *fn-zin-window*) (natp h) (<= h *fn-zin-window*)
                (natp kk) (<= (fn-zfr-dirty (+ tout k)) kk))
           (equal (nthcdr kk (mv-nth 1 (fn-zin-f-copy k w d tout h fn-zin-win fn-zin-out)))
                  (nthcdr kk fn-zin-win)))
  :hints (("Goal" :induct (fn-zin-f-copy k w d tout h fn-zin-win fn-zin-out)
           :in-theory (enable fn-zin-f-copy))))

(defthm fn-zfr-f-sym-pos
  (implies (and (fn-zfr-posp w tout) (natp tout))
           (let ((r (fn-zin-f-sym bits nbits ip end w tout limit h fn-octets fn-zin-tab fn-zin-win
                                  fn-zin-out)))
             (and (fn-zfr-posp (mv-nth 4 r) (mv-nth 5 r))
                  (natp (mv-nth 5 r))
                  (<= tout (mv-nth 5 r)))))
  :hints (("Goal" :in-theory (enable fn-zin-f-sym) :do-not-induct t)))

(defthm fn-zfr-f-sym-tout
  (implies (and (fn-zfr-posp w tout) (natp tout))
           (let ((r (fn-zin-f-sym bits nbits ip end w tout limit h fn-octets fn-zin-tab fn-zin-win
                                  fn-zin-out)))
             (and (natp (mv-nth 5 r)) (<= tout (mv-nth 5 r)))))
  :rule-classes ((:linear :corollary
                  (implies (and (fn-zfr-posp w tout) (natp tout))
                           (<= tout (mv-nth 5 (fn-zin-f-sym bits nbits ip end w tout limit h fn-octets
                                                            fn-zin-tab fn-zin-win fn-zin-out)))))
                 (:type-prescription :corollary
                  (implies (and (fn-zfr-posp w tout) (natp tout))
                           (natp (mv-nth 5 (fn-zin-f-sym bits nbits ip end w tout limit h fn-octets
                                                         fn-zin-tab fn-zin-win fn-zin-out)))))))

(defthm fn-zfr-f-sym-frame
  (implies (and (fn-zfr-posp w tout) (natp tout) (natp kk)
                (<= (fn-zfr-dirty (mv-nth 5 (fn-zin-f-sym bits nbits ip end w tout limit h fn-octets
                                                          fn-zin-tab fn-zin-win fn-zin-out)))
                    kk))
           (equal (nthcdr kk (mv-nth 6 (fn-zin-f-sym bits nbits ip end w tout limit h fn-octets
                                                     fn-zin-tab fn-zin-win fn-zin-out)))
                  (nthcdr kk fn-zin-win)))
  :hints (("Goal" :in-theory (enable fn-zin-f-sym) :do-not-induct t)))

(defthm fn-zfr-fast-pos
  (implies (and (fn-zfr-posp w tout) (natp tout))
           (let ((r (fn-zin-fast k bits nbits ip end w tout limit h fn-octets fn-zin-tab fn-zin-win
                                 fn-zin-out)))
             (and (fn-zfr-posp (mv-nth 4 r) (mv-nth 5 r))
                  (natp (mv-nth 5 r))
                  (<= tout (mv-nth 5 r)))))
  :hints (("Goal" :induct (fn-zin-fast k bits nbits ip end w tout limit h fn-octets fn-zin-tab
                                       fn-zin-win fn-zin-out)
           :in-theory (enable fn-zin-fast))))

(defthm fn-zfr-fast-tout
  (implies (and (fn-zfr-posp w tout) (natp tout))
           (let ((r (fn-zin-fast k bits nbits ip end w tout limit h fn-octets fn-zin-tab fn-zin-win
                                 fn-zin-out)))
             (and (natp (mv-nth 5 r)) (<= tout (mv-nth 5 r)))))
  :rule-classes ((:linear :corollary
                  (implies (and (fn-zfr-posp w tout) (natp tout))
                           (<= tout (mv-nth 5 (fn-zin-fast k bits nbits ip end w tout limit h fn-octets
                                                           fn-zin-tab fn-zin-win fn-zin-out)))))
                 (:type-prescription :corollary
                  (implies (and (fn-zfr-posp w tout) (natp tout))
                           (natp (mv-nth 5 (fn-zin-fast k bits nbits ip end w tout limit h fn-octets
                                                        fn-zin-tab fn-zin-win fn-zin-out)))))))

(defthm fn-zfr-fast-w
  (implies (and (fn-zfr-posp w tout) (natp tout))
           (natp (mv-nth 4 (fn-zin-fast k bits nbits ip end w tout limit h fn-octets
                                        fn-zin-tab fn-zin-win fn-zin-out))))
  :hints (("Goal" :use fn-zfr-fast-pos :in-theory (disable fn-zfr-fast-pos)))
  :rule-classes :type-prescription)

(defthm fn-zfr-fast-frame
  (implies (and (fn-zfr-posp w tout) (natp tout) (natp kk)
                (<= (fn-zfr-dirty (mv-nth 5 (fn-zin-fast k bits nbits ip end w tout limit h fn-octets
                                                         fn-zin-tab fn-zin-win fn-zin-out)))
                    kk))
           (equal (nthcdr kk (mv-nth 6 (fn-zin-fast k bits nbits ip end w tout limit h fn-octets
                                                    fn-zin-tab fn-zin-win fn-zin-out)))
                  (nthcdr kk fn-zin-win)))
  :hints (("Goal" :induct (fn-zin-fast k bits nbits ip end w tout limit h fn-octets fn-zin-tab
                                       fn-zin-win fn-zin-out)
           :in-theory (enable fn-zin-fast))))

; A fast path that takes no symbol changes nothing it returns.
(local
 (defthm fn-zfr-f-sym-stop
   (implies (not (car (fn-zin-f-sym bits nbits ip end w tout limit h fn-octets fn-zin-tab
                                    fn-zin-win fn-zin-out)))
            (let ((r (fn-zin-f-sym bits nbits ip end w tout limit h fn-octets fn-zin-tab fn-zin-win
                                   fn-zin-out)))
              (and (equal (mv-nth 5 r) (nfix tout))
                   (equal (mv-nth 6 r) fn-zin-win))))
   :hints (("Goal" :in-theory (enable fn-zin-f-sym) :do-not-induct t))))

(local
 (defthm fn-zfr-fast-stop
   (implies (equal (car (fn-zin-fast k bits nbits ip end w tout limit h fn-octets fn-zin-tab
                                     fn-zin-win fn-zin-out))
                   (nfix k))
            (let ((r (fn-zin-fast k bits nbits ip end w tout limit h fn-octets fn-zin-tab fn-zin-win
                                  fn-zin-out)))
              (and (equal (mv-nth 5 r) (nfix tout))
                   (equal (mv-nth 6 r) fn-zin-win))))
   :hints (("Goal" :in-theory (enable fn-zin-fast) :expand ((:free (bits nbits ip w tout fn-zin-win fn-zin-out) (fn-zin-fast k bits nbits ip end w tout limit h fn-octets fn-zin-tab fn-zin-win fn-zin-out))) :do-not-induct t))))

(defthm fn-zfr-ahead-fast-pos
  (implies (fn-zfr-posp (fn-zin-fld 5 fn-zin-st) (fn-zin-fld 6 fn-zin-st))
           (let ((r (fn-zin-ahead-fast b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab
                                       fn-zin-out)))
             (and (fn-zfr-posp (fn-zin-fld 5 (mv-nth 2 r)) (fn-zin-fld 6 (mv-nth 2 r)))
                  (<= (fn-zin-fld 6 fn-zin-st) (fn-zin-fld 6 (mv-nth 2 r))))))
  :hints (("Goal" :in-theory (enable fn-zin-ahead-fast) :do-not-induct t)))

(defthm fn-zfr-ahead-fast-tout
  (implies (fn-zfr-posp (fn-zin-fld 5 fn-zin-st) (fn-zin-fld 6 fn-zin-st))
           (<= (fn-zin-fld 6 fn-zin-st)
               (fn-zin-fld 6 (mv-nth 2 (fn-zin-ahead-fast b ip end lim fn-zin-st fn-octets fn-zin-win
                                                          fn-zin-tab fn-zin-out)))))
  :rule-classes :linear)

(defthm fn-zfr-ahead-fast-frame
  (implies (and (fn-zfr-posp (fn-zin-fld 5 fn-zin-st) (fn-zin-fld 6 fn-zin-st)) (natp kk)
                (<= (fn-zfr-dirty (fn-zin-fld 6 (mv-nth 2 (fn-zin-ahead-fast b ip end lim fn-zin-st
                                                                            fn-octets fn-zin-win
                                                                            fn-zin-tab fn-zin-out))))
                    kk))
           (equal (nthcdr kk (mv-nth 3 (fn-zin-ahead-fast b ip end lim fn-zin-st fn-octets fn-zin-win
                                                          fn-zin-tab fn-zin-out)))
                  (nthcdr kk fn-zin-win)))
  :hints (("Goal" :in-theory (enable fn-zin-ahead-fast) :do-not-induct t)))

; The slow path's actions over the machine state: fields 5 (the ring's next
; cell) and 6 (octets produced).
(local
 (defthm fn-zfr-take-keeps
   (and (equal (fn-zin-fld 5 (mv-nth 1 (fn-zin-take n fn-zin-st))) (fn-zin-fld 5 fn-zin-st))
        (equal (fn-zin-fld 6 (mv-nth 1 (fn-zin-take n fn-zin-st))) (fn-zin-fld 6 fn-zin-st)))
   :hints (("Goal" :in-theory (enable fn-zin-take)))))

(local
 (defthm fn-zfr-decode-bit-keeps
   (and (equal (fn-zin-fld 5 (mv-nth 2 (fn-zin-decode-bit tb fn-zin-st fn-zin-tab)))
               (fn-zin-fld 5 fn-zin-st))
        (equal (fn-zin-fld 6 (mv-nth 2 (fn-zin-decode-bit tb fn-zin-st fn-zin-tab)))
               (fn-zin-fld 6 fn-zin-st)))
   :hints (("Goal" :in-theory (enable fn-zin-decode-bit)))))

(defmacro fn-zfr-st-lemmas (name call)
  ; CALL answers (mv _ fn-zin-st fn-zin-win ...).
  (let ((pos (intern-in-package-of-symbol (concatenate 'string "FN-ZFR-" (symbol-name name) "-POS") 'fn-zfr-dirty))
        (lin (intern-in-package-of-symbol (concatenate 'string "FN-ZFR-" (symbol-name name) "-TOUT") 'fn-zfr-dirty))
        (frm (intern-in-package-of-symbol (concatenate 'string "FN-ZFR-" (symbol-name name) "-FRAME") 'fn-zfr-dirty))
        (fn (intern-in-package-of-symbol (concatenate 'string "FN-ZIN-" (symbol-name name)) 'fn-zfr-dirty)))
    `(progn
       (defthm ,pos
         (implies (fn-zfr-posp (fn-zin-fld 5 fn-zin-st) (fn-zin-fld 6 fn-zin-st))
                  (and (fn-zfr-posp (fn-zin-fld 5 (mv-nth 1 ,call)) (fn-zin-fld 6 (mv-nth 1 ,call)))
                       (<= (fn-zin-fld 6 fn-zin-st) (fn-zin-fld 6 (mv-nth 1 ,call)))))
         :hints (("Goal" :in-theory (enable ,fn) :do-not-induct t)))
       (defthm ,lin
         (implies (fn-zfr-posp (fn-zin-fld 5 fn-zin-st) (fn-zin-fld 6 fn-zin-st))
                  (<= (fn-zin-fld 6 fn-zin-st) (fn-zin-fld 6 (mv-nth 1 ,call))))
         :hints (("Goal" :use ,pos :in-theory (theory 'minimal-theory)))
         :rule-classes :linear)
       (defthm ,frm
         (implies (and (fn-zfr-posp (fn-zin-fld 5 fn-zin-st) (fn-zin-fld 6 fn-zin-st)) (natp kk)
                       (<= (fn-zfr-dirty (fn-zin-fld 6 (mv-nth 1 ,call))) kk))
                  (equal (nthcdr kk (mv-nth 2 ,call)) (nthcdr kk fn-zin-win)))
         :hints (("Goal" :in-theory (enable ,fn) :do-not-induct t))))))

(fn-zfr-st-lemmas emit (fn-zin-emit o fn-zin-st fn-zin-win fn-zin-out))
(fn-zfr-st-lemmas match (fn-zin-match room fn-zin-st fn-zin-win fn-zin-out))
(fn-zfr-st-lemmas lits (fn-zin-lits room fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))
(fn-zfr-st-lemmas act (fn-zin-act fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))
(local (in-theory (disable fn-zin-match-counts fn-zin-lits-counts fn-zin-act-counts
                           fn-zin-match-out-free fn-zin-lits-out-free)))
(fn-zfr-st-lemmas step (fn-zin-step room fn-zin-st fn-zin-win fn-zin-tab fn-zin-out))

(local
 (defthm fn-zfr-pull-keeps
   (and (equal (fn-zin-fld 5 (fn-zin-pull ip fn-zin-st fn-octets)) (fn-zin-fld 5 fn-zin-st))
        (equal (fn-zin-fld 6 (fn-zin-pull ip fn-zin-st fn-octets)) (fn-zin-fld 6 fn-zin-st)))
   :hints (("Goal" :in-theory (enable fn-zin-pull)))))

(local
 (defthm fn-zfr-loop-ahead-pos
   (implies (fn-zfr-posp (fn-zin-fld 5 fn-zin-st) (fn-zin-fld 6 fn-zin-st))
            (let ((r (fn-zin-loop-ahead b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab
                                        fn-zin-out)))
              (and (fn-zfr-posp (fn-zin-fld 5 (mv-nth 3 r)) (fn-zin-fld 6 (mv-nth 3 r)))
                   (<= (fn-zin-fld 6 fn-zin-st) (fn-zin-fld 6 (mv-nth 3 r))))))
   :hints (("Goal" :induct (fn-zin-loop-ahead b ip end lim fn-zin-st fn-octets fn-zin-win
                                              fn-zin-tab fn-zin-out)
            :in-theory (e/d (fn-zin-loop-ahead) (fn-zin-pull fn-zin-step-counts))))))

(local
 (defthm fn-zfr-loop-ahead-tout
   (implies (fn-zfr-posp (fn-zin-fld 5 fn-zin-st) (fn-zin-fld 6 fn-zin-st))
            (<= (fn-zin-fld 6 fn-zin-st)
                (fn-zin-fld 6 (mv-nth 3 (fn-zin-loop-ahead b ip end lim fn-zin-st fn-octets
                                                           fn-zin-win fn-zin-tab fn-zin-out)))))
   :hints (("Goal" :use fn-zfr-loop-ahead-pos :in-theory (theory 'minimal-theory)))
   :rule-classes :linear))

(local
 (defthm fn-zfr-loop-ahead-frame-kk
   (implies (and (fn-zfr-posp (fn-zin-fld 5 fn-zin-st) (fn-zin-fld 6 fn-zin-st)) (natp kk)
                 (<= (fn-zfr-dirty (fn-zin-fld 6 (mv-nth 3 (fn-zin-loop-ahead b ip end lim fn-zin-st
                                                                              fn-octets fn-zin-win
                                                                              fn-zin-tab fn-zin-out))))
                     kk))
            (equal (nthcdr kk (mv-nth 4 (fn-zin-loop-ahead b ip end lim fn-zin-st fn-octets fn-zin-win
                                                           fn-zin-tab fn-zin-out)))
                   (nthcdr kk fn-zin-win)))
   :hints (("Goal" :induct (fn-zin-loop-ahead b ip end lim fn-zin-st fn-octets fn-zin-win
                                              fn-zin-tab fn-zin-out)
            :in-theory (e/d (fn-zin-loop-ahead) (fn-zin-pull fn-zin-step-counts))))))

; KEYSTONE (the window frame).
(defthm fn-zfr-loop-ahead-frame
  (implies (fn-zfr-posp (fn-zin-wpos fn-zin-st) (fn-zin-tout fn-zin-st))
    (let ((r (fn-zin-loop-ahead b ip end lim fn-zin-st fn-octets fn-zin-win fn-zin-tab fn-zin-out)))
      (and (fn-zfr-posp (fn-zin-wpos (mv-nth 3 r)) (fn-zin-tout (mv-nth 3 r)))
           (<= (fn-zin-tout fn-zin-st) (fn-zin-tout (mv-nth 3 r)))
           (equal (nthcdr (fn-zfr-dirty (fn-zin-tout (mv-nth 3 r))) (mv-nth 4 r))
                  (nthcdr (fn-zfr-dirty (fn-zin-tout (mv-nth 3 r))) fn-zin-win)))))
  :hints (("Goal" :in-theory (disable fn-zin-loop-ahead))))
