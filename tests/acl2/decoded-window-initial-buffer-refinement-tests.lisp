(in-package "ACL2")
(include-book "../../books/decoded-window-initial-buffer-refinement")

(local (defthm piwct-clear-capacity-and-fill
 (and (equal (fn-octets$c-buf-length (fn-octets$c-clear b)) (fn-octets$c-buf-length b))
      (equal (fn-octets$c-fill (fn-octets$c-clear b)) 0))
 :hints (("Goal" :in-theory (enable fn-octets$c-clear)))))
(local (defthm piwct-reserve-capacity-and-fill
 (implies (natp n)
  (and (equal (fn-octets$c-buf-length (fn-octets$c-reserve n b))
              (max n (fn-octets$c-buf-length b)))
       (equal (fn-octets$c-fill (fn-octets$c-reserve n b)) (fn-octets$c-fill b))))
 :hints (("Goal" :in-theory (enable fn-octets$c-reserve)))))
(local (defthm piwct-len-nthcdr
 (equal (len (nthcdr n xs)) (nfix (- (len xs) (nfix n))))
 :hints (("Goal" :induct (nthcdr n xs) :in-theory (enable nthcdr)))))

(local (defthm piwct-append-octet-fill
 (equal (fn-octets$c-fill (fn-octets$c-append-octet o b))
        (+ 1 (fn-octets$c-fill b)))
 :hints (("Goal" :in-theory (enable fn-octets$c-append-octet)))))
(local (defthm piwct-append-back-fill
 (equal (fn-octets$c-fill (fn-octets$c-append-back off n b))
        (+ n (fn-octets$c-fill b)))
 :hints (("Goal" :in-theory (e/d (fn-octets$c-append-back) (fn-oct-back-loop))))))
(local (defthm piwct-write-list-fill
 (implies (acl2-numberp (fn-octets$c-fill b))
  (equal (fn-octets$c-fill (fn-oct-write-list xs b))
         (+ (len xs) (fn-octets$c-fill b))))
 :hints (("Goal" :induct (fn-oct-write-list xs b)
            :in-theory (e/d (fn-oct-write-list) (fn-octets$c-append-octet))))))


(local (defthm piwc-back-loop-keeps-tail
 (implies (and (natp i) (<= end i))
  (equal (fn-octets$c-bufi i (fn-oct-back-loop src dst end c))
         (fn-octets$c-bufi i c)))
 :hints (("Goal" :induct (fn-oct-back-loop src dst end c)
                 :in-theory (enable fn-oct-back-loop fn-octets$c-bufi)))))
(local (defthm piwc-bufi-of-update-fill
 (equal (fn-octets$c-bufi i (update-fn-octets$c-fill n c)) (fn-octets$c-bufi i c))
 :hints (("Goal" :in-theory (enable fn-octets$c-bufi)))))
(local (defthm piwc-append-back-keeps-tail
 (implies (and (natp i) (natp n) (natp (fn-octets$c-fill c))
              (<= (+ (fn-octets$c-fill c) n) i)
              (<= (+ (fn-octets$c-fill c) n) (fn-octets$c-buf-length c)))
  (equal (fn-octets$c-bufi i (fn-octets$c-append-back off n c))
         (fn-octets$c-bufi i c)))
 :hints (("Goal" :use ((:instance piwc-back-loop-keeps-tail
        (src (- (fn-octets$c-fill c) off)) (dst (fn-octets$c-fill c))
        (end (+ (fn-octets$c-fill c) n))))
 :in-theory (e/d (fn-octets$c-append-back)
              (fn-oct-back-loop fn-octets$c-bufi update-fn-octets$c-fill piwc-back-loop-keeps-tail))))))
(local (defthm piwc-append-octet-keeps-tail
 (implies (and (natp i) (natp (fn-octets$c-fill c))
              (< (fn-octets$c-fill c) (fn-octets$c-buf-length c))
              (< (fn-octets$c-fill c) i))
  (equal (fn-octets$c-bufi i (fn-octets$c-append-octet o c))
         (fn-octets$c-bufi i c)))
 :hints (("Goal" :in-theory (enable fn-octets$c-append-octet fn-octets$c-bufi)))))
(local (defthm piwc-write-list-keeps-tail
 (implies (and (natp i) (natp (fn-octets$c-fill c))
              (<= (+ (fn-octets$c-fill c) (len xs)) i)
              (<= (+ (fn-octets$c-fill c) (len xs)) (fn-octets$c-buf-length c)))
  (equal (fn-octets$c-bufi i (fn-oct-write-list xs c))
         (fn-octets$c-bufi i c)))
 :hints (("Goal" :induct (fn-oct-write-list xs c)
 :in-theory (e/d (fn-oct-write-list) (fn-octets$c-append-octet fn-octets$c-bufi fn-octets$c-buf-length fn-octets$c-fill))))))
(local (defthm piwc-clear-keeps-tail
 (equal (fn-octets$c-bufi i (fn-octets$c-clear c)) (fn-octets$c-bufi i c))
 :hints (("Goal" :in-theory (e/d (fn-octets$c-clear) (update-fn-octets$c-fill fn-octets$c-bufi))))))
(local (defthm piwc-reserve-is-unchanged
 (implies (<= n (fn-octets$c-buf-length c)) (equal (fn-octets$c-reserve n c) c))
 :hints (("Goal" :in-theory (enable fn-octets$c-reserve)))))
(encapsulate ()
 (local (include-book "arithmetic-5/top" :dir :system))
 (defthm piwc-payload-ready-keeps-unused-tail
 (let ((r (fn-piwc-payload-ready dict cwin ctab)))
  (and (implies (and (natp i) (<= 65536 i) (< i (fn-octets$c-buf-length cwin)))
        (equal (fn-octets$c-bufi i (mv-nth 1 r)) (fn-octets$c-bufi i cwin)))
       (implies (and (natp i) (<= 3494 i) (< i (fn-octets$c-buf-length ctab)))
        (equal (fn-octets$c-bufi i (mv-nth 2 r)) (fn-octets$c-bufi i ctab)))))
 :hints (("Goal" :do-not '(preprocess)
 :in-theory (e/d (fn-piwc-payload-ready)
   (fn-octets$c-bufi fn-octets$c-buf-length fn-octets$c-fill fn-octets$c-clear
    fn-octets$c-reserve fn-octets$c-append-octet fn-octets$c-append-back
    fn-oct-write-list fn-oct-back-loop nthcdr (:e fn-octets$c-append-back)))))))
(local (defthm piwc-begin-keeps-unused-tail
 (let ((r (fn-piwc-begin token incarnation hash zin cwin ctab cout)))
  (and (implies (and (natp i) (<= 65536 i) (< i (fn-octets$c-buf-length cwin)))
        (equal (fn-octets$c-bufi i (mv-nth 3 r)) (fn-octets$c-bufi i cwin)))
       (implies (and (natp i) (<= 3494 i) (< i (fn-octets$c-buf-length ctab)))
        (equal (fn-octets$c-bufi i (mv-nth 4 r)) (fn-octets$c-bufi i ctab)))
       (implies (and (natp i) (<= 64 i) (< i (fn-octets$c-buf-length cout)))
        (equal (fn-octets$c-bufi i (mv-nth 5 r)) (fn-octets$c-bufi i cout)))))
 :hints (("Goal" :do-not '(preprocess)
 :use ((:instance piwc-payload-ready-keeps-unused-tail (dict (fn-pwz-dictionary token))))
 :in-theory (e/d (fn-piwc-begin fn-piwc-ewz-begin fn-piwc-initialize)
   (fn-piwc-payload-ready piwc-payload-ready-keeps-unused-tail
    fn-octets$c-bufi fn-octets$c-buf-length fn-octets$c-fill fn-octets$c-clear
    fn-octets$c-reserve fn-pwz-dictionary fn-pwz-nth fn-zin-reset fn-zin-set
    fn-ews-begin fn-ewz-state fn-pzd-budget fn-pzw-stored-admissiblep nfix nth natp
    (:e fn-pwz-dictionary)))))))
(local (defthm piwc-corr-implies-all-capacity-cells-typed
 (implies (and (fn-octets$corr c a) (natp i) (< i (fn-octets$c-buf-length c)))
          (fn-cbor-octetp (fn-octets$c-bufi i c)))
 :hints (("Goal" :in-theory (enable fn-octets$corr fn-octets$cp
                   fn-octets$c-buf-length fn-octets$c-bufi)))))
(local (defthm piwc-cp-implies-all-capacity-cells-typed
 (implies (and (fn-octets$cp c) (natp i) (< i (fn-octets$c-buf-length c)))
          (fn-cbor-octetp (fn-octets$c-bufi i c)))
 :hints (("Goal" :in-theory (enable fn-octets$cp fn-octets$c-buf-length fn-octets$c-bufi)))))
(defmacro piwc-full-refinement-conclusion (token hash zin cw ct co aw at ao)
 `(let ((rc (fn-piwc-begin ,token 301 ,hash ,zin ,cw ,ct ,co))
        (ra (fn-pwz-begin ,token 301 ,hash ,zin ,aw ,at ,ao)))
  (and (equal (mv-nth 0 rc) (mv-nth 0 ra))
       (equal (mv-nth 1 rc) (mv-nth 1 ra))
       (equal (mv-nth 2 rc) (mv-nth 2 ra))
       (fn-octets$corr (mv-nth 3 rc) (mv-nth 3 ra))
       (fn-octets$corr (mv-nth 4 rc) (mv-nth 4 ra))
       (fn-octets$corr (mv-nth 5 rc) (mv-nth 5 ra)))))
(defthm piwc-literal-complete-refinement-positive
 (let ((token '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 0))
       (h (create-pgs-digest-state)) (z (create-fn-zin-st))
       (c (create-fn-octets$c)))
  (and (fn-pwz-tokenp token) (fn-octets$cp c) (fn-octets$cp c) (fn-octets$cp c)
       (not (fn-octets$corr c '(256)))
       (piwc-full-refinement-conclusion token h z c c c '(256) '(256) '(256))))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
 :use ((:instance fn-piwc-begin-refines-actual-begin-from-typed-arrays
 (token '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 0)) (incarnation 301)
 (pgs-digest-state (create-pgs-digest-state)) (fn-zin-st (create-fn-zin-st))
 (cwin (create-fn-octets$c)) (ctab (create-fn-octets$c)) (cout (create-fn-octets$c))
 (awin '(256)) (atab '(256)) (aout '(256))))
 :in-theory (disable fn-piwc-begin fn-pwz-begin (:e fn-piwc-begin) (:e fn-pwz-begin)))))

; Corrupted-state removal: a non-octet survives beyond the new fill.
(defthm piwc-literal-remove-typed-window-array
 (let* ((token '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 0))
        (h (create-pgs-digest-state)) (z (create-fn-zin-st))
        (cwin (update-fn-octets$c-bufi 65536 300 (resize-fn-octets$c-buf 65537 (create-fn-octets$c)))) (ctab (create-fn-octets$c)) (cout (create-fn-octets$c)))
  (and (not (fn-octets$cp cwin)) (fn-octets$cp ctab) (fn-octets$cp cout)
       (not (piwc-full-refinement-conclusion token h z cwin ctab cout nil nil nil))))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
 :use ((:instance piwc-begin-keeps-unused-tail
    (token '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 0))
    (incarnation 301) (hash (create-pgs-digest-state)) (zin (create-fn-zin-st))
    (cwin (update-fn-octets$c-bufi 65536 300 (resize-fn-octets$c-buf 65537 (create-fn-octets$c)))) (ctab (create-fn-octets$c)) (cout (create-fn-octets$c)) (i 65536))
   (:instance fn-piwc-begin-keeps-initial-capacities
    (token '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 0))
    (incarnation 301) (pgs-digest-state (create-pgs-digest-state)) (fn-zin-st (create-fn-zin-st))
    (cwin (update-fn-octets$c-bufi 65536 300 (resize-fn-octets$c-buf 65537 (create-fn-octets$c)))) (ctab (create-fn-octets$c)) (cout (create-fn-octets$c)))
   (:instance piwc-cp-implies-all-capacity-cells-typed (c (update-fn-octets$c-bufi 65536 300 (resize-fn-octets$c-buf 65537 (create-fn-octets$c)))) (i 65536))
   (:instance piwc-corr-implies-all-capacity-cells-typed
    (i 65536) (a (mv-nth 3 (fn-pwz-begin '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 0) 301
       (create-pgs-digest-state) (create-fn-zin-st) nil nil nil)))
    (c (mv-nth 3 (fn-piwc-begin '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 0) 301
       (create-pgs-digest-state) (create-fn-zin-st) (update-fn-octets$c-bufi 65536 300 (resize-fn-octets$c-buf 65537 (create-fn-octets$c))) (create-fn-octets$c) (create-fn-octets$c))))))
 :in-theory (disable fn-piwc-begin fn-pwz-begin fn-octets$corr fn-octets$cp
  (:e fn-piwc-begin) (:e fn-pwz-begin)
  piwc-begin-keeps-unused-tail piwc-corr-implies-all-capacity-cells-typed
  piwc-cp-implies-all-capacity-cells-typed))))

; Corrupted-state removal: a non-octet survives beyond the new fill.
(defthm piwc-literal-remove-typed-table-array
 (let* ((token '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 0))
        (h (create-pgs-digest-state)) (z (create-fn-zin-st))
        (cwin (create-fn-octets$c)) (ctab (update-fn-octets$c-bufi 3494 300 (resize-fn-octets$c-buf 3495 (create-fn-octets$c)))) (cout (create-fn-octets$c)))
  (and (fn-octets$cp cwin) (not (fn-octets$cp ctab)) (fn-octets$cp cout)
       (not (piwc-full-refinement-conclusion token h z cwin ctab cout nil nil nil))))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
 :use ((:instance piwc-begin-keeps-unused-tail
    (token '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 0))
    (incarnation 301) (hash (create-pgs-digest-state)) (zin (create-fn-zin-st))
    (cwin (create-fn-octets$c)) (ctab (update-fn-octets$c-bufi 3494 300 (resize-fn-octets$c-buf 3495 (create-fn-octets$c)))) (cout (create-fn-octets$c)) (i 3494))
   (:instance fn-piwc-begin-keeps-initial-capacities
    (token '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 0))
    (incarnation 301) (pgs-digest-state (create-pgs-digest-state)) (fn-zin-st (create-fn-zin-st))
    (cwin (create-fn-octets$c)) (ctab (update-fn-octets$c-bufi 3494 300 (resize-fn-octets$c-buf 3495 (create-fn-octets$c)))) (cout (create-fn-octets$c)))
   (:instance piwc-cp-implies-all-capacity-cells-typed (c (update-fn-octets$c-bufi 3494 300 (resize-fn-octets$c-buf 3495 (create-fn-octets$c)))) (i 3494))
   (:instance piwc-corr-implies-all-capacity-cells-typed
    (i 3494) (a (mv-nth 4 (fn-pwz-begin '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 0) 301
       (create-pgs-digest-state) (create-fn-zin-st) nil nil nil)))
    (c (mv-nth 4 (fn-piwc-begin '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 0) 301
       (create-pgs-digest-state) (create-fn-zin-st) (create-fn-octets$c) (update-fn-octets$c-bufi 3494 300 (resize-fn-octets$c-buf 3495 (create-fn-octets$c))) (create-fn-octets$c))))))
 :in-theory (disable fn-piwc-begin fn-pwz-begin fn-octets$corr fn-octets$cp
  (:e fn-piwc-begin) (:e fn-pwz-begin)
  piwc-begin-keeps-unused-tail piwc-corr-implies-all-capacity-cells-typed
  piwc-cp-implies-all-capacity-cells-typed))))

; Corrupted-state removal: a non-octet survives beyond the new fill.
(defthm piwc-literal-remove-typed-output-array
 (let* ((token '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 0))
        (h (create-pgs-digest-state)) (z (create-fn-zin-st))
        (cwin (create-fn-octets$c)) (ctab (create-fn-octets$c)) (cout (update-fn-octets$c-bufi 64 300 (resize-fn-octets$c-buf 65 (create-fn-octets$c)))))
  (and (fn-octets$cp cwin) (fn-octets$cp ctab) (not (fn-octets$cp cout))
       (not (piwc-full-refinement-conclusion token h z cwin ctab cout nil nil nil))))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
 :use ((:instance piwc-begin-keeps-unused-tail
    (token '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 0))
    (incarnation 301) (hash (create-pgs-digest-state)) (zin (create-fn-zin-st))
    (cwin (create-fn-octets$c)) (ctab (create-fn-octets$c)) (cout (update-fn-octets$c-bufi 64 300 (resize-fn-octets$c-buf 65 (create-fn-octets$c)))) (i 64))
   (:instance fn-piwc-begin-keeps-initial-capacities
    (token '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 0))
    (incarnation 301) (pgs-digest-state (create-pgs-digest-state)) (fn-zin-st (create-fn-zin-st))
    (cwin (create-fn-octets$c)) (ctab (create-fn-octets$c)) (cout (update-fn-octets$c-bufi 64 300 (resize-fn-octets$c-buf 65 (create-fn-octets$c)))))
   (:instance piwc-cp-implies-all-capacity-cells-typed (c (update-fn-octets$c-bufi 64 300 (resize-fn-octets$c-buf 65 (create-fn-octets$c)))) (i 64))
   (:instance piwc-corr-implies-all-capacity-cells-typed
    (i 64) (a (mv-nth 5 (fn-pwz-begin '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 0) 301
       (create-pgs-digest-state) (create-fn-zin-st) nil nil nil)))
    (c (mv-nth 5 (fn-piwc-begin '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 0) 301
       (create-pgs-digest-state) (create-fn-zin-st) (create-fn-octets$c) (create-fn-octets$c) (update-fn-octets$c-bufi 64 300 (resize-fn-octets$c-buf 65 (create-fn-octets$c))))))))
 :in-theory (disable fn-piwc-begin fn-pwz-begin fn-octets$corr fn-octets$cp
  (:e fn-piwc-begin) (:e fn-pwz-begin)
  piwc-begin-keeps-unused-tail piwc-corr-implies-all-capacity-cells-typed
  piwc-cp-implies-all-capacity-cells-typed))))
; Complete unconditional capacity theorem at actual selected begin composition.
; Larger previously allocated buffers are retained; no shrink tariff is asserted.
(defthm piwc-literal-complete-retained-capacities-positive
 (let* ((cw (resize-fn-octets$c-buf 70000 (create-fn-octets$c)))
        (ct (resize-fn-octets$c-buf 4000 (create-fn-octets$c)))
        (co (resize-fn-octets$c-buf 128 (create-fn-octets$c)))
        (r (fn-piwc-begin '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 0)
              301 (create-pgs-digest-state) (create-fn-zin-st) cw ct co)))
  (and (equal (fn-octets$c-buf-length (mv-nth 3 r))
              (max 65536 (fn-octets$c-buf-length cw)))
       (equal (fn-octets$c-fill (mv-nth 3 r)) 65536)
       (equal (fn-octets$c-buf-length (mv-nth 4 r))
              (max 3494 (fn-octets$c-buf-length ct)))
       (equal (fn-octets$c-fill (mv-nth 4 r)) 3494)
       (equal (fn-octets$c-buf-length (mv-nth 5 r))
              (max 64 (fn-octets$c-buf-length co)))
       (equal (fn-octets$c-fill (mv-nth 5 r)) 0)
       (equal (fn-octets$c-buf-length (mv-nth 3 r)) 70000)
       (equal (fn-octets$c-buf-length (mv-nth 4 r)) 4000)
       (equal (fn-octets$c-buf-length (mv-nth 5 r)) 128)))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
 :use ((:instance fn-piwc-begin-keeps-initial-capacities
   (token '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 0)) (incarnation 301)
   (pgs-digest-state (create-pgs-digest-state)) (fn-zin-st (create-fn-zin-st))
   (cwin (resize-fn-octets$c-buf 70000 (create-fn-octets$c)))
   (ctab (resize-fn-octets$c-buf 4000 (create-fn-octets$c)))
   (cout (resize-fn-octets$c-buf 128 (create-fn-octets$c)))))
 :in-theory (disable fn-piwc-begin (:e fn-piwc-begin)))))

; Separately labelled mutation of the proposed physical shrink tariff.
(defthm piwc-literal-retained-capacity-tariff-mutation
 (let ((r (fn-piwc-begin '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 0)
             301 (create-pgs-digest-state) (create-fn-zin-st)
             (resize-fn-octets$c-buf 70000 (create-fn-octets$c))
             (resize-fn-octets$c-buf 4000 (create-fn-octets$c))
             (resize-fn-octets$c-buf 128 (create-fn-octets$c)))))
  (and (equal (fn-octets$c-buf-length (mv-nth 3 r)) 70000)
       (not (equal (fn-octets$c-buf-length (mv-nth 3 r)) 65536))
       (equal (fn-octets$c-buf-length (mv-nth 4 r)) 4000)
       (not (equal (fn-octets$c-buf-length (mv-nth 4 r)) 3494))
       (equal (fn-octets$c-buf-length (mv-nth 5 r)) 128)
       (not (equal (fn-octets$c-buf-length (mv-nth 5 r)) 64))))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
 :use piwc-literal-complete-retained-capacities-positive
 :in-theory (disable fn-piwc-begin (:e fn-piwc-begin)))))
