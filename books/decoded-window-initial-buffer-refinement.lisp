; Proof-only actual export-selected executive composition, not a host caller.
(in-package "ACL2")
(include-book "decoded-window-initial-buffer-exec")

(local (defthm fn-piwc-clear-capacity-and-fill
 (and (equal (fn-octets$c-buf-length (fn-octets$c-clear b)) (fn-octets$c-buf-length b))
      (equal (fn-octets$c-fill (fn-octets$c-clear b)) 0))
 :hints (("Goal" :in-theory (enable fn-octets$c-clear)))))
(local (defthm fn-piwc-reserve-capacity-and-fill
 (implies (natp n)
  (and (equal (fn-octets$c-buf-length (fn-octets$c-reserve n b))
              (max n (fn-octets$c-buf-length b)))
       (equal (fn-octets$c-fill (fn-octets$c-reserve n b)) (fn-octets$c-fill b))))
 :hints (("Goal" :in-theory (enable fn-octets$c-reserve)))))
(local (defthm fn-piwc-len-nthcdr
 (equal (len (nthcdr n xs)) (nfix (- (len xs) (nfix n))))
 :hints (("Goal" :induct (nthcdr n xs) :in-theory (enable nthcdr)))))

(local (defthm fn-piwc-append-octet-fill
 (equal (fn-octets$c-fill (fn-octets$c-append-octet o b))
        (+ 1 (fn-octets$c-fill b)))
 :hints (("Goal" :in-theory (enable fn-octets$c-append-octet)))))
(local (defthm fn-piwc-append-back-fill
 (equal (fn-octets$c-fill (fn-octets$c-append-back off n b))
        (+ n (fn-octets$c-fill b)))
 :hints (("Goal" :in-theory (e/d (fn-octets$c-append-back) (fn-oct-back-loop))))))
(local (defthm fn-piwc-write-list-fill
 (implies (acl2-numberp (fn-octets$c-fill b))
  (equal (fn-octets$c-fill (fn-oct-write-list xs b))
         (+ (len xs) (fn-octets$c-fill b))))
 :hints (("Goal" :induct (fn-oct-write-list xs b)
            :in-theory (e/d (fn-oct-write-list) (fn-octets$c-append-octet))))))

(encapsulate
 ()
 (local (include-book "arithmetic-5/top" :dir :system))
 (defthm fn-piwc-actual-export-composition-keeps-initial-capacities
  (let ((r (fn-piwc-payload-ready dict cwin ctab)))
   (and (equal (mv-nth 0 r) (min (len dict) 32768))
        (equal (fn-octets$c-buf-length (mv-nth 1 r))
               (max 65536 (fn-octets$c-buf-length cwin)))
        (equal (fn-octets$c-fill (mv-nth 1 r)) 65536)
        (equal (fn-octets$c-buf-length (mv-nth 2 r))
               (max 3494 (fn-octets$c-buf-length ctab)))
        (equal (fn-octets$c-fill (mv-nth 2 r)) 3494)))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
   :in-theory
    (e/d (fn-piwc-payload-ready)
         (fn-octets$c-buf-length fn-octets$c-fill fn-octets$c-clear
          fn-octets$c-reserve fn-octets$c-append-octet fn-octets$c-append-back
          fn-oct-write-list fn-oct-back-loop nthcdr (:e fn-octets$c-append-back)))))))


(local (defthm fn-piwc-clear-correspondence-unfolds
 (implies (fn-octets$corr fn-octets$c fn-octets) (fn-octets$corr (fn-octets$c-clear fn-octets$c) (fn-octets$a-clear fn-octets)))
 :hints (("Goal" :use fn-octets-clear{correspondence}))))

(local (defthm fn-piwc-reserve-correspondence-unfolds
 (implies (and (fn-octets$corr fn-octets$c fn-octets) (natp n)) (fn-octets$corr (fn-octets$c-reserve n fn-octets$c) (fn-octets$a-reserve n fn-octets)))
 :hints (("Goal" :use fn-octets-reserve{correspondence}))))

(local (defthm fn-piwc-append-octet-correspondence-unfolds
 (implies (and (fn-octets$corr fn-octets$c fn-octets) (fn-cbor-octetp o)) (fn-octets$corr (fn-octets$c-append-octet o fn-octets$c) (fn-octets$a-append-octet o fn-octets)))
 :hints (("Goal" :use fn-octets-append-octet{correspondence}))))

(local (defthm fn-piwc-append-list-correspondence-unfolds
 (implies (and (fn-octets$corr fn-octets$c fn-octets) (fn-cbor-octet-listp xs)) (fn-octets$corr (fn-oct-write-list xs fn-octets$c) (fn-octets$a-append-list xs fn-octets)))
 :hints (("Goal" :use fn-octets-append-list{correspondence}))))

(local (defthm fn-piwc-append-back-correspondence-unfolds
 (implies (and (fn-octets$corr fn-octets$c fn-octets) (natp off) (<= 1 off) (<= off (fn-octets$a-len fn-octets)) (natp n)) (fn-octets$corr (fn-octets$c-append-back off n fn-octets$c) (fn-octets$a-append-back off n fn-octets)))
 :hints (("Goal" :use fn-octets-append-back{correspondence}))))

(local (defthm fn-piwc-corr-implies-typed-model
 (implies (fn-octets$corr c a) (fn-cbor-octet-listp a))
 :hints (("Goal" :in-theory (enable fn-octets$corr)))))

(local (defthm fn-piwc-typed-nthcdr
 (implies (fn-cbor-octet-listp xs) (fn-cbor-octet-listp (nthcdr n xs)))
 :hints (("Goal" :induct (nthcdr n xs) :in-theory (enable nthcdr fn-cbor-octet-listp)))))

(local (defthm fn-piwc-clear-corr-empty
 (implies (fn-octets$corr c a) (fn-octets$corr (fn-octets$c-clear c) nil))
 :hints (("Goal" :use ((:instance fn-octets-clear{correspondence}
                       (fn-octets$c c) (fn-octets a)))
  :in-theory (e/d (fn-octets$a-clear) (fn-octets$corr fn-octets$c-clear))))))
(local (defthm fn-piwc-reserve-corr-same
 (implies (and (fn-octets$corr c a) (natp n))
          (fn-octets$corr (fn-octets$c-reserve n c) a))
 :hints (("Goal" :use ((:instance fn-octets-reserve{correspondence}
                        (fn-octets$c c) (fn-octets a)))
  :in-theory (e/d (fn-octets$a-reserve) (fn-octets$corr fn-octets$c-reserve))))))
(local (defthm fn-piwc-first-zero-corr
 (implies (fn-octets$corr c nil)
          (fn-octets$corr (fn-octets$c-append-octet 0 c) '(0)))
 :hints (("Goal" :use ((:instance fn-octets-append-octet{correspondence}
                        (fn-octets$c c) (fn-octets nil) (o 0)))
  :in-theory (e/d (fn-octets$a-append-octet) (fn-octets$corr fn-octets$c-append-octet))))))
(local (defthm fn-piwc-abstract-list-length
 (implies (true-listp a)
  (equal (len (fn-octets$a-append-list xs a)) (+ (len a) (len xs))))
 :hints (("Goal" :in-theory (enable fn-octets$a-append-list)))))
(local (defthm fn-piwc-abstract-octet-length
 (implies (true-listp a)
  (equal (len (fn-octets$a-append-octet o a)) (+ 1 (len a))))
 :hints (("Goal" :in-theory (enable fn-octets$a-append-octet)))))
(local (defthm fn-piwc-len-append
 (equal (len (append a b)) (+ (len a) (len b)))
 :hints (("Goal" :induct (append a b)))))
(local (defthm fn-piwc-back-copy-length
 (implies (and (natp n) (posp off) (<= off (len a)) (true-listp a))
  (equal (len (fn-oct-back-copy off n a)) (+ n (len a))))
 :hints (("Goal" :induct (fn-oct-back-copy off n a)
           :in-theory (enable fn-oct-back-copy)))))
(local (defthm fn-piwc-abstract-back-length
 (implies (and (natp n) (posp off) (<= off (len a)) (true-listp a))
  (equal (len (fn-octets$a-append-back off n a)) (+ n (len a))))
 :hints (("Goal" :in-theory (enable fn-octets$a-append-back)))))
(local (defthm fn-piwc-typed-model-is-proper
 (implies (fn-cbor-octet-listp a) (true-listp a))
 :hints (("Goal" :induct (fn-cbor-octet-listp a)
            :in-theory (enable fn-cbor-octet-listp)))))

(local (defthm fn-piwc-typed-abstract-back
 (implies (fn-cbor-octet-listp a)
  (fn-cbor-octet-listp (fn-octets$a-append-back off n a)))
 :hints (("Goal" :in-theory (e/d (fn-octets$a-append-back) (fn-oct-back-copy))))))
(local (defthm fn-piwc-typed-abstract-list
 (implies (and (fn-cbor-octet-listp a) (fn-cbor-octet-listp xs))
  (fn-cbor-octet-listp (fn-octets$a-append-list xs a)))
 :hints (("Goal" :in-theory (enable fn-octets$a-append-list)))))
(local (defthm fn-piwc-typed-abstract-zero
 (implies (fn-cbor-octet-listp a)
  (fn-cbor-octet-listp (fn-octets$a-append-octet 0 a)))
 :hints (("Goal" :in-theory (enable fn-octets$a-append-octet fn-cbor-octet-listp)))))

(defthm fn-piwc-actual-export-composition-refines-payload-ready
 (implies (and (fn-cbor-octet-listp dict)
               (fn-octets$corr cwin awin) (fn-octets$corr ctab atab))
  (let ((rc (fn-piwc-payload-ready dict cwin ctab))
        (ra (fn-zin-payload-ready dict awin atab)))
   (and (equal (mv-nth 0 rc) (mv-nth 0 ra))
        (fn-octets$corr (mv-nth 1 rc) (mv-nth 1 ra))
        (fn-octets$corr (mv-nth 2 rc) (mv-nth 2 ra)))))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
  :in-theory
   (e/d (fn-piwc-payload-ready fn-zin-payload-ready fn-octets$a-len
         fn-zin-win-clear fn-zin-win-reserve fn-zin-win-append-octet
         fn-zin-win-append-back fn-zin-win-append-list
         fn-zin-tab-clear fn-zin-tab-reserve fn-zin-tab-append-octet fn-zin-tab-append-back)
        (fn-zin-payload-ready-ignores-buffers
         (:e fn-zin-win-append-octet) (:e fn-zin-tab-append-octet)
         (:e fn-zin-win-clear) (:e fn-zin-tab-clear)
         (:e fn-zin-win-reserve) (:e fn-zin-tab-reserve)
         fn-octets$corr fn-octets$c-clear fn-octets$c-reserve
         fn-octets$c-append-octet fn-octets$c-append-back fn-oct-write-list
         fn-octets$a-clear fn-octets$a-reserve fn-octets$a-append-octet
         fn-octets$a-append-back fn-octets$a-append-list
         (:e fn-zin-win-append-back) (:e fn-zin-tab-append-back)
         (:e fn-octets$a-append-back) (:e fn-octets$c-append-back))))))

(defthm fn-piwc-actual-export-composition-refines-initialize
 (implies (and (fn-cbor-octet-listp dict)
               (fn-octets$corr cwin awin) (fn-octets$corr ctab atab)
               (fn-octets$corr cout aout))
  (let ((rc (fn-piwc-initialize dict fn-zin-st cwin ctab cout))
        (ra (fn-pzw-initialize dict fn-zin-st awin atab aout)))
   (and (equal (mv-nth 0 rc) (mv-nth 0 ra))
        (fn-octets$corr (mv-nth 1 rc) (mv-nth 1 ra))
        (fn-octets$corr (mv-nth 2 rc) (mv-nth 2 ra))
        (fn-octets$corr (mv-nth 3 rc) (mv-nth 3 ra)))))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
  :use ((:instance fn-piwc-actual-export-composition-refines-payload-ready))
  :in-theory
   (e/d (fn-piwc-initialize fn-pzw-initialize fn-zin-out-clear fn-zin-out-reserve)
        (fn-piwc-payload-ready fn-zin-payload-ready fn-zin-set fn-zin-reset
         fn-octets$corr fn-octets$c-clear fn-octets$c-reserve fn-octets$a-clear
         fn-octets$a-reserve (:e fn-piwc-payload-ready) (:e fn-zin-payload-ready))))))

(defthm fn-piwc-actual-initialize-keeps-initial-capacities
 (let ((r (fn-piwc-initialize dict fn-zin-st cwin ctab cout)))
  (and (equal (fn-octets$c-buf-length (mv-nth 1 r))
              (max 65536 (fn-octets$c-buf-length cwin)))
       (equal (fn-octets$c-fill (mv-nth 1 r)) 65536)
       (equal (fn-octets$c-buf-length (mv-nth 2 r))
              (max 3494 (fn-octets$c-buf-length ctab)))
       (equal (fn-octets$c-fill (mv-nth 2 r)) 3494)
       (equal (fn-octets$c-buf-length (mv-nth 3 r))
              (max 64 (fn-octets$c-buf-length cout)))
       (equal (fn-octets$c-fill (mv-nth 3 r)) 0)))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
  :use fn-piwc-actual-export-composition-keeps-initial-capacities
  :in-theory (e/d (fn-piwc-initialize)
     (fn-piwc-payload-ready fn-octets$c-buf-length fn-octets$c-fill
      fn-octets$c-clear fn-octets$c-reserve fn-zin-reset fn-zin-set
      (:e fn-piwc-payload-ready))))))

(local
 (defthm fn-piwc-ewz-begin-refines-actual
  (implies (and (fn-cbor-octet-listp dict)
                (fn-octets$corr cwin awin) (fn-octets$corr ctab atab)
                (fn-octets$corr cout aout))
   (let ((rc (fn-piwc-ewz-begin file eoff elen poff compressed decoded offset
               ticket incarnation lease expected dict pgs-digest-state
               fn-zin-st cwin ctab cout))
         (ra (fn-ewz-begin file eoff elen poff compressed decoded offset
               ticket incarnation lease expected dict pgs-digest-state
               fn-zin-st awin atab aout)))
    (and (equal (mv-nth 0 rc) (mv-nth 0 ra))
         (equal (mv-nth 1 rc) (mv-nth 1 ra))
         (equal (mv-nth 2 rc) (mv-nth 2 ra))
         (fn-octets$corr (mv-nth 3 rc) (mv-nth 3 ra))
         (fn-octets$corr (mv-nth 4 rc) (mv-nth 4 ra))
         (fn-octets$corr (mv-nth 5 rc) (mv-nth 5 ra)))))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
   :use fn-piwc-actual-export-composition-refines-initialize
   :in-theory (e/d (fn-piwc-ewz-begin fn-ewz-begin)
      (fn-piwc-initialize fn-pzw-initialize fn-ews-begin fn-ewz-state fn-pzd-budget
       fn-pzw-stored-admissiblep nfix natp nth fn-octets$corr))))))

(defthm fn-piwc-begin-refines-actual-begin
 (implies (and (fn-octets$corr cwin awin) (fn-octets$corr ctab atab)
               (fn-octets$corr cout aout))
  (let ((rc (fn-piwc-begin token incarnation pgs-digest-state fn-zin-st cwin ctab cout))
        (ra (fn-pwz-begin token incarnation pgs-digest-state fn-zin-st awin atab aout)))
   (and (equal (mv-nth 0 rc) (mv-nth 0 ra))
        (equal (mv-nth 1 rc) (mv-nth 1 ra))
        (equal (mv-nth 2 rc) (mv-nth 2 ra))
        (fn-octets$corr (mv-nth 3 rc) (mv-nth 3 ra))
        (fn-octets$corr (mv-nth 4 rc) (mv-nth 4 ra))
        (fn-octets$corr (mv-nth 5 rc) (mv-nth 5 ra)))))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
  :use (fn-pwz-dictionary-is-bounded-octets
        (:instance fn-piwc-ewz-begin-refines-actual
           (dict (fn-pwz-dictionary token))
           (file (nfix (fn-pwz-nth 2 token))) (eoff (nfix (fn-pwz-nth 3 token)))
           (elen (nfix (fn-pwz-nth 4 token))) (poff (nfix (fn-pwz-nth 5 token)))
           (compressed (nfix (fn-pwz-nth 6 token))) (decoded (nfix (fn-pwz-nth 9 token)))
           (offset (nfix (fn-pwz-nth 7 token))) (ticket (fn-pwz-nth 1 token))
           (lease token) (expected (nfix (fn-pwz-nth 8 token)))))
  :in-theory (e/d (fn-piwc-begin fn-pwz-begin)
       (fn-piwc-ewz-begin fn-ewz-begin fn-pwz-dictionary fn-pwz-nth nfix natp
        fn-octets$corr (:e fn-pwz-dictionary))))))

(defthm fn-piwc-begin-keeps-initial-capacities
 (let ((r (fn-piwc-begin token incarnation pgs-digest-state fn-zin-st cwin ctab cout)))
  (and (equal (fn-octets$c-buf-length (mv-nth 3 r))
              (max 65536 (fn-octets$c-buf-length cwin)))
       (equal (fn-octets$c-fill (mv-nth 3 r)) 65536)
       (equal (fn-octets$c-buf-length (mv-nth 4 r))
              (max 3494 (fn-octets$c-buf-length ctab)))
       (equal (fn-octets$c-fill (mv-nth 4 r)) 3494)
       (equal (fn-octets$c-buf-length (mv-nth 5 r))
              (max 64 (fn-octets$c-buf-length cout)))
       (equal (fn-octets$c-fill (mv-nth 5 r)) 0)))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
  :use ((:instance fn-piwc-actual-initialize-keeps-initial-capacities
                    (dict (fn-pwz-dictionary token))))
  :in-theory (e/d (fn-piwc-begin fn-piwc-ewz-begin)
     (fn-piwc-initialize fn-pwz-dictionary fn-pwz-nth fn-ews-begin fn-ewz-state
      fn-pzd-budget fn-pzw-stored-admissiblep nfix natp nth
      fn-octets$c-buf-length fn-octets$c-fill (:e fn-pwz-dictionary))))))

; Initial model contents are discarded by the actual initializer.  The
; physical arrays must still be typed: unused cells beyond the new fill survive.
(local (defthm fn-piwc-typed-clear-corr-empty
 (implies (fn-octets$cp c)
          (fn-octets$corr (fn-octets$c-clear c) nil))
 :hints (("Goal" :in-theory
  (enable fn-octets$corr fn-octets$c-clear fn-octets$cp
          fn-oct-list-from fn-octets$c-fillp fn-octets$c-bufp)))))

(local
 (defthm fn-piwc-payload-ready-refines-from-typed-arrays
 (implies (and (fn-cbor-octet-listp dict)
               (fn-octets$cp cwin) (fn-octets$cp ctab))
  (let ((rc (fn-piwc-payload-ready dict cwin ctab))
        (ra (fn-zin-payload-ready dict awin atab)))
   (and (equal (mv-nth 0 rc) (mv-nth 0 ra))
        (fn-octets$corr (mv-nth 1 rc) (mv-nth 1 ra))
        (fn-octets$corr (mv-nth 2 rc) (mv-nth 2 ra)))))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
  :use ((:instance fn-piwc-typed-clear-corr-empty (c cwin))
        (:instance fn-piwc-typed-clear-corr-empty (c ctab)))
  :in-theory
   (e/d (fn-piwc-payload-ready fn-zin-payload-ready fn-octets$a-len
         fn-zin-win-clear fn-zin-win-reserve fn-zin-win-append-octet
         fn-zin-win-append-back fn-zin-win-append-list
         fn-zin-tab-clear fn-zin-tab-reserve fn-zin-tab-append-octet fn-zin-tab-append-back)
        (fn-zin-payload-ready-ignores-buffers
         (:e fn-zin-win-append-octet) (:e fn-zin-tab-append-octet)
         (:e fn-zin-win-clear) (:e fn-zin-tab-clear)
         (:e fn-zin-win-reserve) (:e fn-zin-tab-reserve)
         fn-octets$corr fn-octets$c-clear fn-octets$c-reserve
         fn-octets$c-append-octet fn-octets$c-append-back fn-oct-write-list
         fn-octets$a-clear fn-octets$a-reserve fn-octets$a-append-octet
         fn-octets$a-append-back fn-octets$a-append-list
         (:e fn-zin-win-append-back) (:e fn-zin-tab-append-back)
         (:e fn-octets$a-append-back) (:e fn-octets$c-append-back)))))))

(local
 (defthm fn-piwc-initialize-refines-from-typed-arrays
 (implies (and (fn-cbor-octet-listp dict)
               (fn-octets$cp cwin) (fn-octets$cp ctab)
               (fn-octets$cp cout))
  (let ((rc (fn-piwc-initialize dict fn-zin-st cwin ctab cout))
        (ra (fn-pzw-initialize dict fn-zin-st awin atab aout)))
   (and (equal (mv-nth 0 rc) (mv-nth 0 ra))
        (fn-octets$corr (mv-nth 1 rc) (mv-nth 1 ra))
        (fn-octets$corr (mv-nth 2 rc) (mv-nth 2 ra))
        (fn-octets$corr (mv-nth 3 rc) (mv-nth 3 ra)))))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
  :use ((:instance fn-piwc-payload-ready-refines-from-typed-arrays)
        (:instance fn-piwc-typed-clear-corr-empty (c cout)))
  :in-theory
   (e/d (fn-piwc-initialize fn-pzw-initialize fn-zin-out-clear fn-zin-out-reserve)
        (fn-piwc-payload-ready fn-zin-payload-ready fn-zin-set fn-zin-reset
         fn-octets$corr fn-octets$c-clear fn-octets$c-reserve fn-octets$a-clear
         fn-octets$a-reserve (:e fn-piwc-payload-ready) (:e fn-zin-payload-ready)))))))

(local
 (defthm fn-piwc-ewz-begin-refines-from-typed-arrays
  (implies (and (fn-cbor-octet-listp dict)
                (fn-octets$cp cwin) (fn-octets$cp ctab)
                (fn-octets$cp cout))
   (let ((rc (fn-piwc-ewz-begin file eoff elen poff compressed decoded offset
               ticket incarnation lease expected dict pgs-digest-state
               fn-zin-st cwin ctab cout))
         (ra (fn-ewz-begin file eoff elen poff compressed decoded offset
               ticket incarnation lease expected dict pgs-digest-state
               fn-zin-st awin atab aout)))
    (and (equal (mv-nth 0 rc) (mv-nth 0 ra))
         (equal (mv-nth 1 rc) (mv-nth 1 ra))
         (equal (mv-nth 2 rc) (mv-nth 2 ra))
         (fn-octets$corr (mv-nth 3 rc) (mv-nth 3 ra))
         (fn-octets$corr (mv-nth 4 rc) (mv-nth 4 ra))
         (fn-octets$corr (mv-nth 5 rc) (mv-nth 5 ra)))))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
   :use fn-piwc-initialize-refines-from-typed-arrays
   :in-theory (e/d (fn-piwc-ewz-begin fn-ewz-begin)
      (fn-piwc-initialize fn-pzw-initialize fn-ews-begin fn-ewz-state fn-pzd-budget
       fn-pzw-stored-admissiblep nfix natp nth fn-octets$corr))))))


(defthm fn-piwc-begin-refines-actual-begin-from-typed-arrays
 (implies (and (fn-octets$cp cwin) (fn-octets$cp ctab)
               (fn-octets$cp cout))
  (let ((rc (fn-piwc-begin token incarnation pgs-digest-state fn-zin-st cwin ctab cout))
        (ra (fn-pwz-begin token incarnation pgs-digest-state fn-zin-st awin atab aout)))
   (and (equal (mv-nth 0 rc) (mv-nth 0 ra))
        (equal (mv-nth 1 rc) (mv-nth 1 ra))
        (equal (mv-nth 2 rc) (mv-nth 2 ra))
        (fn-octets$corr (mv-nth 3 rc) (mv-nth 3 ra))
        (fn-octets$corr (mv-nth 4 rc) (mv-nth 4 ra))
        (fn-octets$corr (mv-nth 5 rc) (mv-nth 5 ra)))))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
  :use (fn-pwz-dictionary-is-bounded-octets
        (:instance fn-piwc-ewz-begin-refines-from-typed-arrays
           (dict (fn-pwz-dictionary token))
           (file (nfix (fn-pwz-nth 2 token))) (eoff (nfix (fn-pwz-nth 3 token)))
           (elen (nfix (fn-pwz-nth 4 token))) (poff (nfix (fn-pwz-nth 5 token)))
           (compressed (nfix (fn-pwz-nth 6 token))) (decoded (nfix (fn-pwz-nth 9 token)))
           (offset (nfix (fn-pwz-nth 7 token))) (ticket (fn-pwz-nth 1 token))
           (lease token) (expected (nfix (fn-pwz-nth 8 token)))))
  :in-theory (e/d (fn-piwc-begin fn-pwz-begin)
       (fn-piwc-ewz-begin fn-ewz-begin fn-pwz-dictionary fn-pwz-nth nfix natp
        fn-octets$corr (:e fn-pwz-dictionary))))))

