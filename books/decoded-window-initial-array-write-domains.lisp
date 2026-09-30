; Actual selected executive write operand domains, not setter allocation costs.
(in-package "ACL2")
(include-book "decoded-window-initial-buffer-counts")
(defun-nx fn-piwa-write-domainp (limit trace)
 (if (atom trace) t
  (and
   (cond ((and (consp (car trace)) (equal (caar trace) :array-write))
          (let* ((args (caddr (car trace))) (i (car args)) (o (cadr args)) (c (caddr args)))
           (and (natp i) (< i limit) (< i (fn-octets$c-buf-length c))
                (unsigned-byte-p 8 o))))
         ((and (consp (car trace)) (equal (caar trace) :fill-write))
          (let* ((args (caddr (car trace))) (n (car args)) (c (cadr args)))
           (and (natp n) (<= n limit) (<= n (fn-octets$c-buf-length c)))))
         (t t))
   (fn-piwa-write-domainp limit (cdr trace)))))
(defthm fn-piwa-write-domainp-of-append
 (equal (fn-piwa-write-domainp limit (append a b))
        (and (fn-piwa-write-domainp limit a) (fn-piwa-write-domainp limit b)))
 :hints (("Goal" :induct (append a b))))
(defthm fn-piwa-clear-establishes-write-domain
 (implies (natp limit)
  (fn-piwa-write-domainp limit (cdr (fn-pib-octets$c-clear c))))
 :hints (("Goal" :in-theory (enable fn-piwa-write-domainp fn-pib-octets$c-clear))))
(defthm fn-piwa-reserve-has-no-byte-or-fill-write
 (fn-piwa-write-domainp limit (cdr (fn-pib-octets$c-reserve n c)))
 :hints (("Goal" :in-theory (enable fn-piwa-write-domainp fn-pib-octets$c-reserve))))
(defthm fn-piwa-append-octet-actual-write-domain
 (implies (and (natp limit) (natp (fn-octets$c-fill c))
               (< (fn-octets$c-fill c) limit) (unsigned-byte-p 8 o))
  (fn-piwa-write-domainp limit (cdr (fn-pib-octets$c-append-octet o c))))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
  :in-theory (e/d (fn-pib-octets$c-append-octet fn-piwa-write-domainp max)
    (fn-octets$c-append-octet fn-pib-octets$c-append-octet-value-and-effects-projection)))))
(local (defthm fn-piwa-concrete-cell-is-ubyte
 (implies (and (fn-octets$cp c) (natp i) (< i (fn-octets$c-buf-length c)))
          (unsigned-byte-p 8 (fn-octets$c-bufi i c)))
 :hints (("Goal" :use (:instance fn-oct-bufp-cell-is-octet (buf (nth 0 c)) (k i))
  :in-theory (e/d (fn-octets$c-bufi fn-octets$c-buf-length)
                 (fn-octets$cp nth unsigned-byte-p))))))
(local (defthm fn-piwa-concrete-byte-write-keeps-type
 (implies (and (fn-octets$cp c) (natp i) (< i (fn-octets$c-buf-length c))
               (unsigned-byte-p 8 o))
          (fn-octets$cp (update-fn-octets$c-bufi i o c)))
 :hints (("Goal" :do-not '(preprocess)
  :use ((:instance fn-oct-cp-fields (fn-octets$c c))
        (:instance fn-oct-bufp-of-update-nth (buf (nth 0 c)) (k i) (v o))
        (:instance fn-oct-cp-of-update-buf (fn-octets$c c) (buf (update-nth i o (nth 0 c)))))
  :in-theory (e/d (update-fn-octets$c-bufi update-nth-array fn-octets$c-buf-length)
    (fn-octets$cp nth update-nth unsigned-byte-p fn-oct-cp-fields
     fn-oct-bufp-of-update-nth fn-oct-cp-of-update-buf))))))
(local (defthm fn-piwa-byte-write-keeps-capacity
 (implies (and (natp i) (< i (fn-octets$c-buf-length c)))
  (equal (fn-octets$c-buf-length (update-fn-octets$c-bufi i o c))
         (fn-octets$c-buf-length c)))
 :hints (("Goal" :in-theory (e/d
   (fn-octets$c-buf-length update-fn-octets$c-bufi update-nth-array)
   (nth update-nth))))))
(defthm fn-piwa-back-loop-actual-write-domain
 (implies (and (natp limit) (fn-octets$cp c)
               (natp src) (natp dst) (natp end) (< src dst) (<= dst end)
               (<= end limit) (<= end (fn-octets$c-buf-length c)))
  (fn-piwa-write-domainp limit (cdr (fn-pib-oct-back-loop src dst end c))))
 :rule-classes nil
 :hints (("Goal" :induct (fn-oct-back-loop src dst end c)
  :in-theory (e/d (fn-pib-oct-back-loop fn-piwa-write-domainp)
    (fn-octets$cp fn-octets$c-bufi fn-octets$c-buf-length
     update-fn-octets$c-bufi update-nth-array nth update-nth
     fn-pib-octets$c-append-octet unsigned-byte-p)))))
(local (defthm fn-piwa-append-octet-keeps-type
 (implies (and (fn-octets$cp c) (natp (fn-octets$c-fill c))
               (<= (fn-octets$c-fill c) (fn-octets$c-buf-length c))
               (fn-cbor-octetp o))
  (fn-octets$cp (fn-octets$c-append-octet o c)))
 :hints (("Goal" :use (:instance fn-oct-append-octet-step (fn-octets$c c))
  :in-theory (e/d (fn-octets$c-fill fn-octets$c-buf-length)
   (fn-oct-append-octet-step fn-octets$c-append-octet fn-oct-list-from fn-octets$cp nth))))))
(defthm fn-piwa-write-list-actual-write-domain
 (implies (and (natp limit) (fn-octets$cp c) (fn-cbor-octet-listp xs)
               (natp (fn-octets$c-fill c))
               (<= (+ (fn-octets$c-fill c) (len xs)) limit)
               (<= (+ (fn-octets$c-fill c) (len xs)) (fn-octets$c-buf-length c)))
  (fn-piwa-write-domainp limit (cdr (fn-pib-oct-write-list xs c))))
 :rule-classes nil
 :hints (("Goal" :induct (fn-oct-write-list xs c)
  :in-theory (e/d (fn-pib-oct-write-list fn-cbor-octet-listp fn-piwa-write-domainp)
    (fn-pib-octets$c-append-octet fn-octets$c-append-octet
     fn-octets$cp fn-octets$c-fill fn-octets$c-buf-length nth update-nth
     fn-oct-list-from fn-oct-append-octet-step unsigned-byte-p)))
 ("Subgoal *1/2" :use
  ((:instance fn-piwa-append-octet-actual-write-domain (o (car xs)))
   (:instance fn-piwa-append-octet-keeps-type (o (car xs)))))))
(local (defthm fn-piwa-back-loop-keeps-type-and-capacity
 (implies (and (fn-octets$cp c) (natp src) (natp dst) (natp end)
               (< src dst) (<= dst end) (<= end (fn-octets$c-buf-length c)))
  (and (fn-octets$cp (fn-oct-back-loop src dst end c))
       (equal (fn-octets$c-buf-length (fn-oct-back-loop src dst end c))
              (fn-octets$c-buf-length c))))
 :hints (("Goal" :use (:instance fn-oct-back-loop-steps (fn-octets$c c))
  :in-theory (e/d (fn-octets$c-buf-length)
   (fn-oct-back-loop-steps fn-oct-back-loop fn-oct-list-from fn-oct-back-copy fn-octets$cp nth))))))
(defthm fn-piwa-append-back-actual-write-domain
 (implies (and (natp limit) (fn-octets$cp c)
               (natp (fn-octets$c-fill c)) (posp off) (<= off (fn-octets$c-fill c))
               (natp n) (<= (+ (fn-octets$c-fill c) n) limit)
               (<= (+ (fn-octets$c-fill c) n) (fn-octets$c-buf-length c)))
  (fn-piwa-write-domainp limit (cdr (fn-pib-octets$c-append-back off n c))))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
  :use (:instance fn-piwa-back-loop-actual-write-domain
         (src (- (fn-octets$c-fill c) off)) (dst (fn-octets$c-fill c))
         (end (+ (fn-octets$c-fill c) n)))
  :in-theory (e/d (fn-pib-octets$c-append-back fn-piwa-write-domainp)
   (fn-oct-back-loop fn-pib-oct-back-loop fn-octets$c-fill fn-octets$c-buf-length
    fn-octets$cp nth update-nth)))))
(local (defthm fn-piwa-clear-keeps-type-capacity-and-fill
 (and (equal (fn-octets$c-buf-length (fn-octets$c-clear c)) (fn-octets$c-buf-length c))
      (equal (fn-octets$c-fill (fn-octets$c-clear c)) 0)
      (implies (fn-octets$cp c) (fn-octets$cp (fn-octets$c-clear c))))
 :hints (("Goal" :in-theory (e/d (fn-octets$c-clear update-fn-octets$c-fill)
   (fn-octets$cp nth update-nth))))))
(local (defthm fn-piwa-reserve-keeps-type-capacity-and-fill
 (implies (natp n)
  (and (equal (fn-octets$c-buf-length (fn-octets$c-reserve n c)) (max n (fn-octets$c-buf-length c)))
       (equal (fn-octets$c-fill (fn-octets$c-reserve n c)) (fn-octets$c-fill c))
       (implies (fn-octets$cp c) (fn-octets$cp (fn-octets$c-reserve n c)))))
 :hints (("Goal" :do-not '(preprocess)
  :use ((:instance fn-oct-cp-fields (fn-octets$c c))
        (:instance fn-oct-bufp-of-resize-list (buf (nth 0 c)) (m n))
        (:instance fn-oct-cp-of-update-buf (fn-octets$c c) (buf (resize-list (nth 0 c) n 0))))
  :in-theory (e/d (fn-octets$c-reserve resize-fn-octets$c-buf)
   (fn-octets$cp nth update-nth resize-list fn-oct-cp-fields
    fn-oct-bufp-of-resize-list fn-oct-cp-of-update-buf))))))
(local (defthm fn-piwa-append-back-keeps-type
 (implies (and (fn-octets$cp c) (natp (fn-octets$c-fill c))
               (posp off) (<= off (fn-octets$c-fill c)) (natp n)
               (<= (+ (fn-octets$c-fill c) n) (fn-octets$c-buf-length c)))
  (fn-octets$cp (fn-octets$c-append-back off n c)))
 :hints (("Goal" :in-theory (e/d (fn-octets$c-append-back update-fn-octets$c-fill)
   (fn-oct-back-loop fn-octets$c-fill fn-octets$c-buf-length fn-octets$cp nth update-nth))))))
(local (defthm fn-piwa-write-list-keeps-type
 (implies (and (fn-octets$cp c) (natp (fn-octets$c-fill c))
               (<= (fn-octets$c-fill c) (fn-octets$c-buf-length c))
               (fn-cbor-octet-listp xs))
  (fn-octets$cp (fn-oct-write-list xs c)))
 :hints (("Goal" :use (:instance fn-oct-write-list-steps (fn-octets$c c))
  :in-theory (e/d (fn-octets$c-fill fn-octets$c-buf-length)
   (fn-oct-write-list-steps fn-oct-write-list fn-oct-list-from fn-octets$cp nth))))))
(local (defthm fn-piwa-typed-nthcdr
 (implies (fn-cbor-octet-listp xs) (fn-cbor-octet-listp (nthcdr n xs)))
 :hints (("Goal" :induct (nthcdr n xs) :in-theory (enable nthcdr fn-cbor-octet-listp)))))
(local (defthm fn-piwa-len-nthcdr
 (equal (len (nthcdr n xs)) (nfix (- (len xs) (nfix n))))
 :hints (("Goal" :induct (nthcdr n xs) :in-theory (enable nthcdr)))))
(encapsulate ()
 (local (include-book "arithmetic-5/top" :dir :system))
 (defthm fn-piwa-payload-ready-actual-write-domain
  (implies (and (fn-octets$cp cwin) (fn-octets$cp ctab) (fn-cbor-octet-listp dict))
   (fn-piwa-write-domainp 65536 (cdr (fn-pib-piwc-payload-ready dict cwin ctab))))
  :rule-classes nil
  :hints (("Goal" :do-not '(preprocess)
   :use ((:instance fn-piwa-append-octet-actual-write-domain (limit 65536) (o 0) (c (fn-octets$c-reserve 65536 (fn-octets$c-clear cwin))))
    (:instance fn-piwa-append-back-actual-write-domain (limit 65536) (off 1) (n 32767) (c (fn-octets$c-append-octet 0 (fn-octets$c-reserve 65536 (fn-octets$c-clear cwin)))))
    (:instance fn-piwa-write-list-actual-write-domain (limit 65536) (xs (if (< 32768 (len dict)) (nthcdr (- (len dict) 32768) dict) dict)) (c (fn-octets$c-append-back 1 32767 (fn-octets$c-append-octet 0 (fn-octets$c-reserve 65536 (fn-octets$c-clear cwin))))))
    (:instance fn-piwa-append-octet-actual-write-domain (limit 65536) (o 0) (c (fn-oct-write-list (if (< 32768 (len dict)) (nthcdr (- (len dict) 32768) dict) dict) (fn-octets$c-append-back 1 32767 (fn-octets$c-append-octet 0 (fn-octets$c-reserve 65536 (fn-octets$c-clear cwin)))))))
    (:instance fn-piwa-append-back-actual-write-domain (limit 65536) (off 1) (n (- 32768 (+ 1 (min (len dict) 32768)))) (c (fn-octets$c-append-octet 0 (fn-oct-write-list (if (< 32768 (len dict)) (nthcdr (- (len dict) 32768) dict) dict) (fn-octets$c-append-back 1 32767 (fn-octets$c-append-octet 0 (fn-octets$c-reserve 65536 (fn-octets$c-clear cwin))))))))
    (:instance fn-piwa-append-octet-actual-write-domain (limit 65536) (o 0) (c (fn-octets$c-reserve 3494 (fn-octets$c-clear ctab))))
    (:instance fn-piwa-append-back-actual-write-domain (limit 65536) (off 1) (n 3493) (c (fn-octets$c-append-octet 0 (fn-octets$c-reserve 3494 (fn-octets$c-clear ctab)))))
    fn-pib-prefilled-dict-capacity-and-fill)
   :in-theory (e/d (fn-pib-piwc-payload-ready fn-piwa-write-domainp)
    (fn-pib-prefilled-dict-capacity-and-fill
     fn-pib-octets$c-clear fn-pib-octets$c-reserve fn-pib-octets$c-append-octet
     fn-pib-octets$c-append-back fn-pib-oct-write-list fn-pib-oct-back-loop
     fn-octets$c-clear fn-octets$c-reserve fn-octets$c-append-octet
     fn-octets$c-append-back fn-oct-write-list fn-oct-back-loop
     fn-octets$c-fill fn-octets$c-buf-length fn-octets$cp fn-cbor-octet-listp
     nthcdr (:e fn-octets$c-append-back)))))))
(defthm fn-piwa-initialize-actual-write-domain
 (implies (and (fn-octets$cp cwin) (fn-octets$cp ctab) (fn-cbor-octet-listp dict))
  (fn-piwa-write-domainp 65536
   (cdr (fn-pib-piwc-initialize dict zin cwin ctab cout))))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
  :use fn-piwa-payload-ready-actual-write-domain
  :in-theory (e/d (fn-pib-piwc-initialize fn-piwa-write-domainp)
   (fn-pib-piwc-payload-ready fn-piwc-payload-ready fn-zin-reset
    fn-zin-set fn-pib-octets$c-clear fn-pib-octets$c-reserve
    fn-octets$c-clear fn-octets$c-reserve fn-octets$cp fn-cbor-octet-listp)))))
(defthm fn-piwa-ewz-begin-actual-write-domain
 (implies (and (fn-octets$cp cwin) (fn-octets$cp ctab) (fn-cbor-octet-listp dict))
  (fn-piwa-write-domainp 65536
   (cdr (fn-pib-piwc-ewz-begin file eoff elen poff compressed decoded offset
                    ticket incarnation lease expected dict hash zin cwin ctab cout))))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
  :use fn-piwa-initialize-actual-write-domain
  :in-theory (e/d (fn-pib-piwc-ewz-begin fn-piwa-write-domainp)
   (fn-pib-piwc-initialize fn-piwc-initialize fn-ews-begin fn-ewz-state fn-pzd-budget
    fn-pzw-stored-admissiblep nfix natp nth fn-octets$cp fn-cbor-octet-listp)))))
(defthm fn-piwa-begin-actual-write-domain
 (implies (and (fn-octets$cp cwin) (fn-octets$cp ctab))
  (fn-piwa-write-domainp 65536
   (cdr (fn-pib-piwc-begin token incarnation hash zin cwin ctab cout))))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
  :use (fn-pwz-dictionary-is-bounded-octets
   (:instance fn-piwa-ewz-begin-actual-write-domain
    (file (nfix (fn-pwz-nth 2 token))) (eoff (nfix (fn-pwz-nth 3 token)))
    (elen (nfix (fn-pwz-nth 4 token))) (poff (nfix (fn-pwz-nth 5 token)))
    (compressed (nfix (fn-pwz-nth 6 token))) (decoded (nfix (fn-pwz-nth 9 token)))
    (offset (nfix (fn-pwz-nth 7 token))) (ticket (fn-pwz-nth 1 token))
    (lease token) (expected (nfix (fn-pwz-nth 8 token))) (dict (fn-pwz-dictionary token))))
  :in-theory (e/d (fn-pib-piwc-begin fn-piwa-write-domainp)
   (fn-pib-piwc-ewz-begin fn-piwc-ewz-begin fn-pwz-nth fn-pwz-dictionary
    fn-octets$cp nfix natp nth)))))
(defthm fn-piwa-actual-begin-array-write-domain-boundary
 (implies (and (fn-octets$cp cwin) (fn-octets$cp ctab) (fn-octets$cp cout))
  (let* ((o (fn-pib-piwc-begin token incarnation hash zin cwin ctab cout))
         (rc (car o)) (ra (fn-pwz-begin token incarnation hash zin awin atab aout)))
   (and (equal (mv-nth 0 rc) (mv-nth 0 ra))
        (equal (mv-nth 1 rc) (mv-nth 1 ra))
        (equal (mv-nth 2 rc) (mv-nth 2 ra))
        (fn-octets$corr (mv-nth 3 rc) (mv-nth 3 ra))
        (fn-octets$corr (mv-nth 4 rc) (mv-nth 4 ra))
        (fn-octets$corr (mv-nth 5 rc) (mv-nth 5 ra))
        (fn-piwa-write-domainp 65536 (cdr o)))))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
  :use (fn-pib-actual-begin-array-source-boundary fn-piwa-begin-actual-write-domain)
  :in-theory (disable fn-pib-piwc-begin fn-piwc-begin fn-pwz-begin
   fn-piwa-write-domainp fn-octets$cp fn-octets$corr
   (:e fn-pib-piwc-begin) (:e fn-piwc-begin) (:e fn-pwz-begin)))))
