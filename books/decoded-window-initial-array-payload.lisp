; Actual source resize request payloads, not runtime object/header charges.
(in-package "ACL2")
(include-book "decoded-window-initial-buffer-counts")
(defun-nx fn-pib-resize-request-payload (trace)
 (if (atom trace) 0
  (+ (if (and (consp (car trace)) (equal (caar trace) :array-resize))
         (nfix (car (caddr (car trace)))) 0)
     (fn-pib-resize-request-payload (cdr trace)))))
(defthm fn-pib-resize-request-payload-of-append
 (equal (fn-pib-resize-request-payload (append a b))
        (+ (fn-pib-resize-request-payload a) (fn-pib-resize-request-payload b)))
 :hints (("Goal" :induct (append a b))))
(defthm fn-pib-no-resize-means-no-request-payload
 (implies (equal (fn-pib-event-count :array-resize trace) 0)
          (equal (fn-pib-resize-request-payload trace) 0))
 :hints (("Goal" :induct (fn-pib-event-count :array-resize trace)
                 :in-theory (enable fn-pib-resize-request-payload fn-pib-event-count))))
(defthm fn-pib-reserve-request-payload
 (implies (natp n)
  (equal (fn-pib-resize-request-payload (cdr (fn-pib-octets$c-reserve n c)))
         (if (<= n (fn-octets$c-buf-length c)) 0 n)))
 :hints (("Goal" :in-theory (enable fn-pib-resize-request-payload fn-pib-octets$c-reserve))))

(local (defthm fn-pibp-clear-capacity-and-fill
 (and (equal (fn-octets$c-buf-length (fn-octets$c-clear b)) (fn-octets$c-buf-length b))
      (equal (fn-octets$c-fill (fn-octets$c-clear b)) 0))
 :hints (("Goal" :in-theory (enable fn-octets$c-clear)))))
(local (defthm fn-pibp-reserve-capacity-and-fill
 (implies (natp n)
  (and (equal (fn-octets$c-buf-length (fn-octets$c-reserve n b))
              (max n (fn-octets$c-buf-length b)))
       (equal (fn-octets$c-fill (fn-octets$c-reserve n b)) (fn-octets$c-fill b))))
 :hints (("Goal" :in-theory (enable fn-octets$c-reserve)))))
(local (defthm fn-pibp-len-nthcdr
 (equal (len (nthcdr n xs)) (nfix (- (len xs) (nfix n))))
 :hints (("Goal" :induct (nthcdr n xs) :in-theory (enable nthcdr)))))

(local (defthm fn-pibp-append-octet-fill
 (equal (fn-octets$c-fill (fn-octets$c-append-octet o b))
        (+ 1 (fn-octets$c-fill b)))
 :hints (("Goal" :in-theory (enable fn-octets$c-append-octet)))))
(local (defthm fn-pibp-append-back-fill
 (equal (fn-octets$c-fill (fn-octets$c-append-back off n b))
        (+ n (fn-octets$c-fill b)))
 :hints (("Goal" :in-theory (e/d (fn-octets$c-append-back) (fn-oct-back-loop))))))
(local (defthm fn-pibp-write-list-fill
 (implies (acl2-numberp (fn-octets$c-fill b))
  (equal (fn-octets$c-fill (fn-oct-write-list xs b))
         (+ (len xs) (fn-octets$c-fill b))))
 :hints (("Goal" :induct (fn-oct-write-list xs b)
            :in-theory (e/d (fn-oct-write-list) (fn-octets$c-append-octet))))))

(local (defthm fn-pibp-ready-prefix-capacity-and-fill
 (let ((b (fn-octets$c-append-back 1 32767
             (fn-octets$c-append-octet 0
               (fn-octets$c-reserve 65536 (fn-octets$c-clear c))))))
  (and (equal (fn-octets$c-fill b) 32768)
       (equal (fn-octets$c-buf-length b) (max 65536 (fn-octets$c-buf-length c)))))
 :hints (("Goal" :in-theory (disable fn-octets$c-clear fn-octets$c-reserve
   fn-octets$c-append-octet fn-octets$c-append-back fn-octets$c-fill fn-octets$c-buf-length)))))

(encapsulate ()
 (local (include-book "arithmetic-5/top" :dir :system))
 (defthm fn-pib-payload-ready-exact-resize-payload
  (equal (fn-pib-resize-request-payload (cdr (fn-pib-piwc-payload-ready dict cwin ctab)))
   (+ (if (<= 65536 (fn-octets$c-buf-length cwin)) 0 65536)
      (if (<= 3494 (fn-octets$c-buf-length ctab)) 0 3494)))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
 :use (fn-pib-prefilled-dict-source-counts fn-pib-prefilled-dict-capacity-and-fill)
 :in-theory (e/d (fn-pib-piwc-payload-ready fn-pib-resize-request-payload)
   (fn-pib-prefilled-dict-source-counts fn-pib-prefilled-dict-capacity-and-fill
    fn-pib-octets$c-clear fn-pib-octets$c-reserve fn-pib-octets$c-append-octet
    fn-pib-octets$c-append-back fn-pib-oct-write-list fn-pib-oct-back-loop
    fn-octets$c-clear fn-octets$c-reserve fn-octets$c-append-octet
    fn-octets$c-append-back fn-oct-write-list fn-oct-back-loop fn-pib-event-count
    fn-octets$c-fill fn-octets$c-buf-length nthcdr (:e fn-octets$c-append-back)))))))
(defun fn-pib-initial-new-array-payload (wc tc oc)
 (declare (xargs :guard t))
 (+ (if (<= 65536 (nfix wc)) 0 65536)
    (if (<= 3494 (nfix tc)) 0 3494)
    (if (<= 64 (nfix oc)) 0 64)))
(defun fn-pib-initial-retained-and-requested-payload (wc tc oc)
 (declare (xargs :guard t))
 (+ (nfix wc) (nfix tc) (nfix oc) (fn-pib-initial-new-array-payload wc tc oc)))
(defthm fn-pib-initialize-exact-resize-payload
 (equal (fn-pib-resize-request-payload
          (cdr (fn-pib-piwc-initialize dict zin cwin ctab cout)))
   (fn-pib-initial-new-array-payload (fn-octets$c-buf-length cwin)
           (fn-octets$c-buf-length ctab) (fn-octets$c-buf-length cout)))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
 :use fn-pib-payload-ready-exact-resize-payload
 :in-theory (e/d (fn-pib-piwc-initialize fn-pib-initial-new-array-payload fn-pib-resize-request-payload)
    (fn-pib-piwc-payload-ready fn-piwc-payload-ready fn-octets$c-clear
     fn-octets$c-reserve fn-octets$c-buf-length fn-octets$c-fill
     fn-pib-octets$c-clear fn-pib-octets$c-reserve fn-pib-event-count fn-zin-reset fn-zin-set)))))
(defthm fn-pib-ewz-begin-exact-resize-payload
 (equal (fn-pib-resize-request-payload
         (cdr (fn-pib-piwc-ewz-begin file eoff elen poff compressed decoded offset
                    ticket incarnation lease expected dict hash zin cwin ctab cout)))
   (fn-pib-initial-new-array-payload (fn-octets$c-buf-length cwin)
           (fn-octets$c-buf-length ctab) (fn-octets$c-buf-length cout)))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
 :use fn-pib-initialize-exact-resize-payload
 :in-theory (e/d (fn-pib-piwc-ewz-begin fn-pib-resize-request-payload)
    (fn-pib-piwc-initialize fn-piwc-initialize fn-pib-initial-new-array-payload
     fn-ews-begin fn-ewz-state fn-pzd-budget fn-pzw-stored-admissiblep nfix natp nth
     fn-pib-event-count fn-octets$c-buf-length fn-octets$c-fill)))))
(defthm fn-pib-begin-exact-resize-payload
 (equal (fn-pib-resize-request-payload
         (cdr (fn-pib-piwc-begin token incarnation hash zin cwin ctab cout)))
   (fn-pib-initial-new-array-payload (fn-octets$c-buf-length cwin)
           (fn-octets$c-buf-length ctab) (fn-octets$c-buf-length cout)))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
 :use ((:instance fn-pib-ewz-begin-exact-resize-payload (dict (fn-pwz-dictionary token))
    (file (nfix (fn-pwz-nth 2 token))) (eoff (nfix (fn-pwz-nth 3 token)))
    (elen (nfix (fn-pwz-nth 4 token))) (poff (nfix (fn-pwz-nth 5 token)))
    (compressed (nfix (fn-pwz-nth 6 token))) (decoded (nfix (fn-pwz-nth 9 token)))
    (offset (nfix (fn-pwz-nth 7 token))) (ticket (fn-pwz-nth 1 token))
    (lease token) (expected (nfix (fn-pwz-nth 8 token)))))
 :in-theory (e/d (fn-pib-piwc-begin fn-pib-resize-request-payload)
    (fn-pib-piwc-ewz-begin fn-piwc-ewz-begin fn-pib-piwc-initialize fn-piwc-initialize
     fn-pib-initial-new-array-payload fn-pwz-nth fn-pwz-dictionary fn-pib-event-count
     fn-octets$c-buf-length fn-octets$c-fill fn-ews-begin fn-ewz-state fn-pzd-budget
     fn-pzw-stored-admissiblep nfix natp nth (:e fn-pwz-dictionary))))))

(defthm fn-pib-initial-new-array-payload-bound
 (and (natp (fn-pib-initial-new-array-payload wc tc oc))
      (<= (fn-pib-initial-new-array-payload wc tc oc) 69094))
 :hints (("Goal" :in-theory (enable fn-pib-initial-new-array-payload))))
; This counts source-request payload and retained capacities.  It is not an
; allocator/header, garbage collector, or alias-lifetime highwater theorem.
(defthm fn-pib-actual-begin-retained-payload-bound
 (let* ((r (fn-piwc-begin token incarnation hash zin cwin ctab cout))
        (retained (+ (fn-octets$c-buf-length (mv-nth 3 r))
                     (fn-octets$c-buf-length (mv-nth 4 r))
                     (fn-octets$c-buf-length (mv-nth 5 r)))))
  (<= retained
      (fn-pib-initial-retained-and-requested-payload
       (fn-octets$c-buf-length cwin) (fn-octets$c-buf-length ctab)
       (fn-octets$c-buf-length cout))))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
 :use ((:instance fn-piwc-begin-keeps-initial-capacities
                   (pgs-digest-state hash) (fn-zin-st zin)))
 :in-theory (e/d (fn-pib-initial-retained-and-requested-payload
                  fn-pib-initial-new-array-payload max nfix)
                 (fn-piwc-begin fn-octets$c-buf-length (:e fn-piwc-begin))))))

(defthm fn-pib-actual-begin-array-payload-boundary
 (implies (and (fn-octets$cp cwin) (fn-octets$cp ctab) (fn-octets$cp cout))
  (let* ((o (fn-pib-piwc-begin token incarnation hash zin cwin ctab cout))
         (rc (car o)) (ra (fn-pwz-begin token incarnation hash zin awin atab aout)))
   (and (equal (mv-nth 0 rc) (mv-nth 0 ra))
        (equal (mv-nth 1 rc) (mv-nth 1 ra))
        (equal (mv-nth 2 rc) (mv-nth 2 ra))
        (fn-octets$corr (mv-nth 3 rc) (mv-nth 3 ra))
        (fn-octets$corr (mv-nth 4 rc) (mv-nth 4 ra))
        (fn-octets$corr (mv-nth 5 rc) (mv-nth 5 ra))
        (equal (fn-pib-resize-request-payload (cdr o))
          (fn-pib-initial-new-array-payload (fn-octets$c-buf-length cwin)
            (fn-octets$c-buf-length ctab) (fn-octets$c-buf-length cout)))
        (<= (+ (fn-octets$c-buf-length (mv-nth 3 rc))
               (fn-octets$c-buf-length (mv-nth 4 rc))
               (fn-octets$c-buf-length (mv-nth 5 rc)))
            (fn-pib-initial-retained-and-requested-payload
              (fn-octets$c-buf-length cwin) (fn-octets$c-buf-length ctab)
              (fn-octets$c-buf-length cout))))))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
 :use (fn-pib-begin-exact-resize-payload fn-pib-actual-begin-retained-payload-bound
       (:instance fn-piwc-begin-refines-actual-begin-from-typed-arrays
         (pgs-digest-state hash) (fn-zin-st zin)))
 :in-theory (disable fn-pib-piwc-begin fn-piwc-begin fn-pwz-begin
  fn-pib-resize-request-payload fn-pib-initial-new-array-payload
  fn-pib-initial-retained-and-requested-payload fn-octets$cp fn-octets$corr
  fn-octets$c-buf-length (:e fn-pib-piwc-begin) (:e fn-piwc-begin) (:e fn-pwz-begin)))))
